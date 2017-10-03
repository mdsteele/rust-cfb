//! A library for reading/writing [Compound File Binary](
//! https://en.wikipedia.org/wiki/Compound_File_Binary_Format) (structured
//! storage) files.  See [MS-CFB](
//! https://msdn.microsoft.com/en-us/library/dd942138.aspx) for the format
//! specification.
//!
//! A Compound File Binary (CFB) file, also called a *structured storage file*
//! or simply a *compound file*, is a bit like a simple file system within a
//! file.  A compound file contains a tree of *storage* objects
//! (i.e. directories), each of which can contain *stream* objects (i.e. files)
//! or other storage objects.  The format is designed to allow reasonably
//! efficient in-place mutation and resizing of these stream and storage
//! objects, without having to completely rewrite the CFB file on disk.
//!
//! # Example usage
//!
//! ```no_run
//! use cfb;
//! use std::io::{Read, Seek, SeekFrom, Write};
//!
//! // Open an existing compound file in read-write mode.
//! let mut comp = cfb::open_rw("path/to/cfb/file").unwrap();
//!
//! // Read in all the data from one of the streams in that compound file.
//! let data = {
//!     let mut stream = comp.open_stream("/foo/bar").unwrap();
//!     let mut buffer = Vec::new();
//!     stream.read_to_end(&mut buffer).unwrap();
//!     buffer
//! };
//!
//! // Append that data to the end of another stream in the same file.
//! {
//!     let mut stream = comp.open_stream("/baz").unwrap();
//!     stream.seek(SeekFrom::End(0)).unwrap();
//!     stream.write_all(&data).unwrap();
//! }
//!
//! // Now create a new compound file, and create a new stream with the data.
//! let mut comp2 = cfb::create("some/other/path").unwrap();
//! comp2.create_storage("/spam/").unwrap();
//! let mut stream = comp2.create_stream("/spam/eggs").unwrap();
//! stream.write_all(&data).unwrap();
//! ```

#![warn(missing_docs)]

extern crate byteorder;

use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use internal::{DirEntry, Sector, SectorInit, Sectors};
pub use internal::{Entries, Entry, Version};
use internal::consts::{self, END_OF_CHAIN, NO_STREAM};
use std::cmp::{self, Ordering};
use std::collections::HashSet;
use std::fs;
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::Path;

#[macro_use]
mod internal;

// ========================================================================= //

/// Opens an existing compound file at the given path in read-only mode.
pub fn open<P: AsRef<Path>>(path: P) -> io::Result<CompoundFile<fs::File>> {
    CompoundFile::open(fs::File::open(path)?)
}

/// Opens an existing compound file at the given path in read-write mode.
pub fn open_rw<P: AsRef<Path>>(path: P) -> io::Result<CompoundFile<fs::File>> {
    open_rw_with_path(path.as_ref())
}

fn open_rw_with_path(path: &Path) -> io::Result<CompoundFile<fs::File>> {
    let file = fs::OpenOptions::new().read(true).write(true).open(path)?;
    CompoundFile::open(file)
}

/// Creates a new compound file with no contents at the given path.
///
/// The returned `CompoundFile` object will be both readable and writable.  If
/// a file already exists at the given path, this will overwrite it.
pub fn create<P: AsRef<Path>>(path: P) -> io::Result<CompoundFile<fs::File>> {
    create_with_path(path.as_ref())
}

fn create_with_path(path: &Path) -> io::Result<CompoundFile<fs::File>> {
    let file = fs::OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(true)
        .open(path)?;
    CompoundFile::create(file)
}

// ========================================================================= //

/// A compound file, backed by an underlying reader/writer (such as a
/// [`File`](https://doc.rust-lang.org/std/fs/struct.File.html) or
/// [`Cursor`](https://doc.rust-lang.org/std/io/struct.Cursor.html)).
pub struct CompoundFile<F> {
    sectors: Sectors<F>,
    difat: Vec<u32>,
    fat: Vec<u32>,
    minifat: Vec<u32>,
    minifat_start_sector: u32,
    directory: Vec<DirEntry>,
    directory_start_sector: u32,
}

impl<F> CompoundFile<F> {
    /// Returns the CFB format version used for this compound file.
    pub fn version(&self) -> Version { self.sectors.version() }

    fn root_dir_entry(&self) -> &DirEntry {
        self.dir_entry(consts::ROOT_STREAM_ID)
    }

    fn root_dir_entry_mut(&mut self) -> &mut DirEntry {
        self.dir_entry_mut(consts::ROOT_STREAM_ID)
    }

    fn dir_entry(&self, stream_id: u32) -> &DirEntry {
        &self.directory[stream_id as usize]
    }

    fn dir_entry_mut(&mut self, stream_id: u32) -> &mut DirEntry {
        &mut self.directory[stream_id as usize]
    }

    fn stream_id_for_name_chain(&self, names: &[&str]) -> Option<u32> {
        let mut stream_id = consts::ROOT_STREAM_ID;
        for name in names.iter() {
            stream_id = self.dir_entry(stream_id).child;
            loop {
                if stream_id == NO_STREAM {
                    return None;
                }
                let dir_entry = self.dir_entry(stream_id);
                match internal::path::compare_names(&name, &dir_entry.name) {
                    Ordering::Equal => break,
                    Ordering::Less => stream_id = dir_entry.left_sibling,
                    Ordering::Greater => stream_id = dir_entry.right_sibling,
                }
            }
        }
        Some(stream_id)
    }

    /// Given a path within the compound file, get information about that
    /// stream or storage object.
    pub fn entry<P: AsRef<Path>>(&self, path: P) -> io::Result<Entry> {
        self.entry_with_path(path.as_ref())
    }

    fn entry_with_path(&self, path: &Path) -> io::Result<Entry> {
        let names = internal::path::name_chain_from_path(path)?;
        let path = internal::path::path_from_name_chain(&names);
        let stream_id = match self.stream_id_for_name_chain(&names) {
            Some(stream_id) => stream_id,
            None => not_found!("No such object: {:?}", path),
        };
        Ok(internal::new_entry(self.dir_entry(stream_id), path))
    }

    /// Returns an iterator over the entries within a storage object.
    pub fn read_storage<P: AsRef<Path>>(&self, path: P)
                                        -> io::Result<Entries> {
        self.read_storage_with_path(path.as_ref())
    }

    fn read_storage_with_path(&self, path: &Path) -> io::Result<Entries> {
        let names = internal::path::name_chain_from_path(path)?;
        let path = internal::path::path_from_name_chain(&names);
        let stream_id = match self.stream_id_for_name_chain(&names) {
            Some(stream_id) => stream_id,
            None => not_found!("No such storage: {:?}", path),
        };
        let start = {
            let dir_entry = self.dir_entry(stream_id);
            if dir_entry.obj_type == consts::OBJ_TYPE_STREAM {
                invalid_input!("Not a storage: {:?}", path);
            }
            debug_assert!(dir_entry.obj_type == consts::OBJ_TYPE_STORAGE ||
                              dir_entry.obj_type == consts::OBJ_TYPE_ROOT);
            dir_entry.child
        };
        Ok(internal::new_entries(&self.directory, path, start))
    }

    /// Returns true if there is an existing stream or storage at the given
    /// path, or false if there is nothing at that path.
    pub fn exists<P: AsRef<Path>>(&self, path: P) -> bool {
        match internal::path::name_chain_from_path(path.as_ref()) {
            Ok(names) => self.stream_id_for_name_chain(&names).is_some(),
            Err(_) => false,
        }
    }

    /// Returns true if there is an existing stream at the given path, or false
    /// if there is a storage or nothing at that path.
    pub fn is_stream<P: AsRef<Path>>(&self, path: P) -> bool {
        match internal::path::name_chain_from_path(path.as_ref()) {
            Ok(names) => {
                match self.stream_id_for_name_chain(&names) {
                    Some(stream_id) => {
                        self.dir_entry(stream_id).obj_type ==
                            consts::OBJ_TYPE_STREAM
                    }
                    None => false,
                }
            }
            Err(_) => false,
        }
    }

    /// Returns true if there is an existing storage at the given path, or
    /// false if there is a stream or nothing at that path.
    pub fn is_storage<P: AsRef<Path>>(&self, path: P) -> bool {
        match internal::path::name_chain_from_path(path.as_ref()) {
            Ok(names) => {
                match self.stream_id_for_name_chain(&names) {
                    Some(stream_id) => {
                        self.dir_entry(stream_id).obj_type !=
                            consts::OBJ_TYPE_STREAM
                    }
                    None => false,
                }
            }
            Err(_) => false,
        }
    }

    // TODO: pub fn walk_storage

    // TODO: pub fn copy_stream

    // TODO: pub fn rename

    /// Consumes the `CompoundFile`, returning the underlying reader/writer.
    pub fn into_inner(self) -> F { self.sectors.into_inner() }

    fn validate_difat_and_fat(&self) -> io::Result<()> {
        if self.fat.len() > self.sectors.num_sectors() as usize {
            invalid_data!("Malformed FAT (has {} entries, but file has only \
                           {} sectors)",
                          self.fat.len(),
                          self.sectors.num_sectors());
        }
        for &fat_sector in self.difat.iter() {
            if fat_sector as usize >= self.fat.len() {
                invalid_data!("Malformed DIFAT (index {} out of bounds)",
                              fat_sector);
            }
            if self.fat[fat_sector as usize] != consts::FAT_SECTOR {
                invalid_data!("Malformed FAT (sector {} not marked as FAT)",
                              fat_sector);
            }
        }
        let mut pointees = HashSet::new();
        for (from_sector, &to_sector) in self.fat.iter().enumerate() {
            if to_sector <= consts::MAX_REGULAR_SECTOR {
                if to_sector as usize >= self.fat.len() {
                    invalid_data!("Malformed FAT (sector {} points to {}, \
                                   which is out of bounds)",
                                  from_sector,
                                  to_sector);
                }
                if pointees.contains(&to_sector) {
                    invalid_data!("Malformed FAT (sector {} pointed to twice)",
                                  to_sector);
                }
                pointees.insert(to_sector);
            }
        }
        Ok(())
    }

    fn validate_minifat(&self) -> io::Result<()> {
        let mut pointees = HashSet::new();
        for (from_mini_sector, &to_mini_sector) in
            self.minifat.iter().enumerate()
        {
            if to_mini_sector <= consts::MAX_REGULAR_SECTOR {
                if to_mini_sector as usize >= self.minifat.len() {
                    invalid_data!("Malformed MiniFAT (mini sector {} points \
                                   to {}, which is out of bounds)",
                                  from_mini_sector,
                                  to_mini_sector);
                }
                if pointees.contains(&to_mini_sector) {
                    invalid_data!("Malformed MiniFAT (mini sector {} pointed \
                                   to twice)",
                                  to_mini_sector);
                }
                pointees.insert(to_mini_sector);
            }
        }
        Ok(())
    }

    fn validate_directory(&self) -> io::Result<()> {
        // Note: The MS-CFB spec says that root entries MUST be colored black,
        // but apparently some implementations don't actually do this (see
        // https://social.msdn.microsoft.com/Forums/sqlserver/en-US/
        // 9290d877-d91f-4509-ace9-cb4575c48514/red-black-tree-in-mscfb).  So
        // we don't complain if the root is red.
        let root_entry = self.root_dir_entry();
        if root_entry.name != consts::ROOT_DIR_NAME {
            invalid_data!("Malformed directory (root name)");
        }
        let expected_root_stream_len = consts::MINI_SECTOR_LEN as u64 *
            self.minifat.len() as u64;
        if root_entry.stream_len != expected_root_stream_len {
            invalid_data!("Malformed directory (root stream len is {}, but \
                           should be {})",
                          root_entry.stream_len,
                          expected_root_stream_len);
        }
        if root_entry.stream_len % consts::MINI_SECTOR_LEN as u64 != 0 {
            invalid_data!("Malformed directory (root stream len is {}, but \
                           should be multiple of {})",
                          root_entry.stream_len,
                          consts::MINI_SECTOR_LEN);
        }
        let mut visited = HashSet::new();
        let mut stack = vec![(consts::ROOT_STREAM_ID, false)];
        while let Some((stream_id, parent_is_red)) = stack.pop() {
            if visited.contains(&stream_id) {
                invalid_data!("Malformed directory (loop in tree)");
            }
            visited.insert(stream_id);
            let dir_entry = self.dir_entry(stream_id);
            if stream_id == consts::ROOT_STREAM_ID {
                if dir_entry.obj_type != consts::OBJ_TYPE_ROOT {
                    invalid_data!("Malformed directory (wrong object type for \
                                   root entry: {})",
                                  dir_entry.obj_type);
                }
            } else if dir_entry.obj_type != consts::OBJ_TYPE_STORAGE &&
                       dir_entry.obj_type != consts::OBJ_TYPE_STREAM
            {
                invalid_data!("Malformed directory (wrong object type for \
                               non-root entry: {})",
                              dir_entry.obj_type);
            }
            let node_is_red = dir_entry.color == consts::COLOR_RED;
            if parent_is_red && node_is_red {
                invalid_data!("Malformed directory (two red nodes in a row)");
            }
            let left_sibling = dir_entry.left_sibling;
            if left_sibling != NO_STREAM {
                if left_sibling as usize >= self.directory.len() {
                    invalid_data!("Malformed directory (sibling index)");
                }
                let entry = &self.dir_entry(left_sibling);
                if internal::path::compare_names(&entry.name,
                                                 &dir_entry.name) !=
                    Ordering::Less
                {
                    invalid_data!("Malformed directory (name ordering, \
                                   {:?} vs {:?})",
                                  &dir_entry.name,
                                  &entry.name);
                }
                stack.push((left_sibling, node_is_red));
            }
            let right_sibling = dir_entry.right_sibling;
            if right_sibling != NO_STREAM {
                if right_sibling as usize >= self.directory.len() {
                    invalid_data!("Malformed directory (sibling index)");
                }
                let entry = &self.dir_entry(right_sibling);
                if internal::path::compare_names(&dir_entry.name,
                                                 &entry.name) !=
                    Ordering::Less
                {
                    invalid_data!("Malformed directory (name ordering, \
                                   {:?} vs {:?})",
                                  &dir_entry.name,
                                  &entry.name);
                }
                stack.push((right_sibling, node_is_red));
            }
            let child = dir_entry.child;
            if child != NO_STREAM {
                if child as usize >= self.directory.len() {
                    invalid_data!("Malformed directory (child index)");
                }
                stack.push((child, false));
            }
        }
        Ok(())
    }
}

impl<F: Seek> CompoundFile<F> {
    fn seek_to_mini_sector(&mut self, mini_sector: u32)
                           -> io::Result<Sector<F>> {
        self.seek_within_mini_sector(mini_sector, 0)
    }

    fn seek_within_mini_sector(&mut self, mini_sector: u32,
                               offset_within_mini_sector: u64)
                               -> io::Result<Sector<F>> {
        let sector_len = self.sectors.sector_len();
        let offset_within_mini_stream = offset_within_mini_sector +
            consts::MINI_SECTOR_LEN as u64 * mini_sector as u64;
        let mini_stream_start_sector = self.root_dir_entry().start_sector;
        let mut mini_stream_sector = mini_stream_start_sector;
        for _ in 0..(offset_within_mini_stream / sector_len as u64) {
            debug_assert_ne!(mini_stream_sector, END_OF_CHAIN);
            mini_stream_sector = self.fat[mini_stream_sector as usize];
        }
        let mini_sectors_per_sector = sector_len / consts::MINI_SECTOR_LEN;
        let mini_sector_start_within_sector = (mini_sector as usize %
                                                   mini_sectors_per_sector) *
            consts::MINI_SECTOR_LEN;
        let offset_within_sector = offset_within_mini_stream %
            sector_len as u64;
        let sector =
            self.sectors
                .seek_within_sector(mini_stream_sector, offset_within_sector)?;
        Ok(sector.subsector(mini_sector_start_within_sector,
                            consts::MINI_SECTOR_LEN))
    }

    fn seek_to_dir_entry(&mut self, stream_id: u32) -> io::Result<Sector<F>> {
        self.seek_within_dir_entry(stream_id, 0)
    }

    fn seek_within_dir_entry(&mut self, stream_id: u32,
                             offset_within_dir_entry: usize)
                             -> io::Result<Sector<F>> {
        let dir_entries_per_sector = self.version().dir_entries_per_sector();
        let index_within_sector = stream_id as usize % dir_entries_per_sector;
        let offset_within_sector = index_within_sector *
            consts::DIR_ENTRY_LEN +
            offset_within_dir_entry;
        let mut directory_sector = self.directory_start_sector;
        for _ in 0..(stream_id as usize / dir_entries_per_sector) {
            debug_assert_ne!(directory_sector, END_OF_CHAIN);
            directory_sector = self.fat[directory_sector as usize];
        }
        self.sectors
            .seek_within_sector(directory_sector, offset_within_sector as u64)
    }

    /// Opens an existing stream in the compound file for reading and/or
    /// writing (depending on what the underlying file supports).
    pub fn open_stream<P: AsRef<Path>>(&mut self, path: P)
                                       -> io::Result<Stream<F>> {
        self.open_stream_with_path(path.as_ref())
    }

    fn open_stream_with_path(&mut self, path: &Path) -> io::Result<Stream<F>> {
        let names = internal::path::name_chain_from_path(path)?;
        let path = internal::path::path_from_name_chain(&names);
        let stream_id = match self.stream_id_for_name_chain(&names) {
            Some(stream_id) => stream_id,
            None => not_found!("No such stream: {:?}", path),
        };
        if self.dir_entry(stream_id).obj_type != consts::OBJ_TYPE_STREAM {
            invalid_input!("Not a stream: {:?}", path);
        }
        Stream::new(self, stream_id)
    }
}

impl<F: Read + Seek> CompoundFile<F> {
    /// Opens an existing compound file, using the underlying reader.  If the
    /// underlying reader also supports the `Write` trait, then the
    /// `CompoundFile` object will be writable as well.
    pub fn open(mut inner: F) -> io::Result<CompoundFile<F>> {
        // Read basic header information.
        inner.seek(SeekFrom::Start(0))?;
        let mut magic = [0u8; 8];
        inner.read_exact(&mut magic)?;
        if magic != consts::MAGIC_NUMBER {
            invalid_data!("Invalid CFB file (wrong magic number)");
        }
        let inner_len = inner.seek(SeekFrom::End(0))?;
        inner.seek(SeekFrom::Start(26))?;
        let version_number = inner.read_u16::<LittleEndian>()?;
        let version = match Version::from_number(version_number) {
            Some(version) => version,
            None => {
                invalid_data!("CFB version {} is not supported",
                              version_number);
            }
        };
        let sector_len = version.sector_len();
        if inner_len < sector_len as u64 {
            invalid_data!("Invalid CFB file ({} bytes is too small)",
                          inner_len);
        }
        let num_sectors = (inner_len - sector_len as u64) / sector_len as u64;
        if num_sectors > (consts::MAX_REGULAR_SECTOR + 1) as u64 {
            invalid_data!("Invalid CFB file ({} bytes is too large)",
                          inner_len);
        }
        if inner.read_u16::<LittleEndian>()? != consts::BYTE_ORDER_MARK {
            invalid_data!("Invalid CFB byte order mark");
        }
        let sector_shift = inner.read_u16::<LittleEndian>()?;
        if sector_shift != version.sector_shift() {
            invalid_data!("Incorrect sector shift for CFB version {} \
                           (is {}, but must be {})",
                          version.number(),
                          sector_shift,
                          version.sector_shift());
        }
        let mini_sector_shift = inner.read_u16::<LittleEndian>()?;
        if mini_sector_shift != consts::MINI_SECTOR_SHIFT {
            invalid_data!("Incorrect mini sector shift \
                           (is {}, but must be {})",
                          mini_sector_shift,
                          consts::MINI_SECTOR_SHIFT);
        }
        inner.seek(SeekFrom::Start(44))?;
        let num_fat_sectors = inner.read_u32::<LittleEndian>()?;
        let first_dir_sector = inner.read_u32::<LittleEndian>()?;
        let _transaction_signature = inner.read_u32::<LittleEndian>()?;
        let mini_stream_cutoff = inner.read_u32::<LittleEndian>()?;
        if mini_stream_cutoff != consts::MINI_STREAM_CUTOFF {
            invalid_data!("Invalid mini stream cutoff value \
                           (is {}, but must be {})",
                          mini_stream_cutoff,
                          consts::MINI_STREAM_CUTOFF);
        }
        let first_minifat_sector = inner.read_u32::<LittleEndian>()?;
        let num_minifat_sectors = inner.read_u32::<LittleEndian>()?;
        let first_difat_sector = inner.read_u32::<LittleEndian>()?;
        let num_difat_sectors = inner.read_u32::<LittleEndian>()?;

        // Read in DIFAT.
        let mut difat = Vec::new();
        for _ in 0..consts::NUM_DIFAT_ENTRIES_IN_HEADER {
            let next = inner.read_u32::<LittleEndian>()?;
            if next == consts::FREE_SECTOR {
                break;
            } else if next > consts::MAX_REGULAR_SECTOR {
                invalid_data!("Invalid sector index ({}) in DIFAT", next);
            }
            difat.push(next);
        }
        let mut sectors = Sectors::new(version, num_sectors as u32, inner);
        let mut difat_sectors = Vec::new();
        let mut current_difat_sector = first_difat_sector;
        while current_difat_sector != END_OF_CHAIN {
            difat_sectors.push(current_difat_sector);
            let mut sector = sectors.seek_to_sector(current_difat_sector)?;
            for _ in 0..(sector_len / 4 - 1) {
                let next = sector.read_u32::<LittleEndian>()?;
                if next != consts::FREE_SECTOR &&
                    next > consts::MAX_REGULAR_SECTOR
                {
                    invalid_data!("Invalid sector index ({}) in DIFAT", next);
                }
                difat.push(next);
            }
            current_difat_sector = sector.read_u32::<LittleEndian>()?;
        }
        if num_difat_sectors as usize != difat_sectors.len() {
            invalid_data!("Incorrect DIFAT chain length \
                           (header says {}, actual is {})",
                          num_difat_sectors,
                          difat_sectors.len());
        }
        while difat.last() == Some(&consts::FREE_SECTOR) {
            difat.pop();
        }
        if num_fat_sectors as usize != difat.len() {
            invalid_data!("Incorrect number of FAT sectors \
                           (header says {}, DIFAT says {})",
                          num_fat_sectors,
                          difat.len());
        }

        // Read in FAT.
        let mut fat = Vec::new();
        for index in 0..difat.len() {
            let mut sector = sectors.seek_to_sector(difat[index])?;
            for _ in 0..(sector_len / 4) {
                fat.push(sector.read_u32::<LittleEndian>()?);
            }
        }
        while fat.last() == Some(&consts::FREE_SECTOR) {
            fat.pop();
        }

        let mut comp = CompoundFile {
            sectors: sectors,
            difat: difat,
            fat: fat,
            minifat: Vec::new(),
            minifat_start_sector: first_minifat_sector,
            directory: Vec::new(),
            directory_start_sector: first_dir_sector,
        };
        comp.validate_difat_and_fat()?;

        // Read in MiniFAT.
        let mut minifat_sectors = Vec::new();
        let mut current_minifat_sector = first_minifat_sector;
        while current_minifat_sector != END_OF_CHAIN {
            minifat_sectors.push(current_minifat_sector);
            let mut sector = comp.sectors
                .seek_to_sector(current_minifat_sector)?;
            for _ in 0..(sector_len / 4) {
                comp.minifat.push(sector.read_u32::<LittleEndian>()?);
            }
            current_minifat_sector = comp.fat[current_minifat_sector as usize];
        }
        if num_minifat_sectors as usize != minifat_sectors.len() {
            invalid_data!("Incorrect MiniFAT chain length \
                           (header says {}, actual is {})",
                          num_minifat_sectors,
                          minifat_sectors.len());
        }
        while comp.minifat.last() == Some(&consts::FREE_SECTOR) {
            comp.minifat.pop();
        }
        comp.validate_minifat()?;

        // Read in directory.
        let mut current_dir_sector = first_dir_sector;
        while current_dir_sector != END_OF_CHAIN {
            let mut sector = comp.sectors.seek_to_sector(current_dir_sector)?;
            for _ in 0..version.dir_entries_per_sector() {
                comp.directory
                    .push(DirEntry::read_from(&mut sector, version)?);
            }
            current_dir_sector = comp.fat[current_dir_sector as usize];
        }
        comp.validate_directory()?;
        Ok(comp)
    }
}

impl<F: Read + Write + Seek> CompoundFile<F> {
    /// Creates a new compound file with no contents, using the underlying
    /// reader/writer.  The reader/writer should be initially empty.
    pub fn create(inner: F) -> io::Result<CompoundFile<F>> {
        CompoundFile::create_with_version(Version::V4, inner)
    }

    /// Creates a new compound file of the given version with no contents,
    /// using the underlying writer.  The writer should be initially empty.
    pub fn create_with_version(version: Version, mut inner: F)
                               -> io::Result<CompoundFile<F>> {
        // Write file header:
        inner.write_all(&consts::MAGIC_NUMBER)?;
        inner.write_all(&[0; 16])?; // reserved field
        inner.write_u16::<LittleEndian>(consts::MINOR_VERSION)?;
        inner.write_u16::<LittleEndian>(version.number())?;
        inner.write_u16::<LittleEndian>(consts::BYTE_ORDER_MARK)?;
        inner.write_u16::<LittleEndian>(version.sector_shift())?;
        inner.write_u16::<LittleEndian>(consts::MINI_SECTOR_SHIFT)?;
        inner.write_all(&[0; 6])?; // reserved field
        inner.write_u32::<LittleEndian>(1)?; // num dir sectors
        inner.write_u32::<LittleEndian>(1)?; // num FAT sectors
        inner.write_u32::<LittleEndian>(1)?; // first dir sector
        inner.write_u32::<LittleEndian>(0)?; // transaction signature (unused)
        inner.write_u32::<LittleEndian>(consts::MINI_STREAM_CUTOFF)?;
        inner.write_u32::<LittleEndian>(END_OF_CHAIN)?; // first MiniFAT sector
        inner.write_u32::<LittleEndian>(0)?; // num MiniFAT sectors
        inner.write_u32::<LittleEndian>(END_OF_CHAIN)?; // first DIFAT sector
        inner.write_u32::<LittleEndian>(0)?; // num DIFAT sectors
        // First 109 DIFAT entries:
        inner.write_u32::<LittleEndian>(0)?;
        for _ in 1..consts::NUM_DIFAT_ENTRIES_IN_HEADER {
            inner.write_u32::<LittleEndian>(consts::FREE_SECTOR)?;
        }
        // Pad the header with zeroes so it's the length of a sector.
        let sector_len = version.sector_len();
        debug_assert!(sector_len >= consts::HEADER_LEN);
        if sector_len > consts::HEADER_LEN {
            inner.write_all(&vec![0; sector_len - consts::HEADER_LEN])?;
        }

        // Write FAT sector:
        let fat = vec![consts::FAT_SECTOR, END_OF_CHAIN];
        for &entry in fat.iter() {
            inner.write_u32::<LittleEndian>(entry)?;
        }
        for _ in fat.len()..(sector_len / 4) {
            inner.write_u32::<LittleEndian>(consts::FREE_SECTOR)?;
        }

        // Write directory sector:
        let root_dir_entry = DirEntry {
            name: consts::ROOT_DIR_NAME.to_string(),
            obj_type: consts::OBJ_TYPE_ROOT,
            color: consts::COLOR_BLACK,
            left_sibling: NO_STREAM,
            right_sibling: NO_STREAM,
            child: NO_STREAM,
            clsid: consts::NULL_CLSID,
            state_bits: 0,
            creation_time: 0,
            modified_time: 0,
            start_sector: END_OF_CHAIN,
            stream_len: 0,
        };
        root_dir_entry.write_to(&mut inner)?;
        for _ in 1..version.dir_entries_per_sector() {
            DirEntry::unallocated().write_to(&mut inner)?;
        }

        Ok(CompoundFile {
               sectors: Sectors::new(version, 2, inner),
               difat: vec![0],
               fat: fat,
               minifat: vec![],
               minifat_start_sector: END_OF_CHAIN,
               directory: vec![root_dir_entry],
               directory_start_sector: 1,
           })
    }

    /// Creates a new, empty storage object (i.e. "directory") at the provided
    /// path.  The parent storage object must already exist.
    pub fn create_storage<P: AsRef<Path>>(&mut self, path: P)
                                          -> io::Result<()> {
        self.create_storage_with_path(path.as_ref())
    }

    fn create_storage_with_path(&mut self, path: &Path) -> io::Result<()> {
        let mut names = internal::path::name_chain_from_path(path)?;
        if let Some(stream_id) = self.stream_id_for_name_chain(&names) {
            if self.dir_entry(stream_id).obj_type != consts::OBJ_TYPE_STREAM {
                already_exists!("A storage already exists at that path");
            } else {
                already_exists!("A stream already exists at that path");
            }
        }
        // If names is empty, that means we're trying to create the root.  But
        // the root always already exists and will have been rejected above.
        debug_assert!(!names.is_empty());
        let name = names.pop().unwrap();
        let parent_id = match self.stream_id_for_name_chain(&names) {
            Some(stream_id) => stream_id,
            None => {
                not_found!("Parent storage doesn't exist");
            }
        };
        self.insert_dir_entry(parent_id, name, consts::OBJ_TYPE_STORAGE)?;
        Ok(())
    }

    // TODO: pub fn create_storage_all

    /// Removes the storage object at the provided path.  The storage object
    /// must exist and have no children.
    pub fn remove_storage<P: AsRef<Path>>(&mut self, path: P)
                                          -> io::Result<()> {
        self.remove_storage_with_path(path.as_ref())
    }

    fn remove_storage_with_path(&mut self, path: &Path) -> io::Result<()> {
        let mut names = internal::path::name_chain_from_path(path)?;
        let stream_id = match self.stream_id_for_name_chain(&names) {
            Some(parent_id) => parent_id,
            None => not_found!("No such storage: {:?}", path),
        };
        {
            let dir_entry = self.dir_entry(stream_id);
            if dir_entry.obj_type == consts::OBJ_TYPE_ROOT {
                invalid_input!("Cannot remove the root storage object");
            }
            if dir_entry.obj_type == consts::OBJ_TYPE_STREAM {
                invalid_input!("Not a storage: {:?}", path);
            }
            debug_assert_eq!(dir_entry.obj_type, consts::OBJ_TYPE_STORAGE);
            if dir_entry.child != NO_STREAM {
                invalid_input!("Storage is not empty: {:?}", path);
            }
        }
        debug_assert!(!names.is_empty());
        let name = names.pop().unwrap();
        let parent_id = self.stream_id_for_name_chain(&names).unwrap();
        self.remove_dir_entry(parent_id, name)?;
        Ok(())
    }

    // TODO: pub fn remove_storage_all

    /// Creates and returns a new, empty stream object at the provided path.
    /// If a stream already exists at that path, it will be replaced by the new
    /// stream.  The parent storage object must already exist.
    pub fn create_stream<P: AsRef<Path>>(&mut self, path: P)
                                         -> io::Result<Stream<F>> {
        self.create_stream_with_path(path.as_ref(), true)
    }

    /// Creates and returns a new, empty stream object at the provided path.
    /// Returns an error if a stream already exists at that path.  The parent
    /// storage object must already exist.
    pub fn create_new_stream<P: AsRef<Path>>(&mut self, path: P)
                                             -> io::Result<Stream<F>> {
        self.create_stream_with_path(path.as_ref(), false)
    }

    fn create_stream_with_path(&mut self, path: &Path, overwrite: bool)
                               -> io::Result<Stream<F>> {
        let mut names = internal::path::name_chain_from_path(path)?;
        if let Some(stream_id) = self.stream_id_for_name_chain(&names) {
            if self.dir_entry(stream_id).obj_type != consts::OBJ_TYPE_STREAM {
                already_exists!("A storage already exists at that path");
            } else if !overwrite {
                already_exists!("A stream already exists at that path");
            } else {
                let mut stream = Stream::new(self, stream_id)?;
                stream.set_len(0)?;
                return Ok(stream);
            }
        }
        // If names is empty, that means we're trying to create the root.  But
        // the root always already exists and will have been rejected above.
        debug_assert!(!names.is_empty());
        let name = names.pop().unwrap();
        let parent_id = match self.stream_id_for_name_chain(&names) {
            Some(stream_id) => stream_id,
            None => {
                not_found!("Parent storage doesn't exist");
            }
        };
        let new_stream_id =
            self.insert_dir_entry(parent_id, name, consts::OBJ_TYPE_STREAM)?;
        Ok(Stream {
               comp: self,
               stream_id: new_stream_id,
               offset_from_start: 0,
               offset_within_sector: 0,
               current_sector: END_OF_CHAIN,
               finisher: None,
           })
    }

    /// Removes the stream object at the provided path.
    pub fn remove_stream<P: AsRef<Path>>(&mut self, path: P)
                                         -> io::Result<()> {
        self.remove_stream_with_path(path.as_ref())
    }

    fn remove_stream_with_path(&mut self, path: &Path) -> io::Result<()> {
        let mut names = internal::path::name_chain_from_path(path)?;
        let stream_id = match self.stream_id_for_name_chain(&names) {
            Some(parent_id) => parent_id,
            None => not_found!("No such stream: {:?}", path),
        };
        let mut sector = {
            let dir_entry = self.dir_entry(stream_id);
            if dir_entry.obj_type != consts::OBJ_TYPE_STREAM {
                invalid_input!("Not a stream: {:?}", path);
            }
            debug_assert_eq!(dir_entry.child, NO_STREAM);
            dir_entry.start_sector
        };
        while sector != END_OF_CHAIN {
            let next = self.fat[sector as usize];
            self.free_sector(sector)?;
            sector = next;
        }
        debug_assert!(!names.is_empty());
        let name = names.pop().unwrap();
        let parent_id = self.stream_id_for_name_chain(&names).unwrap();
        self.remove_dir_entry(parent_id, name)?;
        Ok(())
    }

    /// Sets the modified time for the object at the given path to now.  Has no
    /// effect when called on the root storage.
    pub fn touch<P: AsRef<Path>>(&mut self, path: P) -> io::Result<()> {
        self.touch_with_path(path.as_ref())
    }

    fn touch_with_path(&mut self, path: &Path) -> io::Result<()> {
        let names = internal::path::name_chain_from_path(path)?;
        let path = internal::path::path_from_name_chain(&names);
        let stream_id = match self.stream_id_for_name_chain(&names) {
            Some(stream_id) => stream_id,
            None => not_found!("No such object: {:?}", path),
        };
        if stream_id != consts::ROOT_STREAM_ID {
            debug_assert_ne!(self.dir_entry(stream_id).obj_type,
                             consts::OBJ_TYPE_ROOT);
            let now = internal::time::current_timestamp();
            self.dir_entry_mut(stream_id).modified_time = now;
            let mut sector = self.seek_within_dir_entry(stream_id, 108)?;
            sector.write_u64::<LittleEndian>(now)?;
        }
        Ok(())
    }

    /// Flushes all changes to the underlying file.
    pub fn flush(&mut self) -> io::Result<()> { self.sectors.flush() }

    /// Given the starting mini sector of a mini chain, copies the data in that
    /// chain into a newly-allocated regular sector chain, frees the mini
    /// chain, and returns the start sector of the new chain.
    fn migrate_out_of_mini_stream(&mut self, start_mini_sector: u32)
                                  -> io::Result<u32> {
        debug_assert_ne!(start_mini_sector, END_OF_CHAIN);
        let mut mini_sectors = Vec::new();
        let mut current_mini_sector = start_mini_sector;
        while current_mini_sector != END_OF_CHAIN {
            mini_sectors.push(current_mini_sector);
            current_mini_sector = self.minifat[current_mini_sector as usize];
        }
        debug_assert!(!mini_sectors.is_empty());
        let sector_len = self.sectors.sector_len();
        let mut new_start_sector = END_OF_CHAIN;
        let mut data = vec![0u8; sector_len];
        let mut data_start = 0;
        let mut index = 0;
        while index < mini_sectors.len() {
            let mini_sector = mini_sectors[index];
            let data_end = data_start + consts::MINI_SECTOR_LEN;
            {
                let mut sector = self.seek_to_mini_sector(mini_sector)?;
                sector.read_exact(&mut data[data_start..data_end])?;
            }
            data_start += consts::MINI_SECTOR_LEN;
            self.free_mini_sector(mini_sector)?;
            index += 1;
            if index == mini_sectors.len() || data_start == sector_len {
                let new_sector = if new_start_sector == END_OF_CHAIN {
                    new_start_sector = self.allocate_sector(SectorInit::Zero)?;
                    new_start_sector
                } else {
                    self.extend_chain(new_start_sector, SectorInit::Zero)?
                };
                let mut sector = self.sectors.seek_to_sector(new_sector)?;
                sector.write_all(&data[0..data_start])?;
                data_start = 0;
            }
        }
        debug_assert_ne!(new_start_sector, END_OF_CHAIN);
        Ok(new_start_sector)
    }

    /// Given the starting sector (or any internal sector) of a chain, extends
    /// the end of that chain by one sector and returns the new sector number,
    /// updating the FAT as necessary.
    fn extend_chain(&mut self, start_sector: u32, init: SectorInit)
                    -> io::Result<u32> {
        debug_assert_ne!(start_sector, END_OF_CHAIN);
        let mut last_sector = start_sector;
        loop {
            let next = self.fat[last_sector as usize];
            if next == END_OF_CHAIN {
                break;
            }
            last_sector = next;
        }
        let new_sector = self.allocate_sector(init)?;
        self.set_fat(last_sector, new_sector)?;
        Ok(new_sector)
    }

    /// Given the starting mini sector (or any internal mini sector) of a mini
    /// chain, extends the end of that chain by one mini sector and returns the
    /// new mini sector number, updating the MiniFAT as necessary.
    fn extend_mini_chain(&mut self, start_mini_sector: u32)
                         -> io::Result<u32> {
        debug_assert_ne!(start_mini_sector, END_OF_CHAIN);
        let mut last_mini_sector = start_mini_sector;
        loop {
            let next = self.minifat[last_mini_sector as usize];
            if next == END_OF_CHAIN {
                break;
            }
            last_mini_sector = next;
        }
        let new_mini_sector = self.allocate_mini_sector(END_OF_CHAIN)?;
        self.set_minifat(last_mini_sector, new_mini_sector)?;
        Ok(new_mini_sector)
    }

    /// Allocates a new entry in the FAT, sets its value to `END_OF_CHAIN`, and
    /// returns the new sector number.
    fn allocate_sector(&mut self, init: SectorInit) -> io::Result<u32> {
        // If there's an existing free sector, use that.
        for sector_id in 0..self.fat.len() {
            if self.fat[sector_id] == consts::FREE_SECTOR {
                let sector_id = sector_id as u32;
                self.set_fat(sector_id, END_OF_CHAIN)?;
                return Ok(sector_id);
            }
        }
        // Otherwise, we need a new sector; if there's not room in the FAT to
        // add it, then first we need to allocate a new FAT sector.
        let sector_len = self.sectors.sector_len();
        if self.fat.len() % (sector_len / 4) == 0 {
            self.append_fat_sector()?;
        }
        // Add a new sector to the end of the file and return it.
        let new_sector = self.fat.len() as u32;
        self.set_fat(new_sector, END_OF_CHAIN)?;
        self.sectors.init_sector(new_sector, init)?;
        Ok(new_sector)
    }

    /// Allocates a new entry in the MiniFAT, sets its value to `value`, and
    /// returns the new mini sector number.
    fn allocate_mini_sector(&mut self, value: u32) -> io::Result<u32> {
        // If there's an existing free mini sector, use that.
        for mini_sector in 0..self.minifat.len() {
            if self.minifat[mini_sector] == consts::FREE_SECTOR {
                let mini_sector = mini_sector as u32;
                self.set_minifat(mini_sector, value)?;
                return Ok(mini_sector);
            }
        }
        // Otherwise, we need a new mini sector; if there's not room in the
        // MiniFAT to add it, then first we need to allocate a new MiniFAT
        // sector.
        let minifat_entries_per_sector = self.sectors.sector_len() / 4;
        let num_minifat_sectors =
            (self.minifat.len() / minifat_entries_per_sector) as u32;
        if self.minifat_start_sector == END_OF_CHAIN {
            debug_assert!(self.minifat.is_empty());
            debug_assert_eq!(num_minifat_sectors, 0);
            let new_sector = self.allocate_sector(SectorInit::Fat)?;
            self.minifat_start_sector = new_sector;
            let mut header = self.sectors.seek_within_header(60)?;
            header.write_u32::<LittleEndian>(new_sector)?;
            header.write_u32::<LittleEndian>(num_minifat_sectors + 1)?;
        } else if self.minifat.len() % minifat_entries_per_sector == 0 {
            let start = self.minifat_start_sector;
            self.extend_chain(start, SectorInit::Fat)?;
            let mut header = self.sectors.seek_within_header(64)?;
            header.write_u32::<LittleEndian>(num_minifat_sectors + 1)?;
        }
        // Add a new mini sector to the end of the mini stream and return it.
        let new_mini_sector = self.minifat.len() as u32;
        self.set_minifat(new_mini_sector, value)?;
        self.append_mini_sector()?;
        Ok(new_mini_sector)
    }

    /// Adds a new (uninitialized) entry to the directory and returns the new
    /// sector ID.
    fn allocate_dir_entry(&mut self) -> io::Result<u32> {
        // If there's an existing unalloated directory entry, use that.
        for (stream_id, entry) in self.directory.iter().enumerate() {
            if entry.obj_type == consts::OBJ_TYPE_UNALLOCATED {
                return Ok(stream_id as u32);
            }
        }
        // Otherwise, we need a new entry; if there's not room in the directory
        // chain to add it, then first we need to add a new directory sector.
        let dir_entries_per_sector = self.version().dir_entries_per_sector();
        let unallocated_dir_entry = DirEntry::unallocated();
        if self.directory.len() % dir_entries_per_sector == 0 {
            let start_sector = self.directory_start_sector;
            self.extend_chain(start_sector, SectorInit::Dir)?;
        }
        // Add a new entry to the end of the directory and return it.
        let stream_id = self.directory.len() as u32;
        self.directory.push(unallocated_dir_entry);
        Ok(stream_id)
    }

    /// Adds a new sector to the FAT chain at the end of the file, and updates
    /// the FAT and DIFAT accordingly.
    fn append_fat_sector(&mut self) -> io::Result<()> {
        // Add a new sector to the end of the file.
        let new_fat_sector = self.fat.len() as u32;
        self.sectors.init_sector(new_fat_sector, SectorInit::Fat)?;

        // Record this new FAT sector in the DIFAT and in the FAT itself.
        let difat_index = self.difat.len();
        self.difat.push(new_fat_sector);
        if difat_index < consts::NUM_DIFAT_ENTRIES_IN_HEADER {
            let offset = 76 + 4 * difat_index as u64;
            let mut header = self.sectors.seek_within_header(offset)?;
            header.write_u32::<LittleEndian>(new_fat_sector)?;
        } else {
            // TODO: write into a DIFAT sector, possibly allocating a new one
            panic!("more than {} DIFAT entries not yet supported");
        }
        self.set_fat(new_fat_sector, consts::FAT_SECTOR)?;
        debug_assert_eq!(self.fat.len(), new_fat_sector as usize + 1);

        // Update length of FAT chain in header.
        let mut header = self.sectors.seek_within_header(44)?;
        header.write_u32::<LittleEndian>(self.difat.len() as u32)?;
        Ok(())
    }

    /// Adds a new mini sector to the end of the mini stream.
    fn append_mini_sector(&mut self) -> io::Result<()> {
        let mini_stream_start_sector = self.root_dir_entry().start_sector;
        let mini_stream_len = self.root_dir_entry().stream_len;
        debug_assert_eq!(mini_stream_len % consts::MINI_SECTOR_LEN as u64, 0);
        let sector_len = self.sectors.sector_len();

        // If the mini stream doesn't have room for new mini sector, add
        // another regular sector to its chain.
        if mini_stream_start_sector == END_OF_CHAIN {
            debug_assert_eq!(mini_stream_len, 0);
            let new_sector_id = self.allocate_sector(SectorInit::Zero)?;
            self.root_dir_entry_mut().start_sector = new_sector_id;
            let mut sector =
                self.seek_within_dir_entry(consts::ROOT_STREAM_ID, 116)?;
            sector.write_u32::<LittleEndian>(new_sector_id)?;
        } else if mini_stream_len % sector_len as u64 == 0 {
            self.extend_chain(mini_stream_start_sector, SectorInit::Zero)?;
        }

        // Update length of mini stream in root directory entry.
        self.root_dir_entry_mut().stream_len += consts::MINI_SECTOR_LEN as u64;
        let mini_stream_len = self.root_dir_entry().stream_len;
        let mut sector = self.seek_within_dir_entry(consts::ROOT_STREAM_ID,
                                                    120)?;
        sector.write_u64::<LittleEndian>(mini_stream_len)?;
        Ok(())
    }

    /// Inserts a new directory entry into the tree under the specified parent
    /// entry.
    fn insert_dir_entry(&mut self, parent_id: u32, name: &str, obj_type: u8)
                        -> io::Result<u32> {
        debug_assert_ne!(obj_type, consts::OBJ_TYPE_UNALLOCATED);
        // Create a new directory entry.
        let stream_id = self.allocate_dir_entry()?;
        let now = internal::time::current_timestamp();
        *self.dir_entry_mut(stream_id) = DirEntry {
            name: name.to_string(),
            obj_type: obj_type,
            color: consts::COLOR_BLACK,
            left_sibling: NO_STREAM,
            right_sibling: NO_STREAM,
            child: NO_STREAM,
            clsid: consts::NULL_CLSID,
            state_bits: 0,
            creation_time: now,
            modified_time: now,
            start_sector: if obj_type == consts::OBJ_TYPE_STREAM {
                END_OF_CHAIN
            } else {
                0
            },
            stream_len: 0,
        };

        // Insert the new entry into the tree.
        let mut sibling_id = self.dir_entry(parent_id).child;
        let mut prev_sibling_id = parent_id;
        let mut ordering = Ordering::Equal;
        while sibling_id != NO_STREAM {
            let sibling = self.dir_entry(sibling_id);
            prev_sibling_id = sibling_id;
            ordering = internal::path::compare_names(name, &sibling.name);
            sibling_id = match ordering {
                Ordering::Less => sibling.left_sibling,
                Ordering::Greater => sibling.right_sibling,
                Ordering::Equal => panic!("internal error: insert duplicate"),
            };
        }
        match ordering {
            Ordering::Less => {
                self.dir_entry_mut(prev_sibling_id).left_sibling = stream_id;
                let mut sector =
                    self.seek_within_dir_entry(prev_sibling_id, 68)?;
                sector.write_u32::<LittleEndian>(stream_id)?;
            }
            Ordering::Greater => {
                self.dir_entry_mut(prev_sibling_id).right_sibling = stream_id;
                let mut sector =
                    self.seek_within_dir_entry(prev_sibling_id, 72)?;
                sector.write_u32::<LittleEndian>(stream_id)?;
            }
            Ordering::Equal => {
                debug_assert_eq!(prev_sibling_id, parent_id);
                self.dir_entry_mut(parent_id).child = stream_id;
                let mut sector = self.seek_within_dir_entry(parent_id, 76)?;
                sector.write_u32::<LittleEndian>(stream_id)?;
            }
        }
        // TODO: rebalance tree

        // Write new entry to underyling file.
        self.write_dir_entry(stream_id)?;
        Ok(stream_id)
    }

    /// Removes a directory entry from the tree and deallocates it.
    fn remove_dir_entry(&mut self, parent_id: u32, name: &str)
                        -> io::Result<()> {
        // Find the directory entry with the given name below the parent.
        let mut stream_ids = Vec::new();
        let mut stream_id = self.dir_entry(parent_id).child;
        loop {
            debug_assert_ne!(stream_id, NO_STREAM);
            debug_assert!(!stream_ids.contains(&stream_id));
            stream_ids.push(stream_id);
            let dir_entry = self.dir_entry(stream_id);
            match internal::path::compare_names(name, &dir_entry.name) {
                Ordering::Equal => break,
                Ordering::Less => stream_id = dir_entry.left_sibling,
                Ordering::Greater => stream_id = dir_entry.right_sibling,
            }
        }
        debug_assert_eq!(self.dir_entry(stream_id).child, NO_STREAM);

        // Restructure the tree.
        let mut replacement_id = NO_STREAM;
        loop {
            let left_sibling = self.dir_entry(stream_id).left_sibling;
            let right_sibling = self.dir_entry(stream_id).right_sibling;
            if left_sibling == NO_STREAM && right_sibling == NO_STREAM {
                break;
            } else if left_sibling == NO_STREAM {
                replacement_id = right_sibling;
                break;
            } else if right_sibling == NO_STREAM {
                replacement_id = left_sibling;
                break;
            }
            let mut predecessor_id = left_sibling;
            loop {
                stream_ids.push(predecessor_id);
                let next_id = self.dir_entry(predecessor_id).right_sibling;
                if next_id == NO_STREAM {
                    break;
                }
                predecessor_id = next_id;
            }
            let mut pred_entry = self.dir_entry(predecessor_id).clone();
            debug_assert_eq!(pred_entry.right_sibling, NO_STREAM);
            pred_entry.left_sibling = left_sibling;
            pred_entry.right_sibling = right_sibling;
            pred_entry.write_to(&mut self.seek_to_dir_entry(stream_id)?)?;
            *self.dir_entry_mut(stream_id) = pred_entry;
            stream_id = predecessor_id;
        }
        // TODO: recolor nodes

        // Remove the entry.
        debug_assert_eq!(stream_ids.last(), Some(&stream_id));
        stream_ids.pop();
        if let Some(&sibling_id) = stream_ids.last() {
            if self.dir_entry(sibling_id).left_sibling == stream_id {
                self.dir_entry_mut(sibling_id).left_sibling = replacement_id;
                let mut sector = self.seek_within_dir_entry(sibling_id, 68)?;
                sector.write_u32::<LittleEndian>(replacement_id)?;
            } else {
                debug_assert_eq!(self.dir_entry(sibling_id).right_sibling,
                                 stream_id);
                self.dir_entry_mut(sibling_id).right_sibling = replacement_id;
                let mut sector = self.seek_within_dir_entry(sibling_id, 72)?;
                sector.write_u32::<LittleEndian>(replacement_id)?;
            }
        } else {
            self.dir_entry_mut(parent_id).child = replacement_id;
            let mut sector = self.seek_within_dir_entry(parent_id, 76)?;
            sector.write_u32::<LittleEndian>(replacement_id)?;
        }
        self.free_dir_entry(stream_id)?;
        Ok(())
    }

    /// Deallocates the specified sector.
    fn free_sector(&mut self, sector: u32) -> io::Result<()> {
        self.set_fat(sector, consts::FREE_SECTOR)?;
        // TODO: Truncate FAT if last FAT sector is now all free.
        Ok(())
    }

    /// Deallocates the specified mini sector.
    fn free_mini_sector(&mut self, mini_sector: u32) -> io::Result<()> {
        self.set_minifat(mini_sector, consts::FREE_SECTOR)?;
        let mut mini_stream_len = self.root_dir_entry().stream_len;
        debug_assert_eq!(mini_stream_len % consts::MINI_SECTOR_LEN as u64, 0);
        while self.minifat.last() == Some(&consts::FREE_SECTOR) {
            mini_stream_len -= consts::MINI_SECTOR_LEN as u64;
            self.minifat.pop();
            // TODO: Truncate MiniFAT if last MiniFAT sector is now all free.
        }
        if mini_stream_len != self.root_dir_entry().stream_len {
            self.root_dir_entry_mut().stream_len = mini_stream_len;
            let mut sector =
                self.seek_within_dir_entry(consts::ROOT_STREAM_ID, 120)?;
            sector.write_u64::<LittleEndian>(mini_stream_len)?;
        }
        Ok(())
    }

    /// Deallocates the specified directory entry.
    fn free_dir_entry(&mut self, stream_id: u32) -> io::Result<()> {
        debug_assert_ne!(stream_id, consts::ROOT_STREAM_ID);
        let dir_entry = DirEntry::unallocated();
        dir_entry.write_to(&mut self.seek_to_dir_entry(stream_id)?)?;
        *self.dir_entry_mut(stream_id) = dir_entry;
        // TODO: Truncate directory chain if last directory sector is now all
        //       unallocated.
        Ok(())
    }

    /// Sets `self.fat[index] = value`, and also writes that change to the
    /// underlying file.  The `index` must be <= `self.fat.len()`.
    fn set_fat(&mut self, index: u32, value: u32) -> io::Result<()> {
        let index = index as usize;
        debug_assert!(index <= self.fat.len());
        let fat_entries_per_sector = self.sectors.sector_len() / 4;
        let fat_sector = self.difat[index / fat_entries_per_sector];
        let offset = 4 * (index % fat_entries_per_sector) as u64;
        let mut sector = self.sectors.seek_within_sector(fat_sector, offset)?;
        sector.write_u32::<LittleEndian>(value)?;
        if index == self.fat.len() {
            self.fat.push(value);
        } else {
            self.fat[index] = value;
        }
        Ok(())
    }

    /// Sets `self.minifat[index] = value`, and also writes that change to the
    /// underlying file.  The `index` must be <= `self.minifat.len()`.
    fn set_minifat(&mut self, index: u32, value: u32) -> io::Result<()> {
        let index = index as usize;
        debug_assert!(index <= self.minifat.len());
        let minifat_entries_per_sector = self.sectors.sector_len() / 4;
        let mut minifat_sector = self.minifat_start_sector;
        for _ in 0..(index / minifat_entries_per_sector) {
            debug_assert_ne!(minifat_sector, END_OF_CHAIN);
            minifat_sector = self.fat[minifat_sector as usize];
        }
        let offset = 4 * (index % minifat_entries_per_sector) as u64;
        let mut sector = self.sectors
            .seek_within_sector(minifat_sector, offset)?;
        sector.write_u32::<LittleEndian>(value)?;
        if index == self.minifat.len() {
            self.minifat.push(value);
        } else {
            self.minifat[index] = value;
        }
        Ok(())
    }

    fn write_dir_entry(&mut self, stream_id: u32) -> io::Result<()> {
        let dir_entries_per_sector = self.version().dir_entries_per_sector();
        let index_within_sector = stream_id as usize % dir_entries_per_sector;
        let offset_within_sector = index_within_sector * consts::DIR_ENTRY_LEN;
        let mut directory_sector = self.directory_start_sector;
        for _ in 0..(stream_id as usize / dir_entries_per_sector) {
            debug_assert_ne!(directory_sector, END_OF_CHAIN);
            directory_sector = self.fat[directory_sector as usize];
        }
        let mut sector =
            self.sectors
                .seek_within_sector(directory_sector,
                                    offset_within_sector as u64)?;
        self.directory[stream_id as usize].write_to(&mut sector)?;
        Ok(())
    }
}

// ========================================================================= //

/// A stream entry in a compound file, much like a filesystem file.
pub struct Stream<'a, F: 'a> {
    comp: &'a mut CompoundFile<F>,
    stream_id: u32,
    offset_from_start: u64,
    offset_within_sector: usize,
    current_sector: u32,
    finisher: Option<Box<Finish<F>>>,
}

impl<'a, F> Stream<'a, F> {
    fn dir_entry(&self) -> &DirEntry { self.comp.dir_entry(self.stream_id) }

    fn dir_entry_mut(&mut self) -> &mut DirEntry {
        self.comp.dir_entry_mut(self.stream_id)
    }

    /// Returns the current length of the stream, in bytes.
    pub fn len(&self) -> u64 { self.dir_entry().stream_len }

    fn is_in_mini_stream(&self) -> bool {
        self.len() < consts::MINI_STREAM_CUTOFF as u64
    }

    fn sector_len(&self) -> usize {
        if self.is_in_mini_stream() {
            consts::MINI_SECTOR_LEN
        } else {
            self.comp.sectors.sector_len()
        }
    }
}

impl<'a, F: Seek> Stream<'a, F> {
    fn new(comp: &'a mut CompoundFile<F>, stream_id: u32)
           -> io::Result<Stream<'a, F>> {
        let start_sector = comp.dir_entry(stream_id).start_sector;
        Ok(Stream {
               comp: comp,
               stream_id: stream_id,
               offset_from_start: 0,
               offset_within_sector: 0,
               current_sector: start_sector,
               finisher: None,
           })
    }

    fn seek_to_current_position(&mut self) -> io::Result<Sector<F>> {
        debug_assert_ne!(self.current_sector, END_OF_CHAIN);
        if self.is_in_mini_stream() {
            self.comp.seek_within_mini_sector(self.current_sector,
                                              self.offset_within_sector as u64)
        } else {
            self.comp.sectors.seek_within_sector(self.current_sector,
                                                 self.offset_within_sector as
                                                     u64)
        }
    }

    fn advance_to_next_sector(&mut self) {
        debug_assert_ne!(self.current_sector, END_OF_CHAIN);
        debug_assert_eq!(self.offset_within_sector, self.sector_len());
        self.offset_within_sector = 0;
        let is_mini = self.is_in_mini_stream();
        self.current_sector = if is_mini {
            self.comp.minifat[self.current_sector as usize]
        } else {
            self.comp.fat[self.current_sector as usize]
        };
    }
}

impl<'a, F: Read + Write + Seek> Stream<'a, F> {
    /// Truncates or extends the stream, updating the size of this stream to
    /// become `size`.
    ///
    /// If `size` is less than the stream's current size, then the stream will
    /// be shrunk.  If it is greater than the stream's current size, then the
    /// stream will be padded with zeros.
    pub fn set_len(&mut self, size: u64) -> io::Result<()> {
        let current_size = self.len();
        if size == current_size {
            Ok(()) // Do nothing.
        } else if size > current_size {
            let current_pos = self.seek(SeekFrom::End(0))?;
            io::copy(&mut io::repeat(0).take(size - current_size), self)?;
            self.seek(SeekFrom::Start(current_pos))?;
            Ok(())
        } else {
            debug_assert!(current_size > 0);
            self.mark_modified();
            if size < self.offset_from_start {
                self.seek(SeekFrom::Start(size))?;
            }
            let mut sector = self.current_sector;
            debug_assert_ne!(sector, END_OF_CHAIN);
            if size == 0 {
                self.dir_entry_mut().start_sector = END_OF_CHAIN;
                self.current_sector = END_OF_CHAIN;
            } else {
                if size % self.sector_len() as u64 == 0 {
                    self.current_sector = END_OF_CHAIN;
                }
                if self.is_in_mini_stream() {
                    let next = self.comp.minifat[sector as usize];
                    self.comp.set_minifat(sector, END_OF_CHAIN)?;
                    sector = next;
                } else {
                    let next = self.comp.fat[sector as usize];
                    self.comp.set_fat(sector, END_OF_CHAIN)?;
                    sector = next;
                };
            }
            while sector != END_OF_CHAIN {
                if self.is_in_mini_stream() {
                    let next = self.comp.minifat[sector as usize];
                    self.comp.free_mini_sector(sector)?;
                    sector = next;
                } else {
                    let next = self.comp.fat[sector as usize];
                    self.comp.free_sector(sector)?;
                    sector = next;
                }
            }
            self.dir_entry_mut().stream_len = size;
            Ok(())
        }
    }

    fn mark_modified(&mut self) {
        if self.finisher.is_none() {
            let finisher: Box<Finish<F>> =
                Box::new(UpdateDirEntry::new(self.stream_id));
            self.finisher = Some(finisher);
        }
    }
}

impl<'a, F: Read + Seek> Seek for Stream<'a, F> {
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        let total_len = self.len();
        let new_pos = match pos {
            SeekFrom::Start(delta) => delta as i64,
            SeekFrom::End(delta) => delta + total_len as i64,
            SeekFrom::Current(delta) => delta + self.offset_from_start as i64,
        };
        if new_pos < 0 || (new_pos as u64) > total_len {
            invalid_input!("Cannot seek to {}, stream length is {}",
                           new_pos,
                           total_len);
        }
        let new_pos = new_pos as u64;
        if new_pos != self.offset_from_start {
            let is_mini = self.is_in_mini_stream();
            let sector_len = self.sector_len() as u64;
            let mut offset = new_pos;
            let mut sector = self.dir_entry().start_sector;
            while offset >= sector_len {
                sector = if is_mini {
                    self.comp.minifat[sector as usize]
                } else {
                    self.comp.fat[sector as usize]
                };
                offset -= sector_len;
            }
            self.current_sector = sector;
            self.offset_within_sector = offset as usize;
            self.offset_from_start = new_pos;
        }
        Ok(new_pos)
    }
}

impl<'a, F: Read + Seek> Read for Stream<'a, F> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let total_len = self.len();
        debug_assert!(self.offset_from_start <= total_len);
        let remaining_in_file = total_len - self.offset_from_start;
        let sector_len = self.sector_len();
        debug_assert!(self.offset_within_sector <= sector_len);
        if self.offset_within_sector == sector_len {
            self.advance_to_next_sector();
        }
        debug_assert!(self.offset_within_sector < sector_len);
        let max_len = cmp::min(buf.len() as u64, remaining_in_file) as usize;
        if max_len == 0 {
            return Ok(0);
        }
        let bytes_read = self.seek_to_current_position()?
            .read(&mut buf[0..max_len])?;
        self.offset_within_sector += bytes_read;
        debug_assert!(self.offset_within_sector <= sector_len);
        self.offset_from_start += bytes_read as u64;
        debug_assert!(self.offset_from_start <= total_len);
        Ok(bytes_read)
    }
}

impl<'a, F: Read + Write + Seek> Write for Stream<'a, F> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if buf.is_empty() {
            return Ok(0);
        }
        self.mark_modified();
        let sector_len = self.sector_len();
        debug_assert!(self.offset_within_sector <= sector_len);
        if self.offset_within_sector == sector_len {
            self.advance_to_next_sector();
        }
        if self.current_sector == END_OF_CHAIN {
            debug_assert_eq!(self.offset_from_start, self.len());
            debug_assert_eq!(self.offset_within_sector, 0);
            let start_sector = self.dir_entry().start_sector;
            self.current_sector = if start_sector == END_OF_CHAIN {
                debug_assert!(self.is_in_mini_stream());
                let sector_id = self.comp.allocate_mini_sector(END_OF_CHAIN)?;
                self.dir_entry_mut().start_sector = sector_id;
                sector_id
            } else if self.is_in_mini_stream() {
                self.comp.extend_mini_chain(start_sector)?
            } else {
                self.comp.extend_chain(start_sector, SectorInit::Zero)?
            };
        }
        debug_assert_ne!(self.current_sector, END_OF_CHAIN);
        debug_assert!(self.offset_within_sector < sector_len);
        let bytes_written = self.seek_to_current_position()?.write(buf)?;
        self.offset_within_sector += bytes_written;
        debug_assert!(self.offset_within_sector <= sector_len);
        self.offset_from_start += bytes_written as u64;
        if self.offset_from_start > self.len() {
            let was_mini = self.is_in_mini_stream();
            self.dir_entry_mut().stream_len = self.offset_from_start;
            if was_mini && !self.is_in_mini_stream() {
                debug_assert_eq!(self.dir_entry().stream_len,
                                 consts::MINI_STREAM_CUTOFF as u64);
                let old_start_sector = self.dir_entry().start_sector;
                let new_start_sector =
                    self.comp.migrate_out_of_mini_stream(old_start_sector)?;
                self.dir_entry_mut().start_sector = new_start_sector;
                let sector_len = self.sector_len();
                debug_assert_eq!(self.offset_from_start % sector_len as u64,
                                 0);
                self.offset_within_sector = 0;
                self.current_sector = END_OF_CHAIN;
            }
        }
        debug_assert!(self.offset_from_start <= self.len());
        Ok(bytes_written)
    }

    fn flush(&mut self) -> io::Result<()> {
        if let Some(finisher) = self.finisher.take() {
            finisher.finish(self.comp)?;
        }
        self.comp.sectors.flush()
    }
}

impl<'a, F> Drop for Stream<'a, F> {
    fn drop(&mut self) {
        if let Some(finisher) = self.finisher.take() {
            let _ = finisher.finish(self.comp);
        }
    }
}

// ========================================================================= //

trait Finish<F> {
    fn finish(&self, comp: &mut CompoundFile<F>) -> io::Result<()>;
}

struct UpdateDirEntry {
    stream_id: u32,
}

impl UpdateDirEntry {
    fn new(stream_id: u32) -> UpdateDirEntry {
        UpdateDirEntry { stream_id: stream_id }
    }
}

impl<F: Read + Write + Seek> Finish<F> for UpdateDirEntry {
    fn finish(&self, comp: &mut CompoundFile<F>) -> io::Result<()> {
        comp.directory[self.stream_id as usize].modified_time =
            internal::time::current_timestamp();
        comp.write_dir_entry(self.stream_id)?;
        Ok(())
    }
}

// ========================================================================= //

#[cfg(test)]
mod tests {
    use super::{CompoundFile, Version};
    use internal::consts;
    use std::io::{Cursor, Read, Seek, SeekFrom, Write};

    fn list_storage<F>(comp: &CompoundFile<F>, path: &str) -> Vec<String> {
        comp.read_storage(path)
            .unwrap()
            .map(|e| e.name().to_string())
            .collect()
    }

    #[test]
    #[should_panic(expected = "Invalid CFB file (wrong magic number)")]
    fn wrong_magic_number() {
        let cursor = Cursor::new([1u8, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]);
        CompoundFile::open(cursor).unwrap();
    }

    #[test]
    fn create_empty_compound_file() {
        let version = Version::V3;

        let cursor = Cursor::new(Vec::new());
        let comp = CompoundFile::create_with_version(version, cursor)
            .expect("create");
        assert_eq!(comp.version(), version);
        assert_eq!(comp.entry("/").unwrap().name(), consts::ROOT_DIR_NAME);

        let cursor = comp.into_inner();
        assert_eq!(cursor.get_ref().len(), 3 * version.sector_len());
        let comp = CompoundFile::open(cursor).expect("open");
        assert_eq!(comp.version(), version);
        assert_eq!(comp.entry("/").unwrap().name(), consts::ROOT_DIR_NAME);
    }

    #[test]
    fn empty_compound_file_has_no_children() {
        let cursor = Cursor::new(Vec::new());
        let comp = CompoundFile::create_with_version(Version::V4, cursor)
            .expect("create");
        assert!(comp.entry("/").unwrap().is_root());
        assert_eq!(comp.read_storage("/").unwrap().count(), 0);
    }

    #[test]
    fn create_directory_tree() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        comp.create_storage("/foo").unwrap();
        comp.create_storage("/baz").unwrap();
        comp.create_storage("/foo/bar").unwrap();

        let cursor = comp.into_inner();
        let comp = CompoundFile::open(cursor).expect("open");
        assert_eq!(list_storage(&comp, "/"), vec!["baz", "foo"]);
        assert_eq!(list_storage(&comp, "/foo"), vec!["bar"]);
        assert!(list_storage(&comp, "/baz").is_empty());
        assert!(list_storage(&comp, "/foo/bar").is_empty());
    }

    #[test]
    fn create_streams() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        comp.create_stream("/foo").unwrap().write_all(b"foobar").unwrap();
        comp.create_stream("/baz").unwrap().write_all(b"baz!").unwrap();

        let cursor = comp.into_inner();
        let mut comp = CompoundFile::open(cursor).expect("open");
        {
            let mut stream = comp.open_stream("/foo").unwrap();
            let mut data = String::new();
            stream.read_to_string(&mut data).unwrap();
            assert_eq!(&data, "foobar");
        }
        {
            let mut stream = comp.open_stream("/baz").unwrap();
            let mut data = String::new();
            stream.read_to_string(&mut data).unwrap();
            assert_eq!(&data, "baz!");
        }
    }

    #[test]
    fn create_small_stream() {
        let data = vec![b'x'; 500];
        assert!(data.len() > consts::MINI_SECTOR_LEN);
        assert!(data.len() < consts::MINI_STREAM_CUTOFF as usize);

        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create_with_version(Version::V3, cursor)
            .expect("create");
        comp.create_stream("foobar").unwrap().write_all(&data).unwrap();

        let cursor = comp.into_inner();
        let mut comp = CompoundFile::open(cursor).expect("open");
        let mut stream = comp.open_stream("foobar").unwrap();
        let mut actual_data = Vec::new();
        stream.read_to_end(&mut actual_data).unwrap();
        assert_eq!(actual_data, data);
    }

    #[test]
    fn create_large_stream() {
        let data = vec![b'x'; 5000];
        assert!(data.len() > consts::MINI_STREAM_CUTOFF as usize);

        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create_with_version(Version::V3, cursor)
            .expect("create");
        comp.create_stream("foobar").unwrap().write_all(&data).unwrap();

        let cursor = comp.into_inner();
        let mut comp = CompoundFile::open(cursor).expect("open");
        let mut stream = comp.open_stream("foobar").unwrap();
        let mut actual_data = Vec::new();
        stream.read_to_end(&mut actual_data).unwrap();
        assert_eq!(actual_data, data);
    }

    #[test]
    fn create_very_large_stream() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create_with_version(Version::V3, cursor)
            .expect("create");
        {
            let mut stream = comp.create_stream("foobar").unwrap();
            let data = vec![b'x'; 1000];
            for _ in 0..1000 {
                stream.write_all(&data).unwrap();
            }
        }

        let cursor = comp.into_inner();
        let mut comp = CompoundFile::open(cursor).expect("open");
        let mut stream = comp.open_stream("foobar").unwrap();
        assert_eq!(stream.len(), 1_000_000);
        assert_eq!(stream.seek(SeekFrom::End(0)).unwrap(), 1_000_000);
    }

    #[test]
    fn create_stream_where_stream_exists() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        let data1 = vec![b'x'; 200];
        comp.create_stream("/foobar").unwrap().write_all(&data1).unwrap();
        let data2 = vec![b'y'; 100];
        comp.create_stream("/foobar").unwrap().write_all(&data2).unwrap();
        let mut stream = comp.open_stream("/foobar").expect("open");
        assert_eq!(stream.len(), data2.len() as u64);
        let mut actual_data = Vec::new();
        stream.read_to_end(&mut actual_data).unwrap();
        assert_eq!(actual_data, data2);
    }

    #[test]
    #[should_panic(expected = "A storage already exists at that path")]
    fn create_stream_where_storage_exists() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        comp.create_storage("/foobar/").expect("create_storage");
        comp.create_stream("/foobar").unwrap();
    }

    #[test]
    #[should_panic(expected = "A stream already exists at that path")]
    fn create_new_stream_where_stream_exists() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        let data = vec![b'x'; 200];
        comp.create_new_stream("/foobar").unwrap().write_all(&data).unwrap();
        comp.create_new_stream("/foobar").unwrap();
    }

    #[test]
    #[should_panic(expected = "A storage already exists at that path")]
    fn create_new_stream_where_storage_exists() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        comp.create_storage("/foobar/").expect("create_storage");
        comp.create_new_stream("/foobar").unwrap();
    }

    #[test]
    #[should_panic(expected = "A stream already exists at that path")]
    fn create_storage_where_stream_exists() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        let data = vec![b'x'; 200];
        comp.create_new_stream("/foobar").unwrap().write_all(&data).unwrap();
        comp.create_storage("/foobar/").unwrap();
    }

    #[test]
    #[should_panic(expected = "A storage already exists at that path")]
    fn create_storage_where_storage_exists() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        comp.create_storage("/foobar/").expect("create_storage");
        comp.create_storage("/foobar/").unwrap();
    }

    #[test]
    #[should_panic(expected = "A storage already exists at that path")]
    fn create_root_storage() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        comp.create_storage("/").unwrap();
    }

    #[test]
    #[should_panic(expected = "Not a storage: \\\"/foo\\\"")]
    fn read_storage_on_stream() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        comp.create_stream("/foo").unwrap().write_all(b"foobar").unwrap();
        comp.read_storage("/foo").unwrap();
    }

    #[test]
    fn path_exists() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        comp.create_stream("/foo").unwrap().write_all(b"foo").unwrap();
        comp.create_storage("/bar/").unwrap();
        comp.create_stream("/bar/quux").unwrap().write_all(b"quux").unwrap();

        assert!(comp.exists("/"));
        assert!(comp.exists("foo"));
        assert!(comp.exists("/bar"));
        assert!(!comp.exists("quux"));
        assert!(comp.exists("bar/quux"));
        assert!(!comp.exists("bar/foo"));
        assert!(comp.exists("/bar/../foo"));
        assert!(comp.exists("/bar/../bar"));
        assert!(!comp.exists("../../foo"));
    }

    #[test]
    fn path_is_stream() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        comp.create_stream("/foo").unwrap().write_all(b"foo").unwrap();
        comp.create_storage("/bar/").unwrap();
        comp.create_stream("/bar/quux").unwrap().write_all(b"quux").unwrap();

        assert!(!comp.is_stream("/"));
        assert!(comp.is_stream("foo"));
        assert!(!comp.is_stream("/bar"));
        assert!(!comp.is_stream("quux"));
        assert!(comp.is_stream("bar/quux"));
        assert!(!comp.is_stream("bar/foo"));
        assert!(comp.is_stream("/bar/../foo"));
        assert!(!comp.is_stream("/bar/../bar"));
        assert!(!comp.is_stream("../../foo"));
    }

    #[test]
    fn path_is_storage() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        comp.create_stream("/foo").unwrap().write_all(b"foo").unwrap();
        comp.create_storage("/bar/").unwrap();
        comp.create_stream("/bar/quux").unwrap().write_all(b"quux").unwrap();

        assert!(comp.is_storage("/"));
        assert!(!comp.is_storage("foo"));
        assert!(comp.is_storage("/bar"));
        assert!(!comp.is_storage("quux"));
        assert!(!comp.is_storage("bar/quux"));
        assert!(!comp.is_storage("bar/foo"));
        assert!(!comp.is_storage("/bar/../foo"));
        assert!(comp.is_storage("/bar/../bar"));
        assert!(!comp.is_storage("../../bar"));
    }

    #[test]
    fn remove_storages() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        comp.create_storage("/foo").unwrap();
        comp.create_storage("/foo/bar").unwrap();
        comp.create_storage("/baz").unwrap();
        comp.create_storage("/quux").unwrap();
        comp.create_storage("/baz/blarg").unwrap();
        comp.remove_storage("/foo/bar").unwrap();
        comp.remove_storage("/foo").unwrap();
        comp.remove_storage("/baz/blarg").unwrap();

        let cursor = comp.into_inner();
        let comp = CompoundFile::open(cursor).expect("open");
        assert_eq!(list_storage(&comp, "/"), vec!["baz", "quux"]);
        assert!(list_storage(&comp, "/baz").is_empty());
    }

    #[test]
    #[should_panic(expected = "No such storage: \\\"/foo\\\"")]
    fn remove_nonexistent_storage() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        comp.remove_storage("/foo").unwrap();
    }

    #[test]
    #[should_panic(expected = "Cannot remove the root storage object")]
    fn remove_root_storage() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        comp.remove_storage("/").unwrap();
    }

    #[test]
    #[should_panic(expected = "Not a storage: \\\"/foo\\\"")]
    fn remove_non_storage() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        comp.create_stream("/foo").unwrap();
        comp.remove_storage("/foo").unwrap();
    }

    #[test]
    #[should_panic(expected = "Storage is not empty: \\\"/foo\\\"")]
    fn remove_non_empty_storage() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        comp.create_storage("/foo").unwrap();
        comp.create_storage("/foo/bar").unwrap();
        comp.remove_storage("/foo").unwrap();
    }

    #[test]
    fn remove_streams() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        comp.create_stream("/foo")
            .unwrap()
            .write_all(&vec![b'x'; 5000])
            .unwrap();
        comp.create_storage("/baz").unwrap();
        comp.create_storage("/quux").unwrap();
        comp.create_stream("/baz/blarg").unwrap();
        comp.remove_stream("/foo").unwrap();
        comp.remove_stream("/baz/blarg").unwrap();

        let cursor = comp.into_inner();
        let comp = CompoundFile::open(cursor).expect("open");
        assert_eq!(list_storage(&comp, "/"), vec!["baz", "quux"]);
        assert!(list_storage(&comp, "/baz").is_empty());
    }

    #[test]
    #[should_panic(expected = "No such stream: \\\"/foo\\\"")]
    fn remove_nonexistent_stream() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        comp.remove_stream("/foo").unwrap();
    }

    #[test]
    #[should_panic(expected = "Not a stream: \\\"/foo\\\"")]
    fn remove_non_stream() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        comp.create_storage("/foo").unwrap();
        comp.remove_stream("/foo").unwrap();
    }

    #[test]
    fn truncate_stream() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        {
            let mut stream = comp.create_stream("/foobar").unwrap();
            stream.write_all(&vec![b'x'; 5000]).unwrap();
            stream.write_all(&vec![b'y'; 5000]).unwrap();
            assert_eq!(stream.len(), 10000);
            stream.set_len(5000).unwrap();
            assert_eq!(stream.len(), 5000);
            stream.write_all(&vec![b'x'; 1000]).unwrap();
            assert_eq!(stream.len(), 6000);
        }

        let cursor = comp.into_inner();
        let mut comp = CompoundFile::open(cursor).expect("open");
        let mut stream = comp.open_stream("/foobar").unwrap();
        assert_eq!(stream.len(), 6000);
        let mut actual_data = Vec::new();
        stream.read_to_end(&mut actual_data).unwrap();
        assert_eq!(actual_data.len(), 6000);
        assert!(actual_data == vec![b'x'; 6000]);
    }

    #[test]
    fn extend_stream() {
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        {
            let mut stream = comp.create_stream("/foobar").unwrap();
            assert_eq!(stream.len(), 0);
            stream.set_len(5000).unwrap();
            assert_eq!(stream.len(), 5000);
        }

        let cursor = comp.into_inner();
        let mut comp = CompoundFile::open(cursor).expect("open");
        let mut stream = comp.open_stream("/foobar").unwrap();
        assert_eq!(stream.len(), 5000);
        let mut actual_data = Vec::new();
        stream.read_to_end(&mut actual_data).unwrap();
        assert_eq!(actual_data.len(), 5000);
        assert!(actual_data == vec![0; 5000]);
    }

    #[test]
    fn stream_seek() {
        let mut data = Vec::new();
        data.append(&mut vec![1; 128]);
        data.append(&mut vec![2; 128]);
        data.append(&mut vec![3; 128]);
        data.append(&mut vec![4; 128]);
        assert_eq!(data.len(), 512);
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).expect("create");
        comp.create_stream("foobar").unwrap().write_all(&data).unwrap();
        let mut stream = comp.open_stream("foobar").expect("open");
        assert_eq!(stream.len(), 512);
        let mut buffer = vec![0; 128];
        assert_eq!(stream.seek(SeekFrom::Start(128)).unwrap(), 128);
        stream.read_exact(&mut buffer).unwrap();
        assert_eq!(buffer, vec![2; 128]);
        assert_eq!(stream.seek(SeekFrom::End(-128)).unwrap(), 384);
        stream.read_exact(&mut buffer).unwrap();
        assert_eq!(buffer, vec![4; 128]);
        assert_eq!(stream.seek(SeekFrom::Current(-256)).unwrap(), 256);
        stream.read_exact(&mut buffer).unwrap();
        assert_eq!(buffer, vec![3; 128]);
    }
}

// ========================================================================= //
