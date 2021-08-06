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

use crate::internal::consts::{self, END_OF_CHAIN, NO_STREAM};
use crate::internal::{
    Allocator, Chain, DirEntry, EntriesOrder, Sector, SectorInit, Sectors,
};
pub use crate::internal::{Entries, Entry, Version};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use std::cmp::{self, Ordering};
use std::collections::HashSet;
use std::fs;
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use uuid::Uuid;

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
    allocator: Allocator<F>,
    minifat: Vec<u32>,
    minifat_start_sector: u32,
    directory: Vec<DirEntry>,
    directory_start_sector: u32,
}

impl<F> CompoundFile<F> {
    /// Returns the CFB format version used for this compound file.
    pub fn version(&self) -> Version {
        self.allocator.version()
    }

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

    /// Returns information about the root storage object.  This is equivalent
    /// to `self.entry("/").unwrap()` (but always succeeds).
    pub fn root_entry(&self) -> Entry {
        Entry::new(self.root_dir_entry(), PathBuf::from("/"))
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
        Ok(Entry::new(self.dir_entry(stream_id), path))
    }

    /// Returns an iterator over the entries within a storage object.
    pub fn read_storage<P: AsRef<Path>>(
        &self,
        path: P,
    ) -> io::Result<Entries> {
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
            debug_assert!(
                dir_entry.obj_type == consts::OBJ_TYPE_STORAGE
                    || dir_entry.obj_type == consts::OBJ_TYPE_ROOT
            );
            dir_entry.child
        };
        Ok(Entries::new(
            EntriesOrder::Nonrecursive,
            &self.directory,
            path,
            start,
        ))
    }

    /// Returns an iterator over all entries under a storage subtree, including
    /// the given path itself.  The iterator walks the storage tree in a
    /// preorder traversal.
    pub fn walk_storage<P: AsRef<Path>>(
        &self,
        path: P,
    ) -> io::Result<Entries> {
        self.walk_storage_with_path(path.as_ref())
    }

    fn walk_storage_with_path(&self, path: &Path) -> io::Result<Entries> {
        let mut names = internal::path::name_chain_from_path(path)?;
        let stream_id = match self.stream_id_for_name_chain(&names) {
            Some(stream_id) => stream_id,
            None => {
                not_found!(
                    "No such object: {:?}",
                    internal::path::path_from_name_chain(&names)
                );
            }
        };
        names.pop();
        let parent_path = internal::path::path_from_name_chain(&names);
        Ok(Entries::new(
            EntriesOrder::Preorder,
            &self.directory,
            parent_path,
            stream_id,
        ))
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
            Ok(names) => match self.stream_id_for_name_chain(&names) {
                Some(stream_id) => {
                    self.dir_entry(stream_id).obj_type
                        == consts::OBJ_TYPE_STREAM
                }
                None => false,
            },
            Err(_) => false,
        }
    }

    /// Returns true if there is an existing storage at the given path, or
    /// false if there is a stream or nothing at that path.
    pub fn is_storage<P: AsRef<Path>>(&self, path: P) -> bool {
        match internal::path::name_chain_from_path(path.as_ref()) {
            Ok(names) => match self.stream_id_for_name_chain(&names) {
                Some(stream_id) => {
                    self.dir_entry(stream_id).obj_type
                        != consts::OBJ_TYPE_STREAM
                }
                None => false,
            },
            Err(_) => false,
        }
    }

    // TODO: pub fn copy_stream

    // TODO: pub fn rename

    /// Consumes the `CompoundFile`, returning the underlying reader/writer.
    pub fn into_inner(self) -> F {
        self.allocator.into_inner()
    }

    fn validate_minifat(&self) -> io::Result<()> {
        let mut pointees = HashSet::new();
        for (from_mini_sector, &to_mini_sector) in
            self.minifat.iter().enumerate()
        {
            if to_mini_sector <= consts::MAX_REGULAR_SECTOR {
                if to_mini_sector as usize >= self.minifat.len() {
                    invalid_data!(
                        "Malformed MiniFAT (mini sector {} points \
                                   to {}, which is out of bounds)",
                        from_mini_sector,
                        to_mini_sector
                    );
                }
                if pointees.contains(&to_mini_sector) {
                    invalid_data!(
                        "Malformed MiniFAT (mini sector {} pointed \
                                   to twice)",
                        to_mini_sector
                    );
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
        let expected_root_stream_len =
            consts::MINI_SECTOR_LEN as u64 * self.minifat.len() as u64;
        if root_entry.stream_len != expected_root_stream_len {
            invalid_data!(
                "Malformed directory (root stream len is {}, but \
                           should be {})",
                root_entry.stream_len,
                expected_root_stream_len
            );
        }
        if root_entry.stream_len % consts::MINI_SECTOR_LEN as u64 != 0 {
            invalid_data!(
                "Malformed directory (root stream len is {}, but \
                           should be multiple of {})",
                root_entry.stream_len,
                consts::MINI_SECTOR_LEN
            );
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
                    invalid_data!(
                        "Malformed directory (wrong object type for \
                                   root entry: {})",
                        dir_entry.obj_type
                    );
                }
            } else if dir_entry.obj_type != consts::OBJ_TYPE_STORAGE
                && dir_entry.obj_type != consts::OBJ_TYPE_STREAM
            {
                invalid_data!(
                    "Malformed directory (wrong object type for \
                               non-root entry: {})",
                    dir_entry.obj_type
                );
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
                if internal::path::compare_names(&entry.name, &dir_entry.name)
                    != Ordering::Less
                {
                    invalid_data!(
                        "Malformed directory (name ordering, \
                                   {:?} vs {:?})",
                        dir_entry.name,
                        entry.name
                    );
                }
                stack.push((left_sibling, node_is_red));
            }
            let right_sibling = dir_entry.right_sibling;
            if right_sibling != NO_STREAM {
                if right_sibling as usize >= self.directory.len() {
                    invalid_data!("Malformed directory (sibling index)");
                }
                let entry = &self.dir_entry(right_sibling);
                if internal::path::compare_names(&dir_entry.name, &entry.name)
                    != Ordering::Less
                {
                    invalid_data!(
                        "Malformed directory (name ordering, \
                                   {:?} vs {:?})",
                        dir_entry.name,
                        entry.name
                    );
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
    fn seek_to_mini_sector(
        &mut self,
        mini_sector: u32,
    ) -> io::Result<Sector<F>> {
        self.seek_within_mini_sector(mini_sector, 0)
    }

    fn seek_within_mini_sector(
        &mut self,
        mini_sector: u32,
        offset_within_mini_sector: u64,
    ) -> io::Result<Sector<F>> {
        let sector_len = self.allocator.sector_len();
        let offset_within_mini_stream = offset_within_mini_sector
            + consts::MINI_SECTOR_LEN as u64 * mini_sector as u64;
        let mini_stream_start_sector = self.root_dir_entry().start_sector;
        let mut mini_stream_sector = mini_stream_start_sector;
        for _ in 0..(offset_within_mini_stream / sector_len as u64) {
            debug_assert_ne!(mini_stream_sector, END_OF_CHAIN);
            mini_stream_sector = self.allocator.next(mini_stream_sector);
        }
        let mini_sectors_per_sector = sector_len / consts::MINI_SECTOR_LEN;
        let mini_sector_start_within_sector = (mini_sector as usize
            % mini_sectors_per_sector)
            * consts::MINI_SECTOR_LEN;
        let offset_within_sector =
            offset_within_mini_stream % sector_len as u64;
        let sector = self
            .allocator
            .seek_within_sector(mini_stream_sector, offset_within_sector)?;
        Ok(sector.subsector(
            mini_sector_start_within_sector,
            consts::MINI_SECTOR_LEN,
        ))
    }

    fn seek_to_dir_entry(&mut self, stream_id: u32) -> io::Result<Sector<F>> {
        self.seek_within_dir_entry(stream_id, 0)
    }

    fn seek_within_dir_entry(
        &mut self,
        stream_id: u32,
        offset_within_dir_entry: usize,
    ) -> io::Result<Sector<F>> {
        let dir_entries_per_sector = self.version().dir_entries_per_sector();
        let index_within_sector = stream_id as usize % dir_entries_per_sector;
        let offset_within_sector = index_within_sector * consts::DIR_ENTRY_LEN
            + offset_within_dir_entry;
        let mut directory_sector = self.directory_start_sector;
        for _ in 0..(stream_id as usize / dir_entries_per_sector) {
            debug_assert_ne!(directory_sector, END_OF_CHAIN);
            directory_sector = self.allocator.next(directory_sector);
        }
        self.allocator
            .seek_within_sector(directory_sector, offset_within_sector as u64)
    }

    /// Opens an existing stream in the compound file for reading and/or
    /// writing (depending on what the underlying file supports).
    pub fn open_stream<P: AsRef<Path>>(
        &mut self,
        path: P,
    ) -> io::Result<Stream<F>> {
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
                invalid_data!(
                    "CFB version {} is not supported",
                    version_number
                );
            }
        };
        let sector_len = version.sector_len();
        if inner_len < sector_len as u64 {
            invalid_data!(
                "Invalid CFB file ({} bytes is too small)",
                inner_len
            );
        }
        if inner_len
            > ((consts::MAX_REGULAR_SECTOR + 1) as u64) * (sector_len as u64)
        {
            invalid_data!(
                "Invalid CFB file ({} bytes is too large)",
                inner_len
            );
        }
        if inner.read_u16::<LittleEndian>()? != consts::BYTE_ORDER_MARK {
            invalid_data!("Invalid CFB byte order mark");
        }
        let sector_shift = inner.read_u16::<LittleEndian>()?;
        if sector_shift != version.sector_shift() {
            invalid_data!(
                "Incorrect sector shift for CFB version {} \
                           (is {}, but must be {})",
                version.number(),
                sector_shift,
                version.sector_shift()
            );
        }
        let mini_sector_shift = inner.read_u16::<LittleEndian>()?;
        if mini_sector_shift != consts::MINI_SECTOR_SHIFT {
            invalid_data!(
                "Incorrect mini sector shift \
                           (is {}, but must be {})",
                mini_sector_shift,
                consts::MINI_SECTOR_SHIFT
            );
        }
        inner.seek(SeekFrom::Start(44))?;
        let num_fat_sectors = inner.read_u32::<LittleEndian>()?;
        let first_dir_sector = inner.read_u32::<LittleEndian>()?;
        let _transaction_signature = inner.read_u32::<LittleEndian>()?;
        let mini_stream_cutoff = inner.read_u32::<LittleEndian>()?;
        if mini_stream_cutoff != consts::MINI_STREAM_CUTOFF {
            invalid_data!(
                "Invalid mini stream cutoff value \
                           (is {}, but must be {})",
                mini_stream_cutoff,
                consts::MINI_STREAM_CUTOFF
            );
        }
        let first_minifat_sector = inner.read_u32::<LittleEndian>()?;
        let num_minifat_sectors = inner.read_u32::<LittleEndian>()?;
        let mut first_difat_sector = inner.read_u32::<LittleEndian>()?;
        let num_difat_sectors = inner.read_u32::<LittleEndian>()?;

        // Some cfb implementations use FREE_SECTOR to indicate END_OF_CHAIN
        if first_difat_sector == consts::FREE_SECTOR {
            first_difat_sector = END_OF_CHAIN;
        }

        // Read in DIFAT.
        let mut difat = Vec::<u32>::new();
        for _ in 0..consts::NUM_DIFAT_ENTRIES_IN_HEADER {
            let next = inner.read_u32::<LittleEndian>()?;
            if next == consts::FREE_SECTOR {
                break;
            } else if next > consts::MAX_REGULAR_SECTOR {
                invalid_data!("Invalid sector index ({}) in DIFAT", next);
            }
            difat.push(next);
        }
        let mut sectors = Sectors::new(version, inner_len, inner);
        let mut difat_sector_ids = Vec::new();
        let mut current_difat_sector = first_difat_sector;
        while current_difat_sector != END_OF_CHAIN {
            difat_sector_ids.push(current_difat_sector);
            let mut sector = sectors.seek_to_sector(current_difat_sector)?;
            for _ in 0..(sector_len / 4 - 1) {
                let next = sector.read_u32::<LittleEndian>()?;
                if next != consts::FREE_SECTOR
                    && next > consts::MAX_REGULAR_SECTOR
                {
                    invalid_data!("Invalid sector index ({}) in DIFAT", next);
                }
                difat.push(next);
            }
            current_difat_sector = sector.read_u32::<LittleEndian>()?;
        }
        if num_difat_sectors as usize != difat_sector_ids.len() {
            invalid_data!(
                "Incorrect DIFAT chain length \
                           (header says {}, actual is {})",
                num_difat_sectors,
                difat_sector_ids.len()
            );
        }
        while difat.last() == Some(&consts::FREE_SECTOR) {
            difat.pop();
        }
        if num_fat_sectors as usize != difat.len() {
            invalid_data!(
                "Incorrect number of FAT sectors \
                           (header says {}, DIFAT says {})",
                num_fat_sectors,
                difat.len()
            );
        }

        // Read in FAT.
        let mut fat = Vec::<u32>::new();
        for index in 0..difat.len() {
            let mut sector = sectors.seek_to_sector(difat[index])?;
            for _ in 0..(sector_len / 4) {
                fat.push(sector.read_u32::<LittleEndian>()?);
            }
        }
        while fat.last() == Some(&consts::FREE_SECTOR) {
            fat.pop();
        }

        let mut allocator =
            Allocator::new(sectors, difat_sector_ids, difat, fat)?;

        // Read in MiniFAT.
        let minifat = {
            let mut chain = Chain::new(
                &mut allocator,
                first_minifat_sector,
                SectorInit::Fat,
            );
            if num_minifat_sectors as usize != chain.num_sectors() {
                invalid_data!(
                    "Incorrect MiniFAT chain length \
                               (header says {}, actual is {})",
                    num_minifat_sectors,
                    chain.num_sectors()
                );
            }
            let num_minifat_entries = (chain.len() / 4) as usize;
            let mut minifat = Vec::<u32>::with_capacity(num_minifat_entries);
            for _ in 0..num_minifat_entries {
                minifat.push(chain.read_u32::<LittleEndian>()?);
            }
            while minifat.last() == Some(&consts::FREE_SECTOR) {
                minifat.pop();
            }
            minifat
        };

        let mut comp = CompoundFile {
            allocator,
            minifat,
            minifat_start_sector: first_minifat_sector,
            directory: Vec::new(),
            directory_start_sector: first_dir_sector,
        };
        comp.validate_minifat()?;

        // Read in directory.
        let mut current_dir_sector = first_dir_sector;
        while current_dir_sector != END_OF_CHAIN {
            {
                let mut sector =
                    comp.allocator.seek_to_sector(current_dir_sector)?;
                for _ in 0..version.dir_entries_per_sector() {
                    comp.directory
                        .push(DirEntry::read_from(&mut sector, version)?);
                }
            }
            current_dir_sector = comp.allocator.next(current_dir_sector);
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
    pub fn create_with_version(
        version: Version,
        mut inner: F,
    ) -> io::Result<CompoundFile<F>> {
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
        let fat: Vec<u32> = vec![consts::FAT_SECTOR, END_OF_CHAIN];
        for &entry in fat.iter() {
            inner.write_u32::<LittleEndian>(entry)?;
        }
        for _ in fat.len()..(sector_len / 4) {
            inner.write_u32::<LittleEndian>(consts::FREE_SECTOR)?;
        }
        let difat: Vec<u32> = vec![0];
        let difat_sector_ids: Vec<u32> = vec![];

        // Write directory sector:
        let root_dir_entry = DirEntry {
            name: consts::ROOT_DIR_NAME.to_string(),
            obj_type: consts::OBJ_TYPE_ROOT,
            color: consts::COLOR_BLACK,
            left_sibling: NO_STREAM,
            right_sibling: NO_STREAM,
            child: NO_STREAM,
            clsid: Uuid::nil(),
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

        let sectors = Sectors::new(version, 3 * sector_len as u64, inner);
        let allocator = Allocator::new(sectors, difat_sector_ids, difat, fat)
            .expect("allocator");
        Ok(CompoundFile {
            allocator,
            minifat: vec![],
            minifat_start_sector: END_OF_CHAIN,
            directory: vec![root_dir_entry],
            directory_start_sector: 1,
        })
    }

    /// Creates a new, empty storage object (i.e. "directory") at the provided
    /// path.  The parent storage object must already exist.
    pub fn create_storage<P: AsRef<Path>>(
        &mut self,
        path: P,
    ) -> io::Result<()> {
        self.create_storage_with_path(path.as_ref())
    }

    fn create_storage_with_path(&mut self, path: &Path) -> io::Result<()> {
        let mut names = internal::path::name_chain_from_path(path)?;
        if let Some(stream_id) = self.stream_id_for_name_chain(&names) {
            let path = internal::path::path_from_name_chain(&names);
            if self.dir_entry(stream_id).obj_type != consts::OBJ_TYPE_STREAM {
                already_exists!(
                    "Cannot create storage at {:?} because a \
                                 storage already exists there",
                    path
                );
            } else {
                already_exists!(
                    "Cannot create storage at {:?} because a \
                                 stream already exists there",
                    path
                );
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

    /// Recursively creates a storage and all of its parent storages if they
    /// are missing.
    pub fn create_storage_all<P: AsRef<Path>>(
        &mut self,
        path: P,
    ) -> io::Result<()> {
        self.create_storage_all_with_path(path.as_ref())
    }

    fn create_storage_all_with_path(&mut self, path: &Path) -> io::Result<()> {
        let names = internal::path::name_chain_from_path(path)?;
        for length in 1..(names.len() + 1) {
            let prefix_path =
                internal::path::path_from_name_chain(&names[..length]);
            if self.is_storage(&prefix_path) {
                continue;
            }
            self.create_storage_with_path(&prefix_path)?;
        }
        Ok(())
    }

    /// Removes the storage object at the provided path.  The storage object
    /// must exist and have no children.
    pub fn remove_storage<P: AsRef<Path>>(
        &mut self,
        path: P,
    ) -> io::Result<()> {
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

    /// Recursively removes a storage and all of its children.  If called on
    /// the root storage, recursively removes all of its children but not the
    /// root storage itself (which cannot be removed).
    pub fn remove_storage_all<P: AsRef<Path>>(
        &mut self,
        path: P,
    ) -> io::Result<()> {
        self.remove_storage_all_with_path(path.as_ref())
    }

    fn remove_storage_all_with_path(&mut self, path: &Path) -> io::Result<()> {
        let mut stack = Vec::<Entry>::new();
        for entry in self.walk_storage_with_path(path)? {
            stack.push(entry);
        }
        while let Some(entry) = stack.pop() {
            if entry.is_stream() {
                self.remove_stream_with_path(entry.path())?;
            } else if !entry.is_root() {
                self.remove_storage_with_path(entry.path())?;
            }
        }
        Ok(())
    }

    /// Sets the CLSID for the storage object at the provided path.  (To get
    /// the current CLSID for a storage object, use
    /// `self.entry(path)?.clsid()`.)
    pub fn set_storage_clsid<P: AsRef<Path>>(
        &mut self,
        path: P,
        clsid: Uuid,
    ) -> io::Result<()> {
        self.set_storage_clsid_with_path(path.as_ref(), clsid)
    }

    fn set_storage_clsid_with_path(
        &mut self,
        path: &Path,
        clsid: Uuid,
    ) -> io::Result<()> {
        let names = internal::path::name_chain_from_path(path)?;
        let stream_id = match self.stream_id_for_name_chain(&names) {
            Some(stream_id) => stream_id,
            None => not_found!(
                "No such storage: {:?}",
                internal::path::path_from_name_chain(&names)
            ),
        };
        {
            let dir_entry = self.dir_entry_mut(stream_id);
            if dir_entry.obj_type == consts::OBJ_TYPE_STREAM {
                invalid_input!(
                    "Not a storage: {:?}",
                    internal::path::path_from_name_chain(&names)
                );
            }
            dir_entry.clsid = clsid;
        }
        let mut sector = self.seek_within_dir_entry(stream_id, 80)?;
        DirEntry::write_clsid(&mut sector, &clsid)?;
        Ok(())
    }

    /// Creates and returns a new, empty stream object at the provided path.
    /// If a stream already exists at that path, it will be replaced by the new
    /// stream.  The parent storage object must already exist.
    pub fn create_stream<P: AsRef<Path>>(
        &mut self,
        path: P,
    ) -> io::Result<Stream<F>> {
        self.create_stream_with_path(path.as_ref(), true)
    }

    /// Creates and returns a new, empty stream object at the provided path.
    /// Returns an error if a stream already exists at that path.  The parent
    /// storage object must already exist.
    pub fn create_new_stream<P: AsRef<Path>>(
        &mut self,
        path: P,
    ) -> io::Result<Stream<F>> {
        self.create_stream_with_path(path.as_ref(), false)
    }

    fn create_stream_with_path(
        &mut self,
        path: &Path,
        overwrite: bool,
    ) -> io::Result<Stream<F>> {
        let mut names = internal::path::name_chain_from_path(path)?;
        if let Some(stream_id) = self.stream_id_for_name_chain(&names) {
            if self.dir_entry(stream_id).obj_type != consts::OBJ_TYPE_STREAM {
                already_exists!(
                    "Cannot create stream at {:?} because a \
                                 storage already exists there",
                    internal::path::path_from_name_chain(&names)
                );
            } else if !overwrite {
                already_exists!(
                    "Cannot create new stream at {:?} because a \
                                 stream already exists there",
                    internal::path::path_from_name_chain(&names)
                );
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
    pub fn remove_stream<P: AsRef<Path>>(
        &mut self,
        path: P,
    ) -> io::Result<()> {
        self.remove_stream_with_path(path.as_ref())
    }

    fn remove_stream_with_path(&mut self, path: &Path) -> io::Result<()> {
        let mut names = internal::path::name_chain_from_path(path)?;
        let stream_id = match self.stream_id_for_name_chain(&names) {
            Some(parent_id) => parent_id,
            None => not_found!("No such stream: {:?}", path),
        };
        let (start_sector_id, is_in_mini_stream) = {
            let dir_entry = self.dir_entry(stream_id);
            if dir_entry.obj_type != consts::OBJ_TYPE_STREAM {
                invalid_input!("Not a stream: {:?}", path);
            }
            debug_assert_eq!(dir_entry.child, NO_STREAM);
            (
                dir_entry.start_sector,
                dir_entry.stream_len < consts::MINI_STREAM_CUTOFF as u64,
            )
        };
        if is_in_mini_stream {
            let mut mini_sector_id = start_sector_id;
            while mini_sector_id != END_OF_CHAIN {
                let next = self.minifat[mini_sector_id as usize];
                self.free_mini_sector(mini_sector_id)?;
                mini_sector_id = next;
            }
        } else {
            self.allocator.free_chain(start_sector_id)?;
        }
        debug_assert!(!names.is_empty());
        let name = names.pop().unwrap();
        let parent_id = self.stream_id_for_name_chain(&names).unwrap();
        self.remove_dir_entry(parent_id, name)?;
        Ok(())
    }

    /// Sets the user-defined bitflags for the object at the provided path.
    /// (To get the current state bits for an object, use
    /// `self.entry(path)?.state_bits()`.)
    pub fn set_state_bits<P: AsRef<Path>>(
        &mut self,
        path: P,
        bits: u32,
    ) -> io::Result<()> {
        self.set_state_bits_with_path(path.as_ref(), bits)
    }

    fn set_state_bits_with_path(
        &mut self,
        path: &Path,
        bits: u32,
    ) -> io::Result<()> {
        let names = internal::path::name_chain_from_path(path)?;
        let stream_id = match self.stream_id_for_name_chain(&names) {
            Some(stream_id) => stream_id,
            None => not_found!(
                "No such object: {:?}",
                internal::path::path_from_name_chain(&names)
            ),
        };
        self.dir_entry_mut(stream_id).state_bits = bits;
        let mut sector = self.seek_within_dir_entry(stream_id, 96)?;
        sector.write_u32::<LittleEndian>(bits)?;
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
            debug_assert_ne!(
                self.dir_entry(stream_id).obj_type,
                consts::OBJ_TYPE_ROOT
            );
            let now = internal::time::current_timestamp();
            self.dir_entry_mut(stream_id).modified_time = now;
            let mut sector = self.seek_within_dir_entry(stream_id, 108)?;
            sector.write_u64::<LittleEndian>(now)?;
        }
        Ok(())
    }

    /// Flushes all changes to the underlying file.
    pub fn flush(&mut self) -> io::Result<()> {
        self.allocator.flush()
    }

    /// Given the starting mini sector of a mini chain, copies the data in that
    /// chain into a newly-allocated regular sector chain, frees the mini
    /// chain, and returns the start sector of the new chain.
    fn migrate_out_of_mini_stream(
        &mut self,
        start_mini_sector: u32,
    ) -> io::Result<u32> {
        debug_assert_ne!(start_mini_sector, END_OF_CHAIN);
        let mut mini_sectors = Vec::new();
        let mut current_mini_sector = start_mini_sector;
        while current_mini_sector != END_OF_CHAIN {
            mini_sectors.push(current_mini_sector);
            current_mini_sector = self.minifat[current_mini_sector as usize];
        }
        debug_assert!(!mini_sectors.is_empty());
        let sector_len = self.allocator.sector_len();
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
                    new_start_sector =
                        self.allocator.begin_chain(SectorInit::Zero)?;
                    new_start_sector
                } else {
                    self.allocator
                        .extend_chain(new_start_sector, SectorInit::Zero)?
                };
                let mut sector = self.allocator.seek_to_sector(new_sector)?;
                sector.write_all(&data[0..data_start])?;
                data_start = 0;
            }
        }
        debug_assert_ne!(new_start_sector, END_OF_CHAIN);
        Ok(new_start_sector)
    }

    /// Given the starting mini sector (or any internal mini sector) of a mini
    /// chain, extends the end of that chain by one mini sector and returns the
    /// new mini sector number, updating the MiniFAT as necessary.
    fn extend_mini_chain(
        &mut self,
        start_mini_sector: u32,
    ) -> io::Result<u32> {
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
        let minifat_entries_per_sector = self.allocator.sector_len() / 4;
        let num_minifat_sectors =
            (self.minifat.len() / minifat_entries_per_sector) as u32;
        if self.minifat_start_sector == END_OF_CHAIN {
            debug_assert!(self.minifat.is_empty());
            debug_assert_eq!(num_minifat_sectors, 0);
            self.minifat_start_sector =
                self.allocator.begin_chain(SectorInit::Fat)?;
            let mut header = self.allocator.seek_within_header(60)?;
            header.write_u32::<LittleEndian>(self.minifat_start_sector)?;
            header.write_u32::<LittleEndian>(num_minifat_sectors + 1)?;
        } else if self.minifat.len() % minifat_entries_per_sector == 0 {
            let start = self.minifat_start_sector;
            self.allocator.extend_chain(start, SectorInit::Fat)?;
            let mut header = self.allocator.seek_within_header(64)?;
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
            self.allocator.extend_chain(start_sector, SectorInit::Dir)?;
        }
        // Add a new entry to the end of the directory and return it.
        let stream_id = self.directory.len() as u32;
        self.directory.push(unallocated_dir_entry);
        Ok(stream_id)
    }

    /// Adds a new mini sector to the end of the mini stream.
    fn append_mini_sector(&mut self) -> io::Result<()> {
        let mini_stream_start_sector = self.root_dir_entry().start_sector;
        let mini_stream_len = self.root_dir_entry().stream_len;
        debug_assert_eq!(mini_stream_len % consts::MINI_SECTOR_LEN as u64, 0);
        let sector_len = self.allocator.sector_len();

        // If the mini stream doesn't have room for new mini sector, add
        // another regular sector to its chain.
        if mini_stream_start_sector == END_OF_CHAIN {
            debug_assert_eq!(mini_stream_len, 0);
            let start_sector = self.allocator.begin_chain(SectorInit::Zero)?;
            self.root_dir_entry_mut().start_sector = start_sector;
            let mut sector =
                self.seek_within_dir_entry(consts::ROOT_STREAM_ID, 116)?;
            sector.write_u32::<LittleEndian>(start_sector)?;
        } else if mini_stream_len % sector_len as u64 == 0 {
            self.allocator
                .extend_chain(mini_stream_start_sector, SectorInit::Zero)?;
        }

        // Update length of mini stream in root directory entry.
        self.root_dir_entry_mut().stream_len += consts::MINI_SECTOR_LEN as u64;
        let mini_stream_len = self.root_dir_entry().stream_len;
        let mut sector =
            self.seek_within_dir_entry(consts::ROOT_STREAM_ID, 120)?;
        sector.write_u64::<LittleEndian>(mini_stream_len)?;
        Ok(())
    }

    /// Inserts a new directory entry into the tree under the specified parent
    /// entry.
    fn insert_dir_entry(
        &mut self,
        parent_id: u32,
        name: &str,
        obj_type: u8,
    ) -> io::Result<u32> {
        debug_assert_ne!(obj_type, consts::OBJ_TYPE_UNALLOCATED);
        // Create a new directory entry.
        let stream_id = self.allocate_dir_entry()?;
        let now = internal::time::current_timestamp();
        *self.dir_entry_mut(stream_id) = DirEntry {
            name: name.to_string(),
            obj_type,
            color: consts::COLOR_BLACK,
            left_sibling: NO_STREAM,
            right_sibling: NO_STREAM,
            child: NO_STREAM,
            clsid: Uuid::nil(),
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
    fn remove_dir_entry(
        &mut self,
        parent_id: u32,
        name: &str,
    ) -> io::Result<()> {
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
                debug_assert_eq!(
                    self.dir_entry(sibling_id).right_sibling,
                    stream_id
                );
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

    /// Sets `self.minifat[index] = value`, and also writes that change to the
    /// underlying file.  The `index` must be <= `self.minifat.len()`.
    fn set_minifat(&mut self, index: u32, value: u32) -> io::Result<()> {
        debug_assert!(index as usize <= self.minifat.len());
        let mut chain = Chain::new(
            &mut self.allocator,
            self.minifat_start_sector,
            SectorInit::Fat,
        );
        chain.seek(SeekFrom::Start((index as u64) * 4))?;
        chain.write_u32::<LittleEndian>(value)?;
        if (index as usize) == self.minifat.len() {
            self.minifat.push(value);
        } else {
            self.minifat[index as usize] = value;
        }
        Ok(())
    }

    fn write_dir_entry(&mut self, stream_id: u32) -> io::Result<()> {
        let mut chain = Chain::new(
            &mut self.allocator,
            self.directory_start_sector,
            SectorInit::Dir,
        );
        let offset = (consts::DIR_ENTRY_LEN as u64) * (stream_id as u64);
        chain.seek(SeekFrom::Start(offset))?;
        self.directory[stream_id as usize].write_to(&mut chain)
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
    finisher: Option<Box<dyn Finish<F>>>,
}

impl<'a, F> Stream<'a, F> {
    fn dir_entry(&self) -> &DirEntry {
        self.comp.dir_entry(self.stream_id)
    }

    fn dir_entry_mut(&mut self) -> &mut DirEntry {
        self.comp.dir_entry_mut(self.stream_id)
    }

    /// Returns the current length of the stream, in bytes.
    pub fn len(&self) -> u64 {
        self.dir_entry().stream_len
    }

    fn is_in_mini_stream(&self) -> bool {
        self.len() < consts::MINI_STREAM_CUTOFF as u64
    }

    fn sector_len(&self) -> usize {
        if self.is_in_mini_stream() {
            consts::MINI_SECTOR_LEN
        } else {
            self.comp.allocator.sector_len()
        }
    }
}

impl<'a, F: Seek> Stream<'a, F> {
    fn new(
        comp: &'a mut CompoundFile<F>,
        stream_id: u32,
    ) -> io::Result<Stream<'a, F>> {
        let start_sector = comp.dir_entry(stream_id).start_sector;
        Ok(Stream {
            comp,
            stream_id,
            offset_from_start: 0,
            offset_within_sector: 0,
            current_sector: start_sector,
            finisher: None,
        })
    }

    fn seek_to_current_position(&mut self) -> io::Result<Sector<F>> {
        debug_assert_ne!(self.current_sector, END_OF_CHAIN);
        if self.is_in_mini_stream() {
            self.comp.seek_within_mini_sector(
                self.current_sector,
                self.offset_within_sector as u64,
            )
        } else {
            self.comp.allocator.seek_within_sector(
                self.current_sector,
                self.offset_within_sector as u64,
            )
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
            self.comp.allocator.next(self.current_sector)
        };
    }
}

impl<'a, F: Read + Write + Seek> Stream<'a, F> {
    /// Truncates or extends the stream, updating the size of this stream to
    /// become `size`.
    ///
    /// If `size` is less than the stream's current size, then the stream will
    /// be shrunk.  If it is greater than the stream's current size, then the
    /// stream will be padded with zero bytes.
    ///
    /// Does not change the current read/write position within the stream,
    /// unless the stream is truncated to before the current position, in which
    /// case the position becomes the new end of the stream.
    pub fn set_len(&mut self, size: u64) -> io::Result<()> {
        let current_size = self.len();
        if size == current_size {
            Ok(()) // Do nothing.
        } else if size > current_size {
            let current_pos = self.seek(SeekFrom::Current(0))?;
            self.seek(SeekFrom::End(0))?;
            io::copy(&mut io::repeat(0).take(size - current_size), self)?;
            self.seek(SeekFrom::Start(current_pos))?;
            Ok(())
        } else {
            debug_assert!(current_size > 0);
            self.mark_modified();
            let offset_from_start = cmp::min(self.offset_from_start, size);
            self.seek(SeekFrom::Start(size))?;
            let mut sector = self.current_sector;
            debug_assert_ne!(sector, END_OF_CHAIN);
            if self.is_in_mini_stream() {
                if size == 0 {
                    self.dir_entry_mut().start_sector = END_OF_CHAIN;
                    self.current_sector = END_OF_CHAIN;
                } else {
                    if size % self.sector_len() as u64 == 0 {
                        self.current_sector = END_OF_CHAIN;
                    }
                    let next = self.comp.minifat[sector as usize];
                    self.comp.set_minifat(sector, END_OF_CHAIN)?;
                    sector = next;
                }
                while sector != END_OF_CHAIN {
                    let next = self.comp.minifat[sector as usize];
                    self.comp.free_mini_sector(sector)?;
                    sector = next;
                }
            } else {
                if size == 0 {
                    debug_assert_eq!(sector, self.dir_entry().start_sector);
                    self.dir_entry_mut().start_sector = END_OF_CHAIN;
                    self.current_sector = END_OF_CHAIN;
                    self.comp.allocator.free_chain(sector)?;
                } else {
                    if size % self.sector_len() as u64 == 0 {
                        self.current_sector = END_OF_CHAIN;
                    }
                    self.comp.allocator.free_chain_after(sector)?;
                }
            }
            self.dir_entry_mut().stream_len = size;
            self.seek(SeekFrom::Start(offset_from_start))?;
            Ok(())
        }
    }

    fn mark_modified(&mut self) {
        if self.finisher.is_none() {
            let finisher: Box<dyn Finish<F>> =
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
            invalid_input!(
                "Cannot seek to {}, stream length is {}",
                new_pos,
                total_len
            );
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
                    self.comp.allocator.next(sector)
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
        let bytes_read =
            self.seek_to_current_position()?.read(&mut buf[0..max_len])?;
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
                let sector_id =
                    self.comp.allocate_mini_sector(END_OF_CHAIN)?;
                self.dir_entry_mut().start_sector = sector_id;
                sector_id
            } else if self.is_in_mini_stream() {
                self.comp.extend_mini_chain(start_sector)?
            } else {
                self.comp
                    .allocator
                    .extend_chain(start_sector, SectorInit::Zero)?
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
                debug_assert_eq!(
                    self.dir_entry().stream_len,
                    consts::MINI_STREAM_CUTOFF as u64
                );
                let old_start_sector = self.dir_entry().start_sector;
                let new_start_sector =
                    self.comp.migrate_out_of_mini_stream(old_start_sector)?;
                self.dir_entry_mut().start_sector = new_start_sector;
                let sector_len = self.sector_len();
                debug_assert_eq!(
                    self.offset_from_start % sector_len as u64,
                    0
                );
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
        self.comp.allocator.flush()
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
        UpdateDirEntry { stream_id }
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
