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

use std::fmt;
use std::fs;
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::mem::size_of;
use std::path::{Path, PathBuf};
use std::sync::{Arc, RwLock, RwLockReadGuard, RwLockWriteGuard};

use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use fnv::FnvHashSet;
use uuid::Uuid;

use crate::internal::consts;
use crate::internal::{
    Allocator, DirEntry, Directory, EntriesOrder, Header, MiniAllocator,
    ObjType, SectorInit, Sectors, Timestamp, Validation,
};
pub use crate::internal::{Entries, Entry, Stream, Version};

#[macro_use]
mod internal;

//===========================================================================//

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

//===========================================================================//

/// A compound file, backed by an underlying reader/writer (such as a
/// [`File`](https://doc.rust-lang.org/std/fs/struct.File.html) or
/// [`Cursor`](https://doc.rust-lang.org/std/io/struct.Cursor.html)).
pub struct CompoundFile<F> {
    minialloc: Arc<RwLock<MiniAllocator<F>>>,
}

impl<F> CompoundFile<F> {
    fn minialloc(&self) -> RwLockReadGuard<MiniAllocator<F>> {
        self.minialloc.read().unwrap()
    }

    fn minialloc_mut(&mut self) -> RwLockWriteGuard<MiniAllocator<F>> {
        self.minialloc.write().unwrap()
    }

    /// Returns the CFB format version used for this compound file.
    pub fn version(&self) -> Version {
        self.minialloc().version()
    }

    fn stream_id_for_name_chain(&self, names: &[&str]) -> Option<u32> {
        self.minialloc().stream_id_for_name_chain(names)
    }

    /// Returns information about the root storage object.  This is equivalent
    /// to `self.entry("/").unwrap()` (but always succeeds).
    pub fn root_entry(&self) -> Entry {
        Entry::new(self.minialloc().root_dir_entry(), PathBuf::from("/"))
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
        Ok(Entry::new(self.minialloc().dir_entry(stream_id), path))
    }

    /// Returns an iterator over the entries within the root storage object.
    /// This is equivalent to `self.read_storage("/").unwrap()` (but always
    /// succeeds).
    pub fn read_root_storage(&self) -> Entries<F> {
        let start = self.minialloc().root_dir_entry().child;
        Entries::new(
            EntriesOrder::Nonrecursive,
            &self.minialloc,
            internal::path::path_from_name_chain(&[]),
            start,
        )
    }

    /// Returns an iterator over the entries within a storage object.
    pub fn read_storage<P: AsRef<Path>>(
        &self,
        path: P,
    ) -> io::Result<Entries<F>> {
        self.read_storage_with_path(path.as_ref())
    }

    fn read_storage_with_path(&self, path: &Path) -> io::Result<Entries<F>> {
        let names = internal::path::name_chain_from_path(path)?;
        let path = internal::path::path_from_name_chain(&names);
        let stream_id = match self.stream_id_for_name_chain(&names) {
            Some(stream_id) => stream_id,
            None => not_found!("No such storage: {:?}", path),
        };
        let start = {
            let minialloc = self.minialloc();
            let dir_entry = minialloc.dir_entry(stream_id);
            if dir_entry.obj_type == ObjType::Stream {
                invalid_input!("Not a storage: {:?}", path);
            }
            debug_assert!(
                dir_entry.obj_type == ObjType::Storage
                    || dir_entry.obj_type == ObjType::Root
            );
            dir_entry.child
        };
        Ok(Entries::new(
            EntriesOrder::Nonrecursive,
            &self.minialloc,
            path,
            start,
        ))
    }

    /// Returns an iterator over all entries within the compound file, starting
    /// from and including the root entry.  The iterator walks the storage tree
    /// in a preorder traversal.  This is equivalent to
    /// `self.walk_storage("/").unwrap()` (but always succeeds).
    pub fn walk(&self) -> Entries<F> {
        Entries::new(
            EntriesOrder::Preorder,
            &self.minialloc,
            internal::path::path_from_name_chain(&[]),
            consts::ROOT_STREAM_ID,
        )
    }

    /// Returns an iterator over all entries under a storage subtree, including
    /// the given path itself.  The iterator walks the storage tree in a
    /// preorder traversal.
    pub fn walk_storage<P: AsRef<Path>>(
        &self,
        path: P,
    ) -> io::Result<Entries<F>> {
        self.walk_storage_with_path(path.as_ref())
    }

    fn walk_storage_with_path(&self, path: &Path) -> io::Result<Entries<F>> {
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
            &self.minialloc,
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
                    self.minialloc().dir_entry(stream_id).obj_type
                        == ObjType::Stream
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
                    self.minialloc().dir_entry(stream_id).obj_type
                        != ObjType::Stream
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
        // We only ever retain Weak copies of the CompoundFile's minialloc Rc
        // (e.g. in Stream structs), so the Rc::try_unwrap() should always
        // succeed.
        match Arc::try_unwrap(self.minialloc) {
            Ok(ref_cell) => ref_cell.into_inner().unwrap().into_inner(),
            Err(_) => unreachable!(),
        }
    }
}

impl<F: Seek> CompoundFile<F> {
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
        if self.minialloc().dir_entry(stream_id).obj_type != ObjType::Stream {
            invalid_input!("Not a stream: {:?}", path);
        }
        Ok(Stream::new(&self.minialloc, stream_id))
    }
}

impl<F: Read + Seek> CompoundFile<F> {
    /// Opens an existing compound file, using the underlying reader.  If the
    /// underlying reader also supports the `Write` trait, then the
    /// `CompoundFile` object will be writable as well.
    pub fn open(inner: F) -> io::Result<CompoundFile<F>> {
        CompoundFile::open_internal(inner, Validation::Permissive)
    }

    /// Like `open()`, but is stricter when parsing and will return an error if
    /// the file violates the CFB spec in any way (which many CFB files in the
    /// wild do).  This is mainly useful for validating a CFB file or
    /// implemention (such as this crate itself) to help ensure compatibility
    /// with other readers.
    pub fn open_strict(inner: F) -> io::Result<CompoundFile<F>> {
        CompoundFile::open_internal(inner, Validation::Strict)
    }

    fn open_internal(
        mut inner: F,
        validation: Validation,
    ) -> io::Result<CompoundFile<F>> {
        let inner_len = inner.seek(SeekFrom::End(0))?;
        if inner_len < consts::HEADER_LEN as u64 {
            invalid_data!(
                "Invalid CFB file ({} bytes is too small)",
                inner_len
            );
        }
        inner.seek(SeekFrom::Start(0))?;

        let header = Header::read_from(&mut inner, validation)?;
        let sector_len = header.version.sector_len();
        if inner_len
            > ((consts::MAX_REGULAR_SECTOR + 1) as u64) * (sector_len as u64)
        {
            invalid_data!(
                "Invalid CFB file ({} bytes is too large)",
                inner_len
            );
        }

        if inner_len < header.version.sector_len() as u64 {
            invalid_data!(
                "Invalid CFB file (length of {} < sector length of {})",
                inner_len,
                header.version.sector_len()
            );
        }
        let mut sectors = Sectors::new(header.version, inner_len, inner);
        let num_sectors = sectors.num_sectors();

        // Read in DIFAT.
        let mut difat = Vec::<u32>::new();
        difat.extend_from_slice(&header.initial_difat_entries);
        let mut seen_sector_ids = FnvHashSet::default();
        let mut difat_sector_ids = Vec::new();
        let mut current_difat_sector = header.first_difat_sector;
        while current_difat_sector != consts::END_OF_CHAIN
            && current_difat_sector != consts::FREE_SECTOR
        {
            if current_difat_sector > consts::MAX_REGULAR_SECTOR {
                invalid_data!(
                    "DIFAT chain includes invalid sector index {}",
                    current_difat_sector
                );
            } else if current_difat_sector >= num_sectors {
                invalid_data!(
                    "DIFAT chain includes sector index {}, but sector count \
                     is only {}",
                    current_difat_sector,
                    num_sectors
                );
            }
            if seen_sector_ids.contains(&current_difat_sector) {
                invalid_data!(
                    "DIFAT chain includes duplicate sector index {}",
                    current_difat_sector,
                );
            }
            seen_sector_ids.insert(current_difat_sector);
            difat_sector_ids.push(current_difat_sector);
            let mut sector = sectors.seek_to_sector(current_difat_sector)?;
            for _ in 0..(sector_len / size_of::<u32>() - 1) {
                let next = sector.read_u32::<LittleEndian>()?;
                if next != consts::FREE_SECTOR
                    && next > consts::MAX_REGULAR_SECTOR
                {
                    invalid_data!(
                        "DIFAT refers to invalid sector index {}",
                        next
                    );
                }
                difat.push(next);
            }
            current_difat_sector = sector.read_u32::<LittleEndian>()?;
            if validation.is_strict()
                && current_difat_sector == consts::FREE_SECTOR
            {
                invalid_data!(
                    "DIFAT chain must terminate with {}, not {}",
                    consts::END_OF_CHAIN,
                    consts::FREE_SECTOR
                );
            }
        }
        if validation.is_strict()
            && header.num_difat_sectors as usize != difat_sector_ids.len()
        {
            invalid_data!(
                "Incorrect DIFAT chain length (header says {}, actual is {})",
                header.num_difat_sectors,
                difat_sector_ids.len()
            );
        }
        while difat.last() == Some(&consts::FREE_SECTOR) {
            difat.pop();
        }
        if validation.is_strict()
            && header.num_fat_sectors as usize != difat.len()
        {
            invalid_data!(
                "Incorrect number of FAT sectors (header says {}, DIFAT says \
                 {})",
                header.num_fat_sectors,
                difat.len()
            );
        }

        // Read in FAT.
        let mut fat = Vec::<u32>::new();
        for &sector_index in difat.iter() {
            if sector_index >= num_sectors {
                invalid_data!(
                    "DIFAT refers to sector {}, but sector count is only {}",
                    sector_index,
                    num_sectors
                );
            }
            let mut sector = sectors.seek_to_sector(sector_index)?;
            for _ in 0..(sector_len / size_of::<u32>()) {
                fat.push(sector.read_u32::<LittleEndian>()?);
            }
        }
        // If the number of sectors in the file is not a multiple of the number
        // of FAT entries per sector, then the last FAT sector must be padded
        // with FREE_SECTOR entries (see MS-CFB section 2.3).  However, some
        // CFB implementations incorrectly pad the last FAT sector with zeros
        // (see https://github.com/mdsteele/rust-cfb/issues/8), so we allow
        // this under Permissive validation.  Since zero is normally a
        // meaningful FAT entry (referring to sector 0), we only want to strip
        // zeros from the end of the FAT if they are beyond the number of
        // sectors in the file.
        if !validation.is_strict() {
            while fat.len() > num_sectors as usize && fat.last() == Some(&0) {
                fat.pop();
            }
        }
        // Strip FREE_SECTOR entries from the end of the FAT.  Unlike the zero
        // case above, we can remove these even if it makes the number of FAT
        // entries less than the number of sectors in the file; the allocator
        // will implicitly treat these extra sectors as free.
        while fat.last() == Some(&consts::FREE_SECTOR) {
            fat.pop();
        }

        let mut allocator =
            Allocator::new(sectors, difat_sector_ids, difat, fat, validation)?;

        // Read in directory.
        let mut dir_entries = Vec::<DirEntry>::new();
        let mut seen_dir_sectors = FnvHashSet::default();
        let mut current_dir_sector = header.first_dir_sector;
        let mut dir_sector_count = 1;
        while current_dir_sector != consts::END_OF_CHAIN {
            if validation.is_strict()
                && header.version == Version::V4
                && dir_sector_count > header.num_dir_sectors
            {
                invalid_data!(
                    "Directory chain includes at least {} sectors which is greater than header num_dir_sectors {}",
                    dir_sector_count,
                    header.num_dir_sectors
                );
            }
            if current_dir_sector > consts::MAX_REGULAR_SECTOR {
                invalid_data!(
                    "Directory chain includes invalid sector index {}",
                    current_dir_sector
                );
            } else if current_dir_sector >= num_sectors {
                invalid_data!(
                    "Directory chain includes sector index {}, but sector \
                     count is only {}",
                    current_dir_sector,
                    num_sectors
                );
            }
            if seen_dir_sectors.contains(&current_dir_sector) {
                invalid_data!(
                    "Directory chain includes duplicate sector index {}",
                    current_dir_sector,
                );
            }
            seen_dir_sectors.insert(current_dir_sector);
            {
                let mut sector =
                    allocator.seek_to_sector(current_dir_sector)?;
                for _ in 0..header.version.dir_entries_per_sector() {
                    dir_entries.push(DirEntry::read_from(
                        &mut sector,
                        header.version,
                        validation,
                    )?);
                }
            }
            current_dir_sector = allocator.next(current_dir_sector)?;
            dir_sector_count += 1;
        }

        let mut directory = Directory::new(
            allocator,
            dir_entries,
            header.first_dir_sector,
            validation,
        )?;

        // Read in MiniFAT.
        let minifat = {
            let mut chain = directory
                .open_chain(header.first_minifat_sector, SectorInit::Fat)?;
            if validation.is_strict()
                && header.num_minifat_sectors as usize != chain.num_sectors()
            {
                invalid_data!(
                    "Incorrect MiniFAT chain length (header says {}, actual \
                     is {})",
                    header.num_minifat_sectors,
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

        let minialloc = MiniAllocator::new(
            directory,
            minifat,
            header.first_minifat_sector,
            validation,
        )?;

        Ok(CompoundFile { minialloc: Arc::new(RwLock::new(minialloc)) })
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
        let mut header = Header {
            version,
            // 2.2 requires this to be zero in V3
            num_dir_sectors: if version == Version::V3 { 0 } else { 1 },
            num_fat_sectors: 1,
            first_dir_sector: 1,
            first_minifat_sector: consts::END_OF_CHAIN,
            num_minifat_sectors: 0,
            first_difat_sector: consts::END_OF_CHAIN,
            num_difat_sectors: 0,
            initial_difat_entries: [consts::FREE_SECTOR;
                consts::NUM_DIFAT_ENTRIES_IN_HEADER],
        };
        header.initial_difat_entries[0] = 0;
        header.write_to(&mut inner)?;

        // Pad the header with zeroes so it's the length of a sector.
        let sector_len = version.sector_len();
        debug_assert!(sector_len >= consts::HEADER_LEN);
        if sector_len > consts::HEADER_LEN {
            inner.write_all(&vec![0; sector_len - consts::HEADER_LEN])?;
        }

        // Write FAT sector:
        let fat: Vec<u32> = vec![consts::FAT_SECTOR, consts::END_OF_CHAIN];
        for &entry in fat.iter() {
            inner.write_u32::<LittleEndian>(entry)?;
        }
        for _ in fat.len()..(sector_len / size_of::<u32>()) {
            inner.write_u32::<LittleEndian>(consts::FREE_SECTOR)?;
        }
        let difat: Vec<u32> = vec![0];
        let difat_sector_ids: Vec<u32> = vec![];

        // Write directory sector:
        let root_dir_entry = DirEntry::empty_root_entry();
        root_dir_entry.write_to(&mut inner)?;
        for _ in 1..version.dir_entries_per_sector() {
            DirEntry::unallocated().write_to(&mut inner)?;
        }

        let sectors = Sectors::new(version, 3 * sector_len as u64, inner);
        let allocator = Allocator::new(
            sectors,
            difat_sector_ids,
            difat,
            fat,
            Validation::Strict,
        )?;
        let directory = Directory::new(
            allocator,
            vec![root_dir_entry],
            1,
            Validation::Strict,
        )?;
        let minialloc = MiniAllocator::new(
            directory,
            vec![],
            consts::END_OF_CHAIN,
            Validation::Strict,
        )?;
        Ok(CompoundFile { minialloc: Arc::new(RwLock::new(minialloc)) })
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
            if self.minialloc().dir_entry(stream_id).obj_type
                != ObjType::Stream
            {
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
        self.minialloc_mut().insert_dir_entry(
            parent_id,
            name,
            ObjType::Storage,
        )?;
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
            let minialloc = self.minialloc();
            let dir_entry = minialloc.dir_entry(stream_id);
            if dir_entry.obj_type == ObjType::Root {
                invalid_input!("Cannot remove the root storage object");
            }
            if dir_entry.obj_type == ObjType::Stream {
                invalid_input!("Not a storage: {:?}", path);
            }
            debug_assert_eq!(dir_entry.obj_type, ObjType::Storage);
            if dir_entry.child != consts::NO_STREAM {
                invalid_input!("Storage is not empty: {:?}", path);
            }
        }
        debug_assert!(!names.is_empty());
        let name = names.pop().unwrap();
        let parent_id = self.stream_id_for_name_chain(&names).unwrap();
        self.minialloc_mut().remove_dir_entry(parent_id, name)?;
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
        let mut stack = self.walk_storage(path)?.collect::<Vec<Entry>>();
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
        let mut minialloc = self.minialloc_mut();
        if minialloc.dir_entry(stream_id).obj_type == ObjType::Stream {
            invalid_input!(
                "Not a storage: {:?}",
                internal::path::path_from_name_chain(&names)
            );
        }
        minialloc.with_dir_entry_mut(stream_id, |dir_entry| {
            dir_entry.clsid = clsid;
        })
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
            if self.minialloc().dir_entry(stream_id).obj_type
                != ObjType::Stream
            {
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
                let mut stream = Stream::new(&self.minialloc, stream_id);
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
        let new_stream_id = self.minialloc_mut().insert_dir_entry(
            parent_id,
            name,
            ObjType::Stream,
        )?;
        Ok(Stream::new(&self.minialloc, new_stream_id))
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
            let minialloc = self.minialloc();
            let dir_entry = minialloc.dir_entry(stream_id);
            if dir_entry.obj_type != ObjType::Stream {
                invalid_input!("Not a stream: {:?}", path);
            }
            debug_assert_eq!(dir_entry.child, consts::NO_STREAM);
            (
                dir_entry.start_sector,
                dir_entry.stream_len < consts::MINI_STREAM_CUTOFF as u64,
            )
        };
        if is_in_mini_stream {
            self.minialloc_mut().free_mini_chain(start_sector_id)?;
        } else {
            self.minialloc_mut().free_chain(start_sector_id)?;
        }
        debug_assert!(!names.is_empty());
        let name = names.pop().unwrap();
        let parent_id = self.stream_id_for_name_chain(&names).unwrap();
        self.minialloc_mut().remove_dir_entry(parent_id, name)?;
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
        self.minialloc_mut().with_dir_entry_mut(stream_id, |dir_entry| {
            dir_entry.state_bits = bits;
        })
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
            let mut minialloc = self.minialloc_mut();
            debug_assert_ne!(
                minialloc.dir_entry(stream_id).obj_type,
                ObjType::Root
            );
            minialloc.with_dir_entry_mut(stream_id, |dir_entry| {
                dir_entry.modified_time = Timestamp::now();
            })?;
        }
        Ok(())
    }

    /// Flushes all changes to the underlying file.
    pub fn flush(&mut self) -> io::Result<()> {
        self.minialloc_mut().flush()
    }
}

impl<F: fmt::Debug> fmt::Debug for CompoundFile<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("CompoundFile").field(self.minialloc().inner()).finish()
    }
}

//===========================================================================//

#[cfg(test)]
mod tests {
    use std::io::{self, Cursor, Seek, SeekFrom};
    use std::mem::size_of;
    use std::path::Path;

    use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};

    use crate::internal::{consts, DirEntry, Header, Version};

    use super::CompoundFile;

    fn make_cfb_file_with_zero_padded_fat() -> io::Result<Vec<u8>> {
        let version = Version::V3;
        let mut data = Vec::<u8>::new();
        let mut header = Header {
            version,
            num_dir_sectors: 0,
            num_fat_sectors: 1,
            first_dir_sector: 1,
            first_minifat_sector: consts::END_OF_CHAIN,
            num_minifat_sectors: 0,
            first_difat_sector: consts::END_OF_CHAIN,
            num_difat_sectors: 0,
            initial_difat_entries: [consts::FREE_SECTOR;
                consts::NUM_DIFAT_ENTRIES_IN_HEADER],
        };
        header.initial_difat_entries[0] = 0;
        header.write_to(&mut data)?;
        // Write FAT sector:
        let fat: Vec<u32> = vec![consts::FAT_SECTOR, consts::END_OF_CHAIN];
        for &entry in fat.iter() {
            data.write_u32::<LittleEndian>(entry)?;
        }
        // Pad the FAT sector with zeros instead of FREE_SECTOR.  Technically
        // this violates the MS-CFB spec (section 2.3), but apparently some CFB
        // implementations do this.
        for _ in fat.len()..(version.sector_len() / size_of::<u32>()) {
            data.write_u32::<LittleEndian>(0)?;
        }
        // Write directory sector:
        DirEntry::empty_root_entry().write_to(&mut data)?;
        for _ in 1..version.dir_entries_per_sector() {
            DirEntry::unallocated().write_to(&mut data)?;
        }
        Ok(data)
    }

    #[test]
    fn zero_padded_fat_strict() {
        let data = make_cfb_file_with_zero_padded_fat().unwrap();
        let result = CompoundFile::open_strict(Cursor::new(data));
        assert_eq!(
            result.err().unwrap().to_string(),
            "Malformed FAT (FAT has 128 entries, but file has only 2 sectors)"
        );
    }

    // Regression test for https://github.com/mdsteele/rust-cfb/issues/8.
    #[test]
    fn zero_padded_fat_permissive() {
        let data = make_cfb_file_with_zero_padded_fat().unwrap();
        // Despite the zero-padded FAT, we should be able to read this file
        // under Permissive validation.
        CompoundFile::open(Cursor::new(data)).expect("open");
    }

    // Regression test for https://github.com/mdsteele/rust-cfb/issues/52.
    #[test]
    fn update_num_dir_sectors() {
        // Create a CFB file with 2 sectors for the directory.
        let cursor = Cursor::new(Vec::new());
        let mut comp = CompoundFile::create(cursor).unwrap();
        // root + 31 entries in the first sector
        // 1 stream entry in the second sector
        for i in 0..32 {
            let path = format!("stream{}", i);
            let path = Path::new(&path);
            comp.create_stream(path).unwrap();
        }
        comp.flush().unwrap();

        // read num_dir_sectors from the header
        let mut cursor = comp.into_inner();
        cursor.seek(SeekFrom::Start(40)).unwrap();
        let num_dir_sectors = cursor.read_u32::<LittleEndian>().unwrap();
        assert_eq!(num_dir_sectors, 2);
    }
}

//===========================================================================//
