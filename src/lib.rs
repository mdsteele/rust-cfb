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

use fnv::FnvHashSet;
use uuid::Uuid;

use crate::internal::consts;
use crate::internal::DEFAULT_STREAM_MAX_BUFFER_SIZE;
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
    OpenOptions::new().open(path)
}

/// Opens an existing compound file at the given path in read-write mode.
pub fn open_rw<P: AsRef<Path>>(path: P) -> io::Result<CompoundFile<fs::File>> {
    OpenOptions::new().open_rw(path)
}

/// Creates a new compound file with no contents at the given path.
///
/// The returned `CompoundFile` object will be both readable and writable.  If
/// a file already exists at the given path, this will overwrite it.
pub fn create<P: AsRef<Path>>(path: P) -> io::Result<CompoundFile<fs::File>> {
    OpenOptions::new().create(path)
}

//===========================================================================//

/// Options for opening or creating a compound file.
pub struct OpenOptions {
    pub(crate) max_buffer_size: usize,
    pub(crate) validation: Validation,
}

impl OpenOptions {
    /// Creates a new `OpenOptions` with default settings.
    pub fn new() -> Self {
        OpenOptions::default()
    }

    /// Sets the maximum size of a stream's internal buffer.
    ///
    /// The buffer grows dynamically up to this limit. Larger limits can improve
    /// throughput for large streams, while smaller limits reduce peak memory
    /// usage. Values below the internal minimum are clamped up to that minimum.
    pub fn max_buffer_size(mut self, size: usize) -> Self {
        self.max_buffer_size = size;
        self
    }

    /// Any violation of the CFB spec will be treated as an error when parsing.
    pub fn strict(mut self) -> Self {
        self.validation = Validation::Strict;
        self
    }

    /// Opens an existing compound file at the given path in read-only mode.
    pub fn open<P: AsRef<Path>>(
        self,
        path: P,
    ) -> io::Result<CompoundFile<fs::File>> {
        self.open_with(fs::File::open(path)?)
    }

    /// Opens an existing compound file at the given path in read-write mode.
    pub fn open_rw<P: AsRef<Path>>(
        self,
        path: P,
    ) -> io::Result<CompoundFile<fs::File>> {
        let file = fs::OpenOptions::new().read(true).write(true).open(path)?;
        self.open_with(file)
    }

    /// Creates a new compound file with no contents at the given path.
    ///
    /// The returned `CompoundFile` object will be both readable and writable.
    /// If a file already exists at the given path, this will overwrite it.
    pub fn create<P: AsRef<Path>>(
        self,
        path: P,
    ) -> io::Result<CompoundFile<fs::File>> {
        let file = fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(true)
            .open(path)?;
        self.create_with(file)
    }

    /// Opens an existing compound file using the underlying reader.
    pub fn open_with<F: Read + Seek>(
        self,
        inner: F,
    ) -> io::Result<CompoundFile<F>> {
        CompoundFile::open_internal(
            inner,
            self.validation,
            self.max_buffer_size,
        )
    }

    /// Creates a new compound file with no contents using the underlying writer.
    pub fn create_with<F: Read + Write + Seek>(
        self,
        inner: F,
    ) -> io::Result<CompoundFile<F>> {
        CompoundFile::create_with_version_and_options(
            Version::V4,
            inner,
            self.max_buffer_size,
        )
    }
}

impl Default for OpenOptions {
    fn default() -> Self {
        OpenOptions {
            max_buffer_size: DEFAULT_STREAM_MAX_BUFFER_SIZE,
            validation: Validation::Permissive,
        }
    }
}

//===========================================================================//

/// A compound file, backed by an underlying reader/writer (such as a
/// [`File`](https://doc.rust-lang.org/std/fs/struct.File.html) or
/// [`Cursor`](https://doc.rust-lang.org/std/io/struct.Cursor.html)).
pub struct CompoundFile<F> {
    minialloc: Arc<RwLock<MiniAllocator<F>>>,
    max_buffer_size: usize,
}

impl<F> CompoundFile<F> {
    fn minialloc(&self) -> RwLockReadGuard<'_, MiniAllocator<F>> {
        self.minialloc.read().unwrap()
    }

    fn minialloc_mut(&mut self) -> RwLockWriteGuard<'_, MiniAllocator<F>> {
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
    pub fn read_root_storage(&self) -> Entries<'_, F> {
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
    ) -> io::Result<Entries<'_, F>> {
        self.read_storage_with_path(path.as_ref())
    }

    fn read_storage_with_path(
        &self,
        path: &Path,
    ) -> io::Result<Entries<'_, F>> {
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
    pub fn walk(&self) -> Entries<'_, F> {
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
    ) -> io::Result<Entries<'_, F>> {
        self.walk_storage_with_path(path.as_ref())
    }

    fn walk_storage_with_path(
        &self,
        path: &Path,
    ) -> io::Result<Entries<'_, F>> {
        let mut names = internal::path::name_chain_from_path(path)?;
        let stream_id = match self.stream_id_for_name_chain(&names) {
            Some(stream_id) => stream_id,
            None => not_found!(
                "No such object: {:?}",
                internal::path::path_from_name_chain(&names)
            ),
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
        Ok(Stream::new(&self.minialloc, stream_id, self.max_buffer_size))
    }
}

impl<F: Read + Seek> CompoundFile<F> {
    /// Opens an existing compound file, using the underlying reader.  If the
    /// underlying reader also supports the `Write` trait, then the
    /// `CompoundFile` object will be writable as well.
    pub fn open(inner: F) -> io::Result<CompoundFile<F>> {
        OpenOptions::new().open_with(inner)
    }

    /// Like `open()`, but is stricter when parsing and will return an error if
    /// the file violates the CFB spec in any way (which many CFB files in the
    /// wild do).  This is mainly useful for validating a CFB file or
    /// implementation (such as this crate itself) to help ensure compatibility
    /// with other readers.
    pub fn open_strict(inner: F) -> io::Result<CompoundFile<F>> {
        OpenOptions::new().strict().open_with(inner)
    }

    fn open_internal(
        mut inner: F,
        validation: Validation,
        max_buffer_size: usize,
    ) -> io::Result<CompoundFile<F>> {
        let inner_len = inner.seek(SeekFrom::End(0))?;
        if inner_len < consts::HEADER_LEN as u64 {
            invalid_data!(
                "Invalid CFB file ({} bytes is too small)",
                inner_len
            );
        }
        inner.seek(SeekFrom::Start(0))?;

        // 2.2 Compound File Header
        let header = Header::read_from(&mut inner, validation)?;
        // Major Version
        let sector_len = header.version.sector_len();
        if inner_len
            > (consts::MAX_REGULAR_SECTOR as u64 + 1) * (sector_len as u64)
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
                let next = sector.read_le_u32()?;
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
            current_difat_sector = sector.read_le_u32()?;
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
        // The DIFAT should be padded with FREE_SECTOR, but DIFAT sectors
        // may instead instead be incorrectly zero padded (see
        // https://github.com/mdsteele/rust-cfb/issues/41).
        // In case num_fat_sectors is not reliable, only remove zeroes,
        // and don't remove sectors from the header DIFAT.
        if !validation.is_strict() {
            while difat.len() > consts::NUM_DIFAT_ENTRIES_IN_HEADER
                && difat.len() > header.num_fat_sectors as usize
                && difat.last() == Some(&0)
            {
                difat.pop();
            }
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
                fat.push(sector.read_le_u32()?);
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
        // Files have been seen with erroneous other types of sectors beyond
        // EOF, so strip those as well.
        if !validation.is_strict() {
            while fat.len() > num_sectors as usize {
                if fat.last() == Some(&0)
                    || fat.last() == Some(&consts::DIFAT_SECTOR)
                    || fat.last() == Some(&consts::FAT_SECTOR)
                    || fat.last() == Some(&consts::FREE_SECTOR)
                {
                    fat.pop();
                } else {
                    break;
                }
            }
        }
        // Strip FREE_SECTOR entries from the end of the FAT.
        while fat.len() > num_sectors as usize
            && fat.last() == Some(&consts::FREE_SECTOR)
        {
            fat.pop();
        }
        while fat.len() < num_sectors as usize {
            fat.push(consts::FREE_SECTOR);
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
                minifat.push(chain.read_le_u32()?);
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

        Ok(CompoundFile {
            minialloc: Arc::new(RwLock::new(minialloc)),
            max_buffer_size,
        })
    }
}

impl<F: Read + Write + Seek> CompoundFile<F> {
    /// Creates a new compound file with no contents, using the underlying
    /// reader/writer.  The reader/writer should be initially empty.
    pub fn create(inner: F) -> io::Result<CompoundFile<F>> {
        OpenOptions::new().create_with(inner)
    }

    /// Creates a new compound file of the given version with no contents,
    /// using the underlying writer.  The writer should be initially empty.
    pub fn create_with_version(
        version: Version,
        inner: F,
    ) -> io::Result<CompoundFile<F>> {
        CompoundFile::create_with_version_and_options(
            version,
            inner,
            DEFAULT_STREAM_MAX_BUFFER_SIZE,
        )
    }

    fn create_with_version_and_options(
        version: Version,
        mut inner: F,
        max_buffer_size: usize,
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
            inner.write_le_u32(entry)?;
        }
        for _ in fat.len()..(sector_len / size_of::<u32>()) {
            inner.write_le_u32(consts::FREE_SECTOR)?;
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
        Ok(CompoundFile {
            minialloc: Arc::new(RwLock::new(minialloc)),
            max_buffer_size,
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
            None => not_found!("Parent storage doesn't exist"),
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
                let mut stream = Stream::new(
                    &self.minialloc,
                    stream_id,
                    self.max_buffer_size,
                );
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
            None => not_found!("Parent storage doesn't exist"),
        };
        let new_stream_id = self.minialloc_mut().insert_dir_entry(
            parent_id,
            name,
            ObjType::Stream,
        )?;
        Ok(Stream::new(&self.minialloc, new_stream_id, self.max_buffer_size))
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
        self.set_entry_with_path(path.as_ref(), |dir_entry| {
            dir_entry.state_bits = bits
        })
    }

    /// Sets the modified time for the object at the given path to now.  Has no
    /// effect when called on the root storage.
    pub fn touch<P: AsRef<Path>>(&mut self, path: P) -> io::Result<()> {
        self.set_modified_time(path, web_time::SystemTime::now())
    }

    /// Sets the modified time for the object at the given path.
    /// Has no effect on streams due to requirements imposed by CFB spec.
    pub fn set_modified_time<P: AsRef<Path>>(
        &mut self,
        path: P,
        ts: web_time::SystemTime,
    ) -> io::Result<()> {
        self.set_entry_with_path(path.as_ref(), |dir_entry| {
            if dir_entry.obj_type != ObjType::Stream {
                dir_entry.modified_time = Timestamp::from_system_time(ts);
            }
        })
    }

    /// Sets the created time for the object at the given path.
    /// Has no effect on streams due to requirements imposed by CFB spec.
    pub fn set_created_time<P: AsRef<Path>>(
        &mut self,
        path: P,
        ts: web_time::SystemTime,
    ) -> io::Result<()> {
        self.set_entry_with_path(path.as_ref(), |dir_entry| {
            if dir_entry.obj_type != ObjType::Stream {
                dir_entry.creation_time = Timestamp::from_system_time(ts);
            }
        })
    }

    fn set_entry_with_path<G: FnMut(&mut DirEntry)>(
        &mut self,
        path: &Path,
        f: G,
    ) -> io::Result<()> {
        let names = internal::path::name_chain_from_path(path)?;
        let path = internal::path::path_from_name_chain(&names);
        let stream_id = match self.stream_id_for_name_chain(&names) {
            Some(stream_id) => stream_id,
            None => not_found!("No such object: {:?}", path),
        };
        self.minialloc_mut().with_dir_entry_mut(stream_id, f)?;
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

trait ReadLeNumber: Read {
    fn read_le_u64(&mut self) -> Result<u64, std::io::Error> {
        let mut buf = [0u8; 8];
        self.read_exact(&mut buf)?;
        Ok(u64::from_le_bytes(buf))
    }
    fn read_le_u32(&mut self) -> Result<u32, std::io::Error> {
        let mut buf = [0u8; 4];
        self.read_exact(&mut buf)?;
        Ok(u32::from_le_bytes(buf))
    }
    fn read_le_u16(&mut self) -> Result<u16, std::io::Error> {
        let mut buf = [0u8; 2];
        self.read_exact(&mut buf)?;
        Ok(u16::from_le_bytes(buf))
    }
}
impl<T: Read> ReadLeNumber for T {}

trait WriteLeNumber: Write {
    fn write_le_u64(&mut self, num: u64) -> Result<(), std::io::Error> {
        self.write_all(&num.to_le_bytes())
    }
    fn write_le_u32(&mut self, num: u32) -> Result<(), std::io::Error> {
        self.write_all(&num.to_le_bytes())
    }
    fn write_le_u16(&mut self, num: u16) -> Result<(), std::io::Error> {
        self.write_all(&num.to_le_bytes())
    }
}
impl<T: Write> WriteLeNumber for T {}
//===========================================================================//

#[cfg(test)]
mod tests {
    use std::io::{self, Cursor, Seek, SeekFrom};
    use std::mem::size_of;
    use std::path::Path;

    use crate::internal::{
        consts, DirEntry, Header, ObjType, Timestamp, Version,
    };
    use crate::{ReadLeNumber, WriteLeNumber};

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
            data.write_le_u32(entry)?;
        }
        // Pad the FAT sector with zeros instead of FREE_SECTOR.  Technically
        // this violates the MS-CFB spec (section 2.3), but apparently some CFB
        // implementations do this.
        for _ in fat.len()..(version.sector_len() / size_of::<u32>()) {
            data.write_le_u32(0)?;
        }
        // Write directory sector:
        DirEntry::empty_root_entry().write_to(&mut data)?;
        for _ in 1..version.dir_entries_per_sector() {
            DirEntry::unallocated().write_to(&mut data)?;
        }
        Ok(data)
    }

    fn make_cfb_with_ts(ts: web_time::SystemTime) -> Vec<u8> {
        use std::io::Write;

        let mut buf = Vec::new();
        let mut cfb = CompoundFile::create(io::Cursor::new(&mut buf)).unwrap();

        cfb.create_storage("/foo/").unwrap();
        let mut stream = cfb.create_stream("/foo/bar").unwrap();
        stream.write_all(b"data").unwrap();
        drop(stream);

        let entries: Vec<_> = cfb.walk().collect();
        for entr in entries {
            cfb.set_modified_time(entr.path(), ts).unwrap();
            cfb.set_created_time(entr.path(), ts).unwrap();
        }
        cfb.flush().unwrap();
        buf
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

    fn make_cfb_file_with_zero_padded_difat() -> io::Result<Vec<u8>> {
        let version = Version::V3;
        let mut data = Vec::<u8>::new();

        let dir_sector = 0;
        let difat_sector = 1;
        // The zero-padded DIFAT issue is only seen with a DIFAT sector
        let num_fat_sectors = consts::NUM_DIFAT_ENTRIES_IN_HEADER + 1;
        // Layout FAT sectors after the DIFAT sector
        let first_fat_sector = difat_sector + 1;
        let fat_sectors: Vec<u32> = (0..num_fat_sectors)
            .map(|i| (first_fat_sector + i) as u32)
            .collect();

        // Construct header full of DIFAT entries
        let header = Header {
            version,
            num_dir_sectors: 0,
            num_fat_sectors: num_fat_sectors as u32,
            first_dir_sector: dir_sector as u32,
            first_minifat_sector: consts::END_OF_CHAIN,
            num_minifat_sectors: 0,
            first_difat_sector: difat_sector as u32,
            num_difat_sectors: 1,
            initial_difat_entries: std::array::from_fn(|difat_entry_i| {
                fat_sectors[difat_entry_i]
            }),
        };
        header.write_to(&mut data)?;

        // Write the directory sector
        DirEntry::empty_root_entry().write_to(&mut data)?;
        for _ in 1..version.dir_entries_per_sector() {
            DirEntry::unallocated().write_to(&mut data)?;
        }

        // Write the DIFAT sector
        let num_difat_entries_in_sector =
            version.sector_len() / size_of::<u32>() - 1;
        for i in 0..num_difat_entries_in_sector {
            let difat_entry_i = i + consts::NUM_DIFAT_ENTRIES_IN_HEADER;

            let entry = if difat_entry_i < num_fat_sectors {
                fat_sectors[difat_entry_i]
            } else {
                // Pad with zeroes instead of FREE_SECTOR, this is
                // the point where it deviates from spec.
                0
            };
            data.write_le_u32(entry)?;
        }
        // End DIFAT chain
        data.write_le_u32(consts::END_OF_CHAIN)?;

        // Write the first two FAT sectors, referencing the header data
        let num_fat_entries_in_sector =
            version.sector_len() / size_of::<u32>();
        let mut fat = vec![consts::FREE_SECTOR; num_fat_entries_in_sector * 2];
        fat[difat_sector] = consts::DIFAT_SECTOR;
        fat[dir_sector] = consts::END_OF_CHAIN;
        for fat_sector in fat_sectors {
            fat[fat_sector as usize] = consts::FAT_SECTOR;
        }
        for entry in fat {
            data.write_le_u32(entry)?;
        }

        // Pad out the rest of the FAT sectors with FREE_SECTOR
        for _fat_sector in 2..num_fat_sectors {
            for _i in 0..num_fat_entries_in_sector {
                data.write_le_u32(consts::FREE_SECTOR)?;
            }
        }

        Ok(data)
    }

    #[test]
    fn zero_padded_difat_strict() {
        let data = make_cfb_file_with_zero_padded_difat().unwrap();
        let result = CompoundFile::open_strict(Cursor::new(data));
        assert_eq!(
            result.err().unwrap().to_string(),
            "Incorrect number of FAT sectors (header says 110, DIFAT says 236)",
        );
    }

    // Regression test for https://github.com/mdsteele/rust-cfb/issues/41.
    #[test]
    fn zero_padded_difat_permissive() {
        let data = make_cfb_file_with_zero_padded_difat().unwrap();
        // Despite the zero-padded DIFAT, we should be able to read this file
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
            let path = format!("stream{i}");
            let path = Path::new(&path);
            comp.create_stream(path).unwrap();
        }
        comp.flush().unwrap();

        // read num_dir_sectors from the header
        let mut cursor = comp.into_inner();
        cursor.seek(SeekFrom::Start(40)).unwrap();
        let num_dir_sectors = cursor.read_le_u32().unwrap();
        assert_eq!(num_dir_sectors, 2);
    }

    #[test]
    fn deterministic_cfbs() {
        let ts = web_time::SystemTime::now();
        let cfb1 = make_cfb_with_ts(ts);
        let cfb2 = make_cfb_with_ts(ts);
        let ts = Timestamp::from_system_time(ts);
        assert_eq!(cfb1, cfb2);

        let cfb = CompoundFile::open(Cursor::new(&cfb1)).unwrap();

        let entry = cfb.entry("/foo").unwrap();
        assert_eq!(Timestamp::from_system_time(entry.created()), ts);
        assert_eq!(Timestamp::from_system_time(entry.modified()), ts);

        let strict = CompoundFile::open_strict(Cursor::new(cfb1)).unwrap();

        let entry = strict.entry("/foo").unwrap();
        assert_eq!(Timestamp::from_system_time(entry.created()), ts);
        assert_eq!(Timestamp::from_system_time(entry.modified()), ts);
    }
    fn make_cfb_with_inconsistent_difat_entries() -> io::Result<Vec<u8>> {
        let mut data = Vec::new();
        // cfb has spare DIFAT_SECTOR entries in FAT not accounted for in header
        let mut hdr = Header {
            version: Version::V3,
            num_dir_sectors: 0,
            num_fat_sectors: 1,
            first_dir_sector: 0,
            first_minifat_sector: consts::END_OF_CHAIN,
            num_minifat_sectors: 0,
            first_difat_sector: consts::END_OF_CHAIN,
            num_difat_sectors: 0,
            initial_difat_entries: [consts::FREE_SECTOR;
                consts::NUM_DIFAT_ENTRIES_IN_HEADER],
        };
        hdr.initial_difat_entries[0] = 1;

        hdr.write_to(&mut data)?;

        // write dir sector
        for entr in [
            DirEntry::new("Root Entry", ObjType::Root, Timestamp::now()),
            DirEntry::unallocated(),
            DirEntry::unallocated(),
            DirEntry::unallocated(),
        ] {
            entr.write_to(&mut data)?;
        }

        // write FAT sector
        data.extend(&consts::END_OF_CHAIN.to_le_bytes());
        data.extend(&consts::FAT_SECTOR.to_le_bytes());
        // add a DIFAT_SECTOR to FAT, although inconsistent with header
        data.extend(&consts::DIFAT_SECTOR.to_le_bytes());
        for _ in (0..128).skip(3) {
            data.extend(&consts::FREE_SECTOR.to_le_bytes());
        }

        Ok(data)
    }

    #[test]
    fn too_many_fat_entries() {
        use std::io::Write;

        let cfb = make_cfb_with_inconsistent_difat_entries().unwrap();

        let mut cfb = CompoundFile::open(Cursor::new(cfb)).unwrap();
        let mut f = cfb.create_stream("stream").unwrap();
        f.write_all(&vec![0; 1024 * 1024]).unwrap();
    }
}

//===========================================================================//
