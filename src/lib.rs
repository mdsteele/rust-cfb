//! A library for reading/writing [Compound File Binary](
//! https://en.wikipedia.org/wiki/Compound_File_Binary_Format) (structured
//! storage) files.  See [MS-CFB](
//! https://msdn.microsoft.com/en-us/library/dd942138.aspx) for the format
//! specification.

#![warn(missing_docs)]

extern crate byteorder;

use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use std::cmp;
use std::path::{Path, PathBuf};
use std::io::{self, Error, ErrorKind, Read, Seek, SeekFrom, Write};

// ========================================================================= //

const HEADER_LEN: usize = 512; // length of CFB file header, in bytes

const MAGIC_NUMBER: [u8; 8] = [0xd0, 0xcf, 0x11, 0xe0, 0xa1, 0xb1, 0x1a, 0xe1];
const MINOR_VERSION: u16 = 0x3e;
const BYTE_ORDER_MARK: u16 = 0xfffe;
const MINI_SECTOR_SHIFT: u16 = 6; // 64-byte mini sectors
const MINI_STREAM_MAX_LEN: u32 = 4096;

const END_OF_CHAIN: u32 = 0xfffffffe;
const FREE_SECTOR: u32 = 0xffffffff;

// ========================================================================= //

/// A compound file, backed by an underlying reader/writer (such as a
/// [`File`](https://doc.rust-lang.org/std/fs/struct.File.html) or
/// [`Cursor`](https://doc.rust-lang.org/std/io/struct.Cursor.html)).
pub struct CompoundFile<F> {
    inner: F,
    version: Version,
    fat: Vec<u32>,
}

impl<F> CompoundFile<F> {
    /// Returns the CFB format version used for this compound file.
    pub fn version(&self) -> Version { self.version }

    /// Returns the root storage (i.e. directory) within this compound file.
    pub fn root_storage(&mut self) -> Storage<F> {
        Storage {
            comp: self,
            path: PathBuf::from("/"),
        }
    }

    /// Consumes the `CompoundFile`, returning the underlying reader/writer.
    pub fn into_inner(self) -> F { self.inner }
}

impl<F: Seek> CompoundFile<F> {
    fn seek_to_sector(&mut self, sector_index: u32) -> io::Result<()> {
        self.seek_within_sector(sector_index, 0)
    }

    fn seek_within_sector(&mut self, sector_index: u32,
                          offset_within_sector: usize)
                          -> io::Result<()> {
        self.inner
            .seek(SeekFrom::Start((HEADER_LEN + offset_within_sector +
                                   self.version.sector_len() *
                                   sector_index as usize) as
                                  u64))?;
        Ok(())
    }
}

impl<F: Read + Seek> CompoundFile<F> {
    /// Opens a existing compound file, using the underlying reader.
    pub fn open(mut inner: F) -> io::Result<CompoundFile<F>> {
        inner.seek(SeekFrom::Start(0))?;
        let mut magic = [0u8; 8];
        inner.read_exact(&mut magic)?;
        if magic != MAGIC_NUMBER {
            let msg = "Invalid CFB file (wrong magic number)";
            return Err(Error::new(ErrorKind::InvalidData, msg));
        }
        inner.seek(SeekFrom::Start(26))?;
        let version_number = inner.read_u16::<LittleEndian>()?;
        let version = match Version::from_number(version_number) {
            Some(version) => version,
            None => {
                let msg = format!("CFB version {} is not supported",
                                  version_number);
                return Err(Error::new(ErrorKind::InvalidData, msg));
            }
        };
        inner.seek(SeekFrom::Start(30))?;
        let sector_shift = inner.read_u16::<LittleEndian>()?;
        if sector_shift != version.sector_shift() {
            let msg = format!("Incorrect sector shift ({}) for CFB version {}",
                              sector_shift,
                              version.number());
            return Err(Error::new(ErrorKind::InvalidData, msg));
        }
        Ok(CompoundFile {
            inner: inner,
            version: version,
            fat: Vec::new(), // TODO: read in FAT
        })
    }
}

impl<F: Write + Seek> CompoundFile<F> {
    /// Creates a new compound file with no contents, using the underlying
    /// writer.  The writer should be initially empty.
    pub fn create(inner: F) -> io::Result<CompoundFile<F>> {
        CompoundFile::create_with_version(inner, Version::V4)
    }

    /// Creates a new compound file of the given version with no contents,
    /// using the underlying writer.  The writer should be initially empty.
    pub fn create_with_version(mut inner: F, version: Version)
                               -> io::Result<CompoundFile<F>> {
        inner.write_all(&MAGIC_NUMBER)?;
        inner.write_all(&[0; 16])?; // reserved field
        inner.write_u16::<LittleEndian>(MINOR_VERSION)?;
        inner.write_u16::<LittleEndian>(version.number())?;
        inner.write_u16::<LittleEndian>(BYTE_ORDER_MARK)?;
        inner.write_u16::<LittleEndian>(version.sector_shift())?;
        inner.write_u16::<LittleEndian>(MINI_SECTOR_SHIFT)?;
        inner.write_all(&[0; 6])?; // reserved field
        inner.write_u32::<LittleEndian>(0)?; // num dir sectors
        inner.write_u32::<LittleEndian>(0)?; // num FAT sectors
        inner.write_u32::<LittleEndian>(END_OF_CHAIN)?; // first dir sector
        inner.write_u32::<LittleEndian>(0)?; // transaction signature (unused)
        inner.write_u32::<LittleEndian>(MINI_STREAM_MAX_LEN)?;
        inner.write_u32::<LittleEndian>(END_OF_CHAIN)?; // first MiniFAT sector
        inner.write_u32::<LittleEndian>(0)?; // num MiniFAT sectors
        inner.write_u32::<LittleEndian>(END_OF_CHAIN)?; // first DIFAT sector
        inner.write_u32::<LittleEndian>(0)?; // num DIFAT sectors
        // First 109 DIFAT entries:
        inner.write_u32::<LittleEndian>(END_OF_CHAIN)?;
        for _ in 1..109 {
            inner.write_u32::<LittleEndian>(FREE_SECTOR)?;
        }
        Ok(CompoundFile {
            inner: inner,
            version: version,
            fat: Vec::new(),
        })
    }
}

// ========================================================================= //

/// A storage entry in a compound file, much like a filesystem directory.
pub struct Storage<'a, F: 'a> {
    comp: &'a mut CompoundFile<F>,
    path: PathBuf,
}

impl<'a, F> Storage<'a, F> {
    /// Returns this storage entry's path within the compound file.  The root
    /// storage entry has a path of `/`.
    pub fn path(&self) -> &Path { &self.path }

    /// Consumes this `Storage` object and returns its parent storage entry, or
    /// `None` if this was the root storage entry.
    pub fn parent(self) -> Option<Storage<'a, F>> {
        Some(self.comp.root_storage()) // TODO: implement this
    }
}

// ========================================================================= //

/// A stream entry in a compound file, much like a filesystem file.
pub struct Stream<'a, F: 'a> {
    comp: &'a mut CompoundFile<F>,
    total_len: usize,
    offset_from_start: usize,
    offset_within_sector: usize,
    start_sector: u32,
    current_sector: u32,
}

impl<'a, F> Stream<'a, F> {
    /// Returns the current length of the stream, in bytes.
    pub fn len(&self) -> usize { self.total_len }
}

impl<'a, F: Seek> Seek for Stream<'a, F> {
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        let new_pos = match pos {
            SeekFrom::Start(delta) => delta as i64,
            SeekFrom::End(delta) => delta + self.total_len as i64,
            SeekFrom::Current(delta) => delta + self.offset_from_start as i64,
        };
        if new_pos < 0 || new_pos > self.total_len as i64 {
            let msg = format!("Cannot seek to {}, stream length is {}",
                              new_pos,
                              self.total_len);
            Err(Error::new(ErrorKind::InvalidInput, msg))
        } else {
            let old_pos = self.offset_from_start as u64;
            let new_pos = new_pos as usize;
            if new_pos != self.offset_from_start {
                let sector_len = self.comp.version.sector_len();
                let mut offset = new_pos;
                let mut sector = self.start_sector;
                while offset >= sector_len {
                    sector = self.comp.fat[sector as usize];
                    offset -= sector_len;
                }
                self.comp.seek_within_sector(sector, offset)?;
                self.current_sector = sector;
                self.offset_within_sector = offset;
                self.offset_from_start = new_pos;
            }
            Ok(old_pos)
        }
    }
}

impl<'a, F: Read + Seek> Read for Stream<'a, F> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        debug_assert!(self.offset_from_start <= self.total_len);
        let remaining_in_file = self.total_len - self.offset_from_start;
        debug_assert!(self.offset_within_sector <= self.offset_from_start);
        let sector_len = self.comp.version.sector_len();
        debug_assert!(self.offset_within_sector < sector_len);
        let remaining_in_sector = sector_len - self.offset_within_sector;
        let max_len = cmp::min(buf.len(),
                               cmp::min(remaining_in_file,
                                        remaining_in_sector));
        if max_len == 0 {
            return Ok(0);
        }
        let bytes_read = self.comp.inner.read(&mut buf[0..max_len])?;
        self.offset_from_start += bytes_read;
        debug_assert!(self.offset_from_start <= self.total_len);
        self.offset_within_sector += bytes_read;
        debug_assert!(self.offset_within_sector <= sector_len);
        if self.offset_within_sector == sector_len {
            self.offset_within_sector = 0;
            self.current_sector = self.comp.fat[self.current_sector as usize];
            if self.current_sector == END_OF_CHAIN {
                debug_assert!(self.offset_from_start == self.total_len);
            } else {
                self.comp.seek_to_sector(self.current_sector)?;
            }
        }
        Ok(bytes_read)
    }
}

// ========================================================================= //

/// The CFB format version to use.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Version {
    /// Version 3, which uses 512-byte sectors.
    V3,
    /// Version 4, which uses 4096-byte sectors.
    V4,
}

impl Version {
    fn from_number(number: u16) -> Option<Version> {
        match number {
            3 => Some(Version::V3),
            4 => Some(Version::V4),
            _ => None,
        }
    }

    fn number(self) -> u16 {
        match self {
            Version::V3 => 3,
            Version::V4 => 4,
        }
    }

    fn sector_shift(self) -> u16 {
        match self {
            Version::V3 => 9, // 512-byte sectors
            Version::V4 => 12, // 4096-byte sectors
        }
    }

    fn sector_len(self) -> usize { 1 << (self.sector_shift() as usize) }
}

// ========================================================================= //

#[cfg(test)]
mod tests {
    use std::io::Cursor;
    use super::{CompoundFile, Version};

    #[test]
    fn write_and_read_empty_compound_file() {
        let cursor = Cursor::new(Vec::new());
        let comp = CompoundFile::create_with_version(cursor, Version::V3)
            .unwrap();
        let cursor = comp.into_inner();
        let comp = CompoundFile::open(cursor).unwrap();
        assert_eq!(comp.version(), Version::V3);
    }
}

// ========================================================================= //
