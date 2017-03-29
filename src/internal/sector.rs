use byteorder::{LittleEndian, WriteBytesExt};
use internal::{DirEntry, Version, consts};
use std::cmp;
use std::io::{self, Read, Seek, SeekFrom, Write};

// ========================================================================= //

/// A wrapper around the underlying file of a CompoundFile struct, providing
/// access to individual sectors of the file.
pub struct Sectors<F> {
    inner: F,
    version: Version,
    num_sectors: u32,
}

impl<F> Sectors<F> {
    pub fn new(version: Version, num_sectors: u32, inner: F) -> Sectors<F> {
        Sectors {
            inner: inner,
            version: version,
            num_sectors: num_sectors,
        }
    }

    pub fn version(&self) -> Version { self.version }

    pub fn sector_len(&self) -> usize { self.version.sector_len() }

    pub fn num_sectors(&self) -> u32 { self.num_sectors }

    pub fn into_inner(self) -> F { self.inner }
}

impl<F: Seek> Sectors<F> {
    pub fn seek_within_header(&mut self, offset_within_header: u64)
                              -> io::Result<Sector<F>> {
        debug_assert!(offset_within_header < self.sector_len() as u64);
        self.inner.seek(SeekFrom::Start(offset_within_header))?;
        Ok(Sector {
            sectors: self,
            offset_within_sector: offset_within_header as usize,
        })
    }

    pub fn seek_to_sector(&mut self, sector_id: u32) -> io::Result<Sector<F>> {
        self.seek_within_sector(sector_id, 0)
    }

    pub fn seek_within_sector(&mut self, sector_id: u32,
                              offset_within_sector: u64)
                              -> io::Result<Sector<F>> {
        debug_assert!(sector_id < self.num_sectors);
        debug_assert!(offset_within_sector < self.sector_len() as u64);
        let sector_len = self.sector_len() as u64;
        self.inner
            .seek(SeekFrom::Start((sector_id + 1) as u64 * sector_len +
                                  offset_within_sector))?;
        Ok(Sector {
            sectors: self,
            offset_within_sector: offset_within_sector as usize,
        })
    }
}

impl<F: Write + Seek> Sectors<F> {
    /// Creates or resets the specified sector using the given initializer.
    pub fn init_sector(&mut self, sector_id: u32, init: SectorInit)
                       -> io::Result<()> {
        debug_assert!(sector_id <= self.num_sectors);
        if sector_id == self.num_sectors {
            self.num_sectors += 1;
        }
        let mut sector = self.seek_to_sector(sector_id)?;
        init.initialize(&mut sector)?;
        Ok(())
    }

    /// Flushes all changes to the underlying file.
    pub fn flush(&mut self) -> io::Result<()> { self.inner.flush() }
}

// ========================================================================= //

/// A wrapper around a single sector within a CFB file, allowing read and write
/// access only within that sector.
pub struct Sector<'a, F: 'a> {
    sectors: &'a mut Sectors<F>,
    offset_within_sector: usize,
}

impl<'a, F> Sector<'a, F> {
    /// Returns the total length of this sector.
    pub fn len(&self) -> usize { self.sectors.sector_len() }

    fn remaining(&self) -> usize {
        debug_assert!(self.offset_within_sector <= self.len());
        self.len() - self.offset_within_sector
    }
}

impl<'a, F: Read> Read for Sector<'a, F> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let max_len = cmp::min(buf.len(), self.remaining());
        if max_len == 0 {
            return Ok(0);
        }
        let bytes_read = self.sectors.inner.read(&mut buf[0..max_len])?;
        self.offset_within_sector += bytes_read;
        debug_assert!(self.offset_within_sector <= self.len());
        Ok(bytes_read)
    }
}

impl<'a, F: Write> Write for Sector<'a, F> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let max_len = cmp::min(buf.len(), self.remaining());
        if max_len == 0 {
            return Ok(0);
        }
        let bytes_written = self.sectors.inner.write(&buf[0..max_len])?;
        self.offset_within_sector += bytes_written;
        debug_assert!(self.offset_within_sector <= self.len());
        Ok(bytes_written)
    }

    fn flush(&mut self) -> io::Result<()> { self.sectors.inner.flush() }
}

impl<'a, F: Seek> Seek for Sector<'a, F> {
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        let old_offset = self.offset_within_sector as i64;
        let new_offset = match pos {
            SeekFrom::Start(delta) => delta as i64,
            SeekFrom::End(delta) => self.len() as i64 + delta,
            SeekFrom::Current(delta) => {
                self.offset_within_sector as i64 + delta
            }
        };
        if new_offset < 0 || new_offset > self.len() as i64 {
            panic!("Internal error: cannot seek outside of sector");
        }
        self.sectors
            .inner
            .seek(SeekFrom::Current(new_offset - old_offset))?;
        self.offset_within_sector = new_offset as usize;
        Ok(new_offset as u64)
    }
}

// ========================================================================= //

#[derive(Clone, Copy)]
pub enum SectorInit {
    Zero,
    Fat,
    Dir,
}

impl SectorInit {
    fn initialize<F: Write>(self, sector: &mut Sector<F>) -> io::Result<()> {
        debug_assert_eq!(sector.offset_within_sector, 0);
        match self {
            SectorInit::Zero => {
                io::copy(&mut io::repeat(0).take(sector.len() as u64),
                         sector)?;
            }
            SectorInit::Fat => {
                for _ in 0..(sector.len() / 4) {
                    sector.write_u32::<LittleEndian>(consts::FREE_SECTOR)?;
                }
            }
            SectorInit::Dir => {
                let dir_entry = DirEntry::unallocated();
                for _ in 0..(sector.len() / consts::DIR_ENTRY_LEN) {
                    dir_entry.write_to(sector)?;
                }
            }
        }
        Ok(())
    }
}

// ========================================================================= //

#[cfg(test)]
mod tests {
    use super::Sectors;
    use internal::Version;
    use std::io::{Cursor, Read, Seek, SeekFrom, Write};

    #[test]
    fn sector_read() {
        let mut data = vec![1u8; 512];
        data.append(&mut vec![2; 512]);
        data.append(&mut vec![3; 512]);
        data.append(&mut vec![4; 512]);
        let mut sectors = Sectors::new(Version::V3, 4, Cursor::new(data));
        assert_eq!(sectors.sector_len(), 512);
        let mut sector = sectors.seek_to_sector(1).unwrap();
        assert_eq!(sector.len(), 512);
        {
            let mut buffer = vec![0; 400];
            assert_eq!(sector.read(&mut buffer).unwrap(), 400);
            assert_eq!(buffer, vec![3; 400])
        }
        {
            let mut buffer = vec![0; 400];
            assert_eq!(sector.read(&mut buffer).unwrap(), 112);
            let mut expected_data = vec![3; 112];
            expected_data.append(&mut vec![0; 288]);
            assert_eq!(buffer, expected_data);
        }
        {
            let mut buffer = vec![0; 400];
            assert_eq!(sector.read(&mut buffer).unwrap(), 0);
            assert_eq!(buffer, vec![0; 400])
        }
    }

    #[test]
    fn sector_write() {
        let cursor = Cursor::new(vec![0u8; 2048]);
        let mut sectors = Sectors::new(Version::V3, 4, cursor);
        assert_eq!(sectors.sector_len(), 512);
        {
            let mut sector = sectors.seek_to_sector(1).unwrap();
            assert_eq!(sector.len(), 512);
            assert_eq!(sector.write(&vec![1; 400]).unwrap(), 400);
            assert_eq!(sector.write(&vec![2; 400]).unwrap(), 112);
            assert_eq!(sector.write(&vec![3; 400]).unwrap(), 0);
        }
        let actual_data = sectors.into_inner().into_inner();
        let mut expected_data = vec![0u8; 1024];
        expected_data.append(&mut vec![1; 400]);
        expected_data.append(&mut vec![2; 112]);
        expected_data.append(&mut vec![0; 512]);
        assert_eq!(actual_data, expected_data);
    }


    #[test]
    fn sector_seek() {
        let mut data = vec![0u8; 512];
        data.append(&mut vec![1; 128]);
        data.append(&mut vec![2; 128]);
        data.append(&mut vec![3; 128]);
        data.append(&mut vec![4; 128]);
        assert_eq!(data.len(), 1024);
        let mut sectors = Sectors::new(Version::V3, 2, Cursor::new(data));
        assert_eq!(sectors.sector_len(), 512);
        let mut sector = sectors.seek_to_sector(0).unwrap();
        let mut buffer = vec![0; 128];
        assert_eq!(sector.seek(SeekFrom::Start(128)).unwrap(), 128);
        sector.read_exact(&mut buffer).unwrap();
        assert_eq!(buffer, vec![2; 128]);
        assert_eq!(sector.seek(SeekFrom::End(-128)).unwrap(), 384);
        sector.read_exact(&mut buffer).unwrap();
        assert_eq!(buffer, vec![4; 128]);
        assert_eq!(sector.seek(SeekFrom::Current(-256)).unwrap(), 256);
        sector.read_exact(&mut buffer).unwrap();
        assert_eq!(buffer, vec![3; 128]);
    }
}

// ========================================================================= //
