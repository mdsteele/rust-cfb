use internal::Version;
use std::cmp;
use std::io::{self, Read, Seek, SeekFrom, Write};

// ========================================================================= //

/// A wrapper around the underlying file of a CompoundFile struct, providing
/// access to individual sectors of the file.
pub struct Sectors<F> {
    inner: F,
    version: Version,
}

impl<F> Sectors<F> {
    pub fn new(version: Version, inner: F) -> Sectors<F> {
        Sectors {
            inner: inner,
            version: version,
        }
    }

    pub fn version(&self) -> Version { self.version }

    pub fn sector_len(&self) -> usize { self.version.sector_len() }

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

impl<F: Write> Sectors<F> {
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

// ========================================================================= //

#[cfg(test)]
mod tests {
    use super::Sectors;
    use internal::Version;
    use std::io::{Cursor, Read, Write};

    #[test]
    fn read_to_end_of_sector() {
        let mut data = vec![1u8; 512];
        data.append(&mut vec![2; 512]);
        data.append(&mut vec![3; 512]);
        data.append(&mut vec![41; 512]);
        let mut sectors = Sectors::new(Version::V3, Cursor::new(data));
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
    fn write_to_end_of_sector() {
        let cursor = Cursor::new(vec![0u8; 2048]);
        let mut sectors = Sectors::new(Version::V3, cursor);
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
}

// ========================================================================= //
