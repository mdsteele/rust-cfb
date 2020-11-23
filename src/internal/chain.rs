use crate::internal::{consts, Allocator, SectorInit};
use std::cmp;
use std::io::{self, Read, Seek, SeekFrom, Write};

// ========================================================================= //

pub struct Chain<'a, F: 'a> {
    allocator: &'a mut Allocator<F>,
    init: SectorInit,
    sector_ids: Vec<u32>,
    offset_from_start: u64,
}

impl<'a, F> Chain<'a, F> {
    pub fn new(
        allocator: &'a mut Allocator<F>,
        start_sector_id: u32,
        init: SectorInit,
    ) -> Chain<'a, F> {
        let mut sector_ids = Vec::<u32>::new();
        let mut current_sector_id = start_sector_id;
        while current_sector_id != consts::END_OF_CHAIN {
            sector_ids.push(current_sector_id);
            current_sector_id = allocator.next(current_sector_id);
        }
        Chain { allocator, init, sector_ids, offset_from_start: 0 }
    }

    pub fn num_sectors(&self) -> usize {
        self.sector_ids.len()
    }

    pub fn len(&self) -> u64 {
        (self.allocator.sector_len() as u64) * (self.sector_ids.len() as u64)
    }
}

impl<'a, F> Seek for Chain<'a, F> {
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        let length = self.len();
        let new_offset = match pos {
            SeekFrom::Start(delta) => delta as i64,
            SeekFrom::End(delta) => delta + length as i64,
            SeekFrom::Current(delta) => delta + self.offset_from_start as i64,
        };
        if new_offset < 0 || (new_offset as u64) > length {
            invalid_input!(
                "Cannot seek to {}, chain length is {} bytes",
                new_offset,
                length
            );
        }
        self.offset_from_start = new_offset as u64;
        Ok(self.offset_from_start)
    }
}

impl<'a, F: Read + Seek> Read for Chain<'a, F> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let total_len = self.len();
        debug_assert!(self.offset_from_start <= total_len);
        let remaining_in_chain = total_len - self.offset_from_start;
        let max_len = cmp::min(buf.len() as u64, remaining_in_chain) as usize;
        if max_len == 0 {
            return Ok(0);
        }
        let sector_len = self.allocator.sector_len() as u64;
        let current_sector_index =
            (self.offset_from_start / sector_len) as usize;
        debug_assert!(current_sector_index < self.sector_ids.len());
        let current_sector_id = self.sector_ids[current_sector_index];
        let offset_within_sector = self.offset_from_start % sector_len;
        let mut sector = self
            .allocator
            .seek_within_sector(current_sector_id, offset_within_sector)?;
        let bytes_read = sector.read(&mut buf[0..max_len])?;
        self.offset_from_start += bytes_read as u64;
        debug_assert!(self.offset_from_start <= total_len);
        Ok(bytes_read)
    }
}

impl<'a, F: Write + Seek> Write for Chain<'a, F> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if buf.is_empty() {
            return Ok(0);
        }
        let mut total_len = self.len();
        let sector_len = self.allocator.sector_len() as u64;
        if self.offset_from_start == total_len {
            let new_sector_id =
                if let Some(&last_sector_id) = self.sector_ids.last() {
                    self.allocator.extend_chain(last_sector_id, self.init)?
                } else {
                    self.allocator.begin_chain(self.init)?
                };
            self.sector_ids.push(new_sector_id);
            total_len += sector_len;
            debug_assert_eq!(total_len, self.len());
        }
        let current_sector_index =
            (self.offset_from_start / sector_len) as usize;
        debug_assert!(current_sector_index < self.sector_ids.len());
        let current_sector_id = self.sector_ids[current_sector_index];
        let offset_within_sector = self.offset_from_start % sector_len;
        let mut sector = self
            .allocator
            .seek_within_sector(current_sector_id, offset_within_sector)?;
        let bytes_written = sector.write(buf)?;
        self.offset_from_start += bytes_written as u64;
        debug_assert!(self.offset_from_start <= total_len);
        Ok(bytes_written)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.allocator.flush()
    }
}

// ========================================================================= //
