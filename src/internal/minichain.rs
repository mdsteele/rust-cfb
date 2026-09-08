use crate::internal::{consts, MiniAllocator};
use std::io::{self, Read, Seek, SeekFrom, Write};

//===========================================================================//

pub struct MiniChain<'a, F: 'a> {
    minialloc: &'a mut MiniAllocator<F>,
    sector_ids: Vec<u32>,
    offset_from_start: u64,
}

impl<'a, F> MiniChain<'a, F> {
    pub fn new(
        minialloc: &'a mut MiniAllocator<F>,
        start_sector_id: u32,
    ) -> io::Result<MiniChain<'a, F>> {
        let mut sector_ids = Vec::<u32>::new();
        let mut current_sector_id = start_sector_id;
        let first_sector_id = start_sector_id;
        while current_sector_id != consts::END_OF_CHAIN {
            sector_ids.push(current_sector_id);
            current_sector_id =
                minialloc.next_mini_sector(current_sector_id)?;
            if current_sector_id == first_sector_id {
                invalid_data!(
                    "Minichain contained duplicate sector id {}",
                    current_sector_id
                );
            }
        }
        Ok(MiniChain { minialloc, sector_ids, offset_from_start: 0 })
    }

    pub fn start_sector_id(&self) -> u32 {
        self.sector_ids.first().copied().unwrap_or(consts::END_OF_CHAIN)
    }

    pub fn len(&self) -> u64 {
        (consts::MINI_SECTOR_LEN as u64) * (self.sector_ids.len() as u64)
    }

    /// How many mini sectors from `index` on are consecutive within one
    /// regular sector (and so can be read or written in one go), looking
    /// no further than needed to cover `wanted` bytes from
    /// `offset_within_sector` into the first.
    fn run_len(
        &self,
        index: usize,
        offset_within_sector: u64,
        wanted: usize,
    ) -> usize {
        let mini_sector_len = consts::MINI_SECTOR_LEN as u64;
        let per_sector =
            (self.minialloc.sector_len() / consts::MINI_SECTOR_LEN) as u32;
        let first = self.sector_ids[index];
        let mut run = 1;
        while index + run < self.sector_ids.len()
            && self.sector_ids[index + run]
                == self.sector_ids[index + run - 1] + 1
            && self.sector_ids[index + run] / per_sector == first / per_sector
            && run as u64 * mini_sector_len - offset_within_sector
                < wanted as u64
        {
            run += 1;
        }
        run
    }
}

impl<'a, F: Read + Write + Seek> MiniChain<'a, F> {
    /// Adds `count` mini sectors to the end of the chain.
    fn extend_by(&mut self, count: usize) -> io::Result<()> {
        let last_sector_id =
            self.sector_ids.last().copied().unwrap_or(consts::END_OF_CHAIN);
        let new_sector_ids =
            self.minialloc.extend_mini_chain_by(last_sector_id, count)?;
        self.sector_ids.extend(new_sector_ids);
        Ok(())
    }

    /// Resizes the chain to the minimum number of sectors large enough to old
    /// `new_len` bytes, allocating or freeing sectors as needed.
    pub fn set_len(&mut self, new_len: u64) -> io::Result<()> {
        debug_assert!(new_len < consts::MINI_STREAM_CUTOFF as u64);
        let sector_len = consts::MINI_SECTOR_LEN as u64;
        let new_num_sectors =
            ((sector_len + new_len - 1) / sector_len) as usize;
        if new_num_sectors == 0 {
            if let Some(&start_sector) = self.sector_ids.first() {
                self.minialloc.free_mini_chain(start_sector)?;
            }
        } else if new_num_sectors <= self.sector_ids.len() {
            if new_num_sectors < self.sector_ids.len() {
                self.minialloc.free_mini_chain_after(
                    self.sector_ids[new_num_sectors - 1],
                )?;
            }
            self.zero_tail(new_len)?;
        } else {
            self.extend_by(new_num_sectors - self.sector_ids.len())?;
        }
        Ok(())
    }

    /// Overwrites with zeros the bytes from `offset` to the end of the mini
    /// sector containing it, so that no stale data lingers past a stream's
    /// length.  Does nothing if `offset` is at the start of a mini sector.
    pub fn zero_tail(&mut self, offset: u64) -> io::Result<()> {
        let sector_len = consts::MINI_SECTOR_LEN as u64;
        let offset_within_sector = offset % sector_len;
        if offset_within_sector == 0 {
            return Ok(());
        }
        debug_assert!(offset < self.len());
        let sector_id = self.sector_ids[(offset / sector_len) as usize];
        let zeros = vec![0u8; (sector_len - offset_within_sector) as usize];
        self.minialloc
            .seek_within_mini_sector(sector_id, offset_within_sector)?
            .write_all(&zeros)
    }

    pub fn free(self) -> io::Result<()> {
        self.minialloc.free_mini_chain(self.start_sector_id())
    }
}

impl<'a, F> Seek for MiniChain<'a, F> {
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

impl<'a, F: Read + Seek> Read for MiniChain<'a, F> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let total_len = self.len();
        debug_assert!(self.offset_from_start <= total_len);
        let remaining_in_chain = total_len - self.offset_from_start;
        let max_len = remaining_in_chain.min(buf.len() as u64) as usize;
        if max_len == 0 {
            return Ok(0);
        }
        let sector_len = consts::MINI_SECTOR_LEN as u64;
        let current_sector_index =
            (self.offset_from_start / sector_len) as usize;
        debug_assert!(current_sector_index < self.sector_ids.len());
        let current_sector_id = self.sector_ids[current_sector_index];
        let offset_within_sector = self.offset_from_start % sector_len;
        // Read through as many consecutive mini sectors as the buffer
        // covers.
        let run =
            self.run_len(current_sector_index, offset_within_sector, max_len);
        let run_len = run as u64 * sector_len - offset_within_sector;
        let max_len = max_len.min(run_len as usize);
        let mut sector = self.minialloc.seek_within_mini_sector(
            current_sector_id,
            offset_within_sector,
        )?;
        let bytes_read = sector.read(&mut buf[0..max_len])?;
        self.offset_from_start += bytes_read as u64;
        debug_assert!(self.offset_from_start <= total_len);
        Ok(bytes_read)
    }
}

impl<'a, F: Read + Write + Seek> Write for MiniChain<'a, F> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if buf.is_empty() {
            return Ok(0);
        }
        let total_len = self.len();
        debug_assert!(self.offset_from_start <= total_len);
        let sector_len = consts::MINI_SECTOR_LEN as u64;
        // Make room for the whole buffer at once.
        let end = self.offset_from_start + buf.len() as u64;
        if end > total_len {
            let count = (end - total_len).div_ceil(sector_len) as usize;
            self.extend_by(count)?;
        }
        let current_sector_index =
            (self.offset_from_start / sector_len) as usize;
        debug_assert!(current_sector_index < self.sector_ids.len());
        let current_sector_id = self.sector_ids[current_sector_index];
        let offset_within_sector = self.offset_from_start % sector_len;
        // Write through as many consecutive mini sectors as the buffer
        // covers.
        let run = self.run_len(
            current_sector_index,
            offset_within_sector,
            buf.len(),
        );
        let run_len = run as u64 * sector_len - offset_within_sector;
        let max_len = buf.len().min(run_len as usize);
        let mut sector = self.minialloc.seek_within_mini_sector(
            current_sector_id,
            offset_within_sector,
        )?;
        let bytes_written = sector.write(&buf[..max_len])?;
        self.offset_from_start += bytes_written as u64;
        debug_assert!(self.offset_from_start <= self.len());
        Ok(bytes_written)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.minialloc.flush()
    }
}

//===========================================================================//
