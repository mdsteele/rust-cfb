use crate::internal::{consts, Allocator, Sector, SectorInit};
use std::cmp;
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::sync::Arc;

//===========================================================================//

enum SectorIds {
    Shared(Arc<[u32]>),
    Owned(Vec<u32>),
}

impl SectorIds {
    fn len(&self) -> usize {
        match self {
            SectorIds::Shared(s) => s.len(),
            SectorIds::Owned(v) => v.len(),
        }
    }

    fn first(&self) -> Option<u32> {
        match self {
            SectorIds::Shared(s) => s.first().copied(),
            SectorIds::Owned(v) => v.first().copied(),
        }
    }

    fn last(&self) -> Option<u32> {
        match self {
            SectorIds::Shared(s) => s.last().copied(),
            SectorIds::Owned(v) => v.last().copied(),
        }
    }

    fn get(&self, idx: usize) -> Option<u32> {
        match self {
            SectorIds::Shared(s) => s.get(idx).copied(),
            SectorIds::Owned(v) => v.get(idx).copied(),
        }
    }

    fn to_vec(&self) -> Vec<u32> {
        match self {
            SectorIds::Shared(s) => s.as_ref().to_vec(),
            SectorIds::Owned(v) => v.clone(),
        }
    }

    fn push(&mut self, value: u32) {
        match self {
            SectorIds::Owned(v) => v.push(value),
            SectorIds::Shared(_) => {
                let mut v = self.to_vec();
                v.push(value);
                *self = SectorIds::Owned(v);
            }
        }
    }

    fn as_slice(&self) -> &[u32] {
        match self {
            SectorIds::Shared(s) => s.as_ref(),
            SectorIds::Owned(v) => v.as_slice(),
        }
    }
}

pub struct Chain<'a, F: 'a> {
    allocator: &'a mut Allocator<F>,
    init: SectorInit,
    sector_ids: SectorIds,
    offset_from_start: u64,
}

impl<'a, F> Chain<'a, F> {
    pub fn from_sector_ids(
        allocator: &'a mut Allocator<F>,
        sector_ids: Arc<[u32]>,
        init: SectorInit,
    ) -> Chain<'a, F> {
        Chain {
            allocator,
            init,
            sector_ids: SectorIds::Shared(sector_ids),
            offset_from_start: 0,
        }
    }

    pub fn new(
        allocator: &'a mut Allocator<F>,
        start_sector_id: u32,
        init: SectorInit,
    ) -> io::Result<Chain<'a, F>> {
        if start_sector_id != consts::END_OF_CHAIN {
            if let Some(sector_ids) =
                allocator.cached_chain_sector_ids(start_sector_id)
            {
                return Ok(Chain::from_sector_ids(
                    allocator, sector_ids, init,
                ));
            }
        }

        let mut sector_ids = Vec::<u32>::new();
        let mut current_sector_id = start_sector_id;
        let first_sector_id = start_sector_id;

        while current_sector_id != consts::END_OF_CHAIN {
            sector_ids.push(current_sector_id);
            let next_id = allocator.fat_entry(current_sector_id)?;
            if next_id != consts::END_OF_CHAIN
                && (next_id > consts::MAX_REGULAR_SECTOR
                    || next_id as usize >= allocator.fat_len())
            {
                invalid_data!("next_id ({}) is invalid", next_id);
            }

            current_sector_id = next_id;
            if current_sector_id == first_sector_id {
                invalid_data!(
                    "Chain contained duplicate sector id {}",
                    current_sector_id
                );
            }
        }

        if start_sector_id != consts::END_OF_CHAIN {
            allocator
                .put_cached_chain_sector_ids(start_sector_id, &sector_ids);
        }

        Ok(Chain {
            allocator,
            init,
            sector_ids: SectorIds::Owned(sector_ids),
            offset_from_start: 0,
        })
    }

    pub fn start_sector_id(&self) -> u32 {
        self.sector_ids.first().unwrap_or(consts::END_OF_CHAIN)
    }

    pub fn num_sectors(&self) -> usize {
        self.sector_ids.len()
    }

    pub fn len(&self) -> u64 {
        (self.allocator.sector_len() as u64) * (self.sector_ids.len() as u64)
    }

    pub(crate) fn sector_ids(&self) -> &[u32] {
        self.sector_ids.as_slice()
    }
}

impl<'a, F: Seek> Chain<'a, F> {
    pub fn into_subsector(
        self,
        subsector_index: u32,
        subsector_len: usize,
        offset_within_subsector: u64,
    ) -> io::Result<Sector<'a, F>> {
        debug_assert!(offset_within_subsector <= subsector_len as u64);
        debug_assert_eq!(self.allocator.sector_len() % subsector_len, 0);
        let subsectors_per_sector =
            self.allocator.sector_len() / subsector_len;
        let sector_index_within_chain =
            subsector_index as usize / subsectors_per_sector;
        let subsector_index_within_sector =
            subsector_index % (subsectors_per_sector as u32);
        let sector_id = self
            .sector_ids
            .get(sector_index_within_chain)
            .ok_or_else(|| {
                io::Error::new(io::ErrorKind::InvalidData, "invalid sector id")
            })?;
        self.allocator.seek_within_subsector(
            sector_id,
            subsector_index_within_sector,
            subsector_len,
            offset_within_subsector,
        )
    }
}

impl<'a, F: Write + Seek> Chain<'a, F> {
    /// Resizes the chain to the minimum number of sectors large enough to old
    /// `new_len` bytes, allocating or freeing sectors as needed.
    pub fn set_len(&mut self, new_len: u64) -> io::Result<()> {
        let sector_len = self.allocator.sector_len() as u64;
        let new_num_sectors =
            ((sector_len + new_len - 1) / sector_len) as usize;
        if new_num_sectors == 0 {
            if let Some(start_sector) = self.sector_ids.first() {
                self.allocator.free_chain(start_sector)?;
            }
        } else if new_num_sectors <= self.sector_ids.len() {
            if new_num_sectors < self.sector_ids.len() {
                let last_kept = self
                    .sector_ids
                    .get(new_num_sectors - 1)
                    .expect("sector id should exist");
                self.allocator.free_chain_after(last_kept)?;
            }
            // TODO: init remainder of final sector
        } else {
            for _ in self.sector_ids.len()..new_num_sectors {
                let new_sector_id = if let Some(last_sector_id) =
                    self.sector_ids.last()
                {
                    self.allocator.extend_chain(last_sector_id, self.init)?
                } else {
                    self.allocator.begin_chain(self.init)?
                };
                self.sector_ids.push(new_sector_id);
            }
        }
        Ok(())
    }

    pub fn free(self) -> io::Result<()> {
        self.allocator.free_chain(self.start_sector_id())
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
        let current_sector_id = self
            .sector_ids
            .get(current_sector_index)
            .expect("sector id should exist");
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
                if let Some(last_sector_id) = self.sector_ids.last() {
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
        let current_sector_id = self
            .sector_ids
            .get(current_sector_index)
            .expect("sector id should exist");
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

//===========================================================================//
