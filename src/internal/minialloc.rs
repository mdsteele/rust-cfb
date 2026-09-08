use std::io::{self, Seek, Write};
use std::mem::size_of;

use fnv::FnvHashSet;

use crate::internal::{
    consts, Chain, DirEntry, Directory, MiniChain, ObjType, Sector,
    SectorInit, Validation, Version,
};
use crate::WriteLeNumber;

//===========================================================================//

macro_rules! malformed {
    ($e:expr) => { invalid_data!("Malformed MiniFAT ({})", $e) };
    ($fmt:expr, $($arg:tt)+) => {
        invalid_data!("Malformed MiniFAT ({})", format!($fmt, $($arg)+))
    };
}

//===========================================================================//

/// A wrapper around the directory manager that additionally provides
/// mini-sector allocation via the MiniFAT.
pub struct MiniAllocator<F> {
    directory: Directory<F>,
    minifat: Vec<u32>,
    minifat_start_sector: u32,
    free_mini_sectors: Vec<u32>,
    /// The sector IDs of the mini stream's chain, in order, once walked.
    /// Every access to a mini sector needs the regular sector it lives in;
    /// walking the FAT chain from the start on each access made reading or
    /// writing `n` small streams cost `O(n²)`. The chain only ever grows
    /// (see `append_mini_sector`), so it is walked once and extended in
    /// place.
    mini_stream_sectors: Option<Vec<u32>>,
    /// The sector IDs of the MiniFAT's chain, kept the same way for
    /// `set_minifat`.
    minifat_sectors: Option<Vec<u32>>,
}

impl<F> MiniAllocator<F> {
    pub fn new(
        directory: Directory<F>,
        minifat: Vec<u32>,
        minifat_start_sector: u32,
        validation: Validation,
    ) -> io::Result<MiniAllocator<F>> {
        let mut minialloc = MiniAllocator {
            directory,
            minifat,
            minifat_start_sector,
            free_mini_sectors: Vec::new(),
            mini_stream_sectors: None,
            minifat_sectors: None,
        };
        minialloc.validate(validation)?;
        Ok(minialloc)
    }

    pub fn version(&self) -> Version {
        self.directory.version()
    }

    pub fn inner(&self) -> &F {
        self.directory.inner()
    }

    pub fn next_mini_sector(&self, sector_id: u32) -> io::Result<u32> {
        let index = sector_id as usize;
        if index >= self.minifat.len() {
            invalid_data!(
                "Found reference to mini sector {}, but MiniFAT has only {} \
                 entries",
                index,
                self.minifat.len()
            );
        }
        let next_id = self.minifat[index];
        if next_id != consts::END_OF_CHAIN
            && (next_id > consts::MAX_REGULAR_SECTOR
                || next_id as usize >= self.minifat.len())
        {
            invalid_data!("next_id ({}) is invalid", next_id);
        }
        Ok(next_id)
    }

    pub fn into_inner(self) -> F {
        self.directory.into_inner()
    }

    pub fn sector_len(&self) -> usize {
        self.directory.sector_len()
    }

    pub fn stream_id_for_name_chain(&self, names: &[&str]) -> Option<u32> {
        self.directory.stream_id_for_name_chain(names)
    }

    pub fn open_chain(
        &mut self,
        start_sector_id: u32,
        init: SectorInit,
    ) -> io::Result<Chain<'_, F>> {
        self.directory.open_chain(start_sector_id, init)
    }

    pub fn open_mini_chain(
        &mut self,
        start_sector_id: u32,
    ) -> io::Result<MiniChain<'_, F>> {
        MiniChain::new(self, start_sector_id)
    }

    pub fn root_dir_entry(&self) -> &DirEntry {
        self.directory.root_dir_entry()
    }

    pub fn dir_entry(&self, stream_id: u32) -> &DirEntry {
        self.directory.dir_entry(stream_id)
    }

    fn validate(&mut self, validation: Validation) -> io::Result<()> {
        let root_entry = self.directory.root_dir_entry();
        let root_stream_mini_sectors =
            root_entry.stream_len / (consts::MINI_SECTOR_LEN as u64);
        if root_stream_mini_sectors < (self.minifat.len() as u64) {
            if validation.is_strict() {
                malformed!(
                "MiniFAT has {} entries, but root stream has only {} mini \
                 sectors",
                self.minifat.len(),
                root_stream_mini_sectors
            );
            } else {
                self.minifat.truncate(root_stream_mini_sectors as usize);
            }
        }
        let mut pointees = FnvHashSet::default();
        for (from_mini_sector, &to_mini_sector) in
            self.minifat.iter().enumerate()
        {
            if to_mini_sector <= consts::MAX_REGULAR_SECTOR {
                if to_mini_sector as usize >= self.minifat.len() {
                    malformed!(
                        "MiniFAT has {} entries, but mini sector {} points to \
                         {}",
                        self.minifat.len(),
                        from_mini_sector,
                        to_mini_sector
                    );
                }
                if pointees.contains(&to_mini_sector) {
                    malformed!(
                        "mini sector {} pointed to twice",
                        to_mini_sector
                    );
                }
                pointees.insert(to_mini_sector);
            }
        }

        self.free_mini_sectors.clear();
        for (idx, &entry) in self.minifat.iter().enumerate() {
            if entry == consts::FREE_SECTOR {
                self.free_mini_sectors.push(idx as u32);
            }
        }
        Ok(())
    }
}

impl<F: Seek> MiniAllocator<F> {
    /// Returns the sector IDs of the chain starting at `start_sector_id`,
    /// walking it once and caching the result in `cache`.
    fn cached_chain_sectors<'a>(
        directory: &mut Directory<F>,
        cache: &'a mut Option<Vec<u32>>,
        start_sector_id: u32,
    ) -> io::Result<&'a [u32]> {
        if cache.is_none() {
            let sector_ids = if start_sector_id == consts::END_OF_CHAIN {
                Vec::new()
            } else {
                directory
                    .open_chain(start_sector_id, SectorInit::Fat)?
                    .sector_ids()
                    .to_vec()
            };
            *cache = Some(sector_ids);
        }
        Ok(cache.as_deref().unwrap())
    }

    /// The sector IDs of the mini stream's chain, in order.
    fn mini_stream_sectors(&mut self) -> io::Result<&[u32]> {
        let start_sector = self.directory.root_dir_entry().start_sector;
        Self::cached_chain_sectors(
            &mut self.directory,
            &mut self.mini_stream_sectors,
            start_sector,
        )
    }

    /// The sector IDs of the MiniFAT's chain, in order.
    fn minifat_sectors(&mut self) -> io::Result<&[u32]> {
        let start_sector = self.minifat_start_sector;
        Self::cached_chain_sectors(
            &mut self.directory,
            &mut self.minifat_sectors,
            start_sector,
        )
    }

    /// Seeks to `offset_within_mini_sector` bytes into mini sector
    /// `mini_sector`.  The returned sector runs to the end of the regular
    /// sector the mini sector lives in, so consecutive mini sectors that
    /// share a regular sector can be read or written in one go.
    pub fn seek_within_mini_sector(
        &mut self,
        mini_sector: u32,
        offset_within_mini_sector: u64,
    ) -> io::Result<Sector<'_, F>> {
        debug_assert!(
            offset_within_mini_sector < consts::MINI_SECTOR_LEN as u64
        );
        let mini_sectors_per_sector =
            (self.directory.sector_len() / consts::MINI_SECTOR_LEN) as u32;
        let sector_index = (mini_sector / mini_sectors_per_sector) as usize;
        let mini_sector_within_sector = mini_sector % mini_sectors_per_sector;
        let sector_id = self
            .mini_stream_sectors()?
            .get(sector_index)
            .copied()
            .ok_or_else(|| {
                io::Error::new(io::ErrorKind::InvalidData, "invalid sector id")
            })?;
        self.directory.seek_within_sector(
            sector_id,
            mini_sector_within_sector as u64 * consts::MINI_SECTOR_LEN as u64
                + offset_within_mini_sector,
        )
    }
}

impl<F: Write + Seek> MiniAllocator<F> {
    /// Given the start sector of a chain, deallocates the entire chain.
    pub fn free_chain(&mut self, start_sector_id: u32) -> io::Result<()> {
        if start_sector_id == self.directory.root_dir_entry().start_sector {
            self.mini_stream_sectors = None;
        }
        if start_sector_id == self.minifat_start_sector {
            self.minifat_sectors = None;
        }
        self.directory.free_chain(start_sector_id)
    }

    /// Inserts a new directory entry into the tree under the specified parent
    /// entry, then returns the new stream ID.
    pub fn insert_dir_entry(
        &mut self,
        parent_id: u32,
        name: &str,
        obj_type: ObjType,
    ) -> io::Result<u32> {
        self.directory.insert_dir_entry(parent_id, name, obj_type)
    }

    /// Removes a directory entry from the tree and deallocates it.
    pub fn remove_dir_entry(
        &mut self,
        parent_id: u32,
        name: &str,
    ) -> io::Result<()> {
        self.directory.remove_dir_entry(parent_id, name)
    }

    /// Calls the given function with a mutable reference to the specified
    /// directory entry, then writes the updated directory entry to the
    /// underlying file once the function returns.
    pub fn with_dir_entry_mut<W>(
        &mut self,
        stream_id: u32,
        func: W,
    ) -> io::Result<()>
    where
        W: FnOnce(&mut DirEntry),
    {
        self.directory.with_dir_entry_mut(stream_id, func)
    }

    /// Adds `count` mini sectors to the end of the mini chain whose last
    /// mini sector is `last_mini_sector` (or starts a new mini chain, if
    /// that is `END_OF_CHAIN`), and returns their IDs in chain order.
    ///
    /// Doing this for a whole write at once, rather than a mini sector at a
    /// time, lets the MiniFAT entries of consecutive mini sectors be written
    /// together, and the mini stream (and so the root directory entry) be
    /// grown once.
    pub fn extend_mini_chain_by(
        &mut self,
        last_mini_sector: u32,
        count: usize,
    ) -> io::Result<Vec<u32>> {
        debug_assert!(
            last_mini_sector == consts::END_OF_CHAIN
                || self.minifat[last_mini_sector as usize]
                    == consts::END_OF_CHAIN
        );
        let mut mini_sectors = Vec::with_capacity(count);
        let mut appended = 0;
        for _ in 0..count {
            mini_sectors.push(self.take_mini_sector_id(&mut appended)?);
        }
        // Link the new mini sectors up, writing the MiniFAT entries of each
        // run of consecutive IDs in one go.
        let mut start = 0;
        while start < mini_sectors.len() {
            let mut end = start + 1;
            while end < mini_sectors.len()
                && mini_sectors[end] == mini_sectors[end - 1] + 1
            {
                end += 1;
            }
            let values: Vec<u32> = (start..end)
                .map(|i| {
                    mini_sectors
                        .get(i + 1)
                        .copied()
                        .unwrap_or(consts::END_OF_CHAIN)
                })
                .collect();
            self.set_minifat_run(mini_sectors[start], &values)?;
            start = end;
        }
        if last_mini_sector != consts::END_OF_CHAIN && count > 0 {
            self.set_minifat(last_mini_sector, mini_sectors[0])?;
        }
        if appended > 0 {
            self.append_mini_sectors(appended)?;
        }
        Ok(mini_sectors)
    }

    /// Picks the ID for a new mini sector: a free one if there is one,
    /// otherwise the one past the end of the mini stream (adding a MiniFAT
    /// sector first if the MiniFAT is full), counting it in `appended`.
    /// Its MiniFAT entry is set to `END_OF_CHAIN` in memory only; the
    /// caller writes the entry, and grows the mini stream by the appended
    /// mini sectors.
    fn take_mini_sector_id(
        &mut self,
        appended: &mut usize,
    ) -> io::Result<u32> {
        while let Some(free_idx) = self.free_mini_sectors.pop() {
            if self.minifat[free_idx as usize] == consts::FREE_SECTOR {
                self.minifat[free_idx as usize] = consts::END_OF_CHAIN;
                return Ok(free_idx);
            }
        }
        let minifat_entries_per_sector = self.directory.sector_len() / 4;
        if self.minifat_start_sector == consts::END_OF_CHAIN {
            debug_assert!(self.minifat.is_empty());
            self.minifat_start_sector =
                self.directory.begin_chain(SectorInit::Fat)?;
            self.minifat_sectors = Some(vec![self.minifat_start_sector]);
            let mut header = self.directory.seek_within_header(60)?;
            header.write_le_u32(self.minifat_start_sector)?;
            header.write_le_u32(1)?;
        } else if self.minifat.len() % minifat_entries_per_sector == 0 {
            // Extending from the chain's last sector avoids walking it from
            // the start; `extend_chain` accepts any sector of the chain.
            let last_sector = *self.minifat_sectors()?.last().unwrap();
            let new_sector =
                self.directory.extend_chain(last_sector, SectorInit::Fat)?;
            let sectors = self.minifat_sectors.as_mut().unwrap();
            sectors.push(new_sector);
            let num_minifat_sectors = sectors.len() as u32;
            let mut header = self.directory.seek_within_header(64)?;
            header.write_le_u32(num_minifat_sectors)?;
        }
        let new_mini_sector = self.minifat.len() as u32;
        self.minifat.push(consts::END_OF_CHAIN);
        *appended += 1;
        Ok(new_mini_sector)
    }

    /// Adds `count` mini sectors to the end of the mini stream, adding
    /// regular sectors to its chain as needed.
    fn append_mini_sectors(&mut self, count: usize) -> io::Result<()> {
        let mini_stream_start_sector =
            self.directory.root_dir_entry().start_sector;
        let mini_stream_len = self.directory.root_dir_entry().stream_len;
        debug_assert_eq!(mini_stream_len % consts::MINI_SECTOR_LEN as u64, 0);
        let sector_len = self.directory.sector_len() as u64;
        let new_mini_stream_len =
            mini_stream_len + (count * consts::MINI_SECTOR_LEN) as u64;

        let new_start_sector = if mini_stream_start_sector
            == consts::END_OF_CHAIN
        {
            debug_assert_eq!(mini_stream_len, 0);
            let start_sector = self.directory.begin_chain(SectorInit::Zero)?;
            self.mini_stream_sectors = Some(vec![start_sector]);
            start_sector
        } else {
            mini_stream_start_sector
        };
        // If the mini stream doesn't have room for the new mini sectors, add
        // regular sectors to its chain.
        while (self.mini_stream_sectors()?.len() as u64) * sector_len
            < new_mini_stream_len
        {
            // Extending from the chain's last sector avoids walking it from
            // the start; `extend_chain` accepts any sector of the chain.
            let last_sector = *self.mini_stream_sectors()?.last().unwrap();
            let new_sector =
                self.directory.extend_chain(last_sector, SectorInit::Zero)?;
            self.mini_stream_sectors.as_mut().unwrap().push(new_sector);
        }

        // Update length of mini stream in root directory entry.
        self.directory.with_root_dir_entry_mut(|dir_entry| {
            dir_entry.start_sector = new_start_sector;
            dir_entry.stream_len = new_mini_stream_len;
        })
    }

    /// Deallocates the specified mini sector.
    fn free_mini_sector(&mut self, mini_sector: u32) -> io::Result<()> {
        if self.minifat[mini_sector as usize] == consts::FREE_SECTOR {
            invalid_input!("sector {} freed twice", mini_sector);
        }
        self.set_minifat(mini_sector, consts::FREE_SECTOR)?;
        // Wipe the mini sector now.  Regular sectors are zeroed when they
        // are allocated, but a mini sector can come back into use without
        // passing through allocation of a fresh sector: either from the
        // free list, or by the mini stream growing again over a region it
        // was truncated from below.  A chain growing into it must read
        // zeros there.
        self.seek_within_mini_sector(mini_sector, 0)?
            .write_all(&[0u8; consts::MINI_SECTOR_LEN])?;
        self.free_mini_sectors.push(mini_sector);
        let mut mini_stream_len = self.directory.root_dir_entry().stream_len;
        debug_assert_eq!(mini_stream_len % consts::MINI_SECTOR_LEN as u64, 0);
        while self.minifat.last() == Some(&consts::FREE_SECTOR) {
            mini_stream_len -= consts::MINI_SECTOR_LEN as u64;
            self.minifat.pop();
            // TODO: Truncate MiniFAT if last MiniFAT sector is now all free.
        }
        let minifat_len = self.minifat.len();
        self.free_mini_sectors.retain(|&idx| (idx as usize) < minifat_len);

        if mini_stream_len != self.directory.root_dir_entry().stream_len {
            self.directory.with_root_dir_entry_mut(|dir_entry| {
                dir_entry.stream_len = mini_stream_len;
            })?;
        }
        Ok(())
    }

    /// Given the start sector of a mini chain, deallocates the entire chain.
    pub fn free_mini_chain(
        &mut self,
        start_mini_sector: u32,
    ) -> io::Result<()> {
        let mut mini_sector = start_mini_sector;
        while mini_sector != consts::END_OF_CHAIN {
            let next = self.minifat[mini_sector as usize];
            self.free_mini_sector(mini_sector)?;
            mini_sector = next;
        }
        Ok(())
    }

    /// Sets the given mini sector to point to `END_OF_CHAIN`, and deallocates
    /// all subsequent mini sectors in the chain.
    pub fn free_mini_chain_after(
        &mut self,
        mini_sector: u32,
    ) -> io::Result<()> {
        let next = self.minifat[mini_sector as usize];
        self.set_minifat(mini_sector, consts::END_OF_CHAIN)?;
        self.free_mini_chain(next)?;
        Ok(())
    }

    /// Sets `self.minifat[index] = value`, and also writes that change to the
    /// underlying file.  The `index` must be <= `self.minifat.len()`.
    fn set_minifat(&mut self, index: u32, value: u32) -> io::Result<()> {
        debug_assert!(index as usize <= self.minifat.len());
        if (index as usize) == self.minifat.len() {
            self.minifat.push(value);
        }
        self.set_minifat_run(index, &[value])
    }

    /// Sets `self.minifat[index..index + values.len()] = values`, and also
    /// writes that change to the underlying file, one write per MiniFAT
    /// sector touched.  The entries must already exist.
    fn set_minifat_run(
        &mut self,
        index: u32,
        values: &[u32],
    ) -> io::Result<()> {
        let entries_per_sector =
            self.directory.sector_len() / size_of::<u32>();
        let mut done = 0;
        while done < values.len() {
            let minifat_index = index as usize + done;
            let index_within_sector = minifat_index % entries_per_sector;
            let count = (entries_per_sector - index_within_sector)
                .min(values.len() - done);
            let mut bytes = Vec::with_capacity(count * size_of::<u32>());
            for &value in &values[done..done + count] {
                bytes.extend_from_slice(&value.to_le_bytes());
            }
            let sector_id = self
                .minifat_sectors()?
                .get(minifat_index / entries_per_sector)
                .copied()
                .ok_or_else(|| {
                    io::Error::new(
                        io::ErrorKind::InvalidData,
                        "MiniFAT sector missing",
                    )
                })?;
            let mut sector = self.directory.seek_within_sector(
                sector_id,
                (index_within_sector * size_of::<u32>()) as u64,
            )?;
            sector.write_all(&bytes)?;
            self.minifat[minifat_index..minifat_index + count]
                .copy_from_slice(&values[done..done + count]);
            done += count;
        }
        Ok(())
    }

    /// Flushes all changes to the underlying file.
    pub fn flush(&mut self) -> io::Result<()> {
        self.directory.flush()
    }
}

//===========================================================================//

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use crate::internal::{
        consts, Allocator, DirEntry, Directory, ObjType, SectorInit, Sectors,
        Timestamp, Validation, Version,
    };

    use super::MiniAllocator;

    fn make_minialloc(minifat: Vec<u32>) -> MiniAllocator<Cursor<Vec<u8>>> {
        let root_stream_len = (consts::MINI_SECTOR_LEN * minifat.len()) as u64;
        make_minialloc_with_root_stream_len(minifat, root_stream_len)
    }

    fn make_minialloc_with_root_stream_len(
        minifat: Vec<u32>,
        root_stream_len: u64,
    ) -> MiniAllocator<Cursor<Vec<u8>>> {
        let validation = Validation::Strict;
        let version = Version::V3;
        let num_sectors = 4; // FAT, Directory, MiniFAT, and mini chain
        let data_len = (1 + num_sectors) * version.sector_len();
        let mut data = vec![0; data_len];
        // The MiniFAT lives in sector 2; write it out so that what is on
        // disk matches what is in memory.
        let minifat_offset = 3 * version.sector_len();
        for (i, &entry) in minifat.iter().enumerate() {
            data[minifat_offset + 4 * i..minifat_offset + 4 * i + 4]
                .copy_from_slice(&entry.to_le_bytes());
        }
        let cursor = Cursor::new(data);
        let sectors = Sectors::new(version, data_len as u64, cursor);
        let mut fat = vec![consts::END_OF_CHAIN; num_sectors];
        fat[0] = consts::FAT_SECTOR;
        let allocator =
            Allocator::new(sectors, vec![], vec![0], fat, validation).unwrap();
        let mut root_entry = DirEntry::empty_root_entry();
        root_entry.child = 1;
        root_entry.start_sector = 3;
        root_entry.stream_len = root_stream_len;
        let mut stream_entry =
            DirEntry::new("foo", ObjType::Stream, Timestamp::zero());
        stream_entry.start_sector = 0;
        stream_entry.stream_len = root_entry.stream_len;
        let entries = vec![root_entry, stream_entry];
        let directory =
            Directory::new(allocator, entries, 1, validation).unwrap();
        MiniAllocator::new(directory, minifat, 2, validation).unwrap()
    }

    fn mini_chain(
        minialloc: &MiniAllocator<Cursor<Vec<u8>>>,
        start: u32,
    ) -> Vec<u32> {
        let mut ids = vec![];
        let mut id = start;
        while id != consts::END_OF_CHAIN {
            ids.push(id);
            id = minialloc.next_mini_sector(id).unwrap();
        }
        ids
    }

    /// Reads the MiniFAT back from the file, as a reader would.
    fn minifat_on_disk(
        minialloc: &mut MiniAllocator<Cursor<Vec<u8>>>,
    ) -> Vec<u32> {
        use crate::ReadLeNumber;
        let start = minialloc.minifat_start_sector;
        let mut chain = minialloc.open_chain(start, SectorInit::Fat).unwrap();
        let mut minifat = Vec::new();
        for _ in 0..(chain.len() / 4) {
            minifat.push(chain.read_le_u32().unwrap());
        }
        minifat.truncate(minialloc.minifat.len());
        minifat
    }

    #[test]
    fn extending_a_mini_chain_links_and_grows_the_mini_stream() {
        let mut minialloc = make_minialloc(vec![consts::END_OF_CHAIN]);
        assert_eq!(minialloc.root_dir_entry().stream_len, 64);
        // Ten mini sectors after the existing one: the MiniFAT entries are
        // written, and the mini stream grows to hold them (a V3 sector
        // holds 8 mini sectors).
        let ids = minialloc.extend_mini_chain_by(0, 10).unwrap();
        assert_eq!(ids, (1..=10).collect::<Vec<u32>>());
        assert_eq!(mini_chain(&minialloc, 0), (0..=10).collect::<Vec<u32>>());
        assert_eq!(minifat_on_disk(&mut minialloc), minialloc.minifat);
        assert_eq!(minialloc.root_dir_entry().stream_len, 11 * 64);
        assert_eq!(minialloc.mini_stream_sectors().unwrap().len(), 2);
        // A new chain, then freeing it and extending again reuses its mini
        // sectors, last freed first.
        let other =
            minialloc.extend_mini_chain_by(consts::END_OF_CHAIN, 3).unwrap();
        assert_eq!(other, vec![11, 12, 13]);
        minialloc.free_mini_chain(11).unwrap();
        // Freed mini sectors at the end of the mini stream are dropped from
        // it again.
        assert_eq!(minialloc.root_dir_entry().stream_len, 11 * 64);
        let more = minialloc.extend_mini_chain_by(10, 5).unwrap();
        assert_eq!(more, vec![11, 12, 13, 14, 15]);
        assert_eq!(mini_chain(&minialloc, 0), (0..=15).collect::<Vec<u32>>());
        assert_eq!(minifat_on_disk(&mut minialloc), minialloc.minifat);
        assert_eq!(minialloc.root_dir_entry().stream_len, 16 * 64);
    }

    #[test]
    fn extending_across_minifat_sectors() {
        let mut minialloc = make_minialloc(vec![consts::END_OF_CHAIN]);
        // A V3 MiniFAT sector holds 128 entries.
        let ids =
            minialloc.extend_mini_chain_by(consts::END_OF_CHAIN, 300).unwrap();
        assert_eq!(mini_chain(&minialloc, ids[0]), ids);
        assert_eq!(minialloc.minifat_sectors().unwrap().len(), 3);
        assert_eq!(minifat_on_disk(&mut minialloc), minialloc.minifat);
        assert_eq!(minialloc.root_dir_entry().stream_len, 301 * 64);
    }

    #[test]
    #[should_panic(
        expected = "Malformed MiniFAT (MiniFAT has 3 entries, but root stream \
                    has only 2 mini sectors)"
    )]
    fn root_stream_too_short() {
        let minifat = vec![1, 2, consts::END_OF_CHAIN];
        let root_stream_len = (2 * consts::MINI_SECTOR_LEN) as u64;
        make_minialloc_with_root_stream_len(minifat, root_stream_len);
    }

    #[test]
    #[should_panic(
        expected = "Malformed MiniFAT (MiniFAT has 2 entries, but mini sector \
                    1 points to 3)"
    )]
    fn pointee_out_of_range() {
        let minifat = vec![1, 3];
        make_minialloc(minifat);
    }

    #[test]
    #[should_panic(
        expected = "Malformed MiniFAT (mini sector 1 pointed to twice)"
    )]
    fn double_pointee() {
        let minifat = vec![1, 2, 1];
        make_minialloc(minifat);
    }
}

//===========================================================================//
