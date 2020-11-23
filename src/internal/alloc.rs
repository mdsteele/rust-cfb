use crate::internal::{consts, Sector, SectorInit, Sectors, Version};
use byteorder::{LittleEndian, WriteBytesExt};
use std::collections::HashSet;
use std::io::{self, Seek, Write};

// ========================================================================= //

macro_rules! malformed {
    ($e:expr) => { invalid_data!("Malformed FAT ({})", $e) };
    ($fmt:expr, $($arg:tt)+) => {
        invalid_data!("Malformed FAT ({})", format!($fmt, $($arg)+))
    };
}

// ========================================================================= //

/// A wrapper around the sectors of a compound file, providing sector
/// allocation via the FAT and DIFAT.
pub struct Allocator<F> {
    sectors: Sectors<F>,
    difat_sector_ids: Vec<u32>,
    difat: Vec<u32>,
    fat: Vec<u32>,
}

impl<F> Allocator<F> {
    pub fn new(
        sectors: Sectors<F>,
        difat_sector_ids: Vec<u32>,
        difat: Vec<u32>,
        fat: Vec<u32>,
    ) -> io::Result<Allocator<F>> {
        let alloc = Allocator { sectors, difat_sector_ids, difat, fat };
        alloc.validate()?;
        Ok(alloc)
    }

    pub fn version(&self) -> Version {
        self.sectors.version()
    }

    pub fn sector_len(&self) -> usize {
        self.sectors.sector_len()
    }

    pub fn next(&self, sector_id: u32) -> u32 {
        let next_id = self.fat[sector_id as usize];
        debug_assert!(
            next_id <= consts::MAX_REGULAR_SECTOR
                || next_id == consts::END_OF_CHAIN
        );
        next_id
    }

    pub fn into_inner(self) -> F {
        self.sectors.into_inner()
    }

    fn validate(&self) -> io::Result<()> {
        if self.fat.len() > self.sectors.num_sectors() as usize {
            malformed!(
                "FAT has {} entries, but file has only {} sectors",
                self.fat.len(),
                self.sectors.num_sectors()
            );
        }
        for &difat_sector in self.difat_sector_ids.iter() {
            if difat_sector as usize >= self.fat.len() {
                malformed!(
                    "FAT has {} entries, but DIFAT lists {} as a \
                            DIFAT sector",
                    self.fat.len(),
                    difat_sector
                );
            }
            if self.fat[difat_sector as usize] != consts::DIFAT_SECTOR {
                malformed!(
                    "DIFAT sector {} is not marked as such in the FAT",
                    difat_sector
                );
            }
        }
        for &fat_sector in self.difat.iter() {
            if fat_sector as usize >= self.fat.len() {
                malformed!(
                    "FAT has {} entries, but DIFAT lists {} as a FAT \
                            sector",
                    self.fat.len(),
                    fat_sector
                );
            }
            if self.fat[fat_sector as usize] != consts::FAT_SECTOR {
                malformed!(
                    "FAT sector {} is not marked as such in the FAT",
                    fat_sector
                );
            }
        }
        let mut pointees = HashSet::new();
        for (from_sector, &to_sector) in self.fat.iter().enumerate() {
            if to_sector <= consts::MAX_REGULAR_SECTOR {
                if to_sector as usize >= self.fat.len() {
                    malformed!(
                        "FAT has {} entries, but sector {} points \
                                to {}",
                        self.fat.len(),
                        from_sector,
                        to_sector
                    );
                }
                if pointees.contains(&to_sector) {
                    malformed!("sector {} pointed to twice", to_sector);
                }
                pointees.insert(to_sector);
            } else if to_sector == consts::INVALID_SECTOR {
                malformed!("{} is not a valid FAT entry", to_sector);
            }
        }
        Ok(())
    }
}

impl<F: Seek> Allocator<F> {
    pub fn seek_within_header(
        &mut self,
        offset_within_header: u64,
    ) -> io::Result<Sector<F>> {
        self.sectors.seek_within_header(offset_within_header)
    }

    pub fn seek_to_sector(&mut self, sector_id: u32) -> io::Result<Sector<F>> {
        self.sectors.seek_to_sector(sector_id)
    }

    pub fn seek_within_sector(
        &mut self,
        sector_id: u32,
        offset_within_sector: u64,
    ) -> io::Result<Sector<F>> {
        self.sectors.seek_within_sector(sector_id, offset_within_sector)
    }
}

impl<F: Write + Seek> Allocator<F> {
    /// Allocates a new chain with one sector, and returns the starting sector
    /// number.
    pub fn begin_chain(&mut self, init: SectorInit) -> io::Result<u32> {
        self.allocate_sector(init)
    }

    /// Given the starting sector (or any internal sector) of a chain, extends
    /// the end of that chain by one sector and returns the new sector number,
    /// updating the FAT as necessary.
    pub fn extend_chain(
        &mut self,
        start_sector_id: u32,
        init: SectorInit,
    ) -> io::Result<u32> {
        debug_assert_ne!(start_sector_id, consts::END_OF_CHAIN);
        let mut last_sector_id = start_sector_id;
        loop {
            let next = self.fat[last_sector_id as usize];
            if next == consts::END_OF_CHAIN {
                break;
            }
            last_sector_id = next;
        }
        let new_sector_id = self.allocate_sector(init)?;
        self.set_fat(last_sector_id, new_sector_id)?;
        Ok(new_sector_id)
    }

    /// Allocates a new entry in the FAT, sets its value to `END_OF_CHAIN`, and
    /// returns the new sector number.
    fn allocate_sector(&mut self, init: SectorInit) -> io::Result<u32> {
        // If there's an existing free sector, use that.
        for sector_id in 0..self.fat.len() {
            if self.fat[sector_id] == consts::FREE_SECTOR {
                let sector_id = sector_id as u32;
                self.set_fat(sector_id, consts::END_OF_CHAIN)?;
                return Ok(sector_id);
            }
        }
        // Otherwise, we need a new sector; if there's not room in the FAT to
        // add it, then first we need to allocate a new FAT sector.
        let sector_len = self.sectors.sector_len();
        if self.fat.len() % (sector_len / 4) == 0 {
            self.append_fat_sector()?;
        }
        // Add a new sector to the end of the file and return it.
        let new_sector = self.fat.len() as u32;
        self.set_fat(new_sector, consts::END_OF_CHAIN)?;
        self.sectors.init_sector(new_sector, init)?;
        Ok(new_sector)
    }

    /// Adds a new sector to the FAT chain at the end of the file, and updates
    /// the FAT and DIFAT accordingly.
    fn append_fat_sector(&mut self) -> io::Result<()> {
        // Add a new FAT sector to the end of the file.
        let new_fat_sector_id = self.fat.len() as u32;
        self.sectors.init_sector(new_fat_sector_id, SectorInit::Fat)?;

        // Record this new FAT sector in the DIFAT and in the FAT itself.
        let difat_index = self.difat.len();
        self.difat.push(new_fat_sector_id);
        self.set_fat(new_fat_sector_id, consts::FAT_SECTOR)?;
        debug_assert_eq!(self.fat.len(), new_fat_sector_id as usize + 1);

        // Write DIFAT changes to file.
        if difat_index < consts::NUM_DIFAT_ENTRIES_IN_HEADER {
            // This DIFAT entry goes in the file header.
            let offset = 76 + 4 * difat_index as u64;
            let mut header = self.sectors.seek_within_header(offset)?;
            header.write_u32::<LittleEndian>(new_fat_sector_id)?;
        } else {
            // This DIFAT entry goes in a DIFAT sector.
            let difat_entries_per_sector = (self.sector_len() - 4) / 4;
            let difat_sector_index = (difat_index
                - consts::NUM_DIFAT_ENTRIES_IN_HEADER)
                / difat_entries_per_sector;
            if difat_sector_index >= self.difat_sector_ids.len() {
                // Add a new DIFAT sector to the end of the file.
                let new_difat_sector_id = self.fat.len() as u32;
                self.sectors
                    .init_sector(new_difat_sector_id, SectorInit::Difat)?;
                // Record this new DIFAT sector in the FAT.
                self.set_fat(new_difat_sector_id, consts::DIFAT_SECTOR)?;
                // Add this sector to the end of the DIFAT chain.
                if let Some(&last_sector_id) = self.difat_sector_ids.last() {
                    let offset = self.sector_len() as u64 - 4;
                    let mut sector = self
                        .sectors
                        .seek_within_sector(last_sector_id, offset)?;
                    sector.write_u32::<LittleEndian>(new_difat_sector_id)?;
                }
                self.difat_sector_ids.push(new_difat_sector_id);
                // Update DIFAT chain fields in header.
                let mut header = self.sectors.seek_within_header(68)?;
                header.write_u32::<LittleEndian>(self.difat_sector_ids[0])?;
                header.write_u32::<LittleEndian>(
                    self.difat_sector_ids.len() as u32,
                )?;
            }
            // Write the new entry into the DIFAT sector.
            let difat_sector_id = self.difat_sector_ids[difat_sector_index];
            let index_within_difat_sector = difat_index
                - consts::NUM_DIFAT_ENTRIES_IN_HEADER
                - difat_sector_index * difat_entries_per_sector;
            let mut sector = self.sectors.seek_within_sector(
                difat_sector_id,
                4 * index_within_difat_sector as u64,
            )?;
            sector.write_u32::<LittleEndian>(new_fat_sector_id)?;
        }

        // Update length of FAT chain in header.
        let mut header = self.sectors.seek_within_header(44)?;
        header.write_u32::<LittleEndian>(self.difat.len() as u32)?;
        Ok(())
    }

    /// Sets the given sector to point to `END_OF_CHAIN`, and deallocates all
    /// subsequent sectors in the chain.
    pub fn free_chain_after(&mut self, sector_id: u32) -> io::Result<()> {
        let next = self.next(sector_id);
        self.set_fat(sector_id, consts::END_OF_CHAIN)?;
        self.free_chain(next)?;
        Ok(())
    }

    /// Given the start sector of a chain, deallocates the entire chain.
    pub fn free_chain(&mut self, start_sector_id: u32) -> io::Result<()> {
        let mut sector_id = start_sector_id;
        while sector_id != consts::END_OF_CHAIN {
            let next = self.next(sector_id);
            self.free_sector(sector_id)?;
            sector_id = next;
        }
        Ok(())
    }

    /// Deallocates the specified sector.
    fn free_sector(&mut self, sector_id: u32) -> io::Result<()> {
        self.set_fat(sector_id, consts::FREE_SECTOR)?;
        // TODO: Truncate FAT if last FAT sector is now all free.
        Ok(())
    }

    /// Sets `self.fat[index] = value`, and also writes that change to the
    /// underlying file.  The `index` must be <= `self.fat.len()`.
    fn set_fat(&mut self, index: u32, value: u32) -> io::Result<()> {
        let index = index as usize;
        debug_assert!(index <= self.fat.len());
        let fat_entries_per_sector = self.sectors.sector_len() / 4;
        let fat_sector_id = self.difat[index / fat_entries_per_sector];
        let offset_within_sector = 4 * (index % fat_entries_per_sector) as u64;
        let mut sector = self
            .sectors
            .seek_within_sector(fat_sector_id, offset_within_sector)?;
        sector.write_u32::<LittleEndian>(value)?;
        if index == self.fat.len() {
            self.fat.push(value);
        } else {
            self.fat[index] = value;
        }
        Ok(())
    }

    /// Flushes all changes to the underlying file.
    pub fn flush(&mut self) -> io::Result<()> {
        self.sectors.flush()
    }
}

// ========================================================================= //
