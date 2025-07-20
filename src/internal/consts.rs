// ========================================================================= //

pub const HEADER_LEN: usize = 512; // length of CFB file header, in bytes
pub const DIR_ENTRY_LEN: usize = 128; // length of directory entry, in bytes
pub const NUM_DIFAT_ENTRIES_IN_HEADER: usize = 109;

// Constants for CFB file header values:
pub const MAGIC_NUMBER: [u8; 8] =
    [0xd0, 0xcf, 0x11, 0xe0, 0xa1, 0xb1, 0x1a, 0xe1];
pub const MINOR_VERSION: u16 = 0x3e;
pub const BYTE_ORDER_MARK: u16 = 0xfffe;
pub const MINI_SECTOR_SHIFT: u16 = 6; // 64-byte mini sectors
pub const MINI_SECTOR_LEN: usize = 1 << (MINI_SECTOR_SHIFT as usize);
pub const MINI_STREAM_CUTOFF: u32 = 4096;

// Constants for FAT entries:
pub const MAX_REGULAR_SECTOR: u32 = 0xfffffffa;
pub const INVALID_SECTOR: u32 = 0xfffffffb;
pub const DIFAT_SECTOR: u32 = 0xfffffffc;
pub const FAT_SECTOR: u32 = 0xfffffffd;
pub const END_OF_CHAIN: u32 = 0xfffffffe;
pub const FREE_SECTOR: u32 = 0xffffffff;

// Constants for directory entries:
pub const ROOT_DIR_NAME: &str = "Root Entry";
pub const OBJ_TYPE_UNALLOCATED: u8 = 0;
pub const OBJ_TYPE_STORAGE: u8 = 1;
pub const OBJ_TYPE_STREAM: u8 = 2;
pub const OBJ_TYPE_ROOT: u8 = 5;
pub const COLOR_RED: u8 = 0;
pub const COLOR_BLACK: u8 = 1;
pub const ROOT_STREAM_ID: u32 = 0;
pub const MAX_REGULAR_STREAM_ID: u32 = 0xfffffffa;
pub const NO_STREAM: u32 = 0xffffffff;

pub(crate) fn prettify(sectors: &[u32]) -> Vec<Sector> {
    let mut fmt = Vec::new();
    for s in sectors.iter() {
        match *s {
            END_OF_CHAIN => fmt.push(Sector::End),
            FREE_SECTOR => fmt.push(Sector::Free),
            DIFAT_SECTOR => fmt.push(Sector::Difat),
            FAT_SECTOR => fmt.push(Sector::Fat),
            i => {
                if let Some(Sector::Range(_, end)) = fmt.last_mut() {
                    if *end + 1 == i {
                        *end += 1;
                        continue;
                    }
                }
                fmt.push(Sector::Range(i, i));
            }
        };
    }
    fmt
}

#[derive(Clone, PartialEq, Eq)]
pub(crate) enum Sector {
    Free,
    End,
    Fat,
    Difat,
    Range(u32, u32),
}

impl std::fmt::Debug for Sector {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sector::Range(start, end) if *start == *end => {
                write!(f, "{start}")
            }
            Sector::Range(start, end) => write!(f, "{start}-{end}"),
            Sector::Free => f.write_str("FREE"),
            Sector::End => f.write_str("EOC"),
            Sector::Fat => f.write_str("FAT"),
            Sector::Difat => f.write_str("DIFAT"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_prettify_sectors() {
        let sectors = [
            END_OF_CHAIN,
            0,
            1,
            2,
            3,
            4,
            5,
            6,
            7,
            END_OF_CHAIN,
            23,
            25,
            18,
            FREE_SECTOR,
        ];
        let s = prettify(&sectors);
        assert_eq!("[EOC, 0-7, EOC, 23, 25, 18, FREE]", format!("{s:?}"));
    }
}

// ========================================================================= //
