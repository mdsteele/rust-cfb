use cfb::CompoundFile;
use std::io::Cursor;
use std::path::PathBuf;

const SECTOR_LEN: usize = 4096;
const END_OF_CHAIN: u32 = 0xFFFF_FFFE;
const FAT_SECTOR: u32 = 0xFFFF_FFFD;
const FREE_SECTOR: u32 = 0xFFFF_FFFF;
const NO_STREAM: u32 = 0xFFFF_FFFF;

fn dir_entry(name: &str, obj_type: u8, child: u32, start: u32) -> [u8; 128] {
    let mut entry = [0u8; 128];
    let mut name_len = 0;
    for unit in name.encode_utf16().chain(std::iter::once(0)) {
        entry[name_len..name_len + 2].copy_from_slice(&unit.to_le_bytes());
        name_len += 2;
    }
    entry[64..66].copy_from_slice(&(name_len as u16).to_le_bytes());
    entry[66] = obj_type;
    entry[67] = 1; // black
    entry[68..72].copy_from_slice(&NO_STREAM.to_le_bytes());
    entry[72..76].copy_from_slice(&NO_STREAM.to_le_bytes());
    entry[76..80].copy_from_slice(&child.to_le_bytes());
    entry[116..120].copy_from_slice(&start.to_le_bytes());
    entry
}

/// Builds a version 4 compound file holding nothing but `depth` storages
/// called "a", each inside the one before.  Creating them one by one would
/// take time quadratic in `depth`, as each needs the path of its parent.
fn file_with_nested_storages(depth: usize) -> Vec<u8> {
    let num_entries = (depth + 1).div_ceil(32) * 32;
    let num_dir_sectors = num_entries / 32;
    let num_fat_sectors = (num_dir_sectors + 4).div_ceil(1024);
    assert!(num_fat_sectors <= 4);
    let first_dir_sector = num_fat_sectors;

    let mut header = vec![0u8; SECTOR_LEN];
    header[..8]
        .copy_from_slice(&[0xd0, 0xcf, 0x11, 0xe0, 0xa1, 0xb1, 0x1a, 0xe1]);
    header[24..26].copy_from_slice(&0x3eu16.to_le_bytes()); // minor version
    header[26..28].copy_from_slice(&4u16.to_le_bytes()); // major version
    header[28..30].copy_from_slice(&0xfffeu16.to_le_bytes()); // byte order
    header[30..32].copy_from_slice(&12u16.to_le_bytes()); // sector shift
    header[32..34].copy_from_slice(&6u16.to_le_bytes()); // mini sector shift
    header[40..44].copy_from_slice(&(num_dir_sectors as u32).to_le_bytes());
    header[44..48].copy_from_slice(&(num_fat_sectors as u32).to_le_bytes());
    header[48..52].copy_from_slice(&(first_dir_sector as u32).to_le_bytes());
    header[56..60].copy_from_slice(&4096u32.to_le_bytes()); // mini cutoff
    header[60..64].copy_from_slice(&END_OF_CHAIN.to_le_bytes()); // MiniFAT
    header[68..72].copy_from_slice(&END_OF_CHAIN.to_le_bytes()); // DIFAT
    for i in 0..109 {
        let fat_sector =
            if i < num_fat_sectors { i as u32 } else { FREE_SECTOR };
        header[76 + 4 * i..80 + 4 * i]
            .copy_from_slice(&fat_sector.to_le_bytes());
    }

    let mut fat = vec![FREE_SECTOR; num_fat_sectors * 1024];
    for entry in fat.iter_mut().take(num_fat_sectors) {
        *entry = FAT_SECTOR;
    }
    for i in 0..num_dir_sectors {
        fat[first_dir_sector + i] = if i + 1 == num_dir_sectors {
            END_OF_CHAIN
        } else {
            (first_dir_sector + i + 1) as u32
        };
    }

    let mut bytes = header;
    for entry in fat {
        bytes.extend_from_slice(&entry.to_le_bytes());
    }
    let child_of = |stream_id: usize| {
        if stream_id < depth {
            stream_id as u32 + 1
        } else {
            NO_STREAM
        }
    };
    bytes.extend_from_slice(&dir_entry(
        "Root Entry",
        5,
        child_of(0),
        END_OF_CHAIN,
    ));
    for stream_id in 1..=depth {
        bytes.extend_from_slice(&dir_entry("a", 1, child_of(stream_id), 0));
    }
    for _ in depth + 1..num_entries {
        bytes.extend_from_slice(&dir_entry("", 0, NO_STREAM, 0));
    }
    bytes
}

/// The MS-CFB spec puts no limit on how deeply storages can be nested.  The
/// paths of the entries of this 13 MB file add up to 10 GB, so walking it
/// must not build a path for every entry.
#[test]
fn walk_deeply_nested_storages() {
    const DEPTH: usize = 100_000;
    let bytes = file_with_nested_storages(DEPTH);
    let comp = CompoundFile::open_strict(Cursor::new(bytes)).unwrap();

    let entries: Vec<_> = comp.walk().collect();
    assert_eq!(entries.len(), DEPTH + 1);
    assert!(entries[0].is_root());
    // Paths are joined with the platform's separator, so compare against
    // paths built the same way rather than against strings.
    let nested = |depth: usize| {
        let mut path = PathBuf::from("/");
        path.extend(std::iter::repeat("a").take(depth));
        path
    };
    assert_eq!(entries[0].path(), nested(0));
    assert_eq!(entries[1].path(), nested(1));
    assert_eq!(entries[3].path(), nested(3));
    assert_eq!(entries[DEPTH].path(), nested(DEPTH));
    assert_eq!(entries[DEPTH].path().components().count(), DEPTH + 1);

    // Iterating over the innermost storages by path gives the same paths.
    let inner = entries[DEPTH - 1].path();
    let children: Vec<_> = comp.read_storage(inner).unwrap().collect();
    assert_eq!(children.len(), 1);
    assert_eq!(children[0].path(), entries[DEPTH].path());
    let walked: Vec<_> = comp.walk_storage(inner).unwrap().collect();
    assert_eq!(walked.len(), 2);
    assert_eq!(walked[0].path(), inner);
    assert_eq!(walked[1].path(), entries[DEPTH].path());
}
