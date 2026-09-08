use cfb::{CompoundFile, Version};
use std::io::{Cursor, Read, Seek, SeekFrom, Write};

fn pattern(len: usize, seed: u8) -> Vec<u8> {
    (0..len).map(|i| (i as u8).wrapping_mul(31).wrapping_add(seed)).collect()
}

/// A write that spans many sectors lands in one go and reads back the
/// same, whether the sectors are consecutive in the file or not.
#[test]
fn multi_sector_writes_round_trip() {
    let mut comp = CompoundFile::create_with_version(
        Version::V3,
        Cursor::new(Vec::new()),
    )
    .unwrap();
    // 10 KiB streams take 20 sectors each of the 512-byte V3 sectors.
    let a = pattern(10 * 1024, 1);
    let b = pattern(10 * 1024 + 300, 2);
    comp.create_stream("/a").unwrap().write_all(&a).unwrap();
    comp.create_stream("/b").unwrap().write_all(&b).unwrap();
    // Freeing /a and writing a bigger stream reuses its sectors, whose IDs
    // are handed out last-freed-first, so the new chain is not consecutive.
    comp.remove_stream("/a").unwrap();
    let c = pattern(15 * 1024 + 17, 3);
    comp.create_stream("/c").unwrap().write_all(&c).unwrap();
    // Appending to an existing chain starts inside its last sector.
    let tail = pattern(3000, 4);
    {
        let mut stream = comp.open_stream("/b").unwrap();
        stream.seek(SeekFrom::End(0)).unwrap();
        stream.write_all(&tail).unwrap();
    }
    let bytes = comp.into_inner().into_inner();
    assert_eq!(bytes.len() % 512, 0, "file is whole sectors");

    let mut comp = CompoundFile::open_strict(Cursor::new(bytes)).unwrap();
    let mut read = |path: &str| {
        let mut data = Vec::new();
        comp.open_stream(path).unwrap().read_to_end(&mut data).unwrap();
        data
    };
    assert_eq!(read("/c"), c);
    let mut b_expected = b.clone();
    b_expected.extend_from_slice(&tail);
    assert_eq!(read("/b"), b_expected);
}

/// The FAT itself grows while a long chain is being allocated (a V3 FAT
/// sector only covers 128 sectors), which splits the chain's sector IDs
/// around the new FAT sectors.
#[test]
fn chains_that_outgrow_a_fat_sector_round_trip() {
    let mut comp = CompoundFile::create_with_version(
        Version::V3,
        Cursor::new(Vec::new()),
    )
    .unwrap();
    let data = pattern(600 * 512 + 100, 5);
    comp.create_stream("/big").unwrap().write_all(&data).unwrap();
    let small = pattern(5000, 6);
    comp.create_stream("/small").unwrap().write_all(&small).unwrap();
    let bytes = comp.into_inner().into_inner();
    let mut comp = CompoundFile::open_strict(Cursor::new(bytes)).unwrap();
    let mut back = Vec::new();
    comp.open_stream("/big").unwrap().read_to_end(&mut back).unwrap();
    assert_eq!(back, data);
    back.clear();
    comp.open_stream("/small").unwrap().read_to_end(&mut back).unwrap();
    assert_eq!(back, small);
}

/// Reads that span consecutive sectors come back in large pieces, and
/// still respect sector boundaries where the chain is not consecutive.
#[test]
fn reads_across_sector_runs() {
    let mut comp = CompoundFile::create_with_version(
        Version::V3,
        Cursor::new(Vec::new()),
    )
    .unwrap();
    let a = pattern(2048, 7);
    comp.create_stream("/a").unwrap().write_all(&a).unwrap();
    comp.create_stream("/b").unwrap().write_all(&[1; 512]).unwrap();
    {
        let mut stream = comp.open_stream("/a").unwrap();
        stream.seek(SeekFrom::End(0)).unwrap();
        stream.write_all(&pattern(1024, 8)).unwrap();
    }
    let mut expected = a.clone();
    expected.extend_from_slice(&pattern(1024, 8));
    let mut stream = comp.open_stream("/a").unwrap();
    let mut back = vec![0; expected.len()];
    stream.read_exact(&mut back).unwrap();
    assert_eq!(back, expected);
    stream.seek(SeekFrom::Start(700)).unwrap();
    let mut piece = vec![0; 2000];
    stream.read_exact(&mut piece).unwrap();
    assert_eq!(piece, &expected[700..2700]);
}
