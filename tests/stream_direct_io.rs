use cfb::CompoundFile;
use std::io::{Cursor, Read, Seek, SeekFrom, Write};

fn pattern(len: usize, seed: u32) -> Vec<u8> {
    (0..len as u32)
        .map(|i| (i.wrapping_mul(2654435761) ^ seed) as u8)
        .collect()
}

/// Large writes (which bypass the stream's buffer) and small ones (which
/// go through it) can be mixed freely, including a large write into the
/// middle of a stream; everything reads back the same, whether read in
/// large pieces, small pieces, or all at once.
#[test]
fn large_and_small_writes_and_reads_mix() {
    let mut comp = CompoundFile::create(Cursor::new(Vec::new())).unwrap();
    let big = pattern(300 * 1024, 1);
    let small = pattern(1000, 2);
    let mut expected = Vec::new();
    {
        let mut stream = comp.create_stream("/s").unwrap();
        stream.write_all(&small).unwrap();
        expected.extend_from_slice(&small);
        stream.write_all(&big).unwrap();
        expected.extend_from_slice(&big);
        stream.write_all(&small).unwrap();
        expected.extend_from_slice(&small);
        stream.write_all(&big).unwrap();
        expected.extend_from_slice(&big);
        assert_eq!(stream.len(), expected.len() as u64);
        // A large write into the middle, right after a small one.
        stream.seek(SeekFrom::Start(500)).unwrap();
        let patch_small = pattern(100, 3);
        stream.write_all(&patch_small).unwrap();
        expected[500..600].copy_from_slice(&patch_small);
        let patch_big = pattern(100 * 1024, 4);
        stream.write_all(&patch_big).unwrap();
        expected[600..600 + patch_big.len()].copy_from_slice(&patch_big);
        assert_eq!(stream.len(), expected.len() as u64);
    }
    let check = |comp: &mut CompoundFile<Cursor<Vec<u8>>>| {
        let mut stream = comp.open_stream("/s").unwrap();
        let mut all = Vec::new();
        stream.read_to_end(&mut all).unwrap();
        assert_eq!(all, expected);
        assert_eq!(stream.read_to_end(&mut all).unwrap(), 0);
        stream.seek(SeekFrom::Start(0)).unwrap();
        let mut in_pieces = Vec::new();
        for len in [10usize, 70 * 1024, 5, 200 * 1024, 100_000, 100] {
            let mut piece = vec![0; len];
            stream.read_exact(&mut piece).unwrap();
            in_pieces.extend_from_slice(&piece);
        }
        assert_eq!(in_pieces, expected[..in_pieces.len()]);
        // Reading the rest after small buffered reads hands out what the
        // buffer holds first.
        let mut rest = Vec::new();
        stream.read_to_end(&mut rest).unwrap();
        in_pieces.extend_from_slice(&rest);
        assert_eq!(in_pieces, expected);
    };
    check(&mut comp);
    let bytes = comp.into_inner().into_inner();
    let mut comp = CompoundFile::open_strict(Cursor::new(bytes)).unwrap();
    check(&mut comp);
}

/// Data still sitting in the stream's buffer is flushed before a direct
/// read or write, so nothing is lost or read stale.
#[test]
fn buffered_writes_are_visible_to_direct_reads() {
    let mut comp = CompoundFile::create(Cursor::new(Vec::new())).unwrap();
    let mut stream = comp.create_stream("/s").unwrap();
    let head = pattern(3000, 5);
    stream.write_all(&head).unwrap();
    stream.seek(SeekFrom::Start(0)).unwrap();
    let mut all = Vec::new();
    stream.read_to_end(&mut all).unwrap();
    assert_eq!(all, head);
    // A small write followed by a large one, then a large read of both.
    stream.seek(SeekFrom::Start(1000)).unwrap();
    let mid = pattern(50, 6);
    let tail = pattern(80 * 1024, 7);
    stream.write_all(&mid).unwrap();
    stream.write_all(&tail).unwrap();
    let mut expected = head.clone();
    expected.truncate(1000);
    expected.extend_from_slice(&mid);
    expected.extend_from_slice(&tail);
    assert_eq!(stream.len(), expected.len() as u64);
    stream.seek(SeekFrom::Start(0)).unwrap();
    let mut back = vec![0; expected.len()];
    stream.read_exact(&mut back).unwrap();
    assert_eq!(back, expected);
}

/// A stream shorter than the direct threshold still reads back whole
/// through `read_to_end`, from a stream in the mini stream as well.
#[test]
fn read_to_end_of_small_streams() {
    let mut comp = CompoundFile::create(Cursor::new(Vec::new())).unwrap();
    let tiny = pattern(100, 8);
    comp.create_stream("/tiny").unwrap().write_all(&tiny).unwrap();
    comp.create_stream("/empty").unwrap();
    let mut stream = comp.open_stream("/tiny").unwrap();
    let mut first = [0u8; 30];
    stream.read_exact(&mut first).unwrap();
    let mut rest = Vec::new();
    assert_eq!(stream.read_to_end(&mut rest).unwrap(), 70);
    assert_eq!(rest, tiny[30..]);
    let mut nothing = Vec::new();
    assert_eq!(
        comp.open_stream("/empty").unwrap().read_to_end(&mut nothing).unwrap(),
        0
    );
}

/// A stream longer than one `read_to_end` piece is read whole.
#[test]
fn read_to_end_of_a_stream_beyond_one_piece() {
    let mut comp = CompoundFile::create(Cursor::new(Vec::new())).unwrap();
    let data = pattern(17 * 1024 * 1024 + 123, 9);
    comp.create_stream("/s").unwrap().write_all(&data).unwrap();
    let mut back = Vec::new();
    comp.open_stream("/s").unwrap().read_to_end(&mut back).unwrap();
    assert_eq!(back, data);
}

/// A directory entry may claim any length for its stream; `read_to_end`
/// reserves no more than the stream's chain can hold, and reports the
/// short chain as an error instead of allocating for the claim.
#[test]
fn read_to_end_does_not_trust_a_claimed_length() {
    let mut comp = CompoundFile::create(Cursor::new(Vec::new())).unwrap();
    comp.create_stream("/s").unwrap().write_all(&[7; 5000]).unwrap();
    let mut bytes = comp.into_inner().into_inner();
    // A new V4 file is header, FAT sector, directory sector; the stream's
    // entry is the second one in the directory, and its length field is at
    // offset 120 of the 128 byte entry.  Claim about 4 GB.
    let entry = 2 * 4096 + 128;
    assert_eq!(&bytes[entry..entry + 2], &[b's', 0]);
    bytes[entry + 120..entry + 128]
        .copy_from_slice(&0xFFF0_0000u64.to_le_bytes());
    let mut comp = CompoundFile::open(Cursor::new(bytes)).unwrap();
    let mut stream = comp.open_stream("/s").unwrap();
    assert_eq!(stream.len(), 0xFFF0_0000);
    let mut data = Vec::new();
    assert!(stream.read_to_end(&mut data).is_err());
    assert!(data.capacity() < 1 << 20, "reserved {}", data.capacity());
}
