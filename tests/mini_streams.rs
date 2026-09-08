use cfb::CompoundFile;
use std::io::{Cursor, Read, Write};

/// Writes `count` mini streams of `len` bytes each, named `s{i}`, whose
/// contents identify the stream.
fn write_streams(
    comp: &mut CompoundFile<Cursor<Vec<u8>>>,
    count: u32,
    len: usize,
) {
    for i in 0..count {
        let data = vec![(i % 251) as u8; len];
        let mut stream = comp.create_stream(format!("/s{i}")).unwrap();
        stream.write_all(&data).unwrap();
    }
}

fn assert_stream(
    comp: &mut CompoundFile<Cursor<Vec<u8>>>,
    i: u32,
    len: usize,
) {
    let mut data = Vec::new();
    comp.open_stream(format!("/s{i}"))
        .unwrap()
        .read_to_end(&mut data)
        .unwrap();
    assert_eq!(data.len(), len, "stream s{} length", i);
    assert!(
        data.iter().all(|&b| b == (i % 251) as u8),
        "stream s{} contents",
        i
    );
}

/// Many small streams grow the mini stream across many regular sectors,
/// freeing some shrinks it, and adding more grows it again; every stream
/// must read back intact through all of it, whether the file is the one
/// being written or reopened from its bytes.
#[test]
fn many_mini_streams_grow_shrink_and_regrow() {
    let mut comp = CompoundFile::create(Cursor::new(Vec::new())).unwrap();
    write_streams(&mut comp, 800, 300);
    for i in 0..800 {
        assert_stream(&mut comp, i, 300);
    }

    // Free every third stream, then add a second batch.
    for i in (0..800).step_by(3) {
        comp.remove_stream(format!("/s{i}")).unwrap();
    }
    for i in 800..1000 {
        let data = vec![(i % 251) as u8; 300];
        let mut stream = comp.create_stream(format!("/s{i}")).unwrap();
        stream.write_all(&data).unwrap();
    }
    comp.flush().unwrap();

    let check = |comp: &mut CompoundFile<Cursor<Vec<u8>>>| {
        for i in 0..1000u32 {
            if i < 800 && i % 3 == 0 {
                assert!(
                    !comp.is_stream(format!("/s{i}")),
                    "s{} was removed",
                    i
                );
            } else {
                assert_stream(comp, i, 300);
            }
        }
    };
    check(&mut comp);

    // The same file reopened from its bytes.
    let bytes = comp.into_inner().into_inner();
    let mut reopened = CompoundFile::open(Cursor::new(bytes)).unwrap();
    check(&mut reopened);
}

/// A mini stream that grows past the mini-stream cutoff moves to the regular
/// sectors; a stream truncated back below it returns. Both transitions keep
/// the other mini streams readable.
#[test]
fn a_stream_crossing_the_mini_cutoff_keeps_its_neighbours_intact() {
    let mut comp = CompoundFile::create(Cursor::new(Vec::new())).unwrap();
    write_streams(&mut comp, 100, 200);

    let mut big = comp.create_stream("/big").unwrap();
    big.write_all(&[7u8; 100]).unwrap();
    big.write_all(&vec![7u8; 10_000]).unwrap();
    big.set_len(50).unwrap();
    drop(big);

    for i in 0..100 {
        assert_stream(&mut comp, i, 200);
    }
    let mut data = Vec::new();
    comp.open_stream("/big").unwrap().read_to_end(&mut data).unwrap();
    assert_eq!(data, vec![7u8; 50]);
}

/// A mini stream written in one go lands in one run of mini sectors, one
/// appended in pieces crosses mini sector boundaries mid-write, and one
/// created after others were removed reuses their scattered mini sectors;
/// all of them read back intact, also from a strictly reopened file.
#[test]
fn mini_streams_written_whole_in_pieces_and_into_reused_sectors() {
    let mut comp = CompoundFile::create(Cursor::new(Vec::new())).unwrap();
    let whole: Vec<u8> = (0..3000).map(|i| (i % 253) as u8).collect();
    comp.create_stream("/whole").unwrap().write_all(&whole).unwrap();

    let mut pieces = Vec::new();
    {
        let mut stream = comp.create_stream("/pieces").unwrap();
        for (i, len) in
            [10usize, 60, 100, 1, 63, 64, 65, 500].iter().enumerate()
        {
            let piece = vec![i as u8 + 1; *len];
            stream.write_all(&piece).unwrap();
            pieces.extend_from_slice(&piece);
        }
    }

    write_streams(&mut comp, 20, 200);
    for i in (0..20).step_by(2) {
        comp.remove_stream(format!("/s{i}")).unwrap();
    }
    let reused: Vec<u8> = (0..2500).map(|i| (i % 7) as u8).collect();
    comp.create_stream("/reused").unwrap().write_all(&reused).unwrap();

    let check = |comp: &mut CompoundFile<Cursor<Vec<u8>>>| {
        let mut read = |path: &str| {
            let mut data = Vec::new();
            comp.open_stream(path).unwrap().read_to_end(&mut data).unwrap();
            data
        };
        assert_eq!(read("/whole"), whole);
        assert_eq!(read("/pieces"), pieces);
        assert_eq!(read("/reused"), reused);
        for i in (1..20).step_by(2) {
            assert_stream(comp, i, 200);
        }
    };
    check(&mut comp);
    let bytes = comp.into_inner().into_inner();
    let mut comp = CompoundFile::open_strict(Cursor::new(bytes)).unwrap();
    check(&mut comp);
}

/// Enough mini sectors to need more than one MiniFAT sector (1024 entries
/// per V4 sector) still link up and reopen strictly.
#[test]
fn mini_streams_beyond_one_minifat_sector() {
    let mut comp = CompoundFile::create(Cursor::new(Vec::new())).unwrap();
    // 40 streams of 4000 bytes take 63 mini sectors each: 2520 entries.
    write_streams(&mut comp, 40, 4000);
    let bytes = comp.into_inner().into_inner();
    let mut comp = CompoundFile::open_strict(Cursor::new(bytes)).unwrap();
    for i in 0..40 {
        assert_stream(&mut comp, i, 4000);
    }
}
