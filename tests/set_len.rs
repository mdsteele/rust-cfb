use cfb::{CompoundFile, Version};
use std::io::{Cursor, Read, Seek, SeekFrom, Write};

//===========================================================================//

fn create_data(len: usize) -> Vec<u8> {
    let mut data = Vec::<u8>::new();
    let mut number = 0u32;
    while data.len() < len {
        data.extend_from_slice(number.to_string().as_bytes());
        number += 1;
    }
    data.truncate(len);
    data
}

fn test_set_stream_len(initial_len: usize, resize_len: usize) {
    let data = create_data(initial_len);
    let cursor = Cursor::new(Vec::new());
    let mut comp = CompoundFile::create_with_version(Version::V3, cursor)
        .expect("create");
    {
        let mut stream = comp.create_stream("/foobar").unwrap();
        stream.write_all(&data).unwrap();
    }
    let cursor = comp.into_inner();
    let mut comp = CompoundFile::open_strict(cursor).expect("open");
    {
        let mut stream = comp.open_stream("/foobar").unwrap();
        assert_eq!(stream.len(), initial_len as u64);
        stream.set_len(resize_len as u64).unwrap();
    }
    let cursor = comp.into_inner();
    let mut comp = CompoundFile::open_strict(cursor).expect("open");
    {
        let mut stream = comp.open_stream("/foobar").unwrap();
        assert_eq!(stream.len(), resize_len as u64);
        let mut actual_data = Vec::new();
        stream.read_to_end(&mut actual_data).unwrap();
        assert_eq!(actual_data.len(), resize_len);
        if resize_len <= initial_len {
            assert_eq!(actual_data, data[..resize_len]);
        } else {
            assert_eq!(actual_data[..initial_len], data);
            assert_eq!(
                actual_data[initial_len..],
                vec![0u8; resize_len - initial_len]
            );
        }
    }
}

//===========================================================================//

#[test]
fn resize_zero_to_zero() {
    test_set_stream_len(0, 0);
}

#[test]
fn resize_small_to_zero() {
    test_set_stream_len(1000, 0);
}

#[test]
fn resize_large_to_zero() {
    test_set_stream_len(5000, 0);
}

#[test]
fn resize_small_to_slightly_smaller() {
    test_set_stream_len(1000, 900);
}

#[test]
fn resize_small_to_slightly_bigger() {
    test_set_stream_len(1000, 1100);
}

#[test]
fn resize_small_to_large() {
    test_set_stream_len(1000, 5000);
}

#[test]
fn resize_large_to_small() {
    test_set_stream_len(5000, 1000);
}

#[test]
fn resize_large_to_huge() {
    test_set_stream_len(5000, 10000);
}

#[test]
fn resize_huge_to_large() {
    test_set_stream_len(10000, 5000);
}

//===========================================================================//

//===========================================================================//

// Bytes past a stream's length must not survive in the last sector, or a
// later grow would hand them back as data.

fn count_byte(comp: CompoundFile<Cursor<Vec<u8>>>, byte: u8) -> usize {
    comp.into_inner().get_ref().iter().filter(|&&b| b == byte).count()
}

fn fill_and_shrink(
    initial_len: usize,
    shrunk_len: usize,
) -> CompoundFile<Cursor<Vec<u8>>> {
    let mut comp =
        CompoundFile::create(Cursor::new(Vec::new())).expect("create");
    comp.create_stream("/s")
        .unwrap()
        .write_all(&vec![0xAB; initial_len])
        .unwrap();
    comp.open_stream("/s").unwrap().set_len(shrunk_len as u64).unwrap();
    comp
}

fn read_tail(
    comp: &mut CompoundFile<Cursor<Vec<u8>>>,
    from: usize,
) -> Vec<u8> {
    let mut stream = comp.open_stream("/s").unwrap();
    stream.seek(SeekFrom::Start(from as u64)).unwrap();
    let mut tail = Vec::new();
    stream.read_to_end(&mut tail).unwrap();
    tail
}

#[test]
fn shrink_zeroes_the_rest_of_the_last_sector() {
    assert_eq!(count_byte(fill_and_shrink(5000, 4100), 0xAB), 4100);
    assert_eq!(count_byte(fill_and_shrink(200, 100), 0xAB), 100);
}

#[test]
fn grow_after_shrink_reads_zeros() {
    let mut comp = fill_and_shrink(5000, 4100);
    comp.open_stream("/s").unwrap().set_len(5000).unwrap();
    assert_eq!(read_tail(&mut comp, 4100), vec![0u8; 900]);
    let mut comp = fill_and_shrink(200, 100);
    comp.open_stream("/s").unwrap().set_len(200).unwrap();
    assert_eq!(read_tail(&mut comp, 100), vec![0u8; 100]);
}

#[test]
fn grow_after_shrink_across_the_mini_cutoff_reads_zeros() {
    let mut comp = fill_and_shrink(5000, 100);
    comp.open_stream("/s").unwrap().set_len(5000).unwrap();
    assert_eq!(read_tail(&mut comp, 100), vec![0u8; 4900]);
}

#[test]
fn removing_a_mini_stream_leaves_no_data_behind() {
    let mut comp =
        CompoundFile::create(Cursor::new(Vec::new())).expect("create");
    comp.create_stream("/s").unwrap().write_all(&[0xAB; 200]).unwrap();
    comp.remove_stream("/s").unwrap();
    assert_eq!(count_byte(comp, 0xAB), 0);
}

#[test]
fn grow_in_a_reused_mini_sector_reads_zeros() {
    let mut comp =
        CompoundFile::create(Cursor::new(Vec::new())).expect("create");
    comp.create_stream("/old").unwrap().write_all(&[0xAB; 128]).unwrap();
    comp.remove_stream("/old").unwrap();
    // The new stream takes over the freed mini sectors, whose old contents
    // must not show up when it grows into them.
    comp.create_stream("/s").unwrap().write_all(&[0xCD; 100]).unwrap();
    comp.open_stream("/s").unwrap().set_len(128).unwrap();
    assert_eq!(read_tail(&mut comp, 100), vec![0u8; 28]);
}
