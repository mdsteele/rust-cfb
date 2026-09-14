use cfb::{CompoundFile, OpenOptions};
use std::io::{Cursor, Read, Seek, SeekFrom, Write};

//===========================================================================//

// Every test uses a small stream buffer so that a stream is refilled many
// times, which is what makes the allocator hand a chain's cached sector list
// from one refill to the next.

const BUFFER_SIZE: usize = 1024;
const SECTOR: usize = 4096;

fn create_data(len: usize, seed: u8) -> Vec<u8> {
    (0..len).map(|i| (i as u8).wrapping_mul(31).wrapping_add(seed)).collect()
}

fn create_comp() -> CompoundFile<Cursor<Vec<u8>>> {
    OpenOptions::new()
        .max_buffer_size(BUFFER_SIZE)
        .create_with(Cursor::new(Vec::new()))
        .unwrap()
}

fn reopen(
    comp: CompoundFile<Cursor<Vec<u8>>>,
) -> CompoundFile<Cursor<Vec<u8>>> {
    OpenOptions::new()
        .max_buffer_size(BUFFER_SIZE)
        .strict()
        .open_with(comp.into_inner())
        .unwrap()
}

fn read_all(comp: &mut CompoundFile<Cursor<Vec<u8>>>, path: &str) -> Vec<u8> {
    let mut data = Vec::new();
    comp.open_stream(path).unwrap().read_to_end(&mut data).unwrap();
    data
}

//===========================================================================//

#[test]
fn sequential_reads_reuse_the_chain() {
    let data = create_data(40 * SECTOR + 123, 1);
    let mut comp = create_comp();
    comp.create_stream("/big").unwrap().write_all(&data).unwrap();
    let mut comp = reopen(comp);
    let mut stream = comp.open_stream("/big").unwrap();
    let mut actual = vec![0u8; 100];
    let mut offset = 0;
    while offset < data.len() {
        let n = stream.read(&mut actual).unwrap();
        assert!(n > 0, "short read at {}", offset);
        assert_eq!(actual[..n], data[offset..offset + n], "at {}", offset);
        offset += n;
    }
    assert_eq!(stream.read(&mut actual).unwrap(), 0);
}

#[test]
fn scattered_reads_reuse_the_chain() {
    let data = create_data(64 * SECTOR, 2);
    let mut comp = create_comp();
    comp.create_stream("/big").unwrap().write_all(&data).unwrap();
    let mut comp = reopen(comp);
    let mut stream = comp.open_stream("/big").unwrap();
    let mut actual = [0u8; 16];
    for i in 0..200u64 {
        let offset = (i * 7919 * 13) % (data.len() as u64 - 16);
        stream.seek(SeekFrom::Start(offset)).unwrap();
        stream.read_exact(&mut actual).unwrap();
        let offset = offset as usize;
        assert_eq!(actual, data[offset..offset + 16], "at {}", offset);
    }
}

#[test]
fn interleaved_writes_to_two_streams() {
    let data_a = create_data(30 * SECTOR + 7, 3);
    let data_b = create_data(25 * SECTOR + 9, 4);
    let mut comp = create_comp();
    comp.create_stream("/a").unwrap().write_all(&data_a[..SECTOR]).unwrap();
    comp.create_stream("/b").unwrap().write_all(&data_b[..SECTOR]).unwrap();
    // Each append opens the chain anew after the other stream changed the
    // FAT, so a stale cached chain would corrupt one of the streams.
    let mut off_a = SECTOR;
    let mut off_b = SECTOR;
    while off_a < data_a.len() || off_b < data_b.len() {
        if off_a < data_a.len() {
            let end = (off_a + 3000).min(data_a.len());
            let mut stream = comp.open_stream("/a").unwrap();
            stream.seek(SeekFrom::End(0)).unwrap();
            stream.write_all(&data_a[off_a..end]).unwrap();
            off_a = end;
        }
        if off_b < data_b.len() {
            let end = (off_b + 5000).min(data_b.len());
            let mut stream = comp.open_stream("/b").unwrap();
            stream.seek(SeekFrom::End(0)).unwrap();
            stream.write_all(&data_b[off_b..end]).unwrap();
            off_b = end;
        }
    }
    assert_eq!(read_all(&mut comp, "/a"), data_a);
    assert_eq!(read_all(&mut comp, "/b"), data_b);
    let mut comp = reopen(comp);
    assert_eq!(read_all(&mut comp, "/a"), data_a);
    assert_eq!(read_all(&mut comp, "/b"), data_b);
}

#[test]
fn shrink_then_append() {
    let data = create_data(20 * SECTOR, 5);
    let mut comp = create_comp();
    comp.create_stream("/big").unwrap().write_all(&data).unwrap();
    {
        let mut stream = comp.open_stream("/big").unwrap();
        stream.set_len((8 * SECTOR + 100) as u64).unwrap();
    }
    // The freed sectors must not linger in the cached chain, or the
    // appended data would land in sectors that are no longer part of it.
    let tail = create_data(5 * SECTOR, 7);
    {
        let mut stream = comp.open_stream("/big").unwrap();
        stream.seek(SeekFrom::End(0)).unwrap();
        stream.write_all(&tail).unwrap();
    }
    let other = create_data(12 * SECTOR, 6);
    comp.create_stream("/other").unwrap().write_all(&other).unwrap();
    let mut expected = data[..8 * SECTOR + 100].to_vec();
    expected.extend_from_slice(&tail);
    let mut comp = reopen(comp);
    assert_eq!(read_all(&mut comp, "/big"), expected);
    assert_eq!(read_all(&mut comp, "/other"), other);
}

#[test]
fn shrink_into_mini_stream_then_grow_again() {
    let data = create_data(20 * SECTOR, 8);
    let mut comp = create_comp();
    comp.create_stream("/big").unwrap().write_all(&data).unwrap();
    {
        let mut stream = comp.open_stream("/big").unwrap();
        stream.set_len(1000).unwrap();
    }
    let tail = create_data(10 * SECTOR, 10);
    {
        let mut stream = comp.open_stream("/big").unwrap();
        stream.seek(SeekFrom::End(0)).unwrap();
        stream.write_all(&tail).unwrap();
    }
    let other = create_data(12 * SECTOR, 9);
    comp.create_stream("/other").unwrap().write_all(&other).unwrap();
    let mut expected = data[..1000].to_vec();
    expected.extend_from_slice(&tail);
    let mut comp = reopen(comp);
    assert_eq!(read_all(&mut comp, "/big"), expected);
    assert_eq!(read_all(&mut comp, "/other"), other);
}

#[test]
fn truncate_to_zero_then_rewrite() {
    let data = create_data(20 * SECTOR, 11);
    let mut comp = create_comp();
    comp.create_stream("/big").unwrap().write_all(&data).unwrap();
    comp.open_stream("/big").unwrap().set_len(0).unwrap();
    let other = create_data(12 * SECTOR, 12);
    comp.create_stream("/other").unwrap().write_all(&other).unwrap();
    let again = create_data(15 * SECTOR + 1, 13);
    comp.open_stream("/big").unwrap().write_all(&again).unwrap();
    let mut comp = reopen(comp);
    assert_eq!(read_all(&mut comp, "/big"), again);
    assert_eq!(read_all(&mut comp, "/other"), other);
}

#[test]
fn remove_then_recreate_stream() {
    let data = create_data(20 * SECTOR, 14);
    let mut comp = create_comp();
    comp.create_stream("/big").unwrap().write_all(&data).unwrap();
    comp.remove_stream("/big").unwrap();
    let other = create_data(12 * SECTOR, 15);
    comp.create_stream("/other").unwrap().write_all(&other).unwrap();
    let again = create_data(15 * SECTOR + 1, 16);
    comp.create_stream("/big").unwrap().write_all(&again).unwrap();
    let mut comp = reopen(comp);
    assert_eq!(read_all(&mut comp, "/big"), again);
    assert_eq!(read_all(&mut comp, "/other"), other);
}

//===========================================================================//
