use byteorder::{LittleEndian, WriteBytesExt};
use cfb::CompoundFile;
use std::{
    fs::read_dir,
    io::{Cursor, Read, Seek, SeekFrom, Write},
    path::Path,
    sync::mpsc,
    thread,
    time::Duration,
};

// Run function on another thread, panic if it takes too long
fn panic_after<T, F>(d: Duration, f: F) -> T
where
    T: Send + 'static,
    F: FnOnce() -> T,
    F: Send + 'static,
{
    let (done_tx, done_rx) = mpsc::channel();
    let handle = thread::spawn(move || {
        let val = f();
        done_tx.send(()).expect("Unable to send completion signal");
        val
    });

    match done_rx.recv_timeout(d) {
        Ok(_) => handle.join().expect("Thread panicked"),
        Err(_) => panic!("Thread took too long"),
    }
}

// Checks to see if a file can be walked over and read properly, or fail if it can not be read
fn can_read(path: &Path) {
    let data = std::fs::read(path).unwrap();

    let cursor = Cursor::new(data);
    let mut cfb = match CompoundFile::open(cursor) {
        Ok(cfb) => cfb,
        Err(_) => return,
    };

    #[allow(clippy::needless_collect)]
    let stream_paths = cfb
        .walk()
        .filter(|e| e.is_stream())
        .map(|e| e.path().to_path_buf())
        .collect::<Vec<_>>();

    let _unused = stream_paths
        .into_iter()
        .map(|s| -> Result<Vec<u8>, std::io::Error> {
            let mut data = Vec::new();
            cfb.open_stream(&s)?.read_to_end(&mut data)?;
            Ok(data)
        })
        .collect::<Vec<_>>();
}

/// Regression test for https://github.com/mdsteele/rust-cfb/issues/16.
#[test]
#[should_panic(
    expected = "Found reference to mini sector 123456789, but MiniFAT has \
                only 2 entries"
)]
fn invalid_mini_sector_issue_16() {
    // Create a CFB file with a mini stream.
    let cursor = Cursor::new(Vec::new());
    let mut comp = CompoundFile::create(cursor).unwrap();
    let version = comp.version();
    comp.create_stream("foo").unwrap().write_all(&[0u8; 80]).unwrap();
    let mut cursor = comp.into_inner();

    // Corrupt the starting mini sector ID of the stream.  Due to how we
    // constructed the CFB file, this will be at byte 116 of the second
    // 128-byte directory entry in the third sector of the CFB file.
    let offset = 116 + 128 * 1 + (version.sector_len() as u64) * 2;
    cursor.seek(SeekFrom::Start(offset)).unwrap();
    cursor.write_u32::<LittleEndian>(123456789).unwrap();

    // Re-open the CFB file and try to read the mini stream.
    let mut comp = CompoundFile::open(cursor).unwrap();
    let mut data = Vec::new();
    comp.open_stream("foo").unwrap().read_to_end(&mut data).unwrap();
}

/// Regression test for https://github.com/mdsteele/rust-cfb/issues/17.
#[test]
#[should_panic(expected = "DIFAT chain includes duplicate sector index 0")]
fn infinite_loop_difat_issue_17() {
    let data = vec![
        208, 207, 17, 224, 161, 177, 26, 225, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
        128, 0, 0, 0, 0, 62, 0, 3, 0, 254, 255, 9, 0, 6, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 255,
        255, 255, 255, 255, 255, 255, 27, 80, 255, 255, 253, 0, 0, 0, 254,
        255, 255, 255, 28, 0, 0, 0, 5, 0, 0, 0, 6, 0, 0, 0, 7, 0, 0, 0, 8, 0,
        0, 0, 9, 0, 0, 0, 10, 0, 0, 0, 11, 0, 0, 0, 12, 0, 0, 0, 13, 0, 0, 0,
        14, 0, 0, 0, 15, 208, 207, 17, 224, 161, 177, 26, 225, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62, 0, 3, 0, 254, 255, 9, 0, 6, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 16,
        0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 254, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0,
        0, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 0, 0, 0, 16, 0, 0, 0, 17, 0, 0, 0, 18, 0, 0,
        0, 19, 0, 0, 0, 20, 0, 1, 0, 0, 0, 0, 0, 9, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 252, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 253, 255, 255, 255, 27, 0, 0, 0, 254, 255, 255, 255,
        28, 0, 0, 0, 5, 0, 0, 0, 0, 255, 27, 0, 0, 0, 254, 255, 255, 255, 28,
        0, 0, 0, 5, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 62, 0, 3, 0, 254, 255, 9,
        0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0,
        0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 254, 255,
        255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 253, 255, 255, 255, 27, 0, 0, 0,
        254, 255, 255, 255, 28, 0, 0, 0, 5, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 253, 255, 255, 255, 27, 0, 0, 0, 254, 255, 255, 255, 28, 0, 0, 0,
        5, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
    ];
    CompoundFile::open(Cursor::new(data)).unwrap();
}

#[test]
#[should_panic(
    expected = "Invalid CFB file (length of 512 < sector length of 4096)"
)]
fn sector_panic_pr_24() {
    let data = vec![
        208, 207, 17, 224, 161, 177, 26, 225, 47, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 254, 255, 12, 0, 6, 0, 0, 0, 0, 0, 255,
        255, 0, 0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 16, 0, 0, 5,
        5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 5, 5, 5, 5, 5, 59, 5,
        5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 176, 5, 5, 5,
        5, 5, 5, 208, 207, 17, 224, 255, 177, 26, 225, 0, 0, 5, 5, 5, 5, 5, 5,
        5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 176, 5, 5, 5, 5, 5, 5,
        208, 207, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        229, 229, 229, 229, 229, 229, 231, 229, 229, 229, 229, 229, 229, 229,
        229, 229, 229, 229, 0, 229, 255, 255, 255, 255, 255, 255, 223, 255, 5,
        5, 5, 5, 5, 5, 15, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 176, 5, 5, 5, 5,
        5, 5, 5, 5, 5, 5, 13, 5, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 255, 255,
        255, 255, 255, 17, 224, 255, 255, 255, 255, 255, 255, 255, 255, 177,
        26, 225, 0, 0, 255, 255, 255, 255, 255, 255, 255, 255, 8, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 207, 207,
        207, 207, 207, 207, 207, 207, 207, 207, 207, 207, 207, 207, 207, 207,
        207, 207, 207, 207, 207, 207, 207, 207, 207, 207, 207, 207, 207, 207,
        207, 207, 207, 207, 207, 207, 207, 207, 207, 207, 207, 207, 207, 207,
        207, 207, 207, 207, 207, 207, 207, 207, 207, 207, 207, 207, 207, 207,
        207, 207, 55, 50, 49, 51, 86, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        207, 207, 207, 207, 207, 12, 0, 0, 0, 0, 0, 0, 0, 207, 207, 207, 207,
        207, 207, 207, 207, 207, 207, 207, 5, 5, 5, 5, 5, 5, 5, 5, 12, 0, 6,
        0, 0, 0, 0, 0, 255, 255, 0, 0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
        5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 255, 255, 255, 255,
        255, 17, 224, 255, 255, 255, 255, 255, 255, 255, 255, 177, 26, 225, 0,
        0, 255, 255, 255, 255, 255, 255, 255, 255, 8, 0,
    ];
    CompoundFile::open(Cursor::new(data)).unwrap();
}

#[test]
#[should_panic(expected = "next_id (4294967293) is invalid")]
fn alloc_panic_pr_24() {
    let mut cfb = cfb::open("tests/panics_fuzzed/alloc_panic").unwrap();
    cfb.walk()
        .filter(|e| e.is_stream())
        .map(|e| e.path().to_path_buf())
        .collect::<Vec<_>>()
        .into_iter()
        .map(|s| {
            let mut data = Vec::new();
            cfb.open_stream(&s).unwrap().read_to_end(&mut data).unwrap();
            Ok((s, data))
        })
        .collect::<Result<std::collections::HashMap<_, _>, std::io::Error>>()
        .unwrap();
}

#[test]
#[should_panic(expected = "next_id (4294967295) is invalid")]
fn minialloc_panic_pr_24() {
    let mut cfb = cfb::open("tests/panics_fuzzed/minialloc_panic").unwrap();
    cfb.walk()
        .filter(|e| e.is_stream())
        .map(|e| e.path().to_path_buf())
        .collect::<Vec<_>>()
        .into_iter()
        .map(|s| {
            let mut data = Vec::new();
            cfb.open_stream(&s).unwrap().read_to_end(&mut data).unwrap();
            Ok((s, data))
        })
        .collect::<Result<std::collections::HashMap<_, _>, std::io::Error>>()
        .unwrap();
}

#[test]
fn check_for_infinite_loops() {
    // Loop through the provided files
    for entry in read_dir("tests/infinite_loops_fuzzed").unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        // Test will panic if it takes more than 1 second to load the file ie. stuck in a loop
        panic_after(Duration::from_secs(1), move || can_read(&path))
    }
}

#[rustfmt::skip]
fn difat_terminate_in_freesect() -> Cursor<Vec<u8>> {
    let mut data = Vec::with_capacity(7_864_832);

    // Header
    // =============================
    data.extend_from_slice(&[
        0xd0, 0xcf, 0x11, 0xe0, 0xa1, 0xb1, 0x1a, 0xe1, // Header signature
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // Header CLSID
        0x3e, 0x00, // Minor Version
        0x03, 0x00, // Major Version
        0xfe, 0xff, // Byte Order
        0x09, 0x00, // Sector Shift
        0x06, 0x00, // Mini Sector Shift
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // Reserved
        0x00, 0x00, 0x00, 0x00, // Number of Directory Sectors
        0x78, 0x00, 0x00, 0x00, // Number of FAT Sectors - 120
        0x01, 0x00, 0x00, 0x00, // First Directory Sector Location
        0x00, 0x00, 0x00, 0x00, // Transaction Signature Number
        0x00, 0x10, 0x00, 0x00, // Mini Stream Cutoff Size
        0xfe, 0xff, 0xff, 0xff, // First Mini FAT Sector Location - end of chain
        0x00, 0x00, 0x00, 0x00, // Number of Mini FAT Sectors - None
        0x02, 0x00, 0x00, 0x00, // First DIFAT Sector Location
        0x01, 0x00, 0x00, 0x00, // Number of DIFAT Sectors
    ]);
    // First 109 DIFAT Sectors
    data.extend_from_slice(&[0x00, 0x00, 0x00, 0x00]);
    for i in 0..108 {
        data.extend_from_slice(&[i + 3, 0x00, 0x00, 0x00]);
    }

    // First FAT Sector
    // =============================
    data.extend_from_slice(&[
        0xfd, 0xff, 0xff, 0xff, // FAT sector - The current sector
        0xfe, 0xff, 0xff, 0xff, // Directory - End of chain, just the one
        0xfc, 0xff, 0xff, 0xff, // DIFAT #2
    ]);
    // The remaining 119 FAT sectors
    for _ in 0..119 {
        data.extend_from_slice(&[0xfd, 0xff, 0xff, 0xff]);
    }
    // The first 6 sectors for content, make it all one stream
    for i in 0..6 {
        data.extend_from_slice(&[i + 123, 0x00, 0x00, 0x00]);
    }

    // Directory
    // =============================
    // Root entry
    data.extend_from_slice(&[
        b'R', 0x00, b'o', 0x00, b'o', 0x00, b't', 0x00, b' ', 0x00, b'E', 0x00, b'n', 0x00, b't', 0x00,
        b'r', 0x00, b'y', 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // Directory Entry Name
        0x16, 0x00, // Directory Entry Name Length
        0x05, // Object Type - Root Storage Object
        0x00, // Color Flag - red
        0xff, 0xff, 0xff, 0xff, // Left Sibling ID - None
        0xff, 0xff, 0xff, 0xff, // Right Sibling ID - None
        0x01, 0x00, 0x00, 0x00, // Child ID - Stream 1
        0x00, 0x67, 0x61, 0x56, 0x54, 0xc1, 0xce, 0x11, 0x85, 0x53, 0x00, 0xaa, 0x00, 0xa1, 0xf9, 0x5b, // CLSID
        0x00, 0x00, 0x00, 0x00, // State Bits
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // Creation Time
        0xb0, 0xfd, 0x97, 0x18, 0xab, 0xe9, 0xc4, 0x01, // Modification Time
        0x00, 0x00, 0x00, 0x00, // Starting Sector Location - Mini-stream, None as not using
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // Stream Size - Mini-stream, None as not using
    ]);
    // Stream 1
    data.extend_from_slice(&[
        b'S', 0x00, b't', 0x00, b'r', 0x00, b'e', 0x00, b'a', 0x00, b'm', 0x00, b' ', 0x00, b'1', 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // Directory Entry Name
        0x12, 0x00, // Directory Entry Name Length
        0x02, // Object Type - Stream Object
        0x01, // Color Flag - black
        0xff, 0xff, 0xff, 0xff, // Left Sibling ID - None
        0xff, 0xff, 0xff, 0xff, // Right Sibling ID - None
        0xff, 0xff, 0xff, 0xff, // Child ID - No stream
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // CLSID
        0x00, 0x00, 0x00, 0x00, // State Bits
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // Creation Time
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // Modification Time
        0x7c, 0x00, 0x00, 0x00, // Starting Sector Location - 124
        0x00, 0x0c, 0x77, 0x00, 0x00, 0x00, 0x00, 0x00, // Stream Size - 7_801_856 bytes
        // ((119 FAT pages * 128 sectors per page) + 6 sectors from 1st page) * 512 bytes per sector
    ]);
    // Unused
    data.extend_from_slice(&[
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // Directory Entry Name
        0x00, 0x00, // Directory Entry Name Length
        0x00, // Object Type
        0x00, // Color Flag
        0xff, 0xff, 0xff, 0xff, // Left Sibling ID - None
        0xff, 0xff, 0xff, 0xff, // Right Sibling ID - None
        0xff, 0xff, 0xff, 0xff, // Child ID - No stream
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // CLSID
        0x00, 0x00, 0x00, 0x00, // State Bits
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // Creation Time
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // Modification Time
        0x00, 0x00, 0x00, 0x00, // Starting Sector Location
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // Stream Size
    ]);
    // Unused
    data.extend_from_slice(&[
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // Directory Entry Name
        0x00, 0x00, // Directory Entry Name Length
        0x00, // Object Type
        0x00, // Color Flag
        0xff, 0xff, 0xff, 0xff, // Left Sibling ID - None
        0xff, 0xff, 0xff, 0xff, // Right Sibling ID - None
        0xff, 0xff, 0xff, 0xff, // Child ID - No stream
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // CLSID
        0x00, 0x00, 0x00, 0x00, // State Bits
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // Creation Time
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // Modification Time
        0x00, 0x00, 0x00, 0x00, // Starting Sector Location
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // Stream Size
    ]);

    // DIFAT #2
    // =============================
    // DIFAT Sectors 110 to 120
    for i in 0..11 {
        data.extend_from_slice(&[i + 111, 0x00, 0x00, 0x00]);
    }
    // Pad out the rest of the sector with free sector markers
    for _ in 0..116 {
        data.extend_from_slice(&[0xff, 0xff, 0xff, 0xff]);
    }
    // Next DIFAT Sector Location
    // NOTE: This is wrong and should be 0xfffffffe
    data.extend_from_slice(&[0xff, 0xff, 0xff, 0xff]);

    // Subsequent FAT Sectors
    // =============================
    let mut lower = 128;
    let mut upper = 0;
    let range = (119 * 128) - 1;
    for _ in 0..range {
        if lower == 0xff {
            lower = 0x00;
            upper += 1;
        } else {
            lower += 1;
        }
        data.extend_from_slice(&[lower, upper, 0x00, 0x00]);
    }
    // End the chain with an end of chain marker
    data.extend_from_slice(&[0xfe, 0xff, 0xff, 0xff]);

    // The stream data
    // =============================
    let sectors = (119 * 128) + 6;
    for _ in 0..sectors {
        data.extend_from_slice(&[
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ]);
    }

    Cursor::new(data)
}

#[test]
fn open_difat_terminate_freesect() {
    CompoundFile::open(difat_terminate_in_freesect()).unwrap();
}

#[test]
#[should_panic(
    expected = "DIFAT chain must terminate with 4294967294, not 4294967295"
)]
fn open_strict_difat_terminate_freesect() {
    CompoundFile::open_strict(difat_terminate_in_freesect()).unwrap();
}

/// Regression test for https://github.com/mdsteele/rust-cfb/issues/52.
#[test]
#[should_panic(
    expected = "Directory chain includes at least 2 sectors which is greater than header num_dir_sectors 1"
)]
fn invalid_num_dir_sectors_issue_52() {
    // Create a CFB file with 2 sectors for the directory.
    let cursor = Cursor::new(Vec::new());
    let mut comp = CompoundFile::create(cursor).unwrap();
    // root + 31 entries in the first sector
    // 1 stream entry in the second sector
    for i in 0..32 {
        let path = format!("stream{}", i);
        let path = Path::new(&path);
        comp.create_stream(path).unwrap();
    }
    comp.flush().unwrap();

    // update the header and set num_dir_sectors = 1 instead of 2
    let mut cursor = comp.into_inner();
    cursor.seek(SeekFrom::Start(40)).unwrap();
    cursor.write_u32::<LittleEndian>(1).unwrap();
    cursor.flush().unwrap();

    // Read the file back in.
    CompoundFile::open_strict(cursor).unwrap();
}
