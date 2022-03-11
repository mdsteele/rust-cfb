use byteorder::{LittleEndian, WriteBytesExt};
use cfb::CompoundFile;
use std::io::{Cursor, Read, Seek, SeekFrom, Write};

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
