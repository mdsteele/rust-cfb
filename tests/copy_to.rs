use cfb::{CompoundFile, Version};
use std::io::{Cursor, Read, Seek, SeekFrom, Write};
use std::path::PathBuf;
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use uuid::Uuid;

//===========================================================================//

fn pattern(len: usize, seed: u8) -> Vec<u8> {
    (0..len).map(|i| (i as u8).wrapping_mul(37).wrapping_add(seed)).collect()
}

fn epoch_plus(secs: u64) -> SystemTime {
    UNIX_EPOCH + Duration::from_secs(secs)
}

/// Builds a file with nested storages, mini and regular streams, metadata on
/// several entries, and wasted space from a removed and a shrunk stream.
fn build_source(version: Version) -> CompoundFile<Cursor<Vec<u8>>> {
    let mut comp =
        CompoundFile::create_with_version(version, Cursor::new(Vec::new()))
            .unwrap();
    comp.create_storage("/a").unwrap();
    comp.create_storage_all("/a/b/c").unwrap();
    comp.create_stream("/small").unwrap().write_all(&pattern(100, 1)).unwrap();
    comp.create_stream("/a/empty").unwrap();
    comp.create_stream("/a/b/c/mid")
        .unwrap()
        .write_all(&pattern(5000, 2))
        .unwrap();
    {
        let mut stream = comp.create_stream("/a/large").unwrap();
        stream.write_all(&pattern(200_000, 4)).unwrap();
        stream.set_len(100_000).unwrap();
    }
    // Written last, so that nothing reuses its sectors once it is gone.
    comp.create_stream("/junk")
        .unwrap()
        .write_all(&pattern(300_000, 3))
        .unwrap();
    comp.remove_stream("/junk").unwrap();
    comp.set_storage_clsid("/", Uuid::from_u128(0x1111)).unwrap();
    comp.set_storage_clsid("/a/b", Uuid::from_u128(0x2222)).unwrap();
    comp.set_state_bits("/small", 0x1234).unwrap();
    comp.set_state_bits("/a", 0x5678).unwrap();
    comp.set_created_time("/a", epoch_plus(1_000_000)).unwrap();
    comp.set_modified_time("/a/b/c", epoch_plus(2_000_000)).unwrap();
    comp.set_modified_time("/", epoch_plus(3_000_000)).unwrap();
    comp
}

type Snapshot = Vec<(PathBuf, bool, u64, Uuid, u32, SystemTime, SystemTime)>;

fn snapshot<F>(comp: &CompoundFile<F>) -> Snapshot {
    comp.walk()
        .map(|e| {
            (
                e.path().to_path_buf(),
                e.is_stream(),
                e.len(),
                *e.clsid(),
                e.state_bits(),
                e.created(),
                e.modified(),
            )
        })
        .collect()
}

fn stream_contents<F: Read + Seek>(
    comp: &mut CompoundFile<F>,
) -> Vec<(PathBuf, Vec<u8>)> {
    let paths: Vec<PathBuf> = comp
        .walk()
        .filter(|e| e.is_stream())
        .map(|e| e.path().to_path_buf())
        .collect();
    paths
        .into_iter()
        .map(|path| {
            let mut data = Vec::new();
            comp.open_stream(&path).unwrap().read_to_end(&mut data).unwrap();
            (path, data)
        })
        .collect()
}

//===========================================================================//

#[test]
fn copy_preserves_tree_metadata_and_contents() {
    for version in [Version::V3, Version::V4] {
        let mut source = build_source(version);
        let mut copy = source.copy_to(Cursor::new(Vec::new())).unwrap();
        assert_eq!(copy.version(), version);
        assert_eq!(snapshot(&copy), snapshot(&source));
        assert_eq!(stream_contents(&mut copy), stream_contents(&mut source));
        assert_eq!(
            copy.entry("/a/large").unwrap().len(),
            100_000,
            "shrunk stream keeps its new length"
        );

        // The copy must also hold up on disk, under strict validation.
        let mut reopened =
            CompoundFile::open_strict(copy.into_inner()).unwrap();
        assert_eq!(snapshot(&reopened), snapshot(&source));
        assert_eq!(
            stream_contents(&mut reopened),
            stream_contents(&mut source)
        );
    }
}

#[test]
fn copy_drops_the_space_of_removed_and_shrunk_streams() {
    let mut source = build_source(Version::V4);
    let copy = source.copy_to(Cursor::new(Vec::new())).unwrap();
    let source_len = source.into_inner().into_inner().len();
    let copy_len = copy.into_inner().into_inner().len();
    // The source still holds every sector the removed stream and the shrunk
    // one ever used; the copy holds only the 105 KB that is live plus a few
    // sectors of metadata.
    assert!(source_len > 400_000, "source is {} bytes", source_len);
    assert!(copy_len < 140_000, "copy is {} bytes", copy_len);
}

#[test]
fn copy_from_a_read_only_source() {
    let bytes = build_source(Version::V3).into_inner().into_inner();
    // A `Cursor<&[u8]>` can be read and seeked but not written.
    let mut source =
        CompoundFile::open(Cursor::new(bytes.as_slice())).unwrap();
    let mut copy = source.copy_to(Cursor::new(Vec::new())).unwrap();
    assert_eq!(snapshot(&copy), snapshot(&source));
    assert_eq!(stream_contents(&mut copy), stream_contents(&mut source));
}

#[test]
fn copy_of_an_empty_file() {
    let mut source = CompoundFile::create(Cursor::new(Vec::new())).unwrap();
    let copy = source.copy_to(Cursor::new(Vec::new())).unwrap();
    assert_eq!(snapshot(&copy), snapshot(&source));
    CompoundFile::open_strict(copy.into_inner()).unwrap();
}

#[test]
fn copy_leaves_the_source_readable() {
    let mut source = build_source(Version::V3);
    let before = snapshot(&source);
    source.copy_to(Cursor::new(Vec::new())).unwrap();
    assert_eq!(snapshot(&source), before);
    let mut stream = source.open_stream("/a/b/c/mid").unwrap();
    stream.seek(SeekFrom::Start(4000)).unwrap();
    let mut tail = Vec::new();
    stream.read_to_end(&mut tail).unwrap();
    assert_eq!(tail, pattern(5000, 2)[4000..]);
}

//===========================================================================//
