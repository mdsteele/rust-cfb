use cfb::CompoundFile;
use std::io::{Cursor, Write};

/// Streams created in ascending name order (the common case: `Item0`,
/// `Item1`, ...) used to be appended to one long branch of the sibling
/// tree.  The tree is now kept balanced, and strict validation of the
/// result checks the red-black coloring rules that the rebalancing has to
/// respect.
#[test]
fn many_streams_reopen_strictly_after_inserts_and_removals() {
    let mut comp = CompoundFile::create(Cursor::new(Vec::new())).unwrap();
    comp.create_storage("/Items").unwrap();
    for i in 0..3000 {
        let mut stream =
            comp.create_stream(format!("/Items/Item{i}")).unwrap();
        stream.write_all(&[i as u8; 100]).unwrap();
    }
    for i in (0..3000).step_by(5) {
        comp.remove_stream(format!("/Items/Item{i}")).unwrap();
    }
    for i in (0..3000).step_by(7) {
        comp.create_stream(format!("/Items/Item{i}")).unwrap();
    }
    let bytes = comp.into_inner().into_inner();

    let comp = CompoundFile::open_strict(Cursor::new(bytes)).unwrap();
    let names: Vec<String> = comp
        .read_storage("/Items")
        .unwrap()
        .map(|entry| entry.name().to_string())
        .collect();
    for i in 0..3000 {
        let expected = i % 5 != 0 || i % 7 == 0;
        assert_eq!(
            comp.exists(format!("/Items/Item{i}")),
            expected,
            "Item{i}"
        );
        assert_eq!(names.contains(&format!("Item{i}")), expected);
    }
}
