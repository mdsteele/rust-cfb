#![no_main]
//! Drives the write side from fuzz input: a sequence of stream and storage
//! creations, writes and removals with names and sizes taken from the
//! bytes.  Afterwards the file must reopen under strict validation, every
//! stream the model still expects must be found with the right content,
//! and nothing else may be there.
use cfb::CompoundFile;
use libfuzzer_sys::fuzz_target;
use std::collections::HashMap;
use std::io::{Cursor, Read, Write};

fuzz_target!(|data: &[u8]| {
    let mut comp = CompoundFile::create(Cursor::new(Vec::new())).unwrap();
    // uppercased path -> Some(content) for streams, None for storages
    // (names are case-insensitive, so `/s1` and `/S1` are one entry)
    let mut model: HashMap<String, Option<Vec<u8>>> = HashMap::new();
    let storages = ["/", "/A", "/B", "/A/C"];
    let mut bytes = data.iter().copied();
    while let (Some(op), Some(n1), Some(n2)) = (bytes.next(), bytes.next(), bytes.next()) {
        let parent = storages[(n1 % 4) as usize];
        // Names: a small alphabet with case variants, so that the same name
        // in different cases and near-duplicates come up often.
        let name = match n2 % 6 {
            0 => format!("s{}", n1 / 4),
            1 => format!("S{}", n1 / 4),
            2 => format!("item{}", n1),
            3 => format!("ITEM{}", n1),
            4 => format!("{}", char::from(b'a' + n1 % 26)),
            _ => format!("x{}y{}", n1 % 7, n2 % 5),
        };
        let path = if parent == "/" { format!("/{name}") } else { format!("{parent}/{name}") };
        let key = path.to_uppercase();
        match op % 5 {
            0 | 1 | 2 => {
                // Storages must exist first; skip creating under a missing one.
                // The parent must exist and be a storage (a stream of that
                // name, in any case, is not one).
                if parent != "/" && model.get(&parent.to_uppercase()) != Some(&None) {
                    continue;
                }
                if model.get(&key).map(|e| e.is_none()).unwrap_or(false) {
                    continue; // a storage of that name exists
                }
                let len = (op as usize) * 700 + n2 as usize * 3; // 0..~2100 + up to 765
                let len = if n1 % 5 == 0 { len * 4 } else { len }; // sometimes past the mini cutoff
                let content: Vec<u8> = (0..len).map(|i| (i as u8) ^ n1).collect();
                let mut stream = comp.create_stream(&path).unwrap();
                stream.write_all(&content).unwrap();
                drop(stream);
                model.insert(key, Some(content));
            }
            3 => {
                if let Some(Some(_)) = model.get(&key) {
                    comp.remove_stream(&path).unwrap();
                    model.remove(&key);
                }
            }
            _ => {
                // Create one of the fixed storages if missing.
                let storage = storages[1 + (n2 % 3) as usize];
                let parent_ok = storage == "/A" || storage == "/B" || model.get("/A") == Some(&None);
                if parent_ok && !model.contains_key(&storage.to_uppercase()) {
                    comp.create_storage(storage).unwrap();
                    model.insert(storage.to_uppercase(), None);
                }
            }
        }
    }
    comp.flush().unwrap();
    let bytes = comp.into_inner().into_inner();
    let mut comp = CompoundFile::open_strict(Cursor::new(bytes)).expect("strict reopen");
    let entries: Vec<(String, bool)> = comp
        .walk()
        .map(|e| (e.path().to_str().unwrap().to_string(), e.is_stream()))
        .collect();
    let mut found = 0;
    for (path, is_stream) in entries {
        if path == "/" {
            continue;
        }
        found += 1;
        match model.get(&path.to_uppercase()) {
            Some(Some(content)) => {
                assert!(is_stream, "{path}");
                let mut back = Vec::new();
                comp.open_stream(&path).unwrap().read_to_end(&mut back).unwrap();
                assert_eq!(&back, content, "{path}");
            }
            Some(None) => assert!(!is_stream, "{path}"),
            None => panic!("unexpected entry {path}"),
        }
    }
    assert_eq!(found, model.len(), "entry count");
});
