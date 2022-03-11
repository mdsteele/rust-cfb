#![no_main]
use cfb::CompoundFile;
use libfuzzer_sys::fuzz_target;
use std::io::{Cursor, Read};

fuzz_target!(|data: &[u8]| {
    let cursor = Cursor::new(data);
    let mut cfb = match CompoundFile::open(cursor) {
        Ok(cfb) => cfb,
        Err(_) => return,
    };
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
});
