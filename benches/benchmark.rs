use cfb::CompoundFile;
use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use std::fs::OpenOptions;
use std::hint::black_box;
use std::io::Cursor;
use std::io::Read;
use std::io::Write;
use tempfile::NamedTempFile;

fn write_many_streams(n: usize, size: usize) -> Vec<u8> {
    let mut buff = Vec::new();
    {
        let mut test_comp =
            CompoundFile::create(Cursor::new(&mut buff)).unwrap();
        let data = vec![0; size];
        for i in 0..n {
            let name = format!("test{i}");
            let mut stream = test_comp.create_stream(name).unwrap();
            stream.write_all(&data).unwrap();
        }
    }
    buff
}

fn write_many_streams_disk(n: usize, size: usize) {
    let tmpfile = NamedTempFile::new().unwrap();
    {
        let mut test_comp = CompoundFile::create(
            OpenOptions::new()
                .read(true)
                .write(true)
                .open(tmpfile.path())
                .unwrap(),
        )
        .unwrap();
        let data = vec![0; size];
        for i in 0..n {
            let name = format!("test{i}");
            let mut stream = test_comp.create_stream(name).unwrap();
            stream.write_all(&data).unwrap();
        }
    }
    // File is deleted when tmpfile is dropped
}

fn read_many_streams(buff: &[u8], n: usize) {
    let mut test_comp = CompoundFile::open(Cursor::new(buff)).unwrap();
    for i in 0..n {
        let name = format!("test{i}");
        let mut stream = test_comp.open_stream(name).unwrap();
        let mut sink = Vec::new();
        stream.read_to_end(&mut sink).unwrap();
        black_box(sink);
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    let stream_benches = [
        // (label, stream_size, stream_count)
        ("n=10000,size=0B", 0, 10000usize),
        ("n=1000,size=64B", 64usize, 1000usize),
        ("n=100,size=4KiB-1 (MiniFAT)", 1024 * 4 - 1, 100usize),
        ("n=100,size=4KiB (FAT)", 1024 * 4, 100usize),
        ("n=50,size=1MiB", 1024 * 1024usize, 50usize),
        ("n=1,size=256MiB", 256 * 1024 * 1024usize, 1usize),
    ];

    let mut group = c.benchmark_group("write_streams_memory");
    for (label, stream_size, stream_count) in stream_benches {
        let total_bytes = (stream_count * stream_size) as u64;
        group.sample_size(10);
        if total_bytes > 0 {
            group.throughput(Throughput::Bytes(total_bytes));
        }
        group.bench_function(label, |b| {
            b.iter(|| {
                let out = write_many_streams(
                    black_box(stream_count),
                    black_box(stream_size),
                );
                black_box(out);
            })
        });
    }
    group.finish();

    let mut disk_group = c.benchmark_group("write_streams_disk");
    for (label, stream_size, stream_count) in stream_benches {
        let total_bytes = (stream_count * stream_size) as u64;
        disk_group.sample_size(10);
        if total_bytes > 0 {
            disk_group.throughput(Throughput::Bytes(total_bytes));
        }
        disk_group.bench_function(label, |b| {
            b.iter(|| {
                write_many_streams_disk(
                    black_box(stream_count),
                    black_box(stream_size),
                );
            })
        });
    }
    disk_group.finish();

    let mut read_group = c.benchmark_group("read_streams_memory");
    for (label, stream_size, stream_count) in stream_benches {
        let total_bytes = (stream_count * stream_size) as u64;
        let buff = write_many_streams(stream_count, stream_size);
        read_group.sample_size(10);
        if total_bytes > 0 {
            read_group.throughput(Throughput::Bytes(total_bytes));
        }
        read_group.bench_function(label, |b| {
            b.iter(|| {
                read_many_streams(black_box(&buff), black_box(stream_count));
            })
        });
    }
    read_group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
