use cfb::CompoundFile;
use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use std::fs::{File, OpenOptions};
use std::hint::black_box;
use std::io::Cursor;
use std::io::Read;
use std::io::Write;
use std::time::Duration;
use tempfile::NamedTempFile;

// The buffers a case writes into or reads into are created once per case and
// reused across iterations, so that the measurements cover the crate rather
// than the kernel mapping fresh memory: for the large sizes, filling a newly
// allocated Vec costs several times the copy itself.

/// Writes `n` streams of `data` into `buff`, reusing its allocation.
fn write_many_streams_into(buff: &mut Vec<u8>, data: &[u8], n: usize) {
    buff.clear();
    let mut test_comp = CompoundFile::create(Cursor::new(buff)).unwrap();
    for i in 0..n {
        let name = format!("test{i}");
        let mut stream = test_comp.create_stream(name).unwrap();
        stream.write_all(data).unwrap();
    }
}

fn write_many_streams(n: usize, size: usize) -> Vec<u8> {
    let mut buff = Vec::new();
    write_many_streams_into(&mut buff, &vec![0; size], n);
    buff
}

fn write_many_streams_to_file(tmpfile: &NamedTempFile, data: &[u8], n: usize) {
    let mut test_comp = CompoundFile::create(
        OpenOptions::new()
            .read(true)
            .write(true)
            .open(tmpfile.path())
            .unwrap(),
    )
    .unwrap();
    for i in 0..n {
        let name = format!("test{i}");
        let mut stream = test_comp.create_stream(name).unwrap();
        stream.write_all(data).unwrap();
    }
}

fn write_many_streams_disk(data: &[u8], n: usize) {
    let tmpfile = NamedTempFile::new().unwrap();
    write_many_streams_to_file(&tmpfile, data, n);
    // File is deleted when tmpfile is dropped
}

/// Reads every stream into `sink`, reusing its allocation.
fn read_many_streams(buff: &[u8], n: usize, sink: &mut Vec<u8>) {
    let mut test_comp = CompoundFile::open(Cursor::new(buff)).unwrap();
    for i in 0..n {
        let name = format!("test{i}");
        let mut stream = test_comp.open_stream(name).unwrap();
        sink.clear();
        stream.read_to_end(sink).unwrap();
        black_box(&sink);
    }
}

fn read_many_streams_disk(
    tmpfile: &NamedTempFile,
    n: usize,
    sink: &mut Vec<u8>,
) {
    // An unbuffered File, as `cfb::open` hands out.
    let mut test_comp =
        CompoundFile::open(File::open(tmpfile.path()).unwrap()).unwrap();
    for i in 0..n {
        let name = format!("test{i}");
        let mut stream = test_comp.open_stream(name).unwrap();
        sink.clear();
        stream.read_to_end(sink).unwrap();
        black_box(&sink);
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
        let data = vec![0u8; stream_size];
        let mut buff = Vec::new();
        group.bench_function(label, |b| {
            b.iter(|| {
                write_many_streams_into(
                    black_box(&mut buff),
                    black_box(&data),
                    black_box(stream_count),
                );
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
        let data = vec![0u8; stream_size];
        disk_group.bench_function(label, |b| {
            b.iter(|| {
                write_many_streams_disk(
                    black_box(&data),
                    black_box(stream_count),
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
        let mut sink = Vec::new();
        read_group.bench_function(label, |b| {
            b.iter(|| {
                read_many_streams(
                    black_box(&buff),
                    black_box(stream_count),
                    &mut sink,
                );
            })
        });
    }
    read_group.finish();

    let mut read_disk_group = c.benchmark_group("read_streams_disk");
    for (label, stream_size, stream_count) in stream_benches {
        let total_bytes = (stream_count * stream_size) as u64;
        let tmpfile = NamedTempFile::new().unwrap();
        write_many_streams_to_file(
            &tmpfile,
            &vec![0; stream_size],
            stream_count,
        );
        let mut sink = Vec::new();
        // Disk cases are slow per iteration; keep the group's run time down.
        read_disk_group.sample_size(10);
        read_disk_group.warm_up_time(Duration::from_secs(1));
        read_disk_group.measurement_time(Duration::from_secs(2));
        if total_bytes > 0 {
            read_disk_group.throughput(Throughput::Bytes(total_bytes));
        }
        read_disk_group.bench_function(label, |b| {
            b.iter(|| {
                read_many_streams_disk(
                    black_box(&tmpfile),
                    black_box(stream_count),
                    &mut sink,
                );
            })
        });
    }
    read_disk_group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
