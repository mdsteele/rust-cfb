use cfb::{CompoundFile, CreateStreamOptions};
use criterion::{
    criterion_group, criterion_main, BenchmarkId, Criterion, Throughput,
};
use std::fs::OpenOptions;
use std::hint::black_box;
use std::io::Cursor;
use std::io::Write;
use tempfile::NamedTempFile;

fn write_many_streams(
    n: usize,
    size: usize,
    stream_buffer_size: Option<usize>,
) -> Vec<u8> {
    let mut buff = Vec::new();
    {
        let mut test_comp =
            CompoundFile::create(Cursor::new(&mut buff)).unwrap();
        let data = vec![0; size];
        for i in 0..n {
            let name = format!("test{i}");
            let mut stream = match stream_buffer_size {
                Some(buf_size) => {
                    let options =
                        CreateStreamOptions::new().buffer_size(buf_size);
                    test_comp
                        .create_stream_with_options(name, options)
                        .unwrap()
                }
                None => test_comp.create_stream(name).unwrap(),
            };
            stream.write_all(&data).unwrap();
        }
    }
    buff
}

fn write_many_streams_disk(
    n: usize,
    size: usize,
    stream_buffer_size: Option<usize>,
) {
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
            let mut stream = match stream_buffer_size {
                Some(buf_size) => {
                    let options =
                        CreateStreamOptions::new().buffer_size(buf_size);
                    test_comp
                        .create_stream_with_options(name, options)
                        .unwrap()
                }
                None => test_comp.create_stream(name).unwrap(),
            };
            stream.write_all(&data).unwrap();
        }
    }
    // File is deleted when tmpfile is dropped
}

fn criterion_benchmark(c: &mut Criterion) {
    // Buffer sizes to compare (in bytes). `None` means the default internal
    // stream buffer size.
    let buffer_sizes: &[(Option<usize>, &str)] = &[
        (None, "default"),
        (Some(8 * 1024), "buffer=8192"),
        (Some(64 * 1024), "buffer=65536"),
        (Some(256 * 1024), "buffer=262144"),
        (Some(1024 * 1024), "buffer=1048576"),
    ];

    // many small streams with throughput reporting
    let mut small = c.benchmark_group("write many smaller streams");
    let size = 64usize;
    let n = 1000;
    let total_bytes = (n * size) as u64;
    small.sample_size(10);
    small.throughput(Throughput::Bytes(total_bytes));

    for (buf, label) in buffer_sizes {
        small.bench_with_input(
            BenchmarkId::new("total", *label),
            &size,
            |b, &s| {
                b.iter(|| {
                    let out = write_many_streams(
                        black_box(n),
                        black_box(s),
                        buf.map(black_box),
                    );
                    black_box(out);
                })
            },
        );
    }
    small.finish();

    // several medium streams with throughput reporting
    let mut medium = c.benchmark_group("write several medium streams");
    let size = 1024 * 1024usize;
    let n = 50;
    let total_bytes = (n * size) as u64;
    medium.sample_size(10);
    medium.throughput(Throughput::Bytes(total_bytes));

    for (buf, label) in buffer_sizes {
        medium.bench_with_input(
            BenchmarkId::new("total", *label),
            &size,
            |b, &s| {
                b.iter(|| {
                    let out = write_many_streams(
                        black_box(n),
                        black_box(s),
                        buf.map(black_box),
                    );
                    black_box(out);
                })
            },
        );
    }
    medium.finish();

    // single large stream with throughput reporting
    let mut group = c.benchmark_group("write large stream");
    let size = 256 * 1024 * 1024usize;
    let n = 1;
    group.sample_size(10);
    group.throughput(Throughput::Bytes(size as u64));
    for (buf, label) in buffer_sizes {
        group.bench_with_input(
            BenchmarkId::new("total", *label),
            &size,
            |b, &s| {
                b.iter(|| {
                    let out = write_many_streams(
                        black_box(n),
                        black_box(s),
                        buf.map(black_box),
                    );
                    black_box(out);
                })
            },
        );
    }
    group.finish();

    // many small streams with throughput reporting (disk)
    let mut small_disk =
        c.benchmark_group("write many smaller streams (disk)");
    let size = 64usize;
    let n = 1000;
    let total_bytes = (n * size) as u64;
    small_disk.sample_size(10);
    small_disk.throughput(Throughput::Bytes(total_bytes));
    for (buf, label) in buffer_sizes {
        small_disk.bench_with_input(
            BenchmarkId::new("total", *label),
            &size,
            |b, &s| {
                b.iter(|| {
                    write_many_streams_disk(
                        black_box(n),
                        black_box(s),
                        buf.map(black_box),
                    );
                })
            },
        );
    }
    small_disk.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
