use cfb::CompoundFile;
use criterion::{
    criterion_group, criterion_main, BenchmarkId, Criterion, Throughput,
};
use std::hint::black_box;
use std::io::Cursor;
use std::io::Write;

fn write_many_streams(n: usize, size: usize) -> Vec<u8> {
    let mut buff = Vec::new();
    {
        let mut test_comp =
            CompoundFile::create(Cursor::new(&mut buff)).unwrap();
        let data = vec![0; size];
        for i in 0..n {
            let mut stream =
                test_comp.create_stream(format!("test{i}")).unwrap();
            stream.write_all(&data).unwrap();
        }
    }
    buff
}

fn criterion_benchmark(c: &mut Criterion) {
    // many small streams
    let size = 64usize;
    let n = 1000;
    c.bench_function("write many smaller streams", |b| {
        b.iter(|| {
            let out = write_many_streams(black_box(n), black_box(size));
            black_box(out);
        })
    });

    // a few medium streams
    let size = 1024 * 1024usize;
    let n = 50;
    c.bench_function("write several medium streams", |b| {
        b.iter(|| {
            let out = write_many_streams(black_box(n), black_box(size));
            black_box(out);
        })
    });

    // single large stream with throughput reporting
    let mut group = c.benchmark_group("write large stream");
    let size = 256 * 1024 * 1024usize;
    let n = 1;
    group.sample_size(10);
    group.throughput(Throughput::Bytes(size as u64));
    group.bench_with_input(
        BenchmarkId::from_parameter("size"),
        &size,
        |b, &s| {
            b.iter(|| {
                let out = write_many_streams(black_box(n), black_box(s));
                black_box(out);
            })
        },
    );
    group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
