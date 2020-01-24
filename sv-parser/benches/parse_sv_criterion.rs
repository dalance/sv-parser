use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::time::Duration;
use std::{env, fs};
use sv_parser::parse_sv;

fn get_path(s: &str) -> PathBuf {
    PathBuf::from(format!(
        "{}/testcases/{}",
        env::var("CARGO_MANIFEST_DIR").unwrap(),
        s
    ))
}

fn get_size(p: &Path) -> u64 {
    let metadata = fs::metadata(p).unwrap();
    metadata.len()
}

fn gen_benchmark_group(c: &mut Criterion, s: &str) {
    let defines = HashMap::new();
    let includes: Vec<PathBuf> = Vec::new();
    let path = get_path(s);
    let size = get_size(&path);
    let mut group = c.benchmark_group(s);
    group.throughput(Throughput::Bytes(size));
    group.bench_function(s, |b| {
        b.iter_with_large_drop(|| parse_sv(&path, &defines, &includes, false))
    });
    group.finish();
}

fn config() -> Criterion {
    Criterion::default()
        .sample_size(30)
        .measurement_time(Duration::new(30, 0))
    //Criterion::default().measurement_time(Duration::new(90, 0))
}

fn criterion_benchmark(c: &mut Criterion) {
    gen_benchmark_group(c, "test1.sv");
    gen_benchmark_group(c, "test2.sv");
}

criterion_group! {
    name = benches;
    config = config();
    targets = criterion_benchmark
}

criterion_main!(benches);
