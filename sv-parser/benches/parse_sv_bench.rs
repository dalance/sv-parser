#![feature(test)]

extern crate test;

use std::collections::HashMap;
use std::env;
use std::path::PathBuf;
use sv_parser::parse_sv;
use test::Bencher;

fn get_path(s: &str) -> PathBuf {
    PathBuf::from(format!(
        "{}/testcases/{}",
        env::var("CARGO_MANIFEST_DIR").unwrap(),
        s
    ))
}

#[bench]
fn test1(b: &mut Bencher) {
    let defines = HashMap::new();
    let includes: Vec<PathBuf> = Vec::new();
    let path = get_path("test1.sv");
    b.iter(|| {
        let _ = parse_sv(&path, &defines, &includes, false);
    });
}

#[bench]
fn test2(b: &mut Bencher) {
    let defines = HashMap::new();
    let includes: Vec<PathBuf> = Vec::new();
    let path = get_path("test2.sv");
    b.iter(|| {
        let _ = parse_sv(&path, &defines, &includes, false);
    });
}
