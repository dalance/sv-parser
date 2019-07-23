use regex::Regex;
use std::env;
use std::fs::File;
use std::io::{BufRead, BufReader, Write};
use std::path::Path;
use walkdir::WalkDir;

fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let dest = Path::new(&out_dir).join("any_node.rs");
    let mut out = File::create(&dest).unwrap();

    let _ = write!(out, "#[derive(Debug, Clone, AnyNode)]\n");
    let _ = write!(out, "pub enum AnyNode<'a> {{\n");
    let _ = write!(out, "    Locate(&'a Locate),\n");

    let re_node = Regex::new(r"#\[derive.*Node.*\]").unwrap();

    for entry in WalkDir::new("src/parser") {
        let entry = entry.unwrap();
        if entry.file_type().is_file() {
            let f = File::open(entry.path()).unwrap();
            let f = BufReader::new(f);
            let mut hit_node = false;
            for line in f.lines() {
                let line = line.unwrap();
                if hit_node {
                    let name = line.split_whitespace().nth(2).unwrap().replace("<'a>", "");
                    let _ = write!(out, "    {}(&'a {}),\n", name, name);
                    hit_node = false;
                }
                if re_node.is_match(&line) {
                    hit_node = true;
                }
            }
        }
    }

    let _ = write!(out, "}}\n");
}
