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

    let mut ref_node = String::new();
    ref_node = format!("{}#[derive(Debug, Clone, RefNode)]\n", ref_node);
    ref_node = format!("{}pub enum RefNode<'a> {{\n", ref_node);
    ref_node = format!("{}    Locate(&'a Locate),\n", ref_node);

    let mut any_node = String::new();
    any_node = format!("{}#[derive(Debug, Clone, AnyNode)]\n", any_node);
    any_node = format!("{}pub enum AnyNode {{\n", any_node);
    any_node = format!("{}    Locate(Locate),\n", any_node);

    let re_node = Regex::new(r"#\[derive.*Node.*\]").unwrap();

    for entry in WalkDir::new("src") {
        let entry = entry.unwrap();
        if entry.file_type().is_file() {
            let f = File::open(entry.path()).unwrap();
            let f = BufReader::new(f);
            let mut hit_node = false;
            for line in f.lines() {
                let line = line.unwrap();
                if hit_node {
                    let name = line.split_whitespace().nth(2).unwrap().replace("<'a>", "");
                    ref_node = format!("{}    {}(&'a {}),\n", ref_node, name, name);
                    any_node = format!("{}    {}({}),\n", any_node, name, name);
                    hit_node = false;
                }
                if re_node.is_match(&line) {
                    hit_node = true;
                }
            }
        }
    }

    ref_node = format!("{}}}\n", ref_node);
    any_node = format!("{}}}\n", any_node);
    let _ = write!(out, "{}", ref_node);
    let _ = write!(out, "{}", any_node);
}
