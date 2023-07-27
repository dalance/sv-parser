use regex::Regex;
use std::env;
use std::fs::File;
use std::io::{BufRead, BufReader, Write};
use std::path::Path;
use walkdir::WalkDir;

static REF_NODE_HEADER: &str = r##"
#[derive(Clone, Debug, PartialEq, RefNode)]
pub enum RefNode<'a> {
    Locate(&'a Locate),
"##;

static REF_NODE_FOOTER: &str = r##"
}
"##;

static ANY_NODE_HEADER: &str = r##"
#[derive(Clone, Debug, PartialEq, AnyNode)]
pub enum AnyNode {
    Locate(Locate),
"##;

static ANY_NODE_FOOTER: &str = r##"
}
"##;

static REF_NODE_DISPLAY_HEADER: &str = r##"
impl<'a> std::fmt::Display for RefNode<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RefNode::Locate(_) => write!(f, "Locate"),
"##;

static REF_NODE_DISPLAY_FOOTER: &str = r##"
        }
    }
}
"##;

static ANY_NODE_DISPLAY_HEADER: &str = r##"
impl std::fmt::Display for AnyNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AnyNode::Locate(_) => write!(f, "Locate"),
"##;

static ANY_NODE_DISPLAY_FOOTER: &str = r##"
        }
    }
}
"##;

fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let dest = Path::new(&out_dir).join("any_node.rs");
    let mut out = File::create(&dest).unwrap();

    let mut ref_node = String::from(REF_NODE_HEADER);
    let mut any_node = String::from(ANY_NODE_HEADER);
    let mut ref_node_display = String::from(REF_NODE_DISPLAY_HEADER);
    let mut any_node_display = String::from(ANY_NODE_DISPLAY_HEADER);

    let re_node = Regex::new(r"#\[derive.*Node.*\]").unwrap();

    for entry in WalkDir::new("src") {
        let entry = entry.unwrap();
        if entry.path().is_file() {
            let f = File::open(entry.path()).unwrap();
            let f = BufReader::new(f);
            let mut hit_node = false;
            for line in f.lines() {
                let line = line.unwrap();
                if hit_node {
                    let name = line.split_whitespace().nth(2).unwrap().replace("<'a>", "");
                    ref_node = format!("{}    {}(&'a {}),\n", ref_node, name, name);
                    any_node = format!("{}    {}({}),\n", any_node, name, name);
                    ref_node_display = format!(
                        "{}            RefNode::{}(_) => write!(f, \"{}\"),\n",
                        ref_node_display, name, name
                    );
                    any_node_display = format!(
                        "{}            AnyNode::{}(_) => write!(f, \"{}\"),\n",
                        any_node_display, name, name
                    );
                    hit_node = false;
                }
                if re_node.is_match(&line) {
                    hit_node = true;
                }
            }
        }
    }

    ref_node = format!("{}{}\n", ref_node, REF_NODE_FOOTER);
    any_node = format!("{}{}\n", any_node, ANY_NODE_FOOTER);
    ref_node_display = format!("{}{}\n", ref_node_display, REF_NODE_DISPLAY_FOOTER);
    any_node_display = format!("{}{}\n", any_node_display, ANY_NODE_DISPLAY_FOOTER);
    let _ = write!(out, "{}", ref_node);
    let _ = write!(out, "{}", any_node);
    let _ = write!(out, "{}", ref_node_display);
    let _ = write!(out, "{}", any_node_display);
}
