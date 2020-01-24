use std::collections::HashMap;
use std::error::Error as StdError;
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;
use std::{cmp, process};
use structopt::StructOpt;
use sv_parser::parse_sv;
use sv_parser_error::Error;
use sv_parser_pp::preprocess::preprocess;

#[derive(StructOpt)]
struct Opt {
    pub files: Vec<PathBuf>,

    /// Include path
    #[structopt(short = "i", long = "include", multiple = true, number_of_values = 1)]
    pub includes: Vec<PathBuf>,

    /// Show syntax tree
    #[structopt(short = "t", long = "tree")]
    pub tree: bool,

    /// Show preprocesed text
    #[structopt(short = "p", long = "pp")]
    pub pp: bool,

    /// Quiet
    #[structopt(short = "q", long = "quiet")]
    pub quiet: bool,
}

fn main() {
    let opt = Opt::from_args();
    let mut defines = HashMap::new();
    let mut exit = 0;
    for path in &opt.files {
        if opt.pp {
            match preprocess(&path, &defines, &opt.includes, false) {
                Ok((preprocessed_text, new_defines)) => {
                    println!("{}", preprocessed_text.text());
                    defines = new_defines;
                }
                _ => (),
            }
        } else {
            match parse_sv(&path, &defines, &opt.includes, false) {
                Ok((syntax_tree, new_defines)) => {
                    if opt.tree {
                        println!("{}", syntax_tree);
                    }
                    defines = new_defines;
                    if !opt.quiet {
                        println!("parse succeeded: {:?}", path);
                    }
                }
                Err(x) => {
                    match x {
                        Error::Parse(Some((origin_path, origin_pos))) => {
                            println!("parse failed: {:?}", path);
                            print_parse_error(&origin_path, &origin_pos);
                        }
                        x => {
                            println!("parse failed: {:?} ({})", path, x);
                            let mut err = x.source();
                            while let Some(x) = err {
                                println!("  Caused by {}", x);
                                err = x.source();
                            }
                        }
                    }
                    exit = 1;
                }
            }
        }
    }
    process::exit(exit);
}

static CHAR_CR: u8 = 0x0d;
static CHAR_LF: u8 = 0x0a;

fn print_parse_error(origin_path: &PathBuf, origin_pos: &usize) {
    let mut f = File::open(&origin_path).unwrap();
    let mut s = String::new();
    let _ = f.read_to_string(&mut s);

    let mut pos = 0;
    let mut column = 1;
    let mut last_lf = None;
    while pos < s.len() {
        if s.as_bytes()[pos] == CHAR_LF {
            column += 1;
            last_lf = Some(pos);
        }
        pos += 1;

        if *origin_pos == pos {
            let row = if let Some(last_lf) = last_lf {
                pos - last_lf
            } else {
                pos + 1
            };
            let mut next_crlf = pos;
            while next_crlf < s.len() {
                if s.as_bytes()[next_crlf] == CHAR_CR || s.as_bytes()[next_crlf] == CHAR_LF {
                    break;
                }
                next_crlf += 1;
            }

            let column_len = format!("{}", column).len();

            print!(" {}:{}:{}\n", origin_path.to_string_lossy(), column, row);

            print!("{}|\n", " ".repeat(column_len + 1));

            print!("{} |", column);

            let beg = if let Some(last_lf) = last_lf {
                last_lf + 1
            } else {
                0
            };
            print!(
                " {}\n",
                String::from_utf8_lossy(&s.as_bytes()[beg..next_crlf])
            );

            print!("{}|", " ".repeat(column_len + 1));

            print!(
                " {}{}\n",
                " ".repeat(pos - beg),
                "^".repeat(cmp::min(origin_pos + 1, next_crlf) - origin_pos)
            );
        }
    }
}
