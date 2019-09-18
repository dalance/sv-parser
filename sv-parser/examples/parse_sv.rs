use std::collections::HashMap;
use std::path::PathBuf;
use structopt::StructOpt;
use sv_parser::parse_sv;

#[derive(StructOpt)]
struct Opt {
    pub files: Vec<PathBuf>,

    /// Include path
    #[structopt(short = "i", long = "include", multiple = true, number_of_values = 1)]
    pub includes: Vec<PathBuf>,

    /// Show syntax tree
    #[structopt(short = "t", long = "tree")]
    pub tree: bool,

    /// Quiet
    #[structopt(short = "q", long = "quiet")]
    pub quiet: bool,
}

fn main() {
    let opt = Opt::from_args();
    let mut defines = HashMap::new();
    for path in &opt.files {
        match parse_sv(&path, &defines, &opt.includes) {
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
                println!("parse failed: {:?} ({})", path, x);
            }
        }
    }
}
