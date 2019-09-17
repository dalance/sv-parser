use std::collections::HashMap;
use std::path::PathBuf;
use structopt::StructOpt;
use sv_parser::parse_sv;

#[derive(StructOpt)]
struct Opt {
    pub files: Vec<PathBuf>,

    #[structopt(short = "I", long = "include", multiple = true, number_of_values = 1)]
    pub includes: Vec<PathBuf>,

    /// Show syntax tree
    #[structopt(short = "t", long = "tree")]
    pub tree: bool,
}

fn main() {
    let opt = Opt::from_args();
    for path in &opt.files {
        let syntax_tree = parse_sv(&path, &HashMap::new(), &opt.includes);

        match syntax_tree {
            Ok(x) => {
                if opt.tree {
                    println!("{}", x);
                }
                println!("parse succeeded: {:?}", path);
            }
            Err(x) => {
                println!("parse failed: {:?} ({})", path, x);
            }
        }
    }
}
