use std::env;
use std::fs::File;
use std::io::Read;
use sv_parser::{parse_sv, RefNode};

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut f = File::open(&args[1]).unwrap();
    let mut buf = String::new();
    let _ = f.read_to_string(&mut buf);

    let syntax_tree = parse_sv(&buf);

    if let Ok(syntax_tree) = syntax_tree {
        //for node in &syntax_tree {
        //    match node {
        //        RefNode::Locate(x) => {
        //            dbg!(syntax_tree.get_str(x));
        //        }
        //        _ => (),
        //    }
        //}
        println!("parse succeeded");
    } else {
        println!("parse failed");
    }
}
