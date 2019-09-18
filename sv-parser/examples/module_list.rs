use std::collections::HashMap;
use std::convert::TryInto;
use std::env;
use std::path::PathBuf;
use sv_parser::{parse_sv, Locate, RefNode};

fn main() {
    let args: Vec<String> = env::args().collect();

    // The path of SystemVerilog source file
    let path = PathBuf::from(&args[1]);
    // The list of defined macros
    let defines = HashMap::new();
    // The list of include paths
    let includes: Vec<PathBuf> = Vec::new();

    // Do parse
    let result = parse_sv(&path, &defines, &includes);

    if let Ok((syntax_tree, _)) = result {
        // SyntexTree is iterable
        for node in &syntax_tree {
            // The type of Each node is RefNode
            match node {
                RefNode::ModuleDeclarationNonansi(x) => {
                    // The type of header is ModuleNonansiHeader
                    let (ref header, _, _, _, _) = x.nodes;
                    // The type of name is ModuleIdentifier
                    let (_, _, _, ref name, _, _, _, _) = header.nodes;

                    // Any type included in SyntaxTree can be convert RefNode by into()
                    let id = get_identifier(name.into()).unwrap();

                    // Original string can be got by SyntexTree::get_str(self, locate: &Locate)
                    let id = syntax_tree.get_str(&id);
                    println!("module: {}", id);
                }
                RefNode::ModuleDeclarationAnsi(x) => {
                    let (ref header, _, _, _, _) = x.nodes;
                    let (_, _, _, ref name, _, _, _, _) = header.nodes;
                    let id = get_identifier(name.into()).unwrap();
                    let id = syntax_tree.get_str(&id);
                    println!("module: {}", id);
                }
                _ => (),
            }
        }
    } else {
        println!("Parse failed");
    }
}

fn get_identifier(node: RefNode) -> Option<Locate> {
    for n in node {
        match n {
            RefNode::SimpleIdentifier(x) => {
                let x: Locate = x.nodes.0.try_into().unwrap();
                return Some(x);
            }
            RefNode::EscapedIdentifier(x) => {
                let x: Locate = x.nodes.0.try_into().unwrap();
                return Some(x);
            }
            _ => (),
        }
    }
    None
}
