# sv-parser
SystemVerilog parser library fully compliant with [IEEE 1800-2017](https://standards.ieee.org/standard/1800-2017.html).

[![Actions Status](https://github.com/dalance/sv-parser/workflows/Rust/badge.svg)](https://github.com/dalance/sv-parser/actions)
[![Crates.io](https://img.shields.io/crates/v/sv-parser.svg)](https://crates.io/crates/sv-parser)
[![Docs.rs](https://docs.rs/sv-parser/badge.svg)](https://docs.rs/sv-parser)

## Tools using sv-parser

* [morty](https://github.com/zarubaf/morty): A SystemVerilog source file pickler
* [svinst](https://github.com/sgherbst/svinst): Determines the modules declared and instantiated in a SystemVerilog file
* [svlint](https://github.com/dalance/svlint): SystemVerilog linter
* [svls](https://github.com/dalance/svls): SystemVerilog language server

## Usage

```Cargo.toml
[dependencies]
sv-parser = "0.8.1"
```

sv-parser provides [`parse_sv`](https://docs.rs/sv-parser/latest/sv_parser/fn.parse_sv.html) function which returns [`SyntaxTree`](https://docs.rs/sv-parser/latest/sv_parser/struct.SyntaxTree.html).
`SyntaxTree` shows Concrete Syntax Tree. It has the preprocessed string and the parsed tree.

[`RefNode`](https://docs.rs/sv-parser/latest/sv_parser/any_node/enum.RefNode.html) shows a reference to any node of `SyntaxTree`.
You can get `RefNode` through an iterator of `SyntaxTree`.
Variant names of `RefNode` follows "Annex A Formal syntax" of IEEE 1800-2017.

[`Locate`](https://docs.rs/sv-parser/latest/sv_parser/struct.Locate.html) shows a position of token. All leaf node of `SyntaxTree` is `Locate`.
You can get string from `Locate` by [`get_str`](https://docs.rs/sv-parser/latest/sv_parser/struct.SyntaxTree.html#method.get_str).

## Example

The following example parses a SystemVerilog source file and shows module names.

```rust
use std::collections::HashMap;
use std::env;
use std::path::PathBuf;
use sv_parser::{parse_sv, unwrap_node, Locate, RefNode};

fn main() {
    let args: Vec<String> = env::args().collect();

    // The path of SystemVerilog source file
    let path = PathBuf::from(&args[1]);
    // The list of defined macros
    let defines = HashMap::new();
    // The list of include paths
    let includes: Vec<PathBuf> = Vec::new();

    // Parse
    let result = parse_sv(&path, &defines, &includes, false);

    if let Ok((syntax_tree, _)) = result {
        // &SyntaxTree is iterable
        for node in &syntax_tree {
            // The type of each node is RefNode
            match node {
                RefNode::ModuleDeclarationNonansi(x) => {
                    // unwrap_node! gets the nearest ModuleIdentifier from x
                    let id = unwrap_node!(x, ModuleIdentifier).unwrap();

                    let id = get_identifier(id).unwrap();

                    // Original string can be got by SyntaxTree::get_str(self, locate: &Locate)
                    let id = syntax_tree.get_str(&id).unwrap();
                    println!("module: {}", id);
                }
                RefNode::ModuleDeclarationAnsi(x) => {
                    let id = unwrap_node!(x, ModuleIdentifier).unwrap();
                    let id = get_identifier(id).unwrap();
                    let id = syntax_tree.get_str(&id).unwrap();
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
    // unwrap_node! can take multiple types
    match unwrap_node!(node, SimpleIdentifier, EscapedIdentifier) {
        Some(RefNode::SimpleIdentifier(x)) => {
            return Some(x.nodes.0);
        }
        Some(RefNode::EscapedIdentifier(x)) => {
            return Some(x.nodes.0);
        }
        _ => None,
    }
}
```

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
