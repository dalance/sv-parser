# Architecture & Codebase Guide for `sv-parser`

`sv-parser` is a high-performance, fully compliant SystemVerilog parser library for Rust implementing the [IEEE 1800-2017](https://standards.ieee.org/standard/1800-2017.html) standard.

This guide provides an end-to-end architectural overview to help you navigate and understand the codebase when reading or modifying the code.

---

## 1. Crate Architecture & Workspace Organization

The repository is organized into a Cargo workspace consisting of 6 specialized crates:

```text
sv-parser (root facade)
├── sv-parser-pp (preprocessor)
│   ├── sv-parser-error (shared error definitions)
│   ├── sv-parser-parser (compiler directive parser)
│   └── sv-parser-syntaxtree (preprocessor AST nodes)
├── sv-parser-parser (grammar parser)
│   ├── sv-parser-syntaxtree (CST node types)
│   └── sv-parser-macros (derive macros)
├── sv-parser-syntaxtree (concrete syntax tree definitions)
│   └── sv-parser-macros (Node, RefNode, AnyNode derives)
├── sv-parser-macros (procedural macro crate)
└── sv-parser-error (thiserror-based error types)
```

| Crate | Purpose | Key Files |
| :--- | :--- | :--- |
| [`sv-parser`](file:///home/gevurah/compilers/sv-parser/sv-parser) | Main user-facing facade crate. Provides convenient entry points (`parse_sv`, `parse_sv_str`), `SyntaxTree` abstraction, string extraction, and helper macros. | [`src/lib.rs`](file:///home/gevurah/compilers/sv-parser/sv-parser/src/lib.rs) |
| [`sv-parser-pp`](file:///home/gevurah/compilers/sv-parser/sv-parser-pp) | SystemVerilog preprocessor. Handles `` `define ``, `` `include ``, `` `ifdef ``/`` `else ``, macro substitution, and tracks source text origins back to original files. | [`src/preprocess.rs`](file:///home/gevurah/compilers/sv-parser/sv-parser-pp/src/preprocess.rs), [`src/range.rs`](file:///home/gevurah/compilers/sv-parser/sv-parser-pp/src/range.rs) |
| [`sv-parser-parser`](file:///home/gevurah/compilers/sv-parser/sv-parser-parser) | Nom-based recursive descent parser. Implements IEEE 1800-2017 Annex A formal grammar rules with packrat memoization and recursion support. | [`src/lib.rs`](file:///home/gevurah/compilers/sv-parser/sv-parser-parser/src/lib.rs), [`src/utils.rs`](file:///home/gevurah/compilers/sv-parser/sv-parser-parser/src/utils.rs), [`src/keywords.rs`](file:///home/gevurah/compilers/sv-parser/sv-parser-parser/src/keywords.rs) |
| [`sv-parser-syntaxtree`](file:///home/gevurah/compilers/sv-parser/sv-parser-syntaxtree) | Concrete Syntax Tree (CST) definitions for every production rule in IEEE 1800-2017. Also provides `Locate`, `RefNode`, `AnyNode`, and depth-first tree iterators. | [`src/lib.rs`](file:///home/gevurah/compilers/sv-parser/sv-parser-syntaxtree/src/lib.rs), [`src/any_node.rs`](file:///home/gevurah/compilers/sv-parser/sv-parser-syntaxtree/src/any_node.rs), [`src/special_node.rs`](file:///home/gevurah/compilers/sv-parser/sv-parser-syntaxtree/src/special_node.rs) |
| [`sv-parser-error`](file:///home/gevurah/compilers/sv-parser/sv-parser-error) | Error definitions implementing `thiserror::Error`. Captures IO errors, UTF-8 decoding issues, syntax errors, and preprocessor limits. | [`src/lib.rs`](file:///home/gevurah/compilers/sv-parser/sv-parser-error/src/lib.rs) |
| [`sv-parser-macros`](file:///home/gevurah/compilers/sv-parser/sv-parser-macros) | Procedural derive macros: `#[derive(Node)]`, `#[derive(AnyNode)]`, and `#[derive(RefNode)]`. Generates tree navigation, iteration, and conversions. | [`src/lib.rs`](file:///home/gevurah/compilers/sv-parser/sv-parser-macros/src/lib.rs) |

---

## 2. Compilation & Parsing Pipeline

The pipeline transforms raw SystemVerilog source code into an navigable Concrete Syntax Tree:

```text
┌────────────────────────┐
│  Source File(s) on Disk │
└───────────┬────────────┘
            │
            ▼
┌────────────────────────────────────────────────────────┐
│ 1. sv-parser-pp (Preprocessor)                         │
│    - Resolves `include search paths                    │
│    - Evaluates `ifdef / `ifndef / `elsif / `endif      │
│    - Expands `define macros with arguments & defaults  │
│    - Strips comments (optional)                        │
│    - Maps character offsets -> (PathBuf, ByteOffset)   │
└───────────┬────────────────────────────────────────────┘
            │ PreprocessedText & Defines
            ▼
┌────────────────────────────────────────────────────────┐
│ 2. sv-parser-parser (Parser)                           │
│    - Wraps text in LocatedSpan (SpanInfo)              │
│    - Evaluates keyword versions (`begin_keywords)      │
│    - Parses grammar via Nom + Packrat memoization      │
│    - Resolves left-recursive productions               │
└───────────┬────────────────────────────────────────────┘
            │ SourceText / LibraryText
            ▼
┌────────────────────────────────────────────────────────┐
│ 3. sv-parser::SyntaxTree (Concrete Syntax Tree)        │
│    - Stores AnyNode root + PreprocessedText            │
│    - Iteration via &SyntaxTree -> RefNode              │
│    - Token slices via get_str / get_str_trim           │
│    - Source mapping via get_origin                     │
└────────────────────────────────────────────────────────┘
```

---

## 3. Deep Dive into Subsystems

### 3.1 Preprocessing & Origin Tracking (`sv-parser-pp`)

Preprocessing alters the source string: macros expand into longer or shorter strings, included files are injected in-place, and conditional branches are skipped.

To preserve the ability to report accurate file and line diagnostics, `sv-parser-pp` maintains an origin lookup table:
- **[`PreprocessedText`](file:///home/gevurah/compilers/sv-parser/sv-parser-pp/src/preprocess.rs)**: Stores the concatenated output string alongside a `BTreeMap<Range, Origin>`.
- **Interval Query Trick in [`Range`](file:///home/gevurah/compilers/sv-parser/sv-parser-pp/src/range.rs)**: `Range` represents `[begin, end)` with custom `PartialEq` and `Ord` implementations that consider two ranges equal if they overlap. Querying `origins.get(&Range::new(pos, pos + 1))` looks up which original file and byte range produced character `pos` in $O(\log N)$ time.
- **Recursion Guard**: Guarantees prevention of infinite macro loops or cyclic includes via `RECURSIVE_LIMIT` (default: 64).

### 3.2 Concrete Syntax Tree (`sv-parser-syntaxtree`)

Unlike an Abstract Syntax Tree (AST), which typically discards whitespace, comments, and keywords:
- **Full Fidelity (CST)**: Every token, semicolon, parenthesis, comment, and keyword is stored as typed structs.
- **Terminal Tokens as [`Locate`](file:///home/gevurah/compilers/sv-parser/sv-parser-syntaxtree/src/lib.rs)**: Each terminal token records its preprocessed byte offset (`offset`), 1-indexed source line (`line`), and byte length (`len`).
- **[`RefNode`](file:///home/gevurah/compilers/sv-parser/sv-parser-syntaxtree/src/any_node.rs)**: A massive borrowed enum containing reference variants for all grammar productions (e.g. `RefNode::ModuleDeclarationAnsi(&ModuleDeclarationAnsi)`). Traversal borrows nodes without memory allocation.
- **Traversals**:
  - `Iter`: Simple pre-order iterator yielding `RefNode<'a>`.
  - `EventIter`: Yields `NodeEvent::Enter(RefNode)` when descending into a node and `NodeEvent::Leave(RefNode)` when ascending. This allows maintaining scoping contexts (e.g., current module or function).

### 3.3 Parser Combinators & Performance (`sv-parser-parser`)

The parser is implemented using [`nom`](https://crates.io/crates/nom) with several key techniques:
- **Packrat Memoization (`nom-packrat`)**: SystemVerilog has extensive grammar ambiguities where naive backtracking would cause exponential slowdowns. `nom-packrat` memoizes intermediate parse results at each token position.
- **Left Recursion (`nom-recursive`)**: Allows direct specification of left-recursive grammar productions (such as expression operators).
- **Keyword Sets & Versions**: SystemVerilog versions (1364-1995 through 1800-2017) can be changed dynamically in source code via `` `begin_keywords "1364-2001" ``. The parser tracks active keyword sets via thread-local state in [`utils.rs`](file:///home/gevurah/compilers/sv-parser/sv-parser-parser/src/utils.rs).
- **Whitespace / Directive Separation**: In standard SystemVerilog code, whitespace, comments, and non-reset compiler directives can appear between almost any two tokens. Combinators like `ws()` automatically consume trailing whitespace into `Vec<WhiteSpace>` attached to tokens.

### 3.4 Procedural Macros (`sv-parser-macros`)

Because the SystemVerilog grammar defines hundreds of distinct structs and enums, boilerplate is generated via derive macros:
- `#[derive(Node)]`: Implements `Node::next(&self)` by inspecting struct fields or enum variants, implements `IntoIterator`, and implements conversions to `RefNode` and `AnyNode`.
- `#[derive(AnyNode)]`: Implements dynamic downcasting `TryFrom<AnyNode>` for each concrete node type.
- `#[derive(RefNode)]`: Implements unified dispatch for `next()` and iteration across all variants.

---

## 4. Code Reading Guide

When reading specific parts of the parser, use this quick navigation table:

| If you are investigating... | Look at these files |
| :--- | :--- |
| Entry point & parsing high-level API | [`sv-parser/src/lib.rs`](file:///home/gevurah/compilers/sv-parser/sv-parser/src/lib.rs) |
| Macro definition & expansion | [`sv-parser-pp/src/preprocess.rs`](file:///home/gevurah/compilers/sv-parser/sv-parser-pp/src/preprocess.rs) |
| Source file origin tracking | [`sv-parser-pp/src/range.rs`](file:///home/gevurah/compilers/sv-parser/sv-parser-pp/src/range.rs) and [`preprocess.rs`](file:///home/gevurah/compilers/sv-parser/sv-parser-pp/src/preprocess.rs) |
| Module declarations & items | [`sv-parser-syntaxtree/src/source_text/`](file:///home/gevurah/compilers/sv-parser/sv-parser-syntaxtree/src/source_text/) and [`sv-parser-parser/src/source_text/`](file:///home/gevurah/compilers/sv-parser/sv-parser-parser/src/source_text/) |
| Behavioral statements (always, initial, if, case, loops) | [`sv-parser-syntaxtree/src/behavioral_statements/`](file:///home/gevurah/compilers/sv-parser/sv-parser-syntaxtree/src/behavioral_statements/) and [`sv-parser-parser/src/behavioral_statements/`](file:///home/gevurah/compilers/sv-parser/sv-parser-parser/src/behavioral_statements/) |
| Expressions & operators | [`sv-parser-syntaxtree/src/expressions/`](file:///home/gevurah/compilers/sv-parser/sv-parser-syntaxtree/src/expressions/) and [`sv-parser-parser/src/expressions/`](file:///home/gevurah/compilers/sv-parser/sv-parser-parser/src/expressions/) |
| Type & variable declarations | [`sv-parser-syntaxtree/src/declarations/`](file:///home/gevurah/compilers/sv-parser/sv-parser-syntaxtree/src/declarations/) and [`sv-parser-parser/src/declarations/`](file:///home/gevurah/compilers/sv-parser/sv-parser-parser/src/declarations/) |
| Keywords and version switching | [`sv-parser-parser/src/keywords.rs`](file:///home/gevurah/compilers/sv-parser/sv-parser-parser/src/keywords.rs) and [`sv-parser-parser/src/utils.rs`](file:///home/gevurah/compilers/sv-parser/sv-parser-parser/src/utils.rs) |
| Error variants and diagnostics | [`sv-parser-error/src/lib.rs`](file:///home/gevurah/compilers/sv-parser/sv-parser-error/src/lib.rs) |

---

## 5. Usage Recipes

### 5.1 Finding all Module Declarations

```rust
use std::collections::HashMap;
use std::path::PathBuf;
use sv_parser::{parse_sv, unwrap_node, Locate, RefNode};

fn main() {
    let path = PathBuf::from("my_design.sv");
    let defines = HashMap::new();
    let includes: Vec<PathBuf> = vec![];

    let (syntax_tree, _) = parse_sv(&path, &defines, &includes, false, false).unwrap();

    for node in &syntax_tree {
        match node {
            RefNode::ModuleDeclarationAnsi(decl) => {
                if let Some(id_node) = unwrap_node!(decl, ModuleIdentifier) {
                    let name = syntax_tree.get_str(&id_node).unwrap();
                    println!("Found ANSI module: {}", name);
                }
            }
            RefNode::ModuleDeclarationNonansi(decl) => {
                if let Some(id_node) = unwrap_node!(decl, ModuleIdentifier) {
                    let name = syntax_tree.get_str(&id_node).unwrap();
                    println!("Found non-ANSI module: {}", name);
                }
            }
            _ => (),
        }
    }
}
```

### 5.2 Tracking Hierarchical Scopes with `EventIter`

```rust
use sv_parser::{NodeEvent, RefNode, SyntaxTree};

fn analyze_scopes(syntax_tree: &SyntaxTree) {
    let mut current_module: Option<String> = None;

    for event in syntax_tree.into_iter().event() {
        match event {
            NodeEvent::Enter(RefNode::ModuleDeclarationAnsi(m)) => {
                let name = syntax_tree.get_str(m).unwrap_or("unknown");
                current_module = Some(name.to_string());
                println!("Entering module: {}", name);
            }
            NodeEvent::Leave(RefNode::ModuleDeclarationAnsi(_)) => {
                println!("Leaving module: {:?}", current_module);
                current_module = None;
            }
            _ => ()
        }
    }
}
```

### 5.3 Mapping Nodes Back to Source Files & Line Numbers

```rust
use sv_parser::{unwrap_locate, RefNode, SyntaxTree};

fn print_node_origin(syntax_tree: &SyntaxTree, node: RefNode) {
    if let Some(locate) = unwrap_locate!(node) {
        if let Some((origin_file, byte_offset)) = syntax_tree.get_origin(&locate) {
            println!(
                "Node at line {} originates from {:?} at byte offset {}",
                locate.line, origin_file, byte_offset
            );
        }
    }
}
```
