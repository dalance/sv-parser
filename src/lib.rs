#![recursion_limit = "128"]
pub mod ast;
pub mod parser;

use nom_packrat::storage;

storage!(ast::AnyNode);
