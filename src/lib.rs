#![recursion_limit = "256"]
pub mod ast;
pub mod parser;

use nom_packrat::storage;

storage!(ast::AnyNode);
