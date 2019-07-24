#![recursion_limit = "256"]
pub mod ast;
pub mod parser;
use ast::*;
use parser::*;

use nom_packrat::storage;

storage!(ast::AnyNode);

pub fn parse_sv(s: &str) -> Result<SourceText, ()> {
    let s = Span::new_extra(s, Extra::default());
    match source_text(s) {
        Ok((_, x)) => Ok(x),
        Err(_) => Err(()),
    }
}

pub fn parse_lib(s: &str) -> Result<LibraryText, ()> {
    let s = Span::new_extra(s, Extra::default());
    match library_text(s) {
        Ok((_, x)) => Ok(x),
        Err(_) => Err(()),
    }
}
