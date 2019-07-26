#[macro_use]
pub mod utils;
pub(crate) use utils::*;

mod tests;

pub mod behavioral_statements;
pub mod declarations;
pub mod expressions;
pub mod general;
pub mod instantiations;
pub mod primitive_instances;
pub mod source_text;
pub mod specify_section;
pub mod udp_declaration_and_instantiation;
pub(crate) use behavioral_statements::*;
pub(crate) use declarations::*;
pub(crate) use expressions::*;
pub(crate) use general::*;
pub(crate) use instantiations::*;
pub(crate) use primitive_instances::*;
pub(crate) use source_text::*;
pub(crate) use specify_section::*;
pub(crate) use udp_declaration_and_instantiation::*;

pub(crate) use nom::branch::*;
pub(crate) use nom::bytes::complete::*;
pub(crate) use nom::character::complete::*;
pub(crate) use nom::combinator::*;
pub(crate) use nom::error::{make_error, ErrorKind};
pub(crate) use nom::multi::*;
pub(crate) use nom::sequence::*;
pub(crate) use nom::{Err, IResult};
pub(crate) use nom_packrat::{self, packrat_parser};
pub(crate) use sv_parser_macros::*;
pub(crate) use sv_parser_syntaxtree::*;

// -----------------------------------------------------------------------------

nom_packrat::storage!(AnyNode);

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

// -----------------------------------------------------------------------------

mod thread_context {

    use std::cell::RefCell;
    use std::collections::HashMap;
    use sv_parser_syntaxtree::RECURSIVE_FLAG_WORDS;

    pub struct ParserIndex {
        index: HashMap<&'static str, usize>,
        allocated: [u128; RECURSIVE_FLAG_WORDS],
    }

    impl ParserIndex {
        pub fn get(&mut self, key: &'static str) -> Option<usize> {
            if let Some(x) = self.index.get(key) {
                Some(*x)
            } else {
                for i in 0..128 * RECURSIVE_FLAG_WORDS {
                    let upper = i / 128;
                    let lower = i % 128;
                    if ((self.allocated[upper] >> lower) & 1) == 0 {
                        let val = 1u128 << lower;
                        let mask = !(1u128 << lower);
                        self.allocated[upper] = (self.allocated[upper] & mask) | val;
                        self.index.insert(key, i);
                        return Some(i);
                    }
                }
                None
            }
        }
    }

    thread_local!(
        pub static PARSER_INDEX: RefCell<ParserIndex> = {
            RefCell::new(ParserIndex{index: HashMap::new(), allocated: [0;RECURSIVE_FLAG_WORDS]})
        }
    );
}
