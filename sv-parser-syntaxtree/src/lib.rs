#![recursion_limit = "256"]

pub mod any_node;
pub mod behavioral_statements;
pub mod declarations;
pub mod expressions;
pub mod general;
pub mod instantiations;
pub mod primitive_instances;
pub mod source_text;
pub mod special_node;
pub mod specify_section;
pub mod udp_declaration_and_instantiation;
pub use any_node::*;
pub use behavioral_statements::*;
pub use declarations::*;
pub use expressions::*;
pub use general::*;
pub use instantiations::*;
pub use primitive_instances::*;
pub use source_text::*;
pub use special_node::*;
pub use specify_section::*;
pub use udp_declaration_and_instantiation::*;

pub(crate) use sv_parser_macros::*;

// -----------------------------------------------------------------------------

pub const RECURSIVE_FLAG_WORDS: usize = 1;

#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct Extra {
    #[cfg(feature = "trace")]
    pub depth: usize,
    pub recursive_flag: [u128; RECURSIVE_FLAG_WORDS],
}

pub type Span<'a> = nom_locate::LocatedSpanEx<&'a str, Extra>;

// -----------------------------------------------------------------------------

#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct Locate {
    offset: usize,
    line: u32,
    len: usize,
}

impl<'a> From<Span<'a>> for Locate {
    fn from(x: Span<'a>) -> Self {
        Locate {
            offset: x.offset,
            line: x.line,
            len: x.fragment.len(),
        }
    }
}

// -----------------------------------------------------------------------------

pub trait Node<'a> {
    fn next(&'a self) -> RefNodes<'a>;
}

impl<'a> Node<'a> for Locate {
    fn next(&'a self) -> RefNodes<'a> {
        vec![].into()
    }
}
