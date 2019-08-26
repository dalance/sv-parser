#![recursion_limit = "256"]

pub mod any_node;
pub mod behavioral_statements;
pub mod declarations;
pub mod expressions;
pub mod general;
pub mod instantiations;
pub mod preprocessor;
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
pub use preprocessor::*;
pub use primitive_instances::*;
pub use source_text::*;
pub use special_node::*;
pub use specify_section::*;
pub use udp_declaration_and_instantiation::*;

pub(crate) use sv_parser_macros::*;

// -----------------------------------------------------------------------------

#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct Locate {
    pub offset: usize,
    pub line: u32,
    pub len: usize,
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

impl<'a> IntoIterator for &'a Locate {
    type Item = RefNode<'a>;
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        let nodes: RefNodes = self.into();
        Iter { next: nodes }
    }
}
