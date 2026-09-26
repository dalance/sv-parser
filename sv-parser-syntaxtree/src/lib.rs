//! Concrete Syntax Tree (CST) definitions for SystemVerilog compliant with IEEE 1800-2017.
//!
//! Unlike an Abstract Syntax Tree (AST), this crate models a **Concrete Syntax Tree (CST)**
//! corresponding directly to the formal grammar specifications in **IEEE 1800-2017 Annex A**.
//! All syntax tokens, keywords, symbols, whitespace, comments, and compiler directives
//! are preserved in the tree hierarchy. This makes it ideal for lossless reconstruction,
//! linters, formatters, and language servers.
//!
//! # Core Concepts
//!
//! - [`Locate`]: Terminal token position recording byte offset, line number, and length.
//! - [`Node`]: Trait implemented by every CST node providing access to child nodes via `next()`.
//! - [`RefNode`]: Unified borrowed enum over any CST node variant, enabling zero-copy tree walking.
//! - [`AnyNode`]: Unified owned enum over any CST node variant.
//! - [`Iter`]: Iterator performing pre-order depth-first traversal over any syntax node.
//! - [`EventIter`]: Event iterator producing [`NodeEvent::Enter`] and [`NodeEvent::Leave`] events.

#![recursion_limit = "256"]
#![allow(
    clippy::module_inception,
    clippy::large_enum_variant,
    clippy::type_complexity
)]

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

/// Position and span of a terminal token in the preprocessed source text.
///
/// Every leaf node in the concrete syntax tree contains or is a `Locate`.
/// `Locate` records the byte offset, 1-indexed line number, and byte length of the token.
#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct Locate {
    /// Byte offset in the preprocessed text.
    pub offset: usize,
    /// 1-indexed line number in the source file.
    pub line: u32,
    /// Byte length of the token.
    pub len: usize,
}

impl Locate {
    /// Extracts the token string slice corresponding to this `Locate` from the given source string.
    pub fn str<'a, 'b>(&'a self, s: &'b str) -> &'b str {
        &s[self.offset..self.offset + self.len]
    }
}

// -----------------------------------------------------------------------------

/// Trait implemented by all CST nodes for hierarchical traversal.
///
/// Enables navigating down into child nodes via [`Node::next`].
pub trait Node<'a> {
    /// Returns the immediate child nodes of this node wrapped in [`RefNodes`].
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
