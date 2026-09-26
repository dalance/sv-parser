//! Special structural node wrappers for SystemVerilog syntax trees.
//!
//! Provides wrapper types for operators/punctuation ([`Symbol`]), keywords ([`Keyword`]),
//! non-semantic tokens ([`WhiteSpace`]), bracketed expressions ([`Paren`], [`Brace`],
//! [`Bracket`], [`ApostropheBrace`]), and delimited lists ([`List`]).

use crate::*;

// -----------------------------------------------------------------------------

/// Punctuation or operator symbol token together with trailing whitespace.
#[derive(Clone, Debug, PartialEq, Node)]
pub struct Symbol {
    /// Token location and trailing whitespace elements.
    pub nodes: (Locate, Vec<WhiteSpace>),
}

/// Language keyword token together with trailing whitespace.
#[derive(Clone, Debug, PartialEq, Node)]
pub struct Keyword {
    /// Token location and trailing whitespace elements.
    pub nodes: (Locate, Vec<WhiteSpace>),
}

/// Non-semantic token such as spaces, newlines, comments, or compiler directives.
#[derive(Clone, Debug, PartialEq, Node)]
pub enum WhiteSpace {
    /// Newline token span.
    Newline(Box<Locate>),
    /// Horizontal whitespace (spaces/tabs) span.
    Space(Box<Locate>),
    /// Source code comment.
    Comment(Box<Comment>),
    /// Preprocessor compiler directive.
    CompilerDirective(Box<CompilerDirective>),
}

/// Node enclosed within parentheses: `( T )`.
#[derive(Clone, Debug, PartialEq)]
pub struct Paren<T> {
    /// Tuple of `(opening_paren, inner_node, closing_paren)`.
    pub nodes: (Symbol, T, Symbol),
}

/// Node enclosed within curly braces: `{ T }`.
#[derive(Clone, Debug, PartialEq)]
pub struct Brace<T> {
    /// Tuple of `(opening_brace, inner_node, closing_brace)`.
    pub nodes: (Symbol, T, Symbol),
}

/// Node enclosed within square brackets: `[ T ]`.
#[derive(Clone, Debug, PartialEq)]
pub struct Bracket<T> {
    /// Tuple of `(opening_bracket, inner_node, closing_bracket)`.
    pub nodes: (Symbol, T, Symbol),
}

/// Node enclosed within apostrophe and curly braces: `'{ T }` (e.g., assignment patterns).
#[derive(Clone, Debug, PartialEq)]
pub struct ApostropheBrace<T> {
    /// Tuple of `(opening_apostrophe_brace, inner_node, closing_brace)`.
    pub nodes: (Symbol, T, Symbol),
}

/// Delimited list of items `U` separated by delimiter `T` (e.g. comma-separated lists `item1, item2, item3`).
#[derive(Clone, Debug, PartialEq)]
pub struct List<T, U> {
    /// Tuple of `(first_element, vec_of_(delimiter, subsequent_element))`.
    pub nodes: (U, Vec<(T, U)>),
}

impl<T, U> List<T, U> {
    /// Flattens the list into a `Vec` of references to every element `&U`.
    pub fn contents(&self) -> Vec<&U> {
        let mut ret = vec![];
        let (ref x, ref y) = self.nodes;
        ret.push(x);
        for (_, y) in y {
            ret.push(y)
        }
        ret
    }
}
