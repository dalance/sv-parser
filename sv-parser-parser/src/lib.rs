//! Recursive-descent parser for SystemVerilog compliant with IEEE 1800-2017.
//!
//! This crate parses preprocessed SystemVerilog source text into the Concrete Syntax Tree (CST)
//! defined by `sv-parser-syntaxtree`.
//!
//! # Architecture & Features
//!
//! - **Parser combinators**: Built using [`nom`] combinators, parsing grammar rules in a declarative style.
//! - **Packrat memoization**: Uses `nom-packrat` to memoize parser results across branching paths,
//!   avoiding exponential backtracking overhead.
//! - **Left recursion handling**: Uses `nom-recursive` to handle left-recursive grammar productions.
//! - **State tracking**: Tracks context-sensitive states, such as active IEEE keyword versions
//!   (via `` `begin_keywords ``) and directive scopes (via `SpanInfo`).

#![recursion_limit = "256"]
#![allow(clippy::many_single_char_names, clippy::module_inception)]

pub mod keywords;
#[macro_use]
pub mod utils;
pub(crate) use keywords::*;
pub(crate) use utils::*;

mod tests;

pub mod behavioral_statements;
pub mod declarations;
pub mod expressions;
pub mod general;
pub mod instantiations;
pub mod preprocessor;
pub mod primitive_instances;
pub mod source_text;
pub mod specify_section;
pub mod udp_declaration_and_instantiation;
pub(crate) use behavioral_statements::*;
pub(crate) use declarations::*;
pub(crate) use expressions::*;
pub(crate) use general::*;
pub(crate) use instantiations::*;
pub(crate) use preprocessor::*;
pub(crate) use primitive_instances::*;
pub(crate) use source_text::*;
pub(crate) use specify_section::*;
pub(crate) use udp_declaration_and_instantiation::*;

pub(crate) use nom::branch::*;
pub(crate) use nom::bytes::complete::*;
pub(crate) use nom::character::complete::*;
pub(crate) use nom::combinator::*;
pub(crate) use nom::error::{context, make_error, ErrorKind};
pub(crate) use nom::multi::*;
pub(crate) use nom::sequence::*;
pub(crate) use nom::Err;
pub(crate) use nom_greedyerror::GreedyError;
pub(crate) use nom_packrat::{self, packrat_parser, HasExtraState};
pub(crate) use nom_recursive::{recursive_parser, HasRecursiveInfo, RecursiveInfo};
pub(crate) use nom_tracable::tracable_parser;
#[cfg(feature = "trace")]
pub(crate) use nom_tracable::{HasTracableInfo, TracableInfo};
pub(crate) use sv_parser_syntaxtree::*;

// -----------------------------------------------------------------------------

/// Extra state stored alongside each parser span during parsing.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct SpanInfo {
    #[cfg(feature = "trace")]
    pub tracable_info: TracableInfo,
    /// State used by `nom-recursive` for tracking left-recursive parse calls.
    pub recursive_info: RecursiveInfo,
}

/// The span type used across all parser combinators in this crate.
pub type Span<'a> = nom_locate::LocatedSpan<&'a str, SpanInfo>;

/// Parser result type using `GreedyError` for syntax error collection.
pub type IResult<T, U> = nom::IResult<T, U, GreedyError<T, ErrorKind>>;

impl HasRecursiveInfo for SpanInfo {
    fn get_recursive_info(&self) -> RecursiveInfo {
        self.recursive_info
    }

    fn set_recursive_info(mut self, info: RecursiveInfo) -> Self {
        self.recursive_info = info;
        self
    }
}

#[cfg(feature = "trace")]
impl HasTracableInfo for SpanInfo {
    fn get_tracable_info(&self) -> TracableInfo {
        self.tracable_info
    }

    fn set_tracable_info(mut self, info: TracableInfo) -> Self {
        self.tracable_info = info;
        self
    }
}

impl HasExtraState<bool> for SpanInfo {
    fn get_extra_state(&self) -> bool {
        in_directive()
    }
}

// -----------------------------------------------------------------------------

nom_packrat::storage!(AnyNode, bool, 1024);

/// Parses complete SystemVerilog source text into a [`SourceText`] CST node.
pub fn sv_parser(s: Span) -> IResult<Span, SourceText> {
    init();
    source_text(s)
}

/// Parses SystemVerilog source text, allowing trailing unparsed input.
pub fn sv_parser_incomplete(s: Span) -> IResult<Span, SourceText> {
    init();
    source_text_incomplete(s)
}

/// Parses a SystemVerilog library source file into a [`LibraryText`] CST node.
pub fn lib_parser(s: Span) -> IResult<Span, LibraryText> {
    init();
    library_text(s)
}

/// Parses a SystemVerilog library source file, allowing trailing unparsed input.
pub fn lib_parser_incomplete(s: Span) -> IResult<Span, LibraryText> {
    init();
    library_text_incomplete(s)
}

/// Parses preprocessor compiler directives into a [`PreprocessorText`] CST node.
pub fn pp_parser(s: Span) -> IResult<Span, PreprocessorText> {
    init();
    preprocessor_text(s)
}

fn init() {
    nom_packrat::init!();
    clear_directive();
    clear_version();
}
