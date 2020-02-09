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

#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct SpanInfo {
    #[cfg(feature = "trace")]
    pub tracable_info: TracableInfo,
    pub recursive_info: RecursiveInfo,
}

pub type Span<'a> = nom_locate::LocatedSpanEx<&'a str, SpanInfo>;
pub type IResult<T, U> = nom::IResult<T, U, GreedyError<T>>;

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

pub fn sv_parser(s: Span) -> IResult<Span, SourceText> {
    nom_packrat::init!();
    source_text(s)
}

pub fn lib_parser(s: Span) -> IResult<Span, LibraryText> {
    nom_packrat::init!();
    library_text(s)
}

pub fn pp_parser(s: Span) -> IResult<Span, PreprocessorText> {
    nom_packrat::init!();
    preprocessor_text(s)
}
