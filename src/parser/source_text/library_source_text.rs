use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct LibraryText<'a> {
    pub nodes: (Vec<LibraryDescription<'a>>,),
}

#[derive(Debug)]
pub enum LibraryDescription<'a> {
    LibraryDeclaration(LibraryDeclaration<'a>),
    IncludeStatement(IncludeStatement<'a>),
    ConfigDeclaration(ConfigDeclaration<'a>),
}

#[derive(Debug)]
pub struct LibraryDeclaration<'a> {
    pub nodes: (
        LibraryIdentifier<'a>,
        Vec<FilePathSpec<'a>>,
        Option<Vec<FilePathSpec<'a>>>,
    ),
}

#[derive(Debug)]
pub struct IncludeStatement<'a> {
    pub nodes: (FilePathSpec<'a>,),
}

#[derive(Debug)]
pub struct FilePathSpec<'a> {
    pub nodes: (Span<'a>,),
}

// -----------------------------------------------------------------------------

pub fn library_text(s: Span) -> IResult<Span, LibraryText> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn library_description(s: Span) -> IResult<Span, LibraryDescription> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn library_declaration(s: Span) -> IResult<Span, LibraryDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn include_statement(s: Span) -> IResult<Span, IncludeStatement> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}
