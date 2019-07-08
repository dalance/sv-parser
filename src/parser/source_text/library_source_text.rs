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
    pub nodes: (&'a str,),
}

// -----------------------------------------------------------------------------

pub fn library_text(s: &str) -> IResult<&str, LibraryText> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn library_description(s: &str) -> IResult<&str, LibraryDescription> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn library_declaration(s: &str) -> IResult<&str, LibraryDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn include_statement(s: &str) -> IResult<&str, IncludeStatement> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}
