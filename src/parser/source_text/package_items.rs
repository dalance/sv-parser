use crate::ast::*;
use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum PackageItem<'a> {
    PackageOrGenerateItemDeclaration(PackageOrGenerateItemDeclaration<'a>),
    AnonymousProgram(AnonymousProgram<'a>),
    PackageExportDeclaration(PackageExportDeclaration<'a>),
    TimeunitsDeclaration(TimeunitsDeclaration<'a>),
}

#[derive(Debug, Node)]
pub enum PackageOrGenerateItemDeclaration<'a> {
    NetDeclaration(NetDeclaration<'a>),
    DataDeclaration(DataDeclaration<'a>),
    TaskDeclaration(TaskDeclaration<'a>),
    FunctionDeclaration(FunctionDeclaration<'a>),
    CheckerDeclaration(CheckerDeclaration<'a>),
    DpiImportExport(DpiImportExport<'a>),
    ExternConstraintDeclaration(ExternConstraintDeclaration<'a>),
    ClassDeclaration(ClassDeclaration<'a>),
    ClassConstructorDeclaration(ClassConstructorDeclaration<'a>),
    LocalParameterDeclaration(LocalParameterDeclaration<'a>),
    ParameterDeclaration(ParameterDeclaration<'a>),
    CovergroupDeclaration(CovergroupDeclaration<'a>),
    AssertionItemDeclaration(AssertionItemDeclaration<'a>),
    Empty(Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct AnonymousProgram<'a> {
    pub nodes: (Vec<AnonymousProgramItem<'a>>,),
}

#[derive(Debug, Node)]
pub enum AnonymousProgramItem<'a> {
    TaskDeclaration(TaskDeclaration<'a>),
    FunctionDeclaration(FunctionDeclaration<'a>),
    ClassDeclaration(ClassDeclaration<'a>),
    CovergroupDeclaration(CovergroupDeclaration<'a>),
    ClassConstructorDeclaration(ClassConstructorDeclaration<'a>),
    Empty(Symbol<'a>),
}

// -----------------------------------------------------------------------------

pub fn package_item(s: Span) -> IResult<Span, PackageItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn package_or_generate_item_declaration(
    s: Span,
) -> IResult<Span, PackageOrGenerateItemDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn anonymous_program(s: Span) -> IResult<Span, AnonymousProgram> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn anonymous_program_item(s: Span) -> IResult<Span, AnonymousProgramItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}
