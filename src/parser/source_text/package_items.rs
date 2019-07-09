use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum PackageItem<'a> {
    PackageOrGenerateItemDeclaration(PackageOrGenerateItemDeclaration<'a>),
    AnonymousProgram(AnonymousProgram<'a>),
    PackageExportDeclaration(PackageExportDeclaration<'a>),
    TimeunitsDeclaration(TimeunitsDeclaration<'a>),
}

#[derive(Debug)]
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
    Empty,
}

#[derive(Debug)]
pub struct AnonymousProgram<'a> {
    pub nodes: (Vec<AnonymousProgramItem<'a>>,),
}

#[derive(Debug)]
pub enum AnonymousProgramItem<'a> {
    TaskDeclaration(TaskDeclaration<'a>),
    FunctionDeclaration(FunctionDeclaration<'a>),
    ClassDeclaration(ClassDeclaration<'a>),
    CovergroupDeclaration(CovergroupDeclaration<'a>),
    ClassConstructorDeclaration(ClassConstructorDeclaration<'a>),
    Empty,
}

// -----------------------------------------------------------------------------

pub fn package_item(s: &str) -> IResult<&str, PackageItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn package_or_generate_item_declaration(
    s: &str,
) -> IResult<&str, PackageOrGenerateItemDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn anonymous_program(s: &str) -> IResult<&str, AnonymousProgram> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn anonymous_program_item(s: &str) -> IResult<&str, AnonymousProgramItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}
