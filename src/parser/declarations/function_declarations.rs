use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum FunctionDataTypeOrImplicit<'a> {
    DataType(DataTypeOrVoid<'a>),
    Implicit(ImplicitDataType<'a>),
}

#[derive(Debug)]
pub struct FunctionDeclaration<'a> {
    pub nodes: (Option<Lifetime>, FunctionBodyDeclaration<'a>),
}

#[derive(Debug)]
pub enum FunctionBodyDeclaration<'a> {
    WithoutPort(FunctionBodyDeclarationWithoutPort<'a>),
    WithPort(FunctionBodyDeclarationWithPort<'a>),
}

#[derive(Debug)]
pub struct FunctionBodyDeclarationWithoutPort<'a> {
    pub nodes: (
        FunctionDataTypeOrImplicit<'a>,
        Option<InterfaceIdentifierOrClassScope<'a>>,
        Identifier<'a>,
        Vec<TfItemDeclaration<'a>>,
        Vec<FunctionStatementOrNull<'a>>,
        Option<Identifier<'a>>,
    ),
}

#[derive(Debug)]
pub struct FunctionBodyDeclarationWithPort<'a> {
    pub nodes: (
        FunctionDataTypeOrImplicit<'a>,
        Option<InterfaceIdentifierOrClassScope<'a>>,
        Identifier<'a>,
        Option<TfPortList<'a>>,
        Vec<BlockItemDeclaration<'a>>,
        Vec<FunctionStatementOrNull<'a>>,
        Option<Identifier<'a>>,
    ),
}

#[derive(Debug)]
pub struct FunctionPrototype<'a> {
    pub nodes: (DataTypeOrVoid<'a>, Identifier<'a>, Option<TfPortList<'a>>),
}

#[derive(Debug)]
pub enum DpiImportExport<'a> {
    ImportFunction(DpiImportExportImportFunction<'a>),
    ImportTask(DpiImportExportImportTask<'a>),
    ExportFunction(DpiImportExportExportFunction<'a>),
    ExportTask(DpiImportExportExportTask<'a>),
}

#[derive(Debug)]
pub struct DpiImportExportImportFunction<'a> {
    pub nodes: (
        DpiSpecString,
        Option<DpiFunctionImportProperty>,
        Option<Identifier<'a>>,
        DpiFunctionProto<'a>,
    ),
}

#[derive(Debug)]
pub struct DpiImportExportImportTask<'a> {
    pub nodes: (
        DpiSpecString,
        Option<DpiTaskImportProperty>,
        Option<Identifier<'a>>,
        DpiTaskProto<'a>,
    ),
}

#[derive(Debug)]
pub struct DpiImportExportExportFunction<'a> {
    pub nodes: (DpiSpecString, Option<Identifier<'a>>, Identifier<'a>),
}

#[derive(Debug)]
pub struct DpiImportExportExportTask<'a> {
    pub nodes: (DpiSpecString, Option<Identifier<'a>>, Identifier<'a>),
}

#[derive(Debug)]
pub enum DpiSpecString {
    DpiC,
    Dpi,
}

#[derive(Debug)]
pub enum DpiFunctionImportProperty {
    Context,
    Pure,
}

#[derive(Debug)]
pub enum DpiTaskImportProperty {
    Context,
}

#[derive(Debug)]
pub struct DpiFunctionProto<'a> {
    pub nodes: (FunctionPrototype<'a>,),
}

#[derive(Debug)]
pub struct DpiTaskProto<'a> {
    pub nodes: (TaskPrototype<'a>,),
}

// -----------------------------------------------------------------------------

pub fn function_data_type_or_implicit(s: Span) -> IResult<Span, FunctionDataTypeOrImplicit> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn function_declaration(s: Span) -> IResult<Span, FunctionDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn function_body_declaration(s: Span) -> IResult<Span, FunctionBodyDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn function_prototype(s: Span) -> IResult<Span, FunctionPrototype> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn dpi_import_export(s: Span) -> IResult<Span, DpiImportExport> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn dpi_spec_string(s: Span) -> IResult<Span, DpiSpecString> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn dpi_function_import_property(s: Span) -> IResult<Span, DpiFunctionImportProperty> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn dpi_task_import_property(s: Span) -> IResult<Span, DpiTaskImportProperty> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn dpi_function_proto(s: Span) -> IResult<Span, DpiFunctionProto> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn dpi_task_proto(s: Span) -> IResult<Span, DpiTaskProto> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}
