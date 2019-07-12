use crate::ast::*;
use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum FunctionDataTypeOrImplicit<'a> {
    DataTypeOrVoid(DataTypeOrVoid<'a>),
    ImplicitDataType(ImplicitDataType<'a>),
}

#[derive(Debug, Node)]
pub struct FunctionDeclaration<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<Lifetime<'a>>,
        FunctionBodyDeclaration<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum FunctionBodyDeclaration<'a> {
    WithoutPort(FunctionBodyDeclarationWithoutPort<'a>),
    WithPort(FunctionBodyDeclarationWithPort<'a>),
}

#[derive(Debug, Node)]
pub struct FunctionBodyDeclarationWithoutPort<'a> {
    pub nodes: (
        FunctionDataTypeOrImplicit<'a>,
        Option<InterfaceIdentifierOrClassScope<'a>>,
        FunctionIdentifier<'a>,
        Symbol<'a>,
        Vec<TfItemDeclaration<'a>>,
        Vec<FunctionStatementOrNull<'a>>,
        Symbol<'a>,
        Option<(Symbol<'a>, FunctionIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct FunctionBodyDeclarationWithPort<'a> {
    pub nodes: (
        FunctionDataTypeOrImplicit<'a>,
        Option<InterfaceIdentifierOrClassScope<'a>>,
        FunctionIdentifier<'a>,
        Paren<'a, Option<TfPortList<'a>>>,
        Symbol<'a>,
        Vec<BlockItemDeclaration<'a>>,
        Vec<FunctionStatementOrNull<'a>>,
        Symbol<'a>,
        Option<(Symbol<'a>, FunctionIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct FunctionPrototype<'a> {
    pub nodes: (
        Symbol<'a>,
        DataTypeOrVoid<'a>,
        FunctionIdentifier<'a>,
        Option<Paren<'a, Option<TfPortList<'a>>>>,
    ),
}

#[derive(Debug, Node)]
pub enum DpiImportExport<'a> {
    ImportFunction(DpiImportExportImportFunction<'a>),
    ImportTask(DpiImportExportImportTask<'a>),
    ExportFunction(DpiImportExportExportFunction<'a>),
    ExportTask(DpiImportExportExportTask<'a>),
}

#[derive(Debug, Node)]
pub struct DpiImportExportImportFunction<'a> {
    pub nodes: (
        Symbol<'a>,
        DpiSpecString<'a>,
        Option<DpiFunctionImportProperty<'a>>,
        Option<(CIdentifier<'a>, Symbol<'a>)>,
        DpiFunctionProto<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct DpiImportExportImportTask<'a> {
    pub nodes: (
        Symbol<'a>,
        DpiSpecString<'a>,
        Option<DpiTaskImportProperty<'a>>,
        Option<(CIdentifier<'a>, Symbol<'a>)>,
        DpiTaskProto<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct DpiImportExportExportFunction<'a> {
    pub nodes: (
        Symbol<'a>,
        DpiSpecString<'a>,
        Option<(CIdentifier<'a>, Symbol<'a>)>,
        Symbol<'a>,
        FunctionIdentifier<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct DpiImportExportExportTask<'a> {
    pub nodes: (
        Symbol<'a>,
        DpiSpecString<'a>,
        Option<(CIdentifier<'a>, Symbol<'a>)>,
        Symbol<'a>,
        TaskIdentifier<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum DpiSpecString<'a> {
    DpiC(Symbol<'a>),
    Dpi(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum DpiFunctionImportProperty<'a> {
    Context(Symbol<'a>),
    Pure(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum DpiTaskImportProperty<'a> {
    Context(Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct DpiFunctionProto<'a> {
    pub nodes: (FunctionPrototype<'a>,),
}

#[derive(Debug, Node)]
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
