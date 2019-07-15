use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

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
pub enum InterfaceIdentifierOrClassScope<'a> {
    InterfaceIdentifier((InterfaceIdentifier<'a>, Symbol<'a>)),
    ClassScope(ClassScope<'a>),
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
        Symbol<'a>,
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
        Symbol<'a>,
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
    alt((
        map(data_type_or_void, |x| {
            FunctionDataTypeOrImplicit::DataTypeOrVoid(x)
        }),
        map(implicit_data_type, |x| {
            FunctionDataTypeOrImplicit::ImplicitDataType(x)
        }),
    ))(s)
}

pub fn function_declaration(s: Span) -> IResult<Span, FunctionDeclaration> {
    let (s, a) = symbol("function")(s)?;
    let (s, b) = opt(lifetime)(s)?;
    let (s, c) = function_body_declaration(s)?;
    Ok((s, FunctionDeclaration { nodes: (a, b, c) }))
}

pub fn function_body_declaration(s: Span) -> IResult<Span, FunctionBodyDeclaration> {
    alt((
        function_body_declaration_without_port,
        function_body_declaration_with_port,
    ))(s)
}

pub fn function_body_declaration_without_port(s: Span) -> IResult<Span, FunctionBodyDeclaration> {
    let (s, a) = function_data_type_or_implicit(s)?;
    let (s, b) = opt(interface_identifier_or_class_scope)(s)?;
    let (s, c) = function_identifier(s)?;
    let (s, d) = symbol(";")(s)?;
    let (s, e) = many0(tf_item_declaration)(s)?;
    let (s, f) = many0(function_statement_or_null)(s)?;
    let (s, g) = symbol("endfunction")(s)?;
    let (s, h) = opt(pair(symbol(":"), function_identifier))(s)?;
    Ok((
        s,
        FunctionBodyDeclaration::WithoutPort(FunctionBodyDeclarationWithoutPort {
            nodes: (a, b, c, d, e, f, g, h),
        }),
    ))
}

pub fn function_body_declaration_with_port(s: Span) -> IResult<Span, FunctionBodyDeclaration> {
    let (s, a) = function_data_type_or_implicit(s)?;
    let (s, b) = opt(interface_identifier_or_class_scope)(s)?;
    let (s, c) = function_identifier(s)?;
    let (s, d) = paren(opt(tf_port_list))(s)?;
    let (s, e) = symbol(";")(s)?;
    let (s, f) = many0(block_item_declaration)(s)?;
    let (s, g) = many0(function_statement_or_null)(s)?;
    let (s, h) = symbol("endfunction")(s)?;
    let (s, i) = opt(pair(symbol(":"), function_identifier))(s)?;
    Ok((
        s,
        FunctionBodyDeclaration::WithPort(FunctionBodyDeclarationWithPort {
            nodes: (a, b, c, d, e, f, g, h, i),
        }),
    ))
}

pub fn interface_identifier_or_class_scope(
    s: Span,
) -> IResult<Span, InterfaceIdentifierOrClassScope> {
    alt((
        map(pair(interface_identifier, symbol(".")), |x| {
            InterfaceIdentifierOrClassScope::InterfaceIdentifier(x)
        }),
        map(class_scope, |x| {
            InterfaceIdentifierOrClassScope::ClassScope(x)
        }),
    ))(s)
}

pub fn function_prototype(s: Span) -> IResult<Span, FunctionPrototype> {
    let (s, a) = symbol("function")(s)?;
    let (s, b) = data_type_or_void(s)?;
    let (s, c) = function_identifier(s)?;
    let (s, d) = opt(paren(opt(tf_port_list)))(s)?;
    Ok((
        s,
        FunctionPrototype {
            nodes: (a, b, c, d),
        },
    ))
}

pub fn dpi_import_export(s: Span) -> IResult<Span, DpiImportExport> {
    alt((
        dpi_import_export_import_function,
        dpi_import_export_import_task,
        dpi_import_export_export_function,
        dpi_import_export_export_task,
    ))(s)
}

pub fn dpi_import_export_import_function(s: Span) -> IResult<Span, DpiImportExport> {
    let (s, a) = symbol("import")(s)?;
    let (s, b) = dpi_spec_string(s)?;
    let (s, c) = opt(dpi_function_import_property)(s)?;
    let (s, d) = opt(pair(c_identifier, symbol("=")))(s)?;
    let (s, e) = dpi_function_proto(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        DpiImportExport::ImportFunction(DpiImportExportImportFunction {
            nodes: (a, b, c, d, e, f),
        }),
    ))
}

pub fn dpi_import_export_import_task(s: Span) -> IResult<Span, DpiImportExport> {
    let (s, a) = symbol("import")(s)?;
    let (s, b) = dpi_spec_string(s)?;
    let (s, c) = opt(dpi_task_import_property)(s)?;
    let (s, d) = opt(pair(c_identifier, symbol("=")))(s)?;
    let (s, e) = dpi_task_proto(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        DpiImportExport::ImportTask(DpiImportExportImportTask {
            nodes: (a, b, c, d, e, f),
        }),
    ))
}

pub fn dpi_import_export_export_function(s: Span) -> IResult<Span, DpiImportExport> {
    let (s, a) = symbol("export")(s)?;
    let (s, b) = dpi_spec_string(s)?;
    let (s, c) = opt(pair(c_identifier, symbol("=")))(s)?;
    let (s, d) = symbol("function")(s)?;
    let (s, e) = function_identifier(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        DpiImportExport::ExportFunction(DpiImportExportExportFunction {
            nodes: (a, b, c, d, e, f),
        }),
    ))
}

pub fn dpi_import_export_export_task(s: Span) -> IResult<Span, DpiImportExport> {
    let (s, a) = symbol("export")(s)?;
    let (s, b) = dpi_spec_string(s)?;
    let (s, c) = opt(pair(c_identifier, symbol("=")))(s)?;
    let (s, d) = symbol("task")(s)?;
    let (s, e) = task_identifier(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        DpiImportExport::ExportTask(DpiImportExportExportTask {
            nodes: (a, b, c, d, e, f),
        }),
    ))
}

pub fn dpi_spec_string(s: Span) -> IResult<Span, DpiSpecString> {
    alt((
        map(symbol("DPI-C"), |x| DpiSpecString::DpiC(x)),
        map(symbol("DPI"), |x| DpiSpecString::Dpi(x)),
    ))(s)
}

pub fn dpi_function_import_property(s: Span) -> IResult<Span, DpiFunctionImportProperty> {
    alt((
        map(symbol("context"), |x| DpiFunctionImportProperty::Context(x)),
        map(symbol("pure"), |x| DpiFunctionImportProperty::Pure(x)),
    ))(s)
}

pub fn dpi_task_import_property(s: Span) -> IResult<Span, DpiTaskImportProperty> {
    let (s, a) = symbol("context")(s)?;
    Ok((s, DpiTaskImportProperty::Context(a)))
}

pub fn dpi_function_proto(s: Span) -> IResult<Span, DpiFunctionProto> {
    let (s, a) = function_prototype(s)?;
    Ok((s, DpiFunctionProto { nodes: (a,) }))
}

pub fn dpi_task_proto(s: Span) -> IResult<Span, DpiTaskProto> {
    let (s, a) = task_prototype(s)?;
    Ok((s, DpiTaskProto { nodes: (a,) }))
}
