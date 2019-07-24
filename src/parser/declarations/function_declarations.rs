use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum FunctionDataTypeOrImplicit {
    DataTypeOrVoid(Box<DataTypeOrVoid>),
    ImplicitDataType(Box<ImplicitDataType>),
}

#[derive(Clone, Debug, Node)]
pub struct FunctionDeclaration {
    pub nodes: (Keyword, Option<Lifetime>, FunctionBodyDeclaration),
}

#[derive(Clone, Debug, Node)]
pub enum FunctionBodyDeclaration {
    WithoutPort(Box<FunctionBodyDeclarationWithoutPort>),
    WithPort(Box<FunctionBodyDeclarationWithPort>),
}

#[derive(Clone, Debug, Node)]
pub struct FunctionBodyDeclarationWithoutPort {
    pub nodes: (
        Option<FunctionDataTypeOrImplicit>,
        Option<InterfaceIdentifierOrClassScope>,
        FunctionIdentifier,
        Symbol,
        Vec<TfItemDeclaration>,
        Vec<FunctionStatementOrNull>,
        Keyword,
        Option<(Symbol, FunctionIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct FunctionBodyDeclarationWithPort {
    pub nodes: (
        Option<FunctionDataTypeOrImplicit>,
        Option<InterfaceIdentifierOrClassScope>,
        FunctionIdentifier,
        Paren<Option<TfPortList>>,
        Symbol,
        Vec<BlockItemDeclaration>,
        Vec<FunctionStatementOrNull>,
        Keyword,
        Option<(Symbol, FunctionIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum InterfaceIdentifierOrClassScope {
    InterfaceIdentifier(Box<(InterfaceIdentifier, Symbol)>),
    ClassScope(Box<ClassScope>),
}

#[derive(Clone, Debug, Node)]
pub struct FunctionPrototype {
    pub nodes: (
        Keyword,
        DataTypeOrVoid,
        FunctionIdentifier,
        Option<Paren<Option<TfPortList>>>,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum DpiImportExport {
    ImportFunction(Box<DpiImportExportImportFunction>),
    ImportTask(Box<DpiImportExportImportTask>),
    ExportFunction(Box<DpiImportExportExportFunction>),
    ExportTask(Box<DpiImportExportExportTask>),
}

#[derive(Clone, Debug, Node)]
pub struct DpiImportExportImportFunction {
    pub nodes: (
        Keyword,
        DpiSpecString,
        Option<DpiFunctionImportProperty>,
        Option<(CIdentifier, Symbol)>,
        DpiFunctionProto,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct DpiImportExportImportTask {
    pub nodes: (
        Keyword,
        DpiSpecString,
        Option<DpiTaskImportProperty>,
        Option<(CIdentifier, Symbol)>,
        DpiTaskProto,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct DpiImportExportExportFunction {
    pub nodes: (
        Keyword,
        DpiSpecString,
        Option<(CIdentifier, Symbol)>,
        Keyword,
        FunctionIdentifier,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct DpiImportExportExportTask {
    pub nodes: (
        Keyword,
        DpiSpecString,
        Option<(CIdentifier, Symbol)>,
        Keyword,
        TaskIdentifier,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum DpiSpecString {
    DpiC(Box<Keyword>),
    Dpi(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub enum DpiFunctionImportProperty {
    Context(Box<Keyword>),
    Pure(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub enum DpiTaskImportProperty {
    Context(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub struct DpiFunctionProto {
    pub nodes: (FunctionPrototype,),
}

#[derive(Clone, Debug, Node)]
pub struct DpiTaskProto {
    pub nodes: (TaskPrototype,),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn function_data_type_or_implicit(s: Span) -> IResult<Span, FunctionDataTypeOrImplicit> {
    alt((
        map(data_type_or_void, |x| {
            FunctionDataTypeOrImplicit::DataTypeOrVoid(Box::new(x))
        }),
        map(implicit_data_type, |x| {
            FunctionDataTypeOrImplicit::ImplicitDataType(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn function_declaration(s: Span) -> IResult<Span, FunctionDeclaration> {
    let (s, a) = keyword("function")(s)?;
    let (s, b) = opt(lifetime)(s)?;
    let (s, c) = function_body_declaration(s)?;
    Ok((s, FunctionDeclaration { nodes: (a, b, c) }))
}

#[parser]
pub fn function_body_declaration(s: Span) -> IResult<Span, FunctionBodyDeclaration> {
    alt((
        function_body_declaration_without_port,
        function_body_declaration_with_port,
    ))(s)
}

#[parser(Ambiguous)]
pub fn function_body_declaration_without_port(s: Span) -> IResult<Span, FunctionBodyDeclaration> {
    let (s, a) = ambiguous_opt(function_data_type_or_implicit)(s)?;
    let (s, b) = opt(interface_identifier_or_class_scope)(s)?;
    let (s, c) = function_identifier(s)?;
    let (s, d) = symbol(";")(s)?;
    let (s, e) = many0(tf_item_declaration)(s)?;
    let (s, f) = many0(function_statement_or_null)(s)?;
    let (s, g) = keyword("endfunction")(s)?;
    let (s, h) = opt(pair(symbol(":"), function_identifier))(s)?;
    Ok((
        s,
        FunctionBodyDeclaration::WithoutPort(Box::new(FunctionBodyDeclarationWithoutPort {
            nodes: (a, b, c, d, e, f, g, h),
        })),
    ))
}

#[parser(Ambiguous)]
pub fn function_body_declaration_with_port(s: Span) -> IResult<Span, FunctionBodyDeclaration> {
    let (s, a) = ambiguous_opt(function_data_type_or_implicit)(s)?;
    let (s, b) = opt(interface_identifier_or_class_scope)(s)?;
    let (s, c) = function_identifier(s)?;
    let (s, d) = paren(opt(tf_port_list))(s)?;
    let (s, e) = symbol(";")(s)?;
    let (s, f) = many0(block_item_declaration)(s)?;
    let (s, g) = many0(function_statement_or_null)(s)?;
    let (s, h) = keyword("endfunction")(s)?;
    let (s, i) = opt(pair(symbol(":"), function_identifier))(s)?;
    Ok((
        s,
        FunctionBodyDeclaration::WithPort(Box::new(FunctionBodyDeclarationWithPort {
            nodes: (a, b, c, d, e, f, g, h, i),
        })),
    ))
}

#[parser]
pub fn interface_identifier_or_class_scope(
    s: Span,
) -> IResult<Span, InterfaceIdentifierOrClassScope> {
    alt((
        map(pair(interface_identifier, symbol(".")), |x| {
            InterfaceIdentifierOrClassScope::InterfaceIdentifier(Box::new(x))
        }),
        map(class_scope, |x| {
            InterfaceIdentifierOrClassScope::ClassScope(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn function_prototype(s: Span) -> IResult<Span, FunctionPrototype> {
    let (s, a) = keyword("function")(s)?;
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

#[parser]
pub fn dpi_import_export(s: Span) -> IResult<Span, DpiImportExport> {
    alt((
        dpi_import_export_import_function,
        dpi_import_export_import_task,
        dpi_import_export_export_function,
        dpi_import_export_export_task,
    ))(s)
}

#[parser]
pub fn dpi_import_export_import_function(s: Span) -> IResult<Span, DpiImportExport> {
    let (s, a) = keyword("import")(s)?;
    let (s, b) = dpi_spec_string(s)?;
    let (s, c) = opt(dpi_function_import_property)(s)?;
    let (s, d) = opt(pair(c_identifier, symbol("=")))(s)?;
    let (s, e) = dpi_function_proto(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        DpiImportExport::ImportFunction(Box::new(DpiImportExportImportFunction {
            nodes: (a, b, c, d, e, f),
        })),
    ))
}

#[parser]
pub fn dpi_import_export_import_task(s: Span) -> IResult<Span, DpiImportExport> {
    let (s, a) = keyword("import")(s)?;
    let (s, b) = dpi_spec_string(s)?;
    let (s, c) = opt(dpi_task_import_property)(s)?;
    let (s, d) = opt(pair(c_identifier, symbol("=")))(s)?;
    let (s, e) = dpi_task_proto(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        DpiImportExport::ImportTask(Box::new(DpiImportExportImportTask {
            nodes: (a, b, c, d, e, f),
        })),
    ))
}

#[parser]
pub fn dpi_import_export_export_function(s: Span) -> IResult<Span, DpiImportExport> {
    let (s, a) = keyword("export")(s)?;
    let (s, b) = dpi_spec_string(s)?;
    let (s, c) = opt(pair(c_identifier, symbol("=")))(s)?;
    let (s, d) = keyword("function")(s)?;
    let (s, e) = function_identifier(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        DpiImportExport::ExportFunction(Box::new(DpiImportExportExportFunction {
            nodes: (a, b, c, d, e, f),
        })),
    ))
}

#[parser]
pub fn dpi_import_export_export_task(s: Span) -> IResult<Span, DpiImportExport> {
    let (s, a) = keyword("export")(s)?;
    let (s, b) = dpi_spec_string(s)?;
    let (s, c) = opt(pair(c_identifier, symbol("=")))(s)?;
    let (s, d) = keyword("task")(s)?;
    let (s, e) = task_identifier(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        DpiImportExport::ExportTask(Box::new(DpiImportExportExportTask {
            nodes: (a, b, c, d, e, f),
        })),
    ))
}

#[parser]
pub fn dpi_spec_string(s: Span) -> IResult<Span, DpiSpecString> {
    alt((
        map(keyword("DPI-C"), |x| DpiSpecString::DpiC(Box::new(x))),
        map(keyword("DPI"), |x| DpiSpecString::Dpi(Box::new(x))),
    ))(s)
}

#[parser]
pub fn dpi_function_import_property(s: Span) -> IResult<Span, DpiFunctionImportProperty> {
    alt((
        map(keyword("context"), |x| {
            DpiFunctionImportProperty::Context(Box::new(x))
        }),
        map(keyword("pure"), |x| {
            DpiFunctionImportProperty::Pure(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn dpi_task_import_property(s: Span) -> IResult<Span, DpiTaskImportProperty> {
    let (s, a) = keyword("context")(s)?;
    Ok((s, DpiTaskImportProperty::Context(Box::new(a))))
}

#[parser]
pub fn dpi_function_proto(s: Span) -> IResult<Span, DpiFunctionProto> {
    let (s, a) = function_prototype(s)?;
    Ok((s, DpiFunctionProto { nodes: (a,) }))
}

#[parser]
pub fn dpi_task_proto(s: Span) -> IResult<Span, DpiTaskProto> {
    let (s, a) = task_prototype(s)?;
    Ok((s, DpiTaskProto { nodes: (a,) }))
}
