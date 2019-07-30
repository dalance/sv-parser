use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
pub(crate) fn function_data_type_or_implicit(s: Span) -> IResult<Span, FunctionDataTypeOrImplicit> {
    alt((
        map(
            terminated(
                data_type_or_void,
                peek(pair(
                    opt(interface_identifier_or_class_scope),
                    function_identifier,
                )),
            ),
            |x| FunctionDataTypeOrImplicit::DataTypeOrVoid(Box::new(x)),
        ),
        map(
            terminated(
                implicit_data_type,
                peek(pair(
                    opt(interface_identifier_or_class_scope),
                    function_identifier,
                )),
            ),
            |x| FunctionDataTypeOrImplicit::ImplicitDataType(Box::new(x)),
        ),
    ))(s)
}

#[tracable_parser]
pub(crate) fn function_declaration(s: Span) -> IResult<Span, FunctionDeclaration> {
    let (s, a) = keyword("function")(s)?;
    let (s, b) = opt(lifetime)(s)?;
    let (s, c) = function_body_declaration(s)?;
    Ok((s, FunctionDeclaration { nodes: (a, b, c) }))
}

#[tracable_parser]
pub(crate) fn function_body_declaration(s: Span) -> IResult<Span, FunctionBodyDeclaration> {
    alt((
        function_body_declaration_without_port,
        function_body_declaration_with_port,
    ))(s)
}

#[tracable_parser]
pub(crate) fn function_body_declaration_without_port(
    s: Span,
) -> IResult<Span, FunctionBodyDeclaration> {
    let (s, a) = function_data_type_or_implicit(s)?;
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

#[tracable_parser]
pub(crate) fn function_body_declaration_with_port(
    s: Span,
) -> IResult<Span, FunctionBodyDeclaration> {
    let (s, a) = function_data_type_or_implicit(s)?;
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

#[tracable_parser]
pub(crate) fn interface_identifier_or_class_scope(
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

#[tracable_parser]
pub(crate) fn function_prototype(s: Span) -> IResult<Span, FunctionPrototype> {
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

#[tracable_parser]
pub(crate) fn dpi_import_export(s: Span) -> IResult<Span, DpiImportExport> {
    alt((
        dpi_import_export_import_function,
        dpi_import_export_import_task,
        dpi_import_export_export_function,
        dpi_import_export_export_task,
    ))(s)
}

#[tracable_parser]
pub(crate) fn dpi_import_export_import_function(s: Span) -> IResult<Span, DpiImportExport> {
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

#[tracable_parser]
pub(crate) fn dpi_import_export_import_task(s: Span) -> IResult<Span, DpiImportExport> {
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

#[tracable_parser]
pub(crate) fn dpi_import_export_export_function(s: Span) -> IResult<Span, DpiImportExport> {
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

#[tracable_parser]
pub(crate) fn dpi_import_export_export_task(s: Span) -> IResult<Span, DpiImportExport> {
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

#[tracable_parser]
pub(crate) fn dpi_spec_string(s: Span) -> IResult<Span, DpiSpecString> {
    alt((
        map(keyword("DPI-C"), |x| DpiSpecString::DpiC(Box::new(x))),
        map(keyword("DPI"), |x| DpiSpecString::Dpi(Box::new(x))),
    ))(s)
}

#[tracable_parser]
pub(crate) fn dpi_function_import_property(s: Span) -> IResult<Span, DpiFunctionImportProperty> {
    alt((
        map(keyword("context"), |x| {
            DpiFunctionImportProperty::Context(Box::new(x))
        }),
        map(keyword("pure"), |x| {
            DpiFunctionImportProperty::Pure(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn dpi_task_import_property(s: Span) -> IResult<Span, DpiTaskImportProperty> {
    let (s, a) = keyword("context")(s)?;
    Ok((s, DpiTaskImportProperty::Context(Box::new(a))))
}

#[tracable_parser]
pub(crate) fn dpi_function_proto(s: Span) -> IResult<Span, DpiFunctionProto> {
    let (s, a) = function_prototype(s)?;
    Ok((s, DpiFunctionProto { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn dpi_task_proto(s: Span) -> IResult<Span, DpiTaskProto> {
    let (s, a) = task_prototype(s)?;
    Ok((s, DpiTaskProto { nodes: (a,) }))
}
