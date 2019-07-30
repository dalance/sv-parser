use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
pub(crate) fn data_declaration(s: Span) -> IResult<Span, DataDeclaration> {
    alt((
        data_declaration_variable,
        map(type_declaration, |x| {
            DataDeclaration::TypeDeclaration(Box::new(x))
        }),
        map(package_import_declaration, |x| {
            DataDeclaration::PackageImportDeclaration(Box::new(x))
        }),
        map(net_type_declaration, |x| {
            DataDeclaration::NetTypeDeclaration(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn data_declaration_variable(s: Span) -> IResult<Span, DataDeclaration> {
    let (s, a) = opt(r#const)(s)?;
    let (s, b) = opt(var)(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = data_type_or_implicit_data_declaration_variable(s)?;
    let (s, e) = list_of_variable_decl_assignments(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        DataDeclaration::Variable(Box::new(DataDeclarationVariable {
            nodes: (a, b, c, d, e, f),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn data_type_or_implicit_data_declaration_variable(
    s: Span,
) -> IResult<Span, DataTypeOrImplicit> {
    alt((
        map(terminated(data_type, peek(variable_decl_assignment)), |x| {
            DataTypeOrImplicit::DataType(Box::new(x))
        }),
        map(
            terminated(implicit_data_type, peek(variable_decl_assignment)),
            |x| DataTypeOrImplicit::ImplicitDataType(Box::new(x)),
        ),
    ))(s)
}

#[tracable_parser]
pub(crate) fn r#const(s: Span) -> IResult<Span, Const> {
    let (s, a) = keyword("const")(s)?;
    Ok((s, Const { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn package_import_declaration(s: Span) -> IResult<Span, PackageImportDeclaration> {
    let (s, a) = keyword("import")(s)?;
    let (s, b) = list(symbol(","), package_import_item)(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((s, PackageImportDeclaration { nodes: (a, b, c) }))
}

#[tracable_parser]
pub(crate) fn package_import_item(s: Span) -> IResult<Span, PackageImportItem> {
    alt((package_import_item_identifier, package_import_item_asterisk))(s)
}

#[tracable_parser]
pub(crate) fn package_import_item_identifier(s: Span) -> IResult<Span, PackageImportItem> {
    let (s, a) = package_identifier(s)?;
    let (s, b) = symbol("::")(s)?;
    let (s, c) = identifier(s)?;
    Ok((
        s,
        PackageImportItem::Identifier(Box::new(PackageImportItemIdentifier { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn package_import_item_asterisk(s: Span) -> IResult<Span, PackageImportItem> {
    let (s, a) = package_identifier(s)?;
    let (s, b) = symbol("::")(s)?;
    let (s, c) = symbol("*")(s)?;
    Ok((
        s,
        PackageImportItem::Asterisk(Box::new(PackageImportItemAsterisk { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn package_export_declaration(s: Span) -> IResult<Span, PackageExportDeclaration> {
    alt((
        package_export_declaration_asterisk,
        package_export_declaration_item,
    ))(s)
}

#[tracable_parser]
pub(crate) fn package_export_declaration_asterisk(
    s: Span,
) -> IResult<Span, PackageExportDeclaration> {
    let (s, a) = keyword("export")(s)?;
    let (s, b) = symbol("*::*")(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        PackageExportDeclaration::Asterisk(Box::new(PackageExportDeclarationAsterisk {
            nodes: (a, b, c),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn package_export_declaration_item(s: Span) -> IResult<Span, PackageExportDeclaration> {
    let (s, a) = keyword("export")(s)?;
    let (s, b) = list(symbol(","), package_import_item)(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        PackageExportDeclaration::Item(Box::new(PackageExportDeclarationItem { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn genvar_declaration(s: Span) -> IResult<Span, GenvarDeclaration> {
    let (s, a) = keyword("genvar")(s)?;
    let (s, b) = list_of_genvar_identifiers(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((s, GenvarDeclaration { nodes: (a, b, c) }))
}

#[tracable_parser]
pub(crate) fn net_declaration(s: Span) -> IResult<Span, NetDeclaration> {
    alt((
        net_declaration_interconnect,
        net_declaration_net_type,
        net_declaration_net_type_identifier,
    ))(s)
}

#[tracable_parser]
pub(crate) fn net_declaration_net_type(s: Span) -> IResult<Span, NetDeclaration> {
    let (s, a) = net_type(s)?;
    let (s, b) = opt(strength)(s)?;
    let (s, c) = opt(vector_scalar)(s)?;
    let (s, d) = data_type_or_implicit_net_declaration_net_type(s)?;
    let (s, e) = opt(delay3)(s)?;
    let (s, f) = list_of_net_decl_assignments(s)?;
    let (s, g) = symbol(";")(s)?;
    Ok((
        s,
        NetDeclaration::NetType(Box::new(NetDeclarationNetType {
            nodes: (a, b, c, d, e, f, g),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn data_type_or_implicit_net_declaration_net_type(
    s: Span,
) -> IResult<Span, DataTypeOrImplicit> {
    alt((
        map(
            terminated(data_type, peek(pair(opt(delay3), net_decl_assignment))),
            |x| DataTypeOrImplicit::DataType(Box::new(x)),
        ),
        map(
            terminated(
                implicit_data_type,
                peek(pair(opt(delay3), net_decl_assignment)),
            ),
            |x| DataTypeOrImplicit::ImplicitDataType(Box::new(x)),
        ),
    ))(s)
}

#[tracable_parser]
pub(crate) fn strength(s: Span) -> IResult<Span, Strength> {
    alt((
        map(drive_strength, |x| Strength::Drive(Box::new(x))),
        map(charge_strength, |x| Strength::Charge(Box::new(x))),
    ))(s)
}

#[tracable_parser]
pub(crate) fn vector_scalar(s: Span) -> IResult<Span, VectorScalar> {
    alt((
        map(keyword("vectored"), |x| VectorScalar::Vectored(Box::new(x))),
        map(keyword("scalared"), |x| VectorScalar::Scalared(Box::new(x))),
    ))(s)
}

#[tracable_parser]
pub(crate) fn net_declaration_net_type_identifier(s: Span) -> IResult<Span, NetDeclaration> {
    let (s, a) = net_type_identifier(s)?;
    let (s, b) = opt(delay_control)(s)?;
    let (s, c) = list_of_net_decl_assignments(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        NetDeclaration::NetTypeIdentifier(Box::new(NetDeclarationNetTypeIdentifier {
            nodes: (a, b, c, d),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn net_declaration_interconnect(s: Span) -> IResult<Span, NetDeclaration> {
    let (s, a) = keyword("interconnect")(s)?;
    let (s, b) = implicit_data_type(s)?;
    let (s, c) = opt(pair(symbol("#"), delay_value))(s)?;
    let (s, d) = net_identifier(s)?;
    let (s, e) = many0(unpacked_dimension)(s)?;
    let (s, f) = opt(triple(
        symbol(","),
        net_identifier,
        many0(unpacked_dimension),
    ))(s)?;
    let (s, g) = symbol(";")(s)?;
    Ok((
        s,
        NetDeclaration::Interconnect(Box::new(NetDeclarationInterconnect {
            nodes: (a, b, c, d, e, f, g),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn type_declaration(s: Span) -> IResult<Span, TypeDeclaration> {
    alt((
        type_declaration_data_type,
        type_declaration_interface,
        type_declaration_reserved,
    ))(s)
}

#[tracable_parser]
pub(crate) fn type_declaration_data_type(s: Span) -> IResult<Span, TypeDeclaration> {
    let (s, a) = keyword("typedef")(s)?;
    let (s, b) = data_type(s)?;
    let (s, c) = type_identifier(s)?;
    let (s, d) = many0(variable_dimension)(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        TypeDeclaration::DataType(Box::new(TypeDeclarationDataType {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn type_declaration_interface(s: Span) -> IResult<Span, TypeDeclaration> {
    let (s, a) = keyword("typedef")(s)?;
    let (s, b) = interface_instance_identifier(s)?;
    let (s, c) = constant_bit_select(s)?;
    let (s, d) = symbol(".")(s)?;
    let (s, e) = type_identifier(s)?;
    let (s, f) = type_identifier(s)?;
    let (s, g) = symbol(";")(s)?;
    Ok((
        s,
        TypeDeclaration::Interface(Box::new(TypeDeclarationInterface {
            nodes: (a, b, c, d, e, f, g),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn type_declaration_reserved(s: Span) -> IResult<Span, TypeDeclaration> {
    let (s, a) = keyword("typedef")(s)?;
    let (s, b) = opt(type_declaration_keyword)(s)?;
    let (s, c) = type_identifier(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        TypeDeclaration::Reserved(Box::new(TypeDeclarationReserved {
            nodes: (a, b, c, d),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn type_declaration_keyword(s: Span) -> IResult<Span, TypeDeclarationKeyword> {
    alt((
        map(keyword("enum"), |x| {
            TypeDeclarationKeyword::Enum(Box::new(x))
        }),
        map(keyword("struct"), |x| {
            TypeDeclarationKeyword::Struct(Box::new(x))
        }),
        map(keyword("union"), |x| {
            TypeDeclarationKeyword::Union(Box::new(x))
        }),
        map(keyword("class"), |x| {
            TypeDeclarationKeyword::Class(Box::new(x))
        }),
        map(pair(keyword("interface"), keyword("class")), |x| {
            TypeDeclarationKeyword::InterfaceClass(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn net_type_declaration(s: Span) -> IResult<Span, NetTypeDeclaration> {
    alt((
        net_type_declaration_data_type,
        net_type_declaration_net_type,
    ))(s)
}

#[tracable_parser]
pub(crate) fn net_type_declaration_data_type(s: Span) -> IResult<Span, NetTypeDeclaration> {
    let (s, a) = keyword("nettype")(s)?;
    let (s, b) = data_type(s)?;
    let (s, c) = net_type_identifier(s)?;
    let (s, d) = opt(triple(
        keyword("with"),
        opt(package_scope_or_class_scope),
        tf_identifier,
    ))(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        NetTypeDeclaration::DataType(Box::new(NetTypeDeclarationDataType {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn net_type_declaration_net_type(s: Span) -> IResult<Span, NetTypeDeclaration> {
    let (s, a) = keyword("nettype")(s)?;
    let (s, b) = opt(package_scope_or_class_scope)(s)?;
    let (s, c) = net_type_identifier(s)?;
    let (s, d) = net_type_identifier(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        NetTypeDeclaration::NetType(Box::new(NetTypeDeclarationNetType {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn lifetime(s: Span) -> IResult<Span, Lifetime> {
    alt((
        map(keyword("static"), |x| Lifetime::Static(Box::new(x))),
        map(keyword("automatic"), |x| Lifetime::Automatic(Box::new(x))),
    ))(s)
}
