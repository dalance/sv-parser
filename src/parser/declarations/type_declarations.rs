use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum DataDeclaration<'a> {
    Variable(DataDeclarationVariable<'a>),
    TypeDeclaration(TypeDeclaration<'a>),
    PackageImportDeclaration(PackageImportDeclaration<'a>),
    NetTypeDeclaration(NetTypeDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct DataDeclarationVariable<'a> {
    pub nodes: (
        Option<Const<'a>>,
        Option<Var<'a>>,
        Option<Lifetime<'a>>,
        Option<DataTypeOrImplicit<'a>>,
        ListOfVariableDeclAssignments<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct Const<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug, Node)]
pub struct PackageImportDeclaration<'a> {
    pub nodes: (
        Symbol<'a>,
        List<Symbol<'a>, PackageImportItem<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum PackageImportItem<'a> {
    Identifier(PackageImportItemIdentifier<'a>),
    Asterisk(PackageImportItemAsterisk<'a>),
}

#[derive(Debug, Node)]
pub struct PackageImportItemIdentifier<'a> {
    pub nodes: (PackageIdentifier<'a>, Symbol<'a>, Identifier<'a>),
}

#[derive(Debug, Node)]
pub struct PackageImportItemAsterisk<'a> {
    pub nodes: (PackageIdentifier<'a>, Symbol<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum PackageExportDeclaration<'a> {
    Asterisk(PackageExportDeclarationAsterisk<'a>),
    Item(PackageExportDeclarationItem<'a>),
}

#[derive(Debug, Node)]
pub struct PackageExportDeclarationAsterisk<'a> {
    pub nodes: (Symbol<'a>, Symbol<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct PackageExportDeclarationItem<'a> {
    pub nodes: (
        Symbol<'a>,
        List<Symbol<'a>, PackageImportItem<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct GenvarDeclaration<'a> {
    pub nodes: (Symbol<'a>, ListOfGenvarIdentifiers<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum NetDeclaration<'a> {
    NetType(NetDeclarationNetType<'a>),
    NetTypeIdentifier(NetDeclarationNetTypeIdentifier<'a>),
    Interconnect(NetDeclarationInterconnect<'a>),
}

#[derive(Debug, Node)]
pub struct NetDeclarationNetType<'a> {
    pub nodes: (
        NetType<'a>,
        Option<Strength<'a>>,
        Option<VectorScalar<'a>>,
        Option<DataTypeOrImplicit<'a>>,
        Option<Delay3<'a>>,
        ListOfNetDeclAssignments<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum Strength<'a> {
    Drive(DriveStrength<'a>),
    Charge(ChargeStrength<'a>),
}

#[derive(Debug, Node)]
pub enum VectorScalar<'a> {
    Vectored(Symbol<'a>),
    Scalared(Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct NetDeclarationNetTypeIdentifier<'a> {
    pub nodes: (
        NetTypeIdentifier<'a>,
        Option<DelayControl<'a>>,
        ListOfNetDeclAssignments<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct NetDeclarationInterconnect<'a> {
    pub nodes: (
        Symbol<'a>,
        ImplicitDataType<'a>,
        Option<(Symbol<'a>, DelayValue<'a>)>,
        NetIdentifier<'a>,
        Vec<UnpackedDimension<'a>>,
        Option<(Symbol<'a>, NetIdentifier<'a>, Vec<UnpackedDimension<'a>>)>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum TypeDeclaration<'a> {
    DataType(TypeDeclarationDataType<'a>),
    Interface(TypeDeclarationInterface<'a>),
    Reserved(TypeDeclarationReserved<'a>),
}

#[derive(Debug, Node)]
pub struct TypeDeclarationDataType<'a> {
    pub nodes: (
        Symbol<'a>,
        DataType<'a>,
        TypeIdentifier<'a>,
        Vec<VariableDimension<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct TypeDeclarationInterface<'a> {
    pub nodes: (
        Symbol<'a>,
        InterfaceInstanceIdentifier<'a>,
        ConstantBitSelect<'a>,
        Symbol<'a>,
        TypeIdentifier<'a>,
        TypeIdentifier<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct TypeDeclarationReserved<'a> {
    pub nodes: (
        Symbol<'a>,
        TypeDeclarationKeyword<'a>,
        TypeIdentifier<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum TypeDeclarationKeyword<'a> {
    Enum(Symbol<'a>),
    Struct(Symbol<'a>),
    Union(Symbol<'a>),
    Class(Symbol<'a>),
    InterfaceClass((Symbol<'a>, Symbol<'a>)),
}

#[derive(Debug, Node)]
pub enum NetTypeDeclaration<'a> {
    DataType(NetTypeDeclarationDataType<'a>),
    NetType(NetTypeDeclarationNetType<'a>),
}

#[derive(Debug, Node)]
pub struct NetTypeDeclarationDataType<'a> {
    pub nodes: (
        Symbol<'a>,
        DataType<'a>,
        NetTypeIdentifier<'a>,
        Option<(
            Symbol<'a>,
            Option<PackageScopeOrClassScope<'a>>,
            TfIdentifier<'a>,
        )>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct NetTypeDeclarationNetType<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<PackageScopeOrClassScope<'a>>,
        NetTypeIdentifier<'a>,
        NetTypeIdentifier<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum Lifetime<'a> {
    Static(Symbol<'a>),
    Automatic(Symbol<'a>),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn data_declaration(s: Span) -> IResult<Span, DataDeclaration> {
    alt((
        data_declaration_variable,
        map(type_declaration, |x| DataDeclaration::TypeDeclaration(x)),
        map(package_import_declaration, |x| {
            DataDeclaration::PackageImportDeclaration(x)
        }),
        map(net_type_declaration, |x| {
            DataDeclaration::NetTypeDeclaration(x)
        }),
    ))(s)
}

#[parser(Ambiguous)]
pub fn data_declaration_variable(s: Span) -> IResult<Span, DataDeclaration> {
    let (s, a) = opt(r#const)(s)?;
    let (s, b) = opt(var)(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = ambiguous_opt(data_type_or_implicit)(s)?;
    let (s, e) = list_of_variable_decl_assignments(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        DataDeclaration::Variable(DataDeclarationVariable {
            nodes: (a, b, c, d, e, f),
        }),
    ))
}

#[parser]
pub fn r#const(s: Span) -> IResult<Span, Const> {
    let (s, a) = symbol("const")(s)?;
    Ok((s, Const { nodes: (a,) }))
}

#[parser]
pub fn package_import_declaration(s: Span) -> IResult<Span, PackageImportDeclaration> {
    let (s, a) = symbol("import")(s)?;
    let (s, b) = list(symbol(","), package_import_item)(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((s, PackageImportDeclaration { nodes: (a, b, c) }))
}

#[parser]
pub fn package_import_item(s: Span) -> IResult<Span, PackageImportItem> {
    alt((package_import_item_identifier, package_import_item_asterisk))(s)
}

#[parser]
pub fn package_import_item_identifier(s: Span) -> IResult<Span, PackageImportItem> {
    let (s, a) = package_identifier(s)?;
    let (s, b) = symbol("::")(s)?;
    let (s, c) = identifier(s)?;
    Ok((
        s,
        PackageImportItem::Identifier(PackageImportItemIdentifier { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn package_import_item_asterisk(s: Span) -> IResult<Span, PackageImportItem> {
    let (s, a) = package_identifier(s)?;
    let (s, b) = symbol("::")(s)?;
    let (s, c) = symbol("*")(s)?;
    Ok((
        s,
        PackageImportItem::Asterisk(PackageImportItemAsterisk { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn package_export_declaration(s: Span) -> IResult<Span, PackageExportDeclaration> {
    alt((
        package_export_declaration_asterisk,
        package_export_declaration_item,
    ))(s)
}

#[parser]
pub fn package_export_declaration_asterisk(s: Span) -> IResult<Span, PackageExportDeclaration> {
    let (s, a) = symbol("export")(s)?;
    let (s, b) = symbol("*::*")(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        PackageExportDeclaration::Asterisk(PackageExportDeclarationAsterisk { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn package_export_declaration_item(s: Span) -> IResult<Span, PackageExportDeclaration> {
    let (s, a) = symbol("export")(s)?;
    let (s, b) = list(symbol(","), package_import_item)(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        PackageExportDeclaration::Item(PackageExportDeclarationItem { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn genvar_declaration(s: Span) -> IResult<Span, GenvarDeclaration> {
    let (s, a) = symbol("genvar")(s)?;
    let (s, b) = list_of_genvar_identifiers(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((s, GenvarDeclaration { nodes: (a, b, c) }))
}

#[parser]
pub fn net_declaration(s: Span) -> IResult<Span, NetDeclaration> {
    alt((
        net_declaration_interconnect,
        net_declaration_net_type,
        net_declaration_net_type_identifier,
    ))(s)
}

#[parser(Ambiguous)]
pub fn net_declaration_net_type(s: Span) -> IResult<Span, NetDeclaration> {
    let (s, a) = net_type(s)?;
    let (s, b) = opt(strength)(s)?;
    let (s, c) = opt(vector_scalar)(s)?;
    let (s, d) = ambiguous_opt(data_type_or_implicit)(s)?;
    let (s, e) = opt(delay3)(s)?;
    let (s, f) = list_of_net_decl_assignments(s)?;
    let (s, g) = symbol(";")(s)?;
    Ok((
        s,
        NetDeclaration::NetType(NetDeclarationNetType {
            nodes: (a, b, c, d, e, f, g),
        }),
    ))
}

#[parser]
pub fn strength(s: Span) -> IResult<Span, Strength> {
    alt((
        map(drive_strength, |x| Strength::Drive(x)),
        map(charge_strength, |x| Strength::Charge(x)),
    ))(s)
}

#[parser]
pub fn vector_scalar(s: Span) -> IResult<Span, VectorScalar> {
    alt((
        map(symbol("vectored"), |x| VectorScalar::Vectored(x)),
        map(symbol("scalared"), |x| VectorScalar::Scalared(x)),
    ))(s)
}

#[parser]
pub fn net_declaration_net_type_identifier(s: Span) -> IResult<Span, NetDeclaration> {
    let (s, a) = net_type_identifier(s)?;
    let (s, b) = opt(delay_control)(s)?;
    let (s, c) = list_of_net_decl_assignments(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        NetDeclaration::NetTypeIdentifier(NetDeclarationNetTypeIdentifier {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser]
pub fn net_declaration_interconnect(s: Span) -> IResult<Span, NetDeclaration> {
    let (s, a) = symbol("interconnect")(s)?;
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
        NetDeclaration::Interconnect(NetDeclarationInterconnect {
            nodes: (a, b, c, d, e, f, g),
        }),
    ))
}

#[parser]
pub fn type_declaration(s: Span) -> IResult<Span, TypeDeclaration> {
    alt((
        type_declaration_data_type,
        type_declaration_interface,
        type_declaration_reserved,
    ))(s)
}

#[parser]
pub fn type_declaration_data_type(s: Span) -> IResult<Span, TypeDeclaration> {
    let (s, a) = symbol("typedef")(s)?;
    let (s, b) = data_type(s)?;
    let (s, c) = type_identifier(s)?;
    let (s, d) = many0(variable_dimension)(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        TypeDeclaration::DataType(TypeDeclarationDataType {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser]
pub fn type_declaration_interface(s: Span) -> IResult<Span, TypeDeclaration> {
    let (s, a) = symbol("typedef")(s)?;
    let (s, b) = interface_instance_identifier(s)?;
    let (s, c) = constant_bit_select(s)?;
    let (s, d) = symbol(".")(s)?;
    let (s, e) = type_identifier(s)?;
    let (s, f) = type_identifier(s)?;
    let (s, g) = symbol(";")(s)?;
    Ok((
        s,
        TypeDeclaration::Interface(TypeDeclarationInterface {
            nodes: (a, b, c, d, e, f, g),
        }),
    ))
}

#[parser]
pub fn type_declaration_reserved(s: Span) -> IResult<Span, TypeDeclaration> {
    let (s, a) = symbol("typedef")(s)?;
    let (s, b) = type_declaration_keyword(s)?;
    let (s, c) = type_identifier(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        TypeDeclaration::Reserved(TypeDeclarationReserved {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser]
pub fn type_declaration_keyword(s: Span) -> IResult<Span, TypeDeclarationKeyword> {
    alt((
        map(symbol("enum"), |x| TypeDeclarationKeyword::Enum(x)),
        map(symbol("struct"), |x| TypeDeclarationKeyword::Struct(x)),
        map(symbol("union"), |x| TypeDeclarationKeyword::Union(x)),
        map(symbol("class"), |x| TypeDeclarationKeyword::Class(x)),
        map(pair(symbol("interface"), symbol("class")), |x| {
            TypeDeclarationKeyword::InterfaceClass(x)
        }),
    ))(s)
}

#[parser]
pub fn net_type_declaration(s: Span) -> IResult<Span, NetTypeDeclaration> {
    alt((
        net_type_declaration_data_type,
        net_type_declaration_net_type,
    ))(s)
}

#[parser]
pub fn net_type_declaration_data_type(s: Span) -> IResult<Span, NetTypeDeclaration> {
    let (s, a) = symbol("nettype")(s)?;
    let (s, b) = data_type(s)?;
    let (s, c) = net_type_identifier(s)?;
    let (s, d) = opt(triple(
        symbol("with"),
        opt(package_scope_or_class_scope),
        tf_identifier,
    ))(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        NetTypeDeclaration::DataType(NetTypeDeclarationDataType {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser]
pub fn net_type_declaration_net_type(s: Span) -> IResult<Span, NetTypeDeclaration> {
    let (s, a) = symbol("nettype")(s)?;
    let (s, b) = opt(package_scope_or_class_scope)(s)?;
    let (s, c) = net_type_identifier(s)?;
    let (s, d) = net_type_identifier(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        NetTypeDeclaration::NetType(NetTypeDeclarationNetType {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser]
pub fn lifetime(s: Span) -> IResult<Span, Lifetime> {
    alt((
        map(symbol("static"), |x| Lifetime::Static(x)),
        map(symbol("automatic"), |x| Lifetime::Automatic(x)),
    ))(s)
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_net_type_declaration() {
        parser_test!(
            net_type_declaration,
            "nettype T wT;",
            Ok((_, NetTypeDeclaration::DataType(_)))
        );
        parser_test!(
            net_type_declaration,
            "nettype T wTsum with Tsum;",
            Ok((_, NetTypeDeclaration::DataType(_)))
        );
        parser_test!(
            net_type_declaration,
            "nettype MyBaseT::T narrowTsum with MyBaseT::Tsum;",
            Ok((_, NetTypeDeclaration::DataType(_)))
        );
    }

    #[test]
    fn test_net_declaration() {
        parser_test!(
            net_declaration,
            "trireg (large) logic #(0,0,0) cap1;",
            Ok((_, NetDeclaration::NetType(_)))
        );
        parser_test!(
            net_declaration,
            "wire addressT w1;",
            Ok((_, NetDeclaration::NetType(_)))
        );
        parser_test!(
            net_declaration,
            "wire struct packed { logic ecc; logic [7:0] data; } memsig;",
            Ok((_, NetDeclaration::NetType(_)))
        );
        parser_test!(
            net_declaration,
            "wire w;",
            Ok((_, NetDeclaration::NetType(_)))
        );
        parser_test!(
            net_declaration,
            "wire [15:0] w;",
            Ok((_, NetDeclaration::NetType(_)))
        );
        parser_test!(
            net_declaration,
            "interconnect w1;",
            Ok((_, NetDeclaration::Interconnect(_)))
        );
        parser_test!(
            net_declaration,
            "interconnect [3:0] w2;",
            Ok((_, NetDeclaration::Interconnect(_)))
        );
        parser_test!(
            net_declaration,
            "interconnect [3:0] w3 [1:0];",
            Ok((_, NetDeclaration::Interconnect(_)))
        );
        parser_test!(net_declaration, "interconnect logic [3:0] w4;", Err(_));
        parser_test!(net_declaration, "interconnect #(1,2,3) w5;", Err(_));
    }
}
