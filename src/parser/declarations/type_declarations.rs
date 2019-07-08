use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum DataDeclaration<'a> {
    Variable(DataDeclarationVariable<'a>),
    Type(TypeDeclaration<'a>),
    PackageImport(PackageImportDeclaration<'a>),
    NetType(NetTypeDeclaration<'a>),
}

#[derive(Debug)]
pub struct DataDeclarationVariable<'a> {
    pub nodes: (
        Option<Const>,
        Option<Var>,
        Option<Lifetime>,
        DataTypeOrImplicit<'a>,
        ListOfVariableDeclAssignments<'a>,
    ),
}

#[derive(Debug)]
pub struct Const {}

#[derive(Debug)]
pub struct Var {}

#[derive(Debug)]
pub struct PackageImportDeclaration<'a> {
    pub nodes: (Vec<PackageImportItem<'a>>,),
}

#[derive(Debug)]
pub enum PackageImportItem<'a> {
    Identifier(PackageImportItemIdentifier<'a>),
    Asterisk(PackageImportItemAsterisk<'a>),
}

#[derive(Debug)]
pub struct PackageImportItemIdentifier<'a> {
    pub nodes: (PackageIdentifier<'a>, Identifier<'a>),
}

#[derive(Debug)]
pub struct PackageImportItemAsterisk<'a> {
    pub nodes: (PackageIdentifier<'a>,),
}

#[derive(Debug)]
pub enum PackageExportDeclaration<'a> {
    Asterisk,
    Item(Vec<PackageImportItem<'a>>),
}

#[derive(Debug)]
pub struct GenvarDeclaration<'a> {
    pub nodes: (ListOfGenvarIdentifiers<'a>,),
}

#[derive(Debug)]
pub enum NetDeclaration<'a> {
    NetType(NetDeclarationNetType<'a>),
    NetTypeIdentifier(NetDeclarationNetTypeIdentifier<'a>),
    Interconnect(NetDeclarationInterconnect<'a>),
}

#[derive(Debug)]
pub struct NetDeclarationNetType<'a> {
    pub nodes: (
        NetType,
        Option<Strength>,
        Option<VectorScalar>,
        DataTypeOrImplicit<'a>,
        Option<Delay3<'a>>,
        ListOfNetDeclAssignments<'a>,
    ),
}

#[derive(Debug)]
pub enum Strength {
    Drive(DriveStrength),
    Charge(ChargeStrength),
}

#[derive(Debug)]
pub enum VectorScalar {
    Vectored,
    Scalared,
}

#[derive(Debug)]
pub struct NetDeclarationNetTypeIdentifier<'a> {
    pub nodes: (
        NetTypeIdentifier<'a>,
        Option<DelayControl<'a>>,
        ListOfNetDeclAssignments<'a>,
    ),
}

#[derive(Debug)]
pub struct NetDeclarationInterconnect<'a> {
    pub nodes: (
        ImplicitDataType<'a>,
        Option<DelayValue<'a>>,
        NetIdentifier<'a>,
        Vec<UnpackedDimension<'a>>,
        Option<(NetIdentifier<'a>, Vec<UnpackedDimension<'a>>)>,
    ),
}

#[derive(Debug)]
pub enum TypeDeclaration<'a> {
    DataType(TypeDeclarationDataType<'a>),
    Interface(TypeDeclarationInterface<'a>),
    Reserved(TypeDeclarationReserved<'a>),
}

#[derive(Debug)]
pub struct TypeDeclarationDataType<'a> {
    pub nodes: (DataType<'a>, TypeIdentifier<'a>, Vec<VariableDimension<'a>>),
}

#[derive(Debug)]
pub struct TypeDeclarationInterface<'a> {
    pub nodes: (
        InterfaceInstanceIdentifier<'a>,
        ConstantBitSelect<'a>,
        TypeIdentifier<'a>,
        TypeIdentifier<'a>,
    ),
}

#[derive(Debug)]
pub struct TypeDeclarationReserved<'a> {
    pub nodes: (TypeDeclarationKeyword, TypeIdentifier<'a>),
}

#[derive(Debug)]
pub enum TypeDeclarationKeyword {
    Enum,
    Struct,
    Union,
    Class,
    InterfaceClass,
}

#[derive(Debug)]
pub enum NetTypeDeclaration<'a> {
    DataType(NetTypeDeclarationDataType<'a>),
    NetType(NetTypeDeclarationNetType<'a>),
}

#[derive(Debug)]
pub struct NetTypeDeclarationDataType<'a> {
    pub nodes: (
        DataType<'a>,
        NetTypeIdentifier<'a>,
        Option<(Option<PackageScopeOrClassScope<'a>>, TfIdentifier<'a>)>,
    ),
}

#[derive(Debug)]
pub struct NetTypeDeclarationNetType<'a> {
    pub nodes: (
        Option<PackageScopeOrClassScope<'a>>,
        NetTypeIdentifier<'a>,
        NetTypeIdentifier<'a>,
    ),
}

#[derive(Debug)]
pub enum Lifetime {
    Static,
    Automatic,
}

// -----------------------------------------------------------------------------

pub fn data_declaration(s: &str) -> IResult<&str, DataDeclaration> {
    alt((
        data_declaration_variable,
        map(type_declaration, |x| DataDeclaration::Type(x)),
        map(package_import_declaration, |x| {
            DataDeclaration::PackageImport(x)
        }),
        map(net_type_declaration, |x| DataDeclaration::NetType(x)),
    ))(s)
}

pub fn data_declaration_variable(s: &str) -> IResult<&str, DataDeclaration> {
    let (s, x) = opt(symbol("const"))(s)?;
    let (s, y) = opt(symbol("var"))(s)?;
    let (s, z) = opt(lifetime)(s)?;
    let (s, v) = data_type_or_implicit(s)?;
    let (s, w) = list_of_variable_decl_assignments(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((
        s,
        DataDeclaration::Variable(DataDeclarationVariable {
            nodes: (x.map(|_| Const {}), y.map(|_| Var {}), z, v, w),
        }),
    ))
}

pub fn package_import_declaration(s: &str) -> IResult<&str, PackageImportDeclaration> {
    let (s, _) = symbol("import")(s)?;
    let (s, x) = separated_nonempty_list(symbol(","), package_import_item)(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, PackageImportDeclaration { nodes: (x,) }))
}

pub fn package_import_item(s: &str) -> IResult<&str, PackageImportItem> {
    alt((package_import_item_identifier, package_import_item_asterisk))(s)
}

pub fn package_import_item_identifier(s: &str) -> IResult<&str, PackageImportItem> {
    let (s, x) = package_identifier(s)?;
    let (s, _) = symbol("::")(s)?;
    let (s, y) = identifier(s)?;
    Ok((
        s,
        PackageImportItem::Identifier(PackageImportItemIdentifier { nodes: (x, y) }),
    ))
}

pub fn package_import_item_asterisk(s: &str) -> IResult<&str, PackageImportItem> {
    let (s, x) = package_identifier(s)?;
    let (s, _) = symbol("::")(s)?;
    let (s, _) = symbol("*")(s)?;
    Ok((
        s,
        PackageImportItem::Asterisk(PackageImportItemAsterisk { nodes: (x,) }),
    ))
}

pub fn package_export_declaration(s: &str) -> IResult<&str, PackageExportDeclaration> {
    alt((
        package_export_declaration_asterisk,
        package_export_declaration_item,
    ))(s)
}

pub fn package_export_declaration_asterisk(s: &str) -> IResult<&str, PackageExportDeclaration> {
    let (s, _) = symbol("export")(s)?;
    let (s, _) = symbol("*::*")(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, PackageExportDeclaration::Asterisk))
}

pub fn package_export_declaration_item(s: &str) -> IResult<&str, PackageExportDeclaration> {
    let (s, _) = symbol("export")(s)?;
    let (s, x) = separated_nonempty_list(symbol(","), package_import_item)(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, PackageExportDeclaration::Item(x)))
}

pub fn genvar_declaration(s: &str) -> IResult<&str, GenvarDeclaration> {
    let (s, _) = symbol("genvar")(s)?;
    let (s, x) = list_of_genvar_identifiers(s)?;
    Ok((s, GenvarDeclaration { nodes: (x,) }))
}

pub fn net_declaration(s: &str) -> IResult<&str, NetDeclaration> {
    alt((
        net_declaration_net_type,
        net_declaration_net_type_identifier,
        net_declaration_interconnect,
    ))(s)
}

pub fn net_declaration_net_type(s: &str) -> IResult<&str, NetDeclaration> {
    let (s, x) = net_type(s)?;
    let (s, y) = opt(strength)(s)?;
    let (s, z) = opt(vector_scalar)(s)?;
    let (s, v) = data_type_or_implicit(s)?;
    let (s, w) = opt(delay3)(s)?;
    let (s, u) = list_of_net_decl_assignments(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((
        s,
        NetDeclaration::NetType(NetDeclarationNetType {
            nodes: (x, y, z, v, w, u),
        }),
    ))
}

pub fn strength(s: &str) -> IResult<&str, Strength> {
    alt((
        map(drive_strength, |x| Strength::Drive(x)),
        map(charge_strength, |x| Strength::Charge(x)),
    ))(s)
}

pub fn vector_scalar(s: &str) -> IResult<&str, VectorScalar> {
    alt((
        map(symbol("vectored"), |_| VectorScalar::Vectored),
        map(symbol("scalared"), |_| VectorScalar::Scalared),
    ))(s)
}

pub fn net_declaration_net_type_identifier(s: &str) -> IResult<&str, NetDeclaration> {
    let (s, x) = net_type_identifier(s)?;
    let (s, y) = opt(delay_control)(s)?;
    let (s, z) = list_of_net_decl_assignments(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((
        s,
        NetDeclaration::NetTypeIdentifier(NetDeclarationNetTypeIdentifier { nodes: (x, y, z) }),
    ))
}

pub fn net_declaration_interconnect(s: &str) -> IResult<&str, NetDeclaration> {
    let (s, _) = symbol("interconnect")(s)?;
    let (s, x) = implicit_data_type(s)?;
    let (s, y) = opt(preceded(symbol("#"), delay_value))(s)?;
    let (s, z) = net_identifier(s)?;
    let (s, v) = many0(unpacked_dimension)(s)?;
    let (s, w) = opt(preceded(
        symbol(","),
        pair(net_identifier, many0(unpacked_dimension)),
    ))(s)?;
    Ok((
        s,
        NetDeclaration::Interconnect(NetDeclarationInterconnect {
            nodes: (x, y, z, v, w),
        }),
    ))
}

pub fn type_declaration(s: &str) -> IResult<&str, TypeDeclaration> {
    alt((
        type_declaration_data_type,
        type_declaration_interface,
        type_declaration_reserved,
    ))(s)
}

pub fn type_declaration_data_type(s: &str) -> IResult<&str, TypeDeclaration> {
    let (s, _) = symbol("typedef")(s)?;
    let (s, x) = data_type(s)?;
    let (s, y) = type_identifier(s)?;
    let (s, z) = many0(variable_dimension)(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((
        s,
        TypeDeclaration::DataType(TypeDeclarationDataType { nodes: (x, y, z) }),
    ))
}

pub fn type_declaration_interface(s: &str) -> IResult<&str, TypeDeclaration> {
    let (s, _) = symbol("typedef")(s)?;
    let (s, x) = interface_instance_identifier(s)?;
    let (s, y) = constant_bit_select(s)?;
    let (s, _) = symbol(".")(s)?;
    let (s, z) = type_identifier(s)?;
    let (s, v) = type_identifier(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((
        s,
        TypeDeclaration::Interface(TypeDeclarationInterface {
            nodes: (x, y, z, v),
        }),
    ))
}

pub fn type_declaration_reserved(s: &str) -> IResult<&str, TypeDeclaration> {
    let (s, _) = symbol("typedef")(s)?;
    let (s, x) = type_declaration_keyword(s)?;
    let (s, y) = type_identifier(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((
        s,
        TypeDeclaration::Reserved(TypeDeclarationReserved { nodes: (x, y) }),
    ))
}

pub fn type_declaration_keyword(s: &str) -> IResult<&str, TypeDeclarationKeyword> {
    alt((
        map(symbol("enum"), |_| TypeDeclarationKeyword::Enum),
        map(symbol("struct"), |_| TypeDeclarationKeyword::Struct),
        map(symbol("union"), |_| TypeDeclarationKeyword::Union),
        map(symbol("class"), |_| TypeDeclarationKeyword::Class),
        map(pair(symbol("interface"), symbol("class")), |_| {
            TypeDeclarationKeyword::InterfaceClass
        }),
    ))(s)
}

pub fn net_type_declaration(s: &str) -> IResult<&str, NetTypeDeclaration> {
    alt((
        net_type_declaration_data_type,
        net_type_declaration_net_type,
    ))(s)
}

pub fn net_type_declaration_data_type(s: &str) -> IResult<&str, NetTypeDeclaration> {
    let (s, _) = symbol("nettype")(s)?;
    let (s, x) = data_type(s)?;
    let (s, y) = net_type_identifier(s)?;
    let (s, z) = opt(preceded(
        symbol("with"),
        pair(opt(package_scope_or_class_scope), tf_identifier),
    ))(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((
        s,
        NetTypeDeclaration::DataType(NetTypeDeclarationDataType { nodes: (x, y, z) }),
    ))
}

pub fn net_type_declaration_net_type(s: &str) -> IResult<&str, NetTypeDeclaration> {
    let (s, _) = symbol("nettype")(s)?;
    let (s, x) = opt(package_scope_or_class_scope)(s)?;
    let (s, y) = net_type_identifier(s)?;
    let (s, z) = net_type_identifier(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((
        s,
        NetTypeDeclaration::NetType(NetTypeDeclarationNetType { nodes: (x, y, z) }),
    ))
}

pub fn lifetime(s: &str) -> IResult<&str, Lifetime> {
    alt((
        map(symbol("static"), |_| Lifetime::Static),
        map(symbol("automatic"), |_| Lifetime::Automatic),
    ))(s)
}
