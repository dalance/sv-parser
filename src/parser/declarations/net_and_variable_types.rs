use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum CastingType<'a> {
    SimpleType(Box<SimpleType<'a>>),
    ConstantPrimary(Box<ConstantPrimary<'a>>),
    Signing(Box<Signing<'a>>),
    String(Keyword<'a>),
    Const(Keyword<'a>),
}

#[derive(Debug, Node)]
pub enum DataType<'a> {
    Vector(DataTypeVector<'a>),
    Atom(DataTypeAtom<'a>),
    NonIntegerType(NonIntegerType<'a>),
    StructUnion(Box<DataTypeStructUnion<'a>>),
    Enum(DataTypeEnum<'a>),
    String(Keyword<'a>),
    Chandle(Keyword<'a>),
    Virtual(DataTypeVirtual<'a>),
    Type(DataTypeType<'a>),
    ClassType(ClassType<'a>),
    Event(Keyword<'a>),
    PsCovergroupIdentifier(PsCovergroupIdentifier<'a>),
    TypeReference(Box<TypeReference<'a>>),
}

#[derive(Debug, Node)]
pub struct DataTypeVector<'a> {
    pub nodes: (
        IntegerVectorType<'a>,
        Option<Signing<'a>>,
        Vec<PackedDimension<'a>>,
    ),
}

#[derive(Debug, Node)]
pub struct DataTypeAtom<'a> {
    pub nodes: (IntegerAtomType<'a>, Option<Signing<'a>>),
}

#[derive(Debug, Node)]
pub struct DataTypeStructUnion<'a> {
    pub nodes: (
        StructUnion<'a>,
        Option<(Packed<'a>, Option<Signing<'a>>)>,
        Brace<'a, (StructUnionMember<'a>, Vec<StructUnionMember<'a>>)>,
        Vec<PackedDimension<'a>>,
    ),
}

#[derive(Debug, Node)]
pub struct Packed<'a> {
    pub nodes: (Keyword<'a>,),
}

#[derive(Debug, Node)]
pub struct DataTypeEnum<'a> {
    pub nodes: (
        Keyword<'a>,
        Option<EnumBaseType<'a>>,
        Brace<'a, List<Symbol<'a>, EnumNameDeclaration<'a>>>,
        Vec<PackedDimension<'a>>,
    ),
}

#[derive(Debug, Node)]
pub struct DataTypeVirtual<'a> {
    pub nodes: (
        Keyword<'a>,
        Option<Interface<'a>>,
        InterfaceIdentifier<'a>,
        Option<ParameterValueAssignment<'a>>,
        Option<(Symbol<'a>, ModportIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct Interface<'a> {
    pub nodes: (Keyword<'a>,),
}

#[derive(Debug, Node)]
pub struct DataTypeType<'a> {
    pub nodes: (
        Option<PackageScopeOrClassScope<'a>>,
        TypeIdentifier<'a>,
        Vec<PackedDimension<'a>>,
    ),
}

#[derive(Debug, Node)]
pub enum DataTypeOrImplicit<'a> {
    DataType(DataType<'a>),
    ImplicitDataType(ImplicitDataType<'a>),
}

#[derive(Debug, Node)]
pub struct ImplicitDataType<'a> {
    pub nodes: (Option<Signing<'a>>, Vec<PackedDimension<'a>>),
}

#[derive(Debug, Node)]
pub enum EnumBaseType<'a> {
    Atom(EnumBaseTypeAtom<'a>),
    Vector(EnumBaseTypeVector<'a>),
    Type(EnumBaseTypeType<'a>),
}

#[derive(Debug, Node)]
pub struct EnumBaseTypeAtom<'a> {
    pub nodes: (IntegerAtomType<'a>, Option<Signing<'a>>),
}

#[derive(Debug, Node)]
pub struct EnumBaseTypeVector<'a> {
    pub nodes: (
        IntegerVectorType<'a>,
        Option<Signing<'a>>,
        Option<PackedDimension<'a>>,
    ),
}

#[derive(Debug, Node)]
pub struct EnumBaseTypeType<'a> {
    pub nodes: (TypeIdentifier<'a>, Option<PackedDimension<'a>>),
}

#[derive(Debug, Node)]
pub struct EnumNameDeclaration<'a> {
    pub nodes: (
        EnumIdentifier<'a>,
        Option<Bracket<'a, (IntegralNumber<'a>, Option<(Symbol<'a>, IntegralNumber<'a>)>)>>,
        Option<(Symbol<'a>, ConstantExpression<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct ClassScope<'a> {
    pub nodes: (ClassType<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct ClassType<'a> {
    pub nodes: (
        PsClassIdentifier<'a>,
        Option<ParameterValueAssignment<'a>>,
        Vec<(
            Symbol<'a>,
            ClassIdentifier<'a>,
            Option<ParameterValueAssignment<'a>>,
        )>,
    ),
}

#[derive(Debug, Node)]
pub enum IntegerType<'a> {
    IntegerVectorType(IntegerVectorType<'a>),
    IntegerAtomType(IntegerAtomType<'a>),
}

#[derive(Debug, Node)]
pub enum IntegerAtomType<'a> {
    Byte(Keyword<'a>),
    Shortint(Keyword<'a>),
    Int(Keyword<'a>),
    Longint(Keyword<'a>),
    Integer(Keyword<'a>),
    Time(Keyword<'a>),
}

#[derive(Debug, Node)]
pub enum IntegerVectorType<'a> {
    Bit(Keyword<'a>),
    Logic(Keyword<'a>),
    Reg(Keyword<'a>),
}

#[derive(Debug, Node)]
pub enum NonIntegerType<'a> {
    Shortreal(Keyword<'a>),
    Real(Keyword<'a>),
    Realtime(Keyword<'a>),
}

#[derive(Debug, Node)]
pub enum NetType<'a> {
    Supply0(Keyword<'a>),
    Supply1(Keyword<'a>),
    Tri(Keyword<'a>),
    Triand(Keyword<'a>),
    Trior(Keyword<'a>),
    Trireg(Keyword<'a>),
    Tri0(Keyword<'a>),
    Tri1(Keyword<'a>),
    Uwire(Keyword<'a>),
    Wire(Keyword<'a>),
    Wand(Keyword<'a>),
    Wor(Keyword<'a>),
}

#[derive(Debug, Node)]
pub enum NetPortType<'a> {
    DataType(NetPortTypeDataType<'a>),
    NetTypeIdentifier(NetTypeIdentifier<'a>),
    Interconnect(NetPortTypeInterconnect<'a>),
}

#[derive(Debug, Node)]
pub struct NetPortTypeDataType<'a> {
    pub nodes: (Option<NetType<'a>>, DataTypeOrImplicit<'a>),
}

#[derive(Debug, Node)]
pub struct NetPortTypeInterconnect<'a> {
    pub nodes: (Keyword<'a>, ImplicitDataType<'a>),
}

#[derive(Debug, Node)]
pub struct VariablePortType<'a> {
    pub nodes: (VarDataType<'a>,),
}

#[derive(Debug, Node)]
pub enum VarDataType<'a> {
    DataType(DataType<'a>),
    Var(VarDataTypeVar<'a>),
}

#[derive(Debug, Node)]
pub struct VarDataTypeVar<'a> {
    pub nodes: (Keyword<'a>, DataTypeOrImplicit<'a>),
}

#[derive(Debug, Node)]
pub enum Signing<'a> {
    Signed(Keyword<'a>),
    Unsigned(Keyword<'a>),
}

#[derive(Debug, Node)]
pub enum SimpleType<'a> {
    IntegerType(IntegerType<'a>),
    NonIntegerType(NonIntegerType<'a>),
    PsTypeIdentifier(PsTypeIdentifier<'a>),
    PsParameterIdentifier(PsParameterIdentifier<'a>),
}

#[derive(Debug, Node)]
pub struct StructUnionMember<'a> {
    pub nodes: (
        Vec<AttributeInstance<'a>>,
        Option<RandomQualifier<'a>>,
        DataTypeOrVoid<'a>,
        ListOfVariableDeclAssignments<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum DataTypeOrVoid<'a> {
    DataType(DataType<'a>),
    Void(Keyword<'a>),
}

#[derive(Debug, Node)]
pub enum StructUnion<'a> {
    Struct(Keyword<'a>),
    Union(Keyword<'a>),
    UnionTagged((Keyword<'a>, Keyword<'a>)),
}

#[derive(Debug, Node)]
pub enum TypeReference<'a> {
    Expression(TypeReferenceExpression<'a>),
    DataType(TypeReferenceDataType<'a>),
}

#[derive(Debug, Node)]
pub struct TypeReferenceExpression<'a> {
    pub nodes: (Keyword<'a>, Paren<'a, Expression<'a>>),
}

#[derive(Debug, Node)]
pub struct TypeReferenceDataType<'a> {
    pub nodes: (Keyword<'a>, Paren<'a, DataType<'a>>),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn casting_type(s: Span) -> IResult<Span, CastingType> {
    alt((
        map(simple_type, |x| CastingType::SimpleType(Box::new(x))),
        map(signing, |x| CastingType::Signing(Box::new(x))),
        map(keyword("string"), |x| CastingType::String(x)),
        map(keyword("const"), |x| CastingType::Const(x)),
        map(constant_primary, |x| {
            CastingType::ConstantPrimary(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn data_type(s: Span) -> IResult<Span, DataType> {
    alt((
        data_type_vector,
        data_type_atom,
        map(non_integer_type, |x| DataType::NonIntegerType(x)),
        data_type_struct_union,
        data_type_enum,
        map(keyword("string"), |x| DataType::String(x)),
        map(keyword("chandle"), |x| DataType::Chandle(x)),
        data_type_virtual,
        data_type_type,
        map(class_type, |x| DataType::ClassType(x)),
        map(keyword("event"), |x| DataType::Chandle(x)),
        map(ps_covergroup_identifier, |x| {
            DataType::PsCovergroupIdentifier(x)
        }),
        map(type_reference, |x| DataType::TypeReference(Box::new(x))),
    ))(s)
}

#[parser]
pub fn data_type_vector(s: Span) -> IResult<Span, DataType> {
    let (s, a) = integer_vector_type(s)?;
    let (s, b) = opt(signing)(s)?;
    let (s, c) = many0(packed_dimension)(s)?;
    Ok((s, DataType::Vector(DataTypeVector { nodes: (a, b, c) })))
}

#[parser]
pub fn data_type_atom(s: Span) -> IResult<Span, DataType> {
    let (s, a) = integer_atom_type(s)?;
    let (s, b) = opt(signing)(s)?;
    Ok((s, DataType::Atom(DataTypeAtom { nodes: (a, b) })))
}

#[parser]
pub fn data_type_struct_union(s: Span) -> IResult<Span, DataType> {
    let (s, a) = struct_union(s)?;
    let (s, b) = opt(pair(packed, opt(signing)))(s)?;
    let (s, c) = brace(pair(struct_union_member, many0(struct_union_member)))(s)?;
    let (s, d) = many0(packed_dimension)(s)?;
    Ok((
        s,
        DataType::StructUnion(Box::new(DataTypeStructUnion {
            nodes: (a, b, c, d),
        })),
    ))
}

#[parser]
pub fn packed(s: Span) -> IResult<Span, Packed> {
    let (s, a) = keyword("packed")(s)?;
    Ok((s, Packed { nodes: (a,) }))
}

#[parser]
pub fn data_type_enum(s: Span) -> IResult<Span, DataType> {
    let (s, a) = keyword("enum")(s)?;
    let (s, b) = opt(enum_base_type)(s)?;
    let (s, c) = brace(list(symbol(","), enum_name_declaration))(s)?;
    let (s, d) = many0(packed_dimension)(s)?;
    Ok((
        s,
        DataType::Enum(DataTypeEnum {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser]
pub fn data_type_virtual(s: Span) -> IResult<Span, DataType> {
    let (s, a) = keyword("virtual")(s)?;
    let (s, b) = opt(interface)(s)?;
    let (s, c) = interface_identifier(s)?;
    let (s, d) = opt(parameter_value_assignment)(s)?;
    let (s, e) = opt(pair(symbol("."), modport_identifier))(s)?;
    Ok((
        s,
        DataType::Virtual(DataTypeVirtual {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser]
pub fn interface(s: Span) -> IResult<Span, Interface> {
    let (s, a) = keyword("interface")(s)?;
    Ok((s, Interface { nodes: (a,) }))
}

#[parser]
pub fn data_type_type(s: Span) -> IResult<Span, DataType> {
    let (s, a) = opt(package_scope_or_class_scope)(s)?;
    let (s, b) = type_identifier(s)?;
    let (s, c) = many0(packed_dimension)(s)?;
    Ok((s, DataType::Type(DataTypeType { nodes: (a, b, c) })))
}

#[parser]
pub fn data_type_or_implicit(s: Span) -> IResult<Span, DataTypeOrImplicit> {
    alt((
        map(data_type, |x| DataTypeOrImplicit::DataType(x)),
        map(implicit_data_type, |x| {
            DataTypeOrImplicit::ImplicitDataType(x)
        }),
    ))(s)
}

#[parser]
pub fn implicit_data_type(s: Span) -> IResult<Span, ImplicitDataType> {
    let (s, a) = opt(signing)(s)?;
    let (s, b) = many0(packed_dimension)(s)?;
    Ok((s, ImplicitDataType { nodes: (a, b) }))
}

#[parser]
pub fn enum_base_type(s: Span) -> IResult<Span, EnumBaseType> {
    alt((
        enum_base_type_atom,
        enum_base_type_vector,
        enum_base_type_type,
    ))(s)
}

#[parser]
pub fn enum_base_type_atom(s: Span) -> IResult<Span, EnumBaseType> {
    let (s, a) = integer_atom_type(s)?;
    let (s, b) = opt(signing)(s)?;
    Ok((s, EnumBaseType::Atom(EnumBaseTypeAtom { nodes: (a, b) })))
}

#[parser]
pub fn enum_base_type_vector(s: Span) -> IResult<Span, EnumBaseType> {
    let (s, a) = integer_vector_type(s)?;
    let (s, b) = opt(signing)(s)?;
    let (s, c) = opt(packed_dimension)(s)?;
    Ok((
        s,
        EnumBaseType::Vector(EnumBaseTypeVector { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn enum_base_type_type(s: Span) -> IResult<Span, EnumBaseType> {
    let (s, a) = type_identifier(s)?;
    let (s, b) = opt(packed_dimension)(s)?;
    Ok((s, EnumBaseType::Type(EnumBaseTypeType { nodes: (a, b) })))
}

#[parser]
pub fn enum_name_declaration(s: Span) -> IResult<Span, EnumNameDeclaration> {
    let (s, a) = enum_identifier(s)?;
    let (s, b) = opt(bracket(pair(
        integral_number,
        opt(pair(symbol(":"), integral_number)),
    )))(s)?;
    let (s, c) = opt(pair(symbol("="), constant_expression))(s)?;
    Ok((s, EnumNameDeclaration { nodes: (a, b, c) }))
}

#[parser]
pub fn class_scope(s: Span) -> IResult<Span, ClassScope> {
    let (s, a) = class_type(s)?;
    let (s, b) = symbol("::")(s)?;
    Ok((s, ClassScope { nodes: (a, b) }))
}

#[parser]
pub fn class_type(s: Span) -> IResult<Span, ClassType> {
    let (s, a) = ps_class_identifier(s)?;
    let (s, b) = opt(parameter_value_assignment)(s)?;
    let (s, c) = many0(triple(
        symbol("::"),
        class_identifier,
        opt(parameter_value_assignment),
    ))(s)?;
    Ok((s, ClassType { nodes: (a, b, c) }))
}

#[parser]
pub fn integer_type(s: Span) -> IResult<Span, IntegerType> {
    alt((
        map(integer_vector_type, |x| IntegerType::IntegerVectorType(x)),
        map(integer_atom_type, |x| IntegerType::IntegerAtomType(x)),
    ))(s)
}

#[parser]
pub fn integer_atom_type(s: Span) -> IResult<Span, IntegerAtomType> {
    alt((
        map(keyword("byte"), |x| IntegerAtomType::Byte(x)),
        map(keyword("shortint"), |x| IntegerAtomType::Shortint(x)),
        map(keyword("int"), |x| IntegerAtomType::Int(x)),
        map(keyword("longint"), |x| IntegerAtomType::Longint(x)),
        map(keyword("integer"), |x| IntegerAtomType::Integer(x)),
        map(keyword("time"), |x| IntegerAtomType::Time(x)),
    ))(s)
}

#[parser]
pub fn integer_vector_type(s: Span) -> IResult<Span, IntegerVectorType> {
    alt((
        map(keyword("bit"), |x| IntegerVectorType::Bit(x)),
        map(keyword("logic"), |x| IntegerVectorType::Logic(x)),
        map(keyword("reg"), |x| IntegerVectorType::Reg(x)),
    ))(s)
}

#[parser]
pub fn non_integer_type(s: Span) -> IResult<Span, NonIntegerType> {
    alt((
        map(keyword("shortreal"), |x| NonIntegerType::Shortreal(x)),
        map(keyword("realtime"), |x| NonIntegerType::Realtime(x)),
        map(keyword("real"), |x| NonIntegerType::Real(x)),
    ))(s)
}

#[parser]
pub fn net_type(s: Span) -> IResult<Span, NetType> {
    alt((
        map(keyword("supply0"), |x| NetType::Supply0(x)),
        map(keyword("supply1"), |x| NetType::Supply1(x)),
        map(keyword("triand"), |x| NetType::Triand(x)),
        map(keyword("trior"), |x| NetType::Trior(x)),
        map(keyword("trireg"), |x| NetType::Trireg(x)),
        map(keyword("tri0"), |x| NetType::Tri0(x)),
        map(keyword("tri1"), |x| NetType::Tri1(x)),
        map(keyword("tri"), |x| NetType::Tri(x)),
        map(keyword("uwire"), |x| NetType::Uwire(x)),
        map(keyword("wire"), |x| NetType::Wire(x)),
        map(keyword("wand"), |x| NetType::Wand(x)),
        map(keyword("wor"), |x| NetType::Wor(x)),
    ))(s)
}

#[parser]
pub fn net_port_type(s: Span) -> IResult<Span, NetPortType> {
    alt((
        net_port_type_data_type,
        map(net_type_identifier, |x| NetPortType::NetTypeIdentifier(x)),
        net_port_type_interconnect,
    ))(s)
}

#[parser]
pub fn net_port_type_data_type(s: Span) -> IResult<Span, NetPortType> {
    let (s, a) = opt(net_type)(s)?;
    let (s, b) = data_type_or_implicit(s)?;
    Ok((
        s,
        NetPortType::DataType(NetPortTypeDataType { nodes: (a, b) }),
    ))
}

#[parser]
pub fn net_port_type_interconnect(s: Span) -> IResult<Span, NetPortType> {
    let (s, a) = keyword("interconnect")(s)?;
    let (s, b) = implicit_data_type(s)?;
    Ok((
        s,
        NetPortType::Interconnect(NetPortTypeInterconnect { nodes: (a, b) }),
    ))
}

#[parser]
pub fn variable_port_type(s: Span) -> IResult<Span, VariablePortType> {
    let (s, a) = var_data_type(s)?;
    Ok((s, VariablePortType { nodes: (a,) }))
}

#[parser]
pub fn var_data_type(s: Span) -> IResult<Span, VarDataType> {
    alt((
        map(data_type, |x| VarDataType::DataType(x)),
        var_data_type_var,
    ))(s)
}

#[parser]
pub fn var_data_type_var(s: Span) -> IResult<Span, VarDataType> {
    let (s, a) = keyword("var")(s)?;
    let (s, b) = data_type_or_implicit(s)?;
    Ok((s, VarDataType::Var(VarDataTypeVar { nodes: (a, b) })))
}

#[parser]
pub fn signing(s: Span) -> IResult<Span, Signing> {
    alt((
        map(keyword("signed"), |x| Signing::Signed(x)),
        map(keyword("unsigned"), |x| Signing::Unsigned(x)),
    ))(s)
}

#[parser]
pub fn simple_type(s: Span) -> IResult<Span, SimpleType> {
    alt((
        map(integer_type, |x| SimpleType::IntegerType(x)),
        map(non_integer_type, |x| SimpleType::NonIntegerType(x)),
        map(ps_type_identifier, |x| SimpleType::PsTypeIdentifier(x)),
        map(ps_parameter_identifier, |x| {
            SimpleType::PsParameterIdentifier(x)
        }),
    ))(s)
}

#[parser]
pub fn struct_union_member(s: Span) -> IResult<Span, StructUnionMember> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = opt(random_qualifier)(s)?;
    let (s, c) = data_type_or_void(s)?;
    let (s, d) = list_of_variable_decl_assignments(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        StructUnionMember {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[parser]
pub fn data_type_or_void(s: Span) -> IResult<Span, DataTypeOrVoid> {
    alt((
        map(data_type, |x| DataTypeOrVoid::DataType(x)),
        map(keyword("void"), |x| DataTypeOrVoid::Void(x)),
    ))(s)
}

#[parser]
pub fn struct_union(s: Span) -> IResult<Span, StructUnion> {
    alt((
        map(keyword("struct"), |x| StructUnion::Struct(x)),
        map(pair(keyword("union"), keyword("tagged")), |x| {
            StructUnion::UnionTagged(x)
        }),
        map(keyword("union"), |x| StructUnion::Union(x)),
    ))(s)
}

#[parser]
pub fn type_reference(s: Span) -> IResult<Span, TypeReference> {
    alt((type_reference_expression, type_reference_data_type))(s)
}

#[parser]
pub fn type_reference_expression(s: Span) -> IResult<Span, TypeReference> {
    let (s, a) = keyword("type")(s)?;
    let (s, b) = paren(expression)(s)?;
    Ok((
        s,
        TypeReference::Expression(TypeReferenceExpression { nodes: (a, b) }),
    ))
}

#[parser]
pub fn type_reference_data_type(s: Span) -> IResult<Span, TypeReference> {
    let (s, a) = keyword("type")(s)?;
    let (s, b) = paren(data_type)(s)?;
    Ok((
        s,
        TypeReference::DataType(TypeReferenceDataType { nodes: (a, b) }),
    ))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_data_type() {
        parser_test!(
            data_type,
            "struct { bit [7:0] opcode; bit [23:0] addr; }",
            Ok((_, DataType::StructUnion(_)))
        );
        parser_test!(
            data_type,
            "struct packed signed { int a; shortint b; byte c; bit [7:0] d; }",
            Ok((_, DataType::StructUnion(_)))
        );
        parser_test!(
            data_type,
            "union { int i; shortreal f; } ",
            Ok((_, DataType::StructUnion(_)))
        );
        parser_test!(
            data_type,
            "struct { bit isfloat; union { int i; shortreal f; } n; }",
            Ok((_, DataType::StructUnion(_)))
        );
        parser_test!(
            data_type,
            "union packed { s_atmcell acell; bit [423:0] bit_slice; bit [52:0][7:0] byte_slice; }",
            Ok((_, DataType::StructUnion(_)))
        );
        parser_test!(
            data_type,
            "union tagged { void Invalid; int Valid; }",
            Ok((_, DataType::StructUnion(_)))
        );
    }
}
