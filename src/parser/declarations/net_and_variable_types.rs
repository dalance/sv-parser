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
    String(Symbol<'a>),
    Const(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum DataType<'a> {
    Vector(DataTypeVector<'a>),
    Atom(DataTypeAtom<'a>),
    NonIntegerType(NonIntegerType<'a>),
    Union(Box<DataTypeUnion<'a>>),
    Enum(DataTypeEnum<'a>),
    String(Symbol<'a>),
    Chandle(Symbol<'a>),
    Virtual(DataTypeVirtual<'a>),
    Type(DataTypeType<'a>),
    ClassType(ClassType<'a>),
    Event(Symbol<'a>),
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
pub struct DataTypeUnion<'a> {
    pub nodes: (
        StructUnion<'a>,
        Option<(Packed<'a>, Option<Signing<'a>>)>,
        Brace<'a, (StructUnionMember<'a>, Vec<StructUnionMember<'a>>)>,
        Vec<PackedDimension<'a>>,
    ),
}

#[derive(Debug, Node)]
pub struct Packed<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug, Node)]
pub struct DataTypeEnum<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<EnumBaseType<'a>>,
        Brace<'a, List<Symbol<'a>, EnumNameDeclaration<'a>>>,
        Vec<PackedDimension<'a>>,
    ),
}

#[derive(Debug, Node)]
pub struct DataTypeVirtual<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<Interface<'a>>,
        InterfaceIdentifier<'a>,
        Option<ParameterValueAssignment<'a>>,
        Option<(Symbol<'a>, ModportIdentifier<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct Interface<'a> {
    pub nodes: (Symbol<'a>,),
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
    Byte(Symbol<'a>),
    Shortint(Symbol<'a>),
    Int(Symbol<'a>),
    Longint(Symbol<'a>),
    Integer(Symbol<'a>),
    Time(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum IntegerVectorType<'a> {
    Bit(Symbol<'a>),
    Logic(Symbol<'a>),
    Reg(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum NonIntegerType<'a> {
    Shortreal(Symbol<'a>),
    Real(Symbol<'a>),
    Realtime(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum NetType<'a> {
    Supply0(Symbol<'a>),
    Supply1(Symbol<'a>),
    Tri(Symbol<'a>),
    Triand(Symbol<'a>),
    Trior(Symbol<'a>),
    Trireg(Symbol<'a>),
    Tri0(Symbol<'a>),
    Tri1(Symbol<'a>),
    Uwire(Symbol<'a>),
    Wire(Symbol<'a>),
    Wand(Symbol<'a>),
    Wor(Symbol<'a>),
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
    pub nodes: (Symbol<'a>, ImplicitDataType<'a>),
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
    pub nodes: (Symbol<'a>, DataTypeOrImplicit<'a>),
}

#[derive(Debug, Node)]
pub enum Signing<'a> {
    Signed(Symbol<'a>),
    Unsigned(Symbol<'a>),
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
    Void(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum StructUnion<'a> {
    Struct(Symbol<'a>),
    Union(Symbol<'a>),
    UnionTagged((Symbol<'a>, Symbol<'a>)),
}

#[derive(Debug, Node)]
pub enum TypeReference<'a> {
    Expression(TypeReferenceExpression<'a>),
    DataType(TypeReferenceDataType<'a>),
}

#[derive(Debug, Node)]
pub struct TypeReferenceExpression<'a> {
    pub nodes: (Symbol<'a>, Paren<'a, Expression<'a>>),
}

#[derive(Debug, Node)]
pub struct TypeReferenceDataType<'a> {
    pub nodes: (Symbol<'a>, Paren<'a, DataType<'a>>),
}

// -----------------------------------------------------------------------------

#[trace]
pub fn casting_type(s: Span) -> IResult<Span, CastingType> {
    alt((
        map(simple_type, |x| CastingType::SimpleType(Box::new(x))),
        map(constant_primary, |x| {
            CastingType::ConstantPrimary(Box::new(x))
        }),
        map(signing, |x| CastingType::Signing(Box::new(x))),
        map(symbol("string"), |x| CastingType::String(x)),
        map(symbol("const"), |x| CastingType::Const(x)),
    ))(s)
}

#[trace]
pub fn data_type(s: Span) -> IResult<Span, DataType> {
    alt((
        data_type_vector,
        data_type_atom,
        map(non_integer_type, |x| DataType::NonIntegerType(x)),
        data_type_union,
        data_type_enum,
        map(symbol("string"), |x| DataType::String(x)),
        map(symbol("chandle"), |x| DataType::Chandle(x)),
        data_type_virtual,
        data_type_type,
        map(class_type, |x| DataType::ClassType(x)),
        map(symbol("event"), |x| DataType::Chandle(x)),
        map(ps_covergroup_identifier, |x| {
            DataType::PsCovergroupIdentifier(x)
        }),
        map(type_reference, |x| DataType::TypeReference(Box::new(x))),
    ))(s)
}

#[trace]
pub fn data_type_vector(s: Span) -> IResult<Span, DataType> {
    let (s, a) = integer_vector_type(s)?;
    let (s, b) = opt(signing)(s)?;
    let (s, c) = many0(packed_dimension)(s)?;
    Ok((s, DataType::Vector(DataTypeVector { nodes: (a, b, c) })))
}

#[trace]
pub fn data_type_atom(s: Span) -> IResult<Span, DataType> {
    let (s, a) = integer_atom_type(s)?;
    let (s, b) = opt(signing)(s)?;
    Ok((s, DataType::Atom(DataTypeAtom { nodes: (a, b) })))
}

#[trace]
pub fn data_type_union(s: Span) -> IResult<Span, DataType> {
    let (s, a) = struct_union(s)?;
    let (s, b) = opt(pair(packed, opt(signing)))(s)?;
    let (s, c) = brace(pair(struct_union_member, many0(struct_union_member)))(s)?;
    let (s, d) = many0(packed_dimension)(s)?;
    Ok((
        s,
        DataType::Union(Box::new(DataTypeUnion {
            nodes: (a, b, c, d),
        })),
    ))
}

#[trace]
pub fn packed(s: Span) -> IResult<Span, Packed> {
    let (s, a) = symbol("packed")(s)?;
    Ok((s, Packed { nodes: (a,) }))
}

#[trace]
pub fn data_type_enum(s: Span) -> IResult<Span, DataType> {
    let (s, a) = symbol("enum")(s)?;
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

#[trace]
pub fn data_type_virtual(s: Span) -> IResult<Span, DataType> {
    let (s, a) = symbol("virtual")(s)?;
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

#[trace]
pub fn interface(s: Span) -> IResult<Span, Interface> {
    let (s, a) = symbol("interface")(s)?;
    Ok((s, Interface { nodes: (a,) }))
}

#[trace]
pub fn data_type_type(s: Span) -> IResult<Span, DataType> {
    let (s, a) = opt(package_scope_or_class_scope)(s)?;
    let (s, b) = type_identifier(s)?;
    let (s, c) = many0(packed_dimension)(s)?;
    Ok((s, DataType::Type(DataTypeType { nodes: (a, b, c) })))
}

#[trace]
pub fn data_type_or_implicit(s: Span) -> IResult<Span, DataTypeOrImplicit> {
    alt((
        map(data_type, |x| DataTypeOrImplicit::DataType(x)),
        map(implicit_data_type, |x| {
            DataTypeOrImplicit::ImplicitDataType(x)
        }),
    ))(s)
}

#[trace]
pub fn implicit_data_type(s: Span) -> IResult<Span, ImplicitDataType> {
    let (s, a) = opt(signing)(s)?;
    let (s, b) = many0(packed_dimension)(s)?;
    Ok((s, ImplicitDataType { nodes: (a, b) }))
}

#[trace]
pub fn enum_base_type(s: Span) -> IResult<Span, EnumBaseType> {
    alt((
        enum_base_type_atom,
        enum_base_type_vector,
        enum_base_type_type,
    ))(s)
}

#[trace]
pub fn enum_base_type_atom(s: Span) -> IResult<Span, EnumBaseType> {
    let (s, a) = integer_atom_type(s)?;
    let (s, b) = opt(signing)(s)?;
    Ok((s, EnumBaseType::Atom(EnumBaseTypeAtom { nodes: (a, b) })))
}

#[trace]
pub fn enum_base_type_vector(s: Span) -> IResult<Span, EnumBaseType> {
    let (s, a) = integer_vector_type(s)?;
    let (s, b) = opt(signing)(s)?;
    let (s, c) = opt(packed_dimension)(s)?;
    Ok((
        s,
        EnumBaseType::Vector(EnumBaseTypeVector { nodes: (a, b, c) }),
    ))
}

#[trace]
pub fn enum_base_type_type(s: Span) -> IResult<Span, EnumBaseType> {
    let (s, a) = type_identifier(s)?;
    let (s, b) = opt(packed_dimension)(s)?;
    Ok((s, EnumBaseType::Type(EnumBaseTypeType { nodes: (a, b) })))
}

#[trace]
pub fn enum_name_declaration(s: Span) -> IResult<Span, EnumNameDeclaration> {
    let (s, a) = enum_identifier(s)?;
    let (s, b) = opt(bracket(pair(
        integral_number,
        opt(pair(symbol(":"), integral_number)),
    )))(s)?;
    let (s, c) = opt(pair(symbol("="), constant_expression))(s)?;
    Ok((s, EnumNameDeclaration { nodes: (a, b, c) }))
}

#[trace]
pub fn class_scope(s: Span) -> IResult<Span, ClassScope> {
    let (s, a) = class_type(s)?;
    let (s, b) = symbol("::")(s)?;
    Ok((s, ClassScope { nodes: (a, b) }))
}

#[trace]
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

#[trace]
pub fn integer_type(s: Span) -> IResult<Span, IntegerType> {
    alt((
        map(integer_vector_type, |x| IntegerType::IntegerVectorType(x)),
        map(integer_atom_type, |x| IntegerType::IntegerAtomType(x)),
    ))(s)
}

#[trace]
pub fn integer_atom_type(s: Span) -> IResult<Span, IntegerAtomType> {
    alt((
        map(symbol("byte"), |x| IntegerAtomType::Byte(x)),
        map(symbol("shortint"), |x| IntegerAtomType::Shortint(x)),
        map(symbol("int"), |x| IntegerAtomType::Int(x)),
        map(symbol("longint"), |x| IntegerAtomType::Longint(x)),
        map(symbol("integer"), |x| IntegerAtomType::Integer(x)),
        map(symbol("time"), |x| IntegerAtomType::Time(x)),
    ))(s)
}

#[trace]
pub fn integer_vector_type(s: Span) -> IResult<Span, IntegerVectorType> {
    alt((
        map(symbol("bit"), |x| IntegerVectorType::Bit(x)),
        map(symbol("logic"), |x| IntegerVectorType::Logic(x)),
        map(symbol("reg"), |x| IntegerVectorType::Reg(x)),
    ))(s)
}

#[trace]
pub fn non_integer_type(s: Span) -> IResult<Span, NonIntegerType> {
    alt((
        map(symbol("shortreal"), |x| NonIntegerType::Shortreal(x)),
        map(symbol("realtime"), |x| NonIntegerType::Realtime(x)),
        map(symbol("real"), |x| NonIntegerType::Real(x)),
    ))(s)
}

#[trace]
pub fn net_type(s: Span) -> IResult<Span, NetType> {
    alt((
        map(symbol("supply0"), |x| NetType::Supply0(x)),
        map(symbol("supply1"), |x| NetType::Supply1(x)),
        map(symbol("tri"), |x| NetType::Tri(x)),
        map(symbol("triand"), |x| NetType::Triand(x)),
        map(symbol("trior"), |x| NetType::Trior(x)),
        map(symbol("trireg"), |x| NetType::Trireg(x)),
        map(symbol("tri0"), |x| NetType::Tri0(x)),
        map(symbol("tri1"), |x| NetType::Tri1(x)),
        map(symbol("uwire"), |x| NetType::Uwire(x)),
        map(symbol("wire"), |x| NetType::Wire(x)),
        map(symbol("wand"), |x| NetType::Wand(x)),
        map(symbol("wor"), |x| NetType::Wor(x)),
    ))(s)
}

#[trace]
pub fn net_port_type(s: Span) -> IResult<Span, NetPortType> {
    alt((
        net_port_type_data_type,
        map(net_type_identifier, |x| NetPortType::NetTypeIdentifier(x)),
        net_port_type_interconnect,
    ))(s)
}

#[trace]
pub fn net_port_type_data_type(s: Span) -> IResult<Span, NetPortType> {
    let (s, a) = opt(net_type)(s)?;
    let (s, b) = data_type_or_implicit(s)?;
    Ok((
        s,
        NetPortType::DataType(NetPortTypeDataType { nodes: (a, b) }),
    ))
}

#[trace]
pub fn net_port_type_interconnect(s: Span) -> IResult<Span, NetPortType> {
    let (s, a) = symbol("interconnect")(s)?;
    let (s, b) = implicit_data_type(s)?;
    Ok((
        s,
        NetPortType::Interconnect(NetPortTypeInterconnect { nodes: (a, b) }),
    ))
}

#[trace]
pub fn variable_port_type(s: Span) -> IResult<Span, VariablePortType> {
    let (s, a) = var_data_type(s)?;
    Ok((s, VariablePortType { nodes: (a,) }))
}

#[trace]
pub fn var_data_type(s: Span) -> IResult<Span, VarDataType> {
    alt((
        map(data_type, |x| VarDataType::DataType(x)),
        var_data_type_var,
    ))(s)
}

#[trace]
pub fn var_data_type_var(s: Span) -> IResult<Span, VarDataType> {
    let (s, a) = symbol("var")(s)?;
    let (s, b) = data_type_or_implicit(s)?;
    Ok((s, VarDataType::Var(VarDataTypeVar { nodes: (a, b) })))
}

#[trace]
pub fn signing(s: Span) -> IResult<Span, Signing> {
    alt((
        map(symbol("signed"), |x| Signing::Signed(x)),
        map(symbol("unsigned"), |x| Signing::Unsigned(x)),
    ))(s)
}

#[trace]
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

#[trace]
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

#[trace]
pub fn data_type_or_void(s: Span) -> IResult<Span, DataTypeOrVoid> {
    alt((
        map(data_type, |x| DataTypeOrVoid::DataType(x)),
        map(symbol("void"), |x| DataTypeOrVoid::Void(x)),
    ))(s)
}

#[trace]
pub fn struct_union(s: Span) -> IResult<Span, StructUnion> {
    alt((
        map(symbol("struct"), |x| StructUnion::Struct(x)),
        map(pair(symbol("union"), symbol("tagged")), |x| {
            StructUnion::UnionTagged(x)
        }),
        map(symbol("union"), |x| StructUnion::Union(x)),
    ))(s)
}

#[trace]
pub fn type_reference(s: Span) -> IResult<Span, TypeReference> {
    alt((type_reference_expression, type_reference_data_type))(s)
}

#[trace]
pub fn type_reference_expression(s: Span) -> IResult<Span, TypeReference> {
    let (s, a) = symbol("type")(s)?;
    let (s, b) = paren(expression)(s)?;
    Ok((
        s,
        TypeReference::Expression(TypeReferenceExpression { nodes: (a, b) }),
    ))
}

#[trace]
pub fn type_reference_data_type(s: Span) -> IResult<Span, TypeReference> {
    let (s, a) = symbol("type")(s)?;
    let (s, b) = paren(data_type)(s)?;
    Ok((
        s,
        TypeReference::DataType(TypeReferenceDataType { nodes: (a, b) }),
    ))
}
