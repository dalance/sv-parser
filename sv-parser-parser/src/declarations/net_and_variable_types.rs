use crate::*;

// -----------------------------------------------------------------------------

#[recursive_parser]
#[packrat_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn casting_type(s: Span) -> IResult<Span, CastingType> {
    alt((
        map(terminated(simple_type, peek(tag("'"))), |x| {
            CastingType::SimpleType(Box::new(x))
        }),
        map(signing, |x| CastingType::Signing(Box::new(x))),
        map(keyword("string"), |x| CastingType::String(Box::new(x))),
        map(keyword("const"), |x| CastingType::Const(Box::new(x))),
        map(constant_primary_without_cast, |x| {
            CastingType::ConstantPrimary(Box::new(x))
        }),
    ))(s)
}

#[recursive_parser]
#[packrat_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn constant_casting_type(s: Span) -> IResult<Span, CastingType> {
    alt((
        map(terminated(simple_type, peek(tag("'"))), |x| {
            CastingType::SimpleType(Box::new(x))
        }),
        map(signing, |x| CastingType::Signing(Box::new(x))),
        map(keyword("string"), |x| CastingType::String(Box::new(x))),
        map(keyword("const"), |x| CastingType::Const(Box::new(x))),
        map(constant_primary_without_cast, |x| {
            CastingType::ConstantPrimary(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn data_type(s: Span) -> IResult<Span, DataType> {
    alt((
        data_type_vector,
        data_type_atom,
        map(non_integer_type, |x| DataType::NonIntegerType(Box::new(x))),
        data_type_struct_union,
        data_type_enum,
        map(keyword("string"), |x| DataType::String(Box::new(x))),
        map(keyword("chandle"), |x| DataType::Chandle(Box::new(x))),
        data_type_virtual,
        map(terminated(class_type, peek(not(packed_dimension))), |x| {
            DataType::ClassType(Box::new(x))
        }),
        data_type_type,
        map(keyword("event"), |x| DataType::Chandle(Box::new(x))),
        map(ps_covergroup_identifier, |x| {
            DataType::PsCovergroupIdentifier(Box::new(x))
        }),
        map(type_reference, |x| DataType::TypeReference(Box::new(x))),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn data_type_vector(s: Span) -> IResult<Span, DataType> {
    let (s, a) = integer_vector_type(s)?;
    let (s, b) = opt(signing)(s)?;
    let (s, c) = many0(packed_dimension)(s)?;
    Ok((
        s,
        DataType::Vector(Box::new(DataTypeVector { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn data_type_atom(s: Span) -> IResult<Span, DataType> {
    let (s, a) = integer_atom_type(s)?;
    let (s, b) = opt(signing)(s)?;
    Ok((s, DataType::Atom(Box::new(DataTypeAtom { nodes: (a, b) }))))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn data_type_struct_union(s: Span) -> IResult<Span, DataType> {
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

#[tracable_parser]
#[packrat_parser]
pub(crate) fn packed(s: Span) -> IResult<Span, Packed> {
    let (s, a) = keyword("packed")(s)?;
    Ok((s, Packed { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn data_type_enum(s: Span) -> IResult<Span, DataType> {
    let (s, a) = keyword("enum")(s)?;
    let (s, b) = opt(enum_base_type)(s)?;
    let (s, c) = brace(list(symbol(","), enum_name_declaration))(s)?;
    let (s, d) = many0(packed_dimension)(s)?;
    Ok((
        s,
        DataType::Enum(Box::new(DataTypeEnum {
            nodes: (a, b, c, d),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn data_type_virtual(s: Span) -> IResult<Span, DataType> {
    let (s, a) = keyword("virtual")(s)?;
    let (s, b) = opt(interface)(s)?;
    let (s, c) = interface_identifier(s)?;
    let (s, d) = opt(parameter_value_assignment)(s)?;
    let (s, e) = opt(pair(symbol("."), modport_identifier))(s)?;
    Ok((
        s,
        DataType::Virtual(Box::new(DataTypeVirtual {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn interface(s: Span) -> IResult<Span, Interface> {
    let (s, a) = keyword("interface")(s)?;
    Ok((s, Interface { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn data_type_type(s: Span) -> IResult<Span, DataType> {
    let (s, a) = opt(package_scope_or_class_scope)(s)?;
    let (s, b) = type_identifier(s)?;
    let (s, c) = many0(packed_dimension)(s)?;
    Ok((
        s,
        DataType::Type(Box::new(DataTypeType { nodes: (a, b, c) })),
    ))
}

// all data_type_or_implicit call are specialized for each parser
#[allow(dead_code)]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn data_type_or_implicit(s: Span) -> IResult<Span, DataTypeOrImplicit> {
    alt((
        map(data_type, |x| DataTypeOrImplicit::DataType(Box::new(x))),
        map(implicit_data_type, |x| {
            DataTypeOrImplicit::ImplicitDataType(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn implicit_data_type(s: Span) -> IResult<Span, ImplicitDataType> {
    let (s, a) = opt(signing)(s)?;
    let (s, b) = many0(packed_dimension)(s)?;
    Ok((s, ImplicitDataType { nodes: (a, b) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn enum_base_type(s: Span) -> IResult<Span, EnumBaseType> {
    alt((
        enum_base_type_atom,
        enum_base_type_vector,
        enum_base_type_type,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn enum_base_type_atom(s: Span) -> IResult<Span, EnumBaseType> {
    let (s, a) = integer_atom_type(s)?;
    let (s, b) = opt(signing)(s)?;
    Ok((
        s,
        EnumBaseType::Atom(Box::new(EnumBaseTypeAtom { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn enum_base_type_vector(s: Span) -> IResult<Span, EnumBaseType> {
    let (s, a) = integer_vector_type(s)?;
    let (s, b) = opt(signing)(s)?;
    let (s, c) = opt(packed_dimension)(s)?;
    Ok((
        s,
        EnumBaseType::Vector(Box::new(EnumBaseTypeVector { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn enum_base_type_type(s: Span) -> IResult<Span, EnumBaseType> {
    let (s, a) = type_identifier(s)?;
    let (s, b) = opt(packed_dimension)(s)?;
    Ok((
        s,
        EnumBaseType::Type(Box::new(EnumBaseTypeType { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn enum_name_declaration(s: Span) -> IResult<Span, EnumNameDeclaration> {
    let (s, a) = enum_identifier(s)?;
    let (s, b) = opt(bracket(pair(
        integral_number,
        opt(pair(symbol(":"), integral_number)),
    )))(s)?;
    let (s, c) = opt(pair(symbol("="), constant_expression))(s)?;
    Ok((s, EnumNameDeclaration { nodes: (a, b, c) }))
}

#[packrat_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn class_scope(s: Span) -> IResult<Span, ClassScope> {
    let (s, a) = class_type_class_scope(s)?;
    let (s, b) = symbol("::")(s)?;
    Ok((s, ClassScope { nodes: (a, b) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn class_type_class_scope(s: Span) -> IResult<Span, ClassType> {
    let (s, a) = ps_class_identifier_class_type_class_scope(s)?;
    let (s, b) = opt(parameter_value_assignment)(s)?;
    let (s, c) = many0(terminated(
        triple(
            symbol("::"),
            class_identifier,
            opt(parameter_value_assignment),
        ),
        peek(symbol("::")),
    ))(s)?;
    Ok((s, ClassType { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn ps_class_identifier_class_type_class_scope(
    s: Span,
) -> IResult<Span, PsClassIdentifier> {
    let (s, a) = opt(terminated(
        package_scope,
        peek(pair(class_identifier, symbol("::"))),
    ))(s)?;
    let (s, b) = class_identifier(s)?;
    Ok((s, PsClassIdentifier { nodes: (a, b) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn class_type(s: Span) -> IResult<Span, ClassType> {
    let (s, a) = ps_class_identifier(s)?;
    let (s, b) = opt(parameter_value_assignment)(s)?;
    let (s, c) = many0(triple(
        symbol("::"),
        class_identifier,
        opt(parameter_value_assignment),
    ))(s)?;
    Ok((s, ClassType { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn integer_type(s: Span) -> IResult<Span, IntegerType> {
    alt((
        map(integer_vector_type, |x| {
            IntegerType::IntegerVectorType(Box::new(x))
        }),
        map(integer_atom_type, |x| {
            IntegerType::IntegerAtomType(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn integer_atom_type(s: Span) -> IResult<Span, IntegerAtomType> {
    alt((
        map(keyword("byte"), |x| IntegerAtomType::Byte(Box::new(x))),
        map(keyword("shortint"), |x| {
            IntegerAtomType::Shortint(Box::new(x))
        }),
        map(keyword("int"), |x| IntegerAtomType::Int(Box::new(x))),
        map(keyword("longint"), |x| {
            IntegerAtomType::Longint(Box::new(x))
        }),
        map(keyword("integer"), |x| {
            IntegerAtomType::Integer(Box::new(x))
        }),
        map(keyword("time"), |x| IntegerAtomType::Time(Box::new(x))),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn integer_vector_type(s: Span) -> IResult<Span, IntegerVectorType> {
    alt((
        map(keyword("bit"), |x| IntegerVectorType::Bit(Box::new(x))),
        map(keyword("logic"), |x| IntegerVectorType::Logic(Box::new(x))),
        map(keyword("reg"), |x| IntegerVectorType::Reg(Box::new(x))),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn non_integer_type(s: Span) -> IResult<Span, NonIntegerType> {
    alt((
        map(keyword("shortreal"), |x| {
            NonIntegerType::Shortreal(Box::new(x))
        }),
        map(keyword("realtime"), |x| {
            NonIntegerType::Realtime(Box::new(x))
        }),
        map(keyword("real"), |x| NonIntegerType::Real(Box::new(x))),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn net_type(s: Span) -> IResult<Span, NetType> {
    alt((
        map(keyword("supply0"), |x| NetType::Supply0(Box::new(x))),
        map(keyword("supply1"), |x| NetType::Supply1(Box::new(x))),
        map(keyword("triand"), |x| NetType::Triand(Box::new(x))),
        map(keyword("trior"), |x| NetType::Trior(Box::new(x))),
        map(keyword("trireg"), |x| NetType::Trireg(Box::new(x))),
        map(keyword("tri0"), |x| NetType::Tri0(Box::new(x))),
        map(keyword("tri1"), |x| NetType::Tri1(Box::new(x))),
        map(keyword("tri"), |x| NetType::Tri(Box::new(x))),
        map(keyword("uwire"), |x| NetType::Uwire(Box::new(x))),
        map(keyword("wire"), |x| NetType::Wire(Box::new(x))),
        map(keyword("wand"), |x| NetType::Wand(Box::new(x))),
        map(keyword("wor"), |x| NetType::Wor(Box::new(x))),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn net_port_type(s: Span) -> IResult<Span, NetPortType> {
    alt((
        net_port_type_data_type,
        map(net_type_identifier, |x| {
            NetPortType::NetTypeIdentifier(Box::new(x))
        }),
        net_port_type_interconnect,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn net_port_type_data_type(s: Span) -> IResult<Span, NetPortType> {
    let (s, a) = opt(net_type)(s)?;
    let (s, b) = data_type_or_implicit_net_port_type_data_type(s)?;
    Ok((
        s,
        NetPortType::DataType(Box::new(NetPortTypeDataType { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn data_type_or_implicit_net_port_type_data_type(
    s: Span,
) -> IResult<Span, DataTypeOrImplicit> {
    alt((
        map(terminated(data_type, peek(port_identifier)), |x| {
            DataTypeOrImplicit::DataType(Box::new(x))
        }),
        map(terminated(implicit_data_type, peek(port_identifier)), |x| {
            DataTypeOrImplicit::ImplicitDataType(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn net_port_type_interconnect(s: Span) -> IResult<Span, NetPortType> {
    let (s, a) = keyword("interconnect")(s)?;
    let (s, b) = implicit_data_type(s)?;
    Ok((
        s,
        NetPortType::Interconnect(Box::new(NetPortTypeInterconnect { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn variable_port_type(s: Span) -> IResult<Span, VariablePortType> {
    let (s, a) = var_data_type(s)?;
    Ok((s, VariablePortType { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn var_data_type(s: Span) -> IResult<Span, VarDataType> {
    alt((
        map(terminated(data_type, peek(variable_identifier)), |x| {
            VarDataType::DataType(Box::new(x))
        }),
        var_data_type_var,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn var_data_type_var(s: Span) -> IResult<Span, VarDataType> {
    let (s, a) = keyword("var")(s)?;
    let (s, b) = data_type_or_implicit_var_data_type_var(s)?;
    Ok((
        s,
        VarDataType::Var(Box::new(VarDataTypeVar { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn data_type_or_implicit_var_data_type_var(
    s: Span,
) -> IResult<Span, DataTypeOrImplicit> {
    alt((
        map(terminated(data_type, peek(variable_identifier)), |x| {
            DataTypeOrImplicit::DataType(Box::new(x))
        }),
        map(
            terminated(implicit_data_type, peek(variable_identifier)),
            |x| DataTypeOrImplicit::ImplicitDataType(Box::new(x)),
        ),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn signing(s: Span) -> IResult<Span, Signing> {
    alt((
        map(keyword("signed"), |x| Signing::Signed(Box::new(x))),
        map(keyword("unsigned"), |x| Signing::Unsigned(Box::new(x))),
    ))(s)
}

#[packrat_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn simple_type(s: Span) -> IResult<Span, SimpleType> {
    alt((
        map(integer_type, |x| SimpleType::IntegerType(Box::new(x))),
        map(non_integer_type, |x| {
            SimpleType::NonIntegerType(Box::new(x))
        }),
        map(ps_type_identifier, |x| {
            SimpleType::PsTypeIdentifier(Box::new(x))
        }),
        map(ps_parameter_identifier, |x| {
            SimpleType::PsParameterIdentifier(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn struct_union_member(s: Span) -> IResult<Span, StructUnionMember> {
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

#[tracable_parser]
#[packrat_parser]
pub(crate) fn data_type_or_void(s: Span) -> IResult<Span, DataTypeOrVoid> {
    alt((
        map(data_type, |x| DataTypeOrVoid::DataType(Box::new(x))),
        map(keyword("void"), |x| DataTypeOrVoid::Void(Box::new(x))),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn struct_union(s: Span) -> IResult<Span, StructUnion> {
    alt((
        map(keyword("struct"), |x| StructUnion::Struct(Box::new(x))),
        map(pair(keyword("union"), keyword("tagged")), |x| {
            StructUnion::UnionTagged(Box::new(x))
        }),
        map(keyword("union"), |x| StructUnion::Union(Box::new(x))),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn type_reference(s: Span) -> IResult<Span, TypeReference> {
    alt((type_reference_expression, type_reference_data_type))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn type_reference_expression(s: Span) -> IResult<Span, TypeReference> {
    let (s, a) = keyword("type")(s)?;
    let (s, b) = paren(expression)(s)?;
    Ok((
        s,
        TypeReference::Expression(Box::new(TypeReferenceExpression { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn type_reference_data_type(s: Span) -> IResult<Span, TypeReference> {
    let (s, a) = keyword("type")(s)?;
    let (s, b) = paren(data_type)(s)?;
    Ok((
        s,
        TypeReference::DataType(Box::new(TypeReferenceDataType { nodes: (a, b) })),
    ))
}
