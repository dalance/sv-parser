use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum ConstantPrimary<'a> {
    PrimaryLiteral(PrimaryLiteral<'a>),
    PsParameter(ConstantPrimaryPsParameter<'a>),
    Specparam(ConstantPrimarySpecparam<'a>),
    Genvar(GenvarIdentifier<'a>),
    FormalPort(ConstantPrimaryFormalPort<'a>),
    Enum(ConstantPrimaryEnum<'a>),
    Concatenation(ConstantPrimaryConcatenation<'a>),
    MultipleConcatenation(ConstantPrimaryMultipleConcatenation<'a>),
    FunctionCall(SubroutineCall<'a>),
    LetExpression(LetExpression<'a>),
    MintypmaxExpression(ConstantMintypmaxExpression<'a>),
    Cast(ConstantCast<'a>),
    AssignmentPatternExpression(AssignmentPatternExpression<'a>),
    TypeReference(TypeReference<'a>),
    Null,
}

#[derive(Debug)]
pub struct ConstantPrimaryPsParameter<'a> {
    pub nodes: (PsParameterIdentifier<'a>, ConstantSelect<'a>),
}

#[derive(Debug)]
pub struct ConstantPrimarySpecparam<'a> {
    pub nodes: (SpecparamIdentifier<'a>, Option<ConstantRangeExpression<'a>>),
}

#[derive(Debug)]
pub struct ConstantPrimaryFormalPort<'a> {
    pub nodes: (FormalPortIdentifier<'a>, ConstantSelect<'a>),
}

#[derive(Debug)]
pub struct ConstantPrimaryEnum<'a> {
    pub nodes: (PackageScopeOrClassScope<'a>, EnumIdentifier<'a>),
}

#[derive(Debug)]
pub struct ConstantPrimaryConcatenation<'a> {
    pub nodes: (
        ConstantConcatenation<'a>,
        Option<ConstantRangeExpression<'a>>,
    ),
}

#[derive(Debug)]
pub struct ConstantPrimaryMultipleConcatenation<'a> {
    pub nodes: (
        ConstantMultipleConcatenation<'a>,
        Option<ConstantRangeExpression<'a>>,
    ),
}

#[derive(Debug)]
pub enum ModulePathPrimary<'a> {
    Number(Number<'a>),
    Identifier(Identifier<'a>),
    ModulePathConcatenation(ModulePathConcatenation<'a>),
    ModulePathMultipleConcatenation(ModulePathMultipleConcatenation<'a>),
    FunctionSubroutineCall(SubroutineCall<'a>),
    ModulePathMintypmaxExpression(ModulePathMintypmaxExpression<'a>),
}

#[derive(Debug)]
pub enum Primary<'a> {
    PrimaryLiteral(PrimaryLiteral<'a>),
    Hierarchical(PrimaryHierarchical<'a>),
    EmptyUnpackedArrayConcatenation,
    Concatenation(PrimaryConcatenation<'a>),
    MultipleConcatenation(PrimaryMultipleConcatenation<'a>),
    FunctionSubroutineCall(SubroutineCall<'a>),
    LetExpression(LetExpression<'a>),
    MintypmaxExpression(MintypmaxExpression<'a>),
    Cast(Cast<'a>),
    AssignmentPatternExpression(AssignmentPatternExpression<'a>),
    StreamingConcatenation(StreamingConcatenation<'a>),
    SequenceMethodCall(SequenceMethodCall<'a>),
    This,
    Dollar,
    Null,
}

#[derive(Debug)]
pub struct PrimaryHierarchical<'a> {
    pub nodes: (
        Option<PrimaryHierarchicalQualifier<'a>>,
        HierarchicalIdentifier<'a>,
        Select<'a>,
    ),
}

#[derive(Debug)]
pub struct PrimaryConcatenation<'a> {
    pub nodes: (Concatenation<'a>, Option<RangeExpression<'a>>),
}

#[derive(Debug)]
pub struct PrimaryMultipleConcatenation<'a> {
    pub nodes: (MultipleConcatenation<'a>, Option<RangeExpression<'a>>),
}

#[derive(Debug)]
pub enum PrimaryHierarchicalQualifier<'a> {
    ClassQualifier(ClassQualifier<'a>),
    PackageScope(PackageScope<'a>),
}

#[derive(Debug)]
pub struct ClassQualifier<'a> {
    pub nodes: (Option<Local>, Option<ImplicitClassHandleOrClassScope<'a>>),
}

#[derive(Debug)]
pub struct Local {}

#[derive(Debug)]
pub enum RangeExpression<'a> {
    Expression(Expression<'a>),
    PartSelectRange(PartSelectRange<'a>),
}

#[derive(Debug)]
pub enum PrimaryLiteral<'a> {
    Number(Number<'a>),
    TimeLiteral(TimeLiteral<'a>),
    UnbasedUnsizedLiteral(&'a str),
    StringLiteral(StringLiteral<'a>),
}

#[derive(Debug)]
pub enum TimeLiteral<'a> {
    UnsignedTimeLiteral(UnsignedTimeLiteral<'a>),
    FixedPointTimeLiteral(FixedPointTimeLiteral<'a>),
}

#[derive(Debug)]
pub enum TimeUnit {
    S,
    MS,
    US,
    NS,
    PS,
    FS,
}

#[derive(Debug)]
pub enum ImplicitClassHandle {
    This,
    Super,
    ThisSuper,
}

#[derive(Debug)]
pub struct BitSelect<'a> {
    nodes: (Vec<Expression<'a>>,),
}

#[derive(Debug)]
pub struct UnsignedTimeLiteral<'a> {
    pub nodes: (&'a str, TimeUnit),
}

#[derive(Debug)]
pub struct FixedPointTimeLiteral<'a> {
    pub nodes: (RealNumber<'a>, TimeUnit),
}

#[derive(Debug)]
pub struct Select<'a> {
    pub nodes: (
        Option<SelectMember<'a>>,
        BitSelect<'a>,
        Option<PartSelectRange<'a>>,
    ),
}

#[derive(Debug)]
pub struct ConstantBitSelect<'a> {
    nodes: (Vec<ConstantExpression<'a>>,),
}

#[derive(Debug)]
pub struct ConstantSelect<'a> {
    pub nodes: (
        Option<SelectMember<'a>>,
        ConstantBitSelect<'a>,
        Option<ConstantPartSelectRange<'a>>,
    ),
}

#[derive(Debug)]
pub struct SelectMember<'a> {
    pub nodes: (
        Vec<(MemberIdentifier<'a>, BitSelect<'a>)>,
        MemberIdentifier<'a>,
    ),
}

#[derive(Debug)]
pub struct Cast<'a> {
    pub nodes: (CastingType<'a>, Expression<'a>),
}

#[derive(Debug)]
pub struct ConstantCast<'a> {
    pub nodes: (CastingType<'a>, ConstantExpression<'a>),
}

// -----------------------------------------------------------------------------

pub fn constant_primary(s: &str) -> IResult<&str, ConstantPrimary> {
    alt((
        map(symbol("null"), |_| ConstantPrimary::Null),
        map(primary_literal, |x| ConstantPrimary::PrimaryLiteral(x)),
        constant_primary_ps_parameter,
        constant_primary_specparam,
        map(genvar_identifier, |x| ConstantPrimary::Genvar(x)),
        constant_primary_formal_port,
        constant_primary_enum,
        constant_primary_concatenation,
        constant_primary_multiple_concatenation,
        map(constant_function_call, |x| ConstantPrimary::FunctionCall(x)),
        map(constant_let_expression, |x| {
            ConstantPrimary::LetExpression(x)
        }),
        map(paren(constant_mintypmax_expression), |x| {
            ConstantPrimary::MintypmaxExpression(x)
        }),
        map(constant_cast, |x| ConstantPrimary::Cast(x)),
        map(constant_assignment_pattern_expression, |x| {
            ConstantPrimary::AssignmentPatternExpression(x)
        }),
        map(type_reference, |x| ConstantPrimary::TypeReference(x)),
    ))(s)
}

pub fn constant_primary_ps_parameter(s: &str) -> IResult<&str, ConstantPrimary> {
    let (s, x) = ps_parameter_identifier(s)?;
    let (s, y) = constant_select(s)?;
    Ok((
        s,
        ConstantPrimary::PsParameter(ConstantPrimaryPsParameter { nodes: (x, y) }),
    ))
}

pub fn constant_primary_specparam(s: &str) -> IResult<&str, ConstantPrimary> {
    let (s, x) = specparam_identifier(s)?;
    let (s, y) = opt(bracket(constant_range_expression))(s)?;
    Ok((
        s,
        ConstantPrimary::Specparam(ConstantPrimarySpecparam { nodes: (x, y) }),
    ))
}

pub fn constant_primary_formal_port(s: &str) -> IResult<&str, ConstantPrimary> {
    let (s, x) = formal_port_identifier(s)?;
    let (s, y) = constant_select(s)?;
    Ok((
        s,
        ConstantPrimary::FormalPort(ConstantPrimaryFormalPort { nodes: (x, y) }),
    ))
}

pub fn constant_primary_enum(s: &str) -> IResult<&str, ConstantPrimary> {
    let (s, x) = package_scope_or_class_scope(s)?;
    let (s, y) = enum_identifier(s)?;
    Ok((
        s,
        ConstantPrimary::Enum(ConstantPrimaryEnum { nodes: (x, y) }),
    ))
}

pub fn constant_primary_concatenation(s: &str) -> IResult<&str, ConstantPrimary> {
    let (s, x) = constant_concatenation(s)?;
    let (s, y) = opt(bracket(constant_range_expression))(s)?;
    Ok((
        s,
        ConstantPrimary::Concatenation(ConstantPrimaryConcatenation { nodes: (x, y) }),
    ))
}

pub fn constant_primary_multiple_concatenation(s: &str) -> IResult<&str, ConstantPrimary> {
    let (s, x) = constant_multiple_concatenation(s)?;
    let (s, y) = opt(bracket(constant_range_expression))(s)?;
    Ok((
        s,
        ConstantPrimary::MultipleConcatenation(ConstantPrimaryMultipleConcatenation {
            nodes: (x, y),
        }),
    ))
}

pub fn constant_primary_mintypmax_expression(s: &str) -> IResult<&str, ConstantPrimary> {
    let (s, x) = paren(constant_mintypmax_expression)(s)?;
    Ok((s, ConstantPrimary::MintypmaxExpression(x)))
}

pub fn module_path_primary(s: &str) -> IResult<&str, ModulePathPrimary> {
    alt((
        map(number, |x| ModulePathPrimary::Number(x)),
        map(identifier, |x| ModulePathPrimary::Identifier(x)),
        map(module_path_concatenation, |x| {
            ModulePathPrimary::ModulePathConcatenation(x)
        }),
        map(module_path_multiple_concatenation, |x| {
            ModulePathPrimary::ModulePathMultipleConcatenation(x)
        }),
        map(function_subroutine_call, |x| {
            ModulePathPrimary::FunctionSubroutineCall(x)
        }),
        map(paren(module_path_mintypmax_expression), |x| {
            ModulePathPrimary::ModulePathMintypmaxExpression(x)
        }),
    ))(s)
}

pub fn primary(s: &str) -> IResult<&str, Primary> {
    alt((
        map(primary_literal, |x| Primary::PrimaryLiteral(x)),
        primary_hierarchical,
        map(empty_unpacked_array_concatenation, |_| {
            Primary::EmptyUnpackedArrayConcatenation
        }),
        primary_concatenation,
        map(function_subroutine_call, |x| {
            Primary::FunctionSubroutineCall(x)
        }),
        map(let_expression, |x| Primary::LetExpression(x)),
        map(paren(mintypmax_expression), |x| {
            Primary::MintypmaxExpression(x)
        }),
        map(cast, |x| Primary::Cast(x)),
        map(assignment_pattern_expression, |x| {
            Primary::AssignmentPatternExpression(x)
        }),
        map(streaming_concatenation, |x| {
            Primary::StreamingConcatenation(x)
        }),
        map(sequence_method_call, |x| Primary::SequenceMethodCall(x)),
        map(symbol("this"), |_| Primary::This),
        map(symbol("$"), |_| Primary::Dollar),
        map(symbol("null"), |_| Primary::Null),
    ))(s)
}

pub fn primary_hierarchical(s: &str) -> IResult<&str, Primary> {
    let (s, x) = opt(primary_hierarchical_qualifier)(s)?;
    let (s, y) = hierarchical_identifier(s)?;
    let (s, z) = select(s)?;
    Ok((
        s,
        Primary::Hierarchical(PrimaryHierarchical { nodes: (x, y, z) }),
    ))
}

pub fn primary_concatenation(s: &str) -> IResult<&str, Primary> {
    let (s, x) = concatenation(s)?;
    let (s, y) = opt(range_expression)(s)?;
    Ok((
        s,
        Primary::Concatenation(PrimaryConcatenation { nodes: (x, y) }),
    ))
}

pub fn primary_multiple_concatenation(s: &str) -> IResult<&str, Primary> {
    let (s, x) = multiple_concatenation(s)?;
    let (s, y) = opt(range_expression)(s)?;
    Ok((
        s,
        Primary::MultipleConcatenation(PrimaryMultipleConcatenation { nodes: (x, y) }),
    ))
}

pub fn primary_hierarchical_qualifier(s: &str) -> IResult<&str, PrimaryHierarchicalQualifier> {
    alt((
        map(class_qualifier, |x| {
            PrimaryHierarchicalQualifier::ClassQualifier(x)
        }),
        map(package_scope, |x| {
            PrimaryHierarchicalQualifier::PackageScope(x)
        }),
    ))(s)
}

pub fn class_qualifier(s: &str) -> IResult<&str, ClassQualifier> {
    let (s, x) = opt(symbol("local::"))(s)?;
    let (s, y) = opt(implicit_class_handle_or_class_scope)(s)?;
    Ok((
        s,
        ClassQualifier {
            nodes: (x.map(|_| Local {}), y),
        },
    ))
}

pub fn range_expression(s: &str) -> IResult<&str, RangeExpression> {
    alt((
        map(expression, |x| RangeExpression::Expression(x)),
        map(part_select_range, |x| RangeExpression::PartSelectRange(x)),
    ))(s)
}

pub fn primary_literal(s: &str) -> IResult<&str, PrimaryLiteral> {
    alt((
        map(time_literal, |x| PrimaryLiteral::TimeLiteral(x)),
        map(number, |x| PrimaryLiteral::Number(x)),
        map(unbased_unsized_literal, |x| {
            PrimaryLiteral::UnbasedUnsizedLiteral(x)
        }),
        map(string_literal, |x| PrimaryLiteral::StringLiteral(x)),
    ))(s)
}

pub fn time_literal(s: &str) -> IResult<&str, TimeLiteral> {
    alt((unsigned_time_literal, fixed_point_time_literal))(s)
}

pub fn unsigned_time_literal(s: &str) -> IResult<&str, TimeLiteral> {
    let (s, x) = unsigned_number(s)?;
    let (s, y) = time_unit(s)?;
    Ok((
        s,
        TimeLiteral::UnsignedTimeLiteral(UnsignedTimeLiteral { nodes: (x, y) }),
    ))
}

pub fn fixed_point_time_literal(s: &str) -> IResult<&str, TimeLiteral> {
    let (s, x) = fixed_point_number(s)?;
    let (s, y) = time_unit(s)?;
    Ok((
        s,
        TimeLiteral::FixedPointTimeLiteral(FixedPointTimeLiteral { nodes: (x, y) }),
    ))
}

pub fn time_unit(s: &str) -> IResult<&str, TimeUnit> {
    let (s, x) = alt((
        symbol("s"),
        symbol("ms"),
        symbol("us"),
        symbol("ns"),
        symbol("ps"),
        symbol("fs"),
    ))(s)?;
    let unit = match x {
        "s" => TimeUnit::S,
        "ms" => TimeUnit::MS,
        "us" => TimeUnit::US,
        "ns" => TimeUnit::NS,
        "ps" => TimeUnit::PS,
        "fs" => TimeUnit::FS,
        _ => unreachable!(),
    };
    Ok((s, unit))
}

pub fn implicit_class_handle(s: &str) -> IResult<&str, ImplicitClassHandle> {
    alt((
        map(
            tuple((symbol("this"), symbol("."), symbol("super"))),
            |_| ImplicitClassHandle::ThisSuper,
        ),
        map(symbol("this"), |_| ImplicitClassHandle::This),
        map(symbol("super"), |_| ImplicitClassHandle::Super),
    ))(s)
}

pub fn bit_select(s: &str) -> IResult<&str, BitSelect> {
    let (s, x) = many0(bracket(expression))(s)?;
    Ok((s, BitSelect { nodes: (x,) }))
}

pub fn select(s: &str) -> IResult<&str, Select> {
    let (s, x) = opt(pair(
        many0(preceded(symbol("."), pair(member_identifier, bit_select))),
        preceded(symbol("."), member_identifier),
    ))(s)?;
    let (s, y) = bit_select(s)?;
    let (s, z) = opt(bracket(part_select_range))(s)?;

    let x = if let Some((x, y)) = x {
        Some(SelectMember { nodes: (x, y) })
    } else {
        None
    };

    Ok((s, Select { nodes: (x, y, z) }))
}

pub fn nonrange_select(s: &str) -> IResult<&str, Select> {
    let (s, x) = opt(pair(
        many0(preceded(symbol("."), pair(member_identifier, bit_select))),
        preceded(symbol("."), member_identifier),
    ))(s)?;
    let (s, y) = bit_select(s)?;

    let x = if let Some((x, y)) = x {
        Some(SelectMember { nodes: (x, y) })
    } else {
        None
    };

    Ok((
        s,
        Select {
            nodes: (x, y, None),
        },
    ))
}

pub fn constant_bit_select(s: &str) -> IResult<&str, ConstantBitSelect> {
    let (s, x) = many0(bracket(constant_expression))(s)?;
    Ok((s, ConstantBitSelect { nodes: (x,) }))
}

pub fn constant_select(s: &str) -> IResult<&str, ConstantSelect> {
    let (s, x) = opt(pair(
        many0(preceded(symbol("."), pair(member_identifier, bit_select))),
        preceded(symbol("."), member_identifier),
    ))(s)?;
    let (s, y) = constant_bit_select(s)?;
    let (s, z) = opt(bracket(constant_part_select_range))(s)?;

    let x = if let Some((x, y)) = x {
        Some(SelectMember { nodes: (x, y) })
    } else {
        None
    };

    Ok((s, ConstantSelect { nodes: (x, y, z) }))
}

pub fn constant_cast(s: &str) -> IResult<&str, ConstantCast> {
    let (s, x) = casting_type(s)?;
    let (s, _) = symbol("'")(s)?;
    let (s, y) = paren(constant_expression)(s)?;
    Ok((s, ConstantCast { nodes: (x, y) }))
}

pub fn constant_let_expression(s: &str) -> IResult<&str, LetExpression> {
    let_expression(s)
}

pub fn cast(s: &str) -> IResult<&str, Cast> {
    let (s, x) = casting_type(s)?;
    let (s, _) = symbol("'")(s)?;
    let (s, y) = paren(expression)(s)?;
    Ok((s, Cast { nodes: (x, y) }))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        assert_eq!(
            format!("{:?}", all_consuming(primary)("2.1ns")),
            "Ok((\"\", PrimaryLiteral(TimeLiteral(FixedPointTimeLiteral(FixedPointTimeLiteral { number: FixedPointNumber(FixedPointNumber { integer_value: \"2\", fraction_value: \"1\" }), unit: NS })))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(primary)("40 ps")),
            "Ok((\"\", PrimaryLiteral(TimeLiteral(UnsignedTimeLiteral(UnsignedTimeLiteral { number: \"40\", unit: PS })))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(primary)("'0")),
            "Ok((\"\", PrimaryLiteral(UnbasedUnsizedLiteral(\"\\\'0\"))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(primary)("10")),
            "Ok((\"\", PrimaryLiteral(Number(IntegralNumber(UnsignedNumber(\"10\"))))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(primary)("\"aaa\"")),
            "Ok((\"\", PrimaryLiteral(StringLiteral(StringLiteral { raw: \"aaa\" }))))"
        );
        //assert_eq!(
        //    format!("{:?}", all_consuming(primary)("this")),
        //    "Ok((\"\", This))"
        //);
        //assert_eq!(
        //    format!("{:?}", all_consuming(primary)("$")),
        //    "Ok((\"\", Dollar))"
        //);
        //assert_eq!(
        //    format!("{:?}", all_consuming(primary)("null")),
        //    "Ok((\"\", Null))"
        //);
        assert_eq!(
            format!("{:?}", all_consuming(primary)("this . super.a")),
            "Ok((\"\", Hierarchical(PrimaryHierarchical { qualifier: Some(ClassQualifier(ClassQualifier { local: false, scope: Some(ImplicitClassHandle(ThisSuper)) })), identifier: HierarchicalIdentifier { hierarchy: [], identifier: Identifier { raw: \"a\" } }, select: Select { member: None, bit_select: [], part_select_range: None } })))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(module_path_primary)("10")),
            "Ok((\"\", Number(IntegralNumber(UnsignedNumber(\"10\")))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(constant_primary)("null")),
            "Ok((\"\", Null))"
        );
    }
}
