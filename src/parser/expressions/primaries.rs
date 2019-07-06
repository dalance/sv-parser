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
    Genvar(Identifier<'a>),
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
    identifier: ScopedIdentifier<'a>,
    select: ConstantSelect<'a>,
}

#[derive(Debug)]
pub struct ConstantPrimarySpecparam<'a> {
    identifier: Identifier<'a>,
    range: Option<ConstantRangeExpression<'a>>,
}

#[derive(Debug)]
pub struct ConstantPrimaryFormalPort<'a> {
    identifier: Identifier<'a>,
    select: ConstantSelect<'a>,
}

#[derive(Debug)]
pub struct ConstantPrimaryEnum<'a> {
    scope: Scope<'a>,
    identifier: Identifier<'a>,
}

#[derive(Debug)]
pub struct ConstantPrimaryConcatenation<'a> {
    concatenation: ConstantConcatenation<'a>,
    range: Option<ConstantRangeExpression<'a>>,
}

#[derive(Debug)]
pub struct ConstantPrimaryMultipleConcatenation<'a> {
    concatenation: ConstantMultipleConcatenation<'a>,
    range: Option<ConstantRangeExpression<'a>>,
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
    qualifier: Option<PrimaryHierarchicalQualifier<'a>>,
    identifier: HierarchicalIdentifier<'a>,
    select: Select<'a>,
}

#[derive(Debug)]
pub struct PrimaryConcatenation<'a> {
    concatenation: Concatenation<'a>,
    range: Option<RangeExpression<'a>>,
}

#[derive(Debug)]
pub struct PrimaryMultipleConcatenation<'a> {
    concatenation: MultipleConcatenation<'a>,
    range: Option<RangeExpression<'a>>,
}

#[derive(Debug)]
pub enum PrimaryHierarchicalQualifier<'a> {
    ClassQualifier(ClassQualifier<'a>),
    PackageScope(Scope<'a>),
}

#[derive(Debug)]
pub struct ClassQualifier<'a> {
    local: bool,
    scope: Option<Scope<'a>>,
}

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
pub struct UnsignedTimeLiteral<'a> {
    number: &'a str,
    unit: TimeUnit,
}

#[derive(Debug)]
pub struct FixedPointTimeLiteral<'a> {
    number: RealNumber<'a>,
    unit: TimeUnit,
}

#[derive(Debug)]
pub struct Select<'a> {
    member: Option<SelectMember<'a>>,
    bit_select: Vec<Expression<'a>>,
    part_select_range: Option<PartSelectRange<'a>>,
}

#[derive(Debug)]
pub struct ConstantSelect<'a> {
    member: Option<SelectMember<'a>>,
    bit_select: Vec<ConstantExpression<'a>>,
    part_select_range: Option<ConstantPartSelectRange<'a>>,
}

#[derive(Debug)]
pub struct SelectMember<'a> {
    upper: Vec<(Identifier<'a>, Vec<Expression<'a>>)>,
    identifier: Identifier<'a>,
}

#[derive(Debug)]
pub struct Cast<'a> {
    r#type: CastingType<'a>,
    expression: Expression<'a>,
}

#[derive(Debug)]
pub struct ConstantCast<'a> {
    r#type: CastingType<'a>,
    expression: ConstantExpression<'a>,
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
        ConstantPrimary::PsParameter(ConstantPrimaryPsParameter {
            identifier: x,
            select: y,
        }),
    ))
}

pub fn constant_primary_specparam(s: &str) -> IResult<&str, ConstantPrimary> {
    let (s, x) = specparam_identifier(s)?;
    let (s, y) = opt(bracket(constant_range_expression))(s)?;
    Ok((
        s,
        ConstantPrimary::Specparam(ConstantPrimarySpecparam {
            identifier: x,
            range: y,
        }),
    ))
}

pub fn constant_primary_formal_port(s: &str) -> IResult<&str, ConstantPrimary> {
    let (s, x) = formal_port_identifier(s)?;
    let (s, y) = constant_select(s)?;
    Ok((
        s,
        ConstantPrimary::FormalPort(ConstantPrimaryFormalPort {
            identifier: x,
            select: y,
        }),
    ))
}

pub fn constant_primary_enum(s: &str) -> IResult<&str, ConstantPrimary> {
    let (s, x) = alt((package_scope, class_scope))(s)?;
    let (s, y) = enum_identifier(s)?;
    Ok((
        s,
        ConstantPrimary::Enum(ConstantPrimaryEnum {
            scope: x,
            identifier: y,
        }),
    ))
}

pub fn constant_primary_concatenation(s: &str) -> IResult<&str, ConstantPrimary> {
    let (s, x) = constant_concatenation(s)?;
    let (s, y) = opt(bracket(constant_range_expression))(s)?;
    Ok((
        s,
        ConstantPrimary::Concatenation(ConstantPrimaryConcatenation {
            concatenation: x,
            range: y,
        }),
    ))
}

pub fn constant_primary_multiple_concatenation(s: &str) -> IResult<&str, ConstantPrimary> {
    let (s, x) = constant_multiple_concatenation(s)?;
    let (s, y) = opt(bracket(constant_range_expression))(s)?;
    Ok((
        s,
        ConstantPrimary::MultipleConcatenation(ConstantPrimaryMultipleConcatenation {
            concatenation: x,
            range: y,
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
        Primary::Hierarchical(PrimaryHierarchical {
            qualifier: x,
            identifier: y,
            select: z,
        }),
    ))
}

pub fn primary_concatenation(s: &str) -> IResult<&str, Primary> {
    let (s, x) = concatenation(s)?;
    let (s, y) = opt(range_expression)(s)?;
    Ok((
        s,
        Primary::Concatenation(PrimaryConcatenation {
            concatenation: x,
            range: y,
        }),
    ))
}

pub fn primary_multiple_concatenation(s: &str) -> IResult<&str, Primary> {
    let (s, x) = multiple_concatenation(s)?;
    let (s, y) = opt(range_expression)(s)?;
    Ok((
        s,
        Primary::MultipleConcatenation(PrimaryMultipleConcatenation {
            concatenation: x,
            range: y,
        }),
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
    let (s, y) = opt(alt((
        terminated(implicit_class_handle, symbol(".")),
        class_scope,
    )))(s)?;
    Ok((
        s,
        ClassQualifier {
            local: x.is_some(),
            scope: y,
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
        TimeLiteral::UnsignedTimeLiteral(UnsignedTimeLiteral { number: x, unit: y }),
    ))
}

pub fn fixed_point_time_literal(s: &str) -> IResult<&str, TimeLiteral> {
    let (s, x) = fixed_point_number(s)?;
    let (s, y) = time_unit(s)?;
    Ok((
        s,
        TimeLiteral::FixedPointTimeLiteral(FixedPointTimeLiteral { number: x, unit: y }),
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

pub fn implicit_class_handle(s: &str) -> IResult<&str, Scope> {
    let (s, x) = alt((
        map(
            tuple((symbol("this"), symbol("."), symbol("super"))),
            |_| ImplicitClassHandle::ThisSuper,
        ),
        map(symbol("this"), |_| ImplicitClassHandle::This),
        map(symbol("super"), |_| ImplicitClassHandle::Super),
    ))(s)?;
    Ok((s, Scope::ImplicitClassHandle(x)))
}

pub fn bit_select(s: &str) -> IResult<&str, Vec<Expression>> {
    many0(bracket(expression))(s)
}

pub fn select(s: &str) -> IResult<&str, Select> {
    let (s, x) = opt(pair(
        many0(preceded(symbol("."), pair(member_identifier, bit_select))),
        preceded(symbol("."), member_identifier),
    ))(s)?;
    let (s, y) = bit_select(s)?;
    let (s, z) = opt(bracket(part_select_range))(s)?;

    let x = if let Some((x, y)) = x {
        Some(SelectMember {
            upper: x,
            identifier: y,
        })
    } else {
        None
    };

    Ok((
        s,
        Select {
            member: x,
            bit_select: y,
            part_select_range: z,
        },
    ))
}

pub fn nonrange_select(s: &str) -> IResult<&str, Select> {
    let (s, x) = opt(pair(
        many0(preceded(symbol("."), pair(member_identifier, bit_select))),
        preceded(symbol("."), member_identifier),
    ))(s)?;
    let (s, y) = bit_select(s)?;

    let x = if let Some((x, y)) = x {
        Some(SelectMember {
            upper: x,
            identifier: y,
        })
    } else {
        None
    };

    Ok((
        s,
        Select {
            member: x,
            bit_select: y,
            part_select_range: None,
        },
    ))
}

pub fn constant_bit_select(s: &str) -> IResult<&str, Vec<ConstantExpression>> {
    many0(bracket(constant_expression))(s)
}

pub fn constant_select(s: &str) -> IResult<&str, ConstantSelect> {
    let (s, x) = opt(pair(
        many0(preceded(symbol("."), pair(member_identifier, bit_select))),
        preceded(symbol("."), member_identifier),
    ))(s)?;
    let (s, y) = constant_bit_select(s)?;
    let (s, z) = opt(bracket(constant_part_select_range))(s)?;

    let x = if let Some((x, y)) = x {
        Some(SelectMember {
            upper: x,
            identifier: y,
        })
    } else {
        None
    };

    Ok((
        s,
        ConstantSelect {
            member: x,
            bit_select: y,
            part_select_range: z,
        },
    ))
}

pub fn constant_cast(s: &str) -> IResult<&str, ConstantCast> {
    let (s, x) = casting_type(s)?;
    let (s, _) = symbol("'")(s)?;
    let (s, y) = paren(constant_expression)(s)?;
    Ok((
        s,
        ConstantCast {
            r#type: x,
            expression: y,
        },
    ))
}

pub fn constant_let_expression(s: &str) -> IResult<&str, LetExpression> {
    let_expression(s)
}

pub fn cast(s: &str) -> IResult<&str, Cast> {
    let (s, x) = casting_type(s)?;
    let (s, _) = symbol("'")(s)?;
    let (s, y) = paren(expression)(s)?;
    Ok((
        s,
        Cast {
            r#type: x,
            expression: y,
        },
    ))
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
