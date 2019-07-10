use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum ConstantPrimary<'a> {
    PrimaryLiteral(PrimaryLiteral<'a>),
    PsParameter(ConstantPrimaryPsParameter<'a>),
    Specparam(ConstantPrimarySpecparam<'a>),
    GenvarIdentifier(GenvarIdentifier<'a>),
    FormalPort(ConstantPrimaryFormalPort<'a>),
    Enum(ConstantPrimaryEnum<'a>),
    Concatenation(ConstantPrimaryConcatenation<'a>),
    MultipleConcatenation(ConstantPrimaryMultipleConcatenation<'a>),
    ConstantFunctionCall(ConstantFunctionCall<'a>),
    ConstantLetExpression(ConstantLetExpression<'a>),
    MintypmaxExpression(ConstantPrimaryMintypmaxExpression<'a>),
    ConstantCast(ConstantCast<'a>),
    ConstantAssignmentPatternExpression(ConstantAssignmentPatternExpression<'a>),
    TypeReference(TypeReference<'a>),
    Null(Symbol<'a>),
}

#[derive(Debug)]
pub struct ConstantPrimaryPsParameter<'a> {
    pub nodes: (PsParameterIdentifier<'a>, ConstantSelect<'a>),
}

#[derive(Debug)]
pub struct ConstantPrimarySpecparam<'a> {
    pub nodes: (
        SpecparamIdentifier<'a>,
        Option<Bracket<'a, ConstantRangeExpression<'a>>>,
    ),
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
        Option<Bracket<'a, ConstantRangeExpression<'a>>>,
    ),
}

#[derive(Debug)]
pub struct ConstantPrimaryMultipleConcatenation<'a> {
    pub nodes: (
        ConstantMultipleConcatenation<'a>,
        Option<Bracket<'a, ConstantRangeExpression<'a>>>,
    ),
}

#[derive(Debug)]
pub struct ConstantPrimaryMintypmaxExpression<'a> {
    pub nodes: (Paren<'a, ConstantMintypmaxExpression<'a>>,),
}

#[derive(Debug)]
pub enum ModulePathPrimary<'a> {
    Number(Number<'a>),
    Identifier(Identifier<'a>),
    ModulePathConcatenation(ModulePathConcatenation<'a>),
    ModulePathMultipleConcatenation(ModulePathMultipleConcatenation<'a>),
    FunctionSubroutineCall(FunctionSubroutineCall<'a>),
    Mintypmax(ModulePathPrimaryMintypmax<'a>),
}

#[derive(Debug)]
pub struct ModulePathPrimaryMintypmax<'a> {
    pub nodes: (Paren<'a, ModulePathMintypmaxExpression<'a>>,),
}

#[derive(Debug)]
pub enum Primary<'a> {
    PrimaryLiteral(PrimaryLiteral<'a>),
    Hierarchical(PrimaryHierarchical<'a>),
    EmptyUnpackedArrayConcatenation(EmptyUnpackedArrayConcatenation<'a>),
    Concatenation(PrimaryConcatenation<'a>),
    MultipleConcatenation(PrimaryMultipleConcatenation<'a>),
    FunctionSubroutineCall(FunctionSubroutineCall<'a>),
    LetExpression(LetExpression<'a>),
    MintypmaxExpression(PrimaryMintypmaxExpression<'a>),
    Cast(Cast<'a>),
    AssignmentPatternExpression(AssignmentPatternExpression<'a>),
    StreamingConcatenation(StreamingConcatenation<'a>),
    SequenceMethodCall(SequenceMethodCall<'a>),
    This(Symbol<'a>),
    Dollar(Symbol<'a>),
    Null(Symbol<'a>),
}

#[derive(Debug)]
pub struct PrimaryHierarchical<'a> {
    pub nodes: (
        Option<ClassQualifierOrPackageScope<'a>>,
        HierarchicalIdentifier<'a>,
        Select<'a>,
    ),
}

#[derive(Debug)]
pub struct PrimaryConcatenation<'a> {
    pub nodes: (Concatenation<'a>, Option<Bracket<'a, RangeExpression<'a>>>),
}

#[derive(Debug)]
pub struct PrimaryMultipleConcatenation<'a> {
    pub nodes: (
        MultipleConcatenation<'a>,
        Option<Bracket<'a, RangeExpression<'a>>>,
    ),
}

#[derive(Debug)]
pub struct PrimaryMintypmaxExpression<'a> {
    pub nodes: (Paren<'a, MintypmaxExpression<'a>>,),
}

#[derive(Debug)]
pub enum ClassQualifierOrPackageScope<'a> {
    ClassQualifier(ClassQualifier<'a>),
    PackageScope(PackageScope<'a>),
}

#[derive(Debug)]
pub struct ClassQualifier<'a> {
    pub nodes: (
        Option<Local<'a>>,
        Option<ImplicitClassHandleOrClassScope<'a>>,
    ),
}

#[derive(Debug)]
pub struct Local<'a> {
    pub nodes: (Symbol<'a>,),
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
    UnbasedUnsizedLiteral(UnbasedUnsizedLiteral<'a>),
    StringLiteral(StringLiteral<'a>),
}

#[derive(Debug)]
pub enum TimeLiteral<'a> {
    Unsigned(TimeLiteralUnsigned<'a>),
    FixedPoint(TimeLiteralFixedPoint<'a>),
}

#[derive(Debug)]
pub struct TimeLiteralUnsigned<'a> {
    pub nodes: (UnsignedNumber<'a>, TimeUnit<'a>),
}

#[derive(Debug)]
pub struct TimeLiteralFixedPoint<'a> {
    pub nodes: (FixedPointNumber<'a>, TimeUnit<'a>),
}

#[derive(Debug)]
pub enum TimeUnit<'a> {
    S(Symbol<'a>),
    MS(Symbol<'a>),
    US(Symbol<'a>),
    NS(Symbol<'a>),
    PS(Symbol<'a>),
    FS(Symbol<'a>),
}

#[derive(Debug)]
pub enum ImplicitClassHandle<'a> {
    This(Symbol<'a>),
    Super(Symbol<'a>),
    ThisSuper((Symbol<'a>, Symbol<'a>, Symbol<'a>)),
}

#[derive(Debug)]
pub struct BitSelect<'a> {
    nodes: (Vec<Bracket<'a, Expression<'a>>>,),
}

#[derive(Debug)]
pub struct Select<'a> {
    pub nodes: (
        Option<(
            Vec<(Symbol<'a>, MemberIdentifier<'a>, BitSelect<'a>)>,
            Symbol<'a>,
            MemberIdentifier<'a>,
        )>,
        BitSelect<'a>,
        Option<Bracket<'a, PartSelectRange<'a>>>,
    ),
}

#[derive(Debug)]
pub struct NonrangeSelect<'a> {
    pub nodes: (
        Option<(
            Vec<(Symbol<'a>, MemberIdentifier<'a>, BitSelect<'a>)>,
            Symbol<'a>,
            MemberIdentifier<'a>,
        )>,
        BitSelect<'a>,
    ),
}

#[derive(Debug)]
pub struct ConstantBitSelect<'a> {
    nodes: (Vec<Bracket<'a, ConstantExpression<'a>>>,),
}

#[derive(Debug)]
pub struct ConstantSelect<'a> {
    pub nodes: (
        Option<(
            Vec<(Symbol<'a>, MemberIdentifier<'a>, ConstantBitSelect<'a>)>,
            Symbol<'a>,
            MemberIdentifier<'a>,
        )>,
        ConstantBitSelect<'a>,
        Option<Bracket<'a, ConstantPartSelectRange<'a>>>,
    ),
}

#[derive(Debug)]
pub struct ConstantCast<'a> {
    pub nodes: (
        CastingType<'a>,
        Symbol<'a>,
        Paren<'a, ConstantExpression<'a>>,
    ),
}

#[derive(Debug)]
pub struct ConstantLetExpression<'a> {
    pub nodes: (LetExpression<'a>,),
}

#[derive(Debug)]
pub struct Cast<'a> {
    pub nodes: (CastingType<'a>, Symbol<'a>, Paren<'a, Expression<'a>>),
}

// -----------------------------------------------------------------------------

pub fn constant_primary(s: Span) -> IResult<Span, ConstantPrimary> {
    alt((
        map(primary_literal, |x| ConstantPrimary::PrimaryLiteral(x)),
        constant_primary_ps_parameter,
        constant_primary_specparam,
        map(genvar_identifier, |x| ConstantPrimary::GenvarIdentifier(x)),
        constant_primary_formal_port,
        constant_primary_enum,
        constant_primary_concatenation,
        constant_primary_multiple_concatenation,
        map(constant_function_call, |x| {
            ConstantPrimary::ConstantFunctionCall(x)
        }),
        map(constant_let_expression, |x| {
            ConstantPrimary::ConstantLetExpression(x)
        }),
        constant_primary_mintypmax_expression,
        map(constant_cast, |x| ConstantPrimary::ConstantCast(x)),
        map(constant_assignment_pattern_expression, |x| {
            ConstantPrimary::ConstantAssignmentPatternExpression(x)
        }),
        map(type_reference, |x| ConstantPrimary::TypeReference(x)),
        map(symbol("null"), |x| ConstantPrimary::Null(x)),
    ))(s)
}

pub fn constant_primary_ps_parameter(s: Span) -> IResult<Span, ConstantPrimary> {
    let (s, a) = ps_parameter_identifier(s)?;
    let (s, b) = constant_select(s)?;
    Ok((
        s,
        ConstantPrimary::PsParameter(ConstantPrimaryPsParameter { nodes: (a, b) }),
    ))
}

pub fn constant_primary_specparam(s: Span) -> IResult<Span, ConstantPrimary> {
    let (s, a) = specparam_identifier(s)?;
    let (s, b) = opt(bracket2(constant_range_expression))(s)?;
    Ok((
        s,
        ConstantPrimary::Specparam(ConstantPrimarySpecparam { nodes: (a, b) }),
    ))
}

pub fn constant_primary_formal_port(s: Span) -> IResult<Span, ConstantPrimary> {
    let (s, a) = formal_port_identifier(s)?;
    let (s, b) = constant_select(s)?;
    Ok((
        s,
        ConstantPrimary::FormalPort(ConstantPrimaryFormalPort { nodes: (a, b) }),
    ))
}

pub fn constant_primary_enum(s: Span) -> IResult<Span, ConstantPrimary> {
    let (s, a) = package_scope_or_class_scope(s)?;
    let (s, b) = enum_identifier(s)?;
    Ok((
        s,
        ConstantPrimary::Enum(ConstantPrimaryEnum { nodes: (a, b) }),
    ))
}

pub fn constant_primary_concatenation(s: Span) -> IResult<Span, ConstantPrimary> {
    let (s, a) = constant_concatenation(s)?;
    let (s, b) = opt(bracket2(constant_range_expression))(s)?;
    Ok((
        s,
        ConstantPrimary::Concatenation(ConstantPrimaryConcatenation { nodes: (a, b) }),
    ))
}

pub fn constant_primary_multiple_concatenation(s: Span) -> IResult<Span, ConstantPrimary> {
    let (s, a) = constant_multiple_concatenation(s)?;
    let (s, b) = opt(bracket2(constant_range_expression))(s)?;
    Ok((
        s,
        ConstantPrimary::MultipleConcatenation(ConstantPrimaryMultipleConcatenation {
            nodes: (a, b),
        }),
    ))
}

pub fn constant_primary_mintypmax_expression(s: Span) -> IResult<Span, ConstantPrimary> {
    let (s, a) = paren2(constant_mintypmax_expression)(s)?;
    Ok((
        s,
        ConstantPrimary::MintypmaxExpression(ConstantPrimaryMintypmaxExpression { nodes: (a,) }),
    ))
}

pub fn module_path_primary(s: Span) -> IResult<Span, ModulePathPrimary> {
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
        module_path_primary_mintypmax_expression,
    ))(s)
}

pub fn module_path_primary_mintypmax_expression(s: Span) -> IResult<Span, ModulePathPrimary> {
    let (s, a) = paren2(module_path_mintypmax_expression)(s)?;
    Ok((
        s,
        ModulePathPrimary::Mintypmax(ModulePathPrimaryMintypmax { nodes: (a,) }),
    ))
}

pub fn primary(s: Span) -> IResult<Span, Primary> {
    alt((
        map(primary_literal, |x| Primary::PrimaryLiteral(x)),
        primary_hierarchical,
        map(empty_unpacked_array_concatenation, |x| {
            Primary::EmptyUnpackedArrayConcatenation(x)
        }),
        primary_concatenation,
        map(rec(function_subroutine_call, REC_PRIMARY), |x| {
            Primary::FunctionSubroutineCall(x)
        }),
        map(let_expression, |x| Primary::LetExpression(x)),
        primary_mintypmax_expression,
        map(cast, |x| Primary::Cast(x)),
        map(assignment_pattern_expression, |x| {
            Primary::AssignmentPatternExpression(x)
        }),
        map(streaming_concatenation, |x| {
            Primary::StreamingConcatenation(x)
        }),
        map(sequence_method_call, |x| Primary::SequenceMethodCall(x)),
        map(symbol("this"), |x| Primary::This(x)),
        map(symbol("$"), |x| Primary::Dollar(x)),
        map(symbol("null"), |x| Primary::Null(x)),
    ))(s)
}

pub fn primary_hierarchical(s: Span) -> IResult<Span, Primary> {
    let (s, a) = opt(class_qualifier_or_package_scope)(s)?;
    let (s, b) = hierarchical_identifier(s)?;
    let (s, c) = select(s)?;
    Ok((
        s,
        Primary::Hierarchical(PrimaryHierarchical { nodes: (a, b, c) }),
    ))
}

pub fn primary_concatenation(s: Span) -> IResult<Span, Primary> {
    let (s, a) = concatenation(s)?;
    let (s, b) = opt(bracket2(range_expression))(s)?;
    Ok((
        s,
        Primary::Concatenation(PrimaryConcatenation { nodes: (a, b) }),
    ))
}

pub fn primary_multiple_concatenation(s: Span) -> IResult<Span, Primary> {
    let (s, a) = multiple_concatenation(s)?;
    let (s, b) = opt(bracket2(range_expression))(s)?;
    Ok((
        s,
        Primary::MultipleConcatenation(PrimaryMultipleConcatenation { nodes: (a, b) }),
    ))
}

pub fn primary_mintypmax_expression(s: Span) -> IResult<Span, Primary> {
    let (s, a) = paren2(mintypmax_expression)(s)?;
    Ok((
        s,
        Primary::MintypmaxExpression(PrimaryMintypmaxExpression { nodes: (a,) }),
    ))
}

pub fn class_qualifier_or_package_scope(s: Span) -> IResult<Span, ClassQualifierOrPackageScope> {
    alt((
        map(class_qualifier, |x| {
            ClassQualifierOrPackageScope::ClassQualifier(x)
        }),
        map(package_scope, |x| {
            ClassQualifierOrPackageScope::PackageScope(x)
        }),
    ))(s)
}

pub fn class_qualifier(s: Span) -> IResult<Span, ClassQualifier> {
    let (s, a) = opt(symbol("local::"))(s)?;
    let (s, b) = opt(implicit_class_handle_or_class_scope)(s)?;
    Ok((
        s,
        ClassQualifier {
            nodes: (a.map(|x| Local { nodes: (x,) }), b),
        },
    ))
}

pub fn range_expression(s: Span) -> IResult<Span, RangeExpression> {
    alt((
        map(expression, |x| RangeExpression::Expression(x)),
        map(part_select_range, |x| RangeExpression::PartSelectRange(x)),
    ))(s)
}

pub fn primary_literal(s: Span) -> IResult<Span, PrimaryLiteral> {
    alt((
        map(time_literal, |x| PrimaryLiteral::TimeLiteral(x)),
        map(number, |x| PrimaryLiteral::Number(x)),
        map(unbased_unsized_literal, |x| {
            PrimaryLiteral::UnbasedUnsizedLiteral(x)
        }),
        map(string_literal, |x| PrimaryLiteral::StringLiteral(x)),
    ))(s)
}

pub fn time_literal(s: Span) -> IResult<Span, TimeLiteral> {
    alt((time_literal_unsigned, time_literal_fixed_point))(s)
}

pub fn time_literal_unsigned(s: Span) -> IResult<Span, TimeLiteral> {
    let (s, a) = unsigned_number(s)?;
    let (s, b) = time_unit(s)?;
    Ok((
        s,
        TimeLiteral::Unsigned(TimeLiteralUnsigned { nodes: (a, b) }),
    ))
}

pub fn time_literal_fixed_point(s: Span) -> IResult<Span, TimeLiteral> {
    let (s, a) = fixed_point_number(s)?;
    let (s, b) = time_unit(s)?;
    Ok((
        s,
        TimeLiteral::FixedPoint(TimeLiteralFixedPoint { nodes: (a, b) }),
    ))
}

pub fn time_unit(s: Span) -> IResult<Span, TimeUnit> {
    alt((
        map(symbol("s"), |x| TimeUnit::S(x)),
        map(symbol("ms"), |x| TimeUnit::MS(x)),
        map(symbol("us"), |x| TimeUnit::US(x)),
        map(symbol("ns"), |x| TimeUnit::NS(x)),
        map(symbol("ps"), |x| TimeUnit::PS(x)),
        map(symbol("fs"), |x| TimeUnit::FS(x)),
    ))(s)
}

pub fn implicit_class_handle(s: Span) -> IResult<Span, ImplicitClassHandle> {
    alt((
        map(
            triple(symbol("this"), symbol("."), symbol("super")),
            |(x, y, z)| ImplicitClassHandle::ThisSuper((x, y, z)),
        ),
        map(symbol("this"), |x| ImplicitClassHandle::This(x)),
        map(symbol("super"), |x| ImplicitClassHandle::Super(x)),
    ))(s)
}

pub fn bit_select(s: Span) -> IResult<Span, BitSelect> {
    let (s, a) = many0(bracket2(expression))(s)?;
    Ok((s, BitSelect { nodes: (a,) }))
}

pub fn select(s: Span) -> IResult<Span, Select> {
    let (s, a) = opt(triple(
        many0(triple(symbol("."), member_identifier, bit_select)),
        symbol("."),
        member_identifier,
    ))(s)?;
    let (s, b) = bit_select(s)?;
    let (s, c) = opt(bracket2(part_select_range))(s)?;
    Ok((s, Select { nodes: (a, b, c) }))
}

pub fn nonrange_select(s: Span) -> IResult<Span, NonrangeSelect> {
    let (s, a) = opt(triple(
        many0(triple(symbol("."), member_identifier, bit_select)),
        symbol("."),
        member_identifier,
    ))(s)?;
    let (s, b) = bit_select(s)?;
    Ok((s, NonrangeSelect { nodes: (a, b) }))
}

pub fn constant_bit_select(s: Span) -> IResult<Span, ConstantBitSelect> {
    let (s, a) = many0(bracket2(constant_expression))(s)?;
    Ok((s, ConstantBitSelect { nodes: (a,) }))
}

pub fn constant_select(s: Span) -> IResult<Span, ConstantSelect> {
    let (s, a) = opt(triple(
        many0(triple(symbol("."), member_identifier, constant_bit_select)),
        symbol("."),
        member_identifier,
    ))(s)?;
    let (s, b) = constant_bit_select(s)?;
    let (s, c) = opt(bracket2(constant_part_select_range))(s)?;
    Ok((s, ConstantSelect { nodes: (a, b, c) }))
}

pub fn constant_cast(s: Span) -> IResult<Span, ConstantCast> {
    let (s, a) = casting_type(s)?;
    let (s, b) = symbol("'")(s)?;
    let (s, c) = paren2(constant_expression)(s)?;
    Ok((s, ConstantCast { nodes: (a, b, c) }))
}

pub fn constant_let_expression(s: Span) -> IResult<Span, ConstantLetExpression> {
    let (s, a) = let_expression(s)?;
    Ok((s, ConstantLetExpression { nodes: (a,) }))
}

pub fn cast(s: Span) -> IResult<Span, Cast> {
    let (s, a) = casting_type(s)?;
    let (s, b) = symbol("'")(s)?;
    let (s, c) = paren2(expression)(s)?;
    Ok((s, Cast { nodes: (a, b, c) }))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_primary() {
        let ret = all_consuming(primary)(Span::new_extra("2.1ns", 0));
        if let Ok((_, Primary::PrimaryLiteral(PrimaryLiteral::TimeLiteral(_)))) = ret {
        } else {
            assert!(false, "{:?}", ret)
        }
        let ret = all_consuming(primary)(Span::new_extra("40 ps", 0));
        if let Ok((_, Primary::PrimaryLiteral(PrimaryLiteral::TimeLiteral(_)))) = ret {
        } else {
            assert!(false, "{:?}", ret)
        }
        let ret = all_consuming(primary)(Span::new_extra("'0", 0));
        if let Ok((_, Primary::PrimaryLiteral(PrimaryLiteral::UnbasedUnsizedLiteral(_)))) = ret {
        } else {
            assert!(false, "{:?}", ret)
        }
        let ret = all_consuming(primary)(Span::new_extra("10", 0));
        if let Ok((_, Primary::PrimaryLiteral(PrimaryLiteral::Number(_)))) = ret {
        } else {
            assert!(false, "{:?}", ret)
        }
        let ret = all_consuming(primary)(Span::new_extra("\"aaa\"", 0));
        if let Ok((_, Primary::PrimaryLiteral(PrimaryLiteral::StringLiteral(_)))) = ret {
        } else {
            assert!(false, "{:?}", ret)
        }
        let ret = all_consuming(primary)(Span::new_extra("this", 0));
        if let Ok((_, Primary::This(_))) = ret {
        } else {
            assert!(false, "{:?}", ret)
        }
        let ret = all_consuming(primary)(Span::new_extra("$", 0));
        if let Ok((_, Primary::Dollar(_))) = ret {
        } else {
            assert!(false, "{:?}", ret)
        }
        let ret = all_consuming(primary)(Span::new_extra("null", 0));
        if let Ok((_, Primary::Null(_))) = ret {
        } else {
            assert!(false, "{:?}", ret)
        }
    }
}
