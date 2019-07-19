use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
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

#[derive(Debug, Node)]
pub struct ConstantPrimaryPsParameter<'a> {
    pub nodes: (PsParameterIdentifier<'a>, ConstantSelect<'a>),
}

#[derive(Debug, Node)]
pub struct ConstantPrimarySpecparam<'a> {
    pub nodes: (
        SpecparamIdentifier<'a>,
        Option<Bracket<'a, ConstantRangeExpression<'a>>>,
    ),
}

#[derive(Debug, Node)]
pub struct ConstantPrimaryFormalPort<'a> {
    pub nodes: (FormalPortIdentifier<'a>, ConstantSelect<'a>),
}

#[derive(Debug, Node)]
pub struct ConstantPrimaryEnum<'a> {
    pub nodes: (PackageScopeOrClassScope<'a>, EnumIdentifier<'a>),
}

#[derive(Debug, Node)]
pub struct ConstantPrimaryConcatenation<'a> {
    pub nodes: (
        ConstantConcatenation<'a>,
        Option<Bracket<'a, ConstantRangeExpression<'a>>>,
    ),
}

#[derive(Debug, Node)]
pub struct ConstantPrimaryMultipleConcatenation<'a> {
    pub nodes: (
        ConstantMultipleConcatenation<'a>,
        Option<Bracket<'a, ConstantRangeExpression<'a>>>,
    ),
}

#[derive(Debug, Node)]
pub struct ConstantPrimaryMintypmaxExpression<'a> {
    pub nodes: (Paren<'a, ConstantMintypmaxExpression<'a>>,),
}

#[derive(Debug, Node)]
pub enum ModulePathPrimary<'a> {
    Number(Number<'a>),
    Identifier(Identifier<'a>),
    ModulePathConcatenation(ModulePathConcatenation<'a>),
    ModulePathMultipleConcatenation(ModulePathMultipleConcatenation<'a>),
    FunctionSubroutineCall(FunctionSubroutineCall<'a>),
    Mintypmax(ModulePathPrimaryMintypmax<'a>),
}

#[derive(Debug, Node)]
pub struct ModulePathPrimaryMintypmax<'a> {
    pub nodes: (Paren<'a, ModulePathMintypmaxExpression<'a>>,),
}

#[derive(Debug, Node)]
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

#[derive(Debug, Node)]
pub struct PrimaryHierarchical<'a> {
    pub nodes: (
        Option<ClassQualifierOrPackageScope<'a>>,
        HierarchicalIdentifier<'a>,
        Select<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct PrimaryConcatenation<'a> {
    pub nodes: (Concatenation<'a>, Option<Bracket<'a, RangeExpression<'a>>>),
}

#[derive(Debug, Node)]
pub struct PrimaryMultipleConcatenation<'a> {
    pub nodes: (
        MultipleConcatenation<'a>,
        Option<Bracket<'a, RangeExpression<'a>>>,
    ),
}

#[derive(Debug, Node)]
pub struct PrimaryMintypmaxExpression<'a> {
    pub nodes: (Paren<'a, MintypmaxExpression<'a>>,),
}

#[derive(Debug, Node)]
pub enum ClassQualifierOrPackageScope<'a> {
    ClassQualifier(ClassQualifier<'a>),
    PackageScope(PackageScope<'a>),
}

#[derive(Debug, Node)]
pub struct ClassQualifier<'a> {
    pub nodes: (
        Option<Local<'a>>,
        Option<ImplicitClassHandleOrClassScope<'a>>,
    ),
}

#[derive(Debug, Node)]
pub enum RangeExpression<'a> {
    Expression(Expression<'a>),
    PartSelectRange(PartSelectRange<'a>),
}

#[derive(Debug, Node)]
pub enum PrimaryLiteral<'a> {
    Number(Number<'a>),
    TimeLiteral(TimeLiteral<'a>),
    UnbasedUnsizedLiteral(UnbasedUnsizedLiteral<'a>),
    StringLiteral(StringLiteral<'a>),
}

#[derive(Debug, Node)]
pub enum TimeLiteral<'a> {
    Unsigned(TimeLiteralUnsigned<'a>),
    FixedPoint(TimeLiteralFixedPoint<'a>),
}

#[derive(Debug, Node)]
pub struct TimeLiteralUnsigned<'a> {
    pub nodes: (UnsignedNumber<'a>, TimeUnit<'a>),
}

#[derive(Debug, Node)]
pub struct TimeLiteralFixedPoint<'a> {
    pub nodes: (FixedPointNumber<'a>, TimeUnit<'a>),
}

#[derive(Debug, Node)]
pub enum TimeUnit<'a> {
    S(Symbol<'a>),
    MS(Symbol<'a>),
    US(Symbol<'a>),
    NS(Symbol<'a>),
    PS(Symbol<'a>),
    FS(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum ImplicitClassHandle<'a> {
    This(Symbol<'a>),
    Super(Symbol<'a>),
    ThisSuper((Symbol<'a>, Symbol<'a>, Symbol<'a>)),
}

#[derive(Debug, Node)]
pub struct BitSelect<'a> {
    nodes: (Vec<Bracket<'a, Expression<'a>>>,),
}

#[derive(Debug, Node)]
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

#[derive(Debug, Node)]
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

#[derive(Debug, Node)]
pub struct ConstantBitSelect<'a> {
    nodes: (Vec<Bracket<'a, ConstantExpression<'a>>>,),
}

#[derive(Debug, Node)]
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

#[derive(Debug, Node)]
pub struct ConstantCast<'a> {
    pub nodes: (
        CastingType<'a>,
        Symbol<'a>,
        Paren<'a, ConstantExpression<'a>>,
    ),
}

#[derive(Debug, Node)]
pub struct ConstantLetExpression<'a> {
    pub nodes: (LetExpression<'a>,),
}

#[derive(Debug, Node)]
pub struct Cast<'a> {
    pub nodes: (CastingType<'a>, Symbol<'a>, Paren<'a, Expression<'a>>),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn constant_primary(s: Span) -> IResult<Span, ConstantPrimary> {
    alt((
        map(keyword("null"), |x| ConstantPrimary::Null(x)),
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
    ))(s)
}

#[parser]
pub fn constant_primary_ps_parameter(s: Span) -> IResult<Span, ConstantPrimary> {
    let (s, a) = ps_parameter_identifier(s)?;
    let (s, b) = constant_select(s)?;
    Ok((
        s,
        ConstantPrimary::PsParameter(ConstantPrimaryPsParameter { nodes: (a, b) }),
    ))
}

#[parser]
pub fn constant_primary_specparam(s: Span) -> IResult<Span, ConstantPrimary> {
    let (s, a) = specparam_identifier(s)?;
    let (s, b) = opt(bracket(constant_range_expression))(s)?;
    Ok((
        s,
        ConstantPrimary::Specparam(ConstantPrimarySpecparam { nodes: (a, b) }),
    ))
}

#[parser]
pub fn constant_primary_formal_port(s: Span) -> IResult<Span, ConstantPrimary> {
    let (s, a) = formal_port_identifier(s)?;
    let (s, b) = constant_select(s)?;
    Ok((
        s,
        ConstantPrimary::FormalPort(ConstantPrimaryFormalPort { nodes: (a, b) }),
    ))
}

#[parser]
pub fn constant_primary_enum(s: Span) -> IResult<Span, ConstantPrimary> {
    let (s, a) = package_scope_or_class_scope(s)?;
    let (s, b) = enum_identifier(s)?;
    Ok((
        s,
        ConstantPrimary::Enum(ConstantPrimaryEnum { nodes: (a, b) }),
    ))
}

#[parser]
pub fn constant_primary_concatenation(s: Span) -> IResult<Span, ConstantPrimary> {
    let (s, a) = constant_concatenation(s)?;
    let (s, b) = opt(bracket(constant_range_expression))(s)?;
    Ok((
        s,
        ConstantPrimary::Concatenation(ConstantPrimaryConcatenation { nodes: (a, b) }),
    ))
}

#[parser]
pub fn constant_primary_multiple_concatenation(s: Span) -> IResult<Span, ConstantPrimary> {
    let (s, a) = constant_multiple_concatenation(s)?;
    let (s, b) = opt(bracket(constant_range_expression))(s)?;
    Ok((
        s,
        ConstantPrimary::MultipleConcatenation(ConstantPrimaryMultipleConcatenation {
            nodes: (a, b),
        }),
    ))
}

#[parser]
pub fn constant_primary_mintypmax_expression(s: Span) -> IResult<Span, ConstantPrimary> {
    let (s, a) = paren(constant_mintypmax_expression)(s)?;
    Ok((
        s,
        ConstantPrimary::MintypmaxExpression(ConstantPrimaryMintypmaxExpression { nodes: (a,) }),
    ))
}

#[parser]
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

#[parser]
pub fn module_path_primary_mintypmax_expression(s: Span) -> IResult<Span, ModulePathPrimary> {
    let (s, a) = paren(module_path_mintypmax_expression)(s)?;
    Ok((
        s,
        ModulePathPrimary::Mintypmax(ModulePathPrimaryMintypmax { nodes: (a,) }),
    ))
}

#[parser]
pub fn primary(s: Span) -> IResult<Span, Primary> {
    alt((
        map(keyword("this"), |x| Primary::This(x)),
        map(symbol("$"), |x| Primary::Dollar(x)),
        map(keyword("null"), |x| Primary::Null(x)),
        map(primary_literal, |x| Primary::PrimaryLiteral(x)),
        primary_hierarchical,
        map(empty_unpacked_array_concatenation, |x| {
            Primary::EmptyUnpackedArrayConcatenation(x)
        }),
        primary_concatenation,
        map(function_subroutine_call, |x| {
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
    ))(s)
}

#[parser]
pub fn primary_hierarchical(s: Span) -> IResult<Span, Primary> {
    let (s, a) = opt(class_qualifier_or_package_scope)(s)?;
    let (s, b) = hierarchical_identifier(s)?;
    let (s, c) = select(s)?;
    Ok((
        s,
        Primary::Hierarchical(PrimaryHierarchical { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn primary_concatenation(s: Span) -> IResult<Span, Primary> {
    let (s, a) = concatenation(s)?;
    let (s, b) = opt(bracket(range_expression))(s)?;
    Ok((
        s,
        Primary::Concatenation(PrimaryConcatenation { nodes: (a, b) }),
    ))
}

#[parser]
pub fn primary_multiple_concatenation(s: Span) -> IResult<Span, Primary> {
    let (s, a) = multiple_concatenation(s)?;
    let (s, b) = opt(bracket(range_expression))(s)?;
    Ok((
        s,
        Primary::MultipleConcatenation(PrimaryMultipleConcatenation { nodes: (a, b) }),
    ))
}

#[parser]
pub fn primary_mintypmax_expression(s: Span) -> IResult<Span, Primary> {
    let (s, a) = paren(mintypmax_expression)(s)?;
    Ok((
        s,
        Primary::MintypmaxExpression(PrimaryMintypmaxExpression { nodes: (a,) }),
    ))
}

#[parser]
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

#[parser(MaybeRecursive)]
pub fn class_qualifier(s: Span) -> IResult<Span, ClassQualifier> {
    let (s, a) = opt(local)(s)?;
    let (s, b) = opt(implicit_class_handle_or_class_scope)(s)?;
    Ok((s, ClassQualifier { nodes: (a, b) }))
}

#[parser]
pub fn range_expression(s: Span) -> IResult<Span, RangeExpression> {
    alt((
        map(expression, |x| RangeExpression::Expression(x)),
        map(part_select_range, |x| RangeExpression::PartSelectRange(x)),
    ))(s)
}

#[parser]
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

#[parser]
pub fn time_literal(s: Span) -> IResult<Span, TimeLiteral> {
    alt((time_literal_unsigned, time_literal_fixed_point))(s)
}

#[parser]
pub fn time_literal_unsigned(s: Span) -> IResult<Span, TimeLiteral> {
    let (s, a) = unsigned_number(s)?;
    let (s, b) = time_unit(s)?;
    Ok((
        s,
        TimeLiteral::Unsigned(TimeLiteralUnsigned { nodes: (a, b) }),
    ))
}

#[parser]
pub fn time_literal_fixed_point(s: Span) -> IResult<Span, TimeLiteral> {
    let (s, a) = fixed_point_number(s)?;
    let (s, b) = time_unit(s)?;
    Ok((
        s,
        TimeLiteral::FixedPoint(TimeLiteralFixedPoint { nodes: (a, b) }),
    ))
}

#[parser]
pub fn time_unit(s: Span) -> IResult<Span, TimeUnit> {
    alt((
        map(keyword("s"), |x| TimeUnit::S(x)),
        map(keyword("ms"), |x| TimeUnit::MS(x)),
        map(keyword("us"), |x| TimeUnit::US(x)),
        map(keyword("ns"), |x| TimeUnit::NS(x)),
        map(keyword("ps"), |x| TimeUnit::PS(x)),
        map(keyword("fs"), |x| TimeUnit::FS(x)),
    ))(s)
}

#[parser]
pub fn implicit_class_handle(s: Span) -> IResult<Span, ImplicitClassHandle> {
    alt((
        map(
            triple(keyword("this"), symbol("."), keyword("super")),
            |(x, y, z)| ImplicitClassHandle::ThisSuper((x, y, z)),
        ),
        map(keyword("this"), |x| ImplicitClassHandle::This(x)),
        map(keyword("super"), |x| ImplicitClassHandle::Super(x)),
    ))(s)
}

#[parser]
pub fn bit_select(s: Span) -> IResult<Span, BitSelect> {
    let (s, a) = many0(bracket(expression))(s)?;
    Ok((s, BitSelect { nodes: (a,) }))
}

#[parser]
pub fn select(s: Span) -> IResult<Span, Select> {
    let (s, a) = opt(triple(
        many0(triple(symbol("."), member_identifier, bit_select)),
        symbol("."),
        member_identifier,
    ))(s)?;
    let (s, b) = bit_select(s)?;
    let (s, c) = opt(bracket(part_select_range))(s)?;
    Ok((s, Select { nodes: (a, b, c) }))
}

#[parser]
pub fn nonrange_select(s: Span) -> IResult<Span, NonrangeSelect> {
    let (s, a) = opt(triple(
        many0(triple(symbol("."), member_identifier, bit_select)),
        symbol("."),
        member_identifier,
    ))(s)?;
    let (s, b) = bit_select(s)?;
    Ok((s, NonrangeSelect { nodes: (a, b) }))
}

#[parser]
pub fn constant_bit_select(s: Span) -> IResult<Span, ConstantBitSelect> {
    let (s, a) = many0(bracket(constant_expression))(s)?;
    Ok((s, ConstantBitSelect { nodes: (a,) }))
}

#[parser]
pub fn constant_select(s: Span) -> IResult<Span, ConstantSelect> {
    let (s, a) = opt(triple(
        many0(triple(symbol("."), member_identifier, constant_bit_select)),
        symbol("."),
        member_identifier,
    ))(s)?;
    let (s, b) = constant_bit_select(s)?;
    let (s, c) = opt(bracket(constant_part_select_range))(s)?;
    Ok((s, ConstantSelect { nodes: (a, b, c) }))
}

#[parser(MaybeRecursive)]
pub fn constant_cast(s: Span) -> IResult<Span, ConstantCast> {
    let (s, a) = casting_type(s)?;
    let (s, b) = symbol("'")(s)?;
    let (s, c) = paren(constant_expression)(s)?;
    Ok((s, ConstantCast { nodes: (a, b, c) }))
}

#[parser]
pub fn constant_let_expression(s: Span) -> IResult<Span, ConstantLetExpression> {
    let (s, a) = let_expression(s)?;
    Ok((s, ConstantLetExpression { nodes: (a,) }))
}

#[parser(MaybeRecursive)]
pub fn cast(s: Span) -> IResult<Span, Cast> {
    let (s, a) = casting_type(s)?;
    let (s, b) = symbol("'")(s)?;
    let (s, c) = paren(expression)(s)?;
    Ok((s, Cast { nodes: (a, b, c) }))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_primary() {
        parser_test!(
            primary,
            "2.1ns",
            Ok((_, Primary::PrimaryLiteral(PrimaryLiteral::TimeLiteral(_))))
        );
        parser_test!(
            primary,
            "40 ps",
            Ok((_, Primary::PrimaryLiteral(PrimaryLiteral::TimeLiteral(_))))
        );
        parser_test!(
            primary,
            "'0",
            Ok(
                (
                    _,
                    Primary::PrimaryLiteral(PrimaryLiteral::UnbasedUnsizedLiteral(_))
                ),
            )
        );
        parser_test!(
            primary,
            "10",
            Ok((_, Primary::PrimaryLiteral(PrimaryLiteral::Number(_))))
        );
        parser_test!(
            primary,
            "\"aaa\"",
            Ok((_, Primary::PrimaryLiteral(PrimaryLiteral::StringLiteral(_))))
        );
        parser_test!(primary, "this", Ok((_, Primary::This(_))));
        parser_test!(primary, "$", Ok((_, Primary::Dollar(_))));
        parser_test!(primary, "null", Ok((_, Primary::Null(_))));
    }
}
