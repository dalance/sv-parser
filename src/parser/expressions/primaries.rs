use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::IResult;
use nom_packrat::packrat_parser;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum ConstantPrimary {
    PrimaryLiteral(Box<PrimaryLiteral>),
    PsParameter(Box<ConstantPrimaryPsParameter>),
    Specparam(Box<ConstantPrimarySpecparam>),
    GenvarIdentifier(Box<GenvarIdentifier>),
    FormalPort(Box<ConstantPrimaryFormalPort>),
    Enum(Box<ConstantPrimaryEnum>),
    Concatenation(Box<ConstantPrimaryConcatenation>),
    MultipleConcatenation(Box<ConstantPrimaryMultipleConcatenation>),
    ConstantFunctionCall(Box<ConstantFunctionCall>),
    ConstantLetExpression(Box<ConstantLetExpression>),
    MintypmaxExpression(Box<ConstantPrimaryMintypmaxExpression>),
    ConstantCast(Box<ConstantCast>),
    ConstantAssignmentPatternExpression(Box<ConstantAssignmentPatternExpression>),
    TypeReference(Box<TypeReference>),
    Null(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub struct ConstantPrimaryPsParameter {
    pub nodes: (PsParameterIdentifier, ConstantSelect),
}

#[derive(Clone, Debug, Node)]
pub struct ConstantPrimarySpecparam {
    pub nodes: (
        SpecparamIdentifier,
        Option<Bracket<ConstantRangeExpression>>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ConstantPrimaryFormalPort {
    pub nodes: (FormalPortIdentifier, ConstantSelect),
}

#[derive(Clone, Debug, Node)]
pub struct ConstantPrimaryEnum {
    pub nodes: (PackageScopeOrClassScope, EnumIdentifier),
}

#[derive(Clone, Debug, Node)]
pub struct ConstantPrimaryConcatenation {
    pub nodes: (
        ConstantConcatenation,
        Option<Bracket<ConstantRangeExpression>>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ConstantPrimaryMultipleConcatenation {
    pub nodes: (
        ConstantMultipleConcatenation,
        Option<Bracket<ConstantRangeExpression>>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ConstantPrimaryMintypmaxExpression {
    pub nodes: (Paren<ConstantMintypmaxExpression>,),
}

#[derive(Clone, Debug, Node)]
pub enum ModulePathPrimary {
    Number(Box<Number>),
    Identifier(Box<Identifier>),
    ModulePathConcatenation(Box<ModulePathConcatenation>),
    ModulePathMultipleConcatenation(Box<ModulePathMultipleConcatenation>),
    FunctionSubroutineCall(Box<FunctionSubroutineCall>),
    Mintypmax(Box<ModulePathPrimaryMintypmax>),
}

#[derive(Clone, Debug, Node)]
pub struct ModulePathPrimaryMintypmax {
    pub nodes: (Paren<ModulePathMintypmaxExpression>,),
}

#[derive(Clone, Debug, Node)]
pub enum Primary {
    PrimaryLiteral(Box<PrimaryLiteral>),
    Hierarchical(Box<PrimaryHierarchical>),
    EmptyUnpackedArrayConcatenation(Box<EmptyUnpackedArrayConcatenation>),
    Concatenation(Box<PrimaryConcatenation>),
    MultipleConcatenation(Box<PrimaryMultipleConcatenation>),
    FunctionSubroutineCall(Box<FunctionSubroutineCall>),
    LetExpression(Box<LetExpression>),
    MintypmaxExpression(Box<PrimaryMintypmaxExpression>),
    Cast(Box<Cast>),
    AssignmentPatternExpression(Box<AssignmentPatternExpression>),
    StreamingConcatenation(Box<StreamingConcatenation>),
    SequenceMethodCall(Box<SequenceMethodCall>),
    This(Box<Keyword>),
    Dollar(Box<Symbol>),
    Null(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub struct PrimaryHierarchical {
    pub nodes: (
        Option<ClassQualifierOrPackageScope>,
        HierarchicalIdentifier,
        Select,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct PrimaryConcatenation {
    pub nodes: (Concatenation, Option<Bracket<RangeExpression>>),
}

#[derive(Clone, Debug, Node)]
pub struct PrimaryMultipleConcatenation {
    pub nodes: (MultipleConcatenation, Option<Bracket<RangeExpression>>),
}

#[derive(Clone, Debug, Node)]
pub struct PrimaryMintypmaxExpression {
    pub nodes: (Paren<MintypmaxExpression>,),
}

#[derive(Clone, Debug, Node)]
pub enum ClassQualifierOrPackageScope {
    ClassQualifier(Box<ClassQualifier>),
    PackageScope(Box<PackageScope>),
}

#[derive(Clone, Debug, Node)]
pub struct ClassQualifier {
    pub nodes: (Option<Local>, Option<ImplicitClassHandleOrClassScope>),
}

#[derive(Clone, Debug, Node)]
pub enum RangeExpression {
    Expression(Box<Expression>),
    PartSelectRange(Box<PartSelectRange>),
}

#[derive(Clone, Debug, Node)]
pub enum PrimaryLiteral {
    Number(Box<Number>),
    TimeLiteral(Box<TimeLiteral>),
    UnbasedUnsizedLiteral(Box<UnbasedUnsizedLiteral>),
    StringLiteral(Box<StringLiteral>),
}

#[derive(Clone, Debug, Node)]
pub enum TimeLiteral {
    Unsigned(Box<TimeLiteralUnsigned>),
    FixedPoint(Box<TimeLiteralFixedPoint>),
}

#[derive(Clone, Debug, Node)]
pub struct TimeLiteralUnsigned {
    pub nodes: (UnsignedNumber, TimeUnit),
}

#[derive(Clone, Debug, Node)]
pub struct TimeLiteralFixedPoint {
    pub nodes: (FixedPointNumber, TimeUnit),
}

#[derive(Clone, Debug, Node)]
pub enum TimeUnit {
    S(Box<Keyword>),
    MS(Box<Keyword>),
    US(Box<Keyword>),
    NS(Box<Keyword>),
    PS(Box<Keyword>),
    FS(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub enum ImplicitClassHandle {
    This(Box<Keyword>),
    Super(Box<Keyword>),
    ThisSuper(Box<(Keyword, Symbol, Keyword)>),
}

#[derive(Clone, Debug, Node)]
pub struct BitSelect {
    nodes: (Vec<Bracket<Expression>>,),
}

#[derive(Clone, Debug, Node)]
pub struct Select {
    pub nodes: (
        Option<(
            Vec<(Symbol, MemberIdentifier, BitSelect)>,
            Symbol,
            MemberIdentifier,
        )>,
        BitSelect,
        Option<Bracket<PartSelectRange>>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct NonrangeSelect {
    pub nodes: (
        Option<(
            Vec<(Symbol, MemberIdentifier, BitSelect)>,
            Symbol,
            MemberIdentifier,
        )>,
        BitSelect,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ConstantBitSelect {
    nodes: (Vec<Bracket<ConstantExpression>>,),
}

#[derive(Clone, Debug, Node)]
pub struct ConstantSelect {
    pub nodes: (
        Option<(
            Vec<(Symbol, MemberIdentifier, ConstantBitSelect)>,
            Symbol,
            MemberIdentifier,
        )>,
        ConstantBitSelect,
        Option<Bracket<ConstantPartSelectRange>>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ConstantCast {
    pub nodes: (CastingType, Symbol, Paren<ConstantExpression>),
}

#[derive(Clone, Debug, Node)]
pub struct ConstantLetExpression {
    pub nodes: (LetExpression,),
}

#[derive(Clone, Debug, Node)]
pub struct Cast {
    pub nodes: (CastingType, Symbol, Paren<Expression>),
}

// -----------------------------------------------------------------------------

#[packrat_parser]
#[parser]
pub fn constant_primary(s: Span) -> IResult<Span, ConstantPrimary> {
    alt((
        map(keyword("null"), |x| ConstantPrimary::Null(Box::new(x))),
        map(primary_literal, |x| {
            ConstantPrimary::PrimaryLiteral(Box::new(x))
        }),
        constant_primary_ps_parameter,
        constant_primary_specparam,
        map(genvar_identifier, |x| {
            ConstantPrimary::GenvarIdentifier(Box::new(x))
        }),
        constant_primary_formal_port,
        constant_primary_enum,
        constant_primary_concatenation,
        constant_primary_multiple_concatenation,
        map(constant_function_call, |x| {
            ConstantPrimary::ConstantFunctionCall(Box::new(x))
        }),
        map(constant_let_expression, |x| {
            ConstantPrimary::ConstantLetExpression(Box::new(x))
        }),
        constant_primary_mintypmax_expression,
        map(constant_cast, |x| {
            ConstantPrimary::ConstantCast(Box::new(x))
        }),
        map(constant_assignment_pattern_expression, |x| {
            ConstantPrimary::ConstantAssignmentPatternExpression(Box::new(x))
        }),
        map(type_reference, |x| {
            ConstantPrimary::TypeReference(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn constant_primary_ps_parameter(s: Span) -> IResult<Span, ConstantPrimary> {
    let (s, a) = ps_parameter_identifier(s)?;
    let (s, b) = constant_select(s)?;
    Ok((
        s,
        ConstantPrimary::PsParameter(Box::new(ConstantPrimaryPsParameter { nodes: (a, b) })),
    ))
}

#[parser]
pub fn constant_primary_specparam(s: Span) -> IResult<Span, ConstantPrimary> {
    let (s, a) = specparam_identifier(s)?;
    let (s, b) = opt(bracket(constant_range_expression))(s)?;
    Ok((
        s,
        ConstantPrimary::Specparam(Box::new(ConstantPrimarySpecparam { nodes: (a, b) })),
    ))
}

#[parser]
pub fn constant_primary_formal_port(s: Span) -> IResult<Span, ConstantPrimary> {
    let (s, a) = formal_port_identifier(s)?;
    let (s, b) = constant_select(s)?;
    Ok((
        s,
        ConstantPrimary::FormalPort(Box::new(ConstantPrimaryFormalPort { nodes: (a, b) })),
    ))
}

#[parser]
pub fn constant_primary_enum(s: Span) -> IResult<Span, ConstantPrimary> {
    let (s, a) = package_scope_or_class_scope(s)?;
    let (s, b) = enum_identifier(s)?;
    Ok((
        s,
        ConstantPrimary::Enum(Box::new(ConstantPrimaryEnum { nodes: (a, b) })),
    ))
}

#[parser]
pub fn constant_primary_concatenation(s: Span) -> IResult<Span, ConstantPrimary> {
    let (s, a) = constant_concatenation(s)?;
    let (s, b) = opt(bracket(constant_range_expression))(s)?;
    Ok((
        s,
        ConstantPrimary::Concatenation(Box::new(ConstantPrimaryConcatenation { nodes: (a, b) })),
    ))
}

#[parser]
pub fn constant_primary_multiple_concatenation(s: Span) -> IResult<Span, ConstantPrimary> {
    let (s, a) = constant_multiple_concatenation(s)?;
    let (s, b) = opt(bracket(constant_range_expression))(s)?;
    Ok((
        s,
        ConstantPrimary::MultipleConcatenation(Box::new(ConstantPrimaryMultipleConcatenation {
            nodes: (a, b),
        })),
    ))
}

#[parser]
pub fn constant_primary_mintypmax_expression(s: Span) -> IResult<Span, ConstantPrimary> {
    let (s, a) = paren(constant_mintypmax_expression)(s)?;
    Ok((
        s,
        ConstantPrimary::MintypmaxExpression(Box::new(ConstantPrimaryMintypmaxExpression {
            nodes: (a,),
        })),
    ))
}

#[parser]
pub fn module_path_primary(s: Span) -> IResult<Span, ModulePathPrimary> {
    alt((
        map(number, |x| ModulePathPrimary::Number(Box::new(x))),
        map(identifier, |x| ModulePathPrimary::Identifier(Box::new(x))),
        map(module_path_concatenation, |x| {
            ModulePathPrimary::ModulePathConcatenation(Box::new(x))
        }),
        map(module_path_multiple_concatenation, |x| {
            ModulePathPrimary::ModulePathMultipleConcatenation(Box::new(x))
        }),
        map(function_subroutine_call, |x| {
            ModulePathPrimary::FunctionSubroutineCall(Box::new(x))
        }),
        module_path_primary_mintypmax_expression,
    ))(s)
}

#[parser]
pub fn module_path_primary_mintypmax_expression(s: Span) -> IResult<Span, ModulePathPrimary> {
    let (s, a) = paren(module_path_mintypmax_expression)(s)?;
    Ok((
        s,
        ModulePathPrimary::Mintypmax(Box::new(ModulePathPrimaryMintypmax { nodes: (a,) })),
    ))
}

#[packrat_parser]
#[parser]
pub fn primary(s: Span) -> IResult<Span, Primary> {
    alt((
        map(keyword("this"), |x| Primary::This(Box::new(x))),
        map(symbol("$"), |x| Primary::Dollar(Box::new(x))),
        map(keyword("null"), |x| Primary::Null(Box::new(x))),
        map(primary_literal, |x| Primary::PrimaryLiteral(Box::new(x))),
        primary_hierarchical,
        map(empty_unpacked_array_concatenation, |x| {
            Primary::EmptyUnpackedArrayConcatenation(Box::new(x))
        }),
        primary_concatenation,
        map(function_subroutine_call, |x| {
            Primary::FunctionSubroutineCall(Box::new(x))
        }),
        map(let_expression, |x| Primary::LetExpression(Box::new(x))),
        primary_mintypmax_expression,
        map(cast, |x| Primary::Cast(Box::new(x))),
        map(assignment_pattern_expression, |x| {
            Primary::AssignmentPatternExpression(Box::new(x))
        }),
        map(streaming_concatenation, |x| {
            Primary::StreamingConcatenation(Box::new(x))
        }),
        map(sequence_method_call, |x| {
            Primary::SequenceMethodCall(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn primary_hierarchical(s: Span) -> IResult<Span, Primary> {
    let (s, a) = opt(class_qualifier_or_package_scope)(s)?;
    let (s, b) = hierarchical_identifier(s)?;
    let (s, c) = select(s)?;
    Ok((
        s,
        Primary::Hierarchical(Box::new(PrimaryHierarchical { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn primary_concatenation(s: Span) -> IResult<Span, Primary> {
    let (s, a) = concatenation(s)?;
    let (s, b) = opt(bracket(range_expression))(s)?;
    Ok((
        s,
        Primary::Concatenation(Box::new(PrimaryConcatenation { nodes: (a, b) })),
    ))
}

#[parser]
pub fn primary_multiple_concatenation(s: Span) -> IResult<Span, Primary> {
    let (s, a) = multiple_concatenation(s)?;
    let (s, b) = opt(bracket(range_expression))(s)?;
    Ok((
        s,
        Primary::MultipleConcatenation(Box::new(PrimaryMultipleConcatenation { nodes: (a, b) })),
    ))
}

#[parser]
pub fn primary_mintypmax_expression(s: Span) -> IResult<Span, Primary> {
    let (s, a) = paren(mintypmax_expression)(s)?;
    Ok((
        s,
        Primary::MintypmaxExpression(Box::new(PrimaryMintypmaxExpression { nodes: (a,) })),
    ))
}

#[parser]
pub fn class_qualifier_or_package_scope(s: Span) -> IResult<Span, ClassQualifierOrPackageScope> {
    alt((
        map(class_qualifier, |x| {
            ClassQualifierOrPackageScope::ClassQualifier(Box::new(x))
        }),
        map(package_scope, |x| {
            ClassQualifierOrPackageScope::PackageScope(Box::new(x))
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
        map(expression, |x| RangeExpression::Expression(Box::new(x))),
        map(part_select_range, |x| {
            RangeExpression::PartSelectRange(Box::new(x))
        }),
    ))(s)
}

#[packrat_parser]
#[parser]
pub fn primary_literal(s: Span) -> IResult<Span, PrimaryLiteral> {
    alt((
        map(time_literal, |x| PrimaryLiteral::TimeLiteral(Box::new(x))),
        map(number, |x| PrimaryLiteral::Number(Box::new(x))),
        map(unbased_unsized_literal, |x| {
            PrimaryLiteral::UnbasedUnsizedLiteral(Box::new(x))
        }),
        map(string_literal, |x| {
            PrimaryLiteral::StringLiteral(Box::new(x))
        }),
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
        TimeLiteral::Unsigned(Box::new(TimeLiteralUnsigned { nodes: (a, b) })),
    ))
}

#[parser]
pub fn time_literal_fixed_point(s: Span) -> IResult<Span, TimeLiteral> {
    let (s, a) = fixed_point_number(s)?;
    let (s, b) = time_unit(s)?;
    Ok((
        s,
        TimeLiteral::FixedPoint(Box::new(TimeLiteralFixedPoint { nodes: (a, b) })),
    ))
}

#[parser]
pub fn time_unit(s: Span) -> IResult<Span, TimeUnit> {
    alt((
        map(keyword("s"), |x| TimeUnit::S(Box::new(x))),
        map(keyword("ms"), |x| TimeUnit::MS(Box::new(x))),
        map(keyword("us"), |x| TimeUnit::US(Box::new(x))),
        map(keyword("ns"), |x| TimeUnit::NS(Box::new(x))),
        map(keyword("ps"), |x| TimeUnit::PS(Box::new(x))),
        map(keyword("fs"), |x| TimeUnit::FS(Box::new(x))),
    ))(s)
}

#[parser]
pub fn implicit_class_handle(s: Span) -> IResult<Span, ImplicitClassHandle> {
    alt((
        map(
            triple(keyword("this"), symbol("."), keyword("super")),
            |(x, y, z)| ImplicitClassHandle::ThisSuper(Box::new((x, y, z))),
        ),
        map(keyword("this"), |x| ImplicitClassHandle::This(Box::new(x))),
        map(keyword("super"), |x| {
            ImplicitClassHandle::Super(Box::new(x))
        }),
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
        parser_test!(primary, "2.1ns ", Ok((_, Primary::PrimaryLiteral(_))));
        parser_test!(primary, "40 ps ", Ok((_, Primary::PrimaryLiteral(_))));
        parser_test!(primary, "'0", Ok((_, Primary::PrimaryLiteral(_))));
        parser_test!(primary, "10", Ok((_, Primary::PrimaryLiteral(_))));
        parser_test!(primary, "\"aaa\"", Ok((_, Primary::PrimaryLiteral(_))));
        parser_test!(primary, "this ", Ok((_, Primary::This(_))));
        parser_test!(primary, "$", Ok((_, Primary::Dollar(_))));
        parser_test!(primary, "null ", Ok((_, Primary::Null(_))));
    }

    #[test]
    fn test_cast() {
        parser_test!(cast, "int'(2.0 * 3.0)", Ok((_, _)));
        parser_test!(cast, "shortint'({8'hFA,8'hCE}) ", Ok((_, _)));
        parser_test!(cast, "signed'(x)", Ok((_, _)));
        parser_test!(cast, "const'(x)", Ok((_, _)));
        parser_test!(cast, "type_t'(x)", Ok((_, _)));
    }
}
