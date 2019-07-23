use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum IncOrDecExpression {
    Prefix(IncOrDecExpressionPrefix),
    Suffix(IncOrDecExpressionSuffix),
}

#[derive(Debug, Node)]
pub struct IncOrDecExpressionPrefix {
    pub nodes: (
        IncOrDecOperator,
        Vec<AttributeInstance>,
        VariableLvalue,
    ),
}

#[derive(Debug, Node)]
pub struct IncOrDecExpressionSuffix {
    pub nodes: (
        VariableLvalue,
        Vec<AttributeInstance>,
        IncOrDecOperator,
    ),
}

#[derive(Debug, Node)]
pub struct ConditionalExpression {
    pub nodes: (
        CondPredicate,
        Symbol,
        Vec<AttributeInstance>,
        Expression,
        Symbol,
        Expression,
    ),
}

#[derive(Debug, Node)]
pub enum ConstantExpression {
    ConstantPrimary(Box<ConstantPrimary>),
    Unary(Box<ConstantExpressionUnary>),
    Binary(Box<ConstantExpressionBinary>),
    Ternary(Box<ConstantExpressionTernary>),
}

#[derive(Debug, Node)]
pub struct ConstantExpressionUnary {
    pub nodes: (
        UnaryOperator,
        Vec<AttributeInstance>,
        ConstantPrimary,
    ),
}

#[derive(Debug, Node)]
pub struct ConstantExpressionBinary {
    pub nodes: (
        ConstantExpression,
        BinaryOperator,
        Vec<AttributeInstance>,
        ConstantExpression,
    ),
}

#[derive(Debug, Node)]
pub struct ConstantExpressionTernary {
    pub nodes: (
        ConstantExpression,
        Symbol,
        Vec<AttributeInstance>,
        ConstantExpression,
        Symbol,
        ConstantExpression,
    ),
}

#[derive(Debug, Node)]
pub enum ConstantMintypmaxExpression {
    Unary(ConstantExpression),
    Ternary(ConstantMintypmaxExpressionTernary),
}

#[derive(Debug, Node)]
pub struct ConstantMintypmaxExpressionTernary {
    pub nodes: (
        ConstantExpression,
        Symbol,
        ConstantExpression,
        Symbol,
        ConstantExpression,
    ),
}

#[derive(Debug, Node)]
pub enum ConstantParamExpression {
    ConstantMintypmaxExpression(ConstantMintypmaxExpression),
    DataType(DataType),
    Dollar(Symbol),
}

#[derive(Debug, Node)]
pub enum ParamExpression {
    MintypmaxExpression(MintypmaxExpression),
    DataType(Box<DataType>),
    Dollar(Symbol),
}

#[derive(Debug, Node)]
pub enum ConstantRangeExpression {
    ConstantExpression(ConstantExpression),
    ConstantPartSelectRange(ConstantPartSelectRange),
}

#[derive(Debug, Node)]
pub enum ConstantPartSelectRange {
    ConstantRange(ConstantRange),
    ConstantIndexedRange(ConstantIndexedRange),
}

#[derive(Debug, Node)]
pub struct ConstantRange {
    pub nodes: (ConstantExpression, Symbol, ConstantExpression),
}

#[derive(Debug, Node)]
pub struct ConstantIndexedRange {
    pub nodes: (ConstantExpression, Symbol, ConstantExpression),
}

#[derive(Debug, Node)]
pub enum Expression {
    Primary(Box<Primary>),
    Unary(Box<ExpressionUnary>),
    IncOrDecExpression(Box<IncOrDecExpression>),
    OperatorAssignment(Box<ExpressionOperatorAssignment>),
    Binary(Box<ExpressionBinary>),
    ConditionalExpression(Box<ConditionalExpression>),
    InsideExpression(Box<InsideExpression>),
    TaggedUnionExpression(Box<TaggedUnionExpression>),
}

#[derive(Debug, Node)]
pub struct ExpressionUnary {
    pub nodes: (UnaryOperator, Vec<AttributeInstance>, Primary),
}

#[derive(Debug, Node)]
pub struct ExpressionOperatorAssignment {
    pub nodes: (Paren< OperatorAssignment>,),
}

#[derive(Debug, Node)]
pub struct ExpressionBinary {
    pub nodes: (
        Expression,
        BinaryOperator,
        Vec<AttributeInstance>,
        Expression,
    ),
}

#[derive(Debug, Node)]
pub struct TaggedUnionExpression {
    pub nodes: (Keyword, MemberIdentifier, Option<Expression>),
}

#[derive(Debug, Node)]
pub struct InsideExpression {
    pub nodes: (Expression, Keyword, Brace< OpenRangeList>),
}

#[derive(Debug, Node)]
pub enum ValueRange {
    Expression(Expression),
    Binary(ValueRangeBinary),
}

#[derive(Debug, Node)]
pub struct ValueRangeBinary {
    pub nodes: (Bracket< (Expression, Symbol, Expression)>,),
}

#[derive(Debug, Node)]
pub enum MintypmaxExpression {
    Expression(Expression),
    Ternary(MintypmaxExpressionTernary),
}

#[derive(Debug, Node)]
pub struct MintypmaxExpressionTernary {
    pub nodes: (
        Expression,
        Symbol,
        Expression,
        Symbol,
        Expression,
    ),
}

#[derive(Debug, Node)]
pub struct ModulePathConditionalExpression {
    pub nodes: (
        ModulePathExpression,
        Symbol,
        Vec<AttributeInstance>,
        ModulePathExpression,
        Symbol,
        ModulePathExpression,
    ),
}

#[derive(Debug, Node)]
pub enum ModulePathExpression {
    ModulePathPrimary(Box<ModulePathPrimary>),
    Unary(Box<ModulePathExpressionUnary>),
    Binary(Box<ModulePathExpressionBinary>),
    ModulePathConditionalExpression(Box<ModulePathConditionalExpression>),
}

#[derive(Debug, Node)]
pub struct ModulePathExpressionUnary {
    pub nodes: (
        UnaryModulePathOperator,
        Vec<AttributeInstance>,
        ModulePathPrimary,
    ),
}

#[derive(Debug, Node)]
pub struct ModulePathExpressionBinary {
    pub nodes: (
        ModulePathExpression,
        BinaryModulePathOperator,
        Vec<AttributeInstance>,
        ModulePathExpression,
    ),
}

#[derive(Debug, Node)]
pub enum ModulePathMintypmaxExpression {
    ModulePathExpression(ModulePathExpression),
    Ternary(ModulePathMintypmaxExpressionTernary),
}

#[derive(Debug, Node)]
pub struct ModulePathMintypmaxExpressionTernary {
    pub nodes: (
        ModulePathExpression,
        Symbol,
        ModulePathExpression,
        Symbol,
        ModulePathExpression,
    ),
}

#[derive(Debug, Node)]
pub enum PartSelectRange {
    ConstantRange(ConstantRange),
    IndexedRange(IndexedRange),
}

#[derive(Debug, Node)]
pub struct IndexedRange {
    pub nodes: (Expression, Symbol, ConstantExpression),
}

#[derive(Debug, Node)]
pub struct GenvarExpression {
    pub nodes: (ConstantExpression,),
}

// -----------------------------------------------------------------------------

#[parser(Memoize)]
pub fn inc_or_dec_expression(s: Span) -> IResult<Span, IncOrDecExpression> {
    alt((inc_or_dec_expression_prefix, inc_or_dec_expression_suffix))(s)
}

#[parser]
pub fn inc_or_dec_expression_prefix(s: Span) -> IResult<Span, IncOrDecExpression> {
    let (s, a) = inc_or_dec_operator(s)?;
    let (s, b) = many0(attribute_instance)(s)?;
    let (s, c) = variable_lvalue(s)?;
    Ok((
        s,
        IncOrDecExpression::Prefix(IncOrDecExpressionPrefix { nodes: (a, b, c) }),
    ))
}

#[parser(MaybeRecursive)]
pub fn inc_or_dec_expression_suffix(s: Span) -> IResult<Span, IncOrDecExpression> {
    let (s, a) = variable_lvalue(s)?;
    let (s, b) = many0(attribute_instance)(s)?;
    let (s, c) = inc_or_dec_operator(s)?;
    Ok((
        s,
        IncOrDecExpression::Suffix(IncOrDecExpressionSuffix { nodes: (a, b, c) }),
    ))
}

#[parser(MaybeRecursive, Memoize)]
pub fn conditional_expression(s: Span) -> IResult<Span, ConditionalExpression> {
    let (s, a) = cond_predicate(s)?;
    let (s, b) = symbol("?")(s)?;
    let (s, c) = many0(attribute_instance)(s)?;
    let (s, d) = expression(s)?;
    let (s, e) = symbol(":")(s)?;
    let (s, f) = expression(s)?;
    Ok((
        s,
        ConditionalExpression {
            nodes: (a, b, c, d, e, f),
        },
    ))
}

#[parser(Memoize)]
pub fn constant_expression(s: Span) -> IResult<Span, ConstantExpression> {
    alt((
        constant_expression_unary,
        constant_expression_binary,
        constant_expression_ternary,
        map(constant_primary, |x| {
            ConstantExpression::ConstantPrimary(Box::new(x))
        }),
    ))(s)
}

#[parser(Memoize)]
pub fn constant_expression_unary(s: Span) -> IResult<Span, ConstantExpression> {
    let (s, a) = unary_operator(s)?;
    let (s, b) = many0(attribute_instance)(s)?;
    let (s, c) = constant_primary(s)?;
    Ok((
        s,
        ConstantExpression::Unary(Box::new(ConstantExpressionUnary { nodes: (a, b, c) })),
    ))
}

#[parser(MaybeRecursive, Memoize)]
pub fn constant_expression_binary(s: Span) -> IResult<Span, ConstantExpression> {
    let (s, a) = constant_expression(s)?;
    let (s, b) = binary_operator(s)?;
    let (s, c) = many0(attribute_instance)(s)?;
    let (s, d) = constant_expression(s)?;
    Ok((
        s,
        ConstantExpression::Binary(Box::new(ConstantExpressionBinary {
            nodes: (a, b, c, d),
        })),
    ))
}

#[parser(MaybeRecursive, Memoize)]
pub fn constant_expression_ternary(s: Span) -> IResult<Span, ConstantExpression> {
    let (s, a) = constant_expression(s)?;
    let (s, b) = symbol("?")(s)?;
    let (s, c) = many0(attribute_instance)(s)?;
    let (s, d) = constant_expression(s)?;
    let (s, e) = symbol(":")(s)?;
    let (s, f) = constant_expression(s)?;
    Ok((
        s,
        ConstantExpression::Ternary(Box::new(ConstantExpressionTernary {
            nodes: (a, b, c, d, e, f),
        })),
    ))
}

#[parser]
pub fn constant_mintypmax_expression(s: Span) -> IResult<Span, ConstantMintypmaxExpression> {
    alt((
        constant_mintypmax_expression_ternary,
        map(constant_expression, |x| {
            ConstantMintypmaxExpression::Unary(x)
        }),
    ))(s)
}

#[parser(MaybeRecursive)]
pub fn constant_mintypmax_expression_ternary(
    s: Span,
) -> IResult<Span, ConstantMintypmaxExpression> {
    let (s, a) = constant_expression(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = constant_expression(s)?;
    let (s, d) = symbol(":")(s)?;
    let (s, e) = constant_expression(s)?;
    Ok((
        s,
        ConstantMintypmaxExpression::Ternary(ConstantMintypmaxExpressionTernary {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser]
pub fn constant_param_expression(s: Span) -> IResult<Span, ConstantParamExpression> {
    alt((
        map(symbol("$"), |x| ConstantParamExpression::Dollar(x)),
        map(constant_mintypmax_expression, |x| {
            ConstantParamExpression::ConstantMintypmaxExpression(x)
        }),
        map(data_type, |x| ConstantParamExpression::DataType(x)),
    ))(s)
}

#[parser]
pub fn param_expression(s: Span) -> IResult<Span, ParamExpression> {
    alt((
        map(symbol("$"), |x| ParamExpression::Dollar(x)),
        map(mintypmax_expression, |x| {
            ParamExpression::MintypmaxExpression(x)
        }),
        map(data_type, |x| ParamExpression::DataType(Box::new(x))),
    ))(s)
}

#[parser]
pub fn constant_range_expression(s: Span) -> IResult<Span, ConstantRangeExpression> {
    alt((
        map(constant_part_select_range, |x| {
            ConstantRangeExpression::ConstantPartSelectRange(x)
        }),
        map(constant_expression, |x| {
            ConstantRangeExpression::ConstantExpression(x)
        }),
    ))(s)
}

#[parser]
pub fn constant_part_select_range(s: Span) -> IResult<Span, ConstantPartSelectRange> {
    alt((
        map(constant_range, |x| {
            ConstantPartSelectRange::ConstantRange(x)
        }),
        map(constant_indexed_range, |x| {
            ConstantPartSelectRange::ConstantIndexedRange(x)
        }),
    ))(s)
}

#[parser(MaybeRecursive)]
pub fn constant_range(s: Span) -> IResult<Span, ConstantRange> {
    let (s, a) = constant_expression(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = constant_expression(s)?;
    Ok((s, ConstantRange { nodes: (a, b, c) }))
}

#[parser(MaybeRecursive)]
pub fn constant_indexed_range(s: Span) -> IResult<Span, ConstantIndexedRange> {
    let (s, a) = constant_expression(s)?;
    let (s, b) = alt((symbol("+:"), symbol("-:")))(s)?;
    let (s, c) = constant_expression(s)?;
    Ok((s, ConstantIndexedRange { nodes: (a, b, c) }))
}

#[parser(Memoize)]
pub fn expression(s: Span) -> IResult<Span, Expression> {
    alt((
        expression_unary,
        map(inc_or_dec_expression, |x| {
            Expression::IncOrDecExpression(Box::new(x))
        }),
        expression_operator_assignment,
        expression_binary,
        map(conditional_expression, |x| {
            Expression::ConditionalExpression(Box::new(x))
        }),
        map(inside_expression, |x| {
            Expression::InsideExpression(Box::new(x))
        }),
        map(tagged_union_expression, |x| {
            Expression::TaggedUnionExpression(Box::new(x))
        }),
        map(primary, |x| Expression::Primary(Box::new(x))),
    ))(s)
}

#[parser(Memoize)]
pub fn expression_unary(s: Span) -> IResult<Span, Expression> {
    let (s, x) = unary_operator(s)?;
    let (s, y) = many0(attribute_instance)(s)?;
    let (s, z) = primary(s)?;
    Ok((
        s,
        Expression::Unary(Box::new(ExpressionUnary { nodes: (x, y, z) })),
    ))
}

#[parser(Memoize)]
pub fn expression_operator_assignment(s: Span) -> IResult<Span, Expression> {
    let (s, a) = paren(operator_assignment)(s)?;
    Ok((
        s,
        Expression::OperatorAssignment(Box::new(ExpressionOperatorAssignment { nodes: (a,) })),
    ))
}

#[parser(MaybeRecursive, Memoize)]
pub fn expression_binary(s: Span) -> IResult<Span, Expression> {
    let (s, a) = expression(s)?;
    let (s, b) = binary_operator(s)?;
    let (s, c) = many0(attribute_instance)(s)?;
    let (s, d) = expression(s)?;
    Ok((
        s,
        Expression::Binary(Box::new(ExpressionBinary {
            nodes: (a, b, c, d),
        })),
    ))
}

#[parser(Memoize)]
pub fn tagged_union_expression(s: Span) -> IResult<Span, TaggedUnionExpression> {
    let (s, a) = keyword("tagged")(s)?;
    let (s, b) = member_identifier(s)?;
    let (s, c) = opt(expression)(s)?;
    Ok((s, TaggedUnionExpression { nodes: (a, b, c) }))
}

#[parser(MaybeRecursive, Memoize)]
pub fn inside_expression(s: Span) -> IResult<Span, InsideExpression> {
    let (s, a) = expression(s)?;
    let (s, b) = keyword("inside")(s)?;
    let (s, c) = brace(open_range_list)(s)?;
    Ok((s, InsideExpression { nodes: (a, b, c) }))
}

#[parser]
pub fn value_range(s: Span) -> IResult<Span, ValueRange> {
    alt((
        value_range_binary,
        map(expression, |x| ValueRange::Expression(x)),
    ))(s)
}

#[parser]
pub fn value_range_binary(s: Span) -> IResult<Span, ValueRange> {
    let (s, a) = bracket(triple(expression, symbol(":"), expression))(s)?;
    Ok((s, ValueRange::Binary(ValueRangeBinary { nodes: (a,) })))
}

#[parser]
pub fn mintypmax_expression(s: Span) -> IResult<Span, MintypmaxExpression> {
    alt((
        mintypmax_expression_ternary,
        map(expression, |x| MintypmaxExpression::Expression(x)),
    ))(s)
}

#[parser(MaybeRecursive)]
pub fn mintypmax_expression_ternary(s: Span) -> IResult<Span, MintypmaxExpression> {
    let (s, a) = expression(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = expression(s)?;
    let (s, d) = symbol(":")(s)?;
    let (s, e) = expression(s)?;
    Ok((
        s,
        MintypmaxExpression::Ternary(MintypmaxExpressionTernary {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser(MaybeRecursive)]
pub fn module_path_conditional_expression(
    s: Span,
) -> IResult<Span, ModulePathConditionalExpression> {
    let (s, a) = module_path_expression(s)?;
    let (s, b) = symbol("?")(s)?;
    let (s, c) = many0(attribute_instance)(s)?;
    let (s, d) = module_path_expression(s)?;
    let (s, e) = symbol(":")(s)?;
    let (s, f) = module_path_expression(s)?;
    Ok((
        s,
        ModulePathConditionalExpression {
            nodes: (a, b, c, d, e, f),
        },
    ))
}

#[parser]
pub fn module_path_expression(s: Span) -> IResult<Span, ModulePathExpression> {
    alt((
        map(module_path_primary, |x| {
            ModulePathExpression::ModulePathPrimary(Box::new(x))
        }),
        module_path_expression_unary,
        module_path_expression_binary,
        map(module_path_conditional_expression, |x| {
            ModulePathExpression::ModulePathConditionalExpression(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn module_path_expression_unary(s: Span) -> IResult<Span, ModulePathExpression> {
    let (s, a) = unary_module_path_operator(s)?;
    let (s, b) = many0(attribute_instance)(s)?;
    let (s, c) = module_path_primary(s)?;
    Ok((
        s,
        ModulePathExpression::Unary(Box::new(ModulePathExpressionUnary { nodes: (a, b, c) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn module_path_expression_binary(s: Span) -> IResult<Span, ModulePathExpression> {
    let (s, a) = module_path_expression(s)?;
    let (s, b) = binary_module_path_operator(s)?;
    let (s, c) = many0(attribute_instance)(s)?;
    let (s, d) = module_path_expression(s)?;
    Ok((
        s,
        ModulePathExpression::Binary(Box::new(ModulePathExpressionBinary {
            nodes: (a, b, c, d),
        })),
    ))
}

#[parser]
pub fn module_path_mintypmax_expression(s: Span) -> IResult<Span, ModulePathMintypmaxExpression> {
    alt((
        module_path_mintypmax_expression_ternary,
        map(module_path_expression, |x| {
            ModulePathMintypmaxExpression::ModulePathExpression(x)
        }),
    ))(s)
}

#[parser(MaybeRecursive)]
pub fn module_path_mintypmax_expression_ternary(
    s: Span,
) -> IResult<Span, ModulePathMintypmaxExpression> {
    let (s, a) = module_path_expression(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = module_path_expression(s)?;
    let (s, d) = symbol(":")(s)?;
    let (s, e) = module_path_expression(s)?;
    Ok((
        s,
        ModulePathMintypmaxExpression::Ternary(ModulePathMintypmaxExpressionTernary {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser]
pub fn part_select_range(s: Span) -> IResult<Span, PartSelectRange> {
    alt((
        map(constant_range, |x| PartSelectRange::ConstantRange(x)),
        map(indexed_range, |x| PartSelectRange::IndexedRange(x)),
    ))(s)
}

#[parser(MaybeRecursive)]
pub fn indexed_range(s: Span) -> IResult<Span, IndexedRange> {
    let (s, a) = expression(s)?;
    let (s, b) = alt((symbol("+:"), symbol("-:")))(s)?;
    let (s, c) = constant_expression(s)?;
    Ok((s, IndexedRange { nodes: (a, b, c) }))
}

#[parser]
pub fn genvar_expression(s: Span) -> IResult<Span, GenvarExpression> {
    let (s, a) = constant_expression(s)?;
    Ok((s, GenvarExpression { nodes: (a,) }))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {

    #[test]
    fn test() {}
}
