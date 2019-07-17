use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum IncOrDecExpression<'a> {
    Prefix(IncOrDecExpressionPrefix<'a>),
    Suffix(IncOrDecExpressionSuffix<'a>),
}

#[derive(Debug, Node)]
pub struct IncOrDecExpressionPrefix<'a> {
    pub nodes: (
        IncOrDecOperator<'a>,
        Vec<AttributeInstance<'a>>,
        VariableLvalue<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct IncOrDecExpressionSuffix<'a> {
    pub nodes: (
        VariableLvalue<'a>,
        Vec<AttributeInstance<'a>>,
        IncOrDecOperator<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct ConditionalExpression<'a> {
    pub nodes: (
        CondPredicate<'a>,
        Symbol<'a>,
        Vec<AttributeInstance<'a>>,
        Expression<'a>,
        Symbol<'a>,
        Expression<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum ConstantExpression<'a> {
    ConstantPrimary(Box<ConstantPrimary<'a>>),
    Unary(Box<ConstantExpressionUnary<'a>>),
    Binary(Box<ConstantExpressionBinary<'a>>),
    Ternary(Box<ConstantExpressionTernary<'a>>),
}

#[derive(Debug, Node)]
pub struct ConstantExpressionUnary<'a> {
    pub nodes: (
        UnaryOperator<'a>,
        Vec<AttributeInstance<'a>>,
        ConstantPrimary<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct ConstantExpressionBinary<'a> {
    pub nodes: (
        ConstantExpression<'a>,
        BinaryOperator<'a>,
        Vec<AttributeInstance<'a>>,
        ConstantExpression<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct ConstantExpressionTernary<'a> {
    pub nodes: (
        ConstantExpression<'a>,
        Symbol<'a>,
        Vec<AttributeInstance<'a>>,
        ConstantExpression<'a>,
        Symbol<'a>,
        ConstantExpression<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum ConstantMintypmaxExpression<'a> {
    Unary(ConstantExpression<'a>),
    Ternary(ConstantMintypmaxExpressionTernary<'a>),
}

#[derive(Debug, Node)]
pub struct ConstantMintypmaxExpressionTernary<'a> {
    pub nodes: (
        ConstantExpression<'a>,
        Symbol<'a>,
        ConstantExpression<'a>,
        Symbol<'a>,
        ConstantExpression<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum ConstantParamExpression<'a> {
    ConstantMintypmaxExpression(ConstantMintypmaxExpression<'a>),
    DataType(DataType<'a>),
    Dollar(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum ParamExpression<'a> {
    MintypmaxExpression(MintypmaxExpression<'a>),
    DataType(Box<DataType<'a>>),
    Dollar(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum ConstantRangeExpression<'a> {
    ConstantExpression(ConstantExpression<'a>),
    ConstantPartSelectRange(ConstantPartSelectRange<'a>),
}

#[derive(Debug, Node)]
pub enum ConstantPartSelectRange<'a> {
    ConstantRange(ConstantRange<'a>),
    ConstantIndexedRange(ConstantIndexedRange<'a>),
}

#[derive(Debug, Node)]
pub struct ConstantRange<'a> {
    pub nodes: (ConstantExpression<'a>, Symbol<'a>, ConstantExpression<'a>),
}

#[derive(Debug, Node)]
pub struct ConstantIndexedRange<'a> {
    pub nodes: (ConstantExpression<'a>, Symbol<'a>, ConstantExpression<'a>),
}

#[derive(Debug, Node)]
pub enum Expression<'a> {
    Primary(Box<Primary<'a>>),
    Unary(Box<ExpressionUnary<'a>>),
    IncOrDecExpression(Box<IncOrDecExpression<'a>>),
    OperatorAssignment(Box<ExpressionOperatorAssignment<'a>>),
    Binary(Box<ExpressionBinary<'a>>),
    ConditionalExpression(Box<ConditionalExpression<'a>>),
    InsideExpression(Box<InsideExpression<'a>>),
    TaggedUnionExpression(Box<TaggedUnionExpression<'a>>),
}

#[derive(Debug, Node)]
pub struct ExpressionUnary<'a> {
    pub nodes: (UnaryOperator<'a>, Vec<AttributeInstance<'a>>, Primary<'a>),
}

#[derive(Debug, Node)]
pub struct ExpressionOperatorAssignment<'a> {
    pub nodes: (Paren<'a, OperatorAssignment<'a>>,),
}

#[derive(Debug, Node)]
pub struct ExpressionBinary<'a> {
    pub nodes: (
        Expression<'a>,
        BinaryOperator<'a>,
        Vec<AttributeInstance<'a>>,
        Expression<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct TaggedUnionExpression<'a> {
    pub nodes: (Symbol<'a>, MemberIdentifier<'a>, Option<Expression<'a>>),
}

#[derive(Debug, Node)]
pub struct InsideExpression<'a> {
    pub nodes: (Expression<'a>, Symbol<'a>, Brace<'a, OpenRangeList<'a>>),
}

#[derive(Debug, Node)]
pub enum ValueRange<'a> {
    Expression(Expression<'a>),
    Binary(ValueRangeBinary<'a>),
}

#[derive(Debug, Node)]
pub struct ValueRangeBinary<'a> {
    pub nodes: (Bracket<'a, (Expression<'a>, Symbol<'a>, Expression<'a>)>,),
}

#[derive(Debug, Node)]
pub enum MintypmaxExpression<'a> {
    Expression(Expression<'a>),
    Ternary(MintypmaxExpressionTernary<'a>),
}

#[derive(Debug, Node)]
pub struct MintypmaxExpressionTernary<'a> {
    pub nodes: (
        Expression<'a>,
        Symbol<'a>,
        Expression<'a>,
        Symbol<'a>,
        Expression<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct ModulePathConditionalExpression<'a> {
    pub nodes: (
        ModulePathExpression<'a>,
        Symbol<'a>,
        Vec<AttributeInstance<'a>>,
        ModulePathExpression<'a>,
        Symbol<'a>,
        ModulePathExpression<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum ModulePathExpression<'a> {
    ModulePathPrimary(Box<ModulePathPrimary<'a>>),
    Unary(Box<ModulePathExpressionUnary<'a>>),
    Binary(Box<ModulePathExpressionBinary<'a>>),
    ModulePathConditionalExpression(Box<ModulePathConditionalExpression<'a>>),
}

#[derive(Debug, Node)]
pub struct ModulePathExpressionUnary<'a> {
    pub nodes: (
        UnaryModulePathOperator<'a>,
        Vec<AttributeInstance<'a>>,
        ModulePathPrimary<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct ModulePathExpressionBinary<'a> {
    pub nodes: (
        ModulePathExpression<'a>,
        BinaryModulePathOperator<'a>,
        Vec<AttributeInstance<'a>>,
        ModulePathExpression<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum ModulePathMintypmaxExpression<'a> {
    ModulePathExpression(ModulePathExpression<'a>),
    Ternary(ModulePathMintypmaxExpressionTernary<'a>),
}

#[derive(Debug, Node)]
pub struct ModulePathMintypmaxExpressionTernary<'a> {
    pub nodes: (
        ModulePathExpression<'a>,
        Symbol<'a>,
        ModulePathExpression<'a>,
        Symbol<'a>,
        ModulePathExpression<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum PartSelectRange<'a> {
    ConstantRange(ConstantRange<'a>),
    IndexedRange(IndexedRange<'a>),
}

#[derive(Debug, Node)]
pub struct IndexedRange<'a> {
    pub nodes: (Expression<'a>, Symbol<'a>, ConstantExpression<'a>),
}

#[derive(Debug, Node)]
pub struct GenvarExpression<'a> {
    pub nodes: (ConstantExpression<'a>,),
}

// -----------------------------------------------------------------------------

#[parser]
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

#[parser]
pub fn inc_or_dec_expression_suffix(s: Span) -> IResult<Span, IncOrDecExpression> {
    let (s, a) = variable_lvalue(s)?;
    let (s, b) = many0(attribute_instance)(s)?;
    let (s, c) = inc_or_dec_operator(s)?;
    Ok((
        s,
        IncOrDecExpression::Suffix(IncOrDecExpressionSuffix { nodes: (a, b, c) }),
    ))
}

#[parser]
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

#[parser]
pub fn constant_expression(s: Span) -> IResult<Span, ConstantExpression> {
    alt((
        map(constant_primary, |x| {
            ConstantExpression::ConstantPrimary(Box::new(x))
        }),
        constant_expression_unary,
        constant_expression_binary,
        constant_expression_ternary,
    ))(s)
}

#[parser]
pub fn constant_expression_unary(s: Span) -> IResult<Span, ConstantExpression> {
    let (s, a) = unary_operator(s)?;
    let (s, b) = many0(attribute_instance)(s)?;
    let (s, c) = constant_primary(s)?;
    Ok((
        s,
        ConstantExpression::Unary(Box::new(ConstantExpressionUnary { nodes: (a, b, c) })),
    ))
}

#[parser]
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

#[parser]
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

#[parser]
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

#[parser]
pub fn constant_range(s: Span) -> IResult<Span, ConstantRange> {
    let (s, a) = constant_expression(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = constant_expression(s)?;
    Ok((s, ConstantRange { nodes: (a, b, c) }))
}

#[parser]
pub fn constant_indexed_range(s: Span) -> IResult<Span, ConstantIndexedRange> {
    let (s, a) = constant_expression(s)?;
    let (s, b) = alt((symbol("+:"), symbol("-:")))(s)?;
    let (s, c) = constant_expression(s)?;
    Ok((s, ConstantIndexedRange { nodes: (a, b, c) }))
}

#[parser]
pub fn expression(s: Span) -> IResult<Span, Expression> {
    alt((
        map(primary, |x| Expression::Primary(Box::new(x))),
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
    ))(s)
}

#[parser]
pub fn expression_unary(s: Span) -> IResult<Span, Expression> {
    let (s, x) = unary_operator(s)?;
    let (s, y) = many0(attribute_instance)(s)?;
    let (s, z) = primary(s)?;
    Ok((
        s,
        Expression::Unary(Box::new(ExpressionUnary { nodes: (x, y, z) })),
    ))
}

#[parser]
pub fn expression_operator_assignment(s: Span) -> IResult<Span, Expression> {
    let (s, a) = paren(operator_assignment)(s)?;
    Ok((
        s,
        Expression::OperatorAssignment(Box::new(ExpressionOperatorAssignment { nodes: (a,) })),
    ))
}

#[parser]
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

#[parser]
pub fn tagged_union_expression(s: Span) -> IResult<Span, TaggedUnionExpression> {
    let (s, a) = symbol("tagged")(s)?;
    let (s, b) = member_identifier(s)?;
    let (s, c) = opt(expression)(s)?;
    Ok((s, TaggedUnionExpression { nodes: (a, b, c) }))
}

#[parser]
pub fn inside_expression(s: Span) -> IResult<Span, InsideExpression> {
    let (s, a) = expression(s)?;
    let (s, b) = symbol("inside")(s)?;
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

#[parser]
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

#[parser]
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

#[parser]
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

#[parser]
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

#[parser]
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
