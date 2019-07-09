use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum IncOrDecExpression<'a> {
    Prefix(IncOrDecExpressionPrefix<'a>),
    Suffix(IncOrDecExpressionSuffix<'a>),
}

#[derive(Debug)]
pub struct IncOrDecExpressionPrefix<'a> {
    pub nodes: (Operator<'a>, Vec<AttributeInstance<'a>>, VariableLvalue<'a>),
}

#[derive(Debug)]
pub struct IncOrDecExpressionSuffix<'a> {
    pub nodes: (VariableLvalue<'a>, Vec<AttributeInstance<'a>>, Operator<'a>),
}

#[derive(Debug)]
pub struct ConditionalExpression<'a> {
    pub nodes: (
        CondPredicate<'a>,
        Vec<AttributeInstance<'a>>,
        Expression<'a>,
        Expression<'a>,
    ),
}

#[derive(Debug)]
pub enum ConstantExpression<'a> {
    Nullary(Box<ConstantPrimary<'a>>),
    Unary(Box<ConstantExpressionUnary<'a>>),
    Binary(Box<ConstantExpressionBinary<'a>>),
    Ternary(Box<ConstantExpressionTernary<'a>>),
}

#[derive(Debug)]
pub struct ConstantExpressionUnary<'a> {
    pub nodes: (
        Operator<'a>,
        Vec<AttributeInstance<'a>>,
        ConstantPrimary<'a>,
    ),
}

#[derive(Debug)]
pub struct ConstantExpressionBinary<'a> {
    pub nodes: (
        ConstantExpression<'a>,
        Operator<'a>,
        Vec<AttributeInstance<'a>>,
        ConstantExpression<'a>,
    ),
}

#[derive(Debug)]
pub struct ConstantExpressionTernary<'a> {
    pub nodes: (
        ConstantExpression<'a>,
        Vec<AttributeInstance<'a>>,
        ConstantExpression<'a>,
        ConstantExpression<'a>,
    ),
}

#[derive(Debug)]
pub enum ConstantMintypmaxExpression<'a> {
    Unary(ConstantExpression<'a>),
    Ternary(
        (
            ConstantExpression<'a>,
            ConstantExpression<'a>,
            ConstantExpression<'a>,
        ),
    ),
}

#[derive(Debug)]
pub enum ConstantParamExpression<'a> {
    Mintypmax(ConstantMintypmaxExpression<'a>),
    DataType(DataType<'a>),
    Dollar,
}

#[derive(Debug)]
pub enum ParamExpression<'a> {
    Mintypmax(MintypmaxExpression<'a>),
    DataType(DataType<'a>),
    Dollar,
}

#[derive(Debug)]
pub enum ConstantRangeExpression<'a> {
    Expression(ConstantExpression<'a>),
    PartSelectRange(ConstantPartSelectRange<'a>),
}

#[derive(Debug)]
pub enum ConstantPartSelectRange<'a> {
    Range(ConstantRange<'a>),
    IndexedRange(ConstantIndexedRange<'a>),
}

#[derive(Debug)]
pub struct ConstantRange<'a> {
    pub nodes: (ConstantExpression<'a>, ConstantExpression<'a>),
}

#[derive(Debug)]
pub struct ConstantIndexedRange<'a> {
    pub nodes: (ConstantExpression<'a>, Operator<'a>, ConstantExpression<'a>),
}

#[derive(Debug)]
pub enum Expression<'a> {
    Nullary(Box<Primary<'a>>),
    Unary(Box<ExpressionUnary<'a>>),
    IncOrDec(Box<IncOrDecExpression<'a>>),
    Assignment(Box<OperatorAssignment<'a>>),
    Binary(Box<ExpressionBinary<'a>>),
    Conditional(Box<ConditionalExpression<'a>>),
    Inside(Box<InsideExpression<'a>>),
    TaggedUnion(Box<TaggedUnionExpression<'a>>),
}

#[derive(Debug)]
pub struct ExpressionUnary<'a> {
    pub nodes: (Operator<'a>, Vec<AttributeInstance<'a>>, Primary<'a>),
}

#[derive(Debug)]
pub struct ExpressionBinary<'a> {
    pub nodes: (
        Expression<'a>,
        Operator<'a>,
        Vec<AttributeInstance<'a>>,
        Expression<'a>,
    ),
}

#[derive(Debug)]
pub struct TaggedUnionExpression<'a> {
    pub nodes: (MemberIdentifier<'a>, Option<Expression<'a>>),
}

#[derive(Debug)]
pub struct InsideExpression<'a> {
    pub nodes: (Expression<'a>, Vec<ValueRange<'a>>),
}

#[derive(Debug)]
pub enum ValueRange<'a> {
    Unary(Expression<'a>),
    Binary((Expression<'a>, Expression<'a>)),
}

#[derive(Debug)]
pub enum MintypmaxExpression<'a> {
    Unary(Expression<'a>),
    Ternary((Expression<'a>, Expression<'a>, Expression<'a>)),
}

#[derive(Debug)]
pub struct ModulePathConditionalExpression<'a> {
    pub nodes: (
        ModulePathExpression<'a>,
        Vec<AttributeInstance<'a>>,
        ModulePathExpression<'a>,
        ModulePathExpression<'a>,
    ),
}

#[derive(Debug)]
pub enum ModulePathExpression<'a> {
    Nullary(Box<ModulePathPrimary<'a>>),
    Unary(Box<ModulePathExpressionUnary<'a>>),
    Binary(Box<ModulePathExpressionBinary<'a>>),
    Conditional(Box<ModulePathConditionalExpression<'a>>),
}

#[derive(Debug)]
pub struct ModulePathExpressionUnary<'a> {
    pub nodes: (
        Operator<'a>,
        Vec<AttributeInstance<'a>>,
        ModulePathPrimary<'a>,
    ),
}

#[derive(Debug)]
pub struct ModulePathExpressionBinary<'a> {
    pub nodes: (
        ModulePathExpression<'a>,
        Operator<'a>,
        Vec<AttributeInstance<'a>>,
        ModulePathExpression<'a>,
    ),
}

#[derive(Debug)]
pub enum ModulePathMintypmaxExpression<'a> {
    Unary(ModulePathExpression<'a>),
    Ternary(
        (
            ModulePathExpression<'a>,
            ModulePathExpression<'a>,
            ModulePathExpression<'a>,
        ),
    ),
}

#[derive(Debug)]
pub enum PartSelectRange<'a> {
    Range((ConstantExpression<'a>, ConstantExpression<'a>)),
    IndexedRange((Expression<'a>, Symbol<'a>, ConstantExpression<'a>)),
}

// -----------------------------------------------------------------------------

pub fn inc_or_dec_expression(s: &str) -> IResult<&str, IncOrDecExpression> {
    alt((inc_or_dec_expression_prefix, inc_or_dec_expression_suffix))(s)
}

pub fn inc_or_dec_expression_prefix(s: &str) -> IResult<&str, IncOrDecExpression> {
    let (s, x) = inc_or_dec_operator(s)?;
    let (s, y) = many0(attribute_instance)(s)?;
    let (s, z) = variable_lvalue(s)?;
    Ok((
        s,
        IncOrDecExpression::Prefix(IncOrDecExpressionPrefix { nodes: (x, y, z) }),
    ))
}

pub fn inc_or_dec_expression_suffix(s: &str) -> IResult<&str, IncOrDecExpression> {
    let (s, x) = variable_lvalue(s)?;
    let (s, y) = many0(attribute_instance)(s)?;
    let (s, z) = inc_or_dec_operator(s)?;
    Ok((
        s,
        IncOrDecExpression::Suffix(IncOrDecExpressionSuffix { nodes: (x, y, z) }),
    ))
}

pub fn conditional_expression(s: &str) -> IResult<&str, ConditionalExpression> {
    let (s, x) = cond_predicate(s)?;
    let (s, _) = symbol("?")(s)?;
    let (s, y) = many0(attribute_instance)(s)?;
    let (s, z) = expression(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, v) = expression(s)?;
    Ok((
        s,
        ConditionalExpression {
            nodes: (x, y, z, v),
        },
    ))
}

pub fn constant_expression(s: &str) -> IResult<&str, ConstantExpression> {
    alt((
        map(constant_primary, |x| {
            ConstantExpression::Nullary(Box::new(x))
        }),
        constant_expression_unary,
        constant_expression_binary,
        constant_expression_ternary,
    ))(s)
}

pub fn constant_expression_unary(s: &str) -> IResult<&str, ConstantExpression> {
    let (s, x) = unary_operator(s)?;
    let (s, y) = many0(attribute_instance)(s)?;
    let (s, z) = constant_primary(s)?;
    Ok((
        s,
        ConstantExpression::Unary(Box::new(ConstantExpressionUnary { nodes: (x, y, z) })),
    ))
}

pub fn constant_expression_binary(s: &str) -> IResult<&str, ConstantExpression> {
    let (s, x) = constant_expression(s)?;
    let (s, y) = binary_operator(s)?;
    let (s, z) = many0(attribute_instance)(s)?;
    let (s, v) = constant_expression(s)?;
    Ok((
        s,
        ConstantExpression::Binary(Box::new(ConstantExpressionBinary {
            nodes: (x, y, z, v),
        })),
    ))
}

pub fn constant_expression_ternary(s: &str) -> IResult<&str, ConstantExpression> {
    let (s, x) = constant_expression(s)?;
    let (s, _) = symbol("?")(s)?;
    let (s, y) = many0(attribute_instance)(s)?;
    let (s, z) = constant_expression(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, v) = constant_expression(s)?;
    Ok((
        s,
        ConstantExpression::Ternary(Box::new(ConstantExpressionTernary {
            nodes: (x, y, z, v),
        })),
    ))
}

pub fn constant_mintypmax_expression(s: &str) -> IResult<&str, ConstantMintypmaxExpression> {
    alt((
        constant_mintypmax_expression_ternary,
        map(constant_expression, |x| {
            ConstantMintypmaxExpression::Unary(x)
        }),
    ))(s)
}

pub fn constant_mintypmax_expression_ternary(
    s: &str,
) -> IResult<&str, ConstantMintypmaxExpression> {
    let (s, x) = constant_expression(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, y) = constant_expression(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, z) = constant_expression(s)?;
    Ok((s, ConstantMintypmaxExpression::Ternary((x, y, z))))
}

pub fn constant_param_expression(s: &str) -> IResult<&str, ConstantParamExpression> {
    alt((
        map(symbol("$"), |_| ConstantParamExpression::Dollar),
        map(constant_mintypmax_expression, |x| {
            ConstantParamExpression::Mintypmax(x)
        }),
        map(data_type, |x| ConstantParamExpression::DataType(x)),
    ))(s)
}

pub fn param_expression(s: &str) -> IResult<&str, ParamExpression> {
    alt((
        map(symbol("$"), |_| ParamExpression::Dollar),
        map(mintypmax_expression, |x| ParamExpression::Mintypmax(x)),
        map(data_type, |x| ParamExpression::DataType(x)),
    ))(s)
}

pub fn constant_range_expression(s: &str) -> IResult<&str, ConstantRangeExpression> {
    alt((
        map(constant_part_select_range, |x| {
            ConstantRangeExpression::PartSelectRange(x)
        }),
        map(constant_expression, |x| {
            ConstantRangeExpression::Expression(x)
        }),
    ))(s)
}

pub fn constant_part_select_range(s: &str) -> IResult<&str, ConstantPartSelectRange> {
    alt((
        map(constant_range, |x| ConstantPartSelectRange::Range(x)),
        map(constant_indexed_range, |x| {
            ConstantPartSelectRange::IndexedRange(x)
        }),
    ))(s)
}

pub fn constant_range(s: &str) -> IResult<&str, ConstantRange> {
    let (s, x) = constant_expression(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, y) = constant_expression(s)?;
    Ok((s, ConstantRange { nodes: (x, y) }))
}

pub fn constant_indexed_range(s: &str) -> IResult<&str, ConstantIndexedRange> {
    let (s, x) = constant_expression(s)?;
    let (s, y) = map(alt((symbol("+:"), symbol("-:"))), |x| Operator {
        nodes: (x,),
    })(s)?;
    let (s, z) = constant_expression(s)?;
    Ok((s, ConstantIndexedRange { nodes: (x, y, z) }))
}

pub fn expression(s: &str) -> IResult<&str, Expression> {
    alt((
        map(primary, |x| Expression::Nullary(Box::new(x))),
        expression_unary,
        map(inc_or_dec_expression, |x| Expression::IncOrDec(Box::new(x))),
        map(paren(operator_assignment), |x| {
            Expression::Assignment(Box::new(x))
        }),
        expression_binary,
        map(conditional_expression, |x| {
            Expression::Conditional(Box::new(x))
        }),
        map(inside_expression, |x| Expression::Inside(Box::new(x))),
        map(tagged_union_expression, |x| {
            Expression::TaggedUnion(Box::new(x))
        }),
    ))(s)
}

pub fn expression_unary(s: &str) -> IResult<&str, Expression> {
    let (s, x) = unary_operator(s)?;
    let (s, y) = many0(attribute_instance)(s)?;
    let (s, z) = primary(s)?;
    Ok((
        s,
        Expression::Unary(Box::new(ExpressionUnary { nodes: (x, y, z) })),
    ))
}

pub fn expression_binary(s: &str) -> IResult<&str, Expression> {
    let (s, x) = expression(s)?;
    let (s, y) = binary_operator(s)?;
    let (s, z) = many0(attribute_instance)(s)?;
    let (s, v) = expression(s)?;
    Ok((
        s,
        Expression::Binary(Box::new(ExpressionBinary {
            nodes: (x, y, z, v),
        })),
    ))
}

pub fn tagged_union_expression(s: &str) -> IResult<&str, TaggedUnionExpression> {
    let (s, _) = symbol("tagged")(s)?;
    let (s, x) = member_identifier(s)?;
    let (s, y) = opt(expression)(s)?;
    Ok((s, TaggedUnionExpression { nodes: (x, y) }))
}

pub fn inside_expression(s: &str) -> IResult<&str, InsideExpression> {
    let (s, x) = expression(s)?;
    let (s, _) = symbol("inside")(s)?;
    let (s, y) = brace(open_range_list)(s)?;
    Ok((s, InsideExpression { nodes: (x, y) }))
}

pub fn value_range(s: &str) -> IResult<&str, ValueRange> {
    alt((
        value_range_binary,
        map(expression, |x| ValueRange::Unary(x)),
    ))(s)
}

pub fn value_range_binary(s: &str) -> IResult<&str, ValueRange> {
    let (s, _) = symbol("[")(s)?;
    let (s, x) = expression(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, y) = expression(s)?;
    let (s, _) = symbol("]")(s)?;
    Ok((s, ValueRange::Binary((x, y))))
}

pub fn mintypmax_expression(s: &str) -> IResult<&str, MintypmaxExpression> {
    alt((
        mintypmax_expression_ternary,
        map(expression, |x| MintypmaxExpression::Unary(x)),
    ))(s)
}

pub fn mintypmax_expression_ternary(s: &str) -> IResult<&str, MintypmaxExpression> {
    let (s, x) = expression(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, y) = expression(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, z) = expression(s)?;
    Ok((s, MintypmaxExpression::Ternary((x, y, z))))
}

pub fn module_path_conditional_expression(
    s: &str,
) -> IResult<&str, ModulePathConditionalExpression> {
    let (s, x) = module_path_expression(s)?;
    let (s, _) = symbol("?")(s)?;
    let (s, y) = many0(attribute_instance)(s)?;
    let (s, z) = module_path_expression(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, v) = module_path_expression(s)?;
    Ok((
        s,
        ModulePathConditionalExpression {
            nodes: (x, y, z, v),
        },
    ))
}

pub fn module_path_expression(s: &str) -> IResult<&str, ModulePathExpression> {
    alt((
        map(module_path_primary, |x| {
            ModulePathExpression::Nullary(Box::new(x))
        }),
        module_path_expression_unary,
        module_path_expression_binary,
        map(module_path_conditional_expression, |x| {
            ModulePathExpression::Conditional(Box::new(x))
        }),
    ))(s)
}

pub fn module_path_expression_unary(s: &str) -> IResult<&str, ModulePathExpression> {
    let (s, x) = unary_module_path_operator(s)?;
    let (s, y) = many0(attribute_instance)(s)?;
    let (s, z) = module_path_primary(s)?;
    Ok((
        s,
        ModulePathExpression::Unary(Box::new(ModulePathExpressionUnary { nodes: (x, y, z) })),
    ))
}

pub fn module_path_expression_binary(s: &str) -> IResult<&str, ModulePathExpression> {
    let (s, x) = module_path_expression(s)?;
    let (s, y) = binary_module_path_operator(s)?;
    let (s, z) = many0(attribute_instance)(s)?;
    let (s, v) = module_path_expression(s)?;
    Ok((
        s,
        ModulePathExpression::Binary(Box::new(ModulePathExpressionBinary {
            nodes: (x, y, z, v),
        })),
    ))
}

pub fn module_path_mintypmax_expression(s: &str) -> IResult<&str, ModulePathMintypmaxExpression> {
    alt((
        module_path_mintypmax_expression_ternary,
        map(module_path_expression, |x| {
            ModulePathMintypmaxExpression::Unary(x)
        }),
    ))(s)
}

pub fn module_path_mintypmax_expression_ternary(
    s: &str,
) -> IResult<&str, ModulePathMintypmaxExpression> {
    let (s, x) = module_path_expression(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, y) = module_path_expression(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, z) = module_path_expression(s)?;
    Ok((s, ModulePathMintypmaxExpression::Ternary((x, y, z))))
}

pub fn part_select_range(s: &str) -> IResult<&str, PartSelectRange> {
    alt((range, indexed_range))(s)
}

pub fn range(s: &str) -> IResult<&str, PartSelectRange> {
    let (s, x) = constant_expression(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, y) = constant_expression(s)?;
    Ok((s, PartSelectRange::Range((x, y))))
}

pub fn indexed_range(s: &str) -> IResult<&str, PartSelectRange> {
    let (s, x) = expression(s)?;
    let (s, y) = alt((symbol("+:"), symbol("-:")))(s)?;
    let (s, z) = constant_expression(s)?;
    Ok((s, PartSelectRange::IndexedRange((x, y, z))))
}

pub fn genvar_expression(s: &str) -> IResult<&str, ConstantExpression> {
    constant_expression(s)
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {

    #[test]
    fn test() {
        // TODO after operator_assignment
        //assert_eq!(
        //    format!(
        //        "{:?}",
        //        all_consuming(expression)("(a:b:c) + (d:e:f)")
        //    ),
        //    ""
        //);
        // TODO after operator_assignment
        //assert_eq!(
        //    format!(
        //        "{:?}",
        //        all_consuming(expression)("val - (32'd 50: 32'd 75: 32'd 100)")
        //    ),
        //    ""
        //);
    }
}
