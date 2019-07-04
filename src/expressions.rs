use crate::attributes::*;
use crate::identifiers::*;
use crate::lvalues::*;
use crate::operators::*;
use crate::primaries::*;
use crate::utils::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum IncOrDecExpression<'a> {
    Prefix(IncOrDecExpressionPrefix<'a>),
    Suffix(IncOrDecExpressionSuffix<'a>),
}

#[derive(Debug)]
pub struct IncOrDecExpressionPrefix<'a> {
    pub operator: Operator<'a>,
    pub attribute: Vec<AttributeInstance<'a>>,
    pub lvalue: VariableLvalue<'a>,
}

#[derive(Debug)]
pub struct IncOrDecExpressionSuffix<'a> {
    pub lvalue: VariableLvalue<'a>,
    pub attribute: Vec<AttributeInstance<'a>>,
    pub operator: Operator<'a>,
}

#[derive(Debug)]
pub struct ConditionalExpression<'a> {
    pub predicate: CondPredicate<'a>,
    pub attribute: Vec<AttributeInstance<'a>>,
    pub arg0: Expression<'a>,
    pub arg1: Expression<'a>,
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
    pub operator: Operator<'a>,
    pub attribute: Vec<AttributeInstance<'a>>,
    pub arg0: ConstantPrimary<'a>,
}

#[derive(Debug)]
pub struct ConstantExpressionBinary<'a> {
    pub arg0: ConstantExpression<'a>,
    pub operator: Operator<'a>,
    pub attribute: Vec<AttributeInstance<'a>>,
    pub arg1: ConstantExpression<'a>,
}

#[derive(Debug)]
pub struct ConstantExpressionTernary<'a> {
    pub predicate: ConstantExpression<'a>,
    pub attribute: Vec<AttributeInstance<'a>>,
    pub arg0: ConstantExpression<'a>,
    pub arg1: ConstantExpression<'a>,
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
    Range((ConstantExpression<'a>, ConstantExpression<'a>)),
    IndexedRange((ConstantExpression<'a>, &'a str, ConstantExpression<'a>)),
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
    pub operator: Operator<'a>,
    pub attribute: Vec<AttributeInstance<'a>>,
    pub arg0: Primary<'a>,
}

#[derive(Debug)]
pub struct ExpressionBinary<'a> {
    pub arg0: Expression<'a>,
    pub operator: Operator<'a>,
    pub attribute: Vec<AttributeInstance<'a>>,
    pub arg1: Expression<'a>,
}

#[derive(Debug)]
pub struct TaggedUnionExpression<'a> {
    pub identifier: Identifier<'a>,
    pub expression: Option<Expression<'a>>,
}

#[derive(Debug)]
pub struct InsideExpression<'a> {
    pub expression: Expression<'a>,
    pub open_range_list: OpenRangeList<'a>,
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
    pub predicate: ModulePathExpression<'a>,
    pub attribute: Vec<AttributeInstance<'a>>,
    pub arg0: ModulePathExpression<'a>,
    pub arg1: ModulePathExpression<'a>,
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
    pub operator: Operator<'a>,
    pub attribute: Vec<AttributeInstance<'a>>,
    pub arg0: ModulePathPrimary<'a>,
}

#[derive(Debug)]
pub struct ModulePathExpressionBinary<'a> {
    pub arg0: ModulePathExpression<'a>,
    pub operator: Operator<'a>,
    pub attribute: Vec<AttributeInstance<'a>>,
    pub arg1: ModulePathExpression<'a>,
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
    IndexedRange((Expression<'a>, &'a str, ConstantExpression<'a>)),
}

// -----------------------------------------------------------------------------

pub fn inc_or_dec_expression(s: &str) -> IResult<&str, IncOrDecExpression> {
    alt((inc_or_dec_expression_prefix, inc_or_dec_expression_suffix))(s)
}

pub fn inc_or_dec_expression_prefix(s: &str) -> IResult<&str, IncOrDecExpression> {
    let (s, operator) = inc_or_dec_operator(s)?;
    let (s, attribute) = many0(attribute_instance)(s)?;
    let (s, lvalue) = variable_lvalue(s)?;
    Ok((
        s,
        IncOrDecExpression::Prefix(IncOrDecExpressionPrefix {
            operator,
            attribute,
            lvalue,
        }),
    ))
}

pub fn inc_or_dec_expression_suffix(s: &str) -> IResult<&str, IncOrDecExpression> {
    let (s, lvalue) = variable_lvalue(s)?;
    let (s, attribute) = many0(attribute_instance)(s)?;
    let (s, operator) = inc_or_dec_operator(s)?;
    Ok((
        s,
        IncOrDecExpression::Suffix(IncOrDecExpressionSuffix {
            lvalue,
            attribute,
            operator,
        }),
    ))
}

pub fn conditional_expression(s: &str) -> IResult<&str, ConditionalExpression> {
    let (s, predicate) = cond_predicate(s)?;
    let (s, _) = symbol("?")(s)?;
    let (s, attribute) = many0(attribute_instance)(s)?;
    let (s, arg0) = expression(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, arg1) = expression(s)?;
    Ok((
        s,
        ConditionalExpression {
            predicate,
            attribute,
            arg0,
            arg1,
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
    let (s, operator) = unary_operator(s)?;
    let (s, attribute) = many0(attribute_instance)(s)?;
    let (s, arg0) = constant_primary(s)?;
    Ok((
        s,
        ConstantExpression::Unary(Box::new(ConstantExpressionUnary {
            operator,
            attribute,
            arg0,
        })),
    ))
}

pub fn constant_expression_binary(s: &str) -> IResult<&str, ConstantExpression> {
    let (s, arg0) = constant_expression(s)?;
    let (s, operator) = binary_operator(s)?;
    let (s, attribute) = many0(attribute_instance)(s)?;
    let (s, arg1) = constant_expression(s)?;
    Ok((
        s,
        ConstantExpression::Binary(Box::new(ConstantExpressionBinary {
            arg0,
            operator,
            attribute,
            arg1,
        })),
    ))
}

pub fn constant_expression_ternary(s: &str) -> IResult<&str, ConstantExpression> {
    let (s, predicate) = constant_expression(s)?;
    let (s, _) = symbol("?")(s)?;
    let (s, attribute) = many0(attribute_instance)(s)?;
    let (s, arg0) = constant_expression(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, arg1) = constant_expression(s)?;
    Ok((
        s,
        ConstantExpression::Ternary(Box::new(ConstantExpressionTernary {
            predicate,
            attribute,
            arg0,
            arg1,
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
    alt((constant_range, constant_indexed_range))(s)
}

pub fn constant_range(s: &str) -> IResult<&str, ConstantPartSelectRange> {
    let (s, x) = constant_expression(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, y) = constant_expression(s)?;
    Ok((s, ConstantPartSelectRange::Range((x, y))))
}

pub fn constant_indexed_range(s: &str) -> IResult<&str, ConstantPartSelectRange> {
    let (s, x) = constant_expression(s)?;
    let (s, y) = alt((symbol("+:"), symbol("-:")))(s)?;
    let (s, z) = constant_expression(s)?;
    Ok((s, ConstantPartSelectRange::IndexedRange((x, y, z))))
}

pub fn expression(s: &str) -> IResult<&str, Expression> {
    alt((
        map(primary, |x| Expression::Nullary(Box::new(x))),
        expression_unary,
        map(inc_or_dec_expression, |x| Expression::IncOrDec(Box::new(x))),
        map(
            delimited(symbol("("), operator_assignment, symbol(")")),
            |x| Expression::Assignment(Box::new(x)),
        ),
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
    let (s, operator) = unary_operator(s)?;
    let (s, attribute) = many0(attribute_instance)(s)?;
    let (s, arg0) = primary(s)?;
    Ok((
        s,
        Expression::Unary(Box::new(ExpressionUnary {
            operator,
            attribute,
            arg0,
        })),
    ))
}

pub fn expression_binary(s: &str) -> IResult<&str, Expression> {
    let (s, arg0) = expression(s)?;
    let (s, operator) = binary_operator(s)?;
    let (s, attribute) = many0(attribute_instance)(s)?;
    let (s, arg1) = expression(s)?;
    Ok((
        s,
        Expression::Binary(Box::new(ExpressionBinary {
            arg0,
            operator,
            attribute,
            arg1,
        })),
    ))
}

pub fn tagged_union_expression(s: &str) -> IResult<&str, TaggedUnionExpression> {
    let (s, _) = symbol("tagged")(s)?;
    let (s, identifier) = member_identifier(s)?;
    let (s, expression) = opt(expression)(s)?;
    Ok((
        s,
        TaggedUnionExpression {
            identifier,
            expression,
        },
    ))
}

pub fn inside_expression(s: &str) -> IResult<&str, InsideExpression> {
    let (s, expression) = expression(s)?;
    let (s, _) = symbol("inside")(s)?;
    let (s, open_range_list) = delimited(symbol("{"), open_range_list, symbol("}"))(s)?;
    Ok((
        s,
        InsideExpression {
            expression,
            open_range_list,
        },
    ))
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
    let (s, predicate) = module_path_expression(s)?;
    let (s, _) = symbol("?")(s)?;
    let (s, attribute) = many0(attribute_instance)(s)?;
    let (s, arg0) = module_path_expression(s)?;
    let (s, _) = symbol(":")(s)?;
    let (s, arg1) = module_path_expression(s)?;
    Ok((
        s,
        ModulePathConditionalExpression {
            predicate,
            attribute,
            arg0,
            arg1,
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
    let (s, operator) = unary_module_path_operator(s)?;
    let (s, attribute) = many0(attribute_instance)(s)?;
    let (s, arg0) = module_path_primary(s)?;
    Ok((
        s,
        ModulePathExpression::Unary(Box::new(ModulePathExpressionUnary {
            operator,
            attribute,
            arg0,
        })),
    ))
}

pub fn module_path_expression_binary(s: &str) -> IResult<&str, ModulePathExpression> {
    let (s, arg0) = module_path_expression(s)?;
    let (s, operator) = binary_module_path_operator(s)?;
    let (s, attribute) = many0(attribute_instance)(s)?;
    let (s, arg1) = module_path_expression(s)?;
    Ok((
        s,
        ModulePathExpression::Binary(Box::new(ModulePathExpressionBinary {
            arg0,
            operator,
            attribute,
            arg1,
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
    use super::*;

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
