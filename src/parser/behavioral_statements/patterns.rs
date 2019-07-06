use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum Pattern<'a> {
    VariableIdentifier(Box<Identifier<'a>>),
    Asterisk,
    ConstantExpression(Box<ConstantExpression<'a>>),
    Tagged(Box<(Identifier<'a>, Option<Pattern<'a>>)>),
    Pattern(Box<Vec<Pattern<'a>>>),
    MemberPattern(Box<Vec<(Identifier<'a>, Pattern<'a>)>>),
}

#[derive(Debug)]
pub enum AssignmentPattern<'a> {
    Expression(Vec<Expression<'a>>),
    StructurePatternKey(Vec<(StructurePatternKey<'a>, Expression<'a>)>),
    ArrayPatternKey(Vec<(ArrayPatternKey<'a>, Expression<'a>)>),
    ConstantExpression((ConstantExpression<'a>, Vec<Expression<'a>>)),
}

#[derive(Debug)]
pub enum StructurePatternKey<'a> {
    Identifier(Identifier<'a>),
    PatternKey(AssignmentPatternKey<'a>),
}

#[derive(Debug)]
pub enum ArrayPatternKey<'a> {
    Expression(ConstantExpression<'a>),
    PatternKey(AssignmentPatternKey<'a>),
}

#[derive(Debug)]
pub enum AssignmentPatternKey<'a> {
    SimpleType(SimpleType<'a>),
    Default,
}

#[derive(Debug)]
pub struct AssignmentPatternExpression<'a> {
    pub r#type: Option<AssignmentPatternExpressionType<'a>>,
    pub pattern: AssignmentPattern<'a>,
}

#[derive(Debug)]
pub enum AssignmentPatternExpressionType<'a> {
    Type(ScopedIdentifier<'a>),
    Parameter(ScopedIdentifier<'a>),
    IntegerAtom(IntegerAtomType<'a>),
    TypeReference(TypeReference<'a>),
}

#[derive(Debug)]
pub struct AssignmentPatternNetLvalue<'a> {
    pub lvalue: Vec<NetLvalue<'a>>,
}

#[derive(Debug)]
pub struct AssignmentPatternVariableLvalue<'a> {
    pub lvalue: Vec<VariableLvalue<'a>>,
}

// -----------------------------------------------------------------------------

pub fn pattern(s: &str) -> IResult<&str, Pattern> {
    alt((
        map(preceded(symbol("."), variable_identifier), |x| {
            Pattern::VariableIdentifier(Box::new(x))
        }),
        map(symbol(".*"), |_| Pattern::Asterisk),
        map(constant_expression, |x| {
            Pattern::ConstantExpression(Box::new(x))
        }),
        map(
            preceded(symbol("tagged"), pair(member_identifier, opt(pattern))),
            |x| Pattern::Tagged(Box::new(x)),
        ),
        map(
            apostrophe_brace(separated_nonempty_list(symbol(","), pattern)),
            |x| Pattern::Pattern(Box::new(x)),
        ),
        map(
            apostrophe_brace(separated_nonempty_list(
                symbol(","),
                pair(member_identifier, preceded(symbol(":"), pattern)),
            )),
            |x| Pattern::MemberPattern(Box::new(x)),
        ),
    ))(s)
}

pub fn assignment_pattern(s: &str) -> IResult<&str, AssignmentPattern> {
    alt((
        map(
            apostrophe_brace(separated_nonempty_list(symbol(","), expression)),
            |x| AssignmentPattern::Expression(x),
        ),
        map(
            apostrophe_brace(separated_nonempty_list(
                symbol(","),
                pair(structure_pattern_key, preceded(symbol(":"), expression)),
            )),
            |x| AssignmentPattern::StructurePatternKey(x),
        ),
        map(
            apostrophe_brace(separated_nonempty_list(
                symbol(","),
                pair(array_pattern_key, preceded(symbol(":"), expression)),
            )),
            |x| AssignmentPattern::ArrayPatternKey(x),
        ),
        map(
            apostrophe_brace(pair(
                constant_expression,
                brace(separated_nonempty_list(symbol(","), expression)),
            )),
            |x| AssignmentPattern::ConstantExpression(x),
        ),
    ))(s)
}

pub fn structure_pattern_key(s: &str) -> IResult<&str, StructurePatternKey> {
    alt((
        map(member_identifier, |x| StructurePatternKey::Identifier(x)),
        map(assignment_pattern_key, |x| {
            StructurePatternKey::PatternKey(x)
        }),
    ))(s)
}

pub fn array_pattern_key(s: &str) -> IResult<&str, ArrayPatternKey> {
    alt((
        map(constant_expression, |x| ArrayPatternKey::Expression(x)),
        map(assignment_pattern_key, |x| ArrayPatternKey::PatternKey(x)),
    ))(s)
}

pub fn assignment_pattern_key(s: &str) -> IResult<&str, AssignmentPatternKey> {
    alt((
        map(simple_type, |x| AssignmentPatternKey::SimpleType(x)),
        map(symbol("default"), |_| AssignmentPatternKey::Default),
    ))(s)
}

pub fn assignment_pattern_expression(s: &str) -> IResult<&str, AssignmentPatternExpression> {
    let (s, x) = opt(assignment_pattern_expression_type)(s)?;
    let (s, y) = assignment_pattern(s)?;
    Ok((
        s,
        AssignmentPatternExpression {
            r#type: x,
            pattern: y,
        },
    ))
}

pub fn assignment_pattern_expression_type(
    s: &str,
) -> IResult<&str, AssignmentPatternExpressionType> {
    alt((
        map(ps_type_identifier, |x| {
            AssignmentPatternExpressionType::Type(x)
        }),
        map(ps_parameter_identifier, |x| {
            AssignmentPatternExpressionType::Parameter(x)
        }),
        map(integer_atom_type, |x| {
            AssignmentPatternExpressionType::IntegerAtom(x)
        }),
        map(type_reference, |x| {
            AssignmentPatternExpressionType::TypeReference(x)
        }),
    ))(s)
}

pub fn constant_assignment_pattern_expression(
    s: &str,
) -> IResult<&str, AssignmentPatternExpression> {
    assignment_pattern_expression(s)
}

pub fn assignment_pattern_net_lvalue(s: &str) -> IResult<&str, AssignmentPatternNetLvalue> {
    let (s, x) = apostrophe_brace(separated_nonempty_list(symbol(","), net_lvalue))(s)?;
    Ok((s, AssignmentPatternNetLvalue { lvalue: x }))
}

pub fn assignment_pattern_variable_lvalue(
    s: &str,
) -> IResult<&str, AssignmentPatternVariableLvalue> {
    let (s, x) = apostrophe_brace(separated_nonempty_list(symbol(","), variable_lvalue))(s)?;
    Ok((s, AssignmentPatternVariableLvalue { lvalue: x }))
}

// -----------------------------------------------------------------------------
