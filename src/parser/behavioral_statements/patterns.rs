use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum Pattern<'a> {
    Variable(Box<PatternVariable<'a>>),
    Asterisk(Symbol<'a>),
    ConstantExpression(Box<ConstantExpression<'a>>),
    Tagged(Box<PatternTagged<'a>>),
    List(Box<PatternList<'a>>),
    IdentifierList(Box<PatternIdentifierList<'a>>),
}

#[derive(Debug, Node)]
pub struct PatternVariable<'a> {
    pub nodes: (Symbol<'a>, VariableIdentifier<'a>),
}

#[derive(Debug)]
pub struct PatternTagged<'a> {
    pub nodes: (Symbol<'a>, MemberIdentifier<'a>, Option<Pattern<'a>>),
}

#[derive(Debug)]
pub struct PatternList<'a> {
    pub nodes: (ApostropheBrace<'a, List<Symbol<'a>, Pattern<'a>>>,),
}

#[derive(Debug)]
pub struct PatternIdentifierList<'a> {
    pub nodes:
        (ApostropheBrace<'a, List<Symbol<'a>, (MemberIdentifier<'a>, Symbol<'a>, Pattern<'a>)>>,),
}

#[derive(Debug)]
pub enum AssignmentPattern<'a> {
    List(AssignmentPatternList<'a>),
    Structure(AssignmentPatternStructure<'a>),
    Array(AssignmentPatternArray<'a>),
    Repeat(AssignmentPatternRepeat<'a>),
}

#[derive(Debug)]
pub struct AssignmentPatternList<'a> {
    pub nodes: (ApostropheBrace<'a, List<Symbol<'a>, Expression<'a>>>,),
}

#[derive(Debug)]
pub struct AssignmentPatternStructure<'a> {
    pub nodes: (
        ApostropheBrace<
            'a,
            List<Symbol<'a>, (StructurePatternKey<'a>, Symbol<'a>, Expression<'a>)>,
        >,
    ),
}

#[derive(Debug)]
pub struct AssignmentPatternArray<'a> {
    pub nodes: (
        ApostropheBrace<'a, List<Symbol<'a>, (ArrayPatternKey<'a>, Symbol<'a>, Expression<'a>)>>,
    ),
}

#[derive(Debug)]
pub struct AssignmentPatternRepeat<'a> {
    pub nodes: (
        ApostropheBrace<
            'a,
            (
                ConstantExpression<'a>,
                Brace<'a, List<Symbol<'a>, Expression<'a>>>,
            ),
        >,
    ),
}

#[derive(Debug)]
pub enum StructurePatternKey<'a> {
    MemberIdentifier(MemberIdentifier<'a>),
    AssignmentPatternKey(AssignmentPatternKey<'a>),
}

#[derive(Debug)]
pub enum ArrayPatternKey<'a> {
    ConstantExpression(ConstantExpression<'a>),
    AssignmentPatternKey(AssignmentPatternKey<'a>),
}

#[derive(Debug)]
pub enum AssignmentPatternKey<'a> {
    SimpleType(SimpleType<'a>),
    Default(Symbol<'a>),
}

#[derive(Debug)]
pub struct AssignmentPatternExpression<'a> {
    pub nodes: (
        Option<AssignmentPatternExpressionType<'a>>,
        AssignmentPattern<'a>,
    ),
}

#[derive(Debug)]
pub enum AssignmentPatternExpressionType<'a> {
    PsTypeIdentifier(PsTypeIdentifier<'a>),
    PsParameterIdentifier(PsParameterIdentifier<'a>),
    IntegerAtomType(IntegerAtomType),
    TypeReference(TypeReference<'a>),
}

#[derive(Debug)]
pub struct ConstantAssignmentPatternExpression<'a> {
    pub nodes: (AssignmentPatternExpression<'a>,),
}

#[derive(Debug)]
pub struct AssignmentPatternNetLvalue<'a> {
    pub nodes: (ApostropheBrace<'a, List<Symbol<'a>, NetLvalue<'a>>>,),
}

#[derive(Debug)]
pub struct AssignmentPatternVariableLvalue<'a> {
    pub nodes: (ApostropheBrace<'a, List<Symbol<'a>, VariableLvalue<'a>>>,),
}

// -----------------------------------------------------------------------------

pub fn pattern(s: Span) -> IResult<Span, Pattern> {
    alt((
        pattern_variable,
        map(symbol(".*"), |x| Pattern::Asterisk(x)),
        map(constant_expression, |x| {
            Pattern::ConstantExpression(Box::new(x))
        }),
        pattern_tagged,
        pattern_list,
        pattern_identifier_list,
    ))(s)
}

pub fn pattern_variable(s: Span) -> IResult<Span, Pattern> {
    let (s, a) = symbol(".")(s)?;
    let (s, b) = variable_identifier(s)?;
    Ok((
        s,
        Pattern::Variable(Box::new(PatternVariable { nodes: (a, b) })),
    ))
}

pub fn pattern_tagged(s: Span) -> IResult<Span, Pattern> {
    let (s, a) = symbol("tagged")(s)?;
    let (s, b) = member_identifier(s)?;
    let (s, c) = opt(pattern)(s)?;
    Ok((
        s,
        Pattern::Tagged(Box::new(PatternTagged { nodes: (a, b, c) })),
    ))
}

pub fn pattern_list(s: Span) -> IResult<Span, Pattern> {
    let (s, a) = apostrophe_brace(list(symbol(","), pattern))(s)?;
    Ok((s, Pattern::List(Box::new(PatternList { nodes: (a,) }))))
}

pub fn pattern_identifier_list(s: Span) -> IResult<Span, Pattern> {
    let (s, a) = apostrophe_brace(list(
        symbol(","),
        triple(member_identifier, symbol(":"), pattern),
    ))(s)?;
    Ok((
        s,
        Pattern::IdentifierList(Box::new(PatternIdentifierList { nodes: (a,) })),
    ))
}

pub fn assignment_pattern(s: Span) -> IResult<Span, AssignmentPattern> {
    alt((
        assignment_pattern_list,
        assignment_pattern_structure,
        assignment_pattern_array,
        assignment_pattern_repeat,
    ))(s)
}

pub fn assignment_pattern_list(s: Span) -> IResult<Span, AssignmentPattern> {
    let (s, a) = apostrophe_brace(list(symbol(","), expression))(s)?;
    Ok((
        s,
        AssignmentPattern::List(AssignmentPatternList { nodes: (a,) }),
    ))
}

pub fn assignment_pattern_structure(s: Span) -> IResult<Span, AssignmentPattern> {
    let (s, a) = apostrophe_brace(list(
        symbol(","),
        triple(structure_pattern_key, symbol(":"), expression),
    ))(s)?;
    Ok((
        s,
        AssignmentPattern::Structure(AssignmentPatternStructure { nodes: (a,) }),
    ))
}

pub fn assignment_pattern_array(s: Span) -> IResult<Span, AssignmentPattern> {
    let (s, a) = apostrophe_brace(list(
        symbol(","),
        triple(array_pattern_key, symbol(":"), expression),
    ))(s)?;
    Ok((
        s,
        AssignmentPattern::Array(AssignmentPatternArray { nodes: (a,) }),
    ))
}

pub fn assignment_pattern_repeat(s: Span) -> IResult<Span, AssignmentPattern> {
    let (s, a) = apostrophe_brace(pair(
        constant_expression,
        brace(list(symbol(","), expression)),
    ))(s)?;
    Ok((
        s,
        AssignmentPattern::Repeat(AssignmentPatternRepeat { nodes: (a,) }),
    ))
}

pub fn structure_pattern_key(s: Span) -> IResult<Span, StructurePatternKey> {
    alt((
        map(member_identifier, |x| {
            StructurePatternKey::MemberIdentifier(x)
        }),
        map(assignment_pattern_key, |x| {
            StructurePatternKey::AssignmentPatternKey(x)
        }),
    ))(s)
}

pub fn array_pattern_key(s: Span) -> IResult<Span, ArrayPatternKey> {
    alt((
        map(constant_expression, |x| {
            ArrayPatternKey::ConstantExpression(x)
        }),
        map(assignment_pattern_key, |x| {
            ArrayPatternKey::AssignmentPatternKey(x)
        }),
    ))(s)
}

pub fn assignment_pattern_key(s: Span) -> IResult<Span, AssignmentPatternKey> {
    alt((
        map(simple_type, |x| AssignmentPatternKey::SimpleType(x)),
        map(symbol("default"), |x| AssignmentPatternKey::Default(x)),
    ))(s)
}

pub fn assignment_pattern_expression(s: Span) -> IResult<Span, AssignmentPatternExpression> {
    let (s, a) = opt(assignment_pattern_expression_type)(s)?;
    let (s, b) = assignment_pattern(s)?;
    Ok((s, AssignmentPatternExpression { nodes: (a, b) }))
}

pub fn assignment_pattern_expression_type(
    s: Span,
) -> IResult<Span, AssignmentPatternExpressionType> {
    alt((
        map(ps_type_identifier, |x| {
            AssignmentPatternExpressionType::PsTypeIdentifier(x)
        }),
        map(ps_parameter_identifier, |x| {
            AssignmentPatternExpressionType::PsParameterIdentifier(x)
        }),
        map(integer_atom_type, |x| {
            AssignmentPatternExpressionType::IntegerAtomType(x)
        }),
        map(type_reference, |x| {
            AssignmentPatternExpressionType::TypeReference(x)
        }),
    ))(s)
}

pub fn constant_assignment_pattern_expression(
    s: Span,
) -> IResult<Span, ConstantAssignmentPatternExpression> {
    let (s, a) = assignment_pattern_expression(s)?;
    Ok((s, ConstantAssignmentPatternExpression { nodes: (a,) }))
}

pub fn assignment_pattern_net_lvalue(s: Span) -> IResult<Span, AssignmentPatternNetLvalue> {
    let (s, a) = apostrophe_brace(list(symbol(","), net_lvalue))(s)?;
    Ok((s, AssignmentPatternNetLvalue { nodes: (a,) }))
}

pub fn assignment_pattern_variable_lvalue(
    s: Span,
) -> IResult<Span, AssignmentPatternVariableLvalue> {
    let (s, a) = apostrophe_brace(list(symbol(","), variable_lvalue))(s)?;
    Ok((s, AssignmentPatternVariableLvalue { nodes: (a,) }))
}

// -----------------------------------------------------------------------------
