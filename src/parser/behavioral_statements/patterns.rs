use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;
use nom_packrat::packrat_parser;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum Pattern {
    Variable(Box<PatternVariable>),
    Asterisk(Symbol),
    ConstantExpression(Box<ConstantExpression>),
    Tagged(Box<PatternTagged>),
    List(Box<PatternList>),
    IdentifierList(Box<PatternIdentifierList>),
}

#[derive(Clone, Debug, Node)]
pub struct PatternVariable {
    pub nodes: (Symbol, VariableIdentifier),
}

#[derive(Clone, Debug, Node)]
pub struct PatternTagged {
    pub nodes: (Keyword, MemberIdentifier, Option<Pattern>),
}

#[derive(Clone, Debug, Node)]
pub struct PatternList {
    pub nodes: (ApostropheBrace<List<Symbol, Pattern>>,),
}

#[derive(Clone, Debug, Node)]
pub struct PatternIdentifierList {
    pub nodes: (ApostropheBrace<List<Symbol, (MemberIdentifier, Symbol, Pattern)>>,),
}

#[derive(Clone, Debug, Node)]
pub enum AssignmentPattern {
    List(AssignmentPatternList),
    Structure(AssignmentPatternStructure),
    Array(AssignmentPatternArray),
    Repeat(AssignmentPatternRepeat),
}

#[derive(Clone, Debug, Node)]
pub struct AssignmentPatternList {
    pub nodes: (ApostropheBrace<List<Symbol, Expression>>,),
}

#[derive(Clone, Debug, Node)]
pub struct AssignmentPatternStructure {
    pub nodes: (ApostropheBrace<List<Symbol, (StructurePatternKey, Symbol, Expression)>>,),
}

#[derive(Clone, Debug, Node)]
pub struct AssignmentPatternArray {
    pub nodes: (ApostropheBrace<List<Symbol, (ArrayPatternKey, Symbol, Expression)>>,),
}

#[derive(Clone, Debug, Node)]
pub struct AssignmentPatternRepeat {
    pub nodes: (ApostropheBrace<(ConstantExpression, Brace<List<Symbol, Expression>>)>,),
}

#[derive(Clone, Debug, Node)]
pub enum StructurePatternKey {
    MemberIdentifier(MemberIdentifier),
    AssignmentPatternKey(AssignmentPatternKey),
}

#[derive(Clone, Debug, Node)]
pub enum ArrayPatternKey {
    ConstantExpression(ConstantExpression),
    AssignmentPatternKey(AssignmentPatternKey),
}

#[derive(Clone, Debug, Node)]
pub enum AssignmentPatternKey {
    SimpleType(SimpleType),
    Default(Keyword),
}

#[derive(Clone, Debug, Node)]
pub struct AssignmentPatternExpression {
    pub nodes: (Option<AssignmentPatternExpressionType>, AssignmentPattern),
}

#[derive(Clone, Debug, Node)]
pub enum AssignmentPatternExpressionType {
    PsTypeIdentifier(PsTypeIdentifier),
    PsParameterIdentifier(PsParameterIdentifier),
    IntegerAtomType(IntegerAtomType),
    TypeReference(TypeReference),
}

#[derive(Clone, Debug, Node)]
pub struct ConstantAssignmentPatternExpression {
    pub nodes: (AssignmentPatternExpression,),
}

#[derive(Clone, Debug, Node)]
pub struct AssignmentPatternNetLvalue {
    pub nodes: (ApostropheBrace<List<Symbol, NetLvalue>>,),
}

#[derive(Clone, Debug, Node)]
pub struct AssignmentPatternVariableLvalue {
    pub nodes: (ApostropheBrace<List<Symbol, VariableLvalue>>,),
}

// -----------------------------------------------------------------------------

#[parser]
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

#[parser]
pub fn pattern_variable(s: Span) -> IResult<Span, Pattern> {
    let (s, a) = symbol(".")(s)?;
    let (s, b) = variable_identifier(s)?;
    Ok((
        s,
        Pattern::Variable(Box::new(PatternVariable { nodes: (a, b) })),
    ))
}

#[parser]
pub fn pattern_tagged(s: Span) -> IResult<Span, Pattern> {
    let (s, a) = keyword("tagged")(s)?;
    let (s, b) = member_identifier(s)?;
    let (s, c) = opt(pattern)(s)?;
    Ok((
        s,
        Pattern::Tagged(Box::new(PatternTagged { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn pattern_list(s: Span) -> IResult<Span, Pattern> {
    let (s, a) = apostrophe_brace(list(symbol(","), pattern))(s)?;
    Ok((s, Pattern::List(Box::new(PatternList { nodes: (a,) }))))
}

#[parser]
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

#[parser]
pub fn assignment_pattern(s: Span) -> IResult<Span, AssignmentPattern> {
    alt((
        assignment_pattern_list,
        assignment_pattern_structure,
        assignment_pattern_array,
        assignment_pattern_repeat,
    ))(s)
}

#[parser]
pub fn assignment_pattern_list(s: Span) -> IResult<Span, AssignmentPattern> {
    let (s, a) = apostrophe_brace(list(symbol(","), expression))(s)?;
    Ok((
        s,
        AssignmentPattern::List(AssignmentPatternList { nodes: (a,) }),
    ))
}

#[parser]
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

#[parser]
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

#[parser]
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

#[parser]
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

#[parser]
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

#[parser]
pub fn assignment_pattern_key(s: Span) -> IResult<Span, AssignmentPatternKey> {
    alt((
        map(simple_type, |x| AssignmentPatternKey::SimpleType(x)),
        map(keyword("default"), |x| AssignmentPatternKey::Default(x)),
    ))(s)
}

#[packrat_parser]
#[parser]
pub fn assignment_pattern_expression(s: Span) -> IResult<Span, AssignmentPatternExpression> {
    let (s, a) = opt(assignment_pattern_expression_type)(s)?;
    let (s, b) = assignment_pattern(s)?;
    Ok((s, AssignmentPatternExpression { nodes: (a, b) }))
}

#[parser]
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

#[parser]
pub fn constant_assignment_pattern_expression(
    s: Span,
) -> IResult<Span, ConstantAssignmentPatternExpression> {
    let (s, a) = assignment_pattern_expression(s)?;
    Ok((s, ConstantAssignmentPatternExpression { nodes: (a,) }))
}

#[parser]
pub fn assignment_pattern_net_lvalue(s: Span) -> IResult<Span, AssignmentPatternNetLvalue> {
    let (s, a) = apostrophe_brace(list(symbol(","), net_lvalue))(s)?;
    Ok((s, AssignmentPatternNetLvalue { nodes: (a,) }))
}

#[parser]
pub fn assignment_pattern_variable_lvalue(
    s: Span,
) -> IResult<Span, AssignmentPatternVariableLvalue> {
    let (s, a) = apostrophe_brace(list(symbol(","), variable_lvalue))(s)?;
    Ok((s, AssignmentPatternVariableLvalue { nodes: (a,) }))
}

// -----------------------------------------------------------------------------
