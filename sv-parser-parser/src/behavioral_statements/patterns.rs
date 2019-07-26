use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
pub(crate) fn pattern(s: Span) -> IResult<Span, Pattern> {
    alt((
        pattern_variable,
        map(symbol(".*"), |x| Pattern::Asterisk(Box::new(x))),
        map(constant_expression, |x| {
            Pattern::ConstantExpression(Box::new(x))
        }),
        pattern_tagged,
        pattern_list,
        pattern_identifier_list,
    ))(s)
}

#[tracable_parser]
pub(crate) fn pattern_variable(s: Span) -> IResult<Span, Pattern> {
    let (s, a) = symbol(".")(s)?;
    let (s, b) = variable_identifier(s)?;
    Ok((
        s,
        Pattern::Variable(Box::new(PatternVariable { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn pattern_tagged(s: Span) -> IResult<Span, Pattern> {
    let (s, a) = keyword("tagged")(s)?;
    let (s, b) = member_identifier(s)?;
    let (s, c) = opt(pattern)(s)?;
    Ok((
        s,
        Pattern::Tagged(Box::new(PatternTagged { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn pattern_list(s: Span) -> IResult<Span, Pattern> {
    let (s, a) = apostrophe_brace(list(symbol(","), pattern))(s)?;
    Ok((s, Pattern::List(Box::new(PatternList { nodes: (a,) }))))
}

#[tracable_parser]
pub(crate) fn pattern_identifier_list(s: Span) -> IResult<Span, Pattern> {
    let (s, a) = apostrophe_brace(list(
        symbol(","),
        triple(member_identifier, symbol(":"), pattern),
    ))(s)?;
    Ok((
        s,
        Pattern::IdentifierList(Box::new(PatternIdentifierList { nodes: (a,) })),
    ))
}

#[tracable_parser]
pub(crate) fn assignment_pattern(s: Span) -> IResult<Span, AssignmentPattern> {
    alt((
        assignment_pattern_list,
        assignment_pattern_structure,
        assignment_pattern_array,
        assignment_pattern_repeat,
    ))(s)
}

#[tracable_parser]
pub(crate) fn assignment_pattern_list(s: Span) -> IResult<Span, AssignmentPattern> {
    let (s, a) = apostrophe_brace(list(symbol(","), expression))(s)?;
    Ok((
        s,
        AssignmentPattern::List(Box::new(AssignmentPatternList { nodes: (a,) })),
    ))
}

#[tracable_parser]
pub(crate) fn assignment_pattern_structure(s: Span) -> IResult<Span, AssignmentPattern> {
    let (s, a) = apostrophe_brace(list(
        symbol(","),
        triple(structure_pattern_key, symbol(":"), expression),
    ))(s)?;
    Ok((
        s,
        AssignmentPattern::Structure(Box::new(AssignmentPatternStructure { nodes: (a,) })),
    ))
}

#[tracable_parser]
pub(crate) fn assignment_pattern_array(s: Span) -> IResult<Span, AssignmentPattern> {
    let (s, a) = apostrophe_brace(list(
        symbol(","),
        triple(array_pattern_key, symbol(":"), expression),
    ))(s)?;
    Ok((
        s,
        AssignmentPattern::Array(Box::new(AssignmentPatternArray { nodes: (a,) })),
    ))
}

#[tracable_parser]
pub(crate) fn assignment_pattern_repeat(s: Span) -> IResult<Span, AssignmentPattern> {
    let (s, a) = apostrophe_brace(pair(
        constant_expression,
        brace(list(symbol(","), expression)),
    ))(s)?;
    Ok((
        s,
        AssignmentPattern::Repeat(Box::new(AssignmentPatternRepeat { nodes: (a,) })),
    ))
}

#[tracable_parser]
pub(crate) fn structure_pattern_key(s: Span) -> IResult<Span, StructurePatternKey> {
    alt((
        map(member_identifier, |x| {
            StructurePatternKey::MemberIdentifier(Box::new(x))
        }),
        map(assignment_pattern_key, |x| {
            StructurePatternKey::AssignmentPatternKey(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn array_pattern_key(s: Span) -> IResult<Span, ArrayPatternKey> {
    alt((
        map(constant_expression, |x| {
            ArrayPatternKey::ConstantExpression(Box::new(x))
        }),
        map(assignment_pattern_key, |x| {
            ArrayPatternKey::AssignmentPatternKey(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn assignment_pattern_key(s: Span) -> IResult<Span, AssignmentPatternKey> {
    alt((
        map(simple_type, |x| {
            AssignmentPatternKey::SimpleType(Box::new(x))
        }),
        map(keyword("default"), |x| {
            AssignmentPatternKey::Default(Box::new(x))
        }),
    ))(s)
}

#[packrat_parser]
#[tracable_parser]
pub(crate) fn assignment_pattern_expression(s: Span) -> IResult<Span, AssignmentPatternExpression> {
    let (s, a) = opt(assignment_pattern_expression_type)(s)?;
    let (s, b) = assignment_pattern(s)?;
    Ok((s, AssignmentPatternExpression { nodes: (a, b) }))
}

#[tracable_parser]
pub(crate) fn assignment_pattern_expression_type(
    s: Span,
) -> IResult<Span, AssignmentPatternExpressionType> {
    alt((
        map(ps_type_identifier, |x| {
            AssignmentPatternExpressionType::PsTypeIdentifier(Box::new(x))
        }),
        map(ps_parameter_identifier, |x| {
            AssignmentPatternExpressionType::PsParameterIdentifier(Box::new(x))
        }),
        map(integer_atom_type, |x| {
            AssignmentPatternExpressionType::IntegerAtomType(Box::new(x))
        }),
        map(type_reference, |x| {
            AssignmentPatternExpressionType::TypeReference(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn constant_assignment_pattern_expression(
    s: Span,
) -> IResult<Span, ConstantAssignmentPatternExpression> {
    let (s, a) = assignment_pattern_expression(s)?;
    Ok((s, ConstantAssignmentPatternExpression { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn assignment_pattern_net_lvalue(s: Span) -> IResult<Span, AssignmentPatternNetLvalue> {
    let (s, a) = apostrophe_brace(list(symbol(","), net_lvalue))(s)?;
    Ok((s, AssignmentPatternNetLvalue { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn assignment_pattern_variable_lvalue(
    s: Span,
) -> IResult<Span, AssignmentPatternVariableLvalue> {
    let (s, a) = apostrophe_brace(list(symbol(","), variable_lvalue))(s)?;
    Ok((s, AssignmentPatternVariableLvalue { nodes: (a,) }))
}
