use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
pub(crate) fn attribute_instance(s: Span) -> IResult<Span, AttributeInstance> {
    let (s, a) = symbol("(*")(s)?;
    let (s, b) = list(symbol(","), attr_spec)(s)?;
    let (s, c) = symbol("*)")(s)?;
    Ok((s, AttributeInstance { nodes: (a, b, c) }))
}

#[tracable_parser]
pub(crate) fn attr_spec(s: Span) -> IResult<Span, AttrSpec> {
    let (s, a) = identifier(s)?;
    let (s, b) = opt(pair(symbol("="), constant_expression))(s)?;
    Ok((s, AttrSpec { nodes: (a, b) }))
}
