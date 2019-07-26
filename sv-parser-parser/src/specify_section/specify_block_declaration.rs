use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
pub(crate) fn specify_block(s: Span) -> IResult<Span, SpecifyBlock> {
    let (s, a) = keyword("specify")(s)?;
    let (s, b) = many0(specify_item)(s)?;
    let (s, c) = keyword("endspecify")(s)?;
    Ok((s, SpecifyBlock { nodes: (a, b, c) }))
}

#[tracable_parser]
pub(crate) fn specify_item(s: Span) -> IResult<Span, SpecifyItem> {
    alt((
        map(specparam_declaration, |x| {
            SpecifyItem::SpecparamDeclaration(Box::new(x))
        }),
        map(pulsestyle_declaration, |x| {
            SpecifyItem::PulsestyleDeclaration(Box::new(x))
        }),
        map(showcancelled_declaration, |x| {
            SpecifyItem::ShowcancelledDeclaration(Box::new(x))
        }),
        map(path_declaration, |x| {
            SpecifyItem::PathDeclaration(Box::new(x))
        }),
        map(system_timing_check, |x| {
            SpecifyItem::SystemTimingCheck(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn pulsestyle_declaration(s: Span) -> IResult<Span, PulsestyleDeclaration> {
    let (s, a) = alt((
        keyword("pulsestyle_onevent"),
        keyword("pulsestyle_ondetect"),
    ))(s)?;
    let (s, b) = list_of_path_outputs(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((s, PulsestyleDeclaration { nodes: (a, b, c) }))
}

#[tracable_parser]
pub(crate) fn showcancelled_declaration(s: Span) -> IResult<Span, ShowcancelledDeclaration> {
    let (s, a) = alt((keyword("showcalcelled"), keyword("noshowcancelled")))(s)?;
    let (s, b) = list_of_path_outputs(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((s, ShowcancelledDeclaration { nodes: (a, b, c) }))
}
