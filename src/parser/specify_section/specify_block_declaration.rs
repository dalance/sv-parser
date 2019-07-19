use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct SpecifyBlock<'a> {
    pub nodes: (Symbol<'a>, Vec<SpecifyItem<'a>>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum SpecifyItem<'a> {
    SpecparamDeclaration(SpecparamDeclaration<'a>),
    PulsestyleDeclaration(PulsestyleDeclaration<'a>),
    ShowcancelledDeclaration(ShowcancelledDeclaration<'a>),
    PathDeclaration(PathDeclaration<'a>),
    SystemTimingCheck(SystemTimingCheck<'a>),
}

#[derive(Debug, Node)]
pub struct PulsestyleDeclaration<'a> {
    pub nodes: (Symbol<'a>, ListOfPathOutputs<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct ShowcancelledDeclaration<'a> {
    pub nodes: (Symbol<'a>, ListOfPathOutputs<'a>, Symbol<'a>),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn specify_block(s: Span) -> IResult<Span, SpecifyBlock> {
    let (s, a) = keyword("specify")(s)?;
    let (s, b) = many0(specify_item)(s)?;
    let (s, c) = keyword("endspecify")(s)?;
    Ok((s, SpecifyBlock { nodes: (a, b, c) }))
}

#[parser]
pub fn specify_item(s: Span) -> IResult<Span, SpecifyItem> {
    alt((
        map(specparam_declaration, |x| {
            SpecifyItem::SpecparamDeclaration(x)
        }),
        map(pulsestyle_declaration, |x| {
            SpecifyItem::PulsestyleDeclaration(x)
        }),
        map(showcancelled_declaration, |x| {
            SpecifyItem::ShowcancelledDeclaration(x)
        }),
        map(path_declaration, |x| SpecifyItem::PathDeclaration(x)),
        map(system_timing_check, |x| SpecifyItem::SystemTimingCheck(x)),
    ))(s)
}

#[parser]
pub fn pulsestyle_declaration(s: Span) -> IResult<Span, PulsestyleDeclaration> {
    let (s, a) = alt((
        keyword("pulsestyle_onevent"),
        keyword("pulsestyle_ondetect"),
    ))(s)?;
    let (s, b) = list_of_path_outputs(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((s, PulsestyleDeclaration { nodes: (a, b, c) }))
}

#[parser]
pub fn showcancelled_declaration(s: Span) -> IResult<Span, ShowcancelledDeclaration> {
    let (s, a) = alt((keyword("showcalcelled"), keyword("noshowcancelled")))(s)?;
    let (s, b) = list_of_path_outputs(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((s, ShowcancelledDeclaration { nodes: (a, b, c) }))
}
