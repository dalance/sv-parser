use crate::ast::*;
use crate::parser::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct EnableTerminal<'a> {
    pub nodes: (Expression<'a>,),
}

#[derive(Debug, Node)]
pub struct InoutTerminal<'a> {
    pub nodes: (NetLvalue<'a>,),
}

#[derive(Debug, Node)]
pub struct InputTerminal<'a> {
    pub nodes: (Expression<'a>,),
}

#[derive(Debug, Node)]
pub struct NcontrolTerminal<'a> {
    pub nodes: (Expression<'a>,),
}

#[derive(Debug, Node)]
pub struct OutputTerminal<'a> {
    pub nodes: (NetLvalue<'a>,),
}

#[derive(Debug, Node)]
pub struct PcontrolTerminal<'a> {
    pub nodes: (Expression<'a>,),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn enable_terminal(s: Span) -> IResult<Span, EnableTerminal> {
    let (s, a) = expression(s)?;
    Ok((s, EnableTerminal { nodes: (a,) }))
}

#[parser]
pub fn inout_terminal(s: Span) -> IResult<Span, InoutTerminal> {
    let (s, a) = net_lvalue(s)?;
    Ok((s, InoutTerminal { nodes: (a,) }))
}

#[parser]
pub fn input_terminal(s: Span) -> IResult<Span, InputTerminal> {
    let (s, a) = expression(s)?;
    Ok((s, InputTerminal { nodes: (a,) }))
}

#[parser]
pub fn ncontrol_terminal(s: Span) -> IResult<Span, NcontrolTerminal> {
    let (s, a) = expression(s)?;
    Ok((s, NcontrolTerminal { nodes: (a,) }))
}

#[parser]
pub fn output_terminal(s: Span) -> IResult<Span, OutputTerminal> {
    let (s, a) = net_lvalue(s)?;
    Ok((s, OutputTerminal { nodes: (a,) }))
}

#[parser]
pub fn pcontrol_terminal(s: Span) -> IResult<Span, PcontrolTerminal> {
    let (s, a) = expression(s)?;
    Ok((s, PcontrolTerminal { nodes: (a,) }))
}

// -----------------------------------------------------------------------------
