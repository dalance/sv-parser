use crate::ast::*;
use crate::parser::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct EnableTerminal {
    pub nodes: (Expression,),
}

#[derive(Clone, Debug, Node)]
pub struct InoutTerminal {
    pub nodes: (NetLvalue,),
}

#[derive(Clone, Debug, Node)]
pub struct InputTerminal {
    pub nodes: (Expression,),
}

#[derive(Clone, Debug, Node)]
pub struct NcontrolTerminal {
    pub nodes: (Expression,),
}

#[derive(Clone, Debug, Node)]
pub struct OutputTerminal {
    pub nodes: (NetLvalue,),
}

#[derive(Clone, Debug, Node)]
pub struct PcontrolTerminal {
    pub nodes: (Expression,),
}

// -----------------------------------------------------------------------------

#[parser]
pub(crate) fn enable_terminal(s: Span) -> IResult<Span, EnableTerminal> {
    let (s, a) = expression(s)?;
    Ok((s, EnableTerminal { nodes: (a,) }))
}

#[parser]
pub(crate) fn inout_terminal(s: Span) -> IResult<Span, InoutTerminal> {
    let (s, a) = net_lvalue(s)?;
    Ok((s, InoutTerminal { nodes: (a,) }))
}

#[parser]
pub(crate) fn input_terminal(s: Span) -> IResult<Span, InputTerminal> {
    let (s, a) = expression(s)?;
    Ok((s, InputTerminal { nodes: (a,) }))
}

#[parser]
pub(crate) fn ncontrol_terminal(s: Span) -> IResult<Span, NcontrolTerminal> {
    let (s, a) = expression(s)?;
    Ok((s, NcontrolTerminal { nodes: (a,) }))
}

#[parser]
pub(crate) fn output_terminal(s: Span) -> IResult<Span, OutputTerminal> {
    let (s, a) = net_lvalue(s)?;
    Ok((s, OutputTerminal { nodes: (a,) }))
}

#[parser]
pub(crate) fn pcontrol_terminal(s: Span) -> IResult<Span, PcontrolTerminal> {
    let (s, a) = expression(s)?;
    Ok((s, PcontrolTerminal { nodes: (a,) }))
}

// -----------------------------------------------------------------------------
