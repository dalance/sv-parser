use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum ContinuousAssign<'a> {
    Net(ContinuousAssignNet<'a>),
    Variable(ContinuousAssignVariable<'a>),
}

#[derive(Debug)]
pub struct ContinuousAssignNet<'a> {
    pub nodes: (
        Option<DriveStrength>,
        Option<Delay3<'a>>,
        Vec<NetAssignment<'a>>,
    ),
}

#[derive(Debug)]
pub struct ContinuousAssignVariable<'a> {
    pub nodes: (Option<DelayControl<'a>>, Vec<VariableAssignment<'a>>),
}

#[derive(Debug)]
pub struct NetAlias<'a> {
    pub nodes: (NetLvalue<'a>, Vec<NetLvalue<'a>>),
}

#[derive(Debug)]
pub struct NetAssignment<'a> {
    pub nodes: (NetLvalue<'a>, Expression<'a>),
}

// -----------------------------------------------------------------------------

pub fn continuous_assign(s: Span) -> IResult<Span, ContinuousAssign> {
    alt((continuous_assign_net, continuous_assign_variable))(s)
}

pub fn continuous_assign_net(s: Span) -> IResult<Span, ContinuousAssign> {
    let (s, _) = symbol("assign")(s)?;
    let (s, x) = opt(drive_strength)(s)?;
    let (s, y) = opt(delay3)(s)?;
    let (s, z) = list_of_net_assignments(s)?;
    let (s, _) = symbol(";")(s)?;

    Ok((
        s,
        ContinuousAssign::Net(ContinuousAssignNet { nodes: (x, y, z) }),
    ))
}

pub fn continuous_assign_variable(s: Span) -> IResult<Span, ContinuousAssign> {
    let (s, _) = symbol("assign")(s)?;
    let (s, x) = opt(delay_control)(s)?;
    let (s, y) = list_of_variable_assignments(s)?;
    let (s, _) = symbol(";")(s)?;

    Ok((
        s,
        ContinuousAssign::Variable(ContinuousAssignVariable { nodes: (x, y) }),
    ))
}

pub fn list_of_net_assignments(s: Span) -> IResult<Span, Vec<NetAssignment>> {
    separated_nonempty_list(symbol(","), net_assignment)(s)
}

pub fn list_of_variable_assignments(s: Span) -> IResult<Span, Vec<VariableAssignment>> {
    separated_nonempty_list(symbol(","), variable_assignment)(s)
}

pub fn net_alias(s: Span) -> IResult<Span, NetAlias> {
    let (s, _) = symbol("alias")(s)?;
    let (s, x) = net_lvalue(s)?;
    let (s, y) = many1(preceded(symbol("="), net_lvalue))(s)?;

    Ok((s, NetAlias { nodes: (x, y) }))
}

pub fn net_assignment(s: Span) -> IResult<Span, NetAssignment> {
    let (s, x) = net_lvalue(s)?;
    let (s, _) = symbol("=")(s)?;
    let (s, y) = expression(s)?;

    Ok((s, NetAssignment { nodes: (x, y) }))
}
