use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum ContinuousAssign<'a> {
    Net(ContinuousAssignNet<'a>),
    Variable(ContinuousAssignVariable<'a>),
}

#[derive(Debug, Node)]
pub struct ContinuousAssignNet<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<DriveStrength<'a>>,
        Option<Delay3<'a>>,
        ListOfNetAssignments<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct ContinuousAssignVariable<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<DelayControl<'a>>,
        ListOfVariableAssignments<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct ListOfNetAssignments<'a> {
    pub nodes: (List<Symbol<'a>, NetAssignment<'a>>,),
}

#[derive(Debug, Node)]
pub struct ListOfVariableAssignments<'a> {
    pub nodes: (List<Symbol<'a>, VariableAssignment<'a>>,),
}

#[derive(Debug, Node)]
pub struct NetAlias<'a> {
    pub nodes: (
        Symbol<'a>,
        NetLvalue<'a>,
        Symbol<'a>,
        List<Symbol<'a>, NetLvalue<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct NetAssignment<'a> {
    pub nodes: (NetLvalue<'a>, Symbol<'a>, Expression<'a>),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn continuous_assign(s: Span) -> IResult<Span, ContinuousAssign> {
    alt((continuous_assign_net, continuous_assign_variable))(s)
}

#[parser]
pub fn continuous_assign_net(s: Span) -> IResult<Span, ContinuousAssign> {
    let (s, a) = keyword("assign")(s)?;
    let (s, b) = opt(drive_strength)(s)?;
    let (s, c) = opt(delay3)(s)?;
    let (s, d) = list_of_net_assignments(s)?;
    let (s, e) = symbol(";")(s)?;

    Ok((
        s,
        ContinuousAssign::Net(ContinuousAssignNet {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser]
pub fn continuous_assign_variable(s: Span) -> IResult<Span, ContinuousAssign> {
    let (s, a) = keyword("assign")(s)?;
    let (s, b) = opt(delay_control)(s)?;
    let (s, c) = list_of_variable_assignments(s)?;
    let (s, d) = symbol(";")(s)?;

    Ok((
        s,
        ContinuousAssign::Variable(ContinuousAssignVariable {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser(MaybeRecursive)]
pub fn list_of_net_assignments(s: Span) -> IResult<Span, ListOfNetAssignments> {
    let (s, a) = list(symbol(","), net_assignment)(s)?;
    Ok((s, ListOfNetAssignments { nodes: (a,) }))
}

#[parser(MaybeRecursive)]
pub fn list_of_variable_assignments(s: Span) -> IResult<Span, ListOfVariableAssignments> {
    let (s, a) = list(symbol(","), variable_assignment)(s)?;
    Ok((s, ListOfVariableAssignments { nodes: (a,) }))
}

#[parser]
pub fn net_alias(s: Span) -> IResult<Span, NetAlias> {
    let (s, a) = keyword("alias")(s)?;
    let (s, b) = net_lvalue(s)?;
    let (s, c) = symbol("=")(s)?;
    let (s, d) = list(symbol("="), net_lvalue)(s)?;
    let (s, e) = symbol(";")(s)?;

    Ok((
        s,
        NetAlias {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[parser(MaybeRecursive)]
pub fn net_assignment(s: Span) -> IResult<Span, NetAssignment> {
    let (s, a) = net_lvalue(s)?;
    let (s, b) = symbol("=")(s)?;
    let (s, c) = expression(s)?;

    Ok((s, NetAssignment { nodes: (a, b, c) }))
}
