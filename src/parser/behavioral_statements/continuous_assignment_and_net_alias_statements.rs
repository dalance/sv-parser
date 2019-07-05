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
    pub drive_strength: Option<DriveStrength<'a>>,
    pub delay3: Option<Delay3<'a>>,
    pub list: Vec<NetAssignment<'a>>,
}

#[derive(Debug)]
pub struct ContinuousAssignVariable<'a> {
    pub delay_control: Option<DelayControl<'a>>,
    pub list: Vec<VariableAssignment<'a>>,
}

#[derive(Debug)]
pub struct NetAlias<'a> {
    pub lvalue: NetLvalue<'a>,
    pub rvalue: Vec<NetLvalue<'a>>,
}

#[derive(Debug)]
pub struct NetAssignment<'a> {
    pub lvalue: NetLvalue<'a>,
    pub rvalue: Expression<'a>,
}

// -----------------------------------------------------------------------------

pub fn continuous_assign(s: &str) -> IResult<&str, ContinuousAssign> {
    alt((continuous_assign_net, continuous_assign_variable))(s)
}

pub fn continuous_assign_net(s: &str) -> IResult<&str, ContinuousAssign> {
    let (s, _) = symbol("assign")(s)?;
    let (s, x) = opt(drive_strength)(s)?;
    let (s, y) = opt(delay3)(s)?;
    let (s, z) = list_of_net_assignments(s)?;
    let (s, _) = symbol(";")(s)?;

    Ok((
        s,
        ContinuousAssign::Net(ContinuousAssignNet {
            drive_strength: x,
            delay3: y,
            list: z,
        }),
    ))
}

pub fn continuous_assign_variable(s: &str) -> IResult<&str, ContinuousAssign> {
    let (s, _) = symbol("assign")(s)?;
    let (s, x) = opt(delay_control)(s)?;
    let (s, y) = list_of_variable_assignments(s)?;
    let (s, _) = symbol(";")(s)?;

    Ok((
        s,
        ContinuousAssign::Variable(ContinuousAssignVariable {
            delay_control: x,
            list: y,
        }),
    ))
}

pub fn list_of_net_assignments(s: &str) -> IResult<&str, Vec<NetAssignment>> {
    separated_nonempty_list(symbol(","), net_assignment)(s)
}

pub fn list_of_variable_assignments(s: &str) -> IResult<&str, Vec<VariableAssignment>> {
    separated_nonempty_list(symbol(","), variable_assignment)(s)
}

pub fn net_alias(s: &str) -> IResult<&str, NetAlias> {
    let (s, _) = symbol("alias")(s)?;
    let (s, x) = net_lvalue(s)?;
    let (s, y) = many1(preceded(symbol("="), net_lvalue))(s)?;

    Ok((
        s,
        NetAlias {
            lvalue: x,
            rvalue: y,
        },
    ))
}

pub fn net_assignment(s: &str) -> IResult<&str, NetAssignment> {
    let (s, x) = net_lvalue(s)?;
    let (s, _) = symbol("=")(s)?;
    let (s, y) = expression(s)?;

    Ok((
        s,
        NetAssignment {
            lvalue: x,
            rvalue: y,
        },
    ))
}
