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
    let (s, drive_strength) = opt(drive_strength)(s)?;
    let (s, delay3) = opt(delay3)(s)?;
    let (s, list) = many1(net_assignment)(s)?;

    Ok((
        s,
        ContinuousAssign::Net(ContinuousAssignNet {
            drive_strength,
            delay3,
            list,
        }),
    ))
}

pub fn continuous_assign_variable(s: &str) -> IResult<&str, ContinuousAssign> {
    let (s, delay_control) = opt(delay_control)(s)?;
    let (s, list) = many1(variable_assignment)(s)?;

    Ok((
        s,
        ContinuousAssign::Variable(ContinuousAssignVariable {
            delay_control,
            list,
        }),
    ))
}

pub fn net_alias(s: &str) -> IResult<&str, NetAlias> {
    let (s, _) = symbol("alias")(s)?;
    let (s, lvalue) = net_lvalue(s)?;
    let (s, rvalue) = many1(preceded(symbol("="), net_lvalue))(s)?;

    Ok((s, NetAlias { lvalue, rvalue }))
}

pub fn net_assignment(s: &str) -> IResult<&str, NetAssignment> {
    let (s, lvalue) = net_lvalue(s)?;
    let (s, _) = symbol("=")(s)?;
    let (s, rvalue) = expression(s)?;

    Ok((s, NetAssignment { lvalue, rvalue }))
}
