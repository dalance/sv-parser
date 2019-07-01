use crate::identifiers::*;
use crate::primaries::*;
use crate::util::*;
use nom::branch::*;
use nom::bytes::complete::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum NetLvalue<'a> {
    Identifier(NetLvalueIdentifier<'a>),
    Lvalue(Vec<NetLvalue<'a>>),
    Pattern(NetLvaluePattern<'a>),
}

#[derive(Debug)]
pub struct NetLvalueIdentifier<'a> {
    identifier: ScopedIdentifier<'a>,
    select: ConstantSelect<'a>,
}

#[derive(Debug)]
pub struct NetLvaluePattern<'a> {
    r#type: Option<AssignmentPatternExpressionType<'a>>,
    lvalue: AssignmentPatternNetLvalue<'a>,
}

#[derive(Debug)]
pub enum VariableLvalue<'a> {
    Identifier(VariableLvalueIdentifier<'a>),
    Lvalue(Vec<VariableLvalue<'a>>),
    Pattern(VariableLvaluePattern<'a>),
    Concatenation(StreamingConcatenation<'a>),
}

#[derive(Debug)]
pub struct VariableLvalueIdentifier<'a> {
    scope: Option<Scope<'a>>,
    identifier: HierarchicalIdentifier<'a>,
    select: Select<'a>,
}

#[derive(Debug)]
pub struct VariableLvaluePattern<'a> {
    r#type: Option<AssignmentPatternExpressionType<'a>>,
    lvalue: AssignmentPatternVariableLvalue<'a>,
}

#[derive(Debug)]
pub struct NonrangeVariableLvalue<'a> {
    scope: Option<Scope<'a>>,
    identifier: HierarchicalIdentifier<'a>,
    select: Select<'a>,
}

// -----------------------------------------------------------------------------

pub fn net_lvalue(s: &str) -> IResult<&str, NetLvalue> {
    alt((net_lvalue_identifier, net_lvalue_lvalue, net_lvalue_pattern))(s)
}

pub fn net_lvalue_identifier(s: &str) -> IResult<&str, NetLvalue> {
    let (s, identifier) = ps_or_hierarchical_net_identifier(s)?;
    let (s, select) = sp(constant_select)(s)?;
    Ok((
        s,
        NetLvalue::Identifier(NetLvalueIdentifier { identifier, select }),
    ))
}

pub fn net_lvalue_pattern(s: &str) -> IResult<&str, NetLvalue> {
    let (s, r#type) = opt(assignment_pattern_expression_type)(s)?;
    let (s, lvalue) = sp(assignment_pattern_net_lvalue)(s)?;
    Ok((s, NetLvalue::Pattern(NetLvaluePattern { r#type, lvalue })))
}

pub fn net_lvalue_lvalue(s: &str) -> IResult<&str, NetLvalue> {
    let (s, _) = tag("{")(s)?;
    let (s, x) = sp(net_lvalue)(s)?;
    let (s, y) = many0(preceded(sp(tag(",")), sp(net_lvalue)))(s)?;
    let (s, _) = tag("}")(s)?;

    let mut ret = Vec::new();
    ret.push(x);
    for y in y {
        ret.push(y);
    }

    Ok((s, NetLvalue::Lvalue(ret)))
}

pub fn variable_lvalue(s: &str) -> IResult<&str, VariableLvalue> {
    alt((
        variable_lvalue_identifier,
        variable_lvalue_lvalue,
        variable_lvalue_pattern,
        map(streaming_concatenation, |x| {
            VariableLvalue::Concatenation(x)
        }),
    ))(s)
}

pub fn variable_lvalue_identifier(s: &str) -> IResult<&str, VariableLvalue> {
    let (s, scope) = opt(alt((
        terminated(implicit_class_handle, sp(tag("."))),
        package_scope,
    )))(s)?;
    let (s, identifier) = sp(hierarchical_variable_identifier)(s)?;
    let (s, select) = sp(select)(s)?;
    Ok((
        s,
        VariableLvalue::Identifier(VariableLvalueIdentifier {
            scope,
            identifier,
            select,
        }),
    ))
}

pub fn variable_lvalue_pattern(s: &str) -> IResult<&str, VariableLvalue> {
    let (s, r#type) = opt(assignment_pattern_expression_type)(s)?;
    let (s, lvalue) = sp(assignment_pattern_variable_lvalue)(s)?;
    Ok((
        s,
        VariableLvalue::Pattern(VariableLvaluePattern { r#type, lvalue }),
    ))
}

pub fn variable_lvalue_lvalue(s: &str) -> IResult<&str, VariableLvalue> {
    let (s, _) = tag("{")(s)?;
    let (s, x) = sp(variable_lvalue)(s)?;
    let (s, y) = many0(preceded(sp(tag(",")), sp(variable_lvalue)))(s)?;
    let (s, _) = tag("}")(s)?;

    let mut ret = Vec::new();
    ret.push(x);
    for y in y {
        ret.push(y);
    }

    Ok((s, VariableLvalue::Lvalue(ret)))
}

pub fn nonrange_variable_lvalue(s: &str) -> IResult<&str, NonrangeVariableLvalue> {
    let (s, scope) = opt(alt((
        terminated(implicit_class_handle, sp(tag("."))),
        package_scope,
    )))(s)?;
    let (s, identifier) = sp(hierarchical_variable_identifier)(s)?;
    let (s, select) = sp(nonrange_select)(s)?;
    Ok((
        s,
        NonrangeVariableLvalue {
            scope,
            identifier,
            select,
        },
    ))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {}
}
