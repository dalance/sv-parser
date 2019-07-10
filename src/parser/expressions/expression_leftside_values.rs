use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum NetLvalue<'a> {
    Identifier(NetLvalueIdentifier<'a>),
    Lvalue(Box<NetLvalueLvalue<'a>>),
    Pattern(NetLvaluePattern<'a>),
}

#[derive(Debug)]
pub struct NetLvalueIdentifier<'a> {
    pub nodes: (PsOrHierarchicalNetIdentifier<'a>, ConstantSelect<'a>),
}

#[derive(Debug)]
pub struct NetLvalueLvalue<'a> {
    pub nodes: (Brace<'a, List<Symbol<'a>, NetLvalue<'a>>>,),
}

#[derive(Debug)]
pub struct NetLvaluePattern<'a> {
    pub nodes: (
        Option<AssignmentPatternExpressionType<'a>>,
        AssignmentPatternNetLvalue<'a>,
    ),
}

#[derive(Debug)]
pub enum VariableLvalue<'a> {
    Identifier(VariableLvalueIdentifier<'a>),
    Lvalue(Box<VariableLvalueLvalue<'a>>),
    Pattern(VariableLvaluePattern<'a>),
    StreamingConcatenation(StreamingConcatenation<'a>),
}

#[derive(Debug)]
pub struct VariableLvalueIdentifier<'a> {
    pub nodes: (
        Option<ImplicitClassHandleOrPackageScope<'a>>,
        HierarchicalVariableIdentifier<'a>,
        Select<'a>,
    ),
}

#[derive(Debug)]
pub struct VariableLvalueLvalue<'a> {
    pub nodes: (Brace<'a, List<Symbol<'a>, VariableLvalue<'a>>>,),
}

#[derive(Debug)]
pub struct VariableLvaluePattern<'a> {
    pub nodes: (
        Option<AssignmentPatternExpressionType<'a>>,
        AssignmentPatternVariableLvalue<'a>,
    ),
}

#[derive(Debug)]
pub struct NonrangeVariableLvalue<'a> {
    pub nodes: (
        Option<ImplicitClassHandleOrPackageScope<'a>>,
        HierarchicalVariableIdentifier<'a>,
        NonrangeSelect<'a>,
    ),
}

// -----------------------------------------------------------------------------

pub fn net_lvalue(s: Span) -> IResult<Span, NetLvalue> {
    alt((net_lvalue_identifier, net_lvalue_lvalue, net_lvalue_pattern))(s)
}

pub fn net_lvalue_identifier(s: Span) -> IResult<Span, NetLvalue> {
    let (s, a) = ps_or_hierarchical_net_identifier(s)?;
    let (s, b) = constant_select(s)?;
    Ok((
        s,
        NetLvalue::Identifier(NetLvalueIdentifier { nodes: (a, b) }),
    ))
}

pub fn net_lvalue_pattern(s: Span) -> IResult<Span, NetLvalue> {
    let (s, a) = opt(assignment_pattern_expression_type)(s)?;
    let (s, b) = assignment_pattern_net_lvalue(s)?;
    Ok((s, NetLvalue::Pattern(NetLvaluePattern { nodes: (a, b) })))
}

pub fn net_lvalue_lvalue(s: Span) -> IResult<Span, NetLvalue> {
    let (s, a) = brace2(list(symbol(","), net_lvalue))(s)?;
    Ok((
        s,
        NetLvalue::Lvalue(Box::new(NetLvalueLvalue { nodes: (a,) })),
    ))
}

pub fn variable_lvalue(s: Span) -> IResult<Span, VariableLvalue> {
    alt((
        variable_lvalue_identifier,
        variable_lvalue_lvalue,
        variable_lvalue_pattern,
        map(streaming_concatenation, |x| {
            VariableLvalue::StreamingConcatenation(x)
        }),
    ))(s)
}

pub fn variable_lvalue_identifier(s: Span) -> IResult<Span, VariableLvalue> {
    let (s, a) = opt(implicit_class_handle_or_package_scope)(s)?;
    let (s, b) = hierarchical_variable_identifier(s)?;
    let (s, c) = select(s)?;
    Ok((
        s,
        VariableLvalue::Identifier(VariableLvalueIdentifier { nodes: (a, b, c) }),
    ))
}

pub fn variable_lvalue_pattern(s: Span) -> IResult<Span, VariableLvalue> {
    let (s, a) = opt(assignment_pattern_expression_type)(s)?;
    let (s, b) = assignment_pattern_variable_lvalue(s)?;
    Ok((
        s,
        VariableLvalue::Pattern(VariableLvaluePattern { nodes: (a, b) }),
    ))
}

pub fn variable_lvalue_lvalue(s: Span) -> IResult<Span, VariableLvalue> {
    let (s, a) = brace2(list(symbol(","), variable_lvalue))(s)?;
    Ok((
        s,
        VariableLvalue::Lvalue(Box::new(VariableLvalueLvalue { nodes: (a,) })),
    ))
}

pub fn nonrange_variable_lvalue(s: Span) -> IResult<Span, NonrangeVariableLvalue> {
    let (s, a) = opt(implicit_class_handle_or_package_scope)(s)?;
    let (s, b) = hierarchical_variable_identifier(s)?;
    let (s, c) = nonrange_select(s)?;
    Ok((s, NonrangeVariableLvalue { nodes: (a, b, c) }))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    //use super::*;

    #[test]
    fn test() {}
}
