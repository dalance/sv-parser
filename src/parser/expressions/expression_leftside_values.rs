use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum NetLvalue<'a> {
    Identifier(NetLvalueIdentifier<'a>),
    Lvalue(Box<NetLvalueLvalue<'a>>),
    Pattern(Box<NetLvaluePattern<'a>>),
}

#[derive(Debug, Node)]
pub struct NetLvalueIdentifier<'a> {
    pub nodes: (PsOrHierarchicalNetIdentifier<'a>, ConstantSelect<'a>),
}

#[derive(Debug, Node)]
pub struct NetLvalueLvalue<'a> {
    pub nodes: (Brace<'a, List<Symbol<'a>, NetLvalue<'a>>>,),
}

#[derive(Debug, Node)]
pub struct NetLvaluePattern<'a> {
    pub nodes: (
        Option<AssignmentPatternExpressionType<'a>>,
        AssignmentPatternNetLvalue<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum VariableLvalue<'a> {
    Identifier(VariableLvalueIdentifier<'a>),
    Lvalue(Box<VariableLvalueLvalue<'a>>),
    Pattern(Box<VariableLvaluePattern<'a>>),
    StreamingConcatenation(StreamingConcatenation<'a>),
}

#[derive(Debug, Node)]
pub struct VariableLvalueIdentifier<'a> {
    pub nodes: (
        Option<ImplicitClassHandleOrPackageScope<'a>>,
        HierarchicalVariableIdentifier<'a>,
        Select<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct VariableLvalueLvalue<'a> {
    pub nodes: (Brace<'a, List<Symbol<'a>, VariableLvalue<'a>>>,),
}

#[derive(Debug, Node)]
pub struct VariableLvaluePattern<'a> {
    pub nodes: (
        Option<AssignmentPatternExpressionType<'a>>,
        AssignmentPatternVariableLvalue<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct NonrangeVariableLvalue<'a> {
    pub nodes: (
        Option<ImplicitClassHandleOrPackageScope<'a>>,
        HierarchicalVariableIdentifier<'a>,
        NonrangeSelect<'a>,
    ),
}

// -----------------------------------------------------------------------------

#[trace]
pub fn net_lvalue(s: Span) -> IResult<Span, NetLvalue> {
    alt((net_lvalue_identifier, net_lvalue_lvalue, net_lvalue_pattern))(s)
}

#[trace]
pub fn net_lvalue_identifier(s: Span) -> IResult<Span, NetLvalue> {
    let (s, a) = ps_or_hierarchical_net_identifier(s)?;
    let (s, b) = constant_select(s)?;
    Ok((
        s,
        NetLvalue::Identifier(NetLvalueIdentifier { nodes: (a, b) }),
    ))
}

#[trace]
pub fn net_lvalue_pattern(s: Span) -> IResult<Span, NetLvalue> {
    let (s, a) = opt(assignment_pattern_expression_type)(s)?;
    let (s, b) = assignment_pattern_net_lvalue(s)?;
    Ok((
        s,
        NetLvalue::Pattern(Box::new(NetLvaluePattern { nodes: (a, b) })),
    ))
}

#[trace]
pub fn net_lvalue_lvalue(s: Span) -> IResult<Span, NetLvalue> {
    let (s, a) = brace(list(symbol(","), net_lvalue))(s)?;
    Ok((
        s,
        NetLvalue::Lvalue(Box::new(NetLvalueLvalue { nodes: (a,) })),
    ))
}

#[trace]
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

#[trace]
pub fn variable_lvalue_identifier(s: Span) -> IResult<Span, VariableLvalue> {
    let (s, a) = opt(implicit_class_handle_or_package_scope)(s)?;
    let (s, b) = hierarchical_variable_identifier(s)?;
    let (s, c) = select(s)?;
    Ok((
        s,
        VariableLvalue::Identifier(VariableLvalueIdentifier { nodes: (a, b, c) }),
    ))
}

#[trace]
pub fn variable_lvalue_pattern(s: Span) -> IResult<Span, VariableLvalue> {
    let (s, a) = opt(assignment_pattern_expression_type)(s)?;
    let (s, b) = assignment_pattern_variable_lvalue(s)?;
    Ok((
        s,
        VariableLvalue::Pattern(Box::new(VariableLvaluePattern { nodes: (a, b) })),
    ))
}

#[trace]
pub fn variable_lvalue_lvalue(s: Span) -> IResult<Span, VariableLvalue> {
    let (s, a) = brace(list(symbol(","), variable_lvalue))(s)?;
    Ok((
        s,
        VariableLvalue::Lvalue(Box::new(VariableLvalueLvalue { nodes: (a,) })),
    ))
}

#[trace]
pub fn nonrange_variable_lvalue(s: Span) -> IResult<Span, NonrangeVariableLvalue> {
    let (s, a) = opt(implicit_class_handle_or_package_scope)(s)?;
    let (s, b) = hierarchical_variable_identifier(s)?;
    let (s, c) = nonrange_select(s)?;
    Ok((s, NonrangeVariableLvalue { nodes: (a, b, c) }))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_net_lvalue() {
        parser_test!(net_lvalue, "A", Ok((_, _)));
        parser_test!(net_lvalue, "{A[7:0],A[15:8],A[23:16]}", Ok((_, _)));
        parser_test!(net_lvalue, "'{A[7:0],A[15:8]}", Ok((_, _)));
    }

    #[test]
    fn test_variable_lvalue() {
        parser_test!(variable_lvalue, "A", Ok((_, _)));
        parser_test!(variable_lvalue, "{A[7:0],A[15:8],A[23:16]}", Ok((_, _)));
        parser_test!(variable_lvalue, "'{A[7:0],A[15:8]}", Ok((_, _)));
    }

    #[test]
    fn test_nonrange_variable_lvalue() {
        parser_test!(nonrange_variable_lvalue, "A", Ok((_, _)));
        parser_test!(nonrange_variable_lvalue, "A[][2][3]", Ok((_, _)));
        //parser_test!(nonrange_variable_lvalue, "A[][]", Ok((_, _)));
    }
}
