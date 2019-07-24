use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::IResult;
use nom_packrat::packrat_parser;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum NetLvalue {
    Identifier(NetLvalueIdentifier),
    Lvalue(Box<NetLvalueLvalue>),
    Pattern(Box<NetLvaluePattern>),
}

#[derive(Clone, Debug, Node)]
pub struct NetLvalueIdentifier {
    pub nodes: (PsOrHierarchicalNetIdentifier, ConstantSelect),
}

#[derive(Clone, Debug, Node)]
pub struct NetLvalueLvalue {
    pub nodes: (Brace<List<Symbol, NetLvalue>>,),
}

#[derive(Clone, Debug, Node)]
pub struct NetLvaluePattern {
    pub nodes: (
        Option<AssignmentPatternExpressionType>,
        AssignmentPatternNetLvalue,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum VariableLvalue {
    Identifier(VariableLvalueIdentifier),
    Lvalue(Box<VariableLvalueLvalue>),
    Pattern(Box<VariableLvaluePattern>),
    StreamingConcatenation(StreamingConcatenation),
}

#[derive(Clone, Debug, Node)]
pub struct VariableLvalueIdentifier {
    pub nodes: (
        Option<ImplicitClassHandleOrPackageScope>,
        HierarchicalVariableIdentifier,
        Select,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct VariableLvalueLvalue {
    pub nodes: (Brace<List<Symbol, VariableLvalue>>,),
}

#[derive(Clone, Debug, Node)]
pub struct VariableLvaluePattern {
    pub nodes: (
        Option<AssignmentPatternExpressionType>,
        AssignmentPatternVariableLvalue,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct NonrangeVariableLvalue {
    pub nodes: (
        Option<ImplicitClassHandleOrPackageScope>,
        HierarchicalVariableIdentifier,
        NonrangeSelect,
    ),
}

// -----------------------------------------------------------------------------

#[packrat_parser]
#[parser]
pub fn net_lvalue(s: Span) -> IResult<Span, NetLvalue> {
    alt((net_lvalue_identifier, net_lvalue_lvalue, net_lvalue_pattern))(s)
}

#[parser]
pub fn net_lvalue_identifier(s: Span) -> IResult<Span, NetLvalue> {
    let (s, a) = ps_or_hierarchical_net_identifier(s)?;
    let (s, b) = constant_select(s)?;
    Ok((
        s,
        NetLvalue::Identifier(NetLvalueIdentifier { nodes: (a, b) }),
    ))
}

#[parser]
pub fn net_lvalue_pattern(s: Span) -> IResult<Span, NetLvalue> {
    let (s, a) = opt(assignment_pattern_expression_type)(s)?;
    let (s, b) = assignment_pattern_net_lvalue(s)?;
    Ok((
        s,
        NetLvalue::Pattern(Box::new(NetLvaluePattern { nodes: (a, b) })),
    ))
}

#[parser]
pub fn net_lvalue_lvalue(s: Span) -> IResult<Span, NetLvalue> {
    let (s, a) = brace(list(symbol(","), net_lvalue))(s)?;
    Ok((
        s,
        NetLvalue::Lvalue(Box::new(NetLvalueLvalue { nodes: (a,) })),
    ))
}

#[packrat_parser]
#[parser]
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

#[parser]
pub fn variable_lvalue_identifier(s: Span) -> IResult<Span, VariableLvalue> {
    let (s, a) = opt(implicit_class_handle_or_package_scope)(s)?;
    let (s, b) = hierarchical_variable_identifier(s)?;
    let (s, c) = select(s)?;
    Ok((
        s,
        VariableLvalue::Identifier(VariableLvalueIdentifier { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn variable_lvalue_pattern(s: Span) -> IResult<Span, VariableLvalue> {
    let (s, a) = opt(assignment_pattern_expression_type)(s)?;
    let (s, b) = assignment_pattern_variable_lvalue(s)?;
    Ok((
        s,
        VariableLvalue::Pattern(Box::new(VariableLvaluePattern { nodes: (a, b) })),
    ))
}

#[parser]
pub fn variable_lvalue_lvalue(s: Span) -> IResult<Span, VariableLvalue> {
    let (s, a) = brace(list(symbol(","), variable_lvalue))(s)?;
    Ok((
        s,
        VariableLvalue::Lvalue(Box::new(VariableLvalueLvalue { nodes: (a,) })),
    ))
}

#[parser]
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
        parser_test!(nonrange_variable_lvalue, "A[1][2][3]", Ok((_, _)));
        //TODO
        //parser_test!(nonrange_variable_lvalue, "A[][2][3]", Ok((_, _)));
        //parser_test!(nonrange_variable_lvalue, "A[][]", Ok((_, _)));
    }
}
