use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum PathDelayValue<'a> {
    ListOfPathDelayExpressions(ListOfPathDelayExpressions<'a>),
    Paren(PathDelayValueParen<'a>),
}

#[derive(Debug, Node)]
pub struct PathDelayValueParen<'a> {
    pub nodes: (Paren<'a, ListOfPathDelayExpressions<'a>>,),
}

#[derive(Debug, Node)]
pub struct ListOfPathDelayExpressions<'a> {
    pub nodes: (List<Symbol<'a>, TPathDelayExpression<'a>>,),
}

#[derive(Debug, Node)]
pub struct TPathDelayExpression<'a> {
    pub nodes: (PathDelayExpression<'a>,),
}
#[derive(Debug, Node)]
pub struct PathDelayExpression<'a> {
    pub nodes: (ConstantMintypmaxExpression<'a>,),
}

#[derive(Debug, Node)]
pub enum EdgeSensitivePathDeclaration<'a> {
    Parallel(EdgeSensitivePathDeclarationParallel<'a>),
    Full(EdgeSensitivePathDeclarationFull<'a>),
}

#[derive(Debug, Node)]
pub struct EdgeSensitivePathDeclarationParallel<'a> {
    pub nodes: (
        ParallelEdgeSensitivePathDescription<'a>,
        Symbol<'a>,
        PathDelayValue<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct EdgeSensitivePathDeclarationFull<'a> {
    pub nodes: (
        FullEdgeSensitivePathDescription<'a>,
        Symbol<'a>,
        PathDelayValue<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct ParallelEdgeSensitivePathDescription<'a> {
    pub nodes: (
        Paren<
            'a,
            (
                Option<EdgeIdentifier<'a>>,
                SpecifyInputTerminalDescriptor<'a>,
                Option<PolarityOperator<'a>>,
                Symbol<'a>,
                Paren<
                    'a,
                    (
                        SpecifyOutputTerminalDescriptor<'a>,
                        Option<PolarityOperator<'a>>,
                        Symbol<'a>,
                        DataSourceExpression<'a>,
                    ),
                >,
            ),
        >,
    ),
}

#[derive(Debug, Node)]
pub struct FullEdgeSensitivePathDescription<'a> {
    pub nodes: (
        Paren<
            'a,
            (
                Option<EdgeIdentifier<'a>>,
                ListOfPathInputs<'a>,
                Option<PolarityOperator<'a>>,
                Symbol<'a>,
                Paren<
                    'a,
                    (
                        ListOfPathOutputs<'a>,
                        Option<PolarityOperator<'a>>,
                        Symbol<'a>,
                        DataSourceExpression<'a>,
                    ),
                >,
            ),
        >,
    ),
}

#[derive(Debug, Node)]
pub struct DataSourceExpression<'a> {
    pub nodes: (Expression<'a>,),
}

#[derive(Debug, Node)]
pub enum EdgeIdentifier<'a> {
    Posedge(Symbol<'a>),
    Negedge(Symbol<'a>),
    Edge(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum StateDependentPathDeclaration<'a> {
    IfSimple(StateDependentPathDeclarationIfSimple<'a>),
    IfEdgeSensitive(StateDependentPathDeclarationIfEdgeSensitive<'a>),
    IfNone(StateDependentPathDeclarationIfNone<'a>),
}

#[derive(Debug, Node)]
pub struct StateDependentPathDeclarationIfSimple<'a> {
    pub nodes: (
        Symbol<'a>,
        Paren<'a, ModulePathExpression<'a>>,
        SimplePathDeclaration<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct StateDependentPathDeclarationIfEdgeSensitive<'a> {
    pub nodes: (
        Symbol<'a>,
        Paren<'a, ModulePathExpression<'a>>,
        EdgeSensitivePathDeclaration<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct StateDependentPathDeclarationIfNone<'a> {
    pub nodes: (Symbol<'a>, SimplePathDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct PolarityOperator<'a> {
    pub nodes: (Symbol<'a>,),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn path_delay_value(s: Span) -> IResult<Span, PathDelayValue> {
    alt((
        map(list_of_path_delay_expressions, |x| {
            PathDelayValue::ListOfPathDelayExpressions(x)
        }),
        path_delay_value_paren,
    ))(s)
}

#[parser]
pub fn path_delay_value_paren(s: Span) -> IResult<Span, PathDelayValue> {
    let (s, a) = paren(list_of_path_delay_expressions)(s)?;
    Ok((
        s,
        PathDelayValue::Paren(PathDelayValueParen { nodes: (a,) }),
    ))
}

#[parser]
pub fn list_of_path_delay_expressions(s: Span) -> IResult<Span, ListOfPathDelayExpressions> {
    let (s, a) = list(symbol(","), t_path_delay_expression)(s)?;
    Ok((s, ListOfPathDelayExpressions { nodes: (a,) }))
}

#[parser]
pub fn t_path_delay_expression(s: Span) -> IResult<Span, TPathDelayExpression> {
    let (s, a) = path_delay_expression(s)?;
    Ok((s, TPathDelayExpression { nodes: (a,) }))
}

#[parser]
pub fn path_delay_expression(s: Span) -> IResult<Span, PathDelayExpression> {
    let (s, a) = constant_mintypmax_expression(s)?;
    Ok((s, PathDelayExpression { nodes: (a,) }))
}

#[parser]
pub fn edge_sensitive_path_declaration(s: Span) -> IResult<Span, EdgeSensitivePathDeclaration> {
    alt((
        edge_sensitive_path_declaration_parallel,
        edge_sensitive_path_declaration_full,
    ))(s)
}

#[parser]
pub fn edge_sensitive_path_declaration_parallel(
    s: Span,
) -> IResult<Span, EdgeSensitivePathDeclaration> {
    let (s, a) = parallel_edge_sensitive_path_description(s)?;
    let (s, b) = symbol("=")(s)?;
    let (s, c) = path_delay_value(s)?;
    Ok((
        s,
        EdgeSensitivePathDeclaration::Parallel(EdgeSensitivePathDeclarationParallel {
            nodes: (a, b, c),
        }),
    ))
}

#[parser]
pub fn edge_sensitive_path_declaration_full(
    s: Span,
) -> IResult<Span, EdgeSensitivePathDeclaration> {
    let (s, a) = full_edge_sensitive_path_description(s)?;
    let (s, b) = symbol("=")(s)?;
    let (s, c) = path_delay_value(s)?;
    Ok((
        s,
        EdgeSensitivePathDeclaration::Full(EdgeSensitivePathDeclarationFull { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn parallel_edge_sensitive_path_description(
    s: Span,
) -> IResult<Span, ParallelEdgeSensitivePathDescription> {
    let (s, a) = paren(tuple((
        opt(edge_identifier),
        specify_input_terminal_descriptor,
        opt(polarity_operator),
        symbol("=>"),
        paren(tuple((
            specify_output_terminal_descriptor,
            opt(polarity_operator),
            symbol(":"),
            data_source_expression,
        ))),
    )))(s)?;
    Ok((s, ParallelEdgeSensitivePathDescription { nodes: (a,) }))
}

#[parser]
pub fn full_edge_sensitive_path_description(
    s: Span,
) -> IResult<Span, FullEdgeSensitivePathDescription> {
    let (s, a) = paren(tuple((
        opt(edge_identifier),
        list_of_path_inputs,
        opt(polarity_operator),
        symbol("*>"),
        paren(tuple((
            list_of_path_outputs,
            opt(polarity_operator),
            symbol(":"),
            data_source_expression,
        ))),
    )))(s)?;
    Ok((s, FullEdgeSensitivePathDescription { nodes: (a,) }))
}

#[parser]
pub fn data_source_expression(s: Span) -> IResult<Span, DataSourceExpression> {
    let (s, a) = expression(s)?;
    Ok((s, DataSourceExpression { nodes: (a,) }))
}

#[parser]
pub fn edge_identifier(s: Span) -> IResult<Span, EdgeIdentifier> {
    alt((
        map(keyword("posedge"), |x| EdgeIdentifier::Posedge(x)),
        map(keyword("negedge"), |x| EdgeIdentifier::Negedge(x)),
        map(keyword("edge"), |x| EdgeIdentifier::Edge(x)),
    ))(s)
}

#[parser]
pub fn state_dependent_path_declaration(s: Span) -> IResult<Span, StateDependentPathDeclaration> {
    alt((
        state_dependent_path_declaration_if_simple,
        state_dependent_path_declaration_if_edge_sensitive,
        state_dependent_path_declaration_if_none,
    ))(s)
}

#[parser]
pub fn state_dependent_path_declaration_if_simple(
    s: Span,
) -> IResult<Span, StateDependentPathDeclaration> {
    let (s, a) = keyword("if")(s)?;
    let (s, b) = paren(module_path_expression)(s)?;
    let (s, c) = simple_path_declaration(s)?;
    Ok((
        s,
        StateDependentPathDeclaration::IfSimple(StateDependentPathDeclarationIfSimple {
            nodes: (a, b, c),
        }),
    ))
}

#[parser]
pub fn state_dependent_path_declaration_if_edge_sensitive(
    s: Span,
) -> IResult<Span, StateDependentPathDeclaration> {
    let (s, a) = keyword("if")(s)?;
    let (s, b) = paren(module_path_expression)(s)?;
    let (s, c) = edge_sensitive_path_declaration(s)?;
    Ok((
        s,
        StateDependentPathDeclaration::IfEdgeSensitive(
            StateDependentPathDeclarationIfEdgeSensitive { nodes: (a, b, c) },
        ),
    ))
}

#[parser]
pub fn state_dependent_path_declaration_if_none(
    s: Span,
) -> IResult<Span, StateDependentPathDeclaration> {
    let (s, a) = keyword("ifnone")(s)?;
    let (s, b) = simple_path_declaration(s)?;
    Ok((
        s,
        StateDependentPathDeclaration::IfNone(StateDependentPathDeclarationIfNone {
            nodes: (a, b),
        }),
    ))
}

#[parser]
pub fn polarity_operator(s: Span) -> IResult<Span, PolarityOperator> {
    alt((
        map(symbol("+"), |x| PolarityOperator { nodes: (x,) }),
        map(symbol("-"), |x| PolarityOperator { nodes: (x,) }),
    ))(s)
}
