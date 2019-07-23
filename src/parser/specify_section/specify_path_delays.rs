use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum PathDelayValue {
    ListOfPathDelayExpressions(ListOfPathDelayExpressions),
    Paren(PathDelayValueParen),
}

#[derive(Debug, Node)]
pub struct PathDelayValueParen {
    pub nodes: (Paren<ListOfPathDelayExpressions>,),
}

#[derive(Debug, Node)]
pub struct ListOfPathDelayExpressions {
    pub nodes: (List<Symbol, TPathDelayExpression>,),
}

#[derive(Debug, Node)]
pub struct TPathDelayExpression {
    pub nodes: (PathDelayExpression,),
}
#[derive(Debug, Node)]
pub struct PathDelayExpression {
    pub nodes: (ConstantMintypmaxExpression,),
}

#[derive(Debug, Node)]
pub enum EdgeSensitivePathDeclaration {
    Parallel(EdgeSensitivePathDeclarationParallel),
    Full(EdgeSensitivePathDeclarationFull),
}

#[derive(Debug, Node)]
pub struct EdgeSensitivePathDeclarationParallel {
    pub nodes: (ParallelEdgeSensitivePathDescription, Symbol, PathDelayValue),
}

#[derive(Debug, Node)]
pub struct EdgeSensitivePathDeclarationFull {
    pub nodes: (FullEdgeSensitivePathDescription, Symbol, PathDelayValue),
}

#[derive(Debug, Node)]
pub struct ParallelEdgeSensitivePathDescription {
    pub nodes: (
        Paren<(
            Option<EdgeIdentifier>,
            SpecifyInputTerminalDescriptor,
            Option<PolarityOperator>,
            Symbol,
            Paren<(
                SpecifyOutputTerminalDescriptor,
                Option<PolarityOperator>,
                Symbol,
                DataSourceExpression,
            )>,
        )>,
    ),
}

#[derive(Debug, Node)]
pub struct FullEdgeSensitivePathDescription {
    pub nodes: (
        Paren<(
            Option<EdgeIdentifier>,
            ListOfPathInputs,
            Option<PolarityOperator>,
            Symbol,
            Paren<(
                ListOfPathOutputs,
                Option<PolarityOperator>,
                Symbol,
                DataSourceExpression,
            )>,
        )>,
    ),
}

#[derive(Debug, Node)]
pub struct DataSourceExpression {
    pub nodes: (Expression,),
}

#[derive(Debug, Node)]
pub enum EdgeIdentifier {
    Posedge(Keyword),
    Negedge(Keyword),
    Edge(Keyword),
}

#[derive(Debug, Node)]
pub enum StateDependentPathDeclaration {
    IfSimple(StateDependentPathDeclarationIfSimple),
    IfEdgeSensitive(StateDependentPathDeclarationIfEdgeSensitive),
    IfNone(StateDependentPathDeclarationIfNone),
}

#[derive(Debug, Node)]
pub struct StateDependentPathDeclarationIfSimple {
    pub nodes: (Keyword, Paren<ModulePathExpression>, SimplePathDeclaration),
}

#[derive(Debug, Node)]
pub struct StateDependentPathDeclarationIfEdgeSensitive {
    pub nodes: (
        Keyword,
        Paren<ModulePathExpression>,
        EdgeSensitivePathDeclaration,
    ),
}

#[derive(Debug, Node)]
pub struct StateDependentPathDeclarationIfNone {
    pub nodes: (Keyword, SimplePathDeclaration),
}

#[derive(Debug, Node)]
pub struct PolarityOperator {
    pub nodes: (Symbol,),
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
