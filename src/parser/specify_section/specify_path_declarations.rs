use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum PathDeclaration<'a> {
    SimplePathDeclaration((SimplePathDeclaration<'a>, Symbol<'a>)),
    EdgeSensitivePathDeclaration((EdgeSensitivePathDeclaration<'a>, Symbol<'a>)),
    StateDependentPathDeclaration((StateDependentPathDeclaration<'a>, Symbol<'a>)),
}

#[derive(Debug, Node)]
pub enum SimplePathDeclaration<'a> {
    Parallel(SimplePathDeclarationParallel<'a>),
    Full(SimplePathDeclarationFull<'a>),
}

#[derive(Debug, Node)]
pub struct SimplePathDeclarationParallel<'a> {
    pub nodes: (ParallelPathDescription<'a>, Symbol<'a>, PathDelayValue<'a>),
}

#[derive(Debug, Node)]
pub struct SimplePathDeclarationFull<'a> {
    pub nodes: (FullPathDescription<'a>, Symbol<'a>, PathDelayValue<'a>),
}

#[derive(Debug, Node)]
pub struct ParallelPathDescription<'a> {
    pub nodes: (
        Paren<
            'a,
            (
                SpecifyInputTerminalDescriptor<'a>,
                Option<PolarityOperator<'a>>,
                Symbol<'a>,
                SpecifyOutputTerminalDescriptor<'a>,
            ),
        >,
    ),
}

#[derive(Debug, Node)]
pub struct FullPathDescription<'a> {
    pub nodes: (
        Paren<
            'a,
            (
                ListOfPathInputs<'a>,
                Option<PolarityOperator<'a>>,
                Symbol<'a>,
                ListOfPathOutputs<'a>,
            ),
        >,
    ),
}

#[derive(Debug, Node)]
pub struct ListOfPathInputs<'a> {
    pub nodes: (List<Symbol<'a>, SpecifyInputTerminalDescriptor<'a>>,),
}

#[derive(Debug, Node)]
pub struct ListOfPathOutputs<'a> {
    pub nodes: (List<Symbol<'a>, SpecifyOutputTerminalDescriptor<'a>>,),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn path_declaration(s: Span) -> IResult<Span, PathDeclaration> {
    alt((
        map(pair(simple_path_declaration, symbol(";")), |x| {
            PathDeclaration::SimplePathDeclaration(x)
        }),
        map(pair(edge_sensitive_path_declaration, symbol(";")), |x| {
            PathDeclaration::EdgeSensitivePathDeclaration(x)
        }),
        map(pair(state_dependent_path_declaration, symbol(";")), |x| {
            PathDeclaration::StateDependentPathDeclaration(x)
        }),
    ))(s)
}

#[parser]
pub fn simple_path_declaration(s: Span) -> IResult<Span, SimplePathDeclaration> {
    alt((
        simple_path_declaration_parallel,
        simple_path_declaration_full,
    ))(s)
}

#[parser]
pub fn simple_path_declaration_parallel(s: Span) -> IResult<Span, SimplePathDeclaration> {
    let (s, a) = parallel_path_description(s)?;
    let (s, b) = symbol("=")(s)?;
    let (s, c) = path_delay_value(s)?;
    Ok((
        s,
        SimplePathDeclaration::Parallel(SimplePathDeclarationParallel { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn simple_path_declaration_full(s: Span) -> IResult<Span, SimplePathDeclaration> {
    let (s, a) = full_path_description(s)?;
    let (s, b) = symbol("=")(s)?;
    let (s, c) = path_delay_value(s)?;
    Ok((
        s,
        SimplePathDeclaration::Full(SimplePathDeclarationFull { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn parallel_path_description(s: Span) -> IResult<Span, ParallelPathDescription> {
    let (s, a) = paren(tuple((
        specify_input_terminal_descriptor,
        opt(polarity_operator),
        symbol("=>"),
        specify_output_terminal_descriptor,
    )))(s)?;
    Ok((s, ParallelPathDescription { nodes: (a,) }))
}

#[parser]
pub fn full_path_description(s: Span) -> IResult<Span, FullPathDescription> {
    let (s, a) = paren(tuple((
        list_of_path_inputs,
        opt(polarity_operator),
        symbol("*>"),
        list_of_path_outputs,
    )))(s)?;
    Ok((s, FullPathDescription { nodes: (a,) }))
}

#[parser]
pub fn list_of_path_inputs(s: Span) -> IResult<Span, ListOfPathInputs> {
    let (s, a) = list(symbol(","), specify_input_terminal_descriptor)(s)?;
    Ok((s, ListOfPathInputs { nodes: (a,) }))
}

#[parser]
pub fn list_of_path_outputs(s: Span) -> IResult<Span, ListOfPathOutputs> {
    let (s, a) = list(symbol(","), specify_output_terminal_descriptor)(s)?;
    Ok((s, ListOfPathOutputs { nodes: (a,) }))
}
