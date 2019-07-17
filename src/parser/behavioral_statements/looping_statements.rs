use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum LoopStatement<'a> {
    Forever(LoopStatementForever<'a>),
    Repeat(LoopStatementRepeat<'a>),
    While(LoopStatementWhile<'a>),
    For(LoopStatementFor<'a>),
    DoWhile(LoopStatementDoWhile<'a>),
    Foreach(LoopStatementForeach<'a>),
}

#[derive(Debug, Node)]
pub struct LoopStatementForever<'a> {
    pub nodes: (Symbol<'a>, StatementOrNull<'a>),
}

#[derive(Debug, Node)]
pub struct LoopStatementRepeat<'a> {
    pub nodes: (Symbol<'a>, Paren<'a, Expression<'a>>, StatementOrNull<'a>),
}

#[derive(Debug, Node)]
pub struct LoopStatementWhile<'a> {
    pub nodes: (Symbol<'a>, Paren<'a, Expression<'a>>, StatementOrNull<'a>),
}

#[derive(Debug, Node)]
pub struct LoopStatementFor<'a> {
    pub nodes: (
        Symbol<'a>,
        Paren<
            'a,
            (
                Option<ForInitialization<'a>>,
                Symbol<'a>,
                Option<Expression<'a>>,
                Symbol<'a>,
                Option<ForStep<'a>>,
            ),
        >,
        StatementOrNull<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct LoopStatementDoWhile<'a> {
    pub nodes: (
        Symbol<'a>,
        StatementOrNull<'a>,
        Symbol<'a>,
        Paren<'a, Expression<'a>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct LoopStatementForeach<'a> {
    pub nodes: (
        Symbol<'a>,
        Paren<
            'a,
            (
                PsOrHierarchicalArrayIdentifier<'a>,
                Bracket<'a, LoopVariables<'a>>,
            ),
        >,
        Statement<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum ForInitialization<'a> {
    ListOfVariableAssignments(ListOfVariableAssignments<'a>),
    Declaration(ForInitializationDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct ForInitializationDeclaration<'a> {
    pub nodes: (List<Symbol<'a>, ForVariableDeclaration<'a>>,),
}

#[derive(Debug, Node)]
pub struct ForVariableDeclaration<'a> {
    pub nodes: (
        Option<Var<'a>>,
        DataType<'a>,
        List<Symbol<'a>, (VariableIdentifier<'a>, Symbol<'a>, Expression<'a>)>,
    ),
}

#[derive(Debug, Node)]
pub struct Var<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug, Node)]
pub struct ForStep<'a> {
    pub nodes: (List<Symbol<'a>, ForStepAssignment<'a>>,),
}

#[derive(Debug, Node)]
pub enum ForStepAssignment<'a> {
    OperatorAssignment(OperatorAssignment<'a>),
    IncOrDecExpression(IncOrDecExpression<'a>),
    FunctionSubroutineCall(FunctionSubroutineCall<'a>),
}

#[derive(Debug, Node)]
pub struct LoopVariables<'a> {
    pub nodes: (List<Symbol<'a>, Option<IndexVariableIdentifier<'a>>>,),
}

// -----------------------------------------------------------------------------

#[trace]
pub fn loop_statement(s: Span) -> IResult<Span, LoopStatement> {
    alt((
        loop_statement_forever,
        loop_statement_repeat,
        loop_statement_while,
        loop_statement_for,
        loop_statement_do_while,
        loop_statement_foreach,
    ))(s)
}

#[trace]
pub fn loop_statement_forever(s: Span) -> IResult<Span, LoopStatement> {
    let (s, a) = symbol("forever")(s)?;
    let (s, b) = statement_or_null(s)?;
    Ok((
        s,
        LoopStatement::Forever(LoopStatementForever { nodes: (a, b) }),
    ))
}

#[trace]
pub fn loop_statement_repeat(s: Span) -> IResult<Span, LoopStatement> {
    let (s, a) = symbol("repeat")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = statement_or_null(s)?;
    Ok((
        s,
        LoopStatement::Repeat(LoopStatementRepeat { nodes: (a, b, c) }),
    ))
}

#[trace]
pub fn loop_statement_while(s: Span) -> IResult<Span, LoopStatement> {
    let (s, a) = symbol("while")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = statement_or_null(s)?;
    Ok((
        s,
        LoopStatement::While(LoopStatementWhile { nodes: (a, b, c) }),
    ))
}

#[trace]
pub fn loop_statement_for(s: Span) -> IResult<Span, LoopStatement> {
    let (s, a) = symbol("for")(s)?;
    let (s, b) = paren(tuple((
        opt(for_initialization),
        symbol(":"),
        opt(expression),
        symbol(":"),
        opt(for_step),
    )))(s)?;
    let (s, c) = statement_or_null(s)?;
    Ok((s, LoopStatement::For(LoopStatementFor { nodes: (a, b, c) })))
}

#[trace]
pub fn loop_statement_do_while(s: Span) -> IResult<Span, LoopStatement> {
    let (s, a) = symbol("do")(s)?;
    let (s, b) = statement_or_null(s)?;
    let (s, c) = symbol("while")(s)?;
    let (s, d) = paren(expression)(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        LoopStatement::DoWhile(LoopStatementDoWhile {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[trace]
pub fn loop_statement_foreach(s: Span) -> IResult<Span, LoopStatement> {
    let (s, a) = symbol("foreach")(s)?;
    let (s, b) = paren(pair(
        ps_or_hierarchical_array_identifier,
        bracket(loop_variables),
    ))(s)?;
    let (s, c) = statement(s)?;
    Ok((
        s,
        LoopStatement::Foreach(LoopStatementForeach { nodes: (a, b, c) }),
    ))
}

#[trace]
pub fn for_initialization(s: Span) -> IResult<Span, ForInitialization> {
    alt((
        map(list_of_variable_assignments, |x| {
            ForInitialization::ListOfVariableAssignments(x)
        }),
        for_initialization_declaration,
    ))(s)
}

#[trace]
pub fn for_initialization_declaration(s: Span) -> IResult<Span, ForInitialization> {
    let (s, a) = list(symbol(","), for_variable_declaration)(s)?;
    Ok((
        s,
        ForInitialization::Declaration(ForInitializationDeclaration { nodes: (a,) }),
    ))
}

#[trace]
pub fn for_variable_declaration(s: Span) -> IResult<Span, ForVariableDeclaration> {
    let (s, a) = opt(var)(s)?;
    let (s, b) = data_type(s)?;
    let (s, c) = list(
        symbol(","),
        triple(variable_identifier, symbol("="), expression),
    )(s)?;
    Ok((s, ForVariableDeclaration { nodes: (a, b, c) }))
}

#[trace]
pub fn var(s: Span) -> IResult<Span, Var> {
    let (s, a) = symbol("var")(s)?;
    Ok((s, Var { nodes: (a,) }))
}

#[trace]
pub fn for_step(s: Span) -> IResult<Span, ForStep> {
    let (s, a) = list(symbol(","), for_step_assignment)(s)?;
    Ok((s, ForStep { nodes: (a,) }))
}

#[trace]
pub fn for_step_assignment(s: Span) -> IResult<Span, ForStepAssignment> {
    alt((
        map(operator_assignment, |x| {
            ForStepAssignment::OperatorAssignment(x)
        }),
        map(inc_or_dec_expression, |x| {
            ForStepAssignment::IncOrDecExpression(x)
        }),
        map(function_subroutine_call, |x| {
            ForStepAssignment::FunctionSubroutineCall(x)
        }),
    ))(s)
}

#[trace]
pub fn loop_variables(s: Span) -> IResult<Span, LoopVariables> {
    let (s, a) = list(symbol(","), opt(index_variable_identifier))(s)?;
    Ok((s, LoopVariables { nodes: (a,) }))
}

// -----------------------------------------------------------------------------
