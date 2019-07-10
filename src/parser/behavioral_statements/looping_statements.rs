use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum LoopStatement<'a> {
    Forever(LoopStatementForever<'a>),
    Repeat(LoopStatementRepeat<'a>),
    While(LoopStatementWhile<'a>),
    For(LoopStatementFor<'a>),
    DoWhile(LoopStatementDoWhile<'a>),
    Foreach(LoopStatementForeach<'a>),
}

#[derive(Debug)]
pub struct LoopStatementForever<'a> {
    pub nodes: (StatementOrNull<'a>,),
}

#[derive(Debug)]
pub struct LoopStatementRepeat<'a> {
    pub nodes: (Expression<'a>, StatementOrNull<'a>),
}

#[derive(Debug)]
pub struct LoopStatementWhile<'a> {
    pub nodes: (Expression<'a>, StatementOrNull<'a>),
}

#[derive(Debug)]
pub struct LoopStatementFor<'a> {
    pub nodes: (
        Option<ForInitialization<'a>>,
        Option<Expression<'a>>,
        Option<Vec<ForStepAssignment<'a>>>,
        StatementOrNull<'a>,
    ),
}

#[derive(Debug)]
pub struct LoopStatementDoWhile<'a> {
    pub nodes: (StatementOrNull<'a>, Expression<'a>),
}

#[derive(Debug)]
pub struct LoopStatementForeach<'a> {
    pub nodes: (
        PsOrHierarchicalArrayIdentifier<'a>,
        LoopVariables<'a>,
        Statement<'a>,
    ),
}

#[derive(Debug)]
pub enum ForInitialization<'a> {
    Assignment(ListOfVariableAssignments<'a>),
    Declaration(Vec<ForVariableDeclaration<'a>>),
}

#[derive(Debug)]
pub struct ForVariableDeclaration<'a> {
    pub nodes: (
        Option<Var>,
        DataType<'a>,
        Vec<(VariableIdentifier<'a>, Expression<'a>)>,
    ),
}

#[derive(Debug)]
pub struct Var {}

#[derive(Debug)]
pub enum ForStepAssignment<'a> {
    OperatorAssignment(OperatorAssignment<'a>),
    IncOrDecExpression(IncOrDecExpression<'a>),
    FunctionSubroutineCall(FunctionSubroutineCall<'a>),
}

#[derive(Debug)]
pub struct LoopVariables<'a> {
    pub nodes: (Vec<Option<IndexVariableIdentifier<'a>>>,),
}

// -----------------------------------------------------------------------------

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

pub fn loop_statement_forever(s: Span) -> IResult<Span, LoopStatement> {
    let (s, _) = symbol("forever")(s)?;
    let (s, x) = statement_or_null(s)?;
    Ok((
        s,
        LoopStatement::Forever(LoopStatementForever { nodes: (x,) }),
    ))
}

pub fn loop_statement_repeat(s: Span) -> IResult<Span, LoopStatement> {
    let (s, _) = symbol("repeat")(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, x) = expression(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, y) = statement_or_null(s)?;
    Ok((
        s,
        LoopStatement::Repeat(LoopStatementRepeat { nodes: (x, y) }),
    ))
}

pub fn loop_statement_while(s: Span) -> IResult<Span, LoopStatement> {
    let (s, _) = symbol("while")(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, x) = expression(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, y) = statement_or_null(s)?;
    Ok((
        s,
        LoopStatement::While(LoopStatementWhile { nodes: (x, y) }),
    ))
}

pub fn loop_statement_for(s: Span) -> IResult<Span, LoopStatement> {
    let (s, _) = symbol("for")(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, x) = opt(for_initialization)(s)?;
    let (s, _) = symbol(";")(s)?;
    let (s, y) = opt(expression)(s)?;
    let (s, _) = symbol(";")(s)?;
    let (s, z) = opt(for_step)(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, v) = statement_or_null(s)?;
    Ok((
        s,
        LoopStatement::For(LoopStatementFor {
            nodes: (x, y, z, v),
        }),
    ))
}

pub fn loop_statement_do_while(s: Span) -> IResult<Span, LoopStatement> {
    let (s, _) = symbol("do")(s)?;
    let (s, x) = statement_or_null(s)?;
    let (s, _) = symbol("while")(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, y) = expression(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((
        s,
        LoopStatement::DoWhile(LoopStatementDoWhile { nodes: (x, y) }),
    ))
}

pub fn loop_statement_foreach(s: Span) -> IResult<Span, LoopStatement> {
    let (s, _) = symbol("foreach")(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, x) = ps_or_hierarchical_array_identifier(s)?;
    let (s, _) = symbol("[")(s)?;
    let (s, y) = loop_variables(s)?;
    let (s, _) = symbol("]")(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, z) = statement(s)?;
    Ok((
        s,
        LoopStatement::Foreach(LoopStatementForeach { nodes: (x, y, z) }),
    ))
}

pub fn for_initialization(s: Span) -> IResult<Span, ForInitialization> {
    alt((
        map(list_of_variable_assignments, |x| {
            ForInitialization::Assignment(x)
        }),
        map(
            separated_nonempty_list(symbol(","), for_variable_declaration),
            |x| ForInitialization::Declaration(x),
        ),
    ))(s)
}

pub fn for_variable_declaration(s: Span) -> IResult<Span, ForVariableDeclaration> {
    let (s, x) = opt(symbol("var"))(s)?;
    let (s, y) = data_type(s)?;
    let (s, z) = separated_nonempty_list(
        symbol(","),
        pair(variable_identifier, preceded(symbol("="), expression)),
    )(s)?;
    Ok((
        s,
        ForVariableDeclaration {
            nodes: (x.map(|_| Var {}), y, z),
        },
    ))
}

pub fn for_step(s: Span) -> IResult<Span, Vec<ForStepAssignment>> {
    separated_nonempty_list(symbol(","), for_step_assignment)(s)
}

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

pub fn loop_variables(s: Span) -> IResult<Span, LoopVariables> {
    let (s, x) = separated_nonempty_list(symbol(","), opt(index_variable_identifier))(s)?;
    Ok((s, LoopVariables { nodes: (x,) }))
}

// -----------------------------------------------------------------------------
