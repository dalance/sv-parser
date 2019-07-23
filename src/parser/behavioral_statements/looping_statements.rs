use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum LoopStatement {
    Forever(LoopStatementForever),
    Repeat(LoopStatementRepeat),
    While(LoopStatementWhile),
    For(LoopStatementFor),
    DoWhile(LoopStatementDoWhile),
    Foreach(LoopStatementForeach),
}

#[derive(Debug, Node)]
pub struct LoopStatementForever {
    pub nodes: (Keyword, StatementOrNull),
}

#[derive(Debug, Node)]
pub struct LoopStatementRepeat {
    pub nodes: (Keyword, Paren<Expression>, StatementOrNull),
}

#[derive(Debug, Node)]
pub struct LoopStatementWhile {
    pub nodes: (Keyword, Paren<Expression>, StatementOrNull),
}

#[derive(Debug, Node)]
pub struct LoopStatementFor {
    pub nodes: (
        Keyword,
        Paren<(
            Option<ForInitialization>,
            Symbol,
            Option<Expression>,
            Symbol,
            Option<ForStep>,
        )>,
        StatementOrNull,
    ),
}

#[derive(Debug, Node)]
pub struct LoopStatementDoWhile {
    pub nodes: (Keyword, StatementOrNull, Keyword, Paren<Expression>, Symbol),
}

#[derive(Debug, Node)]
pub struct LoopStatementForeach {
    pub nodes: (
        Keyword,
        Paren<(PsOrHierarchicalArrayIdentifier, Bracket<LoopVariables>)>,
        Statement,
    ),
}

#[derive(Debug, Node)]
pub enum ForInitialization {
    ListOfVariableAssignments(ListOfVariableAssignments),
    Declaration(ForInitializationDeclaration),
}

#[derive(Debug, Node)]
pub struct ForInitializationDeclaration {
    pub nodes: (List<Symbol, ForVariableDeclaration>,),
}

#[derive(Debug, Node)]
pub struct ForVariableDeclaration {
    pub nodes: (
        Option<Var>,
        DataType,
        List<Symbol, (VariableIdentifier, Symbol, Expression)>,
    ),
}

#[derive(Debug, Node)]
pub struct Var {
    pub nodes: (Keyword,),
}

#[derive(Debug, Node)]
pub struct ForStep {
    pub nodes: (List<Symbol, ForStepAssignment>,),
}

#[derive(Debug, Node)]
pub enum ForStepAssignment {
    OperatorAssignment(OperatorAssignment),
    IncOrDecExpression(IncOrDecExpression),
    FunctionSubroutineCall(FunctionSubroutineCall),
}

#[derive(Debug, Node)]
pub struct LoopVariables {
    pub nodes: (List<Symbol, Option<IndexVariableIdentifier>>,),
}

// -----------------------------------------------------------------------------

#[parser]
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

#[parser]
pub fn loop_statement_forever(s: Span) -> IResult<Span, LoopStatement> {
    let (s, a) = keyword("forever")(s)?;
    let (s, b) = statement_or_null(s)?;
    Ok((
        s,
        LoopStatement::Forever(LoopStatementForever { nodes: (a, b) }),
    ))
}

#[parser]
pub fn loop_statement_repeat(s: Span) -> IResult<Span, LoopStatement> {
    let (s, a) = keyword("repeat")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = statement_or_null(s)?;
    Ok((
        s,
        LoopStatement::Repeat(LoopStatementRepeat { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn loop_statement_while(s: Span) -> IResult<Span, LoopStatement> {
    let (s, a) = keyword("while")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = statement_or_null(s)?;
    Ok((
        s,
        LoopStatement::While(LoopStatementWhile { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn loop_statement_for(s: Span) -> IResult<Span, LoopStatement> {
    let (s, a) = keyword("for")(s)?;
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

#[parser]
pub fn loop_statement_do_while(s: Span) -> IResult<Span, LoopStatement> {
    let (s, a) = keyword("do")(s)?;
    let (s, b) = statement_or_null(s)?;
    let (s, c) = keyword("while")(s)?;
    let (s, d) = paren(expression)(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        LoopStatement::DoWhile(LoopStatementDoWhile {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser]
pub fn loop_statement_foreach(s: Span) -> IResult<Span, LoopStatement> {
    let (s, a) = keyword("foreach")(s)?;
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

#[parser]
pub fn for_initialization(s: Span) -> IResult<Span, ForInitialization> {
    alt((
        map(list_of_variable_assignments, |x| {
            ForInitialization::ListOfVariableAssignments(x)
        }),
        for_initialization_declaration,
    ))(s)
}

#[parser(MaybeRecursive)]
pub fn for_initialization_declaration(s: Span) -> IResult<Span, ForInitialization> {
    let (s, a) = list(symbol(","), for_variable_declaration)(s)?;
    Ok((
        s,
        ForInitialization::Declaration(ForInitializationDeclaration { nodes: (a,) }),
    ))
}

#[parser]
pub fn for_variable_declaration(s: Span) -> IResult<Span, ForVariableDeclaration> {
    let (s, a) = opt(var)(s)?;
    let (s, b) = data_type(s)?;
    let (s, c) = list(
        symbol(","),
        triple(variable_identifier, symbol("="), expression),
    )(s)?;
    Ok((s, ForVariableDeclaration { nodes: (a, b, c) }))
}

#[parser]
pub fn var(s: Span) -> IResult<Span, Var> {
    let (s, a) = keyword("var")(s)?;
    Ok((s, Var { nodes: (a,) }))
}

#[parser(MaybeRecursive)]
pub fn for_step(s: Span) -> IResult<Span, ForStep> {
    let (s, a) = list(symbol(","), for_step_assignment)(s)?;
    Ok((s, ForStep { nodes: (a,) }))
}

#[parser]
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

#[parser]
pub fn loop_variables(s: Span) -> IResult<Span, LoopVariables> {
    let (s, a) = list(symbol(","), opt(index_variable_identifier))(s)?;
    Ok((s, LoopVariables { nodes: (a,) }))
}

// -----------------------------------------------------------------------------
