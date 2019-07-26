use crate::*;

// -----------------------------------------------------------------------------

#[parser]
pub(crate) fn loop_statement(s: Span) -> IResult<Span, LoopStatement> {
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
pub(crate) fn loop_statement_forever(s: Span) -> IResult<Span, LoopStatement> {
    let (s, a) = keyword("forever")(s)?;
    let (s, b) = statement_or_null(s)?;
    Ok((
        s,
        LoopStatement::Forever(Box::new(LoopStatementForever { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn loop_statement_repeat(s: Span) -> IResult<Span, LoopStatement> {
    let (s, a) = keyword("repeat")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = statement_or_null(s)?;
    Ok((
        s,
        LoopStatement::Repeat(Box::new(LoopStatementRepeat { nodes: (a, b, c) })),
    ))
}

#[parser]
pub(crate) fn loop_statement_while(s: Span) -> IResult<Span, LoopStatement> {
    let (s, a) = keyword("while")(s)?;
    let (s, b) = paren(expression)(s)?;
    let (s, c) = statement_or_null(s)?;
    Ok((
        s,
        LoopStatement::While(Box::new(LoopStatementWhile { nodes: (a, b, c) })),
    ))
}

#[parser]
pub(crate) fn loop_statement_for(s: Span) -> IResult<Span, LoopStatement> {
    let (s, a) = keyword("for")(s)?;
    let (s, b) = paren(tuple((
        opt(for_initialization),
        symbol(":"),
        opt(expression),
        symbol(":"),
        opt(for_step),
    )))(s)?;
    let (s, c) = statement_or_null(s)?;
    Ok((
        s,
        LoopStatement::For(Box::new(LoopStatementFor { nodes: (a, b, c) })),
    ))
}

#[parser]
pub(crate) fn loop_statement_do_while(s: Span) -> IResult<Span, LoopStatement> {
    let (s, a) = keyword("do")(s)?;
    let (s, b) = statement_or_null(s)?;
    let (s, c) = keyword("while")(s)?;
    let (s, d) = paren(expression)(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        LoopStatement::DoWhile(Box::new(LoopStatementDoWhile {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[parser]
pub(crate) fn loop_statement_foreach(s: Span) -> IResult<Span, LoopStatement> {
    let (s, a) = keyword("foreach")(s)?;
    let (s, b) = paren(pair(
        ps_or_hierarchical_array_identifier,
        bracket(loop_variables),
    ))(s)?;
    let (s, c) = statement(s)?;
    Ok((
        s,
        LoopStatement::Foreach(Box::new(LoopStatementForeach { nodes: (a, b, c) })),
    ))
}

#[parser]
pub(crate) fn for_initialization(s: Span) -> IResult<Span, ForInitialization> {
    alt((
        map(list_of_variable_assignments, |x| {
            ForInitialization::ListOfVariableAssignments(Box::new(x))
        }),
        for_initialization_declaration,
    ))(s)
}

#[recursive_parser]
#[parser]
pub(crate) fn for_initialization_declaration(s: Span) -> IResult<Span, ForInitialization> {
    let (s, a) = list(symbol(","), for_variable_declaration)(s)?;
    Ok((
        s,
        ForInitialization::Declaration(Box::new(ForInitializationDeclaration { nodes: (a,) })),
    ))
}

#[parser]
pub(crate) fn for_variable_declaration(s: Span) -> IResult<Span, ForVariableDeclaration> {
    let (s, a) = opt(var)(s)?;
    let (s, b) = data_type(s)?;
    let (s, c) = list(
        symbol(","),
        triple(variable_identifier, symbol("="), expression),
    )(s)?;
    Ok((s, ForVariableDeclaration { nodes: (a, b, c) }))
}

#[parser]
pub(crate) fn var(s: Span) -> IResult<Span, Var> {
    let (s, a) = keyword("var")(s)?;
    Ok((s, Var { nodes: (a,) }))
}

#[recursive_parser]
#[parser]
pub(crate) fn for_step(s: Span) -> IResult<Span, ForStep> {
    let (s, a) = list(symbol(","), for_step_assignment)(s)?;
    Ok((s, ForStep { nodes: (a,) }))
}

#[parser]
pub(crate) fn for_step_assignment(s: Span) -> IResult<Span, ForStepAssignment> {
    alt((
        map(operator_assignment, |x| {
            ForStepAssignment::OperatorAssignment(Box::new(x))
        }),
        map(inc_or_dec_expression, |x| {
            ForStepAssignment::IncOrDecExpression(Box::new(x))
        }),
        map(function_subroutine_call, |x| {
            ForStepAssignment::FunctionSubroutineCall(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn loop_variables(s: Span) -> IResult<Span, LoopVariables> {
    let (s, a) = list(symbol(","), opt(index_variable_identifier))(s)?;
    Ok((s, LoopVariables { nodes: (a,) }))
}
