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
    pub statement: StatementOrNull<'a>,
}

#[derive(Debug)]
pub struct LoopStatementRepeat<'a> {
    pub expression: Expression<'a>,
    pub statement: StatementOrNull<'a>,
}

#[derive(Debug)]
pub struct LoopStatementWhile<'a> {
    pub expression: Expression<'a>,
    pub statement: StatementOrNull<'a>,
}

#[derive(Debug)]
pub struct LoopStatementFor<'a> {
    pub initilization: Option<ForInitialization<'a>>,
    pub expression: Option<Expression<'a>>,
    pub step: Option<Vec<ForStepAssignment<'a>>>,
    pub statement: StatementOrNull<'a>,
}

#[derive(Debug)]
pub struct LoopStatementDoWhile<'a> {
    pub statement: StatementOrNull<'a>,
    pub expression: Expression<'a>,
}

#[derive(Debug)]
pub struct LoopStatementForeach<'a> {
    pub identifier: ScopedIdentifier<'a>,
    pub variable: Vec<Option<Identifier<'a>>>,
    pub statement: Statement<'a>,
}

#[derive(Debug)]
pub enum ForInitialization<'a> {
    Assignment(Vec<VariableAssignment<'a>>),
    Declaration(Vec<ForVariableDeclaration<'a>>),
}

#[derive(Debug)]
pub struct ForVariableDeclaration<'a> {
    pub var: bool,
    pub r#type: DataType<'a>,
    pub declaration: Vec<(Identifier<'a>, Expression<'a>)>,
}

#[derive(Debug)]
pub enum ForStepAssignment<'a> {
    Operator(OperatorAssignment<'a>),
    IncOrDec(IncOrDecDeclaration<'a>),
    Subroutine(SubroutineCall<'a>),
}

// -----------------------------------------------------------------------------

pub fn loop_statement(s: &str) -> IResult<&str, LoopStatement> {
    alt((
        loop_statement_forever,
        loop_statement_repeat,
        loop_statement_while,
        loop_statement_for,
        loop_statement_do_while,
        loop_statement_foreach,
    ))(s)
}

pub fn loop_statement_forever(s: &str) -> IResult<&str, LoopStatement> {
    let (s, _) = symbol("forever")(s)?;
    let (s, x) = statement_or_null(s)?;
    Ok((
        s,
        LoopStatement::Forever(LoopStatementForever { statement: x }),
    ))
}

pub fn loop_statement_repeat(s: &str) -> IResult<&str, LoopStatement> {
    let (s, _) = symbol("repeat")(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, x) = expression(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, y) = statement_or_null(s)?;
    Ok((
        s,
        LoopStatement::Repeat(LoopStatementRepeat {
            expression: x,
            statement: y,
        }),
    ))
}

pub fn loop_statement_while(s: &str) -> IResult<&str, LoopStatement> {
    let (s, _) = symbol("while")(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, x) = expression(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, y) = statement_or_null(s)?;
    Ok((
        s,
        LoopStatement::While(LoopStatementWhile {
            expression: x,
            statement: y,
        }),
    ))
}

pub fn loop_statement_for(s: &str) -> IResult<&str, LoopStatement> {
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
            initilization: x,
            expression: y,
            step: z,
            statement: v,
        }),
    ))
}

pub fn loop_statement_do_while(s: &str) -> IResult<&str, LoopStatement> {
    let (s, _) = symbol("do")(s)?;
    let (s, x) = statement_or_null(s)?;
    let (s, _) = symbol("while")(s)?;
    let (s, _) = symbol("(")(s)?;
    let (s, y) = expression(s)?;
    let (s, _) = symbol(")")(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((
        s,
        LoopStatement::DoWhile(LoopStatementDoWhile {
            statement: x,
            expression: y,
        }),
    ))
}

pub fn loop_statement_foreach(s: &str) -> IResult<&str, LoopStatement> {
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
        LoopStatement::Foreach(LoopStatementForeach {
            identifier: x,
            variable: y,
            statement: z,
        }),
    ))
}

pub fn for_initialization(s: &str) -> IResult<&str, ForInitialization> {
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

pub fn for_variable_declaration(s: &str) -> IResult<&str, ForVariableDeclaration> {
    let (s, x) = opt(symbol("var"))(s)?;
    let (s, y) = data_type(s)?;
    let (s, z) = separated_nonempty_list(
        symbol(","),
        pair(variable_identifier, preceded(symbol("="), expression)),
    )(s)?;
    Ok((
        s,
        ForVariableDeclaration {
            var: x.is_some(),
            r#type: y,
            declaration: z,
        },
    ))
}

pub fn for_step(s: &str) -> IResult<&str, Vec<ForStepAssignment>> {
    separated_nonempty_list(symbol(","), for_step_assignment)(s)
}

pub fn for_step_assignment(s: &str) -> IResult<&str, ForStepAssignment> {
    alt((
        map(operator_assignment, |x| ForStepAssignment::Operator(x)),
        map(inc_or_dec_declaration, |x| ForStepAssignment::IncOrDec(x)),
        map(function_subroutine_call, |x| {
            ForStepAssignment::Subroutine(x)
        }),
    ))(s)
}

pub fn loop_variables(s: &str) -> IResult<&str, Vec<Option<Identifier>>> {
    separated_nonempty_list(symbol(","), opt(index_variable_identifier))(s)
}

// -----------------------------------------------------------------------------
