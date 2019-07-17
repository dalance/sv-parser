use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum SubroutineCallStatement<'a> {
    SubroutineCall((SubroutineCall<'a>, Symbol<'a>)),
    Function(SubroutineCallStatementFunction<'a>),
}

#[derive(Debug, Node)]
pub struct SubroutineCallStatementFunction<'a> {
    pub nodes: (
        Symbol<'a>,
        Symbol<'a>,
        Paren<'a, FunctionSubroutineCall<'a>>,
        Symbol<'a>,
    ),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn subroutine_call_statement(s: Span) -> IResult<Span, SubroutineCallStatement> {
    alt((
        map(pair(subroutine_call, symbol(";")), |x| {
            SubroutineCallStatement::SubroutineCall(x)
        }),
        subroutine_call_statement_function,
    ))(s)
}

#[parser]
pub fn subroutine_call_statement_function(s: Span) -> IResult<Span, SubroutineCallStatement> {
    let (s, a) = symbol("void")(s)?;
    let (s, b) = symbol("'")(s)?;
    let (s, c) = paren(function_subroutine_call)(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        SubroutineCallStatement::Function(SubroutineCallStatementFunction {
            nodes: (a, b, c, d),
        }),
    ))
}

// -----------------------------------------------------------------------------
