use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum SubroutineCallStatement<'a> {
    SubroutineCall(SubroutineCall<'a>),
    FunctionSubroutineCall(FunctionSubroutineCall<'a>),
}

// -----------------------------------------------------------------------------

pub fn subroutine_call_statement(s: Span) -> IResult<Span, SubroutineCallStatement> {
    alt((
        map(terminated(subroutine_call, symbol(";")), |x| {
            SubroutineCallStatement::SubroutineCall(x)
        }),
        map(
            delimited(
                triple(symbol("void"), symbol("'"), symbol("(")),
                function_subroutine_call,
                pair(symbol(")"), symbol(";")),
            ),
            |x| SubroutineCallStatement::FunctionSubroutineCall(x),
        ),
    ))(s)
}

// -----------------------------------------------------------------------------
