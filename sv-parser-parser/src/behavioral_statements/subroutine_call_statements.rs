use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn subroutine_call_statement(s: Span) -> IResult<Span, SubroutineCallStatement> {
    alt((
        map(pair(subroutine_call, symbol(";")), |x| {
            SubroutineCallStatement::SubroutineCall(Box::new(x))
        }),
        subroutine_call_statement_function,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn subroutine_call_statement_function(
    s: Span,
) -> IResult<Span, SubroutineCallStatement> {
    let (s, a) = keyword("void")(s)?;
    let (s, b) = symbol("'")(s)?;
    let (s, c) = paren(function_subroutine_call)(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        SubroutineCallStatement::Function(Box::new(SubroutineCallStatementFunction {
            nodes: (a, b, c, d),
        })),
    ))
}
