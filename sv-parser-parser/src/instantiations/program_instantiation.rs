use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
pub(crate) fn program_instantiation(s: Span) -> IResult<Span, ProgramInstantiation> {
    let (s, a) = program_identifier(s)?;
    let (s, b) = opt(parameter_value_assignment)(s)?;
    let (s, c) = list(symbol(","), hierarchical_instance)(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        ProgramInstantiation {
            nodes: (a, b, c, d),
        },
    ))
}
