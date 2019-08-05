use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn udp_instantiation(s: Span) -> IResult<Span, UdpInstantiation> {
    let (s, a) = udp_identifier(s)?;
    let (s, b) = opt(drive_strength)(s)?;
    let (s, c) = opt(delay2)(s)?;
    let (s, d) = list(symbol(","), udp_instance)(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        UdpInstantiation {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn udp_instance(s: Span) -> IResult<Span, UdpInstance> {
    let (s, a) = opt(name_of_instance)(s)?;
    let (s, b) = paren(tuple((
        output_terminal,
        symbol(","),
        input_terminal,
        many0(pair(symbol(","), input_terminal)),
    )))(s)?;
    Ok((s, UdpInstance { nodes: (a, b) }))
}
