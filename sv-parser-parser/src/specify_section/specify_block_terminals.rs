use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn specify_input_terminal_descriptor(
    s: Span,
) -> IResult<Span, SpecifyInputTerminalDescriptor> {
    let (s, a) = input_identifier(s)?;
    let (s, b) = opt(bracket(constant_range_expression))(s)?;
    Ok((s, SpecifyInputTerminalDescriptor { nodes: (a, b) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn specify_output_terminal_descriptor(
    s: Span,
) -> IResult<Span, SpecifyOutputTerminalDescriptor> {
    let (s, a) = output_identifier(s)?;
    let (s, b) = opt(bracket(constant_range_expression))(s)?;
    Ok((s, SpecifyOutputTerminalDescriptor { nodes: (a, b) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn input_identifier(s: Span) -> IResult<Span, InputIdentifier> {
    alt((
        input_identifier_interface,
        map(input_port_identifier, |x| {
            InputIdentifier::InputPortIdentifier(Box::new(x))
        }),
        map(inout_port_identifier, |x| {
            InputIdentifier::InoutPortIdentifier(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn input_identifier_interface(s: Span) -> IResult<Span, InputIdentifier> {
    let (s, a) = interface_identifier(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = port_identifier(s)?;
    Ok((
        s,
        InputIdentifier::Interface(Box::new(InputIdentifierInterface { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn output_identifier(s: Span) -> IResult<Span, OutputIdentifier> {
    alt((
        output_identifier_interface,
        map(output_port_identifier, |x| {
            OutputIdentifier::OutputPortIdentifier(Box::new(x))
        }),
        map(inout_port_identifier, |x| {
            OutputIdentifier::InoutPortIdentifier(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn output_identifier_interface(s: Span) -> IResult<Span, OutputIdentifier> {
    let (s, a) = interface_identifier(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = port_identifier(s)?;
    Ok((
        s,
        OutputIdentifier::Interface(Box::new(OutputIdentifierInterface { nodes: (a, b, c) })),
    ))
}
