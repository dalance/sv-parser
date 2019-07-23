use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct SpecifyInputTerminalDescriptor {
    pub nodes: (InputIdentifier, Option<Bracket<ConstantRangeExpression>>),
}

#[derive(Debug, Node)]
pub struct SpecifyOutputTerminalDescriptor {
    pub nodes: (OutputIdentifier, Option<Bracket<ConstantRangeExpression>>),
}

#[derive(Debug, Node)]
pub enum InputIdentifier {
    InputPortIdentifier(InputPortIdentifier),
    InoutPortIdentifier(InoutPortIdentifier),
    Interface(InputIdentifierInterface),
}

#[derive(Debug, Node)]
pub struct InputIdentifierInterface {
    pub nodes: (InterfaceIdentifier, Symbol, PortIdentifier),
}

#[derive(Debug, Node)]
pub enum OutputIdentifier {
    OutputPortIdentifier(OutputPortIdentifier),
    InoutPortIdentifier(InoutPortIdentifier),
    Interface(OutputIdentifierInterface),
}

#[derive(Debug, Node)]
pub struct OutputIdentifierInterface {
    pub nodes: (InterfaceIdentifier, Symbol, PortIdentifier),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn specify_input_terminal_descriptor(s: Span) -> IResult<Span, SpecifyInputTerminalDescriptor> {
    let (s, a) = input_identifier(s)?;
    let (s, b) = opt(bracket(constant_range_expression))(s)?;
    Ok((s, SpecifyInputTerminalDescriptor { nodes: (a, b) }))
}

#[parser]
pub fn specify_output_terminal_descriptor(
    s: Span,
) -> IResult<Span, SpecifyOutputTerminalDescriptor> {
    let (s, a) = output_identifier(s)?;
    let (s, b) = opt(bracket(constant_range_expression))(s)?;
    Ok((s, SpecifyOutputTerminalDescriptor { nodes: (a, b) }))
}

#[parser]
pub fn input_identifier(s: Span) -> IResult<Span, InputIdentifier> {
    alt((
        map(input_port_identifier, |x| {
            InputIdentifier::InputPortIdentifier(x)
        }),
        map(inout_port_identifier, |x| {
            InputIdentifier::InoutPortIdentifier(x)
        }),
        input_identifier_interface,
    ))(s)
}

#[parser]
pub fn input_identifier_interface(s: Span) -> IResult<Span, InputIdentifier> {
    let (s, a) = interface_identifier(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = port_identifier(s)?;
    Ok((
        s,
        InputIdentifier::Interface(InputIdentifierInterface { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn output_identifier(s: Span) -> IResult<Span, OutputIdentifier> {
    alt((
        map(output_port_identifier, |x| {
            OutputIdentifier::OutputPortIdentifier(x)
        }),
        map(inout_port_identifier, |x| {
            OutputIdentifier::InoutPortIdentifier(x)
        }),
        output_identifier_interface,
    ))(s)
}

#[parser]
pub fn output_identifier_interface(s: Span) -> IResult<Span, OutputIdentifier> {
    let (s, a) = interface_identifier(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = port_identifier(s)?;
    Ok((
        s,
        OutputIdentifier::Interface(OutputIdentifierInterface { nodes: (a, b, c) }),
    ))
}
