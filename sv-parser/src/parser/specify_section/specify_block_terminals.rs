use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct SpecifyInputTerminalDescriptor {
    pub nodes: (InputIdentifier, Option<Bracket<ConstantRangeExpression>>),
}

#[derive(Clone, Debug, Node)]
pub struct SpecifyOutputTerminalDescriptor {
    pub nodes: (OutputIdentifier, Option<Bracket<ConstantRangeExpression>>),
}

#[derive(Clone, Debug, Node)]
pub enum InputIdentifier {
    InputPortIdentifier(Box<InputPortIdentifier>),
    InoutPortIdentifier(Box<InoutPortIdentifier>),
    Interface(Box<InputIdentifierInterface>),
}

#[derive(Clone, Debug, Node)]
pub struct InputIdentifierInterface {
    pub nodes: (InterfaceIdentifier, Symbol, PortIdentifier),
}

#[derive(Clone, Debug, Node)]
pub enum OutputIdentifier {
    OutputPortIdentifier(Box<OutputPortIdentifier>),
    InoutPortIdentifier(Box<InoutPortIdentifier>),
    Interface(Box<OutputIdentifierInterface>),
}

#[derive(Clone, Debug, Node)]
pub struct OutputIdentifierInterface {
    pub nodes: (InterfaceIdentifier, Symbol, PortIdentifier),
}

// -----------------------------------------------------------------------------

#[parser]
pub(crate) fn specify_input_terminal_descriptor(s: Span) -> IResult<Span, SpecifyInputTerminalDescriptor> {
    let (s, a) = input_identifier(s)?;
    let (s, b) = opt(bracket(constant_range_expression))(s)?;
    Ok((s, SpecifyInputTerminalDescriptor { nodes: (a, b) }))
}

#[parser]
pub(crate) fn specify_output_terminal_descriptor(
    s: Span,
) -> IResult<Span, SpecifyOutputTerminalDescriptor> {
    let (s, a) = output_identifier(s)?;
    let (s, b) = opt(bracket(constant_range_expression))(s)?;
    Ok((s, SpecifyOutputTerminalDescriptor { nodes: (a, b) }))
}

#[parser]
pub(crate) fn input_identifier(s: Span) -> IResult<Span, InputIdentifier> {
    alt((
        map(input_port_identifier, |x| {
            InputIdentifier::InputPortIdentifier(Box::new(x))
        }),
        map(inout_port_identifier, |x| {
            InputIdentifier::InoutPortIdentifier(Box::new(x))
        }),
        input_identifier_interface,
    ))(s)
}

#[parser]
pub(crate) fn input_identifier_interface(s: Span) -> IResult<Span, InputIdentifier> {
    let (s, a) = interface_identifier(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = port_identifier(s)?;
    Ok((
        s,
        InputIdentifier::Interface(Box::new(InputIdentifierInterface { nodes: (a, b, c) })),
    ))
}

#[parser]
pub(crate) fn output_identifier(s: Span) -> IResult<Span, OutputIdentifier> {
    alt((
        map(output_port_identifier, |x| {
            OutputIdentifier::OutputPortIdentifier(Box::new(x))
        }),
        map(inout_port_identifier, |x| {
            OutputIdentifier::InoutPortIdentifier(Box::new(x))
        }),
        output_identifier_interface,
    ))(s)
}

#[parser]
pub(crate) fn output_identifier_interface(s: Span) -> IResult<Span, OutputIdentifier> {
    let (s, a) = interface_identifier(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = port_identifier(s)?;
    Ok((
        s,
        OutputIdentifier::Interface(Box::new(OutputIdentifierInterface { nodes: (a, b, c) })),
    ))
}
