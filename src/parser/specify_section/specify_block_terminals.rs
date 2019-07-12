use crate::ast::*;
use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct SpecifyInputTerminalDescriptor<'a> {
    pub nodes: (InputIdentifier<'a>, Option<ConstantRangeExpression<'a>>),
}

#[derive(Debug)]
pub struct SpecifyOutputTerminalDescriptor<'a> {
    pub nodes: (OutputIdentifier<'a>, Option<ConstantRangeExpression<'a>>),
}

#[derive(Debug, Node)]
pub enum InputIdentifier<'a> {
    InputPortIdentifier(InputPortIdentifier<'a>),
    InoutPortIdentifier(InoutPortIdentifier<'a>),
    Interface(InputIdentifierInterface<'a>),
}

#[derive(Debug, Node)]
pub struct InputIdentifierInterface<'a> {
    pub nodes: (InterfaceIdentifier<'a>, PortIdentifier<'a>),
}

#[derive(Debug, Node)]
pub enum OutputIdentifier<'a> {
    OutputPortIdentifier(OutputPortIdentifier<'a>),
    InoutPortIdentifier(InoutPortIdentifier<'a>),
    Interface(OutputIdentifierInterface<'a>),
}

#[derive(Debug, Node)]
pub struct OutputIdentifierInterface<'a> {
    pub nodes: (InterfaceIdentifier<'a>, PortIdentifier<'a>),
}

// -----------------------------------------------------------------------------

pub fn specify_input_terminal_descriptor(s: Span) -> IResult<Span, SpecifyInputTerminalDescriptor> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn specify_output_terminal_descriptor(
    s: Span,
) -> IResult<Span, SpecifyOutputTerminalDescriptor> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn input_identifier(s: Span) -> IResult<Span, InputIdentifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn output_identifier(s: Span) -> IResult<Span, OutputIdentifier> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}
