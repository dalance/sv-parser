use crate::parser::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct InterfaceInstantiation<'a> {
    pub nodes: (
        InterfaceIdentifier<'a>,
        Option<ParameterValueAssignment<'a>>,
        HierarchicalInstance<'a>,
        Vec<(Symbol<'a>, HierarchicalInstance<'a>)>,
        Symbol<'a>,
    ),
}

// -----------------------------------------------------------------------------

pub fn interface_instantiation(s: Span) -> IResult<Span, InterfaceInstantiation> {
    let (s, a) = interface_identifier(s)?;
    let (s, b) = opt(parameter_value_assignment)(s)?;
    let (s, c) = hierarchical_instance(s)?;
    let (s, d) = many0(pair(symbol(","), hierarchical_instance))(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        InterfaceInstantiation {
            nodes: (a, b, c, d, e),
        },
    ))
}

// -----------------------------------------------------------------------------
