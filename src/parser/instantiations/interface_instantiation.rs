use crate::ast::*;
use crate::parser::*;
use nom::combinator::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct InterfaceInstantiation {
    pub nodes: (
        InterfaceIdentifier,
        Option<ParameterValueAssignment>,
        List<Symbol, HierarchicalInstance>,
        Symbol,
    ),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn interface_instantiation(s: Span) -> IResult<Span, InterfaceInstantiation> {
    let (s, a) = interface_identifier(s)?;
    let (s, b) = opt(parameter_value_assignment)(s)?;
    let (s, c) = list(symbol(","), hierarchical_instance)(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        InterfaceInstantiation {
            nodes: (a, b, c, d),
        },
    ))
}

// -----------------------------------------------------------------------------
