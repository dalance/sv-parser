use crate::parser::*;
use nom::combinator::*;
use nom::multi::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct InterfaceInstantiation<'a> {
    pub nodes: (
        InterfaceIdentifier<'a>,
        Option<ParameterValueAssignment<'a>>,
        Vec<HierarchicalInstance<'a>>,
    ),
}

// -----------------------------------------------------------------------------

pub fn interface_instantiation(s: &str) -> IResult<&str, InterfaceInstantiation> {
    let (s, x) = interface_identifier(s)?;
    let (s, y) = opt(parameter_value_assignment)(s)?;
    let (s, z) = separated_nonempty_list(symbol(","), hierarchical_instance)(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, InterfaceInstantiation { nodes: (x, y, z) }))
}

// -----------------------------------------------------------------------------
