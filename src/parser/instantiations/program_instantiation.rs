use crate::parser::*;
use nom::combinator::*;
use nom::multi::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct ProgramInstantiation<'a> {
    pub nodes: (
        ProgramIdentifier<'a>,
        Option<ParameterValueAssignment<'a>>,
        Vec<HierarchicalInstance<'a>>,
    ),
}

// -----------------------------------------------------------------------------

pub fn program_instantiation(s: &str) -> IResult<&str, ProgramInstantiation> {
    let (s, x) = program_identifier(s)?;
    let (s, y) = opt(parameter_value_assignment)(s)?;
    let (s, z) = separated_nonempty_list(symbol(","), hierarchical_instance)(s)?;
    let (s, _) = symbol(";")(s)?;
    Ok((s, ProgramInstantiation { nodes: (x, y, z) }))
}

// -----------------------------------------------------------------------------
