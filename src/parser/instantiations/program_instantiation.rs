use crate::ast::*;
use crate::parser::*;
use nom::combinator::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub struct ProgramInstantiation<'a> {
    pub nodes: (
        ProgramIdentifier<'a>,
        Option<ParameterValueAssignment<'a>>,
        List<Symbol<'a>, HierarchicalInstance<'a>>,
        Symbol<'a>,
    ),
}

// -----------------------------------------------------------------------------

pub fn program_instantiation(s: Span) -> IResult<Span, ProgramInstantiation> {
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

// -----------------------------------------------------------------------------
