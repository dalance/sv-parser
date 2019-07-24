use crate::ast::*;
use crate::parser::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct AttributeInstance {
    pub nodes: (Symbol, List<Symbol, AttrSpec>, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct AttrSpec {
    pub nodes: (Identifier, Option<(Symbol, ConstantExpression)>),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn attribute_instance(s: Span) -> IResult<Span, AttributeInstance> {
    let (s, a) = symbol("(*")(s)?;
    let (s, b) = list(symbol(","), attr_spec)(s)?;
    let (s, c) = symbol("*)")(s)?;
    Ok((s, AttributeInstance { nodes: (a, b, c) }))
}

#[parser]
pub fn attr_spec(s: Span) -> IResult<Span, AttrSpec> {
    let (s, a) = identifier(s)?;
    let (s, b) = opt(pair(symbol("="), constant_expression))(s)?;
    Ok((s, AttrSpec { nodes: (a, b) }))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_attribute_instance() {
        parser_test!(
            attribute_instance,
            "(* full_case, parallel_case *)",
            Ok((_, _))
        );
        parser_test!(attribute_instance, "(* full_case=1 *)", Ok((_, _)));
        parser_test!(
            attribute_instance,
            "(* full_case=1, parallel_case = 0 *)",
            Ok((_, _))
        );
    }
}
