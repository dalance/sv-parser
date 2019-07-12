use crate::ast::*;
use crate::parser::*;
use nom::combinator::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct AttributeInstance<'a> {
    pub nodes: (Symbol<'a>, List<Symbol<'a>, AttrSpec<'a>>, Symbol<'a>),
}

#[derive(Debug)]
pub struct AttrSpec<'a> {
    pub nodes: (Identifier<'a>, Option<(Symbol<'a>, ConstantExpression<'a>)>),
}

// -----------------------------------------------------------------------------

pub fn attribute_instance(s: Span) -> IResult<Span, AttributeInstance> {
    let (s, a) = symbol("(*")(s)?;
    let (s, b) = list(symbol(","), attr_spec)(s)?;
    let (s, c) = symbol("*)")(s)?;
    Ok((s, AttributeInstance { nodes: (a, b, c) }))
}

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
