use crate::parser::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct AttributeInstance<'a> {
    pub nodes: (Vec<AttrSpec<'a>>,),
}

#[derive(Debug)]
pub struct AttrSpec<'a> {
    pub nodes: (Identifier<'a>, Option<ConstantExpression<'a>>),
}

// -----------------------------------------------------------------------------

pub fn attribute_instance(s: Span) -> IResult<Span, AttributeInstance> {
    let (s, _) = symbol("(*")(s)?;
    let (s, x) = separated_nonempty_list(symbol(","), attr_spec)(s)?;
    let (s, _) = symbol("*)")(s)?;
    Ok((s, AttributeInstance { nodes: (x,) }))
}

pub fn attr_spec(s: Span) -> IResult<Span, AttrSpec> {
    let (s, x) = identifier(s)?;
    let (s, y) = opt(preceded(symbol("="), constant_expression))(s)?;
    Ok((s, AttrSpec { nodes: (x, y) }))
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
