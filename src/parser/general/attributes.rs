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
    fn test() {
        assert_eq!(
            format!(
                "{:?}",
                all_consuming(attribute_instance)(Span::new("(* full_case, parallel_case *)"))
            ),
            "Ok((LocatedSpanEx { offset: 30, line: 1, fragment: \"\", extra: () }, AttributeInstance { nodes: ([AttrSpec { nodes: (SimpleIdentifier(SimpleIdentifier { nodes: (LocatedSpanEx { offset: 3, line: 1, fragment: \"full_case\", extra: () }, []) }), None) }, AttrSpec { nodes: (SimpleIdentifier(SimpleIdentifier { nodes: (LocatedSpanEx { offset: 14, line: 1, fragment: \"parallel_case\", extra: () }, [Space(LocatedSpanEx { offset: 27, line: 1, fragment: \" \", extra: () })]) }), None) }],) }))"
        );
        assert_eq!(
            format!(
                "{:?}",
                all_consuming(attribute_instance)(Span::new("(* full_case=1 *)"))
            ),
            "Ok((LocatedSpanEx { offset: 17, line: 1, fragment: \"\", extra: () }, AttributeInstance { nodes: ([AttrSpec { nodes: (SimpleIdentifier(SimpleIdentifier { nodes: (LocatedSpanEx { offset: 3, line: 1, fragment: \"full_case\", extra: () }, []) }), Some(Nullary(PrimaryLiteral(Number(IntegralNumber(DecimalNumber(UnsignedNumber(UnsignedNumber { nodes: (LocatedSpanEx { offset: 13, line: 1, fragment: \"1\", extra: () }, [Space(LocatedSpanEx { offset: 14, line: 1, fragment: \" \", extra: () })]) })))))))) }],) }))"
        );
        assert_eq!(
            format!(
                "{:?}",
                all_consuming(attribute_instance)(Span::new("(* full_case=1, parallel_case = 0 *)"))
            ),
            "Ok((LocatedSpanEx { offset: 36, line: 1, fragment: \"\", extra: () }, AttributeInstance { nodes: ([AttrSpec { nodes: (SimpleIdentifier(SimpleIdentifier { nodes: (LocatedSpanEx { offset: 3, line: 1, fragment: \"full_case\", extra: () }, []) }), Some(Nullary(PrimaryLiteral(Number(IntegralNumber(DecimalNumber(UnsignedNumber(UnsignedNumber { nodes: (LocatedSpanEx { offset: 13, line: 1, fragment: \"1\", extra: () }, []) })))))))) }, AttrSpec { nodes: (SimpleIdentifier(SimpleIdentifier { nodes: (LocatedSpanEx { offset: 16, line: 1, fragment: \"parallel_case\", extra: () }, [Space(LocatedSpanEx { offset: 29, line: 1, fragment: \" \", extra: () })]) }), Some(Nullary(PrimaryLiteral(Number(IntegralNumber(DecimalNumber(UnsignedNumber(UnsignedNumber { nodes: (LocatedSpanEx { offset: 32, line: 1, fragment: \"0\", extra: () }, [Space(LocatedSpanEx { offset: 33, line: 1, fragment: \" \", extra: () })]) })))))))) }],) }))"
        );
    }
}
