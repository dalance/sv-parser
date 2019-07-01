use crate::identifiers::*;
use crate::util::*;
use nom::bytes::complete::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct AttributeInstance<'a> {
    pub attr_spec: Vec<AttrSpec<'a>>,
}

#[derive(Debug)]
pub struct AttrSpec<'a> {
    pub attr_name: Identifier<'a>,
    pub rvalue: Option<ConstantExpression<'a>>,
}

// -----------------------------------------------------------------------------

pub fn attribute_instance(s: &str) -> IResult<&str, AttributeInstance> {
    let (s, _) = tag("(*")(s)?;
    let (s, attr_spec) = separated_nonempty_list(sp(tag(",")), sp(attr_spec))(s)?;
    let (s, _) = sp(tag("*)"))(s)?;
    Ok((s, AttributeInstance { attr_spec }))
}

pub fn attr_spec(s: &str) -> IResult<&str, AttrSpec> {
    let (s, attr_name) = identifier(s)?;
    let (s, rvalue) = opt(preceded(sp(tag("=")), sp(constant_expression)))(s)?;
    Ok((s, AttrSpec { attr_name, rvalue }))
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
                all_consuming(attribute_instance)("(* full_case, parallel_case *)")
            ),
            "Ok((\"\", AttributeInstance { attr_spec: [AttrSpec { attr_name: Identifier { raw: [\"full_case\"] }, rvalue: None }, AttrSpec { attr_name: Identifier { raw: [\"parallel_case\"] }, rvalue: None }] }))"
        );
        // TODO after constant_expression
        //assert_eq!(
        //    format!(
        //        "{:?}",
        //        all_consuming(attribute_instance)("(* full_case=1 *)")
        //    ),
        //    ""
        //);
    }
}
