use nom::branch::*;
use nom::bytes::complete::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct Operator<'a> {
    pub raw: &'a str,
}

// -----------------------------------------------------------------------------

pub fn unary_operator(s: &str) -> IResult<&str, Operator> {
    let (s, raw) = alt((
        tag("+"),
        tag("-"),
        tag("!"),
        tag("&"),
        tag("|"),
        tag("~&"),
        tag("~|"),
        tag("~^"),
        tag("^~"),
        tag("^"),
        tag("~"),
    ))(s)?;
    Ok((s, Operator { raw }))
}

pub fn binary_operator(s: &str) -> IResult<&str, Operator> {
    let (s, raw) = alt((
        alt((
            tag("+"),
            tag("-"),
            tag("**"),
            tag("*"),
            tag("/"),
            tag("%"),
            tag("==="),
            tag("==?"),
            tag("=="),
            tag("!=="),
            tag("!=?"),
            tag("!="),
            tag("&&"),
            tag("||"),
        )),
        alt((
            tag("&"),
            tag("|"),
            tag("^~"),
            tag("^"),
            tag("~^"),
            tag(">>>"),
            tag(">>"),
            tag("<<<"),
            tag("<<"),
            tag("->"),
            tag("<->"),
            tag("<="),
            tag("<"),
            tag(">="),
            tag(">"),
        )),
    ))(s)?;
    Ok((s, Operator { raw }))
}

pub fn inc_or_dec_operator(s: &str) -> IResult<&str, Operator> {
    let (s, raw) = alt((tag("++"), tag("--")))(s)?;
    Ok((s, Operator { raw }))
}

pub fn unary_module_path_operator(s: &str) -> IResult<&str, Operator> {
    let (s, raw) = alt((
        tag("!"),
        tag("&"),
        tag("|"),
        tag("~&"),
        tag("~|"),
        tag("~^"),
        tag("^~"),
        tag("^"),
        tag("~"),
    ))(s)?;
    Ok((s, Operator { raw }))
}

pub fn binary_module_path_operator(s: &str) -> IResult<&str, Operator> {
    let (s, raw) = alt((
        tag("=="),
        tag("!="),
        tag("&&"),
        tag("||"),
        tag("&"),
        tag("|"),
        tag("^~"),
        tag("^"),
        tag("~^"),
    ))(s)?;
    Ok((s, Operator { raw }))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use nom::combinator::*;

    #[test]
    fn test() {
        assert_eq!(
            format!("{:?}", all_consuming(unary_operator)("~")),
            "Ok((\"\", Operator { raw: \"~\" }))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(binary_operator)(">>>")),
            "Ok((\"\", Operator { raw: \">>>\" }))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(inc_or_dec_operator)("++")),
            "Ok((\"\", Operator { raw: \"++\" }))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(unary_module_path_operator)("^~")),
            "Ok((\"\", Operator { raw: \"^~\" }))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(binary_module_path_operator)("||")),
            "Ok((\"\", Operator { raw: \"||\" }))"
        );
    }
}
