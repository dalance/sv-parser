use crate::parser::*;
use nom::branch::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct Operator<'a> {
    pub nodes: (Symbol<'a>,),
}

// -----------------------------------------------------------------------------

pub fn unary_operator(s: &str) -> IResult<&str, Operator> {
    let (s, a) = alt((
        symbol("+"),
        symbol("-"),
        symbol("!"),
        symbol("&"),
        symbol("|"),
        symbol("~&"),
        symbol("~|"),
        symbol("~^"),
        symbol("^~"),
        symbol("^"),
        symbol("~"),
    ))(s)?;
    Ok((s, Operator { nodes: (a,) }))
}

pub fn binary_operator(s: &str) -> IResult<&str, Operator> {
    let (s, a) = alt((
        alt((
            symbol("+"),
            symbol("-"),
            symbol("**"),
            symbol("*"),
            symbol("/"),
            symbol("%"),
            symbol("==="),
            symbol("==?"),
            symbol("=="),
            symbol("!=="),
            symbol("!=?"),
            symbol("!="),
            symbol("&&"),
            symbol("||"),
        )),
        alt((
            symbol("&"),
            symbol("|"),
            symbol("^~"),
            symbol("^"),
            symbol("~^"),
            symbol(">>>"),
            symbol(">>"),
            symbol("<<<"),
            symbol("<<"),
            symbol("->"),
            symbol("<->"),
            symbol("<="),
            symbol("<"),
            symbol(">="),
            symbol(">"),
        )),
    ))(s)?;
    Ok((s, Operator { nodes: (a,) }))
}

pub fn inc_or_dec_operator(s: &str) -> IResult<&str, Operator> {
    let (s, a) = alt((symbol("++"), symbol("--")))(s)?;
    Ok((s, Operator { nodes: (a,) }))
}

pub fn unary_module_path_operator(s: &str) -> IResult<&str, Operator> {
    let (s, a) = alt((
        symbol("!"),
        symbol("&"),
        symbol("|"),
        symbol("~&"),
        symbol("~|"),
        symbol("~^"),
        symbol("^~"),
        symbol("^"),
        symbol("~"),
    ))(s)?;
    Ok((s, Operator { nodes: (a,) }))
}

pub fn binary_module_path_operator(s: &str) -> IResult<&str, Operator> {
    let (s, a) = alt((
        symbol("=="),
        symbol("!="),
        symbol("&&"),
        symbol("||"),
        symbol("&"),
        symbol("|"),
        symbol("^~"),
        symbol("^"),
        symbol("~^"),
    ))(s)?;
    Ok((s, Operator { nodes: (a,) }))
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
