use crate::parser::*;
use nom::branch::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct UnaryOperator<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug)]
pub struct BinaryOperator<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug)]
pub struct IncOrDecOperator<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug)]
pub struct UnaryModulePathOperator<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug)]
pub struct BinaryModulePathOperator<'a> {
    pub nodes: (Symbol<'a>,),
}

// -----------------------------------------------------------------------------

pub fn unary_operator(s: Span) -> IResult<Span, UnaryOperator> {
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
    Ok((s, UnaryOperator { nodes: (a,) }))
}

pub fn binary_operator(s: Span) -> IResult<Span, BinaryOperator> {
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
    Ok((s, BinaryOperator { nodes: (a,) }))
}

pub fn inc_or_dec_operator(s: Span) -> IResult<Span, IncOrDecOperator> {
    let (s, a) = alt((symbol("++"), symbol("--")))(s)?;
    Ok((s, IncOrDecOperator { nodes: (a,) }))
}

pub fn unary_module_path_operator(s: Span) -> IResult<Span, UnaryModulePathOperator> {
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
    Ok((s, UnaryModulePathOperator { nodes: (a,) }))
}

pub fn binary_module_path_operator(s: Span) -> IResult<Span, BinaryModulePathOperator> {
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
    Ok((s, BinaryModulePathOperator { nodes: (a,) }))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use nom::combinator::*;

    #[test]
    fn test() {
        assert_eq!(
            format!("{:?}", all_consuming(unary_operator)(Span::new("~"))),
            "Ok((LocatedSpanEx { offset: 1, line: 1, fragment: \"\", extra: () }, UnaryOperator { nodes: (Symbol { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"~\", extra: () }, []) },) }))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(binary_operator)(Span::new(">>>"))),
            "Ok((LocatedSpanEx { offset: 3, line: 1, fragment: \"\", extra: () }, BinaryOperator { nodes: (Symbol { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \">>>\", extra: () }, []) },) }))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(inc_or_dec_operator)(Span::new("++"))),
            "Ok((LocatedSpanEx { offset: 2, line: 1, fragment: \"\", extra: () }, IncOrDecOperator { nodes: (Symbol { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"++\", extra: () }, []) },) }))"
        );
        assert_eq!(
            format!(
                "{:?}",
                all_consuming(unary_module_path_operator)(Span::new("^~"))
            ),
            "Ok((LocatedSpanEx { offset: 2, line: 1, fragment: \"\", extra: () }, UnaryModulePathOperator { nodes: (Symbol { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"^~\", extra: () }, []) },) }))"
        );
        assert_eq!(
            format!(
                "{:?}",
                all_consuming(binary_module_path_operator)(Span::new("||"))
            ),
            "Ok((LocatedSpanEx { offset: 2, line: 1, fragment: \"\", extra: () }, BinaryModulePathOperator { nodes: (Symbol { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"||\", extra: () }, []) },) }))"
        );
    }
}
