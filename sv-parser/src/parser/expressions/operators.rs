use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::IResult;
use nom_packrat::packrat_parser;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct UnaryOperator {
    pub nodes: (Symbol,),
}

#[derive(Clone, Debug, Node)]
pub struct BinaryOperator {
    pub nodes: (Symbol,),
}

#[derive(Clone, Debug, Node)]
pub struct IncOrDecOperator {
    pub nodes: (Symbol,),
}

#[derive(Clone, Debug, Node)]
pub struct UnaryModulePathOperator {
    pub nodes: (Symbol,),
}

#[derive(Clone, Debug, Node)]
pub struct BinaryModulePathOperator {
    pub nodes: (Symbol,),
}

// -----------------------------------------------------------------------------

#[packrat_parser]
#[parser]
pub(crate) fn unary_operator(s: Span) -> IResult<Span, UnaryOperator> {
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

#[parser]
pub(crate) fn binary_operator(s: Span) -> IResult<Span, BinaryOperator> {
    let (s, a) = alt((
        alt((
            symbol("+"),
            symbol("->"),
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
            symbol("<->"),
            symbol("<="),
            symbol("<"),
            symbol(">="),
            symbol(">"),
        )),
    ))(s)?;
    Ok((s, BinaryOperator { nodes: (a,) }))
}

#[parser]
pub(crate) fn inc_or_dec_operator(s: Span) -> IResult<Span, IncOrDecOperator> {
    let (s, a) = alt((symbol("++"), symbol("--")))(s)?;
    Ok((s, IncOrDecOperator { nodes: (a,) }))
}

#[parser]
pub(crate) fn unary_module_path_operator(s: Span) -> IResult<Span, UnaryModulePathOperator> {
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

#[parser]
pub(crate) fn binary_module_path_operator(s: Span) -> IResult<Span, BinaryModulePathOperator> {
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
    fn test_unary_operator() {
        parser_test!(unary_operator, "+", Ok((_, _)));
        parser_test!(unary_operator, "-", Ok((_, _)));
        parser_test!(unary_operator, "!", Ok((_, _)));
        parser_test!(unary_operator, "&", Ok((_, _)));
        parser_test!(unary_operator, "|", Ok((_, _)));
        parser_test!(unary_operator, "~&", Ok((_, _)));
        parser_test!(unary_operator, "~|", Ok((_, _)));
        parser_test!(unary_operator, "~^", Ok((_, _)));
        parser_test!(unary_operator, "^~", Ok((_, _)));
        parser_test!(unary_operator, "^", Ok((_, _)));
        parser_test!(unary_operator, "~", Ok((_, _)));
    }

    #[test]
    fn test_binary_operator() {
        parser_test!(binary_operator, "+", Ok((_, _)));
        parser_test!(binary_operator, "-", Ok((_, _)));
        parser_test!(binary_operator, "**", Ok((_, _)));
        parser_test!(binary_operator, "*", Ok((_, _)));
        parser_test!(binary_operator, "/", Ok((_, _)));
        parser_test!(binary_operator, "%", Ok((_, _)));
        parser_test!(binary_operator, "===", Ok((_, _)));
        parser_test!(binary_operator, "==?", Ok((_, _)));
        parser_test!(binary_operator, "==", Ok((_, _)));
        parser_test!(binary_operator, "!==", Ok((_, _)));
        parser_test!(binary_operator, "!=?", Ok((_, _)));
        parser_test!(binary_operator, "!=", Ok((_, _)));
        parser_test!(binary_operator, "&&", Ok((_, _)));
        parser_test!(binary_operator, "||", Ok((_, _)));
        parser_test!(binary_operator, "&", Ok((_, _)));
        parser_test!(binary_operator, "|", Ok((_, _)));
        parser_test!(binary_operator, "^~", Ok((_, _)));
        parser_test!(binary_operator, "^", Ok((_, _)));
        parser_test!(binary_operator, "~^", Ok((_, _)));
        parser_test!(binary_operator, ">>>", Ok((_, _)));
        parser_test!(binary_operator, ">>", Ok((_, _)));
        parser_test!(binary_operator, "<<<", Ok((_, _)));
        parser_test!(binary_operator, "<<", Ok((_, _)));
        parser_test!(binary_operator, "->", Ok((_, _)));
        parser_test!(binary_operator, "<->", Ok((_, _)));
        parser_test!(binary_operator, "<=", Ok((_, _)));
        parser_test!(binary_operator, "<", Ok((_, _)));
        parser_test!(binary_operator, ">=", Ok((_, _)));
        parser_test!(binary_operator, ">", Ok((_, _)));
    }

    #[test]
    fn test_inc_or_dec_operator() {
        parser_test!(inc_or_dec_operator, "++", Ok((_, _)));
        parser_test!(inc_or_dec_operator, "--", Ok((_, _)));
    }

    #[test]
    fn test_unary_module_path_operator() {
        parser_test!(unary_module_path_operator, "!", Ok((_, _)));
        parser_test!(unary_module_path_operator, "&", Ok((_, _)));
        parser_test!(unary_module_path_operator, "|", Ok((_, _)));
        parser_test!(unary_module_path_operator, "~&", Ok((_, _)));
        parser_test!(unary_module_path_operator, "~|", Ok((_, _)));
        parser_test!(unary_module_path_operator, "~^", Ok((_, _)));
        parser_test!(unary_module_path_operator, "^~", Ok((_, _)));
        parser_test!(unary_module_path_operator, "^", Ok((_, _)));
        parser_test!(unary_module_path_operator, "~", Ok((_, _)));
    }

    #[test]
    fn test_binary_module_path_operator() {
        parser_test!(binary_module_path_operator, "==", Ok((_, _)));
        parser_test!(binary_module_path_operator, "!=", Ok((_, _)));
        parser_test!(binary_module_path_operator, "&&", Ok((_, _)));
        parser_test!(binary_module_path_operator, "||", Ok((_, _)));
        parser_test!(binary_module_path_operator, "&", Ok((_, _)));
        parser_test!(binary_module_path_operator, "|", Ok((_, _)));
        parser_test!(binary_module_path_operator, "^~", Ok((_, _)));
        parser_test!(binary_module_path_operator, "^", Ok((_, _)));
        parser_test!(binary_module_path_operator, "~^", Ok((_, _)));
    }
}
