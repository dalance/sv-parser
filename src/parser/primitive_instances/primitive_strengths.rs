use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum PulldownStrength<'a> {
    Strength01(PulldownStrength01<'a>),
    Strength10(PulldownStrength10<'a>),
    Strength0(PulldownStrength0<'a>),
}

#[derive(Debug, Node)]
pub struct PulldownStrength01<'a> {
    pub nodes: (Paren<'a, (Strength0<'a>, Symbol<'a>, Strength1<'a>)>,),
}

#[derive(Debug, Node)]
pub struct PulldownStrength10<'a> {
    pub nodes: (Paren<'a, (Strength1<'a>, Symbol<'a>, Strength0<'a>)>,),
}

#[derive(Debug, Node)]
pub struct PulldownStrength0<'a> {
    pub nodes: (Paren<'a, Strength0<'a>>,),
}

#[derive(Debug, Node)]
pub enum PullupStrength<'a> {
    Strength01(PullupStrength01<'a>),
    Strength10(PullupStrength10<'a>),
    Strength1(PullupStrength1<'a>),
}

#[derive(Debug, Node)]
pub struct PullupStrength01<'a> {
    pub nodes: (Paren<'a, (Strength0<'a>, Symbol<'a>, Strength1<'a>)>,),
}

#[derive(Debug, Node)]
pub struct PullupStrength10<'a> {
    pub nodes: (Paren<'a, (Strength1<'a>, Symbol<'a>, Strength0<'a>)>,),
}

#[derive(Debug, Node)]
pub struct PullupStrength1<'a> {
    pub nodes: (Paren<'a, Strength1<'a>>,),
}

// -----------------------------------------------------------------------------

#[trace]
pub fn pulldown_strength(s: Span) -> IResult<Span, PulldownStrength> {
    alt((pulldown_strength01, pulldown_strength10, pulldown_strength0))(s)
}

#[trace]
pub fn pulldown_strength01(s: Span) -> IResult<Span, PulldownStrength> {
    let (s, a) = paren(triple(strength0, symbol(","), strength1))(s)?;
    Ok((
        s,
        PulldownStrength::Strength01(PulldownStrength01 { nodes: (a,) }),
    ))
}

#[trace]
pub fn pulldown_strength10(s: Span) -> IResult<Span, PulldownStrength> {
    let (s, a) = paren(triple(strength1, symbol(","), strength0))(s)?;
    Ok((
        s,
        PulldownStrength::Strength10(PulldownStrength10 { nodes: (a,) }),
    ))
}

#[trace]
pub fn pulldown_strength0(s: Span) -> IResult<Span, PulldownStrength> {
    let (s, a) = paren(strength0)(s)?;
    Ok((
        s,
        PulldownStrength::Strength0(PulldownStrength0 { nodes: (a,) }),
    ))
}

#[trace]
pub fn pullup_strength(s: Span) -> IResult<Span, PullupStrength> {
    alt((pullup_strength01, pullup_strength10, pullup_strength1))(s)
}

#[trace]
pub fn pullup_strength01(s: Span) -> IResult<Span, PullupStrength> {
    let (s, a) = paren(triple(strength0, symbol(","), strength1))(s)?;
    Ok((
        s,
        PullupStrength::Strength01(PullupStrength01 { nodes: (a,) }),
    ))
}

#[trace]
pub fn pullup_strength10(s: Span) -> IResult<Span, PullupStrength> {
    let (s, a) = paren(triple(strength1, symbol(","), strength0))(s)?;
    Ok((
        s,
        PullupStrength::Strength10(PullupStrength10 { nodes: (a,) }),
    ))
}

#[trace]
pub fn pullup_strength1(s: Span) -> IResult<Span, PullupStrength> {
    let (s, a) = paren(strength1)(s)?;
    Ok((
        s,
        PullupStrength::Strength1(PullupStrength1 { nodes: (a,) }),
    ))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use nom::combinator::*;

    #[test]
    fn test_pulldown_strength() {
        parser_test!(pulldown_strength, "(supply0, strong1)", Ok((_, _)));
        parser_test!(pulldown_strength, "(pull1, weak0)", Ok((_, _)));
        parser_test!(pulldown_strength, "(pull0)", Ok((_, _)));
    }

    #[test]
    fn test_pullup_strength() {
        parser_test!(pullup_strength, "(supply0, strong1)", Ok((_, _)));
        parser_test!(pullup_strength, "(pull1, weak0)", Ok((_, _)));
        parser_test!(pullup_strength, "(supply1)", Ok((_, _)));
    }
}
