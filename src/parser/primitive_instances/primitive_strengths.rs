use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum PulldownStrength {
    Strength01(Box<PulldownStrength01>),
    Strength10(Box<PulldownStrength10>),
    Strength0(Box<PulldownStrength0>),
}

#[derive(Clone, Debug, Node)]
pub struct PulldownStrength01 {
    pub nodes: (Paren<(Strength0, Symbol, Strength1)>,),
}

#[derive(Clone, Debug, Node)]
pub struct PulldownStrength10 {
    pub nodes: (Paren<(Strength1, Symbol, Strength0)>,),
}

#[derive(Clone, Debug, Node)]
pub struct PulldownStrength0 {
    pub nodes: (Paren<Strength0>,),
}

#[derive(Clone, Debug, Node)]
pub enum PullupStrength {
    Strength01(Box<PullupStrength01>),
    Strength10(Box<PullupStrength10>),
    Strength1(Box<PullupStrength1>),
}

#[derive(Clone, Debug, Node)]
pub struct PullupStrength01 {
    pub nodes: (Paren<(Strength0, Symbol, Strength1)>,),
}

#[derive(Clone, Debug, Node)]
pub struct PullupStrength10 {
    pub nodes: (Paren<(Strength1, Symbol, Strength0)>,),
}

#[derive(Clone, Debug, Node)]
pub struct PullupStrength1 {
    pub nodes: (Paren<Strength1>,),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn pulldown_strength(s: Span) -> IResult<Span, PulldownStrength> {
    alt((pulldown_strength01, pulldown_strength10, pulldown_strength0))(s)
}

#[parser]
pub fn pulldown_strength01(s: Span) -> IResult<Span, PulldownStrength> {
    let (s, a) = paren(triple(strength0, symbol(","), strength1))(s)?;
    Ok((
        s,
        PulldownStrength::Strength01(Box::new(PulldownStrength01 { nodes: (a,) })),
    ))
}

#[parser]
pub fn pulldown_strength10(s: Span) -> IResult<Span, PulldownStrength> {
    let (s, a) = paren(triple(strength1, symbol(","), strength0))(s)?;
    Ok((
        s,
        PulldownStrength::Strength10(Box::new(PulldownStrength10 { nodes: (a,) })),
    ))
}

#[parser]
pub fn pulldown_strength0(s: Span) -> IResult<Span, PulldownStrength> {
    let (s, a) = paren(strength0)(s)?;
    Ok((
        s,
        PulldownStrength::Strength0(Box::new(PulldownStrength0 { nodes: (a,) })),
    ))
}

#[parser]
pub fn pullup_strength(s: Span) -> IResult<Span, PullupStrength> {
    alt((pullup_strength01, pullup_strength10, pullup_strength1))(s)
}

#[parser]
pub fn pullup_strength01(s: Span) -> IResult<Span, PullupStrength> {
    let (s, a) = paren(triple(strength0, symbol(","), strength1))(s)?;
    Ok((
        s,
        PullupStrength::Strength01(Box::new(PullupStrength01 { nodes: (a,) })),
    ))
}

#[parser]
pub fn pullup_strength10(s: Span) -> IResult<Span, PullupStrength> {
    let (s, a) = paren(triple(strength1, symbol(","), strength0))(s)?;
    Ok((
        s,
        PullupStrength::Strength10(Box::new(PullupStrength10 { nodes: (a,) })),
    ))
}

#[parser]
pub fn pullup_strength1(s: Span) -> IResult<Span, PullupStrength> {
    let (s, a) = paren(strength1)(s)?;
    Ok((
        s,
        PullupStrength::Strength1(Box::new(PullupStrength1 { nodes: (a,) })),
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
