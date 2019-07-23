use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum DriveStrength {
    Strength01(DriveStrength01),
    Strength10(DriveStrength10),
    Strength0z(DriveStrength0z),
    Strength1z(DriveStrength1z),
    Strengthz0(DriveStrengthz0),
    Strengthz1(DriveStrengthz1),
}

#[derive(Debug, Node)]
pub struct DriveStrength01 {
    pub nodes: (Paren<(Strength0, Symbol, Strength1)>,),
}

#[derive(Debug, Node)]
pub struct DriveStrength10 {
    pub nodes: (Paren<(Strength1, Symbol, Strength0)>,),
}

#[derive(Debug, Node)]
pub struct DriveStrength0z {
    pub nodes: (Paren<(Strength0, Symbol, Keyword)>,),
}

#[derive(Debug, Node)]
pub struct DriveStrength1z {
    pub nodes: (Paren<(Strength1, Symbol, Keyword)>,),
}

#[derive(Debug, Node)]
pub struct DriveStrengthz1 {
    pub nodes: (Paren<(Keyword, Symbol, Strength1)>,),
}

#[derive(Debug, Node)]
pub struct DriveStrengthz0 {
    pub nodes: (Paren<(Keyword, Symbol, Strength0)>,),
}

#[derive(Debug, Node)]
pub enum Strength0 {
    Supply0(Keyword),
    Strong0(Keyword),
    Pull0(Keyword),
    Weak0(Keyword),
}

#[derive(Debug, Node)]
pub enum Strength1 {
    Supply1(Keyword),
    Strong1(Keyword),
    Pull1(Keyword),
    Weak1(Keyword),
}

#[derive(Debug, Node)]
pub enum ChargeStrength {
    Small(ChargeStrengthSmall),
    Medium(ChargeStrengthMedium),
    Large(ChargeStrengthLarge),
}

#[derive(Debug, Node)]
pub struct ChargeStrengthSmall {
    pub nodes: (Paren<Keyword>,),
}

#[derive(Debug, Node)]
pub struct ChargeStrengthMedium {
    pub nodes: (Paren<Keyword>,),
}

#[derive(Debug, Node)]
pub struct ChargeStrengthLarge {
    pub nodes: (Paren<Keyword>,),
}

// -----------------------------------------------------------------------------

#[parser]
pub fn drive_strength(s: Span) -> IResult<Span, DriveStrength> {
    alt((
        drive_strength01,
        drive_strength10,
        drive_strength0z,
        drive_strength1z,
        drive_strengthz1,
        drive_strengthz0,
    ))(s)
}

#[parser]
pub fn drive_strength01(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(strength0, symbol(","), strength1))(s)?;
    Ok((
        s,
        DriveStrength::Strength01(DriveStrength01 { nodes: (a,) }),
    ))
}

#[parser]
pub fn drive_strength10(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(strength1, symbol(","), strength0))(s)?;
    Ok((
        s,
        DriveStrength::Strength10(DriveStrength10 { nodes: (a,) }),
    ))
}

#[parser]
pub fn drive_strength0z(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(strength0, symbol(","), keyword("highz1")))(s)?;
    Ok((
        s,
        DriveStrength::Strength0z(DriveStrength0z { nodes: (a,) }),
    ))
}

#[parser]
pub fn drive_strength1z(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(strength1, symbol(","), keyword("highz0")))(s)?;
    Ok((
        s,
        DriveStrength::Strength1z(DriveStrength1z { nodes: (a,) }),
    ))
}

#[parser]
pub fn drive_strengthz1(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(keyword("highz0"), symbol(","), strength1))(s)?;
    Ok((
        s,
        DriveStrength::Strengthz1(DriveStrengthz1 { nodes: (a,) }),
    ))
}

#[parser]
pub fn drive_strengthz0(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(keyword("highz1"), symbol(","), strength0))(s)?;
    Ok((
        s,
        DriveStrength::Strengthz0(DriveStrengthz0 { nodes: (a,) }),
    ))
}

#[parser]
pub fn strength0(s: Span) -> IResult<Span, Strength0> {
    alt((
        map(keyword("supply0"), |x| Strength0::Supply0(x)),
        map(keyword("strong0"), |x| Strength0::Strong0(x)),
        map(keyword("pull0"), |x| Strength0::Pull0(x)),
        map(keyword("weak0"), |x| Strength0::Weak0(x)),
    ))(s)
}

#[parser]
pub fn strength1(s: Span) -> IResult<Span, Strength1> {
    alt((
        map(keyword("supply1"), |x| Strength1::Supply1(x)),
        map(keyword("strong1"), |x| Strength1::Strong1(x)),
        map(keyword("pull1"), |x| Strength1::Pull1(x)),
        map(keyword("weak1"), |x| Strength1::Weak1(x)),
    ))(s)
}

#[parser]
pub fn charge_strength(s: Span) -> IResult<Span, ChargeStrength> {
    alt((
        charge_strength_small,
        charge_strength_medium,
        charge_strength_large,
    ))(s)
}

#[parser]
pub fn charge_strength_small(s: Span) -> IResult<Span, ChargeStrength> {
    let (s, a) = paren(keyword("small"))(s)?;
    Ok((
        s,
        ChargeStrength::Small(ChargeStrengthSmall { nodes: (a,) }),
    ))
}

#[parser]
pub fn charge_strength_medium(s: Span) -> IResult<Span, ChargeStrength> {
    let (s, a) = paren(keyword("medium"))(s)?;
    Ok((
        s,
        ChargeStrength::Medium(ChargeStrengthMedium { nodes: (a,) }),
    ))
}

#[parser]
pub fn charge_strength_large(s: Span) -> IResult<Span, ChargeStrength> {
    let (s, a) = paren(keyword("large"))(s)?;
    Ok((
        s,
        ChargeStrength::Large(ChargeStrengthLarge { nodes: (a,) }),
    ))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_drive_strength() {
        parser_test!(drive_strength, "(supply0, strong1)", Ok((_, _)));
        parser_test!(drive_strength, "(pull1, weak0)", Ok((_, _)));
        parser_test!(drive_strength, "(pull0, highz1)", Ok((_, _)));
        parser_test!(drive_strength, "(weak1, highz0)", Ok((_, _)));
        parser_test!(drive_strength, "(highz0, supply1)", Ok((_, _)));
        parser_test!(drive_strength, "(highz1, strong0)", Ok((_, _)));
    }

    #[test]
    fn test_charge_strength() {
        parser_test!(charge_strength, "( small)", Ok((_, _)));
        parser_test!(charge_strength, "( medium  )", Ok((_, _)));
        parser_test!(charge_strength, "(large)", Ok((_, _)));
    }
}
