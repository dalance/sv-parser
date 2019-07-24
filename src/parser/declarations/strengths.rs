use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum DriveStrength {
    Strength01(Box<DriveStrength01>),
    Strength10(Box<DriveStrength10>),
    Strength0z(Box<DriveStrength0z>),
    Strength1z(Box<DriveStrength1z>),
    Strengthz0(Box<DriveStrengthz0>),
    Strengthz1(Box<DriveStrengthz1>),
}

#[derive(Clone, Debug, Node)]
pub struct DriveStrength01 {
    pub nodes: (Paren<(Strength0, Symbol, Strength1)>,),
}

#[derive(Clone, Debug, Node)]
pub struct DriveStrength10 {
    pub nodes: (Paren<(Strength1, Symbol, Strength0)>,),
}

#[derive(Clone, Debug, Node)]
pub struct DriveStrength0z {
    pub nodes: (Paren<(Strength0, Symbol, Keyword)>,),
}

#[derive(Clone, Debug, Node)]
pub struct DriveStrength1z {
    pub nodes: (Paren<(Strength1, Symbol, Keyword)>,),
}

#[derive(Clone, Debug, Node)]
pub struct DriveStrengthz1 {
    pub nodes: (Paren<(Keyword, Symbol, Strength1)>,),
}

#[derive(Clone, Debug, Node)]
pub struct DriveStrengthz0 {
    pub nodes: (Paren<(Keyword, Symbol, Strength0)>,),
}

#[derive(Clone, Debug, Node)]
pub enum Strength0 {
    Supply0(Box<Keyword>),
    Strong0(Box<Keyword>),
    Pull0(Box<Keyword>),
    Weak0(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub enum Strength1 {
    Supply1(Box<Keyword>),
    Strong1(Box<Keyword>),
    Pull1(Box<Keyword>),
    Weak1(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub enum ChargeStrength {
    Small(Box<ChargeStrengthSmall>),
    Medium(Box<ChargeStrengthMedium>),
    Large(Box<ChargeStrengthLarge>),
}

#[derive(Clone, Debug, Node)]
pub struct ChargeStrengthSmall {
    pub nodes: (Paren<Keyword>,),
}

#[derive(Clone, Debug, Node)]
pub struct ChargeStrengthMedium {
    pub nodes: (Paren<Keyword>,),
}

#[derive(Clone, Debug, Node)]
pub struct ChargeStrengthLarge {
    pub nodes: (Paren<Keyword>,),
}

// -----------------------------------------------------------------------------

#[parser]
pub(crate) fn drive_strength(s: Span) -> IResult<Span, DriveStrength> {
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
pub(crate) fn drive_strength01(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(strength0, symbol(","), strength1))(s)?;
    Ok((
        s,
        DriveStrength::Strength01(Box::new(DriveStrength01 { nodes: (a,) })),
    ))
}

#[parser]
pub(crate) fn drive_strength10(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(strength1, symbol(","), strength0))(s)?;
    Ok((
        s,
        DriveStrength::Strength10(Box::new(DriveStrength10 { nodes: (a,) })),
    ))
}

#[parser]
pub(crate) fn drive_strength0z(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(strength0, symbol(","), keyword("highz1")))(s)?;
    Ok((
        s,
        DriveStrength::Strength0z(Box::new(DriveStrength0z { nodes: (a,) })),
    ))
}

#[parser]
pub(crate) fn drive_strength1z(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(strength1, symbol(","), keyword("highz0")))(s)?;
    Ok((
        s,
        DriveStrength::Strength1z(Box::new(DriveStrength1z { nodes: (a,) })),
    ))
}

#[parser]
pub(crate) fn drive_strengthz1(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(keyword("highz0"), symbol(","), strength1))(s)?;
    Ok((
        s,
        DriveStrength::Strengthz1(Box::new(DriveStrengthz1 { nodes: (a,) })),
    ))
}

#[parser]
pub(crate) fn drive_strengthz0(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(keyword("highz1"), symbol(","), strength0))(s)?;
    Ok((
        s,
        DriveStrength::Strengthz0(Box::new(DriveStrengthz0 { nodes: (a,) })),
    ))
}

#[parser]
pub(crate) fn strength0(s: Span) -> IResult<Span, Strength0> {
    alt((
        map(keyword("supply0"), |x| Strength0::Supply0(Box::new(x))),
        map(keyword("strong0"), |x| Strength0::Strong0(Box::new(x))),
        map(keyword("pull0"), |x| Strength0::Pull0(Box::new(x))),
        map(keyword("weak0"), |x| Strength0::Weak0(Box::new(x))),
    ))(s)
}

#[parser]
pub(crate) fn strength1(s: Span) -> IResult<Span, Strength1> {
    alt((
        map(keyword("supply1"), |x| Strength1::Supply1(Box::new(x))),
        map(keyword("strong1"), |x| Strength1::Strong1(Box::new(x))),
        map(keyword("pull1"), |x| Strength1::Pull1(Box::new(x))),
        map(keyword("weak1"), |x| Strength1::Weak1(Box::new(x))),
    ))(s)
}

#[parser]
pub(crate) fn charge_strength(s: Span) -> IResult<Span, ChargeStrength> {
    alt((
        charge_strength_small,
        charge_strength_medium,
        charge_strength_large,
    ))(s)
}

#[parser]
pub(crate) fn charge_strength_small(s: Span) -> IResult<Span, ChargeStrength> {
    let (s, a) = paren(keyword("small"))(s)?;
    Ok((
        s,
        ChargeStrength::Small(Box::new(ChargeStrengthSmall { nodes: (a,) })),
    ))
}

#[parser]
pub(crate) fn charge_strength_medium(s: Span) -> IResult<Span, ChargeStrength> {
    let (s, a) = paren(keyword("medium"))(s)?;
    Ok((
        s,
        ChargeStrength::Medium(Box::new(ChargeStrengthMedium { nodes: (a,) })),
    ))
}

#[parser]
pub(crate) fn charge_strength_large(s: Span) -> IResult<Span, ChargeStrength> {
    let (s, a) = paren(keyword("large"))(s)?;
    Ok((
        s,
        ChargeStrength::Large(Box::new(ChargeStrengthLarge { nodes: (a,) })),
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
