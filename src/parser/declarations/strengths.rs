use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum DriveStrength<'a> {
    Strength01(DriveStrength01<'a>),
    Strength10(DriveStrength10<'a>),
    Strength0z(DriveStrength0z<'a>),
    Strength1z(DriveStrength1z<'a>),
    Strengthz0(DriveStrengthz0<'a>),
    Strengthz1(DriveStrengthz1<'a>),
}

#[derive(Debug, Node)]
pub struct DriveStrength01<'a> {
    pub nodes: (Paren<'a, (Strength0<'a>, Symbol<'a>, Strength1<'a>)>,),
}

#[derive(Debug, Node)]
pub struct DriveStrength10<'a> {
    pub nodes: (Paren<'a, (Strength1<'a>, Symbol<'a>, Strength0<'a>)>,),
}

#[derive(Debug, Node)]
pub struct DriveStrength0z<'a> {
    pub nodes: (Paren<'a, (Strength0<'a>, Symbol<'a>, Symbol<'a>)>,),
}

#[derive(Debug, Node)]
pub struct DriveStrength1z<'a> {
    pub nodes: (Paren<'a, (Strength1<'a>, Symbol<'a>, Symbol<'a>)>,),
}

#[derive(Debug, Node)]
pub struct DriveStrengthz1<'a> {
    pub nodes: (Paren<'a, (Symbol<'a>, Symbol<'a>, Strength1<'a>)>,),
}

#[derive(Debug, Node)]
pub struct DriveStrengthz0<'a> {
    pub nodes: (Paren<'a, (Symbol<'a>, Symbol<'a>, Strength0<'a>)>,),
}

#[derive(Debug, Node)]
pub enum Strength0<'a> {
    Supply0(Symbol<'a>),
    Strong0(Symbol<'a>),
    Pull0(Symbol<'a>),
    Weak0(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum Strength1<'a> {
    Supply1(Symbol<'a>),
    Strong1(Symbol<'a>),
    Pull1(Symbol<'a>),
    Weak1(Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum ChargeStrength<'a> {
    Small(ChargeStrengthSmall<'a>),
    Medium(ChargeStrengthMedium<'a>),
    Large(ChargeStrengthLarge<'a>),
}

#[derive(Debug, Node)]
pub struct ChargeStrengthSmall<'a> {
    pub nodes: (Paren<'a, Symbol<'a>>,),
}

#[derive(Debug, Node)]
pub struct ChargeStrengthMedium<'a> {
    pub nodes: (Paren<'a, Symbol<'a>>,),
}

#[derive(Debug, Node)]
pub struct ChargeStrengthLarge<'a> {
    pub nodes: (Paren<'a, Symbol<'a>>,),
}

// -----------------------------------------------------------------------------

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

pub fn drive_strength01(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(strength0, symbol(","), strength1))(s)?;
    Ok((
        s,
        DriveStrength::Strength01(DriveStrength01 { nodes: (a,) }),
    ))
}

pub fn drive_strength10(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(strength1, symbol(","), strength0))(s)?;
    Ok((
        s,
        DriveStrength::Strength10(DriveStrength10 { nodes: (a,) }),
    ))
}

pub fn drive_strength0z(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(strength0, symbol(","), symbol("highz1")))(s)?;
    Ok((
        s,
        DriveStrength::Strength0z(DriveStrength0z { nodes: (a,) }),
    ))
}

pub fn drive_strength1z(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(strength1, symbol(","), symbol("highz0")))(s)?;
    Ok((
        s,
        DriveStrength::Strength1z(DriveStrength1z { nodes: (a,) }),
    ))
}

pub fn drive_strengthz1(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(symbol("highz0"), symbol(","), strength1))(s)?;
    Ok((
        s,
        DriveStrength::Strengthz1(DriveStrengthz1 { nodes: (a,) }),
    ))
}

pub fn drive_strengthz0(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(symbol("highz1"), symbol(","), strength0))(s)?;
    Ok((
        s,
        DriveStrength::Strengthz0(DriveStrengthz0 { nodes: (a,) }),
    ))
}

pub fn strength0(s: Span) -> IResult<Span, Strength0> {
    alt((
        map(symbol("supply0"), |x| Strength0::Supply0(x)),
        map(symbol("strong0"), |x| Strength0::Strong0(x)),
        map(symbol("pull0"), |x| Strength0::Pull0(x)),
        map(symbol("weak0"), |x| Strength0::Weak0(x)),
    ))(s)
}

pub fn strength1(s: Span) -> IResult<Span, Strength1> {
    alt((
        map(symbol("supply1"), |x| Strength1::Supply1(x)),
        map(symbol("strong1"), |x| Strength1::Strong1(x)),
        map(symbol("pull1"), |x| Strength1::Pull1(x)),
        map(symbol("weak1"), |x| Strength1::Weak1(x)),
    ))(s)
}

pub fn charge_strength(s: Span) -> IResult<Span, ChargeStrength> {
    alt((
        charge_strength_small,
        charge_strength_medium,
        charge_strength_large,
    ))(s)
}

pub fn charge_strength_small(s: Span) -> IResult<Span, ChargeStrength> {
    let (s, a) = paren(symbol("small"))(s)?;
    Ok((
        s,
        ChargeStrength::Small(ChargeStrengthSmall { nodes: (a,) }),
    ))
}

pub fn charge_strength_medium(s: Span) -> IResult<Span, ChargeStrength> {
    let (s, a) = paren(symbol("medium"))(s)?;
    Ok((
        s,
        ChargeStrength::Medium(ChargeStrengthMedium { nodes: (a,) }),
    ))
}

pub fn charge_strength_large(s: Span) -> IResult<Span, ChargeStrength> {
    let (s, a) = paren(symbol("large"))(s)?;
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
