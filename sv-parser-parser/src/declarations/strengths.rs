use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
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

#[tracable_parser]
pub(crate) fn drive_strength01(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(strength0, symbol(","), strength1))(s)?;
    Ok((
        s,
        DriveStrength::Strength01(Box::new(DriveStrength01 { nodes: (a,) })),
    ))
}

#[tracable_parser]
pub(crate) fn drive_strength10(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(strength1, symbol(","), strength0))(s)?;
    Ok((
        s,
        DriveStrength::Strength10(Box::new(DriveStrength10 { nodes: (a,) })),
    ))
}

#[tracable_parser]
pub(crate) fn drive_strength0z(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(strength0, symbol(","), keyword("highz1")))(s)?;
    Ok((
        s,
        DriveStrength::Strength0z(Box::new(DriveStrength0z { nodes: (a,) })),
    ))
}

#[tracable_parser]
pub(crate) fn drive_strength1z(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(strength1, symbol(","), keyword("highz0")))(s)?;
    Ok((
        s,
        DriveStrength::Strength1z(Box::new(DriveStrength1z { nodes: (a,) })),
    ))
}

#[tracable_parser]
pub(crate) fn drive_strengthz1(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(keyword("highz0"), symbol(","), strength1))(s)?;
    Ok((
        s,
        DriveStrength::Strengthz1(Box::new(DriveStrengthz1 { nodes: (a,) })),
    ))
}

#[tracable_parser]
pub(crate) fn drive_strengthz0(s: Span) -> IResult<Span, DriveStrength> {
    let (s, a) = paren(triple(keyword("highz1"), symbol(","), strength0))(s)?;
    Ok((
        s,
        DriveStrength::Strengthz0(Box::new(DriveStrengthz0 { nodes: (a,) })),
    ))
}

#[tracable_parser]
pub(crate) fn strength0(s: Span) -> IResult<Span, Strength0> {
    alt((
        map(keyword("supply0"), |x| Strength0::Supply0(Box::new(x))),
        map(keyword("strong0"), |x| Strength0::Strong0(Box::new(x))),
        map(keyword("pull0"), |x| Strength0::Pull0(Box::new(x))),
        map(keyword("weak0"), |x| Strength0::Weak0(Box::new(x))),
    ))(s)
}

#[tracable_parser]
pub(crate) fn strength1(s: Span) -> IResult<Span, Strength1> {
    alt((
        map(keyword("supply1"), |x| Strength1::Supply1(Box::new(x))),
        map(keyword("strong1"), |x| Strength1::Strong1(Box::new(x))),
        map(keyword("pull1"), |x| Strength1::Pull1(Box::new(x))),
        map(keyword("weak1"), |x| Strength1::Weak1(Box::new(x))),
    ))(s)
}

#[tracable_parser]
pub(crate) fn charge_strength(s: Span) -> IResult<Span, ChargeStrength> {
    alt((
        charge_strength_small,
        charge_strength_medium,
        charge_strength_large,
    ))(s)
}

#[tracable_parser]
pub(crate) fn charge_strength_small(s: Span) -> IResult<Span, ChargeStrength> {
    let (s, a) = paren(keyword("small"))(s)?;
    Ok((
        s,
        ChargeStrength::Small(Box::new(ChargeStrengthSmall { nodes: (a,) })),
    ))
}

#[tracable_parser]
pub(crate) fn charge_strength_medium(s: Span) -> IResult<Span, ChargeStrength> {
    let (s, a) = paren(keyword("medium"))(s)?;
    Ok((
        s,
        ChargeStrength::Medium(Box::new(ChargeStrengthMedium { nodes: (a,) })),
    ))
}

#[tracable_parser]
pub(crate) fn charge_strength_large(s: Span) -> IResult<Span, ChargeStrength> {
    let (s, a) = paren(keyword("large"))(s)?;
    Ok((
        s,
        ChargeStrength::Large(Box::new(ChargeStrengthLarge { nodes: (a,) })),
    ))
}
