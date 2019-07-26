use crate::*;

// -----------------------------------------------------------------------------

#[parser]
pub(crate) fn pulldown_strength(s: Span) -> IResult<Span, PulldownStrength> {
    alt((pulldown_strength01, pulldown_strength10, pulldown_strength0))(s)
}

#[parser]
pub(crate) fn pulldown_strength01(s: Span) -> IResult<Span, PulldownStrength> {
    let (s, a) = paren(triple(strength0, symbol(","), strength1))(s)?;
    Ok((
        s,
        PulldownStrength::Strength01(Box::new(PulldownStrength01 { nodes: (a,) })),
    ))
}

#[parser]
pub(crate) fn pulldown_strength10(s: Span) -> IResult<Span, PulldownStrength> {
    let (s, a) = paren(triple(strength1, symbol(","), strength0))(s)?;
    Ok((
        s,
        PulldownStrength::Strength10(Box::new(PulldownStrength10 { nodes: (a,) })),
    ))
}

#[parser]
pub(crate) fn pulldown_strength0(s: Span) -> IResult<Span, PulldownStrength> {
    let (s, a) = paren(strength0)(s)?;
    Ok((
        s,
        PulldownStrength::Strength0(Box::new(PulldownStrength0 { nodes: (a,) })),
    ))
}

#[parser]
pub(crate) fn pullup_strength(s: Span) -> IResult<Span, PullupStrength> {
    alt((pullup_strength01, pullup_strength10, pullup_strength1))(s)
}

#[parser]
pub(crate) fn pullup_strength01(s: Span) -> IResult<Span, PullupStrength> {
    let (s, a) = paren(triple(strength0, symbol(","), strength1))(s)?;
    Ok((
        s,
        PullupStrength::Strength01(Box::new(PullupStrength01 { nodes: (a,) })),
    ))
}

#[parser]
pub(crate) fn pullup_strength10(s: Span) -> IResult<Span, PullupStrength> {
    let (s, a) = paren(triple(strength1, symbol(","), strength0))(s)?;
    Ok((
        s,
        PullupStrength::Strength10(Box::new(PullupStrength10 { nodes: (a,) })),
    ))
}

#[parser]
pub(crate) fn pullup_strength1(s: Span) -> IResult<Span, PullupStrength> {
    let (s, a) = paren(strength1)(s)?;
    Ok((
        s,
        PullupStrength::Strength1(Box::new(PullupStrength1 { nodes: (a,) })),
    ))
}
