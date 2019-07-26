use crate::*;

// -----------------------------------------------------------------------------

#[packrat_parser]
#[parser]
pub(crate) fn number(s: Span) -> IResult<Span, Number> {
    alt((
        map(real_number, |x| Number::RealNumber(Box::new(x))),
        map(integral_number, |x| Number::IntegralNumber(Box::new(x))),
    ))(s)
}

#[parser]
pub(crate) fn integral_number(s: Span) -> IResult<Span, IntegralNumber> {
    alt((
        map(octal_number, |x| IntegralNumber::OctalNumber(Box::new(x))),
        map(binary_number, |x| IntegralNumber::BinaryNumber(Box::new(x))),
        map(hex_number, |x| IntegralNumber::HexNumber(Box::new(x))),
        map(decimal_number, |x| {
            IntegralNumber::DecimalNumber(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn decimal_number(s: Span) -> IResult<Span, DecimalNumber> {
    alt((
        decimal_number_base_unsigned,
        decimal_number_base_x_number,
        decimal_number_base_z_number,
        map(unsigned_number, |x| {
            DecimalNumber::UnsignedNumber(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn decimal_number_base_unsigned(s: Span) -> IResult<Span, DecimalNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = decimal_base(s)?;
    let (s, c) = unsigned_number(s)?;
    Ok((
        s,
        DecimalNumber::BaseUnsigned(Box::new(DecimalNumberBaseUnsigned { nodes: (a, b, c) })),
    ))
}

#[parser]
pub(crate) fn decimal_number_base_x_number(s: Span) -> IResult<Span, DecimalNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = decimal_base(s)?;
    let (s, c) = x_number(s)?;
    Ok((
        s,
        DecimalNumber::BaseXNumber(Box::new(DecimalNumberBaseXNumber { nodes: (a, b, c) })),
    ))
}

#[parser]
pub(crate) fn decimal_number_base_z_number(s: Span) -> IResult<Span, DecimalNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = decimal_base(s)?;
    let (s, c) = z_number(s)?;
    Ok((
        s,
        DecimalNumber::BaseZNumber(Box::new(DecimalNumberBaseZNumber { nodes: (a, b, c) })),
    ))
}

#[parser]
pub(crate) fn binary_number(s: Span) -> IResult<Span, BinaryNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = binary_base(s)?;
    let (s, c) = binary_value(s)?;
    Ok((s, BinaryNumber { nodes: (a, b, c) }))
}

#[parser]
pub(crate) fn octal_number(s: Span) -> IResult<Span, OctalNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = octal_base(s)?;
    let (s, c) = octal_value(s)?;
    Ok((s, OctalNumber { nodes: (a, b, c) }))
}

#[parser]
pub(crate) fn hex_number(s: Span) -> IResult<Span, HexNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = hex_base(s)?;
    let (s, c) = hex_value(s)?;
    Ok((s, HexNumber { nodes: (a, b, c) }))
}

#[parser]
pub(crate) fn sign(s: Span) -> IResult<Span, Sign> {
    alt((
        map(symbol("+"), |x| Sign::Plus(Box::new(x))),
        map(symbol("-"), |x| Sign::Minus(Box::new(x))),
    ))(s)
}

#[parser]
pub(crate) fn size(s: Span) -> IResult<Span, Size> {
    let (s, a) = non_zero_unsigned_number(s)?;
    Ok((s, Size { nodes: (a,) }))
}

#[parser]
pub(crate) fn non_zero_unsigned_number(s: Span) -> IResult<Span, NonZeroUnsignedNumber> {
    let (s, a) = ws(non_zero_unsigned_number_impl)(s)?;
    Ok((s, NonZeroUnsignedNumber { nodes: a }))
}

#[parser]
pub(crate) fn non_zero_unsigned_number_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = is_a("123456789")(s)?;
    let (s, a) = fold_many0(alt((tag("_"), digit1)), a, |acc, item| {
        concat(acc, item).unwrap()
    })(s)?;
    Ok((s, a.into()))
}

#[parser]
pub(crate) fn real_number(s: Span) -> IResult<Span, RealNumber> {
    alt((
        real_number_floating,
        map(fixed_point_number, |x| {
            RealNumber::FixedPointNumber(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn real_number_floating(s: Span) -> IResult<Span, RealNumber> {
    let (s, a) = unsigned_number(s)?;
    let (s, b) = opt(pair(symbol("."), unsigned_number))(s)?;
    let (s, c) = exp(s)?;
    let (s, d) = opt(sign)(s)?;
    let (s, e) = unsigned_number(s)?;
    Ok((
        s,
        RealNumber::Floating(Box::new(RealNumberFloating {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[parser]
pub(crate) fn fixed_point_number(s: Span) -> IResult<Span, FixedPointNumber> {
    let (s, a) = unsigned_number(s)?;
    let (s, b) = map(tag("."), |x: Span| Symbol {
        nodes: (x.into(), vec![]),
    })(s)?;
    let (s, c) = unsigned_number(s)?;
    Ok((s, FixedPointNumber { nodes: (a, b, c) }))
}

#[parser]
pub(crate) fn exp(s: Span) -> IResult<Span, Exp> {
    let (s, a) = alt((symbol("e"), symbol("E")))(s)?;
    Ok((s, Exp { nodes: (a,) }))
}

#[parser]
pub(crate) fn unsigned_number(s: Span) -> IResult<Span, UnsignedNumber> {
    let (s, a) = ws(unsigned_number_impl)(s)?;
    Ok((s, UnsignedNumber { nodes: a }))
}

#[parser]
pub(crate) fn unsigned_number_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = digit1(s)?;
    let (s, a) = fold_many0(alt((tag("_"), digit1)), a, |acc, item| {
        concat(acc, item).unwrap()
    })(s)?;
    Ok((s, a.into()))
}

#[parser]
pub(crate) fn binary_value(s: Span) -> IResult<Span, BinaryValue> {
    let (s, a) = ws(binary_value_impl)(s)?;
    Ok((s, BinaryValue { nodes: a }))
}

#[parser]
pub(crate) fn binary_value_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = is_a("01xXzZ?")(s)?;
    let (s, a) = fold_many0(alt((tag("_"), is_a("01xXzZ?"))), a, |acc, item| {
        concat(acc, item).unwrap()
    })(s)?;
    Ok((s, a.into()))
}

#[parser]
pub(crate) fn octal_value(s: Span) -> IResult<Span, OctalValue> {
    let (s, a) = ws(octal_value_impl)(s)?;
    Ok((s, OctalValue { nodes: a }))
}

#[parser]
pub(crate) fn octal_value_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = is_a("01234567xXzZ?")(s)?;
    let (s, a) = fold_many0(alt((tag("_"), is_a("01234567xXzZ?"))), a, |acc, item| {
        concat(acc, item).unwrap()
    })(s)?;
    Ok((s, a.into()))
}

#[parser]
pub(crate) fn hex_value(s: Span) -> IResult<Span, HexValue> {
    let (s, a) = ws(hex_value_impl)(s)?;
    Ok((s, HexValue { nodes: a }))
}

#[parser]
pub(crate) fn hex_value_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = is_a("0123456789abcdefABCDEFxXzZ?")(s)?;
    let (s, a) = fold_many0(
        alt((tag("_"), is_a("0123456789abcdefABCDEFxXzZ?"))),
        a,
        |acc, item| concat(acc, item).unwrap(),
    )(s)?;
    Ok((s, a.into()))
}

#[parser]
pub(crate) fn decimal_base(s: Span) -> IResult<Span, DecimalBase> {
    let (s, a) = ws(decimal_base_impl)(s)?;
    Ok((s, DecimalBase { nodes: a }))
}

#[parser]
pub(crate) fn decimal_base_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = alt((tag_no_case("'d"), tag_no_case("'sd")))(s)?;
    Ok((s, a.into()))
}

#[parser]
pub(crate) fn binary_base(s: Span) -> IResult<Span, BinaryBase> {
    let (s, a) = ws(binary_base_impl)(s)?;
    Ok((s, BinaryBase { nodes: a }))
}

#[parser]
pub(crate) fn binary_base_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = alt((tag_no_case("'b"), tag_no_case("'sb")))(s)?;
    Ok((s, a.into()))
}

#[parser]
pub(crate) fn octal_base(s: Span) -> IResult<Span, OctalBase> {
    let (s, a) = ws(octal_base_impl)(s)?;
    Ok((s, OctalBase { nodes: a }))
}

#[parser]
pub(crate) fn octal_base_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = alt((tag_no_case("'o"), tag_no_case("'so")))(s)?;
    Ok((s, a.into()))
}

#[parser]
pub(crate) fn hex_base(s: Span) -> IResult<Span, HexBase> {
    let (s, a) = ws(hex_base_impl)(s)?;
    Ok((s, HexBase { nodes: a }))
}

#[parser]
pub(crate) fn hex_base_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = alt((tag_no_case("'h"), tag_no_case("'sh")))(s)?;
    Ok((s, a.into()))
}

#[parser]
pub(crate) fn x_number(s: Span) -> IResult<Span, XNumber> {
    let (s, a) = ws(x_number_impl)(s)?;
    Ok((s, XNumber { nodes: a }))
}

#[parser]
pub(crate) fn x_number_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = tag_no_case("x")(s)?;
    let (s, a) = fold_many0(alt((tag("_"), is_a("_"))), a, |acc, item| {
        concat(acc, item).unwrap()
    })(s)?;
    Ok((s, a.into()))
}

#[parser]
pub(crate) fn z_number(s: Span) -> IResult<Span, ZNumber> {
    let (s, a) = ws(z_number_impl)(s)?;
    Ok((s, ZNumber { nodes: a }))
}

#[parser]
pub(crate) fn z_number_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = alt((tag_no_case("z"), tag("?")))(s)?;
    let (s, a) = fold_many0(alt((tag("_"), is_a("_"))), a, |acc, item| {
        concat(acc, item).unwrap()
    })(s)?;
    Ok((s, a.into()))
}

#[parser]
pub(crate) fn unbased_unsized_literal(s: Span) -> IResult<Span, UnbasedUnsizedLiteral> {
    let (s, a) = alt((symbol("'0"), symbol("'1"), symbol("'z"), symbol("'x")))(s)?;
    Ok((s, UnbasedUnsizedLiteral { nodes: (a,) }))
}
