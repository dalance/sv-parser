use crate::parser::*;
use nom::branch::*;
use nom::bytes::complete::*;
use nom::character::complete::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum Number<'a> {
    IntegralNumber(IntegralNumber<'a>),
    RealNumber(RealNumber<'a>),
}

#[derive(Debug)]
pub enum IntegralNumber<'a> {
    DecimalNumber(DecimalNumber<'a>),
    OctalNumber(OctalNumber<'a>),
    BinaryNumber(BinaryNumber<'a>),
    HexNumber(HexNumber<'a>),
}

#[derive(Debug)]
pub enum DecimalNumber<'a> {
    UnsignedNumber(UnsignedNumber<'a>),
    BaseUnsigned(DecimalNumberBaseUnsigned<'a>),
    BaseXNumber(DecimalNumberBaseXNumber<'a>),
    BaseZNumber(DecimalNumberBaseZNumber<'a>),
}

#[derive(Debug)]
pub struct DecimalNumberBaseUnsigned<'a> {
    pub nodes: (Option<Size<'a>>, DecimalBase<'a>, UnsignedNumber<'a>),
}

#[derive(Debug)]
pub struct DecimalNumberBaseXNumber<'a> {
    pub nodes: (Option<Size<'a>>, DecimalBase<'a>, XNumber<'a>),
}

#[derive(Debug)]
pub struct DecimalNumberBaseZNumber<'a> {
    pub nodes: (Option<Size<'a>>, DecimalBase<'a>, ZNumber<'a>),
}

#[derive(Debug)]
pub struct BinaryNumber<'a> {
    pub nodes: (Option<Size<'a>>, BinaryBase<'a>, BinaryValue<'a>),
}

#[derive(Debug)]
pub struct OctalNumber<'a> {
    pub nodes: (Option<Size<'a>>, OctalBase<'a>, OctalValue<'a>),
}

#[derive(Debug)]
pub struct HexNumber<'a> {
    pub nodes: (Option<Size<'a>>, HexBase<'a>, HexValue<'a>),
}

#[derive(Debug)]
pub enum Sign<'a> {
    Plus(Symbol<'a>),
    Minus(Symbol<'a>),
}

#[derive(Debug)]
pub struct Size<'a> {
    pub nodes: (NonZeroUnsignedNumber<'a>,),
}

#[derive(Debug)]
pub struct NonZeroUnsignedNumber<'a> {
    pub nodes: (Span<'a>, Vec<WhiteSpace<'a>>),
}

#[derive(Debug)]
pub enum RealNumber<'a> {
    FixedPointNumber(FixedPointNumber<'a>),
    Floating(RealNumberFloating<'a>),
}

#[derive(Debug)]
pub struct RealNumberFloating<'a> {
    pub nodes: (
        UnsignedNumber<'a>,
        Option<(Symbol<'a>, UnsignedNumber<'a>)>,
        Exp<'a>,
        Option<Sign<'a>>,
        UnsignedNumber<'a>,
    ),
}

#[derive(Debug)]
pub struct FixedPointNumber<'a> {
    pub nodes: (UnsignedNumber<'a>, Symbol<'a>, UnsignedNumber<'a>),
}

#[derive(Debug)]
pub struct Exp<'a> {
    pub nodes: (Symbol<'a>,),
}

#[derive(Debug)]
pub struct UnsignedNumber<'a> {
    pub nodes: (Span<'a>, Vec<WhiteSpace<'a>>),
}

#[derive(Debug)]
pub struct BinaryValue<'a> {
    pub nodes: (Span<'a>, Vec<WhiteSpace<'a>>),
}

#[derive(Debug)]
pub struct OctalValue<'a> {
    pub nodes: (Span<'a>, Vec<WhiteSpace<'a>>),
}

#[derive(Debug)]
pub struct HexValue<'a> {
    pub nodes: (Span<'a>, Vec<WhiteSpace<'a>>),
}

#[derive(Debug)]
pub struct DecimalBase<'a> {
    pub nodes: (Span<'a>, Vec<WhiteSpace<'a>>),
}

#[derive(Debug)]
pub struct BinaryBase<'a> {
    pub nodes: (Span<'a>, Vec<WhiteSpace<'a>>),
}

#[derive(Debug)]
pub struct OctalBase<'a> {
    pub nodes: (Span<'a>, Vec<WhiteSpace<'a>>),
}

#[derive(Debug)]
pub struct HexBase<'a> {
    pub nodes: (Span<'a>, Vec<WhiteSpace<'a>>),
}

#[derive(Debug)]
pub struct XNumber<'a> {
    pub nodes: (Span<'a>, Vec<WhiteSpace<'a>>),
}

#[derive(Debug)]
pub struct ZNumber<'a> {
    pub nodes: (Span<'a>, Vec<WhiteSpace<'a>>),
}

#[derive(Debug)]
pub struct UnbasedUnsizedLiteral<'a> {
    pub nodes: (Symbol<'a>,),
}

// -----------------------------------------------------------------------------

pub fn number(s: Span) -> IResult<Span, Number> {
    alt((
        map(real_number, |x| Number::RealNumber(x)),
        map(integral_number, |x| Number::IntegralNumber(x)),
    ))(s)
}

pub fn integral_number(s: Span) -> IResult<Span, IntegralNumber> {
    alt((
        map(octal_number, |x| IntegralNumber::OctalNumber(x)),
        map(binary_number, |x| IntegralNumber::BinaryNumber(x)),
        map(hex_number, |x| IntegralNumber::HexNumber(x)),
        map(decimal_number, |x| IntegralNumber::DecimalNumber(x)),
    ))(s)
}

pub fn decimal_number(s: Span) -> IResult<Span, DecimalNumber> {
    alt((
        decimal_number_base_unsigned,
        decimal_number_base_x_number,
        decimal_number_base_z_number,
        map(unsigned_number, |x| DecimalNumber::UnsignedNumber(x)),
    ))(s)
}

pub fn decimal_number_base_unsigned(s: Span) -> IResult<Span, DecimalNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = decimal_base(s)?;
    let (s, c) = unsigned_number(s)?;
    Ok((
        s,
        DecimalNumber::BaseUnsigned(DecimalNumberBaseUnsigned { nodes: (a, b, c) }),
    ))
}

pub fn decimal_number_base_x_number(s: Span) -> IResult<Span, DecimalNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = decimal_base(s)?;
    let (s, c) = x_number(s)?;
    Ok((
        s,
        DecimalNumber::BaseXNumber(DecimalNumberBaseXNumber { nodes: (a, b, c) }),
    ))
}

pub fn decimal_number_base_z_number(s: Span) -> IResult<Span, DecimalNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = decimal_base(s)?;
    let (s, c) = z_number(s)?;
    Ok((
        s,
        DecimalNumber::BaseZNumber(DecimalNumberBaseZNumber { nodes: (a, b, c) }),
    ))
}

pub fn binary_number(s: Span) -> IResult<Span, BinaryNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = binary_base(s)?;
    let (s, c) = binary_value(s)?;
    Ok((s, BinaryNumber { nodes: (a, b, c) }))
}

pub fn octal_number(s: Span) -> IResult<Span, OctalNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = octal_base(s)?;
    let (s, c) = octal_value(s)?;
    Ok((s, OctalNumber { nodes: (a, b, c) }))
}

pub fn hex_number(s: Span) -> IResult<Span, HexNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = hex_base(s)?;
    let (s, c) = hex_value(s)?;
    Ok((s, HexNumber { nodes: (a, b, c) }))
}

pub fn sign(s: Span) -> IResult<Span, Sign> {
    alt((
        map(symbol("+"), |x| Sign::Plus(x)),
        map(symbol("-"), |x| Sign::Minus(x)),
    ))(s)
}

pub fn size(s: Span) -> IResult<Span, Size> {
    let (s, a) = non_zero_unsigned_number(s)?;
    Ok((s, Size { nodes: (a,) }))
}

pub fn non_zero_unsigned_number(s: Span) -> IResult<Span, NonZeroUnsignedNumber> {
    let (s, a) = ws(non_zero_unsigned_number_impl)(s)?;
    Ok((s, NonZeroUnsignedNumber { nodes: a }))
}

pub fn non_zero_unsigned_number_impl(s: Span) -> IResult<Span, Span> {
    let (s, a) = is_a("123456789")(s)?;
    fold_many0(alt((tag("_"), digit1)), a, |acc, item| {
        concat(acc, item).unwrap()
    })(s)
}

pub fn real_number(s: Span) -> IResult<Span, RealNumber> {
    alt((
        real_number_floating,
        map(fixed_point_number, |x| RealNumber::FixedPointNumber(x)),
    ))(s)
}

pub fn real_number_floating(s: Span) -> IResult<Span, RealNumber> {
    let (s, a) = unsigned_number(s)?;
    let (s, b) = opt(pair(symbol("."), unsigned_number))(s)?;
    let (s, c) = exp(s)?;
    let (s, d) = opt(sign)(s)?;
    let (s, e) = unsigned_number(s)?;
    Ok((
        s,
        RealNumber::Floating(RealNumberFloating {
            nodes: (a, b, c, d, e),
        }),
    ))
}

pub fn fixed_point_number(s: Span) -> IResult<Span, FixedPointNumber> {
    let (s, a) = unsigned_number(s)?;
    let (s, b) = map(tag("."), |x| Symbol { nodes: (x, vec![]) })(s)?;;
    let (s, c) = unsigned_number(s)?;
    Ok((s, FixedPointNumber { nodes: (a, b, c) }))
}

pub fn exp(s: Span) -> IResult<Span, Exp> {
    let (s, a) = alt((symbol("e"), symbol("E")))(s)?;
    Ok((s, Exp { nodes: (a,) }))
}

pub fn unsigned_number(s: Span) -> IResult<Span, UnsignedNumber> {
    let (s, a) = ws(unsigned_number_impl)(s)?;
    Ok((s, UnsignedNumber { nodes: a }))
}

pub fn unsigned_number_impl(s: Span) -> IResult<Span, Span> {
    let (s, a) = digit1(s)?;
    fold_many0(alt((tag("_"), digit1)), a, |acc, item| {
        concat(acc, item).unwrap()
    })(s)
}

pub fn binary_value(s: Span) -> IResult<Span, BinaryValue> {
    let (s, a) = ws(binary_value_impl)(s)?;
    Ok((s, BinaryValue { nodes: a }))
}

pub fn binary_value_impl(s: Span) -> IResult<Span, Span> {
    let (s, a) = is_a("01xXzZ?")(s)?;
    fold_many0(alt((tag("_"), is_a("01xXzZ?"))), a, |acc, item| {
        concat(acc, item).unwrap()
    })(s)
}

pub fn octal_value(s: Span) -> IResult<Span, OctalValue> {
    let (s, a) = ws(octal_value_impl)(s)?;
    Ok((s, OctalValue { nodes: a }))
}

pub fn octal_value_impl(s: Span) -> IResult<Span, Span> {
    let (s, a) = is_a("01234567xXzZ?")(s)?;
    fold_many0(alt((tag("_"), is_a("01234567xXzZ?"))), a, |acc, item| {
        concat(acc, item).unwrap()
    })(s)
}

pub fn hex_value(s: Span) -> IResult<Span, HexValue> {
    let (s, a) = ws(hex_value_impl)(s)?;
    Ok((s, HexValue { nodes: a }))
}

pub fn hex_value_impl(s: Span) -> IResult<Span, Span> {
    let (s, a) = is_a("0123456789abcdefABCDEFxXzZ?")(s)?;
    fold_many0(
        alt((tag("_"), is_a("0123456789abcdefABCDEFxXzZ?"))),
        a,
        |acc, item| concat(acc, item).unwrap(),
    )(s)
}

pub fn decimal_base(s: Span) -> IResult<Span, DecimalBase> {
    let (s, a) = ws(decimal_base_impl)(s)?;
    Ok((s, DecimalBase { nodes: a }))
}

pub fn decimal_base_impl(s: Span) -> IResult<Span, Span> {
    alt((tag_no_case("'d"), tag_no_case("'sd")))(s)
}

pub fn binary_base(s: Span) -> IResult<Span, BinaryBase> {
    let (s, a) = ws(binary_base_impl)(s)?;
    Ok((s, BinaryBase { nodes: a }))
}

pub fn binary_base_impl(s: Span) -> IResult<Span, Span> {
    alt((tag_no_case("'b"), tag_no_case("'sb")))(s)
}

pub fn octal_base(s: Span) -> IResult<Span, OctalBase> {
    let (s, a) = ws(octal_base_impl)(s)?;
    Ok((s, OctalBase { nodes: a }))
}

pub fn octal_base_impl(s: Span) -> IResult<Span, Span> {
    alt((tag_no_case("'o"), tag_no_case("'so")))(s)
}

pub fn hex_base(s: Span) -> IResult<Span, HexBase> {
    let (s, a) = ws(hex_base_impl)(s)?;
    Ok((s, HexBase { nodes: a }))
}

pub fn hex_base_impl(s: Span) -> IResult<Span, Span> {
    alt((tag_no_case("'h"), tag_no_case("'sh")))(s)
}

pub fn x_number(s: Span) -> IResult<Span, XNumber> {
    let (s, a) = ws(x_number_impl)(s)?;
    Ok((s, XNumber { nodes: a }))
}

pub fn x_number_impl(s: Span) -> IResult<Span, Span> {
    let (s, a) = tag_no_case("x")(s)?;
    fold_many0(alt((tag("_"), is_a("_"))), a, |acc, item| {
        concat(acc, item).unwrap()
    })(s)
}

pub fn z_number(s: Span) -> IResult<Span, ZNumber> {
    let (s, a) = ws(z_number_impl)(s)?;
    Ok((s, ZNumber { nodes: a }))
}

pub fn z_number_impl(s: Span) -> IResult<Span, Span> {
    let (s, a) = alt((tag_no_case("z"), tag("?")))(s)?;
    fold_many0(alt((tag("_"), is_a("_"))), a, |acc, item| {
        concat(acc, item).unwrap()
    })(s)
}

pub fn unbased_unsized_literal(s: Span) -> IResult<Span, UnbasedUnsizedLiteral> {
    let (s, a) = alt((symbol("'0"), symbol("'1"), symbol("'z"), symbol("'x")))(s)?;
    Ok((s, UnbasedUnsizedLiteral { nodes: (a,) }))
}

// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("659"))),
            "Ok((LocatedSpanEx { offset: 3, line: 1, fragment: \"\", extra: () }, IntegralNumber(DecimalNumber(UnsignedNumber(UnsignedNumber { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"659\", extra: () }, []) })))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("'h 837FF"))),
            "Ok((LocatedSpanEx { offset: 8, line: 1, fragment: \"\", extra: () }, IntegralNumber(HexNumber(HexNumber { nodes: (None, HexBase { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"\\\'h\", extra: () }, [Space(LocatedSpanEx { offset: 2, line: 1, fragment: \" \", extra: () })]) }, HexValue { nodes: (LocatedSpanEx { offset: 3, line: 1, fragment: \"837FF\", extra: () }, []) }) }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("'o7460"))),
            "Ok((LocatedSpanEx { offset: 6, line: 1, fragment: \"\", extra: () }, IntegralNumber(OctalNumber(OctalNumber { nodes: (None, OctalBase { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"\\\'o\", extra: () }, []) }, OctalValue { nodes: (LocatedSpanEx { offset: 2, line: 1, fragment: \"7460\", extra: () }, []) }) }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("4af"))),
            "Err(Error((LocatedSpanEx { offset: 1, line: 1, fragment: \"af\", extra: () }, Eof)))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("4'b1001"))),
            "Ok((LocatedSpanEx { offset: 7, line: 1, fragment: \"\", extra: () }, IntegralNumber(BinaryNumber(BinaryNumber { nodes: (Some(Size { nodes: (NonZeroUnsignedNumber { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"4\", extra: () }, []) },) }), BinaryBase { nodes: (LocatedSpanEx { offset: 1, line: 1, fragment: \"\\\'b\", extra: () }, []) }, BinaryValue { nodes: (LocatedSpanEx { offset: 3, line: 1, fragment: \"1001\", extra: () }, []) }) }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("5 'D 3"))),
            "Ok((LocatedSpanEx { offset: 6, line: 1, fragment: \"\", extra: () }, IntegralNumber(DecimalNumber(BaseUnsigned(DecimalNumberBaseUnsigned { nodes: (Some(Size { nodes: (NonZeroUnsignedNumber { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"5\", extra: () }, [Space(LocatedSpanEx { offset: 1, line: 1, fragment: \" \", extra: () })]) },) }), DecimalBase { nodes: (LocatedSpanEx { offset: 2, line: 1, fragment: \"\\\'D\", extra: () }, [Space(LocatedSpanEx { offset: 4, line: 1, fragment: \" \", extra: () })]) }, UnsignedNumber { nodes: (LocatedSpanEx { offset: 5, line: 1, fragment: \"3\", extra: () }, []) }) })))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("3'b01x"))),
            "Ok((LocatedSpanEx { offset: 6, line: 1, fragment: \"\", extra: () }, IntegralNumber(BinaryNumber(BinaryNumber { nodes: (Some(Size { nodes: (NonZeroUnsignedNumber { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"3\", extra: () }, []) },) }), BinaryBase { nodes: (LocatedSpanEx { offset: 1, line: 1, fragment: \"\\\'b\", extra: () }, []) }, BinaryValue { nodes: (LocatedSpanEx { offset: 3, line: 1, fragment: \"01x\", extra: () }, []) }) }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("12'hx"))),
            "Ok((LocatedSpanEx { offset: 5, line: 1, fragment: \"\", extra: () }, IntegralNumber(HexNumber(HexNumber { nodes: (Some(Size { nodes: (NonZeroUnsignedNumber { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"12\", extra: () }, []) },) }), HexBase { nodes: (LocatedSpanEx { offset: 2, line: 1, fragment: \"\\\'h\", extra: () }, []) }, HexValue { nodes: (LocatedSpanEx { offset: 4, line: 1, fragment: \"x\", extra: () }, []) }) }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("16'hz"))),
            "Ok((LocatedSpanEx { offset: 5, line: 1, fragment: \"\", extra: () }, IntegralNumber(HexNumber(HexNumber { nodes: (Some(Size { nodes: (NonZeroUnsignedNumber { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"16\", extra: () }, []) },) }), HexBase { nodes: (LocatedSpanEx { offset: 2, line: 1, fragment: \"\\\'h\", extra: () }, []) }, HexValue { nodes: (LocatedSpanEx { offset: 4, line: 1, fragment: \"z\", extra: () }, []) }) }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("8 'd -6"))),
            "Err(Error((LocatedSpanEx { offset: 2, line: 1, fragment: \"\\\'d -6\", extra: () }, Eof)))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("4 'shf"))),
            "Ok((LocatedSpanEx { offset: 6, line: 1, fragment: \"\", extra: () }, IntegralNumber(HexNumber(HexNumber { nodes: (Some(Size { nodes: (NonZeroUnsignedNumber { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"4\", extra: () }, [Space(LocatedSpanEx { offset: 1, line: 1, fragment: \" \", extra: () })]) },) }), HexBase { nodes: (LocatedSpanEx { offset: 2, line: 1, fragment: \"\\\'sh\", extra: () }, []) }, HexValue { nodes: (LocatedSpanEx { offset: 5, line: 1, fragment: \"f\", extra: () }, []) }) }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("16'sd?"))),
            "Ok((LocatedSpanEx { offset: 6, line: 1, fragment: \"\", extra: () }, IntegralNumber(DecimalNumber(BaseZNumber(DecimalNumberBaseZNumber { nodes: (Some(Size { nodes: (NonZeroUnsignedNumber { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"16\", extra: () }, []) },) }), DecimalBase { nodes: (LocatedSpanEx { offset: 2, line: 1, fragment: \"\\\'sd\", extra: () }, []) }, ZNumber { nodes: (LocatedSpanEx { offset: 5, line: 1, fragment: \"?\", extra: () }, []) }) })))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("27_195_000"))),
            "Ok((LocatedSpanEx { offset: 10, line: 1, fragment: \"\", extra: () }, IntegralNumber(DecimalNumber(UnsignedNumber(UnsignedNumber { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"27_195_000\", extra: () }, []) })))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("16'b0011_0101_0001_1111"))),
            "Ok((LocatedSpanEx { offset: 23, line: 1, fragment: \"\", extra: () }, IntegralNumber(BinaryNumber(BinaryNumber { nodes: (Some(Size { nodes: (NonZeroUnsignedNumber { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"16\", extra: () }, []) },) }), BinaryBase { nodes: (LocatedSpanEx { offset: 2, line: 1, fragment: \"\\\'b\", extra: () }, []) }, BinaryValue { nodes: (LocatedSpanEx { offset: 4, line: 1, fragment: \"0011_0101_0001_1111\", extra: () }, []) }) }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("32 'h 12ab_f001"))),
            "Ok((LocatedSpanEx { offset: 15, line: 1, fragment: \"\", extra: () }, IntegralNumber(HexNumber(HexNumber { nodes: (Some(Size { nodes: (NonZeroUnsignedNumber { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"32\", extra: () }, [Space(LocatedSpanEx { offset: 2, line: 1, fragment: \" \", extra: () })]) },) }), HexBase { nodes: (LocatedSpanEx { offset: 3, line: 1, fragment: \"\\\'h\", extra: () }, [Space(LocatedSpanEx { offset: 5, line: 1, fragment: \" \", extra: () })]) }, HexValue { nodes: (LocatedSpanEx { offset: 6, line: 1, fragment: \"12ab_f001\", extra: () }, []) }) }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("1.2"))),
            "Ok((LocatedSpanEx { offset: 3, line: 1, fragment: \"\", extra: () }, RealNumber(FixedPointNumber(FixedPointNumber { nodes: (UnsignedNumber { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"1\", extra: () }, []) }, Symbol { nodes: (LocatedSpanEx { offset: 1, line: 1, fragment: \".\", extra: () }, []) }, UnsignedNumber { nodes: (LocatedSpanEx { offset: 2, line: 1, fragment: \"2\", extra: () }, []) }) }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("0.1"))),
            "Ok((LocatedSpanEx { offset: 3, line: 1, fragment: \"\", extra: () }, RealNumber(FixedPointNumber(FixedPointNumber { nodes: (UnsignedNumber { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"0\", extra: () }, []) }, Symbol { nodes: (LocatedSpanEx { offset: 1, line: 1, fragment: \".\", extra: () }, []) }, UnsignedNumber { nodes: (LocatedSpanEx { offset: 2, line: 1, fragment: \"1\", extra: () }, []) }) }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("2394.26331"))),
            "Ok((LocatedSpanEx { offset: 10, line: 1, fragment: \"\", extra: () }, RealNumber(FixedPointNumber(FixedPointNumber { nodes: (UnsignedNumber { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"2394\", extra: () }, []) }, Symbol { nodes: (LocatedSpanEx { offset: 4, line: 1, fragment: \".\", extra: () }, []) }, UnsignedNumber { nodes: (LocatedSpanEx { offset: 5, line: 1, fragment: \"26331\", extra: () }, []) }) }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("1.2E12"))),
            "Ok((LocatedSpanEx { offset: 6, line: 1, fragment: \"\", extra: () }, RealNumber(Floating(RealNumberFloating { nodes: (UnsignedNumber { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"1\", extra: () }, []) }, Some((Symbol { nodes: (LocatedSpanEx { offset: 1, line: 1, fragment: \".\", extra: () }, []) }, UnsignedNumber { nodes: (LocatedSpanEx { offset: 2, line: 1, fragment: \"2\", extra: () }, []) })), Exp { nodes: (Symbol { nodes: (LocatedSpanEx { offset: 3, line: 1, fragment: \"E\", extra: () }, []) },) }, None, UnsignedNumber { nodes: (LocatedSpanEx { offset: 4, line: 1, fragment: \"12\", extra: () }, []) }) }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("1.30e-2"))),
            "Ok((LocatedSpanEx { offset: 7, line: 1, fragment: \"\", extra: () }, RealNumber(Floating(RealNumberFloating { nodes: (UnsignedNumber { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"1\", extra: () }, []) }, Some((Symbol { nodes: (LocatedSpanEx { offset: 1, line: 1, fragment: \".\", extra: () }, []) }, UnsignedNumber { nodes: (LocatedSpanEx { offset: 2, line: 1, fragment: \"30\", extra: () }, []) })), Exp { nodes: (Symbol { nodes: (LocatedSpanEx { offset: 4, line: 1, fragment: \"e\", extra: () }, []) },) }, Some(Minus(Symbol { nodes: (LocatedSpanEx { offset: 5, line: 1, fragment: \"-\", extra: () }, []) })), UnsignedNumber { nodes: (LocatedSpanEx { offset: 6, line: 1, fragment: \"2\", extra: () }, []) }) }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("0.1e-0"))),
            "Ok((LocatedSpanEx { offset: 6, line: 1, fragment: \"\", extra: () }, RealNumber(Floating(RealNumberFloating { nodes: (UnsignedNumber { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"0\", extra: () }, []) }, Some((Symbol { nodes: (LocatedSpanEx { offset: 1, line: 1, fragment: \".\", extra: () }, []) }, UnsignedNumber { nodes: (LocatedSpanEx { offset: 2, line: 1, fragment: \"1\", extra: () }, []) })), Exp { nodes: (Symbol { nodes: (LocatedSpanEx { offset: 3, line: 1, fragment: \"e\", extra: () }, []) },) }, Some(Minus(Symbol { nodes: (LocatedSpanEx { offset: 4, line: 1, fragment: \"-\", extra: () }, []) })), UnsignedNumber { nodes: (LocatedSpanEx { offset: 5, line: 1, fragment: \"0\", extra: () }, []) }) }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("23E10"))),
            "Ok((LocatedSpanEx { offset: 5, line: 1, fragment: \"\", extra: () }, RealNumber(Floating(RealNumberFloating { nodes: (UnsignedNumber { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"23\", extra: () }, []) }, None, Exp { nodes: (Symbol { nodes: (LocatedSpanEx { offset: 2, line: 1, fragment: \"E\", extra: () }, []) },) }, None, UnsignedNumber { nodes: (LocatedSpanEx { offset: 3, line: 1, fragment: \"10\", extra: () }, []) }) }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("29E-2"))),
            "Ok((LocatedSpanEx { offset: 5, line: 1, fragment: \"\", extra: () }, RealNumber(Floating(RealNumberFloating { nodes: (UnsignedNumber { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"29\", extra: () }, []) }, None, Exp { nodes: (Symbol { nodes: (LocatedSpanEx { offset: 2, line: 1, fragment: \"E\", extra: () }, []) },) }, Some(Minus(Symbol { nodes: (LocatedSpanEx { offset: 3, line: 1, fragment: \"-\", extra: () }, []) })), UnsignedNumber { nodes: (LocatedSpanEx { offset: 4, line: 1, fragment: \"2\", extra: () }, []) }) }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("236.123_763_e-12"))),
            "Ok((LocatedSpanEx { offset: 16, line: 1, fragment: \"\", extra: () }, RealNumber(Floating(RealNumberFloating { nodes: (UnsignedNumber { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"236\", extra: () }, []) }, Some((Symbol { nodes: (LocatedSpanEx { offset: 3, line: 1, fragment: \".\", extra: () }, []) }, UnsignedNumber { nodes: (LocatedSpanEx { offset: 4, line: 1, fragment: \"123_763_\", extra: () }, []) })), Exp { nodes: (Symbol { nodes: (LocatedSpanEx { offset: 12, line: 1, fragment: \"e\", extra: () }, []) },) }, Some(Minus(Symbol { nodes: (LocatedSpanEx { offset: 13, line: 1, fragment: \"-\", extra: () }, []) })), UnsignedNumber { nodes: (LocatedSpanEx { offset: 14, line: 1, fragment: \"12\", extra: () }, []) }) }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new(".12"))),
            "Err(Error((LocatedSpanEx { offset: 0, line: 1, fragment: \".12\", extra: () }, Digit)))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("9."))),
            "Err(Error((LocatedSpanEx { offset: 1, line: 1, fragment: \".\", extra: () }, Eof)))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new("4.E3"))),
            "Err(Error((LocatedSpanEx { offset: 1, line: 1, fragment: \".E3\", extra: () }, Eof)))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(Span::new(".2e-7"))),
            "Err(Error((LocatedSpanEx { offset: 0, line: 1, fragment: \".2e-7\", extra: () }, Digit)))"
        );
        assert_eq!(
            format!(
                "{:?}",
                all_consuming(unbased_unsized_literal)(Span::new("'0"))
            ),
            "Ok((LocatedSpanEx { offset: 2, line: 1, fragment: \"\", extra: () }, UnbasedUnsizedLiteral { nodes: (Symbol { nodes: (LocatedSpanEx { offset: 0, line: 1, fragment: \"\\\'0\", extra: () }, []) },) }))"
        );
    }
}
