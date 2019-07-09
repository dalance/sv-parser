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
    pub nodes: (&'a str,),
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
    pub nodes: (&'a str,),
}

#[derive(Debug)]
pub struct BinaryValue<'a> {
    pub nodes: (&'a str,),
}

#[derive(Debug)]
pub struct OctalValue<'a> {
    pub nodes: (&'a str,),
}

#[derive(Debug)]
pub struct HexValue<'a> {
    pub nodes: (&'a str,),
}

#[derive(Debug)]
pub struct DecimalBase<'a> {
    pub nodes: (&'a str,),
}

#[derive(Debug)]
pub struct BinaryBase<'a> {
    pub nodes: (&'a str,),
}

#[derive(Debug)]
pub struct OctalBase<'a> {
    pub nodes: (&'a str,),
}

#[derive(Debug)]
pub struct HexBase<'a> {
    pub nodes: (&'a str,),
}

#[derive(Debug)]
pub struct XNumber<'a> {
    pub nodes: (&'a str,),
}

#[derive(Debug)]
pub struct ZNumber<'a> {
    pub nodes: (&'a str,),
}

#[derive(Debug)]
pub struct UnbasedUnsizedLiteral<'a> {
    pub nodes: (Symbol<'a>,),
}

// -----------------------------------------------------------------------------

pub fn number(s: &str) -> IResult<&str, Number> {
    alt((
        map(real_number, |x| Number::RealNumber(x)),
        map(integral_number, |x| Number::IntegralNumber(x)),
    ))(s)
}

pub fn integral_number(s: &str) -> IResult<&str, IntegralNumber> {
    alt((
        map(octal_number, |x| IntegralNumber::OctalNumber(x)),
        map(binary_number, |x| IntegralNumber::BinaryNumber(x)),
        map(hex_number, |x| IntegralNumber::HexNumber(x)),
        map(decimal_number, |x| IntegralNumber::DecimalNumber(x)),
    ))(s)
}

pub fn decimal_number(s: &str) -> IResult<&str, DecimalNumber> {
    alt((
        map(unsigned_number, |x| DecimalNumber::UnsignedNumber(x)),
        decimal_number_base_unsigned,
        decimal_number_base_x_number,
        decimal_number_base_z_number,
    ))(s)
}

pub fn decimal_number_base_unsigned(s: &str) -> IResult<&str, DecimalNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = decimal_base(s)?;
    let (s, c) = unsigned_number(s)?;
    Ok((
        s,
        DecimalNumber::BaseUnsigned(DecimalNumberBaseUnsigned { nodes: (a, b, c) }),
    ))
}

pub fn decimal_number_base_x_number(s: &str) -> IResult<&str, DecimalNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = decimal_base(s)?;
    let (s, c) = x_number(s)?;
    Ok((
        s,
        DecimalNumber::BaseXNumber(DecimalNumberBaseXNumber { nodes: (a, b, c) }),
    ))
}

pub fn decimal_number_base_z_number(s: &str) -> IResult<&str, DecimalNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = decimal_base(s)?;
    let (s, c) = z_number(s)?;
    Ok((
        s,
        DecimalNumber::BaseZNumber(DecimalNumberBaseZNumber { nodes: (a, b, c) }),
    ))
}

pub fn binary_number(s: &str) -> IResult<&str, BinaryNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = binary_base(s)?;
    let (s, c) = binary_value(s)?;
    Ok((s, BinaryNumber { nodes: (a, b, c) }))
}

pub fn octal_number(s: &str) -> IResult<&str, OctalNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = octal_base(s)?;
    let (s, c) = octal_value(s)?;
    Ok((s, OctalNumber { nodes: (a, b, c) }))
}

pub fn hex_number(s: &str) -> IResult<&str, HexNumber> {
    let (s, a) = opt(size)(s)?;
    let (s, b) = hex_base(s)?;
    let (s, c) = hex_value(s)?;
    Ok((s, HexNumber { nodes: (a, b, c) }))
}

pub fn sign(s: &str) -> IResult<&str, Sign> {
    alt((
        map(symbol("+"), |x| Sign::Plus(x)),
        map(symbol("-"), |x| Sign::Minus(x)),
    ))(s)
}

pub fn size(s: &str) -> IResult<&str, Size> {
    let (s, a) = non_zero_unsigned_number(s)?;
    Ok((s, Size { nodes: (a,) }))
}

pub fn non_zero_unsigned_number(s: &str) -> IResult<&str, NonZeroUnsignedNumber> {
    let (s, a) = ws(non_zero_unsigned_number_impl)(s)?;
    Ok((s, NonZeroUnsignedNumber { nodes: (a,) }))
}

pub fn non_zero_unsigned_number_impl(s: &str) -> IResult<&str, &str> {
    let (s, a) = is_a("123456789")(s)?;
    fold_many0(alt((tag("_"), digit1)), a, |acc, item| {
        str_concat::concat(acc, item).unwrap()
    })(s)
}

pub fn real_number(s: &str) -> IResult<&str, RealNumber> {
    alt((
        real_number_floating,
        map(fixed_point_number, |x| RealNumber::FixedPointNumber(x)),
    ))(s)
}

pub fn real_number_floating(s: &str) -> IResult<&str, RealNumber> {
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

pub fn fixed_point_number(s: &str) -> IResult<&str, FixedPointNumber> {
    let (s, a) = unsigned_number(s)?;
    let (s, b) = map(tag("."), |x| Symbol { nodes: (x,) })(s)?;;
    let (s, c) = unsigned_number(s)?;
    Ok((s, FixedPointNumber { nodes: (a, b, c) }))
}

pub fn exp(s: &str) -> IResult<&str, Exp> {
    let (s, a) = alt((symbol("e"), symbol("E")))(s)?;
    Ok((s, Exp { nodes: (a,) }))
}

pub fn unsigned_number(s: &str) -> IResult<&str, UnsignedNumber> {
    let (s, a) = ws(unsigned_number_impl)(s)?;
    Ok((s, UnsignedNumber { nodes: (a,) }))
}

pub fn unsigned_number_impl(s: &str) -> IResult<&str, &str> {
    let (s, a) = digit1(s)?;
    fold_many0(alt((tag("_"), digit1)), a, |acc, item| {
        str_concat::concat(acc, item).unwrap()
    })(s)
}

pub fn binary_value(s: &str) -> IResult<&str, BinaryValue> {
    let (s, a) = ws(binary_value_impl)(s)?;
    Ok((s, BinaryValue { nodes: (a,) }))
}

pub fn binary_value_impl(s: &str) -> IResult<&str, &str> {
    let (s, a) = is_a("01xXzZ?")(s)?;
    fold_many0(alt((tag("_"), is_a("01xXzZ?"))), a, |acc, item| {
        str_concat::concat(acc, item).unwrap()
    })(s)
}

pub fn octal_value(s: &str) -> IResult<&str, OctalValue> {
    let (s, a) = ws(octal_value_impl)(s)?;
    Ok((s, OctalValue { nodes: (a,) }))
}

pub fn octal_value_impl(s: &str) -> IResult<&str, &str> {
    let (s, a) = is_a("01234567xXzZ?")(s)?;
    fold_many0(alt((tag("_"), is_a("01234567xXzZ?"))), a, |acc, item| {
        str_concat::concat(acc, item).unwrap()
    })(s)
}

pub fn hex_value(s: &str) -> IResult<&str, HexValue> {
    let (s, a) = ws(hex_value_impl)(s)?;
    Ok((s, HexValue { nodes: (a,) }))
}

pub fn hex_value_impl(s: &str) -> IResult<&str, &str> {
    let (s, a) = is_a("0123456789abcdefABCDEFxXzZ?")(s)?;
    fold_many0(
        alt((tag("_"), is_a("0123456789abcdefABCDEFxXzZ?"))),
        a,
        |acc, item| str_concat::concat(acc, item).unwrap(),
    )(s)
}

pub fn decimal_base(s: &str) -> IResult<&str, DecimalBase> {
    let (s, a) = ws(decimal_base_impl)(s)?;
    Ok((s, DecimalBase { nodes: (a,) }))
}

pub fn decimal_base_impl(s: &str) -> IResult<&str, &str> {
    alt((tag_no_case("'d"), tag_no_case("'sd")))(s)
}

pub fn binary_base(s: &str) -> IResult<&str, BinaryBase> {
    let (s, a) = ws(binary_base_impl)(s)?;
    Ok((s, BinaryBase { nodes: (a,) }))
}

pub fn binary_base_impl(s: &str) -> IResult<&str, &str> {
    alt((tag_no_case("'b"), tag_no_case("'sb")))(s)
}

pub fn octal_base(s: &str) -> IResult<&str, OctalBase> {
    let (s, a) = ws(octal_base_impl)(s)?;
    Ok((s, OctalBase { nodes: (a,) }))
}

pub fn octal_base_impl(s: &str) -> IResult<&str, &str> {
    alt((tag_no_case("'o"), tag_no_case("'so")))(s)
}

pub fn hex_base(s: &str) -> IResult<&str, HexBase> {
    let (s, a) = ws(hex_base_impl)(s)?;
    Ok((s, HexBase { nodes: (a,) }))
}

pub fn hex_base_impl(s: &str) -> IResult<&str, &str> {
    alt((tag_no_case("'h"), tag_no_case("'sh")))(s)
}

pub fn x_number(s: &str) -> IResult<&str, XNumber> {
    let (s, a) = ws(x_number_impl)(s)?;
    Ok((s, XNumber { nodes: (a,) }))
}

pub fn x_number_impl(s: &str) -> IResult<&str, &str> {
    let (s, a) = tag_no_case("x")(s)?;
    fold_many0(alt((tag("_"), is_a("_"))), a, |acc, item| {
        str_concat::concat(acc, item).unwrap()
    })(s)
}

pub fn z_number(s: &str) -> IResult<&str, ZNumber> {
    let (s, a) = ws(z_number_impl)(s)?;
    Ok((s, ZNumber { nodes: (a,) }))
}

pub fn z_number_impl(s: &str) -> IResult<&str, &str> {
    let (s, a) = alt((tag_no_case("z"), tag("?")))(s)?;
    fold_many0(alt((tag("_"), is_a("_"))), a, |acc, item| {
        str_concat::concat(acc, item).unwrap()
    })(s)
}

pub fn unbased_unsized_literal(s: &str) -> IResult<&str, UnbasedUnsizedLiteral> {
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
            format!("{:?}", all_consuming(number)("659")),
            "Ok((\"\", IntegralNumber(UnsignedNumber(\"659\"))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("'h 837FF")),
            "Ok((\"\", IntegralNumber(HexNumber(HexNumber { size: None, hex_base: \"\\\'h\", hex_value: \"837FF\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("'o7460")),
            "Ok((\"\", IntegralNumber(OctalNumber(OctalNumber { size: None, octal_base: \"\\\'o\", octal_value: \"7460\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("4af")),
            "Err(Error((\"af\", Eof)))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("4'b1001")),
            "Ok((\"\", IntegralNumber(BinaryNumber(BinaryNumber { size: Some(\"4\"), binary_base: \"\\\'b\", binary_value: \"1001\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("5 'D 3")),
            "Ok((\"\", IntegralNumber(DecimalNumber(DecimalNumber { size: Some(\"5\"), decimal_base: \"\\\'D\", decimal_value: \"3\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("3'b01x")),
            "Ok((\"\", IntegralNumber(BinaryNumber(BinaryNumber { size: Some(\"3\"), binary_base: \"\\\'b\", binary_value: \"01x\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("12'hx")),
            "Ok((\"\", IntegralNumber(HexNumber(HexNumber { size: Some(\"12\"), hex_base: \"\\\'h\", hex_value: \"x\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("16'hz")),
            "Ok((\"\", IntegralNumber(HexNumber(HexNumber { size: Some(\"16\"), hex_base: \"\\\'h\", hex_value: \"z\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("8 'd -6")),
            "Err(Error((\"\\\'d -6\", Eof)))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("4 'shf")),
            "Ok((\"\", IntegralNumber(HexNumber(HexNumber { size: Some(\"4\"), hex_base: \"\\\'sh\", hex_value: \"f\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("16'sd?")),
            "Ok((\"\", IntegralNumber(DecimalNumber(DecimalNumber { size: Some(\"16\"), decimal_base: \"\\\'sd\", decimal_value: \"?\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("27_195_000")),
            "Ok((\"\", IntegralNumber(UnsignedNumber(\"27_195_000\"))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("16'b0011_0101_0001_1111")),
            "Ok((\"\", IntegralNumber(BinaryNumber(BinaryNumber { size: Some(\"16\"), binary_base: \"\\\'b\", binary_value: \"0011_0101_0001_1111\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("32 'h 12ab_f001")),
            "Ok((\"\", IntegralNumber(HexNumber(HexNumber { size: Some(\"32\"), hex_base: \"\\\'h\", hex_value: \"12ab_f001\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("1.2")),
            "Ok((\"\", RealNumber(FixedPointNumber(FixedPointNumber { integer_value: \"1\", fraction_value: \"2\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("0.1")),
            "Ok((\"\", RealNumber(FixedPointNumber(FixedPointNumber { integer_value: \"0\", fraction_value: \"1\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("2394.26331")),
            "Ok((\"\", RealNumber(FixedPointNumber(FixedPointNumber { integer_value: \"2394\", fraction_value: \"26331\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("1.2E12")),
            "Ok((\"\", RealNumber(FloatingPointNumber(FloatingPointNumber { integer_value: \"1\", fraction_value: Some(\"2\"), exponent: \"E\", sign: None, exponent_value: \"12\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("1.30e-2")),
            "Ok((\"\", RealNumber(FloatingPointNumber(FloatingPointNumber { integer_value: \"1\", fraction_value: Some(\"30\"), exponent: \"e\", sign: Some(\"-\"), exponent_value: \"2\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("0.1e-0")),
            "Ok((\"\", RealNumber(FloatingPointNumber(FloatingPointNumber { integer_value: \"0\", fraction_value: Some(\"1\"), exponent: \"e\", sign: Some(\"-\"), exponent_value: \"0\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("23E10")),
            "Ok((\"\", RealNumber(FloatingPointNumber(FloatingPointNumber { integer_value: \"23\", fraction_value: None, exponent: \"E\", sign: None, exponent_value: \"10\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("29E-2")),
            "Ok((\"\", RealNumber(FloatingPointNumber(FloatingPointNumber { integer_value: \"29\", fraction_value: None, exponent: \"E\", sign: Some(\"-\"), exponent_value: \"2\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("236.123_763_e-12")),
            "Ok((\"\", RealNumber(FloatingPointNumber(FloatingPointNumber { integer_value: \"236\", fraction_value: Some(\"123_763_\"), exponent: \"e\", sign: Some(\"-\"), exponent_value: \"12\" }))))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(".12")),
            "Err(Error((\".12\", Digit)))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("9.")),
            "Err(Error((\".\", Eof)))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)("4.E3")),
            "Err(Error((\".E3\", Eof)))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(number)(".2e-7")),
            "Err(Error((\".2e-7\", Digit)))"
        );
        assert_eq!(
            format!("{:?}", all_consuming(unbased_unsized_literal)("'0")),
            "Ok((\"\", \"\\\'0\"))"
        );
    }
}
