#[derive(Debug)]
pub enum Number<'a> {
    IntegralNumber(IntegralNumber<'a>),
    RealNumber(RealNumber),
}

#[derive(Debug)]
pub enum IntegralNumber<'a> {
    DecimalNumber(DecimalNumber<'a>),
    OctalNumber(OctalNumber<'a>),
    BinaryNumber(BinaryNumber<'a>),
    HexNumber(HexNumber<'a>),
    UnsignedNumber(Vec<&'a str>),
}

#[derive(Debug)]
pub struct DecimalNumber<'a> {
    pub size: Option<Vec<&'a str>>,
    pub decimal_base: &'a str,
    pub decimal_number: Vec<&'a str>,
}

#[derive(Debug)]
pub struct BinaryNumber<'a> {
    pub size: Option<Vec<&'a str>>,
    pub binary_base: &'a str,
    pub binary_value: Vec<&'a str>,
}

#[derive(Debug)]
pub struct OctalNumber<'a> {
    pub size: Option<Vec<&'a str>>,
    pub octal_base: &'a str,
    pub octal_value: Vec<&'a str>,
}

#[derive(Debug)]
pub struct HexNumber<'a> {
    pub size: Option<Vec<&'a str>>,
    pub hex_base: &'a str,
    pub hex_value: Vec<&'a str>,
}

#[derive(Debug)]
pub enum RealNumber {
    FixedPointNumber,
    FloatingPointNumber,
}
