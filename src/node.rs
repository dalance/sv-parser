use crate::parser::*;
use node_derive::AnyNode;

pub trait Node<'a> {
    fn test(&'a self) -> String;
    fn next(&'a self) -> Vec<AnyNode<'a>>;
}

impl<'a> Node<'a> for Span<'a> {
    fn test(&'a self) -> String {
        String::from("")
    }
    fn next(&'a self) -> Vec<AnyNode<'a>> {
        vec![]
    }
}

impl<'a> From<&'a Span<'a>> for AnyNode<'a> {
    fn from(x: &'a Span<'a>) -> Self {
        AnyNode::Span(x)
    }
}

#[derive(Debug, Clone, AnyNode)]
pub enum AnyNode<'a> {
    Span(&'a Span<'a>),
    Symbol(&'a Symbol<'a>),
    WhiteSpace(&'a WhiteSpace<'a>),
    Comment(&'a Comment<'a>),
    Number(&'a Number<'a>),
    IntegralNumber(&'a IntegralNumber<'a>),
    DecimalNumber(&'a DecimalNumber<'a>),
    DecimalNumberBaseUnsigned(&'a DecimalNumberBaseUnsigned<'a>),
    DecimalNumberBaseXNumber(&'a DecimalNumberBaseXNumber<'a>),
    DecimalNumberBaseZNumber(&'a DecimalNumberBaseZNumber<'a>),
    BinaryNumber(&'a BinaryNumber<'a>),
    OctalNumber(&'a OctalNumber<'a>),
    HexNumber(&'a HexNumber<'a>),
    Sign(&'a Sign<'a>),
    Size(&'a Size<'a>),
    NonZeroUnsignedNumber(&'a NonZeroUnsignedNumber<'a>),
    RealNumber(&'a RealNumber<'a>),
    RealNumberFloating(&'a RealNumberFloating<'a>),
    FixedPointNumber(&'a FixedPointNumber<'a>),
    Exp(&'a Exp<'a>),
    UnsignedNumber(&'a UnsignedNumber<'a>),
    BinaryValue(&'a BinaryValue<'a>),
    OctalValue(&'a OctalValue<'a>),
    HexValue(&'a HexValue<'a>),
    DecimalBase(&'a DecimalBase<'a>),
    BinaryBase(&'a BinaryBase<'a>),
    OctalBase(&'a OctalBase<'a>),
    HexBase(&'a HexBase<'a>),
    XNumber(&'a XNumber<'a>),
    ZNumber(&'a ZNumber<'a>),
    UnbasedUnsizedLiteral(&'a UnbasedUnsizedLiteral<'a>),
}

pub struct Iter<'a> {
    pub(crate) next: Vec<AnyNode<'a>>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = AnyNode<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let ret = self.next.pop();
        if let Some(x) = ret.clone() {
            let mut x = x.next();
            self.next.append(&mut x);
        }
        ret
    }
}
