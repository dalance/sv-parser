use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum DriveStrength<'a> {
    Strength01(Strength0<'a>, Strength1<'a>),
    Strength10(Strength1<'a>, Strength0<'a>),
    Strength0z(Strength0<'a>),
    Strength1z(Strength1<'a>),
    Strengthz0(Strength0<'a>),
    Strengthz1(Strength1<'a>),
}

#[derive(Debug)]
pub enum Strength0<'a> {
    Supply0(Symbol<'a>),
    Strong0(Symbol<'a>),
    Pull0(Symbol<'a>),
    Weak0(Symbol<'a>),
}

#[derive(Debug)]
pub enum Strength1<'a> {
    Supply1(Symbol<'a>),
    Strong1(Symbol<'a>),
    Pull1(Symbol<'a>),
    Weak1(Symbol<'a>),
}

#[derive(Debug)]
pub enum ChargeStrength<'a> {
    Small(Symbol<'a>),
    Medium(Symbol<'a>),
    Large(Symbol<'a>),
}

// -----------------------------------------------------------------------------

pub fn drive_strength(s: Span) -> IResult<Span, DriveStrength> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn strength0(s: Span) -> IResult<Span, Strength0> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn strength1(s: Span) -> IResult<Span, Strength1> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn charge_strength(s: Span) -> IResult<Span, ChargeStrength> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}
