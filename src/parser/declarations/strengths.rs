//use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum DriveStrength {
    Strength01(Strength0, Strength1),
    Strength10(Strength1, Strength0),
    Strength0z(Strength0),
    Strength1z(Strength1),
    Strengthz0(Strength0),
    Strengthz1(Strength1),
}

#[derive(Debug)]
pub enum Strength0 {
    Supply0,
    Strong0,
    Pull0,
    Weak0,
}

#[derive(Debug)]
pub enum Strength1 {
    Supply1,
    Strong1,
    Pull1,
    Weak1,
}

#[derive(Debug)]
pub enum ChargeStrength {
    Small,
    Medium,
    Large,
}

// -----------------------------------------------------------------------------

pub fn drive_strength(s: &str) -> IResult<&str, DriveStrength> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn strength0(s: &str) -> IResult<&str, Strength0> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn strength1(s: &str) -> IResult<&str, Strength1> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn charge_strength(s: &str) -> IResult<&str, ChargeStrength> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}
