use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum DriveStrength {
    Strength01(Box<DriveStrength01>),
    Strength10(Box<DriveStrength10>),
    Strength0z(Box<DriveStrength0z>),
    Strength1z(Box<DriveStrength1z>),
    Strengthz0(Box<DriveStrengthz0>),
    Strengthz1(Box<DriveStrengthz1>),
}

#[derive(Clone, Debug, Node)]
pub struct DriveStrength01 {
    pub nodes: (Paren<(Strength0, Symbol, Strength1)>,),
}

#[derive(Clone, Debug, Node)]
pub struct DriveStrength10 {
    pub nodes: (Paren<(Strength1, Symbol, Strength0)>,),
}

#[derive(Clone, Debug, Node)]
pub struct DriveStrength0z {
    pub nodes: (Paren<(Strength0, Symbol, Keyword)>,),
}

#[derive(Clone, Debug, Node)]
pub struct DriveStrength1z {
    pub nodes: (Paren<(Strength1, Symbol, Keyword)>,),
}

#[derive(Clone, Debug, Node)]
pub struct DriveStrengthz1 {
    pub nodes: (Paren<(Keyword, Symbol, Strength1)>,),
}

#[derive(Clone, Debug, Node)]
pub struct DriveStrengthz0 {
    pub nodes: (Paren<(Keyword, Symbol, Strength0)>,),
}

#[derive(Clone, Debug, Node)]
pub enum Strength0 {
    Supply0(Box<Keyword>),
    Strong0(Box<Keyword>),
    Pull0(Box<Keyword>),
    Weak0(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub enum Strength1 {
    Supply1(Box<Keyword>),
    Strong1(Box<Keyword>),
    Pull1(Box<Keyword>),
    Weak1(Box<Keyword>),
}

#[derive(Clone, Debug, Node)]
pub enum ChargeStrength {
    Small(Box<ChargeStrengthSmall>),
    Medium(Box<ChargeStrengthMedium>),
    Large(Box<ChargeStrengthLarge>),
}

#[derive(Clone, Debug, Node)]
pub struct ChargeStrengthSmall {
    pub nodes: (Paren<Keyword>,),
}

#[derive(Clone, Debug, Node)]
pub struct ChargeStrengthMedium {
    pub nodes: (Paren<Keyword>,),
}

#[derive(Clone, Debug, Node)]
pub struct ChargeStrengthLarge {
    pub nodes: (Paren<Keyword>,),
}
