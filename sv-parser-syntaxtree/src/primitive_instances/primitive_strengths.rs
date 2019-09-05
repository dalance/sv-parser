use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub enum PulldownStrength {
    Strength01(Box<PulldownStrength01>),
    Strength10(Box<PulldownStrength10>),
    Strength0(Box<PulldownStrength0>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PulldownStrength01 {
    pub nodes: (Paren<(Strength0, Symbol, Strength1)>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PulldownStrength10 {
    pub nodes: (Paren<(Strength1, Symbol, Strength0)>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PulldownStrength0 {
    pub nodes: (Paren<Strength0>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum PullupStrength {
    Strength01(Box<PullupStrength01>),
    Strength10(Box<PullupStrength10>),
    Strength1(Box<PullupStrength1>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PullupStrength01 {
    pub nodes: (Paren<(Strength0, Symbol, Strength1)>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PullupStrength10 {
    pub nodes: (Paren<(Strength1, Symbol, Strength0)>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct PullupStrength1 {
    pub nodes: (Paren<Strength1>,),
}
