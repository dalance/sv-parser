use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct Symbol {
    pub nodes: (Locate, Vec<WhiteSpace>),
}

#[derive(Clone, Debug, Node)]
pub struct Keyword {
    pub nodes: (Locate, Vec<WhiteSpace>),
}

#[derive(Clone, Debug, Node)]
pub enum WhiteSpace {
    Space(Box<Locate>),
    Comment(Box<Comment>),
}

#[derive(Clone, Debug)]
pub struct Paren<T> {
    pub nodes: (Symbol, T, Symbol),
}

#[derive(Clone, Debug)]
pub struct Brace<T> {
    pub nodes: (Symbol, T, Symbol),
}

#[derive(Clone, Debug)]
pub struct Bracket<T> {
    pub nodes: (Symbol, T, Symbol),
}

#[derive(Clone, Debug)]
pub struct ApostropheBrace<T> {
    pub nodes: (Symbol, T, Symbol),
}

#[derive(Clone, Debug)]
pub struct List<T, U> {
    pub nodes: (U, Vec<(T, U)>),
}
