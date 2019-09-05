use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub struct Symbol {
    pub nodes: (Locate, Vec<WhiteSpace>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct Keyword {
    pub nodes: (Locate, Vec<WhiteSpace>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum WhiteSpace {
    Space(Box<Locate>),
    Comment(Box<Comment>),
    CompilerDirective(Box<CompilerDirective>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Paren<T> {
    pub nodes: (Symbol, T, Symbol),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Brace<T> {
    pub nodes: (Symbol, T, Symbol),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Bracket<T> {
    pub nodes: (Symbol, T, Symbol),
}

#[derive(Clone, Debug, PartialEq)]
pub struct ApostropheBrace<T> {
    pub nodes: (Symbol, T, Symbol),
}

#[derive(Clone, Debug, PartialEq)]
pub struct List<T, U> {
    pub nodes: (U, Vec<(T, U)>),
}
