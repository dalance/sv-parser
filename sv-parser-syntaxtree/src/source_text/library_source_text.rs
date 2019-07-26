use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct LibraryText {
    pub nodes: (Vec<LibraryDescription>,),
}

#[derive(Clone, Debug, Node)]
pub enum LibraryDescription {
    LibraryDeclaration(Box<LibraryDeclaration>),
    IncludeStatement(Box<IncludeStatement>),
    ConfigDeclaration(Box<ConfigDeclaration>),
    Null(Box<Symbol>),
}

#[derive(Clone, Debug, Node)]
pub struct LibraryDeclaration {
    pub nodes: (
        Keyword,
        LibraryIdentifier,
        List<Symbol, FilePathSpec>,
        Option<(Keyword, List<Symbol, FilePathSpec>)>,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct IncludeStatement {
    pub nodes: (Keyword, FilePathSpec, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct FilePathSpec {
    pub nodes: (StringLiteral,),
}
