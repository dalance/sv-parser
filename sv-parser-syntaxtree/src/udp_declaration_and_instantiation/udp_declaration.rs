use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub struct UdpNonansiDeclaration {
    pub nodes: (
        Vec<AttributeInstance>,
        Keyword,
        UdpIdentifier,
        Paren<UdpPortList>,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct UdpAnsiDeclaration {
    pub nodes: (
        Vec<AttributeInstance>,
        Keyword,
        UdpIdentifier,
        Paren<UdpDeclarationPortList>,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub enum UdpDeclaration {
    Nonansi(Box<UdpDeclarationNonansi>),
    Ansi(Box<UdpDeclarationAnsi>),
    ExternNonansi(Box<UdpDeclarationExternNonansi>),
    ExternAnsi(Box<UdpDeclarationExternAnsi>),
    Wildcard(Box<UdpDeclarationWildcard>),
}

#[derive(Clone, Debug, Node)]
pub struct UdpDeclarationNonansi {
    pub nodes: (
        UdpNonansiDeclaration,
        UdpPortDeclaration,
        Vec<UdpPortDeclaration>,
        UdpBody,
        Keyword,
        Option<(Symbol, UdpIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct UdpDeclarationAnsi {
    pub nodes: (
        UdpAnsiDeclaration,
        UdpBody,
        Keyword,
        Option<(Symbol, UdpIdentifier)>,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct UdpDeclarationExternNonansi {
    pub nodes: (Keyword, UdpNonansiDeclaration),
}

#[derive(Clone, Debug, Node)]
pub struct UdpDeclarationExternAnsi {
    pub nodes: (Keyword, UdpAnsiDeclaration),
}

#[derive(Clone, Debug, Node)]
pub struct UdpDeclarationWildcard {
    pub nodes: (
        Vec<AttributeInstance>,
        Keyword,
        UdpIdentifier,
        Paren<Symbol>,
        Symbol,
        Vec<UdpPortDeclaration>,
        UdpBody,
        Keyword,
        Option<(Symbol, UdpIdentifier)>,
    ),
}
