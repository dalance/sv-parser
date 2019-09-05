use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub struct CheckerInstantiation {
    pub nodes: (
        PsCheckerIdentifier,
        NameOfInstance,
        Paren<Option<ListOfCheckerPortConnections>>,
        Symbol,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ListOfCheckerPortConnections {
    Ordered(Box<ListOfCheckerPortConnectionsOrdered>),
    Named(Box<ListOfCheckerPortConnectionsNamed>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ListOfCheckerPortConnectionsOrdered {
    pub nodes: (List<Symbol, OrderedCheckerPortConnection>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ListOfCheckerPortConnectionsNamed {
    pub nodes: (List<Symbol, NamedCheckerPortConnection>,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct OrderedCheckerPortConnection {
    pub nodes: (Vec<AttributeInstance>, Option<PropertyActualArg>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum NamedCheckerPortConnection {
    Identifier(Box<NamedCheckerPortConnectionIdentifier>),
    Asterisk(Box<NamedCheckerPortConnectionAsterisk>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct NamedCheckerPortConnectionIdentifier {
    pub nodes: (
        Vec<AttributeInstance>,
        Symbol,
        FormalPortIdentifier,
        Option<Paren<Option<PropertyActualArg>>>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct NamedCheckerPortConnectionAsterisk {
    pub nodes: (Vec<AttributeInstance>, Symbol),
}
