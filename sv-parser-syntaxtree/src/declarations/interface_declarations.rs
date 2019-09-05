use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ModportDeclaration {
    pub nodes: (Keyword, List<Symbol, ModportItem>, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ModportItem {
    pub nodes: (
        ModportIdentifier,
        Paren<List<Symbol, ModportPortsDeclaraton>>,
    ),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ModportPortsDeclaraton {
    Simple(Box<ModportPortsDeclaratonSimple>),
    Tf(Box<ModportPortsDeclaratonTf>),
    Clocking(Box<ModportPortsDeclaratonClocking>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ModportPortsDeclaratonSimple {
    pub nodes: (Vec<AttributeInstance>, ModportSimplePortsDeclaration),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ModportPortsDeclaratonTf {
    pub nodes: (Vec<AttributeInstance>, ModportTfPortsDeclaration),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ModportPortsDeclaratonClocking {
    pub nodes: (Vec<AttributeInstance>, ModportClockingDeclaration),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ModportClockingDeclaration {
    pub nodes: (Keyword, ClockingIdentifier),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ModportSimplePortsDeclaration {
    pub nodes: (PortDirection, List<Symbol, ModportSimplePort>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ModportSimplePort {
    Ordered(Box<ModportSimplePortOrdered>),
    Named(Box<ModportSimplePortNamed>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ModportSimplePortOrdered {
    pub nodes: (PortIdentifier,),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ModportSimplePortNamed {
    pub nodes: (Symbol, PortIdentifier, Paren<Option<Expression>>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ModportTfPortsDeclaration {
    pub nodes: (ImportExport, List<Symbol, ModportTfPort>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ModportTfPort {
    MethodPrototype(Box<MethodPrototype>),
    TfIdentifier(Box<TfIdentifier>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ImportExport {
    Import(Box<Keyword>),
    Export(Box<Keyword>),
}
