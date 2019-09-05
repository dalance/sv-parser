use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Node)]
pub enum InterfaceOrGenerateItem {
    Module(Box<InterfaceOrGenerateItemModule>),
    Extern(Box<InterfaceOrGenerateItemExtern>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct InterfaceOrGenerateItemModule {
    pub nodes: (Vec<AttributeInstance>, ModuleCommonItem),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct InterfaceOrGenerateItemExtern {
    pub nodes: (Vec<AttributeInstance>, ExternTfDeclaration),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum ExternTfDeclaration {
    Method(Box<ExternTfDeclarationMethod>),
    Task(Box<ExternTfDeclarationTask>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ExternTfDeclarationMethod {
    pub nodes: (Keyword, MethodPrototype, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub struct ExternTfDeclarationTask {
    pub nodes: (Keyword, Keyword, TaskPrototype, Symbol),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum InterfaceItem {
    PortDeclaration(Box<(PortDeclaration, Symbol)>),
    NonPortInterfaceItem(Box<NonPortInterfaceItem>),
}

#[derive(Clone, Debug, PartialEq, Node)]
pub enum NonPortInterfaceItem {
    GenerateRegion(Box<GenerateRegion>),
    InterfaceOrGenerateItem(Box<InterfaceOrGenerateItem>),
    ProgramDeclaration(Box<ProgramDeclaration>),
    ModportDeclaration(Box<ModportDeclaration>),
    InterfaceDeclaration(Box<InterfaceDeclaration>),
    TimeunitsDeclaration(Box<TimeunitsDeclaration>),
}
