use crate::*;

// -----------------------------------------------------------------------------

#[derive(Clone, Debug, Node)]
pub enum ElaborationSystemTask {
    TaskFatal(Box<ElaborationSystemTaskFatal>),
    TaskError(Box<ElaborationSystemTaskError>),
    TaskWarning(Box<ElaborationSystemTaskWarning>),
    TaskInfo(Box<ElaborationSystemTaskInfo>),
}

#[derive(Clone, Debug, Node)]
pub struct ElaborationSystemTaskFatal {
    pub nodes: (
        Keyword,
        Option<Paren<(FinishNumber, Option<(Symbol, ListOfArguments)>)>>,
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct ElaborationSystemTaskError {
    pub nodes: (Keyword, Option<Paren<Option<ListOfArguments>>>, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct ElaborationSystemTaskWarning {
    pub nodes: (Keyword, Option<Paren<Option<ListOfArguments>>>, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct ElaborationSystemTaskInfo {
    pub nodes: (Keyword, Option<Paren<Option<ListOfArguments>>>, Symbol),
}

#[derive(Clone, Debug, Node)]
pub enum FinishNumber {
    Zero(Box<Symbol>),
    One(Box<Symbol>),
    Two(Box<Symbol>),
}

#[derive(Clone, Debug, Node)]
pub enum ModuleCommonItem {
    ModuleOrGenerateItemDeclaration(Box<ModuleOrGenerateItemDeclaration>),
    InterfaceInstantiation(Box<InterfaceInstantiation>),
    ProgramInstantiation(Box<ProgramInstantiation>),
    AssertionItem(Box<AssertionItem>),
    BindDirective(Box<BindDirective>),
    ContinuousAssign(Box<ContinuousAssign>),
    NetAlias(Box<NetAlias>),
    InitialConstruct(Box<InitialConstruct>),
    FinalConstruct(Box<FinalConstruct>),
    AlwaysConstruct(Box<AlwaysConstruct>),
    LoopGenerateConstruct(Box<LoopGenerateConstruct>),
    ConditionalGenerateConstruct(Box<ConditionalGenerateConstruct>),
    ElaborationSystemTask(Box<ElaborationSystemTask>),
}

#[derive(Clone, Debug, Node)]
pub enum ModuleItem {
    PortDeclaration(Box<(PortDeclaration, Symbol)>),
    NonPortModuleItem(Box<NonPortModuleItem>),
}

#[derive(Clone, Debug, Node)]
pub enum ModuleOrGenerateItem {
    Parameter(Box<ModuleOrGenerateItemParameter>),
    Gate(Box<ModuleOrGenerateItemGate>),
    Udp(Box<ModuleOrGenerateItemUdp>),
    Module(Box<ModuleOrGenerateItemModule>),
    ModuleItem(Box<ModuleOrGenerateItemModuleItem>),
}

#[derive(Clone, Debug, Node)]
pub struct ModuleOrGenerateItemParameter {
    pub nodes: (Vec<AttributeInstance>, ParameterOverride),
}

#[derive(Clone, Debug, Node)]
pub struct ModuleOrGenerateItemGate {
    pub nodes: (Vec<AttributeInstance>, GateInstantiation),
}

#[derive(Clone, Debug, Node)]
pub struct ModuleOrGenerateItemUdp {
    pub nodes: (Vec<AttributeInstance>, UdpInstantiation),
}

#[derive(Clone, Debug, Node)]
pub struct ModuleOrGenerateItemModule {
    pub nodes: (Vec<AttributeInstance>, ModuleInstantiation),
}

#[derive(Clone, Debug, Node)]
pub struct ModuleOrGenerateItemModuleItem {
    pub nodes: (Vec<AttributeInstance>, ModuleCommonItem),
}

#[derive(Clone, Debug, Node)]
pub enum ModuleOrGenerateItemDeclaration {
    PackageOrGenerateItemDeclaration(Box<PackageOrGenerateItemDeclaration>),
    GenvarDeclaration(Box<GenvarDeclaration>),
    ClockingDeclaration(Box<ClockingDeclaration>),
    Clocking(Box<ModuleOrGenerateItemDeclarationClocking>),
    Disable(Box<ModuleOrGenerateItemDeclarationDisable>),
}

#[derive(Clone, Debug, Node)]
pub struct ModuleOrGenerateItemDeclarationClocking {
    pub nodes: (Keyword, Keyword, ClockingIdentifier, Symbol),
}

#[derive(Clone, Debug, Node)]
pub struct ModuleOrGenerateItemDeclarationDisable {
    pub nodes: (Keyword, Keyword, Keyword, ExpressionOrDist, Symbol),
}

#[derive(Clone, Debug, Node)]
pub enum NonPortModuleItem {
    GenerateRegion(Box<GenerateRegion>),
    ModuleOrGenerateItem(Box<ModuleOrGenerateItem>),
    SpecifyBlock(Box<SpecifyBlock>),
    Specparam(Box<NonPortModuleItemSpecparam>),
    ProgramDeclaration(Box<ProgramDeclaration>),
    ModuleDeclaration(Box<ModuleDeclaration>),
    InterfaceDeclaration(Box<InterfaceDeclaration>),
    TimeunitsDeclaration(Box<TimeunitsDeclaration>),
}

#[derive(Clone, Debug, Node)]
pub struct NonPortModuleItemSpecparam {
    pub nodes: (Vec<AttributeInstance>, SpecparamDeclaration),
}

#[derive(Clone, Debug, Node)]
pub struct ParameterOverride {
    pub nodes: (Keyword, ListOfDefparamAssignments, Symbol),
}

#[derive(Clone, Debug, Node)]
pub enum BindDirective {
    Scope(Box<BindDirectiveScope>),
    Instance(Box<BindDirectiveInstance>),
}

#[derive(Clone, Debug, Node)]
pub struct BindDirectiveScope {
    pub nodes: (
        Keyword,
        BindTargetScope,
        Option<(Symbol, BindTargetInstanceList)>,
        BindInstantiation,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct BindDirectiveInstance {
    pub nodes: (Keyword, BindTargetInstance, BindInstantiation),
}

#[derive(Clone, Debug, Node)]
pub enum BindTargetScope {
    ModuleIdentifier(Box<ModuleIdentifier>),
    InterfaceIdentifier(Box<InterfaceIdentifier>),
}

#[derive(Clone, Debug, Node)]
pub struct BindTargetInstance {
    pub nodes: (HierarchicalIdentifier, ConstantBitSelect),
}

#[derive(Clone, Debug, Node)]
pub struct BindTargetInstanceList {
    pub nodes: (List<Symbol, BindTargetInstance>,),
}

#[derive(Clone, Debug, Node)]
pub enum BindInstantiation {
    ProgramInstantiation(Box<ProgramInstantiation>),
    ModuleInstantiation(Box<ModuleInstantiation>),
    InterfaceInstantiation(Box<InterfaceInstantiation>),
    CheckerInstantiation(Box<CheckerInstantiation>),
}
