use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub enum ElaborationSystemTask<'a> {
    Fatal(ElaborationSystemTaskFatal<'a>),
    Error(ElaborationSystemTaskError<'a>),
    Warning(ElaborationSystemTaskWarning<'a>),
    Info(ElaborationSystemTaskInfo<'a>),
}

#[derive(Debug)]
pub struct ElaborationSystemTaskFatal<'a> {
    pub nodes: (Option<(FinishNumber, Option<ListOfArguments<'a>>)>,),
}

#[derive(Debug)]
pub struct ElaborationSystemTaskError<'a> {
    pub nodes: (Option<Option<ListOfArguments<'a>>>,),
}

#[derive(Debug)]
pub struct ElaborationSystemTaskWarning<'a> {
    pub nodes: (Option<Option<ListOfArguments<'a>>>,),
}

#[derive(Debug)]
pub struct ElaborationSystemTaskInfo<'a> {
    pub nodes: (Option<Option<ListOfArguments<'a>>>,),
}

#[derive(Debug)]
pub enum FinishNumber {
    Zero,
    One,
    Two,
}

#[derive(Debug)]
pub enum ModuleCommonItem<'a> {
    ModuleOrGenerateItemDeclaration(ModuleOrGenerateItemDeclaration<'a>),
    InterfaceInstantiation(InterfaceInstantiation<'a>),
    ProgramInstantiation(ProgramInstantiation<'a>),
    AssertionItem(AssertionItem<'a>),
    BindDirective(BindDirective<'a>),
    ContinuousAssign(ContinuousAssign<'a>),
    NetAlias(NetAlias<'a>),
    InitialConstruct(InitialConstruct<'a>),
    FinalConstruct(FinalConstruct<'a>),
    AlwaysConstruct(AlwaysConstruct<'a>),
    LoopGenerateConstruct(Box<LoopGenerateConstruct<'a>>),
    ConditionalGenerateConstruct(Box<ConditionalGenerateConstruct<'a>>),
    ElaborationSystemTask(ElaborationSystemTask<'a>),
}

#[derive(Debug)]
pub enum ModuleItem<'a> {
    PortDeclaratoin(PortDeclaration<'a>),
    NonPortModuleItem(NonPortModuleItem<'a>),
}

#[derive(Debug)]
pub enum ModuleOrGenerateItem<'a> {
    Parameter(ModuleOrGenerateItemParameter<'a>),
    Gate(ModuleOrGenerateItemGate<'a>),
    Udp(ModuleOrGenerateItemUdp<'a>),
    Module(ModuleOrGenerateItemModule<'a>),
    ModuleItem(Box<ModuleOrGenerateItemModuleItem<'a>>),
}

#[derive(Debug)]
pub struct ModuleOrGenerateItemParameter<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ParameterOverride<'a>),
}

#[derive(Debug)]
pub struct ModuleOrGenerateItemGate<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, GateInstantiation<'a>),
}

#[derive(Debug)]
pub struct ModuleOrGenerateItemUdp<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, UdpInstantiation<'a>),
}

#[derive(Debug)]
pub struct ModuleOrGenerateItemModule<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ModuleInstantiation<'a>),
}

#[derive(Debug)]
pub struct ModuleOrGenerateItemModuleItem<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ModuleCommonItem<'a>),
}

#[derive(Debug)]
pub enum ModuleOrGenerateItemDeclaration<'a> {
    PackageOrGenerateItemDeclaration(PackageOrGenerateItemDeclaration<'a>),
    GenvarDeclaration(GenvarDeclaration<'a>),
    ClockingDeclaration(ClockingDeclaration<'a>),
    Clocking(ModuleOrGenerateItemDeclarationClocking<'a>),
    Expression(ModuleOrGenerateItemDeclarationExpression<'a>),
}

#[derive(Debug)]
pub struct ModuleOrGenerateItemDeclarationClocking<'a> {
    pub nodes: (ClockingIdentifier<'a>),
}

#[derive(Debug)]
pub struct ModuleOrGenerateItemDeclarationExpression<'a> {
    pub nodes: (ExpressionOrDist<'a>),
}

#[derive(Debug)]
pub enum NonPortModuleItem<'a> {
    GenerateRegion(GenerateRegion<'a>),
    ModuleOrGenerateItem(ModuleOrGenerateItem<'a>),
    SpecifyBlock(SpecifyBlock<'a>),
    Specparam(NonPortModuleItemSpecparam<'a>),
    ProgramDeclaration(ProgramDeclaration<'a>),
    ModuleDeclaration(ModuleDeclaration<'a>),
    InterfaceDeclaration(InterfaceDeclaration<'a>),
    TimeunitsDeclaration(TimeunitsDeclaration<'a>),
}

#[derive(Debug)]
pub struct NonPortModuleItemSpecparam<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, SpecparamDeclaration<'a>),
}

#[derive(Debug)]
pub struct ParameterOverride<'a> {
    pub nodes: (ListOfDefparamAssignments<'a>,),
}

#[derive(Debug)]
pub enum BindDirective<'a> {
    Scope(BindDirectiveScope<'a>),
    Instance(BindDirectiveInstance<'a>),
}

#[derive(Debug)]
pub struct BindDirectiveScope<'a> {
    pub nodes: (
        BindTargetScope<'a>,
        Option<BindTargetInstanceList<'a>>,
        BindInstantiation<'a>,
    ),
}

#[derive(Debug)]
pub struct BindDirectiveInstance<'a> {
    pub nodes: (BindTargetInstanceList<'a>, BindInstantiation<'a>),
}

#[derive(Debug)]
pub enum BindTargetScope<'a> {
    ModuleIdentifier(ModuleIdentifier<'a>),
    InterfaceIdentifier(InterfaceIdentifier<'a>),
}

#[derive(Debug)]
pub struct BindTargetInstance<'a> {
    pub nodes: (HierarchicalIdentifier<'a>, ConstantBitSelect<'a>),
}

#[derive(Debug)]
pub struct BindTargetInstanceList<'a> {
    pub nodes: (Vec<BindTargetInstance<'a>>,),
}

#[derive(Debug)]
pub enum BindInstantiation<'a> {
    ProgramInstantiation(ProgramInstantiation<'a>),
    ModuleInstantiation(ModuleInstantiation<'a>),
    InterfaceInstantiation(InterfaceInstantiation<'a>),
    CheckerInstantiation(CheckerInstantiation<'a>),
}

// -----------------------------------------------------------------------------

pub fn elaboration_system_task(s: Span) -> IResult<Span, ElaborationSystemTask> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn finish_number(s: Span) -> IResult<Span, FinishNumber> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn module_common_item(s: Span) -> IResult<Span, ModuleCommonItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn module_item(s: Span) -> IResult<Span, ModuleItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn module_or_generate_item(s: Span) -> IResult<Span, ModuleOrGenerateItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn module_or_generate_item_declaration(
    s: Span,
) -> IResult<Span, ModuleOrGenerateItemDeclaration> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn non_port_module_item(s: Span) -> IResult<Span, NonPortModuleItem> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn parameter_override(s: Span) -> IResult<Span, ParameterOverride> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn bind_directive(s: Span) -> IResult<Span, BindDirective> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn bind_target_scope(s: Span) -> IResult<Span, BindTargetScope> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn bind_target_instance(s: Span) -> IResult<Span, BindTargetInstance> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn bind_target_instance_list(s: Span) -> IResult<Span, BindTargetInstanceList> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn bind_instantiation(s: Span) -> IResult<Span, BindInstantiation> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}
