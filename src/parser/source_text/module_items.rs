use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

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
        Symbol,
    ),
}

#[derive(Clone, Debug, Node)]
pub struct BindDirectiveInstance {
    pub nodes: (Keyword, BindTargetInstance, BindInstantiation, Symbol),
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

// -----------------------------------------------------------------------------

#[parser]
pub fn elaboration_system_task(s: Span) -> IResult<Span, ElaborationSystemTask> {
    alt((
        elaboration_system_task_fatal,
        elaboration_system_task_error,
        elaboration_system_task_warning,
        elaboration_system_task_info,
    ))(s)
}

#[parser]
pub fn elaboration_system_task_fatal(s: Span) -> IResult<Span, ElaborationSystemTask> {
    let (s, a) = keyword("$fatal")(s)?;
    let (s, b) = opt(paren(pair(
        finish_number,
        opt(pair(symbol(","), list_of_arguments)),
    )))(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ElaborationSystemTask::TaskFatal(Box::new(ElaborationSystemTaskFatal { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn elaboration_system_task_error(s: Span) -> IResult<Span, ElaborationSystemTask> {
    let (s, a) = keyword("$error")(s)?;
    let (s, b) = opt(paren(opt(list_of_arguments)))(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ElaborationSystemTask::TaskError(Box::new(ElaborationSystemTaskError { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn elaboration_system_task_warning(s: Span) -> IResult<Span, ElaborationSystemTask> {
    let (s, a) = keyword("$warning")(s)?;
    let (s, b) = opt(paren(opt(list_of_arguments)))(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ElaborationSystemTask::TaskWarning(Box::new(ElaborationSystemTaskWarning {
            nodes: (a, b, c),
        })),
    ))
}

#[parser]
pub fn elaboration_system_task_info(s: Span) -> IResult<Span, ElaborationSystemTask> {
    let (s, a) = keyword("$info")(s)?;
    let (s, b) = opt(paren(opt(list_of_arguments)))(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ElaborationSystemTask::TaskInfo(Box::new(ElaborationSystemTaskInfo { nodes: (a, b, c) })),
    ))
}

#[parser]
pub fn finish_number(s: Span) -> IResult<Span, FinishNumber> {
    alt((
        map(symbol("0"), |x| FinishNumber::Zero(Box::new(x))),
        map(symbol("1"), |x| FinishNumber::One(Box::new(x))),
        map(symbol("2"), |x| FinishNumber::Two(Box::new(x))),
    ))(s)
}

#[parser]
pub fn module_common_item(s: Span) -> IResult<Span, ModuleCommonItem> {
    alt((
        map(module_or_generate_item_declaration, |x| {
            ModuleCommonItem::ModuleOrGenerateItemDeclaration(Box::new(x))
        }),
        map(interface_instantiation, |x| {
            ModuleCommonItem::InterfaceInstantiation(Box::new(x))
        }),
        map(program_instantiation, |x| {
            ModuleCommonItem::ProgramInstantiation(Box::new(x))
        }),
        map(assertion_item, |x| {
            ModuleCommonItem::AssertionItem(Box::new(x))
        }),
        map(bind_directive, |x| {
            ModuleCommonItem::BindDirective(Box::new(x))
        }),
        map(continuous_assign, |x| {
            ModuleCommonItem::ContinuousAssign(Box::new(x))
        }),
        map(net_alias, |x| ModuleCommonItem::NetAlias(Box::new(x))),
        map(initial_construct, |x| {
            ModuleCommonItem::InitialConstruct(Box::new(x))
        }),
        map(final_construct, |x| {
            ModuleCommonItem::FinalConstruct(Box::new(x))
        }),
        map(always_construct, |x| {
            ModuleCommonItem::AlwaysConstruct(Box::new(x))
        }),
        map(loop_generate_construct, |x| {
            ModuleCommonItem::LoopGenerateConstruct(Box::new(x))
        }),
        map(conditional_generate_construct, |x| {
            ModuleCommonItem::ConditionalGenerateConstruct(Box::new(x))
        }),
        map(elaboration_system_task, |x| {
            ModuleCommonItem::ElaborationSystemTask(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn module_item(s: Span) -> IResult<Span, ModuleItem> {
    alt((
        map(pair(port_declaration, symbol(";")), |x| {
            ModuleItem::PortDeclaration(Box::new(x))
        }),
        map(non_port_module_item, |x| {
            ModuleItem::NonPortModuleItem(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn module_or_generate_item(s: Span) -> IResult<Span, ModuleOrGenerateItem> {
    alt((
        module_or_generate_item_parameter,
        module_or_generate_item_gate,
        module_or_generate_item_udp,
        module_or_generate_item_module,
        module_or_generate_item_module_item,
    ))(s)
}

#[parser]
pub fn module_or_generate_item_parameter(s: Span) -> IResult<Span, ModuleOrGenerateItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = parameter_override(s)?;
    Ok((
        s,
        ModuleOrGenerateItem::Parameter(Box::new(ModuleOrGenerateItemParameter { nodes: (a, b) })),
    ))
}

#[parser]
pub fn module_or_generate_item_gate(s: Span) -> IResult<Span, ModuleOrGenerateItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = gate_instantiation(s)?;
    Ok((
        s,
        ModuleOrGenerateItem::Gate(Box::new(ModuleOrGenerateItemGate { nodes: (a, b) })),
    ))
}

#[parser]
pub fn module_or_generate_item_udp(s: Span) -> IResult<Span, ModuleOrGenerateItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = udp_instantiation(s)?;
    Ok((
        s,
        ModuleOrGenerateItem::Udp(Box::new(ModuleOrGenerateItemUdp { nodes: (a, b) })),
    ))
}

#[parser]
pub fn module_or_generate_item_module(s: Span) -> IResult<Span, ModuleOrGenerateItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = module_instantiation(s)?;
    Ok((
        s,
        ModuleOrGenerateItem::Module(Box::new(ModuleOrGenerateItemModule { nodes: (a, b) })),
    ))
}

#[parser(MaybeRecursive)]
pub fn module_or_generate_item_module_item(s: Span) -> IResult<Span, ModuleOrGenerateItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = module_common_item(s)?;
    Ok((
        s,
        ModuleOrGenerateItem::ModuleItem(Box::new(ModuleOrGenerateItemModuleItem {
            nodes: (a, b),
        })),
    ))
}

#[parser]
pub fn module_or_generate_item_declaration(
    s: Span,
) -> IResult<Span, ModuleOrGenerateItemDeclaration> {
    alt((
        map(package_or_generate_item_declaration, |x| {
            ModuleOrGenerateItemDeclaration::PackageOrGenerateItemDeclaration(Box::new(x))
        }),
        map(genvar_declaration, |x| {
            ModuleOrGenerateItemDeclaration::GenvarDeclaration(Box::new(x))
        }),
        map(clocking_declaration, |x| {
            ModuleOrGenerateItemDeclaration::ClockingDeclaration(Box::new(x))
        }),
        module_or_generate_item_declaration_clocking,
        module_or_generate_item_declaration_disable,
    ))(s)
}

#[parser]
pub fn module_or_generate_item_declaration_clocking(
    s: Span,
) -> IResult<Span, ModuleOrGenerateItemDeclaration> {
    let (s, a) = keyword("default")(s)?;
    let (s, b) = keyword("clocking")(s)?;
    let (s, c) = clocking_identifier(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        ModuleOrGenerateItemDeclaration::Clocking(Box::new(
            ModuleOrGenerateItemDeclarationClocking {
                nodes: (a, b, c, d),
            },
        )),
    ))
}

#[parser]
pub fn module_or_generate_item_declaration_disable(
    s: Span,
) -> IResult<Span, ModuleOrGenerateItemDeclaration> {
    let (s, a) = keyword("default")(s)?;
    let (s, b) = keyword("disable")(s)?;
    let (s, c) = keyword("iff")(s)?;
    let (s, d) = expression_or_dist(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        ModuleOrGenerateItemDeclaration::Disable(Box::new(
            ModuleOrGenerateItemDeclarationDisable {
                nodes: (a, b, c, d, e),
            },
        )),
    ))
}

#[parser]
pub fn non_port_module_item(s: Span) -> IResult<Span, NonPortModuleItem> {
    alt((
        map(generate_region, |x| {
            NonPortModuleItem::GenerateRegion(Box::new(x))
        }),
        map(module_or_generate_item, |x| {
            NonPortModuleItem::ModuleOrGenerateItem(Box::new(x))
        }),
        map(specify_block, |x| {
            NonPortModuleItem::SpecifyBlock(Box::new(x))
        }),
        non_port_module_item_specparam,
        map(program_declaration, |x| {
            NonPortModuleItem::ProgramDeclaration(Box::new(x))
        }),
        map(module_declaration, |x| {
            NonPortModuleItem::ModuleDeclaration(Box::new(x))
        }),
        map(interface_declaration, |x| {
            NonPortModuleItem::InterfaceDeclaration(Box::new(x))
        }),
        map(timeunits_declaration, |x| {
            NonPortModuleItem::TimeunitsDeclaration(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn non_port_module_item_specparam(s: Span) -> IResult<Span, NonPortModuleItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = specparam_declaration(s)?;
    Ok((
        s,
        NonPortModuleItem::Specparam(Box::new(NonPortModuleItemSpecparam { nodes: (a, b) })),
    ))
}

#[parser]
pub fn parameter_override(s: Span) -> IResult<Span, ParameterOverride> {
    let (s, a) = keyword("defparam")(s)?;
    let (s, b) = list_of_defparam_assignments(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((s, ParameterOverride { nodes: (a, b, c) }))
}

#[parser]
pub fn bind_directive(s: Span) -> IResult<Span, BindDirective> {
    alt((bind_directive_scope, bind_directive_instance))(s)
}

#[parser]
pub fn bind_directive_scope(s: Span) -> IResult<Span, BindDirective> {
    let (s, a) = keyword("bind")(s)?;
    let (s, b) = bind_target_scope(s)?;
    let (s, c) = opt(pair(symbol(":"), bind_target_instance_list))(s)?;
    let (s, d) = bind_instantiation(s)?;
    let (s, e) = symbol(";")(s)?;
    Ok((
        s,
        BindDirective::Scope(Box::new(BindDirectiveScope {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[parser]
pub fn bind_directive_instance(s: Span) -> IResult<Span, BindDirective> {
    let (s, a) = keyword("bind")(s)?;
    let (s, b) = bind_target_instance(s)?;
    let (s, c) = bind_instantiation(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        BindDirective::Instance(Box::new(BindDirectiveInstance {
            nodes: (a, b, c, d),
        })),
    ))
}

#[parser]
pub fn bind_target_scope(s: Span) -> IResult<Span, BindTargetScope> {
    alt((
        map(module_identifier, |x| {
            BindTargetScope::ModuleIdentifier(Box::new(x))
        }),
        map(interface_identifier, |x| {
            BindTargetScope::InterfaceIdentifier(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub fn bind_target_instance(s: Span) -> IResult<Span, BindTargetInstance> {
    let (s, a) = hierarchical_identifier(s)?;
    let (s, b) = constant_bit_select(s)?;
    Ok((s, BindTargetInstance { nodes: (a, b) }))
}

#[parser]
pub fn bind_target_instance_list(s: Span) -> IResult<Span, BindTargetInstanceList> {
    let (s, a) = list(symbol(","), bind_target_instance)(s)?;
    Ok((s, BindTargetInstanceList { nodes: (a,) }))
}

#[parser]
pub fn bind_instantiation(s: Span) -> IResult<Span, BindInstantiation> {
    alt((
        map(program_instantiation, |x| {
            BindInstantiation::ProgramInstantiation(Box::new(x))
        }),
        map(module_instantiation, |x| {
            BindInstantiation::ModuleInstantiation(Box::new(x))
        }),
        map(interface_instantiation, |x| {
            BindInstantiation::InterfaceInstantiation(Box::new(x))
        }),
        map(checker_instantiation, |x| {
            BindInstantiation::CheckerInstantiation(Box::new(x))
        }),
    ))(s)
}
