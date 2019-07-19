use crate::ast::*;
use crate::parser::*;
use nom::branch::*;
use nom::combinator::*;
use nom::multi::*;
use nom::sequence::*;
use nom::IResult;

// -----------------------------------------------------------------------------

#[derive(Debug, Node)]
pub enum ElaborationSystemTask<'a> {
    Fatal(ElaborationSystemTaskFatal<'a>),
    Error(ElaborationSystemTaskError<'a>),
    Warning(ElaborationSystemTaskWarning<'a>),
    Info(ElaborationSystemTaskInfo<'a>),
}

#[derive(Debug, Node)]
pub struct ElaborationSystemTaskFatal<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<Paren<'a, (FinishNumber<'a>, Option<(Symbol<'a>, ListOfArguments<'a>)>)>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct ElaborationSystemTaskError<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<Paren<'a, Option<ListOfArguments<'a>>>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct ElaborationSystemTaskWarning<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<Paren<'a, Option<ListOfArguments<'a>>>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct ElaborationSystemTaskInfo<'a> {
    pub nodes: (
        Symbol<'a>,
        Option<Paren<'a, Option<ListOfArguments<'a>>>>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum FinishNumber<'a> {
    Zero(Symbol<'a>),
    One(Symbol<'a>),
    Two(Symbol<'a>),
}

#[derive(Debug, Node)]
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

#[derive(Debug, Node)]
pub enum ModuleItem<'a> {
    PortDeclaration((PortDeclaration<'a>, Symbol<'a>)),
    NonPortModuleItem(NonPortModuleItem<'a>),
}

#[derive(Debug, Node)]
pub enum ModuleOrGenerateItem<'a> {
    Parameter(ModuleOrGenerateItemParameter<'a>),
    Gate(ModuleOrGenerateItemGate<'a>),
    Udp(ModuleOrGenerateItemUdp<'a>),
    Module(ModuleOrGenerateItemModule<'a>),
    ModuleItem(Box<ModuleOrGenerateItemModuleItem<'a>>),
}

#[derive(Debug, Node)]
pub struct ModuleOrGenerateItemParameter<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ParameterOverride<'a>),
}

#[derive(Debug, Node)]
pub struct ModuleOrGenerateItemGate<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, GateInstantiation<'a>),
}

#[derive(Debug, Node)]
pub struct ModuleOrGenerateItemUdp<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, UdpInstantiation<'a>),
}

#[derive(Debug, Node)]
pub struct ModuleOrGenerateItemModule<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ModuleInstantiation<'a>),
}

#[derive(Debug, Node)]
pub struct ModuleOrGenerateItemModuleItem<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, ModuleCommonItem<'a>),
}

#[derive(Debug, Node)]
pub enum ModuleOrGenerateItemDeclaration<'a> {
    PackageOrGenerateItemDeclaration(PackageOrGenerateItemDeclaration<'a>),
    GenvarDeclaration(GenvarDeclaration<'a>),
    ClockingDeclaration(ClockingDeclaration<'a>),
    Clocking(ModuleOrGenerateItemDeclarationClocking<'a>),
    Disable(ModuleOrGenerateItemDeclarationDisable<'a>),
}

#[derive(Debug, Node)]
pub struct ModuleOrGenerateItemDeclarationClocking<'a> {
    pub nodes: (Symbol<'a>, Symbol<'a>, ClockingIdentifier<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub struct ModuleOrGenerateItemDeclarationDisable<'a> {
    pub nodes: (
        Symbol<'a>,
        Symbol<'a>,
        Symbol<'a>,
        ExpressionOrDist<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
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

#[derive(Debug, Node)]
pub struct NonPortModuleItemSpecparam<'a> {
    pub nodes: (Vec<AttributeInstance<'a>>, SpecparamDeclaration<'a>),
}

#[derive(Debug, Node)]
pub struct ParameterOverride<'a> {
    pub nodes: (Symbol<'a>, ListOfDefparamAssignments<'a>, Symbol<'a>),
}

#[derive(Debug, Node)]
pub enum BindDirective<'a> {
    Scope(BindDirectiveScope<'a>),
    Instance(BindDirectiveInstance<'a>),
}

#[derive(Debug, Node)]
pub struct BindDirectiveScope<'a> {
    pub nodes: (
        Symbol<'a>,
        BindTargetScope<'a>,
        Option<(Symbol<'a>, BindTargetInstanceList<'a>)>,
        BindInstantiation<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub struct BindDirectiveInstance<'a> {
    pub nodes: (
        Symbol<'a>,
        BindTargetInstance<'a>,
        BindInstantiation<'a>,
        Symbol<'a>,
    ),
}

#[derive(Debug, Node)]
pub enum BindTargetScope<'a> {
    ModuleIdentifier(ModuleIdentifier<'a>),
    InterfaceIdentifier(InterfaceIdentifier<'a>),
}

#[derive(Debug, Node)]
pub struct BindTargetInstance<'a> {
    pub nodes: (HierarchicalIdentifier<'a>, ConstantBitSelect<'a>),
}

#[derive(Debug, Node)]
pub struct BindTargetInstanceList<'a> {
    pub nodes: (List<Symbol<'a>, BindTargetInstance<'a>>,),
}

#[derive(Debug, Node)]
pub enum BindInstantiation<'a> {
    ProgramInstantiation(ProgramInstantiation<'a>),
    ModuleInstantiation(ModuleInstantiation<'a>),
    InterfaceInstantiation(InterfaceInstantiation<'a>),
    CheckerInstantiation(CheckerInstantiation<'a>),
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
        ElaborationSystemTask::Fatal(ElaborationSystemTaskFatal { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn elaboration_system_task_error(s: Span) -> IResult<Span, ElaborationSystemTask> {
    let (s, a) = keyword("$error")(s)?;
    let (s, b) = opt(paren(opt(list_of_arguments)))(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ElaborationSystemTask::Error(ElaborationSystemTaskError { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn elaboration_system_task_warning(s: Span) -> IResult<Span, ElaborationSystemTask> {
    let (s, a) = keyword("$warning")(s)?;
    let (s, b) = opt(paren(opt(list_of_arguments)))(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ElaborationSystemTask::Warning(ElaborationSystemTaskWarning { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn elaboration_system_task_info(s: Span) -> IResult<Span, ElaborationSystemTask> {
    let (s, a) = keyword("$info")(s)?;
    let (s, b) = opt(paren(opt(list_of_arguments)))(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ElaborationSystemTask::Info(ElaborationSystemTaskInfo { nodes: (a, b, c) }),
    ))
}

#[parser]
pub fn finish_number(s: Span) -> IResult<Span, FinishNumber> {
    alt((
        map(symbol("0"), |x| FinishNumber::Zero(x)),
        map(symbol("1"), |x| FinishNumber::One(x)),
        map(symbol("2"), |x| FinishNumber::Two(x)),
    ))(s)
}

#[parser]
pub fn module_common_item(s: Span) -> IResult<Span, ModuleCommonItem> {
    alt((
        map(module_or_generate_item_declaration, |x| {
            ModuleCommonItem::ModuleOrGenerateItemDeclaration(x)
        }),
        map(interface_instantiation, |x| {
            ModuleCommonItem::InterfaceInstantiation(x)
        }),
        map(program_instantiation, |x| {
            ModuleCommonItem::ProgramInstantiation(x)
        }),
        map(assertion_item, |x| ModuleCommonItem::AssertionItem(x)),
        map(bind_directive, |x| ModuleCommonItem::BindDirective(x)),
        map(continuous_assign, |x| ModuleCommonItem::ContinuousAssign(x)),
        map(net_alias, |x| ModuleCommonItem::NetAlias(x)),
        map(initial_construct, |x| ModuleCommonItem::InitialConstruct(x)),
        map(final_construct, |x| ModuleCommonItem::FinalConstruct(x)),
        map(always_construct, |x| ModuleCommonItem::AlwaysConstruct(x)),
        map(loop_generate_construct, |x| {
            ModuleCommonItem::LoopGenerateConstruct(Box::new(x))
        }),
        map(conditional_generate_construct, |x| {
            ModuleCommonItem::ConditionalGenerateConstruct(Box::new(x))
        }),
        map(elaboration_system_task, |x| {
            ModuleCommonItem::ElaborationSystemTask(x)
        }),
    ))(s)
}

#[parser]
pub fn module_item(s: Span) -> IResult<Span, ModuleItem> {
    alt((
        map(pair(port_declaration, symbol(";")), |x| {
            ModuleItem::PortDeclaration(x)
        }),
        map(non_port_module_item, |x| ModuleItem::NonPortModuleItem(x)),
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
        ModuleOrGenerateItem::Parameter(ModuleOrGenerateItemParameter { nodes: (a, b) }),
    ))
}

#[parser]
pub fn module_or_generate_item_gate(s: Span) -> IResult<Span, ModuleOrGenerateItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = gate_instantiation(s)?;
    Ok((
        s,
        ModuleOrGenerateItem::Gate(ModuleOrGenerateItemGate { nodes: (a, b) }),
    ))
}

#[parser]
pub fn module_or_generate_item_udp(s: Span) -> IResult<Span, ModuleOrGenerateItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = udp_instantiation(s)?;
    Ok((
        s,
        ModuleOrGenerateItem::Udp(ModuleOrGenerateItemUdp { nodes: (a, b) }),
    ))
}

#[parser]
pub fn module_or_generate_item_module(s: Span) -> IResult<Span, ModuleOrGenerateItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = module_instantiation(s)?;
    Ok((
        s,
        ModuleOrGenerateItem::Module(ModuleOrGenerateItemModule { nodes: (a, b) }),
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
            ModuleOrGenerateItemDeclaration::PackageOrGenerateItemDeclaration(x)
        }),
        map(genvar_declaration, |x| {
            ModuleOrGenerateItemDeclaration::GenvarDeclaration(x)
        }),
        map(clocking_declaration, |x| {
            ModuleOrGenerateItemDeclaration::ClockingDeclaration(x)
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
        ModuleOrGenerateItemDeclaration::Clocking(ModuleOrGenerateItemDeclarationClocking {
            nodes: (a, b, c, d),
        }),
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
        ModuleOrGenerateItemDeclaration::Disable(ModuleOrGenerateItemDeclarationDisable {
            nodes: (a, b, c, d, e),
        }),
    ))
}

#[parser]
pub fn non_port_module_item(s: Span) -> IResult<Span, NonPortModuleItem> {
    alt((
        map(generate_region, |x| NonPortModuleItem::GenerateRegion(x)),
        map(module_or_generate_item, |x| {
            NonPortModuleItem::ModuleOrGenerateItem(x)
        }),
        map(specify_block, |x| NonPortModuleItem::SpecifyBlock(x)),
        non_port_module_item_specparam,
        map(program_declaration, |x| {
            NonPortModuleItem::ProgramDeclaration(x)
        }),
        map(module_declaration, |x| {
            NonPortModuleItem::ModuleDeclaration(x)
        }),
        map(interface_declaration, |x| {
            NonPortModuleItem::InterfaceDeclaration(x)
        }),
        map(timeunits_declaration, |x| {
            NonPortModuleItem::TimeunitsDeclaration(x)
        }),
    ))(s)
}

#[parser]
pub fn non_port_module_item_specparam(s: Span) -> IResult<Span, NonPortModuleItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = specparam_declaration(s)?;
    Ok((
        s,
        NonPortModuleItem::Specparam(NonPortModuleItemSpecparam { nodes: (a, b) }),
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
        BindDirective::Scope(BindDirectiveScope {
            nodes: (a, b, c, d, e),
        }),
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
        BindDirective::Instance(BindDirectiveInstance {
            nodes: (a, b, c, d),
        }),
    ))
}

#[parser]
pub fn bind_target_scope(s: Span) -> IResult<Span, BindTargetScope> {
    alt((
        map(module_identifier, |x| BindTargetScope::ModuleIdentifier(x)),
        map(interface_identifier, |x| {
            BindTargetScope::InterfaceIdentifier(x)
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
            BindInstantiation::ProgramInstantiation(x)
        }),
        map(module_instantiation, |x| {
            BindInstantiation::ModuleInstantiation(x)
        }),
        map(interface_instantiation, |x| {
            BindInstantiation::InterfaceInstantiation(x)
        }),
        map(checker_instantiation, |x| {
            BindInstantiation::CheckerInstantiation(x)
        }),
    ))(s)
}
