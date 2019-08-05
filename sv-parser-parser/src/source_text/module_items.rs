use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn elaboration_system_task(s: Span) -> IResult<Span, ElaborationSystemTask> {
    alt((
        elaboration_system_task_fatal,
        elaboration_system_task_error,
        elaboration_system_task_warning,
        elaboration_system_task_info,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn elaboration_system_task_fatal(s: Span) -> IResult<Span, ElaborationSystemTask> {
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

#[tracable_parser]
#[packrat_parser]
pub(crate) fn elaboration_system_task_error(s: Span) -> IResult<Span, ElaborationSystemTask> {
    let (s, a) = keyword("$error")(s)?;
    let (s, b) = opt(paren(opt(list_of_arguments)))(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ElaborationSystemTask::TaskError(Box::new(ElaborationSystemTaskError { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn elaboration_system_task_warning(s: Span) -> IResult<Span, ElaborationSystemTask> {
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

#[tracable_parser]
#[packrat_parser]
pub(crate) fn elaboration_system_task_info(s: Span) -> IResult<Span, ElaborationSystemTask> {
    let (s, a) = keyword("$info")(s)?;
    let (s, b) = opt(paren(opt(list_of_arguments)))(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        ElaborationSystemTask::TaskInfo(Box::new(ElaborationSystemTaskInfo { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn finish_number(s: Span) -> IResult<Span, FinishNumber> {
    alt((
        map(symbol("0"), |x| FinishNumber::Zero(Box::new(x))),
        map(symbol("1"), |x| FinishNumber::One(Box::new(x))),
        map(symbol("2"), |x| FinishNumber::Two(Box::new(x))),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn module_common_item(s: Span) -> IResult<Span, ModuleCommonItem> {
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

#[tracable_parser]
#[packrat_parser]
pub(crate) fn module_item(s: Span) -> IResult<Span, ModuleItem> {
    alt((
        map(pair(port_declaration, symbol(";")), |x| {
            ModuleItem::PortDeclaration(Box::new(x))
        }),
        map(non_port_module_item, |x| {
            ModuleItem::NonPortModuleItem(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn module_or_generate_item(s: Span) -> IResult<Span, ModuleOrGenerateItem> {
    alt((
        module_or_generate_item_parameter,
        module_or_generate_item_gate,
        module_or_generate_item_udp,
        module_or_generate_item_module,
        module_or_generate_item_module_item,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn module_or_generate_item_parameter(s: Span) -> IResult<Span, ModuleOrGenerateItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = parameter_override(s)?;
    Ok((
        s,
        ModuleOrGenerateItem::Parameter(Box::new(ModuleOrGenerateItemParameter { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn module_or_generate_item_gate(s: Span) -> IResult<Span, ModuleOrGenerateItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = gate_instantiation(s)?;
    Ok((
        s,
        ModuleOrGenerateItem::Gate(Box::new(ModuleOrGenerateItemGate { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn module_or_generate_item_udp(s: Span) -> IResult<Span, ModuleOrGenerateItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = udp_instantiation(s)?;
    Ok((
        s,
        ModuleOrGenerateItem::Udp(Box::new(ModuleOrGenerateItemUdp { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn module_or_generate_item_module(s: Span) -> IResult<Span, ModuleOrGenerateItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = module_instantiation(s)?;
    Ok((
        s,
        ModuleOrGenerateItem::Module(Box::new(ModuleOrGenerateItemModule { nodes: (a, b) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn module_or_generate_item_module_item(s: Span) -> IResult<Span, ModuleOrGenerateItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = module_common_item(s)?;
    Ok((
        s,
        ModuleOrGenerateItem::ModuleItem(Box::new(ModuleOrGenerateItemModuleItem {
            nodes: (a, b),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn module_or_generate_item_declaration(
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

#[tracable_parser]
#[packrat_parser]
pub(crate) fn module_or_generate_item_declaration_clocking(
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

#[tracable_parser]
#[packrat_parser]
pub(crate) fn module_or_generate_item_declaration_disable(
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

#[tracable_parser]
#[packrat_parser]
pub(crate) fn non_port_module_item(s: Span) -> IResult<Span, NonPortModuleItem> {
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

#[tracable_parser]
#[packrat_parser]
pub(crate) fn non_port_module_item_specparam(s: Span) -> IResult<Span, NonPortModuleItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = specparam_declaration(s)?;
    Ok((
        s,
        NonPortModuleItem::Specparam(Box::new(NonPortModuleItemSpecparam { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn parameter_override(s: Span) -> IResult<Span, ParameterOverride> {
    let (s, a) = keyword("defparam")(s)?;
    let (s, b) = list_of_defparam_assignments(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((s, ParameterOverride { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bind_directive(s: Span) -> IResult<Span, BindDirective> {
    alt((bind_directive_scope, bind_directive_instance))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bind_directive_scope(s: Span) -> IResult<Span, BindDirective> {
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

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bind_directive_instance(s: Span) -> IResult<Span, BindDirective> {
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

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bind_target_scope(s: Span) -> IResult<Span, BindTargetScope> {
    alt((
        map(module_identifier, |x| {
            BindTargetScope::ModuleIdentifier(Box::new(x))
        }),
        map(interface_identifier, |x| {
            BindTargetScope::InterfaceIdentifier(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bind_target_instance(s: Span) -> IResult<Span, BindTargetInstance> {
    let (s, a) = hierarchical_identifier(s)?;
    let (s, b) = constant_bit_select(s)?;
    Ok((s, BindTargetInstance { nodes: (a, b) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bind_target_instance_list(s: Span) -> IResult<Span, BindTargetInstanceList> {
    let (s, a) = list(symbol(","), bind_target_instance)(s)?;
    Ok((s, BindTargetInstanceList { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bind_instantiation(s: Span) -> IResult<Span, BindInstantiation> {
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
