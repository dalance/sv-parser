use crate::*;

// -----------------------------------------------------------------------------

pub(crate) const AZ_: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_";
pub(crate) const AZ09_: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_";
pub(crate) const AZ09_DOLLAR: &str =
    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_$";

#[allow(dead_code)]
#[parser]
pub(crate) fn array_identifier(s: Span) -> IResult<Span, ArrayIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ArrayIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn block_identifier(s: Span) -> IResult<Span, BlockIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, BlockIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn bin_identifier(s: Span) -> IResult<Span, BinIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, BinIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn c_identifier(s: Span) -> IResult<Span, CIdentifier> {
    let (s, a) = ws(c_identifier_impl)(s)?;
    Ok((s, CIdentifier { nodes: a }))
}

#[parser]
pub(crate) fn c_identifier_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = is_a(AZ_)(s)?;
    let (s, b) = opt(is_a(AZ09_))(s)?;
    let a = if let Some(b) = b {
        concat(a, b).unwrap()
    } else {
        a
    };
    if is_keyword(&a) {
        Err(Err::Error(make_error(s, ErrorKind::Fix)))
    } else {
        Ok((s, a.into()))
    }
}

#[parser]
pub(crate) fn cell_identifier(s: Span) -> IResult<Span, CellIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, CellIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn checker_identifier(s: Span) -> IResult<Span, CheckerIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, CheckerIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn class_identifier(s: Span) -> IResult<Span, ClassIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ClassIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn class_variable_identifier(s: Span) -> IResult<Span, ClassVariableIdentifier> {
    let (s, a) = variable_identifier(s)?;
    Ok((s, ClassVariableIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn clocking_identifier(s: Span) -> IResult<Span, ClockingIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ClockingIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn config_identifier(s: Span) -> IResult<Span, ConfigIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ConfigIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn const_identifier(s: Span) -> IResult<Span, ConstIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ConstIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn constraint_identifier(s: Span) -> IResult<Span, ConstraintIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ConstraintIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn covergroup_identifier(s: Span) -> IResult<Span, CovergroupIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, CovergroupIdentifier { nodes: (a,) }))
}

#[allow(dead_code)]
#[parser]
pub(crate) fn covergroup_variable_identifier(
    s: Span,
) -> IResult<Span, CovergroupVariableIdentifier> {
    let (s, a) = variable_identifier(s)?;
    Ok((s, CovergroupVariableIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn cover_point_identifier(s: Span) -> IResult<Span, CoverPointIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, CoverPointIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn cross_identifier(s: Span) -> IResult<Span, CrossIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, CrossIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn dynamic_array_variable_identifier(
    s: Span,
) -> IResult<Span, DynamicArrayVariableIdentifier> {
    let (s, a) = variable_identifier(s)?;
    Ok((s, DynamicArrayVariableIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn enum_identifier(s: Span) -> IResult<Span, EnumIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, EnumIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn escaped_identifier(s: Span) -> IResult<Span, EscapedIdentifier> {
    let (s, a) = ws(escaped_identifier_impl)(s)?;
    Ok((s, EscapedIdentifier { nodes: a }))
}

#[parser]
pub(crate) fn escaped_identifier_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = tag("\\")(s)?;
    let (s, b) = is_not(" \t\r\n")(s)?;
    let a = concat(a, b).unwrap();
    Ok((s, a.into()))
}

#[allow(dead_code)]
#[parser]
pub(crate) fn formal_identifier(s: Span) -> IResult<Span, FormalIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, FormalIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn formal_port_identifier(s: Span) -> IResult<Span, FormalPortIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, FormalPortIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn function_identifier(s: Span) -> IResult<Span, FunctionIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, FunctionIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn generate_block_identifier(s: Span) -> IResult<Span, GenerateBlockIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, GenerateBlockIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn genvar_identifier(s: Span) -> IResult<Span, GenvarIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, GenvarIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn hierarchical_array_identifier(s: Span) -> IResult<Span, HierarchicalArrayIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalArrayIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn hierarchical_block_identifier(s: Span) -> IResult<Span, HierarchicalBlockIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalBlockIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn hierarchical_event_identifier(s: Span) -> IResult<Span, HierarchicalEventIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalEventIdentifier { nodes: (a,) }))
}

#[packrat_parser]
#[parser]
pub(crate) fn hierarchical_identifier(s: Span) -> IResult<Span, HierarchicalIdentifier> {
    let (s, a) = opt(root)(s)?;
    let (s, b) = many0(triple(identifier, constant_bit_select, symbol(".")))(s)?;
    let (s, c) = identifier(s)?;
    Ok((s, HierarchicalIdentifier { nodes: (a, b, c) }))
}

#[parser]
pub(crate) fn root(s: Span) -> IResult<Span, Root> {
    let (s, a) = keyword("$root")(s)?;
    let (s, b) = symbol(".")(s)?;
    Ok((s, Root { nodes: (a, b) }))
}

#[parser]
pub(crate) fn hierarchical_net_identifier(s: Span) -> IResult<Span, HierarchicalNetIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalNetIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn hierarchical_parameter_identifier(
    s: Span,
) -> IResult<Span, HierarchicalParameterIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalParameterIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn hierarchical_property_identifier(
    s: Span,
) -> IResult<Span, HierarchicalPropertyIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalPropertyIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn hierarchical_sequence_identifier(
    s: Span,
) -> IResult<Span, HierarchicalSequenceIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalSequenceIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn hierarchical_task_identifier(s: Span) -> IResult<Span, HierarchicalTaskIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalTaskIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn hierarchical_tf_identifier(s: Span) -> IResult<Span, HierarchicalTfIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalTfIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn hierarchical_variable_identifier(
    s: Span,
) -> IResult<Span, HierarchicalVariableIdentifier> {
    let (s, a) = hierarchical_identifier(s)?;
    Ok((s, HierarchicalVariableIdentifier { nodes: (a,) }))
}

#[packrat_parser]
#[parser]
pub(crate) fn identifier(s: Span) -> IResult<Span, Identifier> {
    alt((
        map(escaped_identifier, |x| {
            Identifier::EscapedIdentifier(Box::new(x))
        }),
        map(simple_identifier, |x| {
            Identifier::SimpleIdentifier(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn index_variable_identifier(s: Span) -> IResult<Span, IndexVariableIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, IndexVariableIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn interface_identifier(s: Span) -> IResult<Span, InterfaceIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, InterfaceIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn interface_instance_identifier(s: Span) -> IResult<Span, InterfaceInstanceIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, InterfaceInstanceIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn inout_port_identifier(s: Span) -> IResult<Span, InoutPortIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, InoutPortIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn input_port_identifier(s: Span) -> IResult<Span, InputPortIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, InputPortIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn instance_identifier(s: Span) -> IResult<Span, InstanceIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, InstanceIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn library_identifier(s: Span) -> IResult<Span, LibraryIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, LibraryIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn member_identifier(s: Span) -> IResult<Span, MemberIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, MemberIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn method_identifier(s: Span) -> IResult<Span, MethodIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, MethodIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn modport_identifier(s: Span) -> IResult<Span, ModportIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ModportIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn module_identifier(s: Span) -> IResult<Span, ModuleIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ModuleIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn net_identifier(s: Span) -> IResult<Span, NetIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, NetIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn net_type_identifier(s: Span) -> IResult<Span, NetTypeIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, NetTypeIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn output_port_identifier(s: Span) -> IResult<Span, OutputPortIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, OutputPortIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn package_identifier(s: Span) -> IResult<Span, PackageIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, PackageIdentifier { nodes: (a,) }))
}

#[packrat_parser]
#[parser]
pub(crate) fn package_scope(s: Span) -> IResult<Span, PackageScope> {
    alt((
        package_scope_package,
        map(unit, |x| PackageScope::Unit(Box::new(x))),
    ))(s)
}

#[parser]
pub(crate) fn package_scope_package(s: Span) -> IResult<Span, PackageScope> {
    let (s, a) = package_identifier(s)?;
    let (s, b) = symbol("::")(s)?;
    Ok((
        s,
        PackageScope::Package(Box::new(PackageScopePackage { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn unit(s: Span) -> IResult<Span, Unit> {
    let (s, a) = keyword("$unit")(s)?;
    let (s, b) = symbol("::")(s)?;
    Ok((s, Unit { nodes: (a, b) }))
}

#[parser]
pub(crate) fn parameter_identifier(s: Span) -> IResult<Span, ParameterIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ParameterIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn port_identifier(s: Span) -> IResult<Span, PortIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, PortIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn production_identifier(s: Span) -> IResult<Span, ProductionIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ProductionIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn program_identifier(s: Span) -> IResult<Span, ProgramIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, ProgramIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn property_identifier(s: Span) -> IResult<Span, PropertyIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, PropertyIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn ps_class_identifier(s: Span) -> IResult<Span, PsClassIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = class_identifier(s)?;
    Ok((s, PsClassIdentifier { nodes: (a, b) }))
}

#[parser]
pub(crate) fn ps_covergroup_identifier(s: Span) -> IResult<Span, PsCovergroupIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = covergroup_identifier(s)?;
    Ok((s, PsCovergroupIdentifier { nodes: (a, b) }))
}

#[parser]
pub(crate) fn ps_checker_identifier(s: Span) -> IResult<Span, PsCheckerIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = checker_identifier(s)?;
    Ok((s, PsCheckerIdentifier { nodes: (a, b) }))
}

#[parser]
pub(crate) fn ps_identifier(s: Span) -> IResult<Span, PsIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = identifier(s)?;
    Ok((s, PsIdentifier { nodes: (a, b) }))
}

#[parser]
pub(crate) fn ps_or_hierarchical_array_identifier(
    s: Span,
) -> IResult<Span, PsOrHierarchicalArrayIdentifier> {
    let (s, a) = opt(implicit_class_handle_or_class_scope_or_package_scope)(s)?;
    let (s, b) = hierarchical_array_identifier(s)?;
    Ok((s, PsOrHierarchicalArrayIdentifier { nodes: (a, b) }))
}

#[parser]
pub(crate) fn ps_or_hierarchical_net_identifier(
    s: Span,
) -> IResult<Span, PsOrHierarchicalNetIdentifier> {
    alt((
        ps_or_hierarchical_net_identifier_package_scope,
        map(hierarchical_net_identifier, |x| {
            PsOrHierarchicalNetIdentifier::HierarchicalNetIdentifier(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn ps_or_hierarchical_net_identifier_package_scope(
    s: Span,
) -> IResult<Span, PsOrHierarchicalNetIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = net_identifier(s)?;
    Ok((
        s,
        PsOrHierarchicalNetIdentifier::PackageScope(Box::new(
            PsOrHierarchicalNetIdentifierPackageScope { nodes: (a, b) },
        )),
    ))
}

#[parser]
pub(crate) fn ps_or_hierarchical_property_identifier(
    s: Span,
) -> IResult<Span, PsOrHierarchicalPropertyIdentifier> {
    alt((
        ps_or_hierarchical_property_identifier_package_scope,
        map(hierarchical_property_identifier, |x| {
            PsOrHierarchicalPropertyIdentifier::HierarchicalPropertyIdentifier(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn ps_or_hierarchical_property_identifier_package_scope(
    s: Span,
) -> IResult<Span, PsOrHierarchicalPropertyIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = property_identifier(s)?;
    Ok((
        s,
        PsOrHierarchicalPropertyIdentifier::PackageScope(Box::new(
            PsOrHierarchicalPropertyIdentifierPackageScope { nodes: (a, b) },
        )),
    ))
}

#[parser]
pub(crate) fn ps_or_hierarchical_sequence_identifier(
    s: Span,
) -> IResult<Span, PsOrHierarchicalSequenceIdentifier> {
    alt((
        ps_or_hierarchical_sequence_identifier_package_scope,
        map(hierarchical_sequence_identifier, |x| {
            PsOrHierarchicalSequenceIdentifier::HierarchicalSequenceIdentifier(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn ps_or_hierarchical_sequence_identifier_package_scope(
    s: Span,
) -> IResult<Span, PsOrHierarchicalSequenceIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = sequence_identifier(s)?;
    Ok((
        s,
        PsOrHierarchicalSequenceIdentifier::PackageScope(Box::new(
            PsOrHierarchicalSequenceIdentifierPackageScope { nodes: (a, b) },
        )),
    ))
}

#[parser]
pub(crate) fn ps_or_hierarchical_tf_identifier(
    s: Span,
) -> IResult<Span, PsOrHierarchicalTfIdentifier> {
    alt((
        ps_or_hierarchical_tf_identifier_package_scope,
        map(hierarchical_tf_identifier, |x| {
            PsOrHierarchicalTfIdentifier::HierarchicalTfIdentifier(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn ps_or_hierarchical_tf_identifier_package_scope(
    s: Span,
) -> IResult<Span, PsOrHierarchicalTfIdentifier> {
    let (s, a) = opt(package_scope)(s)?;
    let (s, b) = tf_identifier(s)?;
    Ok((
        s,
        PsOrHierarchicalTfIdentifier::PackageScope(Box::new(
            PsOrHierarchicalTfIdentifierPackageScope { nodes: (a, b) },
        )),
    ))
}

#[packrat_parser]
#[parser]
pub(crate) fn ps_parameter_identifier(s: Span) -> IResult<Span, PsParameterIdentifier> {
    alt((
        ps_parameter_identifier_scope,
        ps_parameter_identifier_generate,
    ))(s)
}

#[parser]
pub(crate) fn ps_parameter_identifier_scope(s: Span) -> IResult<Span, PsParameterIdentifier> {
    let (s, a) = opt(package_scope_or_class_scope)(s)?;
    let (s, b) = parameter_identifier(s)?;
    Ok((
        s,
        PsParameterIdentifier::Scope(Box::new(PsParameterIdentifierScope { nodes: (a, b) })),
    ))
}

#[parser]
pub(crate) fn ps_parameter_identifier_generate(s: Span) -> IResult<Span, PsParameterIdentifier> {
    let (s, a) = many0(triple(
        generate_block_identifier,
        opt(bracket(constant_expression)),
        symbol("."),
    ))(s)?;
    let (s, b) = parameter_identifier(s)?;
    Ok((
        s,
        PsParameterIdentifier::Generate(Box::new(PsParameterIdentifierGenerate { nodes: (a, b) })),
    ))
}

#[packrat_parser]
#[parser]
pub(crate) fn ps_type_identifier(s: Span) -> IResult<Span, PsTypeIdentifier> {
    let (s, a) = opt(local_or_package_scope_or_class_scope)(s)?;
    let (s, b) = type_identifier(s)?;
    Ok((s, PsTypeIdentifier { nodes: (a, b) }))
}

#[parser]
pub(crate) fn sequence_identifier(s: Span) -> IResult<Span, SequenceIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, SequenceIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn signal_identifier(s: Span) -> IResult<Span, SignalIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, SignalIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn simple_identifier(s: Span) -> IResult<Span, SimpleIdentifier> {
    let (s, a) = ws(simple_identifier_impl)(s)?;
    Ok((s, SimpleIdentifier { nodes: a }))
}

#[parser]
pub(crate) fn simple_identifier_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = is_a(AZ_)(s)?;
    let (s, b) = opt(is_a(AZ09_DOLLAR))(s)?;
    let a = if let Some(b) = b {
        concat(a, b).unwrap()
    } else {
        a
    };
    if is_keyword(&a) {
        Err(Err::Error(make_error(s, ErrorKind::Fix)))
    } else {
        Ok((s, a.into()))
    }
}

#[parser]
pub(crate) fn specparam_identifier(s: Span) -> IResult<Span, SpecparamIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, SpecparamIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn system_tf_identifier(s: Span) -> IResult<Span, SystemTfIdentifier> {
    let (s, a) = ws(system_tf_identifier_impl)(s)?;
    Ok((s, SystemTfIdentifier { nodes: a }))
}

#[parser]
pub(crate) fn system_tf_identifier_impl(s: Span) -> IResult<Span, Locate> {
    let (s, a) = tag("$")(s)?;
    let (s, b) = is_a(AZ09_DOLLAR)(s)?;
    let a = concat(a, b).unwrap();
    Ok((s, a.into()))
}

#[parser]
pub(crate) fn task_identifier(s: Span) -> IResult<Span, TaskIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, TaskIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn tf_identifier(s: Span) -> IResult<Span, TfIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, TfIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn terminal_identifier(s: Span) -> IResult<Span, TerminalIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, TerminalIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn topmodule_identifier(s: Span) -> IResult<Span, TopmoduleIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, TopmoduleIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn type_identifier(s: Span) -> IResult<Span, TypeIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, TypeIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn udp_identifier(s: Span) -> IResult<Span, UdpIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, UdpIdentifier { nodes: (a,) }))
}

#[packrat_parser]
#[parser]
pub(crate) fn variable_identifier(s: Span) -> IResult<Span, VariableIdentifier> {
    let (s, a) = identifier(s)?;
    Ok((s, VariableIdentifier { nodes: (a,) }))
}

#[parser]
pub(crate) fn implicit_class_handle_or_class_scope_or_package_scope(
    s: Span,
) -> IResult<Span, ImplicitClassHandleOrClassScopeOrPackageScope> {
    alt((
        map(pair(implicit_class_handle, symbol(".")), |x| {
            ImplicitClassHandleOrClassScopeOrPackageScope::ImplicitClassHandle(Box::new(x))
        }),
        map(class_scope, |x| {
            ImplicitClassHandleOrClassScopeOrPackageScope::ClassScope(Box::new(x))
        }),
        map(package_scope, |x| {
            ImplicitClassHandleOrClassScopeOrPackageScope::PackageScope(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn implicit_class_handle_or_package_scope(
    s: Span,
) -> IResult<Span, ImplicitClassHandleOrPackageScope> {
    alt((
        map(pair(implicit_class_handle, symbol(".")), |x| {
            ImplicitClassHandleOrPackageScope::ImplicitClassHandle(Box::new(x))
        }),
        map(package_scope, |x| {
            ImplicitClassHandleOrPackageScope::PackageScope(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn implicit_class_handle_or_class_scope(
    s: Span,
) -> IResult<Span, ImplicitClassHandleOrClassScope> {
    alt((
        map(pair(implicit_class_handle, symbol(".")), |x| {
            ImplicitClassHandleOrClassScope::ImplicitClassHandle(Box::new(x))
        }),
        map(class_scope, |x| {
            ImplicitClassHandleOrClassScope::ClassScope(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn package_scope_or_class_scope(s: Span) -> IResult<Span, PackageScopeOrClassScope> {
    alt((
        map(package_scope, |x| {
            PackageScopeOrClassScope::PackageScope(Box::new(x))
        }),
        map(class_scope, |x| {
            PackageScopeOrClassScope::ClassScope(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn local_or_package_scope_or_class_scope(
    s: Span,
) -> IResult<Span, LocalOrPackageScopeOrClassScope> {
    alt((
        map(local, |x| {
            LocalOrPackageScopeOrClassScope::Local(Box::new(x))
        }),
        map(package_scope, |x| {
            LocalOrPackageScopeOrClassScope::PackageScope(Box::new(x))
        }),
        map(class_scope, |x| {
            LocalOrPackageScopeOrClassScope::ClassScope(Box::new(x))
        }),
    ))(s)
}

#[parser]
pub(crate) fn local(s: Span) -> IResult<Span, Local> {
    let (s, a) = keyword("local")(s)?;
    let (s, b) = symbol("::")(s)?;
    Ok((s, Local { nodes: (a, b) }))
}
