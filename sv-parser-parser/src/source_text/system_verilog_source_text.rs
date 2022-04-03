use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn source_text(s: Span) -> IResult<Span, SourceText> {
    let (s, a) = many0(white_space)(s)?;
    let (s, b) = opt(timeunits_declaration)(s)?;
    let (s, (c, _)) = many_till(description, eof)(s)?;
    Ok((s, SourceText { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn source_text_incomplete(s: Span) -> IResult<Span, SourceText> {
    let (s, a) = many0(white_space)(s)?;
    let (s, b) = opt(timeunits_declaration)(s)?;
    let (s, c) = many0(description)(s)?;
    Ok((s, SourceText { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn description(s: Span) -> IResult<Span, Description> {
    alt((
        map(resetall_compiler_directive, |x| {
            Description::ResetallCompilerDirective(Box::new(x))
        }),
        map(module_declaration, |x| {
            Description::ModuleDeclaration(Box::new(x))
        }),
        map(udp_declaration, |x| {
            Description::UdpDeclaration(Box::new(x))
        }),
        map(interface_declaration, |x| {
            Description::InterfaceDeclaration(Box::new(x))
        }),
        map(interface_class_declaration, |x| {
            Description::InterfaceClassDeclaration(Box::new(x))
        }),
        map(program_declaration, |x| {
            Description::ProgramDeclaration(Box::new(x))
        }),
        map(package_declaration, |x| {
            Description::PackageDeclaration(Box::new(x))
        }),
        description_package_item,
        description_bind_directive,
        map(config_declaration, |x| {
            Description::ConfigDeclaration(Box::new(x))
        }),
        map(class_declaration, |x| {
            Description::ClassDeclaration(Box::new(x))
        }),
    ))(s)
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn description_package_item(s: Span) -> IResult<Span, Description> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = package_item(s)?;
    Ok((
        s,
        Description::PackageItem(Box::new(DescriptionPackageItem { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn description_bind_directive(s: Span) -> IResult<Span, Description> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = bind_directive(s)?;
    Ok((
        s,
        Description::BindDirective(Box::new(DescriptionBindDirective { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn module_nonansi_header(s: Span) -> IResult<Span, ModuleNonansiHeader> {
    let (s, (a, b)) = many_till(attribute_instance, module_keyword)(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = module_identifier(s)?;
    let (s, e) = many0(package_import_declaration)(s)?;
    let (s, f) = opt(parameter_port_list)(s)?;
    let (s, g) = list_of_ports(s)?;
    let (s, h) = symbol(";")(s)?;
    Ok((
        s,
        ModuleNonansiHeader {
            nodes: (a, b, c, d, e, f, g, h),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn module_ansi_header(s: Span) -> IResult<Span, ModuleAnsiHeader> {
    let (s, (a, b)) = many_till(attribute_instance, module_keyword)(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = module_identifier(s)?;
    let (s, e) = many0(package_import_declaration)(s)?;
    let (s, f) = opt(parameter_port_list)(s)?;
    let (s, g) = opt(list_of_port_declarations)(s)?;
    let (s, h) = symbol(";")(s)?;
    Ok((
        s,
        ModuleAnsiHeader {
            nodes: (a, b, c, d, e, f, g, h),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn module_declaration(s: Span) -> IResult<Span, ModuleDeclaration> {
    alt((
        module_declaration_ansi,
        module_declaration_nonansi,
        module_declaration_wildcard,
        module_declaration_extern_ansi,
        module_declaration_extern_nonansi,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn module_declaration_nonansi(s: Span) -> IResult<Span, ModuleDeclaration> {
    let (s, a) = module_nonansi_header(s)?;
    let (s, b) = opt(timeunits_declaration)(s)?;
    let (s, (c, d)) = many_till(module_item, keyword("endmodule"))(s)?;
    let (s, e) = opt(pair(symbol(":"), module_identifier))(s)?;
    Ok((
        s,
        ModuleDeclaration::Nonansi(Box::new(ModuleDeclarationNonansi {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn module_declaration_ansi(s: Span) -> IResult<Span, ModuleDeclaration> {
    let (s, a) = module_ansi_header(s)?;
    let (s, b) = opt(timeunits_declaration)(s)?;
    let (s, (c, d)) = many_till(non_port_module_item, keyword("endmodule"))(s)?;
    let (s, e) = opt(pair(symbol(":"), module_identifier))(s)?;
    Ok((
        s,
        ModuleDeclaration::Ansi(Box::new(ModuleDeclarationAnsi {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn module_declaration_wildcard(s: Span) -> IResult<Span, ModuleDeclaration> {
    let (s, (a, b)) = many_till(attribute_instance, module_keyword)(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = module_identifier(s)?;
    let (s, e) = paren(symbol(".*"))(s)?;
    let (s, f) = symbol(";")(s)?;
    let (s, g) = opt(timeunits_declaration)(s)?;
    let (s, (h, i)) = many_till(module_item, keyword("endmodule"))(s)?;
    let (s, j) = opt(pair(symbol(":"), module_identifier))(s)?;
    Ok((
        s,
        ModuleDeclaration::Wildcard(Box::new(ModuleDeclarationWildcard {
            nodes: (a, b, c, d, e, f, g, h, i, j),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn module_declaration_extern_nonansi(s: Span) -> IResult<Span, ModuleDeclaration> {
    let (s, a) = keyword("extern")(s)?;
    let (s, b) = module_nonansi_header(s)?;
    Ok((
        s,
        ModuleDeclaration::ExternNonansi(Box::new(ModuleDeclarationExternNonansi {
            nodes: (a, b),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn module_declaration_extern_ansi(s: Span) -> IResult<Span, ModuleDeclaration> {
    let (s, a) = keyword("extern")(s)?;
    let (s, b) = module_ansi_header(s)?;
    Ok((
        s,
        ModuleDeclaration::ExternAnsi(Box::new(ModuleDeclarationExternAnsi { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn module_keyword(s: Span) -> IResult<Span, ModuleKeyword> {
    alt((
        map(keyword("module"), |x| ModuleKeyword::Module(Box::new(x))),
        map(keyword("macromodule"), |x| {
            ModuleKeyword::Macromodule(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn interface_declaration(s: Span) -> IResult<Span, InterfaceDeclaration> {
    alt((
        interface_declaration_ansi,
        interface_declaration_nonansi,
        interface_declaration_wildcard,
        interface_declaration_extern_ansi,
        interface_declaration_extern_nonansi,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn interface_declaration_nonansi(s: Span) -> IResult<Span, InterfaceDeclaration> {
    let (s, a) = interface_nonansi_header(s)?;
    let (s, b) = opt(timeunits_declaration)(s)?;
    let (s, (c, d)) = many_till(interface_item, keyword("endinterface"))(s)?;
    let (s, e) = opt(pair(symbol(":"), interface_identifier))(s)?;
    Ok((
        s,
        InterfaceDeclaration::Nonansi(Box::new(InterfaceDeclarationNonansi {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn interface_declaration_ansi(s: Span) -> IResult<Span, InterfaceDeclaration> {
    let (s, a) = interface_ansi_header(s)?;
    let (s, b) = opt(timeunits_declaration)(s)?;
    let (s, (c, d)) = many_till(non_port_interface_item, keyword("endinterface"))(s)?;
    let (s, e) = opt(pair(symbol(":"), interface_identifier))(s)?;
    Ok((
        s,
        InterfaceDeclaration::Ansi(Box::new(InterfaceDeclarationAnsi {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn interface_declaration_wildcard(s: Span) -> IResult<Span, InterfaceDeclaration> {
    let (s, (a, b)) = many_till(attribute_instance, keyword("interface"))(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = interface_identifier(s)?;
    let (s, e) = paren(symbol(".*"))(s)?;
    let (s, f) = symbol(";")(s)?;
    let (s, g) = opt(timeunits_declaration)(s)?;
    let (s, (h, i)) = many_till(interface_item, keyword("endinterface"))(s)?;
    let (s, j) = opt(pair(symbol(":"), interface_identifier))(s)?;
    Ok((
        s,
        InterfaceDeclaration::Wildcard(Box::new(InterfaceDeclarationWildcard {
            nodes: (a, b, c, d, e, f, g, h, i, j),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn interface_declaration_extern_nonansi(s: Span) -> IResult<Span, InterfaceDeclaration> {
    let (s, a) = keyword("extern")(s)?;
    let (s, b) = interface_nonansi_header(s)?;
    Ok((
        s,
        InterfaceDeclaration::ExternNonansi(Box::new(InterfaceDeclarationExternNonansi {
            nodes: (a, b),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn interface_declaration_extern_ansi(s: Span) -> IResult<Span, InterfaceDeclaration> {
    let (s, a) = keyword("extern")(s)?;
    let (s, b) = interface_ansi_header(s)?;
    Ok((
        s,
        InterfaceDeclaration::ExternAnsi(Box::new(InterfaceDeclarationExternAnsi {
            nodes: (a, b),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn interface_nonansi_header(s: Span) -> IResult<Span, InterfaceNonansiHeader> {
    let (s, (a, b)) = many_till(attribute_instance, keyword("interface"))(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = interface_identifier(s)?;
    let (s, e) = many0(package_import_declaration)(s)?;
    let (s, f) = opt(parameter_port_list)(s)?;
    let (s, g) = list_of_ports(s)?;
    let (s, h) = symbol(";")(s)?;
    Ok((
        s,
        InterfaceNonansiHeader {
            nodes: (a, b, c, d, e, f, g, h),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn interface_ansi_header(s: Span) -> IResult<Span, InterfaceAnsiHeader> {
    let (s, (a, b)) = many_till(attribute_instance, keyword("interface"))(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = interface_identifier(s)?;
    let (s, e) = many0(package_import_declaration)(s)?;
    let (s, f) = opt(parameter_port_list)(s)?;
    let (s, g) = opt(list_of_port_declarations)(s)?;
    let (s, h) = symbol(";")(s)?;
    Ok((
        s,
        InterfaceAnsiHeader {
            nodes: (a, b, c, d, e, f, g, h),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn program_declaration(s: Span) -> IResult<Span, ProgramDeclaration> {
    alt((
        program_declaration_ansi,
        program_declaration_nonansi,
        program_declaration_wildcard,
        program_declaration_extern_ansi,
        program_declaration_extern_nonansi,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn program_declaration_nonansi(s: Span) -> IResult<Span, ProgramDeclaration> {
    let (s, a) = program_nonansi_header(s)?;
    let (s, b) = opt(timeunits_declaration)(s)?;
    let (s, (c, d)) = many_till(program_item, keyword("endprogram"))(s)?;
    let (s, e) = opt(pair(symbol(":"), program_identifier))(s)?;
    Ok((
        s,
        ProgramDeclaration::Nonansi(Box::new(ProgramDeclarationNonansi {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn program_declaration_ansi(s: Span) -> IResult<Span, ProgramDeclaration> {
    let (s, a) = program_ansi_header(s)?;
    let (s, b) = opt(timeunits_declaration)(s)?;
    let (s, (c, d)) = many_till(non_port_program_item, keyword("endprogram"))(s)?;
    let (s, e) = opt(pair(symbol(":"), program_identifier))(s)?;
    Ok((
        s,
        ProgramDeclaration::Ansi(Box::new(ProgramDeclarationAnsi {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn program_declaration_wildcard(s: Span) -> IResult<Span, ProgramDeclaration> {
    let (s, (a, b)) = many_till(attribute_instance, keyword("program"))(s)?;
    let (s, c) = program_identifier(s)?;
    let (s, d) = paren(symbol(".*"))(s)?;
    let (s, e) = symbol(";")(s)?;
    let (s, f) = opt(timeunits_declaration)(s)?;
    let (s, (g, h)) = many_till(program_item, keyword("endprogram"))(s)?;
    let (s, i) = opt(pair(symbol(":"), program_identifier))(s)?;
    Ok((
        s,
        ProgramDeclaration::Wildcard(Box::new(ProgramDeclarationWildcard {
            nodes: (a, b, c, d, e, f, g, h, i),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn program_declaration_extern_nonansi(s: Span) -> IResult<Span, ProgramDeclaration> {
    let (s, a) = keyword("extern")(s)?;
    let (s, b) = program_nonansi_header(s)?;
    Ok((
        s,
        ProgramDeclaration::ExternNonansi(Box::new(ProgramDeclarationExternNonansi {
            nodes: (a, b),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn program_declaration_extern_ansi(s: Span) -> IResult<Span, ProgramDeclaration> {
    let (s, a) = keyword("extern")(s)?;
    let (s, b) = program_ansi_header(s)?;
    Ok((
        s,
        ProgramDeclaration::ExternAnsi(Box::new(ProgramDeclarationExternAnsi { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn program_nonansi_header(s: Span) -> IResult<Span, ProgramNonansiHeader> {
    let (s, (a, b)) = many_till(attribute_instance, keyword("prgogram"))(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = program_identifier(s)?;
    let (s, e) = many0(package_import_declaration)(s)?;
    let (s, f) = opt(parameter_port_list)(s)?;
    let (s, g) = list_of_ports(s)?;
    let (s, h) = symbol(";")(s)?;
    Ok((
        s,
        ProgramNonansiHeader {
            nodes: (a, b, c, d, e, f, g, h),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn program_ansi_header(s: Span) -> IResult<Span, ProgramAnsiHeader> {
    let (s, (a, b)) = many_till(attribute_instance, keyword("program"))(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = program_identifier(s)?;
    let (s, e) = many0(package_import_declaration)(s)?;
    let (s, f) = opt(parameter_port_list)(s)?;
    let (s, g) = opt(list_of_port_declarations)(s)?;
    let (s, h) = symbol(";")(s)?;
    Ok((
        s,
        ProgramAnsiHeader {
            nodes: (a, b, c, d, e, f, g, h),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn checker_declaration(s: Span) -> IResult<Span, CheckerDeclaration> {
    let (s, a) = keyword("checker")(s)?;
    let (s, b) = checker_identifier(s)?;
    let (s, c) = opt(paren(opt(checker_port_list)))(s)?;
    let (s, d) = symbol(";")(s)?;
    let (s, (e, f)) = many_till(
        pair(many0(attribute_instance), checker_or_generate_item),
        keyword("endchecker"),
    )(s)?;
    let (s, g) = opt(pair(symbol(":"), checker_identifier))(s)?;
    Ok((
        s,
        CheckerDeclaration {
            nodes: (a, b, c, d, e, f, g),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn class_declaration(s: Span) -> IResult<Span, ClassDeclaration> {
    let (s, a) = opt(map(keyword("virtual"), |x| Virtual { nodes: (x,) }))(s)?;
    let (s, b) = keyword("class")(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = class_identifier(s)?;
    let (s, e) = opt(parameter_port_list)(s)?;
    let (s, f) = opt(triple(
        keyword("extends"),
        class_type,
        opt(paren(list_of_arguments)),
    ))(s)?;
    let (s, g) = opt(pair(
        keyword("implements"),
        list(symbol(","), interface_class_type),
    ))(s)?;
    let (s, h) = symbol(";")(s)?;
    let (s, (i, j)) = many_till(class_item, keyword("endclass"))(s)?;
    let (s, k) = opt(pair(symbol(":"), class_identifier))(s)?;
    Ok((
        s,
        ClassDeclaration {
            nodes: (a, b, c, d, e, f, g, h, i, j, k),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn interface_class_type(s: Span) -> IResult<Span, InterfaceClassType> {
    let (s, a) = ps_class_identifier(s)?;
    let (s, b) = opt(parameter_value_assignment)(s)?;
    Ok((s, InterfaceClassType { nodes: (a, b) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn interface_class_declaration(s: Span) -> IResult<Span, InterfaceClassDeclaration> {
    let (s, a) = keyword("interface")(s)?;
    let (s, b) = keyword("class")(s)?;
    let (s, c) = class_identifier(s)?;
    let (s, d) = opt(parameter_port_list)(s)?;
    let (s, e) = opt(pair(
        keyword("extends"),
        list(symbol(","), interface_class_type),
    ))(s)?;
    let (s, f) = symbol(";")(s)?;
    let (s, (g, h)) = many_till(interface_class_item, keyword("endclass"))(s)?;
    let (s, i) = opt(pair(symbol(":"), class_identifier))(s)?;
    Ok((
        s,
        InterfaceClassDeclaration {
            nodes: (a, b, c, d, e, f, g, h, i),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn interface_class_item(s: Span) -> IResult<Span, InterfaceClassItem> {
    alt((
        map(type_declaration, |x| {
            InterfaceClassItem::TypeDeclaration(Box::new(x))
        }),
        interface_class_item_method,
        map(pair(local_parameter_declaration, symbol(";")), |x| {
            InterfaceClassItem::LocalParameterDeclaration(Box::new(x))
        }),
        map(pair(parameter_declaration, symbol(";")), |x| {
            InterfaceClassItem::ParameterDeclaration(Box::new(x))
        }),
        map(symbol(";"), |x| InterfaceClassItem::Null(Box::new(x))),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn interface_class_item_method(s: Span) -> IResult<Span, InterfaceClassItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = interface_class_method(s)?;
    Ok((
        s,
        InterfaceClassItem::Method(Box::new(InterfaceClassItemMethod { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn interface_class_method(s: Span) -> IResult<Span, InterfaceClassMethod> {
    let (s, a) = keyword("pure")(s)?;
    let (s, b) = keyword("virtual")(s)?;
    let (s, c) = method_prototype(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        InterfaceClassMethod {
            nodes: (a, b, c, d),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn package_declaration(s: Span) -> IResult<Span, PackageDeclaration> {
    let (s, (a, b)) = many_till(attribute_instance, keyword("package"))(s)?;
    let (s, c) = opt(lifetime)(s)?;
    let (s, d) = package_identifier(s)?;
    let (s, e) = symbol(";")(s)?;
    let (s, f) = opt(timeunits_declaration)(s)?;
    let (s, (g, h)) = many_till(
        pair(many0(attribute_instance), package_item),
        keyword("endpackage"),
    )(s)?;
    let (s, i) = opt(pair(symbol(":"), package_identifier))(s)?;
    Ok((
        s,
        PackageDeclaration {
            nodes: (a, b, c, d, e, f, g, h, i),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn timeunits_declaration(s: Span) -> IResult<Span, TimeunitsDeclaration> {
    alt((
        timeunits_declaration_timeunit_timeprecision,
        timeunits_declaration_timeunit,
        timeunits_declaration_timeprecision_timeunit,
        timeunits_declaration_timeprecision,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn timeunits_declaration_timeunit(s: Span) -> IResult<Span, TimeunitsDeclaration> {
    let (s, a) = keyword("timeunit")(s)?;
    let (s, b) = time_literal(s)?;
    let (s, c) = opt(pair(symbol("/"), time_literal))(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        TimeunitsDeclaration::Timeunit(Box::new(TimeunitsDeclarationTimeunit {
            nodes: (a, b, c, d),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn timeunits_declaration_timeprecision(s: Span) -> IResult<Span, TimeunitsDeclaration> {
    let (s, a) = keyword("timeprecision")(s)?;
    let (s, b) = time_literal(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        TimeunitsDeclaration::Timeprecision(Box::new(TimeunitsDeclarationTimeprecision {
            nodes: (a, b, c),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn timeunits_declaration_timeunit_timeprecision(
    s: Span,
) -> IResult<Span, TimeunitsDeclaration> {
    let (s, a) = keyword("timeunit")(s)?;
    let (s, b) = time_literal(s)?;
    let (s, c) = symbol(";")(s)?;
    let (s, d) = keyword("timeprecision")(s)?;
    let (s, e) = time_literal(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        TimeunitsDeclaration::TimeunitTimeprecision(Box::new(
            TimeunitsDeclarationTimeunitTimeprecision {
                nodes: (a, b, c, d, e, f),
            },
        )),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn timeunits_declaration_timeprecision_timeunit(
    s: Span,
) -> IResult<Span, TimeunitsDeclaration> {
    let (s, a) = keyword("timeprecision")(s)?;
    let (s, b) = time_literal(s)?;
    let (s, c) = symbol(";")(s)?;
    let (s, d) = keyword("timeunit")(s)?;
    let (s, e) = time_literal(s)?;
    let (s, f) = symbol(";")(s)?;
    Ok((
        s,
        TimeunitsDeclaration::TimeprecisionTimeunit(Box::new(
            TimeunitsDeclarationTimeprecisionTimeunit {
                nodes: (a, b, c, d, e, f),
            },
        )),
    ))
}
