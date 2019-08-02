use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
pub(crate) fn concurrent_assertion_item(s: Span) -> IResult<Span, ConcurrentAssertionItem> {
    alt((
        concurrent_assertion_item_statement,
        map(checker_instantiation, |x| {
            ConcurrentAssertionItem::CheckerInstantiation(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn concurrent_assertion_item_statement(
    s: Span,
) -> IResult<Span, ConcurrentAssertionItem> {
    let (s, a) = opt(pair(block_identifier, symbol(":")))(s)?;
    let (s, b) = concurrent_assertion_statement(s)?;
    Ok((
        s,
        ConcurrentAssertionItem::Statement(Box::new(ConcurrentAssertionItemStatement {
            nodes: (a, b),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn concurrent_assertion_statement(
    s: Span,
) -> IResult<Span, ConcurrentAssertionStatement> {
    alt((
        map(assert_property_statement, |x| {
            ConcurrentAssertionStatement::AssertPropertyStatement(Box::new(x))
        }),
        map(assume_property_statement, |x| {
            ConcurrentAssertionStatement::AssumePropertyStatement(Box::new(x))
        }),
        map(cover_property_statement, |x| {
            ConcurrentAssertionStatement::CoverPropertyStatement(Box::new(x))
        }),
        map(cover_sequence_statement, |x| {
            ConcurrentAssertionStatement::CoverSequenceStatement(Box::new(x))
        }),
        map(restrict_property_statement, |x| {
            ConcurrentAssertionStatement::RestrictPropertyStatement(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn assert_property_statement(s: Span) -> IResult<Span, AssertPropertyStatement> {
    let (s, a) = keyword("assert")(s)?;
    let (s, b) = keyword("property")(s)?;
    let (s, c) = paren(property_spec)(s)?;
    let (s, d) = action_block(s)?;
    Ok((
        s,
        AssertPropertyStatement {
            nodes: (a, b, c, d),
        },
    ))
}

#[tracable_parser]
pub(crate) fn assume_property_statement(s: Span) -> IResult<Span, AssumePropertyStatement> {
    let (s, a) = keyword("assume")(s)?;
    let (s, b) = keyword("property")(s)?;
    let (s, c) = paren(property_spec)(s)?;
    let (s, d) = action_block(s)?;
    Ok((
        s,
        AssumePropertyStatement {
            nodes: (a, b, c, d),
        },
    ))
}

#[tracable_parser]
pub(crate) fn cover_property_statement(s: Span) -> IResult<Span, CoverPropertyStatement> {
    let (s, a) = keyword("cover")(s)?;
    let (s, b) = keyword("property")(s)?;
    let (s, c) = paren(property_spec)(s)?;
    let (s, d) = statement_or_null(s)?;
    Ok((
        s,
        CoverPropertyStatement {
            nodes: (a, b, c, d),
        },
    ))
}

#[tracable_parser]
pub(crate) fn expect_property_statement(s: Span) -> IResult<Span, ExpectPropertyStatement> {
    let (s, a) = keyword("expect")(s)?;
    let (s, b) = paren(property_spec)(s)?;
    let (s, c) = action_block(s)?;
    Ok((s, ExpectPropertyStatement { nodes: (a, b, c) }))
}

#[tracable_parser]
pub(crate) fn cover_sequence_statement(s: Span) -> IResult<Span, CoverSequenceStatement> {
    let (s, a) = keyword("cover")(s)?;
    let (s, b) = keyword("sequence")(s)?;
    let (s, c) = paren(triple(
        opt(clocking_event),
        opt(triple(
            keyword("disable"),
            keyword("iff"),
            paren(expression_or_dist),
        )),
        sequence_expr,
    ))(s)?;
    let (s, d) = statement_or_null(s)?;
    Ok((
        s,
        CoverSequenceStatement {
            nodes: (a, b, c, d),
        },
    ))
}

#[tracable_parser]
pub(crate) fn restrict_property_statement(s: Span) -> IResult<Span, RestrictPropertyStatement> {
    let (s, a) = keyword("restrict")(s)?;
    let (s, b) = keyword("property")(s)?;
    let (s, c) = paren(property_spec)(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        RestrictPropertyStatement {
            nodes: (a, b, c, d),
        },
    ))
}

#[tracable_parser]
pub(crate) fn property_instance(s: Span) -> IResult<Span, PropertyInstance> {
    let (s, a) = ps_or_hierarchical_property_identifier(s)?;
    let (s, b) = opt(paren(opt(property_list_of_arguments)))(s)?;
    Ok((s, PropertyInstance { nodes: (a, b) }))
}

#[tracable_parser]
pub(crate) fn property_list_of_arguments(s: Span) -> IResult<Span, PropertyListOfArguments> {
    alt((
        property_list_of_arguments_named,
        property_list_of_arguments_ordered,
    ))(s)
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn property_list_of_arguments_ordered(
    s: Span,
) -> IResult<Span, PropertyListOfArguments> {
    let (s, a) = list(symbol(","), opt(property_actual_arg))(s)?;
    let (s, b) = many0(tuple((
        symbol(","),
        symbol("."),
        identifier,
        paren(opt(property_actual_arg)),
    )))(s)?;
    Ok((
        s,
        PropertyListOfArguments::Ordered(Box::new(PropertyListOfArgumentsOrdered {
            nodes: (a, b),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn property_list_of_arguments_named(s: Span) -> IResult<Span, PropertyListOfArguments> {
    let (s, a) = list(
        symbol(","),
        triple(symbol("."), identifier, paren(opt(property_actual_arg))),
    )(s)?;
    Ok((
        s,
        PropertyListOfArguments::Named(Box::new(PropertyListOfArgumentsNamed { nodes: (a,) })),
    ))
}

#[tracable_parser]
pub(crate) fn property_actual_arg(s: Span) -> IResult<Span, PropertyActualArg> {
    alt((
        map(property_expr, |x| {
            PropertyActualArg::PropertyExpr(Box::new(x))
        }),
        map(sequence_actual_arg, |x| {
            PropertyActualArg::SequenceActualArg(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn assertion_item_declaration(s: Span) -> IResult<Span, AssertionItemDeclaration> {
    alt((
        map(property_declaration, |x| {
            AssertionItemDeclaration::PropertyDeclaration(Box::new(x))
        }),
        map(sequence_declaration, |x| {
            AssertionItemDeclaration::SequenceDeclaration(Box::new(x))
        }),
        map(let_declaration, |x| {
            AssertionItemDeclaration::LetDeclaration(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn property_declaration(s: Span) -> IResult<Span, PropertyDeclaration> {
    let (s, a) = keyword("property")(s)?;
    let (s, b) = property_identifier(s)?;
    let (s, c) = opt(paren(opt(property_port_list)))(s)?;
    let (s, d) = symbol(";")(s)?;
    let (s, e) = many0(assertion_variable_declaration)(s)?;
    let (s, f) = property_spec(s)?;
    let (s, g) = opt(symbol(";"))(s)?;
    let (s, h) = keyword("endproperty")(s)?;
    let (s, i) = opt(pair(symbol(":"), property_identifier))(s)?;
    Ok((
        s,
        PropertyDeclaration {
            nodes: (a, b, c, d, e, f, g, h, i),
        },
    ))
}

#[tracable_parser]
pub(crate) fn property_port_list(s: Span) -> IResult<Span, PropertyPortList> {
    let (s, a) = list(symbol(","), property_port_item)(s)?;
    Ok((s, PropertyPortList { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn property_port_item(s: Span) -> IResult<Span, PropertyPortItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = opt(pair(local, opt(property_lvar_port_direction)))(s)?;
    let (s, c) = property_formal_type(s)?;
    let (s, d) = formal_port_identifier(s)?;
    let (s, e) = many0(variable_dimension)(s)?;
    let (s, f) = opt(pair(symbol("="), property_actual_arg))(s)?;
    Ok((
        s,
        PropertyPortItem {
            nodes: (a, b, c, d, e, f),
        },
    ))
}

#[tracable_parser]
pub(crate) fn property_lvar_port_direction(s: Span) -> IResult<Span, PropertyLvarPortDirection> {
    let (s, a) = keyword("input")(s)?;
    Ok((s, PropertyLvarPortDirection::Input(Box::new(a))))
}

#[tracable_parser]
pub(crate) fn property_formal_type(s: Span) -> IResult<Span, PropertyFormalType> {
    alt((
        map(sequence_formal_type, |x| {
            PropertyFormalType::SequenceFormalType(Box::new(x))
        }),
        map(keyword("property"), |x| {
            PropertyFormalType::Property(Box::new(x))
        }),
    ))(s)
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn property_spec(s: Span) -> IResult<Span, PropertySpec> {
    let (s, a) = opt(clocking_event)(s)?;
    let (s, b) = opt(triple(
        keyword("disable"),
        keyword("iff"),
        paren(expression_or_dist),
    ))(s)?;
    let (s, c) = property_expr(s)?;
    Ok((s, PropertySpec { nodes: (a, b, c) }))
}

#[tracable_parser]
pub(crate) fn property_expr(s: Span) -> IResult<Span, PropertyExpr> {
    alt((
        alt((
            property_expr_implication_overlapped,
            property_expr_implication_nonoverlapped,
            property_expr_followed_by_overlapped,
            property_expr_followed_by_nonoverlapped,
            map(sequence_expr, |x| PropertyExpr::SequenceExpr(Box::new(x))),
            property_expr_strong,
            property_expr_weak,
            property_expr_paren,
            property_expr_not,
            property_expr_or,
            property_expr_and,
            property_expr_if,
            property_expr_case,
            property_expr_nexttime,
            property_expr_s_nexttime,
        )),
        alt((
            property_expr_always,
            property_expr_s_always,
            property_expr_eventually,
            property_expr_s_eventually,
            property_expr_until,
            property_expr_s_until,
            property_expr_until_with,
            property_expr_s_until_with,
            property_expr_implies,
            property_expr_iff,
            property_expr_accept_on,
            property_expr_reject_on,
            property_expr_sync_accept_on,
            property_expr_sync_reject_on,
            map(property_instance, |x| {
                PropertyExpr::PropertyInstance(Box::new(x))
            }),
            property_expr_clocking_event,
        )),
    ))(s)
}

#[tracable_parser]
pub(crate) fn property_expr_strong(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = keyword("strong")(s)?;
    let (s, b) = paren(sequence_expr)(s)?;
    Ok((
        s,
        PropertyExpr::Strong(Box::new(PropertyExprStrong { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn property_expr_weak(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = keyword("weak")(s)?;
    let (s, b) = paren(sequence_expr)(s)?;
    Ok((
        s,
        PropertyExpr::Strong(Box::new(PropertyExprStrong { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn property_expr_paren(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = paren(sequence_expr)(s)?;
    Ok((
        s,
        PropertyExpr::Paren(Box::new(PropertyExprParen { nodes: (a,) })),
    ))
}

#[tracable_parser]
pub(crate) fn property_expr_not(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = keyword("not")(s)?;
    let (s, b) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::Not(Box::new(PropertyExprNot { nodes: (a, b) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn property_expr_or(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = property_expr(s)?;
    let (s, b) = keyword("or")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::Or(Box::new(PropertyExprOr { nodes: (a, b, c) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn property_expr_and(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = property_expr(s)?;
    let (s, b) = keyword("and")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::And(Box::new(PropertyExprAnd { nodes: (a, b, c) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn property_expr_implication_overlapped(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = sequence_expr(s)?;
    let (s, b) = symbol("|->")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::ImplicationOverlapped(Box::new(PropertyExprImplicationOverlapped {
            nodes: (a, b, c),
        })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn property_expr_implication_nonoverlapped(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = sequence_expr(s)?;
    let (s, b) = symbol("|=>")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::ImplicationNonoverlapped(Box::new(PropertyExprImplicationNonoverlapped {
            nodes: (a, b, c),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn property_expr_if(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = keyword("if")(s)?;
    let (s, b) = paren(expression_or_dist)(s)?;
    let (s, c) = property_expr(s)?;
    let (s, d) = opt(pair(keyword("else"), property_expr))(s)?;
    Ok((
        s,
        PropertyExpr::If(Box::new(PropertyExprIf {
            nodes: (a, b, c, d),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn property_expr_case(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = keyword("case")(s)?;
    let (s, b) = paren(expression_or_dist)(s)?;
    let (s, c) = property_case_item(s)?;
    let (s, d) = many0(property_case_item)(s)?;
    let (s, e) = keyword("endcase")(s)?;
    Ok((
        s,
        PropertyExpr::Case(Box::new(PropertyExprCase {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn property_expr_followed_by_overlapped(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = sequence_expr(s)?;
    let (s, b) = symbol("#-#")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::FollowedByOverlapped(Box::new(PropertyExprFollowedByOverlapped {
            nodes: (a, b, c),
        })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn property_expr_followed_by_nonoverlapped(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = sequence_expr(s)?;
    let (s, b) = symbol("#=#")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::FollowedByNonoverlapped(Box::new(PropertyExprFollowedByNonoverlapped {
            nodes: (a, b, c),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn property_expr_nexttime(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = keyword("nexttime")(s)?;
    let (s, b) = opt(bracket(constant_expression))(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::Nexttime(Box::new(PropertyExprNexttime { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn property_expr_s_nexttime(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = keyword("s_nexttime")(s)?;
    let (s, b) = opt(bracket(constant_expression))(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::SNexttime(Box::new(PropertyExprSNexttime { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn property_expr_always(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = keyword("always")(s)?;
    let (s, b) = opt(bracket(cycle_delay_const_range_expression))(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::Always(Box::new(PropertyExprAlways { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn property_expr_s_always(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = keyword("s_always")(s)?;
    let (s, b) = bracket(cycle_delay_const_range_expression)(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::SAlways(Box::new(PropertyExprSAlways { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn property_expr_eventually(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = keyword("eventually")(s)?;
    let (s, b) = bracket(constant_range)(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::Eventually(Box::new(PropertyExprEventually { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn property_expr_s_eventually(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = keyword("s_eventually")(s)?;
    let (s, b) = opt(bracket(cycle_delay_const_range_expression))(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::SEventually(Box::new(PropertyExprSEventually { nodes: (a, b, c) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn property_expr_until(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = property_expr(s)?;
    let (s, b) = keyword("until")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::Until(Box::new(PropertyExprUntil { nodes: (a, b, c) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn property_expr_s_until(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = property_expr(s)?;
    let (s, b) = keyword("s_until")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::SUntil(Box::new(PropertyExprSUntil { nodes: (a, b, c) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn property_expr_until_with(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = property_expr(s)?;
    let (s, b) = keyword("until_with")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::UntilWith(Box::new(PropertyExprUntilWith { nodes: (a, b, c) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn property_expr_s_until_with(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = property_expr(s)?;
    let (s, b) = keyword("s_until_with")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::SUntilWith(Box::new(PropertyExprSUntilWith { nodes: (a, b, c) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn property_expr_implies(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = property_expr(s)?;
    let (s, b) = keyword("implies")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::Implies(Box::new(PropertyExprImplies { nodes: (a, b, c) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn property_expr_iff(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = property_expr(s)?;
    let (s, b) = keyword("iff")(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::Iff(Box::new(PropertyExprIff { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn property_expr_accept_on(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = keyword("accept_on")(s)?;
    let (s, b) = paren(expression_or_dist)(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::AcceptOn(Box::new(PropertyExprAcceptOn { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn property_expr_reject_on(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = keyword("reject_on")(s)?;
    let (s, b) = paren(expression_or_dist)(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::RejectOn(Box::new(PropertyExprRejectOn { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn property_expr_sync_accept_on(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = keyword("sync_accept_on")(s)?;
    let (s, b) = paren(expression_or_dist)(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::SyncAcceptOn(Box::new(PropertyExprSyncAcceptOn { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn property_expr_sync_reject_on(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = keyword("sync_reject_on")(s)?;
    let (s, b) = paren(expression_or_dist)(s)?;
    let (s, c) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::SyncRejectOn(Box::new(PropertyExprSyncRejectOn { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn property_expr_clocking_event(s: Span) -> IResult<Span, PropertyExpr> {
    let (s, a) = clocking_event(s)?;
    let (s, b) = property_expr(s)?;
    Ok((
        s,
        PropertyExpr::ClockingEvent(Box::new(PropertyExprClockingEvent { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn property_case_item(s: Span) -> IResult<Span, PropertyCaseItem> {
    alt((property_case_item_nondefault, property_case_item_default))(s)
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn property_case_item_nondefault(s: Span) -> IResult<Span, PropertyCaseItem> {
    let (s, a) = list(symbol(","), expression_or_dist)(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = property_expr(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        PropertyCaseItem::Nondefault(Box::new(PropertyCaseItemNondefault {
            nodes: (a, b, c, d),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn property_case_item_default(s: Span) -> IResult<Span, PropertyCaseItem> {
    let (s, a) = keyword("default")(s)?;
    let (s, b) = opt(symbol(":"))(s)?;
    let (s, c) = property_expr(s)?;
    let (s, d) = symbol(";")(s)?;
    Ok((
        s,
        PropertyCaseItem::Default(Box::new(PropertyCaseItemDefault {
            nodes: (a, b, c, d),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn sequence_declaration(s: Span) -> IResult<Span, SequenceDeclaration> {
    let (s, a) = keyword("sequence")(s)?;
    let (s, b) = sequence_identifier(s)?;
    let (s, c) = opt(paren(opt(sequence_port_list)))(s)?;
    let (s, d) = symbol(";")(s)?;
    let (s, e) = many0(assertion_variable_declaration)(s)?;
    let (s, f) = sequence_expr(s)?;
    let (s, g) = opt(symbol(";"))(s)?;
    let (s, h) = keyword("endsequence")(s)?;
    let (s, i) = opt(pair(symbol(":"), sequence_identifier))(s)?;
    Ok((
        s,
        SequenceDeclaration {
            nodes: (a, b, c, d, e, f, g, h, i),
        },
    ))
}

#[tracable_parser]
pub(crate) fn sequence_port_list(s: Span) -> IResult<Span, SequencePortList> {
    let (s, a) = list(symbol(","), sequence_port_item)(s)?;
    Ok((s, SequencePortList { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn sequence_port_item(s: Span) -> IResult<Span, SequencePortItem> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = opt(pair(local, opt(sequence_lvar_port_direction)))(s)?;
    let (s, c) = sequence_formal_type(s)?;
    let (s, d) = formal_port_identifier(s)?;
    let (s, e) = many0(variable_dimension)(s)?;
    let (s, f) = opt(pair(symbol("="), sequence_actual_arg))(s)?;
    Ok((
        s,
        SequencePortItem {
            nodes: (a, b, c, d, e, f),
        },
    ))
}

#[tracable_parser]
pub(crate) fn sequence_lvar_port_direction(s: Span) -> IResult<Span, SequenceLvarPortDirection> {
    alt((
        map(keyword("input"), |x| {
            SequenceLvarPortDirection::Input(Box::new(x))
        }),
        map(keyword("inout"), |x| {
            SequenceLvarPortDirection::Inout(Box::new(x))
        }),
        map(keyword("output"), |x| {
            SequenceLvarPortDirection::Output(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn sequence_formal_type(s: Span) -> IResult<Span, SequenceFormalType> {
    alt((
        map(data_type_or_implicit_sequence_formal_type, |x| {
            SequenceFormalType::DataTypeOrImplicit(Box::new(x))
        }),
        map(keyword("sequence"), |x| {
            SequenceFormalType::Sequence(Box::new(x))
        }),
        map(keyword("untyped"), |x| {
            SequenceFormalType::Untyped(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn data_type_or_implicit_sequence_formal_type(
    s: Span,
) -> IResult<Span, DataTypeOrImplicit> {
    alt((
        map(terminated(data_type, peek(formal_port_identifier)), |x| {
            DataTypeOrImplicit::DataType(Box::new(x))
        }),
        map(
            terminated(implicit_data_type, peek(formal_port_identifier)),
            |x| DataTypeOrImplicit::ImplicitDataType(Box::new(x)),
        ),
    ))(s)
}

#[tracable_parser]
pub(crate) fn sequence_expr(s: Span) -> IResult<Span, SequenceExpr> {
    alt((
        sequence_expr_cycle_delay_expr,
        sequence_expr_expr_cycle_delay_expr,
        sequence_expr_expression,
        sequence_expr_instance,
        sequence_expr_paren,
        sequence_expr_and,
        sequence_expr_intersect,
        sequence_expr_or,
        sequence_expr_first_match,
        sequence_expr_throughout,
        sequence_expr_within,
        sequence_expr_clocking_event,
    ))(s)
}

#[tracable_parser]
pub(crate) fn sequence_expr_cycle_delay_expr(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = cycle_delay_range(s)?;
    let (s, b) = sequence_expr(s)?;
    let (s, c) = many0(pair(cycle_delay_range, sequence_expr))(s)?;
    Ok((
        s,
        SequenceExpr::CycleDelayExpr(Box::new(SequenceExprCycleDelayExpr { nodes: (a, b, c) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn sequence_expr_expr_cycle_delay_expr(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = sequence_expr(s)?;
    let (s, b) = cycle_delay_range(s)?;
    let (s, c) = sequence_expr(s)?;
    let (s, d) = many0(pair(cycle_delay_range, sequence_expr))(s)?;
    Ok((
        s,
        SequenceExpr::ExprCycleDelayExpr(Box::new(SequenceExprExprCycleDelayExpr {
            nodes: (a, b, c, d),
        })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn sequence_expr_expression(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = expression_or_dist(s)?;
    let (s, b) = opt(boolean_abbrev)(s)?;
    Ok((
        s,
        SequenceExpr::Expression(Box::new(SequenceExprExpression { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn sequence_expr_instance(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = sequence_instance(s)?;
    let (s, b) = opt(sequence_abbrev)(s)?;
    Ok((
        s,
        SequenceExpr::Instance(Box::new(SequenceExprInstance { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn sequence_expr_paren(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = paren(pair(
        sequence_expr,
        many0(pair(symbol(","), sequence_match_item)),
    ))(s)?;
    let (s, b) = opt(sequence_abbrev)(s)?;
    Ok((
        s,
        SequenceExpr::Paren(Box::new(SequenceExprParen { nodes: (a, b) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn sequence_expr_and(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = sequence_expr(s)?;
    let (s, b) = keyword("and")(s)?;
    let (s, c) = sequence_expr(s)?;
    Ok((
        s,
        SequenceExpr::And(Box::new(SequenceExprAnd { nodes: (a, b, c) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn sequence_expr_intersect(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = sequence_expr(s)?;
    let (s, b) = keyword("intersect")(s)?;
    let (s, c) = sequence_expr(s)?;
    Ok((
        s,
        SequenceExpr::Intersect(Box::new(SequenceExprIntersect { nodes: (a, b, c) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn sequence_expr_or(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = sequence_expr(s)?;
    let (s, b) = keyword("or")(s)?;
    let (s, c) = sequence_expr(s)?;
    Ok((
        s,
        SequenceExpr::Or(Box::new(SequenceExprOr { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn sequence_expr_first_match(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = keyword("first_match")(s)?;
    let (s, b) = paren(pair(
        sequence_expr,
        many0(pair(symbol(","), sequence_match_item)),
    ))(s)?;
    Ok((
        s,
        SequenceExpr::FirstMatch(Box::new(SequenceExprFirstMatch { nodes: (a, b) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn sequence_expr_throughout(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = expression_or_dist(s)?;
    let (s, b) = keyword("throughout")(s)?;
    let (s, c) = sequence_expr(s)?;
    Ok((
        s,
        SequenceExpr::Throughout(Box::new(SequenceExprThroughout { nodes: (a, b, c) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn sequence_expr_within(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = sequence_expr(s)?;
    let (s, b) = keyword("within")(s)?;
    let (s, c) = sequence_expr(s)?;
    Ok((
        s,
        SequenceExpr::Within(Box::new(SequenceExprWithin { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
pub(crate) fn sequence_expr_clocking_event(s: Span) -> IResult<Span, SequenceExpr> {
    let (s, a) = clocking_event(s)?;
    let (s, b) = sequence_expr(s)?;
    Ok((
        s,
        SequenceExpr::ClockingEvent(Box::new(SequenceExprClockingEvent { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn cycle_delay_range(s: Span) -> IResult<Span, CycleDelayRange> {
    alt((
        cycle_delay_range_primary,
        cycle_delay_range_expression,
        cycle_delay_range_asterisk,
        cycle_delay_range_plus,
    ))(s)
}

#[tracable_parser]
pub(crate) fn cycle_delay_range_primary(s: Span) -> IResult<Span, CycleDelayRange> {
    let (s, a) = symbol("##")(s)?;
    let (s, b) = constant_primary(s)?;
    Ok((
        s,
        CycleDelayRange::Primary(Box::new(CycleDelayRangePrimary { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn cycle_delay_range_expression(s: Span) -> IResult<Span, CycleDelayRange> {
    let (s, a) = symbol("##")(s)?;
    let (s, b) = bracket(cycle_delay_const_range_expression)(s)?;
    Ok((
        s,
        CycleDelayRange::Expression(Box::new(CycleDelayRangeExpression { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn cycle_delay_range_asterisk(s: Span) -> IResult<Span, CycleDelayRange> {
    let (s, a) = symbol("##")(s)?;
    let (s, b) = bracket(symbol("*"))(s)?;
    Ok((
        s,
        CycleDelayRange::Asterisk(Box::new(CycleDelayRangeAsterisk { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn cycle_delay_range_plus(s: Span) -> IResult<Span, CycleDelayRange> {
    let (s, a) = symbol("##")(s)?;
    let (s, b) = bracket(symbol("+"))(s)?;
    Ok((
        s,
        CycleDelayRange::Plus(Box::new(CycleDelayRangePlus { nodes: (a, b) })),
    ))
}

#[tracable_parser]
pub(crate) fn sequence_method_call(s: Span) -> IResult<Span, SequenceMethodCall> {
    let (s, a) = sequence_instance(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = method_identifier(s)?;
    Ok((s, SequenceMethodCall { nodes: (a, b, c) }))
}

#[tracable_parser]
pub(crate) fn sequence_match_item(s: Span) -> IResult<Span, SequenceMatchItem> {
    alt((
        map(operator_assignment, |x| {
            SequenceMatchItem::OperatorAssignment(Box::new(x))
        }),
        map(inc_or_dec_expression, |x| {
            SequenceMatchItem::IncOrDecExpression(Box::new(x))
        }),
        map(subroutine_call, |x| {
            SequenceMatchItem::SubroutineCall(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn sequence_instance(s: Span) -> IResult<Span, SequenceInstance> {
    let (s, a) = ps_or_hierarchical_sequence_identifier(s)?;
    let (s, b) = opt(paren(opt(sequence_list_of_arguments)))(s)?;
    Ok((s, SequenceInstance { nodes: (a, b) }))
}

#[tracable_parser]
pub(crate) fn sequence_list_of_arguments(s: Span) -> IResult<Span, SequenceListOfArguments> {
    alt((
        sequence_list_of_arguments_named,
        sequence_list_of_arguments_ordered,
    ))(s)
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn sequence_list_of_arguments_ordered(
    s: Span,
) -> IResult<Span, SequenceListOfArguments> {
    let (s, a) = list(symbol(","), opt(sequence_actual_arg))(s)?;
    let (s, b) = many0(tuple((
        symbol(","),
        symbol("."),
        identifier,
        paren(opt(sequence_actual_arg)),
    )))(s)?;
    Ok((
        s,
        SequenceListOfArguments::Ordered(Box::new(SequenceListOfArgumentsOrdered {
            nodes: (a, b),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn sequence_list_of_arguments_named(s: Span) -> IResult<Span, SequenceListOfArguments> {
    let (s, a) = list(
        symbol(","),
        triple(symbol("."), identifier, paren(opt(sequence_actual_arg))),
    )(s)?;
    Ok((
        s,
        SequenceListOfArguments::Named(Box::new(SequenceListOfArgumentsNamed { nodes: (a,) })),
    ))
}

#[tracable_parser]
pub(crate) fn sequence_actual_arg(s: Span) -> IResult<Span, SequenceActualArg> {
    alt((
        map(event_expression, |x| {
            SequenceActualArg::EventExpression(Box::new(x))
        }),
        map(sequence_expr, |x| {
            SequenceActualArg::SequenceExpr(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn boolean_abbrev(s: Span) -> IResult<Span, BooleanAbbrev> {
    alt((
        map(consecutive_repetition, |x| {
            BooleanAbbrev::ConsecutiveRepetition(Box::new(x))
        }),
        map(non_consecutive_repetition, |x| {
            BooleanAbbrev::NonConsecutiveRepetition(Box::new(x))
        }),
        map(goto_repetition, |x| {
            BooleanAbbrev::GotoRepetition(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn sequence_abbrev(s: Span) -> IResult<Span, SequenceAbbrev> {
    let (s, a) = consecutive_repetition(s)?;
    Ok((s, SequenceAbbrev { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn consecutive_repetition(s: Span) -> IResult<Span, ConsecutiveRepetition> {
    alt((
        consecutive_repetition_expression,
        consecutive_repetition_asterisk,
        consecutive_repetition_plus,
    ))(s)
}

#[tracable_parser]
pub(crate) fn consecutive_repetition_expression(s: Span) -> IResult<Span, ConsecutiveRepetition> {
    let (s, a) = bracket(pair(symbol("*"), const_or_range_expression))(s)?;
    Ok((
        s,
        ConsecutiveRepetition::Expression(Box::new(ConsecutiveRepetitionExpression {
            nodes: (a,),
        })),
    ))
}

#[tracable_parser]
pub(crate) fn consecutive_repetition_asterisk(s: Span) -> IResult<Span, ConsecutiveRepetition> {
    let (s, a) = bracket(symbol("*"))(s)?;
    Ok((
        s,
        ConsecutiveRepetition::Asterisk(Box::new(ConsecutiveRepetitionAsterisk { nodes: (a,) })),
    ))
}

#[tracable_parser]
pub(crate) fn consecutive_repetition_plus(s: Span) -> IResult<Span, ConsecutiveRepetition> {
    let (s, a) = bracket(symbol("+"))(s)?;
    Ok((
        s,
        ConsecutiveRepetition::Plus(Box::new(ConsecutiveRepetitionPlus { nodes: (a,) })),
    ))
}

#[tracable_parser]
pub(crate) fn non_consecutive_repetition(s: Span) -> IResult<Span, NonConsecutiveRepetition> {
    let (s, a) = bracket(pair(symbol("="), const_or_range_expression))(s)?;
    Ok((s, NonConsecutiveRepetition { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn goto_repetition(s: Span) -> IResult<Span, GotoRepetition> {
    let (s, a) = bracket(pair(symbol("->"), const_or_range_expression))(s)?;
    Ok((s, GotoRepetition { nodes: (a,) }))
}

#[tracable_parser]
pub(crate) fn const_or_range_expression(s: Span) -> IResult<Span, ConstOrRangeExpression> {
    alt((
        map(cycle_delay_const_range_expression, |x| {
            ConstOrRangeExpression::CycleDelayConstRangeExpression(Box::new(x))
        }),
        map(constant_expression, |x| {
            ConstOrRangeExpression::ConstantExpression(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
pub(crate) fn cycle_delay_const_range_expression(
    s: Span,
) -> IResult<Span, CycleDelayConstRangeExpression> {
    alt((
        cycle_delay_const_range_expression_binary,
        cycle_delay_const_range_expression_dollar,
    ))(s)
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn cycle_delay_const_range_expression_binary(
    s: Span,
) -> IResult<Span, CycleDelayConstRangeExpression> {
    let (s, a) = constant_expression(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = constant_expression(s)?;
    Ok((
        s,
        CycleDelayConstRangeExpression::Binary(Box::new(CycleDelayConstRangeExpressionBinary {
            nodes: (a, b, c),
        })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn cycle_delay_const_range_expression_dollar(
    s: Span,
) -> IResult<Span, CycleDelayConstRangeExpression> {
    let (s, a) = constant_expression(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = symbol("$")(s)?;
    Ok((
        s,
        CycleDelayConstRangeExpression::Dollar(Box::new(CycleDelayConstRangeExpressionDollar {
            nodes: (a, b, c),
        })),
    ))
}

#[recursive_parser]
#[tracable_parser]
pub(crate) fn expression_or_dist(s: Span) -> IResult<Span, ExpressionOrDist> {
    let (s, a) = expression(s)?;
    let (s, b) = opt(pair(keyword("dist"), brace(dist_list)))(s)?;
    Ok((s, ExpressionOrDist { nodes: (a, b) }))
}

#[tracable_parser]
pub(crate) fn assertion_variable_declaration(
    s: Span,
) -> IResult<Span, AssertionVariableDeclaration> {
    let (s, a) = var_data_type(s)?;
    let (s, b) = list_of_variable_decl_assignments(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((s, AssertionVariableDeclaration { nodes: (a, b, c) }))
}
