use crate::*;

// -----------------------------------------------------------------------------

#[tracable_parser]
#[packrat_parser]
pub(crate) fn covergroup_declaration(s: Span) -> IResult<Span, CovergroupDeclaration> {
    let (s, a) = keyword("covergroup")(s)?;
    let (s, b) = covergroup_identifier(s)?;
    let (s, c) = opt(paren(opt(tf_port_list)))(s)?;
    let (s, d) = opt(coverage_event)(s)?;
    let (s, e) = symbol(";")(s)?;
    let (s, f) = many0(coverage_spec_or_option)(s)?;
    let (s, g) = keyword("endgroup")(s)?;
    let (s, h) = opt(pair(symbol(":"), covergroup_identifier))(s)?;
    Ok((
        s,
        CovergroupDeclaration {
            nodes: (a, b, c, d, e, f, g, h),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn coverage_spec_or_option(s: Span) -> IResult<Span, CoverageSpecOrOption> {
    alt((coverage_spec_or_option_spec, coverage_spec_or_option_option))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn coverage_spec_or_option_spec(s: Span) -> IResult<Span, CoverageSpecOrOption> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = coverage_spec(s)?;
    Ok((
        s,
        CoverageSpecOrOption::Spec(Box::new(CoverageSpecOrOptionSpec { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn coverage_spec_or_option_option(s: Span) -> IResult<Span, CoverageSpecOrOption> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = coverage_option(s)?;
    let (s, c) = symbol(";")(s)?;
    Ok((
        s,
        CoverageSpecOrOption::Option(Box::new(CoverageSpecOrOptionOption { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn coverage_option(s: Span) -> IResult<Span, CoverageOption> {
    alt((coverage_option_option, coverage_option_type_option))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn coverage_option_option(s: Span) -> IResult<Span, CoverageOption> {
    let (s, a) = keyword("option")(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = member_identifier(s)?;
    let (s, d) = symbol("=")(s)?;
    let (s, e) = expression(s)?;
    Ok((
        s,
        CoverageOption::Option(Box::new(CoverageOptionOption {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn coverage_option_type_option(s: Span) -> IResult<Span, CoverageOption> {
    let (s, a) = keyword("type_option")(s)?;
    let (s, b) = symbol(".")(s)?;
    let (s, c) = member_identifier(s)?;
    let (s, d) = symbol("=")(s)?;
    let (s, e) = constant_expression(s)?;
    Ok((
        s,
        CoverageOption::TypeOption(Box::new(CoverageOptionTypeOption {
            nodes: (a, b, c, d, e),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn coverage_spec(s: Span) -> IResult<Span, CoverageSpec> {
    alt((
        map(cover_point, |x| CoverageSpec::CoverPoint(Box::new(x))),
        map(cover_cross, |x| CoverageSpec::CoverCross(Box::new(x))),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn coverage_event(s: Span) -> IResult<Span, CoverageEvent> {
    alt((
        map(clocking_event, |x| {
            CoverageEvent::ClockingEvent(Box::new(x))
        }),
        coverage_event_sample,
        coverage_event_at,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn coverage_event_sample(s: Span) -> IResult<Span, CoverageEvent> {
    let (s, a) = keyword("with")(s)?;
    let (s, b) = keyword("function")(s)?;
    let (s, c) = keyword("sample")(s)?;
    let (s, d) = paren(opt(tf_port_list))(s)?;
    Ok((
        s,
        CoverageEvent::Sample(Box::new(CoverageEventSample {
            nodes: (a, b, c, d),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn coverage_event_at(s: Span) -> IResult<Span, CoverageEvent> {
    let (s, a) = symbol("@@")(s)?;
    let (s, b) = paren(block_event_expression)(s)?;
    Ok((
        s,
        CoverageEvent::At(Box::new(CoverageEventAt { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn block_event_expression(s: Span) -> IResult<Span, BlockEventExpression> {
    alt((
        block_event_expression_or,
        block_event_expression_begin,
        block_event_expression_end,
    ))(s)
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn block_event_expression_or(s: Span) -> IResult<Span, BlockEventExpression> {
    let (s, a) = block_event_expression(s)?;
    let (s, b) = keyword("or")(s)?;
    let (s, c) = block_event_expression(s)?;
    Ok((
        s,
        BlockEventExpression::Or(Box::new(BlockEventExpressionOr { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn block_event_expression_begin(s: Span) -> IResult<Span, BlockEventExpression> {
    let (s, a) = keyword("begin")(s)?;
    let (s, b) = hierarchical_btf_identifier(s)?;
    Ok((
        s,
        BlockEventExpression::Begin(Box::new(BlockEventExpressionBegin { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn block_event_expression_end(s: Span) -> IResult<Span, BlockEventExpression> {
    let (s, a) = keyword("end")(s)?;
    let (s, b) = hierarchical_btf_identifier(s)?;
    Ok((
        s,
        BlockEventExpression::End(Box::new(BlockEventExpressionEnd { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn hierarchical_btf_identifier(s: Span) -> IResult<Span, HierarchicalBtfIdentifier> {
    alt((
        map(hierarchical_tf_identifier, |x| {
            HierarchicalBtfIdentifier::HierarchicalTfIdentifier(Box::new(x))
        }),
        map(hierarchical_block_identifier, |x| {
            HierarchicalBtfIdentifier::HierarchicalBlockIdentifier(Box::new(x))
        }),
        hierarchical_btf_identifier_method,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn hierarchical_btf_identifier_method(
    s: Span,
) -> IResult<Span, HierarchicalBtfIdentifier> {
    let (s, a) = opt(hierarchical_identifier_or_class_scope)(s)?;
    let (s, b) = method_identifier(s)?;
    Ok((
        s,
        HierarchicalBtfIdentifier::Method(Box::new(HierarchicalBtfIdentifierMethod {
            nodes: (a, b),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn hierarchical_identifier_or_class_scope(
    s: Span,
) -> IResult<Span, HierarchicalIdentifierOrClassScope> {
    alt((
        map(pair(hierarchical_identifier, symbol(".")), |x| {
            HierarchicalIdentifierOrClassScope::HierarchicalIdentifier(Box::new(x))
        }),
        map(class_scope, |x| {
            HierarchicalIdentifierOrClassScope::ClassScope(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn cover_point(s: Span) -> IResult<Span, CoverPoint> {
    let (s, a) = opt(triple(
        opt(data_type_or_implicit_cover_point),
        cover_point_identifier,
        symbol(":"),
    ))(s)?;
    let (s, b) = keyword("coverpoint")(s)?;
    let (s, c) = expression(s)?;
    let (s, d) = opt(pair(keyword("iff"), paren(expression)))(s)?;
    let (s, e) = bins_or_empty(s)?;
    Ok((
        s,
        CoverPoint {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn data_type_or_implicit_cover_point(s: Span) -> IResult<Span, DataTypeOrImplicit> {
    alt((
        map(terminated(data_type, peek(cover_point_identifier)), |x| {
            DataTypeOrImplicit::DataType(Box::new(x))
        }),
        map(
            terminated(implicit_data_type, peek(cover_point_identifier)),
            |x| DataTypeOrImplicit::ImplicitDataType(Box::new(x)),
        ),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bins_or_empty(s: Span) -> IResult<Span, BinsOrEmpty> {
    alt((
        bins_or_empty_non_empty,
        map(symbol(";"), |x| BinsOrEmpty::Empty(Box::new(x))),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bins_or_empty_non_empty(s: Span) -> IResult<Span, BinsOrEmpty> {
    let (s, a) = brace(pair(
        many0(attribute_instance),
        many0(pair(bins_or_options, symbol(";"))),
    ))(s)?;
    Ok((
        s,
        BinsOrEmpty::NonEmpty(Box::new(BinsOrEmptyNonEmpty { nodes: (a,) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bins_or_options(s: Span) -> IResult<Span, BinsOrOptions> {
    alt((
        map(coverage_option, |x| {
            BinsOrOptions::CoverageOption(Box::new(x))
        }),
        bins_or_options_covergroup,
        bins_or_options_cover_point,
        bins_or_options_set_covergroup,
        bins_or_options_trans_list,
        bins_or_options_default_sequence,
        bins_or_options_default,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bins_or_options_covergroup(s: Span) -> IResult<Span, BinsOrOptions> {
    let (s, a) = opt(wildcard)(s)?;
    let (s, b) = bins_keyword(s)?;
    let (s, c) = bin_identifier(s)?;
    let (s, d) = opt(bracket(opt(covergroup_expression)))(s)?;
    let (s, e) = symbol("=")(s)?;
    let (s, f) = brace(covergroup_range_list)(s)?;
    let (s, g) = opt(pair(keyword("with"), paren(with_covergroup_expression)))(s)?;
    let (s, h) = opt(pair(keyword("iff"), paren(expression)))(s)?;
    Ok((
        s,
        BinsOrOptions::Covergroup(Box::new(BinsOrOptionsCovergroup {
            nodes: (a, b, c, d, e, f, g, h),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn wildcard(s: Span) -> IResult<Span, Wildcard> {
    let (s, a) = keyword("wildcard")(s)?;
    Ok((s, Wildcard { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bins_or_options_cover_point(s: Span) -> IResult<Span, BinsOrOptions> {
    let (s, a) = opt(wildcard)(s)?;
    let (s, b) = bins_keyword(s)?;
    let (s, c) = bin_identifier(s)?;
    let (s, d) = opt(bracket(opt(covergroup_expression)))(s)?;
    let (s, e) = symbol("=")(s)?;
    let (s, f) = cover_point_identifier(s)?;
    let (s, g) = keyword("with")(s)?;
    let (s, h) = paren(with_covergroup_expression)(s)?;
    let (s, i) = opt(pair(keyword("iff"), paren(expression)))(s)?;
    Ok((
        s,
        BinsOrOptions::CoverPoint(Box::new(BinsOrOptionsCoverPoint {
            nodes: (a, b, c, d, e, f, g, h, i),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bins_or_options_set_covergroup(s: Span) -> IResult<Span, BinsOrOptions> {
    let (s, a) = opt(wildcard)(s)?;
    let (s, b) = bins_keyword(s)?;
    let (s, c) = bin_identifier(s)?;
    let (s, d) = opt(bracket(opt(covergroup_expression)))(s)?;
    let (s, e) = symbol("=")(s)?;
    let (s, f) = set_covergroup_expression(s)?;
    let (s, g) = opt(pair(keyword("iff"), paren(expression)))(s)?;
    Ok((
        s,
        BinsOrOptions::SetCovergroup(Box::new(BinsOrOptionsSetCovergroup {
            nodes: (a, b, c, d, e, f, g),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bins_or_options_trans_list(s: Span) -> IResult<Span, BinsOrOptions> {
    let (s, a) = opt(wildcard)(s)?;
    let (s, b) = bins_keyword(s)?;
    let (s, c) = bin_identifier(s)?;
    let (s, d) = opt(pair(symbol("["), symbol("]")))(s)?;
    let (s, e) = symbol("=")(s)?;
    let (s, f) = trans_list(s)?;
    let (s, g) = opt(pair(keyword("iff"), paren(expression)))(s)?;
    Ok((
        s,
        BinsOrOptions::TransList(Box::new(BinsOrOptionsTransList {
            nodes: (a, b, c, d, e, f, g),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bins_or_options_default(s: Span) -> IResult<Span, BinsOrOptions> {
    let (s, a) = bins_keyword(s)?;
    let (s, b) = bin_identifier(s)?;
    let (s, c) = opt(bracket(opt(covergroup_expression)))(s)?;
    let (s, d) = symbol("=")(s)?;
    let (s, e) = keyword("default")(s)?;
    let (s, f) = opt(pair(keyword("iff"), paren(expression)))(s)?;
    Ok((
        s,
        BinsOrOptions::Default(Box::new(BinsOrOptionsDefault {
            nodes: (a, b, c, d, e, f),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bins_or_options_default_sequence(s: Span) -> IResult<Span, BinsOrOptions> {
    let (s, a) = bins_keyword(s)?;
    let (s, b) = bin_identifier(s)?;
    let (s, c) = symbol("=")(s)?;
    let (s, d) = keyword("default")(s)?;
    let (s, e) = keyword("sequence")(s)?;
    let (s, f) = opt(pair(keyword("iff"), paren(expression)))(s)?;
    Ok((
        s,
        BinsOrOptions::DefaultSequence(Box::new(BinsOrOptionsDefaultSequence {
            nodes: (a, b, c, d, e, f),
        })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bins_keyword(s: Span) -> IResult<Span, BinsKeyword> {
    alt((
        map(keyword("bins"), |x| BinsKeyword::Bins(Box::new(x))),
        map(keyword("illegal_bins"), |x| {
            BinsKeyword::IllegalBins(Box::new(x))
        }),
        map(keyword("ignore_bins"), |x| {
            BinsKeyword::IgnoreBins(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn trans_list(s: Span) -> IResult<Span, TransList> {
    let (s, a) = list(symbol(","), paren(trans_set))(s)?;
    Ok((s, TransList { nodes: (a,) }))
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn trans_set(s: Span) -> IResult<Span, TransSet> {
    let (s, a) = list(symbol("=>"), trans_range_list)(s)?;
    Ok((s, TransSet { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn trans_range_list(s: Span) -> IResult<Span, TransRangeList> {
    alt((
        trans_range_list_asterisk,
        trans_range_list_arrow,
        trans_range_list_equal,
        map(trans_item, |x| TransRangeList::TransItem(Box::new(x))),
    ))(s)
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn trans_range_list_asterisk(s: Span) -> IResult<Span, TransRangeList> {
    let (s, a) = trans_item(s)?;
    let (s, b) = bracket(pair(symbol("*"), repeat_range))(s)?;
    Ok((
        s,
        TransRangeList::Asterisk(Box::new(TransRangeListAsterisk { nodes: (a, b) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn trans_range_list_arrow(s: Span) -> IResult<Span, TransRangeList> {
    let (s, a) = trans_item(s)?;
    let (s, b) = bracket(pair(symbol("->"), repeat_range))(s)?;
    Ok((
        s,
        TransRangeList::Arrow(Box::new(TransRangeListArrow { nodes: (a, b) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn trans_range_list_equal(s: Span) -> IResult<Span, TransRangeList> {
    let (s, a) = trans_item(s)?;
    let (s, b) = bracket(pair(symbol("="), repeat_range))(s)?;
    Ok((
        s,
        TransRangeList::Equal(Box::new(TransRangeListEqual { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn trans_item(s: Span) -> IResult<Span, TransItem> {
    let (s, a) = covergroup_range_list(s)?;
    Ok((s, TransItem { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn repeat_range(s: Span) -> IResult<Span, RepeatRange> {
    alt((
        repeat_range_binary,
        map(covergroup_expression, |x| {
            RepeatRange::CovergroupExpression(Box::new(x))
        }),
    ))(s)
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn repeat_range_binary(s: Span) -> IResult<Span, RepeatRange> {
    let (s, a) = covergroup_expression(s)?;
    let (s, b) = symbol(":")(s)?;
    let (s, c) = covergroup_expression(s)?;
    Ok((
        s,
        RepeatRange::Binary(Box::new(RepeatRangeBinary { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn cover_cross(s: Span) -> IResult<Span, CoverCross> {
    let (s, a) = opt(pair(cross_identifier, symbol(":")))(s)?;
    let (s, b) = keyword("cross")(s)?;
    let (s, c) = list_of_cross_items(s)?;
    let (s, d) = opt(pair(keyword("iff"), paren(expression)))(s)?;
    let (s, e) = cross_body(s)?;
    Ok((
        s,
        CoverCross {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn list_of_cross_items(s: Span) -> IResult<Span, ListOfCrossItems> {
    let (s, a) = cross_item(s)?;
    let (s, b) = symbol(",")(s)?;
    let (s, c) = list(symbol(","), cross_item)(s)?;
    Ok((s, ListOfCrossItems { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn cross_item(s: Span) -> IResult<Span, CrossItem> {
    alt((
        map(cover_point_identifier, |x| {
            CrossItem::CoverPointIdentifier(Box::new(x))
        }),
        map(variable_identifier, |x| {
            CrossItem::VariableIdentifier(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn cross_body(s: Span) -> IResult<Span, CrossBody> {
    alt((
        cross_body_non_empty,
        map(symbol(";"), |x| CrossBody::Empty(Box::new(x))),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn cross_body_non_empty(s: Span) -> IResult<Span, CrossBody> {
    let (s, a) = brace(many0(cross_body_item))(s)?;
    Ok((
        s,
        CrossBody::NonEmpty(Box::new(CrossBodyNonEmpty { nodes: (a,) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn cross_body_item(s: Span) -> IResult<Span, CrossBodyItem> {
    alt((
        map(function_declaration, |x| {
            CrossBodyItem::FunctionDeclaration(Box::new(x))
        }),
        map(pair(bins_selection_or_option, symbol(";")), |x| {
            CrossBodyItem::BinsSelectionOrOption(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bins_selection_or_option(s: Span) -> IResult<Span, BinsSelectionOrOption> {
    alt((
        bins_selection_or_option_coverage,
        bins_selection_or_option_bins,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bins_selection_or_option_coverage(s: Span) -> IResult<Span, BinsSelectionOrOption> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = coverage_option(s)?;
    Ok((
        s,
        BinsSelectionOrOption::Coverage(Box::new(BinsSelectionOrOptionCoverage { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bins_selection_or_option_bins(s: Span) -> IResult<Span, BinsSelectionOrOption> {
    let (s, a) = many0(attribute_instance)(s)?;
    let (s, b) = bins_selection(s)?;
    Ok((
        s,
        BinsSelectionOrOption::Bins(Box::new(BinsSelectionOrOptionBins { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bins_selection(s: Span) -> IResult<Span, BinsSelection> {
    let (s, a) = bins_keyword(s)?;
    let (s, b) = bin_identifier(s)?;
    let (s, c) = symbol("=")(s)?;
    let (s, d) = select_expression(s)?;
    let (s, e) = opt(pair(keyword("iff"), paren(expression)))(s)?;
    Ok((
        s,
        BinsSelection {
            nodes: (a, b, c, d, e),
        },
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn select_expression(s: Span) -> IResult<Span, SelectExpression> {
    alt((
        select_expression_and,
        select_expression_or,
        select_expression_with,
        map(select_condition, |x| {
            SelectExpression::SelectCondition(Box::new(x))
        }),
        select_expression_not,
        select_expression_paren,
        select_expression_cross_set,
        map(cross_identifier, |x| {
            SelectExpression::CrossIdentifier(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn select_expression_not(s: Span) -> IResult<Span, SelectExpression> {
    let (s, a) = symbol("!")(s)?;
    let (s, b) = select_condition(s)?;
    Ok((
        s,
        SelectExpression::Not(Box::new(SelectExpressionNot { nodes: (a, b) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn select_expression_and(s: Span) -> IResult<Span, SelectExpression> {
    let (s, a) = select_expression(s)?;
    let (s, b) = symbol("&&")(s)?;
    let (s, c) = select_expression(s)?;
    Ok((
        s,
        SelectExpression::And(Box::new(SelectExpressionAnd { nodes: (a, b, c) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn select_expression_or(s: Span) -> IResult<Span, SelectExpression> {
    let (s, a) = select_expression(s)?;
    let (s, b) = symbol("||")(s)?;
    let (s, c) = select_expression(s)?;
    Ok((
        s,
        SelectExpression::Or(Box::new(SelectExpressionOr { nodes: (a, b, c) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn select_expression_paren(s: Span) -> IResult<Span, SelectExpression> {
    let (s, a) = paren(select_expression)(s)?;
    Ok((
        s,
        SelectExpression::Paren(Box::new(SelectExpressionParen { nodes: (a,) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn select_expression_with(s: Span) -> IResult<Span, SelectExpression> {
    let (s, a) = select_expression(s)?;
    let (s, b) = keyword("with")(s)?;
    let (s, c) = paren(with_covergroup_expression)(s)?;
    let (s, d) = opt(pair(keyword("matches"), integer_covergroup_expression))(s)?;
    Ok((
        s,
        SelectExpression::With(Box::new(SelectExpressionWith {
            nodes: (a, b, c, d),
        })),
    ))
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn select_expression_cross_set(s: Span) -> IResult<Span, SelectExpression> {
    let (s, a) = cross_set_expression(s)?;
    let (s, b) = opt(pair(keyword("matches"), integer_covergroup_expression))(s)?;
    Ok((
        s,
        SelectExpression::CrossSet(Box::new(SelectExpressionCrossSet { nodes: (a, b) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn select_condition(s: Span) -> IResult<Span, SelectCondition> {
    let (s, a) = keyword("binsof")(s)?;
    let (s, b) = paren(bins_expression)(s)?;
    let (s, c) = opt(pair(keyword("intersect"), brace(covergroup_range_list)))(s)?;
    Ok((s, SelectCondition { nodes: (a, b, c) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bins_expression(s: Span) -> IResult<Span, BinsExpression> {
    alt((
        bins_expression_cover_point,
        map(variable_identifier, |x| {
            BinsExpression::VariableIdentifier(Box::new(x))
        }),
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn bins_expression_cover_point(s: Span) -> IResult<Span, BinsExpression> {
    let (s, a) = cover_point_identifier(s)?;
    let (s, b) = opt(pair(symbol("."), bin_identifier))(s)?;
    Ok((
        s,
        BinsExpression::CoverPoint(Box::new(BinsExpressionCoverPoint { nodes: (a, b) })),
    ))
}

#[recursive_parser]
#[tracable_parser]
#[packrat_parser]
pub(crate) fn covergroup_range_list(s: Span) -> IResult<Span, CovergroupRangeList> {
    let (s, a) = list(symbol(","), covergroup_value_range)(s)?;
    Ok((s, CovergroupRangeList { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn covergroup_value_range(s: Span) -> IResult<Span, CovergroupValueRange> {
    alt((
        map(covergroup_expression, |x| {
            CovergroupValueRange::CovergroupExpression(Box::new(x))
        }),
        covergroup_value_range_binary,
    ))(s)
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn covergroup_value_range_binary(s: Span) -> IResult<Span, CovergroupValueRange> {
    let (s, a) = bracket(triple(
        covergroup_expression,
        symbol(":"),
        covergroup_expression,
    ))(s)?;
    Ok((
        s,
        CovergroupValueRange::Binary(Box::new(CovergroupValueRangeBinary { nodes: (a,) })),
    ))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn with_covergroup_expression(s: Span) -> IResult<Span, WithCovergroupExpression> {
    let (s, a) = covergroup_expression(s)?;
    Ok((s, WithCovergroupExpression { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn set_covergroup_expression(s: Span) -> IResult<Span, SetCovergroupExpression> {
    let (s, a) = covergroup_expression(s)?;
    Ok((s, SetCovergroupExpression { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn integer_covergroup_expression(s: Span) -> IResult<Span, IntegerCovergroupExpression> {
    let (s, a) = covergroup_expression(s)?;
    Ok((s, IntegerCovergroupExpression { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn cross_set_expression(s: Span) -> IResult<Span, CrossSetExpression> {
    let (s, a) = covergroup_expression(s)?;
    Ok((s, CrossSetExpression { nodes: (a,) }))
}

#[tracable_parser]
#[packrat_parser]
pub(crate) fn covergroup_expression(s: Span) -> IResult<Span, CovergroupExpression> {
    let (s, a) = expression(s)?;
    Ok((s, CovergroupExpression { nodes: (a,) }))
}
