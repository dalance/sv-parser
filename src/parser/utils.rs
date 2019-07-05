use crate::parser::*;
use nom::bytes::complete::*;
use nom::character::complete::*;
use nom::IResult;

// -----------------------------------------------------------------------------

pub fn ws<'a, O, F>(f: F) -> impl Fn(&'a str) -> IResult<&'a str, O>
where
    F: Fn(&'a str) -> IResult<&'a str, O>,
{
    move |s: &'a str| {
        let (s, _) = space0(s)?;
        let (s, x) = f(s)?;
        let (s, _) = space0(s)?;
        Ok((s, x))
    }
}

pub fn symbol<'a>(t: &'a str) -> impl Fn(&'a str) -> IResult<&'a str, &'a str> {
    move |s: &'a str| ws(tag(t.clone()))(s)
}

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct CastingType<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct LetExpression<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct TypeReference<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct SequenceMethodCall<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct DataType<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct ConstraintBlock<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct SimpleType<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct DriveStrength<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct Delay3<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct DynamicArrayNew<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct ClassNew<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct BlockItemDeclaration<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct ExpectPropertyStatement<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct SequenceInstance<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct DelayValue<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct EdgeIdentifier<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct IntegerAtomType<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct IncOrDecDeclaration<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct ConcurrentAssertionItem<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct ConcurrentAssertionStatement<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct CheckerInstantiation<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct AssertionItemDeclaration<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct DataTypeOrVoid<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct TfPortList<'a> {
    pub raw: Vec<&'a str>,
}

#[derive(Debug)]
pub struct DataDeclaration<'a> {
    pub raw: Vec<&'a str>,
}

pub fn class_scope(s: &str) -> IResult<&str, Scope> {
    Ok((s, Scope::ClassScope))
}

pub fn casting_type(s: &str) -> IResult<&str, CastingType> {
    Ok((s, CastingType { raw: vec![] }))
}

pub fn let_expression(s: &str) -> IResult<&str, LetExpression> {
    Ok((s, LetExpression { raw: vec![] }))
}

pub fn type_reference(s: &str) -> IResult<&str, TypeReference> {
    Ok((s, TypeReference { raw: vec![] }))
}

pub fn sequence_method_call(s: &str) -> IResult<&str, SequenceMethodCall> {
    Ok((s, SequenceMethodCall { raw: vec![] }))
}

pub fn data_type(s: &str) -> IResult<&str, DataType> {
    Ok((s, DataType { raw: vec![] }))
}

pub fn constraint_block(s: &str) -> IResult<&str, ConstraintBlock> {
    Ok((s, ConstraintBlock { raw: vec![] }))
}

pub fn identifier_list(s: &str) -> IResult<&str, Vec<Identifier>> {
    Ok((s, vec![]))
}

pub fn simple_type(s: &str) -> IResult<&str, SimpleType> {
    Ok((s, SimpleType { raw: vec![] }))
}

pub fn drive_strength(s: &str) -> IResult<&str, DriveStrength> {
    Ok((s, DriveStrength { raw: vec![] }))
}

pub fn delay3(s: &str) -> IResult<&str, Delay3> {
    Ok((s, Delay3 { raw: vec![] }))
}

pub fn dynamic_array_new(s: &str) -> IResult<&str, DynamicArrayNew> {
    Ok((s, DynamicArrayNew { raw: vec![] }))
}

pub fn class_new(s: &str) -> IResult<&str, ClassNew> {
    Ok((s, ClassNew { raw: vec![] }))
}

pub fn block_item_declaration(s: &str) -> IResult<&str, BlockItemDeclaration> {
    Ok((s, BlockItemDeclaration { raw: vec![] }))
}

pub fn expect_property_statement(s: &str) -> IResult<&str, ExpectPropertyStatement> {
    Ok((s, ExpectPropertyStatement { raw: vec![] }))
}

pub fn sequence_instance(s: &str) -> IResult<&str, SequenceInstance> {
    Ok((s, SequenceInstance { raw: vec![] }))
}

pub fn delay_value(s: &str) -> IResult<&str, DelayValue> {
    Ok((s, DelayValue { raw: vec![] }))
}

pub fn edge_identifier(s: &str) -> IResult<&str, EdgeIdentifier> {
    Ok((s, EdgeIdentifier { raw: vec![] }))
}

pub fn integer_atom_type(s: &str) -> IResult<&str, IntegerAtomType> {
    Ok((s, IntegerAtomType { raw: vec![] }))
}

pub fn inc_or_dec_declaration(s: &str) -> IResult<&str, IncOrDecDeclaration> {
    Ok((s, IncOrDecDeclaration { raw: vec![] }))
}

pub fn concurrent_assertion_item(s: &str) -> IResult<&str, ConcurrentAssertionItem> {
    Ok((s, ConcurrentAssertionItem { raw: vec![] }))
}

pub fn concurrent_assertion_statement(s: &str) -> IResult<&str, ConcurrentAssertionStatement> {
    Ok((s, ConcurrentAssertionStatement { raw: vec![] }))
}

pub fn checker_instantiation(s: &str) -> IResult<&str, CheckerInstantiation> {
    Ok((s, CheckerInstantiation { raw: vec![] }))
}

pub fn assertion_item_declaration(s: &str) -> IResult<&str, AssertionItemDeclaration> {
    Ok((s, AssertionItemDeclaration { raw: vec![] }))
}

pub fn data_type_or_void(s: &str) -> IResult<&str, DataTypeOrVoid> {
    Ok((s, DataTypeOrVoid { raw: vec![] }))
}

pub fn tf_port_list(s: &str) -> IResult<&str, TfPortList> {
    Ok((s, TfPortList { raw: vec![] }))
}

pub fn data_declaration(s: &str) -> IResult<&str, DataDeclaration> {
    Ok((s, DataDeclaration { raw: vec![] }))
}
