use crate::parser::*;
//use nom::branch::*;
//use nom::combinator::*;
use nom::error::*;
use nom::{Err, IResult};

// -----------------------------------------------------------------------------

#[derive(Debug)]
pub struct ListOfDefparamAssignments<'a> {
    pub nodes: (Vec<DefparamAssignment<'a>>,),
}

#[derive(Debug)]
pub struct ListOfGenvarIdentifiers<'a> {
    pub nodes: (Vec<Identifier<'a>>,),
}

#[derive(Debug)]
pub struct ListOfInterfaceIdentifiers<'a> {
    pub nodes: (Vec<(Identifier<'a>, Vec<UnpackedDimension<'a>>)>,),
}

#[derive(Debug)]
pub struct ListOfNetDeclAssignments<'a> {
    pub nodes: (Vec<NetDeclAssignment<'a>>,),
}

#[derive(Debug)]
pub struct ListOfParamAssignments<'a> {
    pub nodes: (Vec<ParamAssignment<'a>>,),
}

#[derive(Debug)]
pub struct ListOfPortIdentifiers<'a> {
    pub nodes: (Vec<(Identifier<'a>, Vec<UnpackedDimension<'a>>)>,),
}

#[derive(Debug)]
pub struct ListOfUdpPortIdentifiers<'a> {
    pub nodes: (Vec<Identifier<'a>>,),
}

#[derive(Debug)]
pub struct ListOfSpecparamAssignments<'a> {
    pub nodes: (Vec<SpecparamAssignment<'a>>,),
}

#[derive(Debug)]
pub struct ListOfTfVariableIdentifiers<'a> {
    pub nodes: (
        Vec<(
            Identifier<'a>,
            Vec<VariableDimension<'a>>,
            Option<Expression<'a>>,
        )>,
    ),
}

#[derive(Debug)]
pub struct ListOfTypeAssignments<'a> {
    pub nodes: (Vec<TypeAssignment<'a>>,),
}

#[derive(Debug)]
pub struct ListOfVariableDeclAssignments<'a> {
    pub nodes: (Vec<VariableDeclAssignment<'a>>,),
}

#[derive(Debug)]
pub struct ListOfVariableIdentifiers<'a> {
    pub nodes: (Vec<(Identifier<'a>, Vec<VariableDimension<'a>>)>,),
}

#[derive(Debug)]
pub struct ListOfVariablePortIdentifiers<'a> {
    pub nodes: (
        Vec<(
            Identifier<'a>,
            Vec<VariableDimension<'a>>,
            Option<ConstantExpression<'a>>,
        )>,
    ),
}

// -----------------------------------------------------------------------------

pub fn list_of_defparam_assignments(s: &str) -> IResult<&str, ListOfDefparamAssignments> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn list_of_genvar_identifiers(s: &str) -> IResult<&str, ListOfGenvarIdentifiers> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn list_of_interface_identifiers(s: &str) -> IResult<&str, ListOfInterfaceIdentifiers> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn list_of_net_decl_assignments(s: &str) -> IResult<&str, ListOfNetDeclAssignments> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn list_of_param_assignments(s: &str) -> IResult<&str, ListOfParamAssignments> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn list_of_port_identifiers(s: &str) -> IResult<&str, ListOfPortIdentifiers> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn list_of_udp_port_identifiers(s: &str) -> IResult<&str, ListOfUdpPortIdentifiers> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn list_of_specparam_assignments(s: &str) -> IResult<&str, ListOfSpecparamAssignments> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn list_of_tf_variable_identifiers(s: &str) -> IResult<&str, ListOfTfVariableIdentifiers> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn list_of_type_assignments(s: &str) -> IResult<&str, ListOfTypeAssignments> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn list_of_variable_decl_assignments(s: &str) -> IResult<&str, ListOfVariableDeclAssignments> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn list_of_variable_identifiers(s: &str) -> IResult<&str, ListOfVariableIdentifiers> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}

pub fn list_of_variable_port_identifiers(s: &str) -> IResult<&str, ListOfVariablePortIdentifiers> {
    Err(Err::Error(make_error(s, ErrorKind::Fix)))
}
