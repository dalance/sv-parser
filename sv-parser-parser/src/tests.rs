#![cfg(test)]

use crate::*;

macro_rules! test {
    ( $x:expr, $y:expr, $z:pat ) => {
        nom_packrat::init!();
        let info = SpanInfo::default();
        let ret = all_consuming($x)(Span::new_extra($y, info));
        if let $z = ret {
        } else {
            assert!(false, "{:?}", ret)
        }
    };
}

#[test]
fn test_pulldown_strength() {
    test!(pulldown_strength, "(supply0, strong1)", Ok((_, _)));
    test!(pulldown_strength, "(pull1, weak0)", Ok((_, _)));
    test!(pulldown_strength, "(pull0)", Ok((_, _)));
    test!(pulldown_strength, "(pull0)", Ok((_, _)));
    test!(pulldown_strength, "(pull0)", Ok((_, _)));
}

#[test]
fn test_pullup_strength() {
    test!(pullup_strength, "(supply0, strong1)", Ok((_, _)));
    test!(pullup_strength, "(pull1, weak0)", Ok((_, _)));
    test!(pullup_strength, "(supply1)", Ok((_, _)));
}

#[test]
fn test_cmos_switchtype() {
    test!(cmos_switchtype, "cmos ", Ok((_, _)));
    test!(cmos_switchtype, "rcmos ", Ok((_, _)));
}

#[test]
fn test_enable_gatetype() {
    test!(enable_gatetype, "bufif0 ", Ok((_, _)));
    test!(enable_gatetype, "bufif1 ", Ok((_, _)));
    test!(enable_gatetype, "notif0 ", Ok((_, _)));
    test!(enable_gatetype, "notif1 ", Ok((_, _)));
}

#[test]
fn test_mos_switchtype() {
    test!(mos_switchtype, "nmos ", Ok((_, _)));
    test!(mos_switchtype, "pmos ", Ok((_, _)));
    test!(mos_switchtype, "rnmos ", Ok((_, _)));
    test!(mos_switchtype, "rpmos ", Ok((_, _)));
}

#[test]
fn test_n_input_gatetype() {
    test!(n_input_gatetype, "and ", Ok((_, _)));
    test!(n_input_gatetype, "nand ", Ok((_, _)));
    test!(n_input_gatetype, "or ", Ok((_, _)));
    test!(n_input_gatetype, "nor ", Ok((_, _)));
    test!(n_input_gatetype, "xor ", Ok((_, _)));
    test!(n_input_gatetype, "xnor ", Ok((_, _)));
}

#[test]
fn test_n_output_gatetype() {
    test!(n_output_gatetype, "buf ", Ok((_, _)));
    test!(n_output_gatetype, "not ", Ok((_, _)));
}

#[test]
fn test_pass_en_switchtype() {
    test!(pass_en_switchtype, "tranif0 ", Ok((_, _)));
    test!(pass_en_switchtype, "tranif1 ", Ok((_, _)));
    test!(pass_en_switchtype, "rtranif0 ", Ok((_, _)));
    test!(pass_en_switchtype, "rtranif1 ", Ok((_, _)));
}

#[test]
fn test_pass_switchtype() {
    test!(pass_switchtype, "tran ", Ok((_, _)));
    test!(pass_switchtype, "rtran ", Ok((_, _)));
}

#[test]
fn test_library_text() {
    test!(
        library_text,
        "library rtlLib \"*.v\" -incdir \"aaa\";\ninclude \"bbb\";;",
        Ok((_, _))
    );
}

#[test]
fn test_timeunits_declaration() {
    test!(timeunits_declaration, "timeunit 1.0ps;", Ok((_, _)));
    test!(timeunits_declaration, "timeunit 1.0ps / 20ms;", Ok((_, _)));
    test!(timeunits_declaration, "timeprecision 10.0fs;", Ok((_, _)));
    test!(
        timeunits_declaration,
        "timeunit 10.0fs; timeprecision 20s;",
        Ok((_, _))
    );
    test!(
        timeunits_declaration,
        "timeprecision 10.0fs; timeunit 20s \n;",
        Ok((_, _))
    );
}

#[test]
fn test_data_type() {
    test!(
        data_type,
        "struct { bit [7:0] opcode; bit [23:0] addr; }",
        Ok((_, DataType::StructUnion(_)))
    );
    test!(
        data_type,
        "struct packed signed { int a; shortint b; byte c; bit [7:0] d; }",
        Ok((_, DataType::StructUnion(_)))
    );
    test!(
        data_type,
        "union { int i; shortreal f; } ",
        Ok((_, DataType::StructUnion(_)))
    );
    test!(
        data_type,
        "struct { bit isfloat; union { int i; shortreal f; } n; }",
        Ok((_, DataType::StructUnion(_)))
    );
    test!(
        data_type,
        "union packed { s_atmcell acell; bit [423:0] bit_slice; bit [52:0][7:0] byte_slice; }",
        Ok((_, DataType::StructUnion(_)))
    );
    test!(
        data_type,
        "union tagged { void Invalid; int Valid; }",
        Ok((_, DataType::StructUnion(_)))
    );
}

#[test]
fn test_parameter_declaration() {
    test!(
        parameter_declaration,
        "parameter e = 25, f = 9 ",
        Ok((_, ParameterDeclaration::Param(_)))
    );
    test!(
        parameter_declaration,
        "parameter byte_size = 8, byte_mask = byte_size - 1",
        Ok((_, ParameterDeclaration::Param(_)))
    );
    test!(
        parameter_declaration,
        "parameter signed [3:0] mux_selector = 0",
        Ok((_, ParameterDeclaration::Param(_)))
    );
    test!(
        parameter_declaration,
        "parameter real r1 = 3.5e17",
        Ok((_, ParameterDeclaration::Param(_)))
    );
    test!(
        parameter_declaration,
        "parameter logic [31:0] P1 [3:0] = '{ 1, 2, 3, 4 } ",
        Ok((_, ParameterDeclaration::Param(_)))
    );
    test!(
        parameter_declaration,
        "parameter r2 = $ ",
        Ok((_, ParameterDeclaration::Param(_)))
    );
    test!(
        parameter_declaration,
        "parameter type p2 = shortint ",
        Ok((_, ParameterDeclaration::Type(_)))
    );
}

#[test]
fn test_specparam_declaration() {
    test!(specparam_declaration, "specparam delay = 10 ; ", Ok((_, _)));
    test!(
        specparam_declaration,
        "specparam tRise_clk_q = 150, tFall_clk_q = 200;",
        Ok((_, _))
    );
}

#[test]
fn test_inout_declaration() {
    test!(inout_declaration, "inout a", Ok((_, _)));
    test!(inout_declaration, "inout [7:0] a", Ok((_, _)));
    test!(inout_declaration, "inout signed [7:0] a", Ok((_, _)));
}

#[test]
fn test_data_declaration() {
    test!(
        data_declaration,
        "integer i_array[*];",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "bit [20:0] array_b[string];",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "event ev_array[myClass];",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "int array_name [*];",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "int array_name1 [ integer ];",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "int a[int] = '{default:1};",
        Ok((_, DataDeclaration::Variable(_)))
    );
    test!(
        data_declaration,
        "byte q1[$];",
        Ok((_, DataDeclaration::Variable(_)))
    );
}

#[test]
fn test_drive_strength() {
    test!(drive_strength, "(supply0, strong1)", Ok((_, _)));
    test!(drive_strength, "(pull1, weak0)", Ok((_, _)));
    test!(drive_strength, "(pull0, highz1)", Ok((_, _)));
    test!(drive_strength, "(weak1, highz0)", Ok((_, _)));
    test!(drive_strength, "(highz0, supply1)", Ok((_, _)));
    test!(drive_strength, "(highz1, strong0)", Ok((_, _)));
}

#[test]
fn test_charge_strength() {
    test!(charge_strength, "( small)", Ok((_, _)));
    test!(charge_strength, "( medium  )", Ok((_, _)));
    test!(charge_strength, "(large)", Ok((_, _)));
}

#[test]
fn test_blocking_assignment() {
    test!(
        blocking_assignment,
        "idest = new [3] (isrc)",
        Ok((_, BlockingAssignment::NonrangeVariable(_)))
    );
}

#[test]
fn test_primary() {
    test!(primary, "'0", Ok((_, Primary::PrimaryLiteral(_))));
    test!(primary, "10", Ok((_, Primary::PrimaryLiteral(_))));
    test!(primary, "\"aaa\"", Ok((_, Primary::PrimaryLiteral(_))));
    test!(primary, "this ", Ok((_, Primary::This(_))));
    test!(primary, "$ ", Ok((_, Primary::Dollar(_))));
    test!(primary, "null ", Ok((_, Primary::Null(_))));
}

#[test]
fn test_cast() {
    test!(cast, "int'(2.0 * 3.0)", Ok((_, _)));
    test!(cast, "shortint'({8'hFA,8'hCE}) ", Ok((_, _)));
    test!(cast, "signed'(x)", Ok((_, _)));
    test!(cast, "const'(x)", Ok((_, _)));
    test!(cast, "type_t'(x)", Ok((_, _)));
}

#[test]
fn test_unbased_unsized_literal() {
    test!(unbased_unsized_literal, "'0", Ok((_, _)));
    test!(unbased_unsized_literal, "'1", Ok((_, _)));
    test!(unbased_unsized_literal, "'x", Ok((_, _)));
    test!(unbased_unsized_literal, "'z", Ok((_, _)));
}

#[test]
fn test_net_lvalue() {
    test!(net_lvalue, "A", Ok((_, _)));
    test!(net_lvalue, "{A[7:0],A[15:8],A[23:16]}", Ok((_, _)));
    test!(net_lvalue, "'{A[7:0],A[15:8]}", Ok((_, _)));
}

#[test]
fn test_variable_lvalue() {
    test!(variable_lvalue, "A", Ok((_, _)));
    test!(variable_lvalue, "{A[7:0],A[15:8],A[23:16]}", Ok((_, _)));
    test!(variable_lvalue, "'{A[7:0],A[15:8]}", Ok((_, _)));
}

#[test]
fn test_nonrange_variable_lvalue() {
    test!(nonrange_variable_lvalue, "A", Ok((_, _)));
    test!(nonrange_variable_lvalue, "A[1][2][3]", Ok((_, _)));
    //TODO
    //test!(nonrange_variable_lvalue, "A[][2][3]", Ok((_, _)));
    //test!(nonrange_variable_lvalue, "A[][]", Ok((_, _)));
}

#[test]
fn test_unary_operator() {
    test!(unary_operator, "+", Ok((_, _)));
    test!(unary_operator, "-", Ok((_, _)));
    test!(unary_operator, "!", Ok((_, _)));
    test!(unary_operator, "&", Ok((_, _)));
    test!(unary_operator, "|", Ok((_, _)));
    test!(unary_operator, "~&", Ok((_, _)));
    test!(unary_operator, "~|", Ok((_, _)));
    test!(unary_operator, "~^", Ok((_, _)));
    test!(unary_operator, "^~", Ok((_, _)));
    test!(unary_operator, "^", Ok((_, _)));
    test!(unary_operator, "~", Ok((_, _)));
}

#[test]
fn test_binary_operator() {
    test!(binary_operator, "+", Ok((_, _)));
    test!(binary_operator, "-", Ok((_, _)));
    test!(binary_operator, "**", Ok((_, _)));
    test!(binary_operator, "*", Ok((_, _)));
    test!(binary_operator, "/", Ok((_, _)));
    test!(binary_operator, "%", Ok((_, _)));
    test!(binary_operator, "===", Ok((_, _)));
    test!(binary_operator, "==?", Ok((_, _)));
    test!(binary_operator, "==", Ok((_, _)));
    test!(binary_operator, "!==", Ok((_, _)));
    test!(binary_operator, "!=?", Ok((_, _)));
    test!(binary_operator, "!=", Ok((_, _)));
    test!(binary_operator, "&&", Ok((_, _)));
    test!(binary_operator, "||", Ok((_, _)));
    test!(binary_operator, "&", Ok((_, _)));
    test!(binary_operator, "|", Ok((_, _)));
    test!(binary_operator, "^~", Ok((_, _)));
    test!(binary_operator, "^", Ok((_, _)));
    test!(binary_operator, "~^", Ok((_, _)));
    test!(binary_operator, ">>>", Ok((_, _)));
    test!(binary_operator, ">>", Ok((_, _)));
    test!(binary_operator, "<<<", Ok((_, _)));
    test!(binary_operator, "<<", Ok((_, _)));
    test!(binary_operator, "->", Ok((_, _)));
    test!(binary_operator, "<->", Ok((_, _)));
    test!(binary_operator, "<=", Ok((_, _)));
    test!(binary_operator, "<", Ok((_, _)));
    test!(binary_operator, ">=", Ok((_, _)));
    test!(binary_operator, ">", Ok((_, _)));
}

#[test]
fn test_inc_or_dec_operator() {
    test!(inc_or_dec_operator, "++", Ok((_, _)));
    test!(inc_or_dec_operator, "--", Ok((_, _)));
}

#[test]
fn test_unary_module_path_operator() {
    test!(unary_module_path_operator, "!", Ok((_, _)));
    test!(unary_module_path_operator, "&", Ok((_, _)));
    test!(unary_module_path_operator, "|", Ok((_, _)));
    test!(unary_module_path_operator, "~&", Ok((_, _)));
    test!(unary_module_path_operator, "~|", Ok((_, _)));
    test!(unary_module_path_operator, "~^", Ok((_, _)));
    test!(unary_module_path_operator, "^~", Ok((_, _)));
    test!(unary_module_path_operator, "^", Ok((_, _)));
    test!(unary_module_path_operator, "~", Ok((_, _)));
}

#[test]
fn test_binary_module_path_operator() {
    test!(binary_module_path_operator, "==", Ok((_, _)));
    test!(binary_module_path_operator, "!=", Ok((_, _)));
    test!(binary_module_path_operator, "&&", Ok((_, _)));
    test!(binary_module_path_operator, "||", Ok((_, _)));
    test!(binary_module_path_operator, "&", Ok((_, _)));
    test!(binary_module_path_operator, "|", Ok((_, _)));
    test!(binary_module_path_operator, "^~", Ok((_, _)));
    test!(binary_module_path_operator, "^", Ok((_, _)));
    test!(binary_module_path_operator, "~^", Ok((_, _)));
}

#[test]
fn test_string_literal() {
    test!(string_literal, "\"aaa aaaa\"", Ok((_, _)));
    test!(string_literal, r#""aaa\" aaaa""#, Ok((_, _)));
    test!(string_literal, r#""aaa\"""#, Ok((_, _)));
}

#[test]
fn test_comment() {
    test!(comment, "// comment", Ok((_, _)));
    test!(comment, "/* comment\n\n */", Ok((_, _)));
}

#[test]
fn test_expression() {
    test!(expression, "(!a ? 0 : !b : 1 : c ? 0 : 1)", Ok((_, _)));
}

#[test]
fn test_clause3() {
    test!(
        module_declaration,
        r##"module mux2to1 (input wire a, b, sel, // combined port and type declaration
                            output logic y);
              always_comb begin // procedural block
                if (sel) y = a; // procedural statement
                else y = b;
              end
            endmodule: mux2to1"##,
        Ok((_, _))
    );
    test!(
        program_declaration,
        r##"program test (input clk, input [16:1] addr, inout [7:0] data);
              initial begin
              end
            endprogram"##,
        Ok((_, _))
    );
    test!(
        module_declaration,
        r##"module memMod(simple_bus a); // simple_bus interface port
              logic avail;
              // When memMod is instantiated in module top, a.req is the req
              // signal in the sb_intf instance of the 'simple_bus' interface
              always @(posedge a.clk) a.gnt <= a.req & avail;
            endmodule"##,
        Ok((_, _))
    );
    test!(
        module_declaration,
        r##"module cpuMod(simple_bus b); // simple_bus interface port
            endmodule"##,
        Ok((_, _))
    );
    test!(
        module_declaration,
        r##"module top;
              logic clk = 0;
              simple_bus sb_intf(.clk(clk)); // Instantiate the interface
              memMod mem(.a(sb_intf)); // Connect interface to module instance
              cpuMod cpu(.b(sb_intf)); // Connect interface to module instance
            endmodule"##,
        Ok((_, _))
    );
    test!(
        package_declaration,
        r##"package ComplexPkg;
              typedef struct {
                shortreal i, r;
              } Complex;

              function Complex add(Complex a, b);
                add.r = a.r + b.r;
                add.i = a.i + b.i;
              endfunction

              function Complex mul(Complex a, b);
                mul.r = (a.r * b.r) - (a.i * b.i);
                mul.i = (a.r * b.i) + (a.i * b.r);
              endfunction
            endpackage : ComplexPkg"##,
        Ok((_, _))
    );
    test!(
        module_declaration,
        r##"module top; // module with no ports
              logic in1, in2, select; // variable declarations
              wire out1; // net declaration

              mux2to1 m1 (.a(in1), .b(in2), .sel(select), .y(out1)); // module instance

            endmodule: top"##,
        Ok((_, _))
    );
    test!(
        module_declaration,
        r##"module mux2to1 (input wire a, b, sel, // combined port and type declaration
                            output logic y);
              // netlist using built-in primitive instances
              not g1 (sel_n, sel);
              and g2 (a_s, a, sel_n);
              and g3 (b_s, b, sel);
              or g4 (y, a_s, b_s);
            endmodule: mux2to1"##,
        Ok((_, _))
    );
    test!(
        task_declaration,
        r##"task t;
              int b;
              b = 5 + $unit::b; // $unit::b is the one outside
            endtask"##,
        Ok((_, _))
    );
    test!(
        module_declaration,
        r##"module D;
              timeunit 100ps;
              timeprecision 10fs;
            endmodule"##,
        Ok((_, _))
    );
    test!(
        module_declaration,
        r##"module E;
              timeunit 100ps / 10fs; // timeunit with optional second argument
            endmodule"##,
        Ok((_, _))
    );
}

#[test]
fn test_clause4() {
    test!(
        module_declaration,
        r##"module test;
              logic a;
              initial begin
                a <= 0;
                a <= 1;
              end
            endmodule"##,
        Ok((_, _))
    );
    test!(
        module_declaration,
        r##"module test;
              assign p = q;
              initial begin
                q = 1;
                #1 q = 0;
                $display(p);
              end
            endmodule"##,
        Ok((_, _))
    );
}

#[test]
fn test_clause5() {
    test!(identifier, "shiftreg_a", Ok((_, _)));
    test!(identifier, "busa_index", Ok((_, _)));
    test!(identifier, "error_condition", Ok((_, _)));
    test!(identifier, "merge_ab", Ok((_, _)));
    test!(identifier, "_bus3", Ok((_, _)));
    test!(identifier, "n$657", Ok((_, _)));
    test!(identifier, "\\busa+index", Ok((_, _)));
    test!(identifier, "\\-clock", Ok((_, _)));
    test!(identifier, "\\***error-condition***", Ok((_, _)));
    test!(identifier, "\\net1/\\net2", Ok((_, _)));
    test!(identifier, "\\{a,b}", Ok((_, _)));
    test!(identifier, "\\a*(b+c)", Ok((_, _)));
    test!(
        subroutine_call_statement,
        "$display (\"display a message\");",
        Ok((_, _))
    );
    test!(subroutine_call_statement, "$finish;", Ok((_, _)));
    test!(primary, "'0", Ok((_, _)));
    test!(primary, "'1", Ok((_, _)));
    test!(primary, "'X", Ok((_, _)));
    test!(primary, "'x", Ok((_, _)));
    test!(primary, "'Z", Ok((_, _)));
    test!(primary, "'z", Ok((_, _)));
    test!(number, "659", Ok((_, Number::IntegralNumber(_))));
    test!(number, "'h 837FF", Ok((_, Number::IntegralNumber(_))));
    test!(number, "'h 837FF", Ok((_, Number::IntegralNumber(_))));
    test!(number, "'o7460", Ok((_, Number::IntegralNumber(_))));
    test!(number, "'4af", Err(_));
    test!(number, "4'b1001", Ok((_, Number::IntegralNumber(_))));
    test!(number, "5 'D 3", Ok((_, Number::IntegralNumber(_))));
    test!(number, "3'b01x", Ok((_, Number::IntegralNumber(_))));
    test!(number, "12'hx", Ok((_, Number::IntegralNumber(_))));
    test!(number, "16'hz", Ok((_, Number::IntegralNumber(_))));
    test!(number, "8 'd -6", Err(_));
    test!(number, "4 'shf", Ok((_, Number::IntegralNumber(_))));
    test!(number, "16'sd?", Ok((_, Number::IntegralNumber(_))));
    test!(number, "27_195_000", Ok((_, Number::IntegralNumber(_))));
    test!(
        number,
        "16'b0011_0101_0001_1111",
        Ok((_, Number::IntegralNumber(_)))
    );
    test!(
        number,
        "32 'h 12ab_f001",
        Ok((_, Number::IntegralNumber(_)))
    );
    test!(number, "1.2", Ok((_, Number::RealNumber(_))));
    test!(number, "0.1", Ok((_, Number::RealNumber(_))));
    test!(number, "2394.26331", Ok((_, Number::RealNumber(_))));
    test!(number, "1.2E12", Ok((_, Number::RealNumber(_))));
    test!(number, "1.30e-2", Ok((_, Number::RealNumber(_))));
    test!(number, "0.1e-0", Ok((_, Number::RealNumber(_))));
    test!(number, "23E10", Ok((_, Number::RealNumber(_))));
    test!(number, "29E-2", Ok((_, Number::RealNumber(_))));
    test!(number, "236.123_763_e-12", Ok((_, Number::RealNumber(_))));
    test!(number, ".12", Err(_));
    test!(number, "9.", Err(_));
    test!(number, "4.E3", Err(_));
    test!(number, ".2e-7", Err(_));
    test!(primary, "2.1ns ", Ok((_, Primary::PrimaryLiteral(_))));
    test!(primary, "40 ps ", Ok((_, Primary::PrimaryLiteral(_))));
    test!(
        subroutine_call_statement,
        r##"$display("Humpty Dumpty sat on a wall. \
            Humpty Dumpty had a great fall.");"##,
        Ok((_, _))
    );
    test!(
        subroutine_call_statement,
        r##"$display("Humpty Dumpty sat on a wall.\n\
            Humpty Dumpty had a great fall.");"##,
        Ok((_, _))
    );
    test!(module_item, r##"byte c1 = "A" ;"##, Ok((_, _)));
    test!(module_item, r##"bit [7:0] d = "\n" ;"##, Ok((_, _)));
    test!(
        module_item,
        r##"bit [8*12:1] stringvar = "Hello world\n";"##,
        Ok((_, _))
    );
    test!(
        module_item,
        r##"bit [0:11] [7:0] stringvar = "Hello world\n" ;"##,
        Ok((_, _))
    );
    test!(
        module_item,
        r##"byte c3 [0:12] = "hello world\n" ;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"typedef struct {int a; shortreal b;} ab;
            ab c;
            c = '{0, 0.0}; // structure literal type determined from
                           // the left-hand context (c)"##,
        Ok((_, _))
    );
    test!(
        module_item,
        r##"ab abarr[1:0] = '{'{1, 1.0}, '{2, 2.0}};"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"c = '{a:0, b:0.0};             // member name and value for that member
            c = '{default:0};              // all elements of structure c are set to 0
            d = ab'{int:1, shortreal:1.0}; // data type and default value for all
                                           // members of that type"##,
        Ok((_, _))
    );
    test!(
        module_item,
        r##"ab abarr[1:0] = '{'{1, 1.0}, '{2, 2.0}};"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"struct {int X,Y,Z;} XYZ = '{3{1}};
            typedef struct {int a,b[4];} ab_t;
            int a,b,c;
            ab_t v1[1:0] [2:0];
            v1 = '{2{'{3{'{a,'{2{b,c}}}}}}};"##,
        Ok((_, _))
    );
    test!(
        module_item,
        r##"int n[1:2][1:3] = '{'{0,1,2},'{3{4}}};"##,
        Ok((_, _))
    );
    test!(
        module_item,
        r##"int n[1:2][1:6] = '{2{'{3{4, 5}}}}; // same as '{'{4,5,4,5,4,5},'{4,5,4,5,4,5}}"##,
        Ok((_, _))
    );
    test!(module_item, r##"typedef int triple [1:3];"##, Ok((_, _)));
    test!(
        module_item,
        r##"triple b = '{1:1, default:0}; // indices 2 and 3 assigned 0"##,
        Ok((_, _))
    );
    test!(
        attribute_instance,
        r##"(* full_case, parallel_case *)"##,
        Ok((_, _))
    );
    test!(attribute_instance, r##"(* full_case=1 *)"##, Ok((_, _)));
    test!(
        attribute_instance,
        r##"(* full_case, // no value assigned
               parallel_case=1 *)"##,
        Ok((_, _))
    );
    test!(attribute_instance, r##"(* full_case *)"##, Ok((_, _)));
    test!(
        attribute_instance,
        r##"(* full_case=1, parallel_case = 0 *)"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"(* fsm_state *) logic [7:0] state1;
            (* fsm_state=1 *) logic [3:0] state2, state3;
            logic [3:0] reg1;                   // reg1 does NOT have fsm_state set
            (* fsm_state=0 *) logic [3:0] reg2; // nor does reg2"##,
        Ok((_, _))
    );
    test!(
        module_item,
        r##"a = b + (* mode = "cla" *) c; // sets the value for the attribute mode
                                          // to be the string cla."##,
        Ok((_, _))
    );
    test!(
        module_item,
        r##"a = add (* mode = "cla" *) (b, c);"##,
        Ok((_, _))
    );
    test!(
        module_item,
        r##"a = b ? (* no_glitch *) c : d;"##,
        Ok((_, _))
    );
}

#[test]
fn test_clause6() {
    test!(
        many1(module_item),
        r##"trireg a;                         // trireg net of charge strength medium
            trireg (large) #(0,0,50) cap1;    // trireg net of charge strength large
                                              // with charge decay time 50 time units
            trireg (small) signed [3:0] cap2; // signed 4-bit trireg vector of
                                              // charge strength small"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"struct {
              bit [7:0] A;
              bit [7:0] B;
              byte C;
            } abc;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"assign abc.C = sel ? 8'hBE : 8'hEF;

            not (abc.A[0],abc.B[0]),
                (abc.A[1],abc.B[1]),
                (abc.A[2],abc.B[2]),
                (abc.A[3],abc.B[3]);

            always @(posedge clk) abc.B <= abc.B + 1;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"assign abc.C = sel ? 8'hDE : 8'hED;

            // Mixing continuous and procedural assignments to abc.A[3]
            always @(posedge clk) abc.A[7:3] <= !abc.B[7:3];"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"wire w = vara & varb;       // net with a continuous assignment

            logic v = consta & constb;  // variable with initialization

            logic vw;                   // no initial assignment
            assign vw = vara & varb;    // continuous assignment to a variable

            real circ;
            assign circ = 2.0 * PI * R; // continuous assignment to a variable"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"typedef struct {
              real field1;
              bit field2;
            } T;

            // user-defined resolution function Tsum
            function automatic T Tsum (input T driver[]);
              Tsum.field1 = 0.0;
              foreach (driver[i])
                Tsum.field1 += driver[i].field1;
            endfunction

            nettype T wT; // an unresolved nettype wT whose data type is T

            // a nettype wTsum whose data type is T and
            // resolution function is Tsum
            nettype T wTsum with Tsum;

            // user-defined data type TR
            typedef real TR[5];

            // an unresolved nettype wTR whose data type
            // is an array of real
            nettype TR wTR;

            // declare another name nettypeid2 for nettype wTsum
            nettype wTsum nettypeid2;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"class Base #(parameter p = 1);
              typedef struct {
                real r;
                bit[p-1:0] data;
              } T;

              static function T Tsum (input T driver[]);
                Tsum.r = 0.0;
                Tsum.data = 0;
                foreach (driver[i])
                  Tsum.data += driver[i].data;
                Tsum.r = $itor(Tsum.data);
              endfunction
            endclass

            typedef Base#(32) MyBaseT;
            nettype MyBaseT::T narrowTsum with MyBaseT::Tsum;

            typedef Base#(64) MyBaseType;
            nettype MyBaseType::T wideTsum with MyBaseType::Tsum;

            narrowTsum net1; // data is 32 bits wide
            wideTsum net2; // data is 64 bits wide"##,
        Ok((_, _))
    );
    test!(
        source_text,
        r##"package NetsPkg;
              nettype real realNet;
            endpackage : NetsPkg

            module top();
              interconnect [0:1] iBus;
              lDriver l1(iBus[0]);
              rDriver r1(iBus[1]);
              rlMod m1(iBus);
            endmodule : top

            module lDriver(output wire logic out);
            endmodule : lDriver

            module rDriver
              import NetsPkg::*;
              (output realNet out);
            endmodule : rDriver

            module rlMod(input interconnect [0:1] iBus);
              lMod l1(iBus[0]);
              rMod r1(iBus[1]);
            endmodule : rlMod"##,
        Ok((_, _))
    );
    test!(
        library_text,
        r##"library realLib *.svr;
            library logicLib *.sv;

            config cfgReal;
              design logicLib.top;
              default liblist realLib logicLib;
            endconfig

            config cfgLogic;
              design logicLib.top;
              default liblist logicLib realLib;
            endconfig"##,
        Ok((_, _))
    );
    test!(
        source_text,
        r##"module top();
              interconnect [0:3] [0:1] aBus;
              logic [0:3] dBus;
              driver driverArray[0:3](aBus);
              cmp cmpArray[0:3](aBus,rst,dBus);
            endmodule : top"##,
        Ok((_, _))
    );
    test!(
        source_text,
        r##"package NetsPkg;
              nettype real realNet;
            endpackage : NetsPkg"##,
        Ok((_, _))
    );
    test!(
        source_text,
        r##"module driver
              import NetsPkg::*;
              #(parameter int delay = 30,
                          int iterations = 256)
              (output realNet [0:1] out);
              timeunit 1ns / 1ps;
              real outR[1:0];
              assign out = outR;
              initial begin
                outR[0] = 0.0;
                outR[1] = 3.3;
                for (int i = 0; i < iterations; i++) begin
                  #delay outR[0] += 0.2;
                  outR[1] -= 0.2;
                end
              end
            endmodule : driver"##,
        Ok((_, _))
    );
    test!(
        source_text,
        r##"module driver #(parameter int delay = 30,
                                      int iterations = 256)
                           (output wire logic [0:1] out);
              timeunit 1ns / 1ps;
              logic [0:1] outvar;

              assign out = outvar;

              initial begin
                outvar = '0;
                for (int i = 0; i < iterations; i++)
                  #delay outvar++;
              end
            endmodule : driver"##,
        Ok((_, _))
    );
    test!(
        source_text,
        r##"module cmp
              import NetsPkg::*;
              #(parameter real hyst = 0.65)
              (input realNet [0:1] inA,
               input logic rst,
               output logic out);
              timeunit 1ns / 1ps;
              real updatePeriod = 100.0;

              initial out = 1'b0;

              always #updatePeriod begin
                if (rst) out <= 1'b0;
                else if (inA[0] > inA[1]) out <= 1'b1;
                else if (inA[0] < inA[1] - hyst) out <= 1'b0;
              end
            endmodule : cmp"##,
        Ok((_, _))
    );
    test!(
        source_text,
        r##"module cmp #(parameter real hyst = 0.65)
                        (input wire logic [0:1] inA,
              input logic rst,
              output logic out);

              initial out = 1'b0;

              always @(inA, rst) begin
                if (rst) out <= 1'b0;
                else if (inA[0] & ~inA[1]) out <= 1'b1;
                else out <= 1'b0;
              end
            endmodule : cmp"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"trireg (large) logic #(0,0,0) cap1;
            typedef logic [31:0] addressT;
            wire addressT w1;
            wire struct packed { logic ecc; logic [7:0] data; } memsig;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"wire w;         // equivalent to "wire logic w;"
            wire [15:0] ww; // equivalent to "wire logic [15:0] ww;""##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"tri reg r;
            inout wire reg p;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"interconnect w1;             // legal
            interconnect [3:0] w2;       // legal
            interconnect [3:0] w3 [1:0]; // legal"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"nettype T wT;

            // a nettype wTsum whose data type is T and
            // resolution function is Tsum
            // Refer to example in 6.6.7 for the declaration of Tsum
            nettype T wTsum with Tsum;

            // a net of unresolved nettype wT
            wT w1;

            // an array of nets, each net element is of unresolved nettype wT
            wT w2[8];

            // a net of resolved nettype wTsum and resolution function Tsum
            wTsum w3;

            // an array of nets, each net is of resolved nettype wTsum
            wTsum w4[8];

            // user-defined data type TR which is an array of reals
            typedef real TR[5];

            // an unresolved nettype wTR with data type TR
            nettype TR wTR;

            // a net with unresolved nettype wTR and data type TR
            wTR w5;

            // an array of nets, each net has an unresolved nettype wTR
            // and data type TR
            wTR w6[8];"##,
        Ok((_, _))
    );
    test!(many1(module_item), r##"shortint s1, s2[0:9];"##, Ok((_, _)));
    test!(
        many1(module_item),
        r##"var byte my_byte; // equivalent to "byte my_byte;"
            var v;            // equivalent to "var logic v;"
            var [15:0] vw;    // equivalent to "var logic [15:0] vw;"
            var enum bit { clear, error } status;
            input var logic data_in;
            var reg r;"##,
        Ok((_, _))
    );
    test!(many1(module_item), r##"int i = 0;"##, Ok((_, _)));
    test!(
        many1(module_item),
        r##"wand w;                        // a scalar "wand" net
            tri [15:0] busa;               // a 16-bit bus
            trireg (small) storeit;        // a charge storage node of strength small
            logic a;                       // a scalar variable
            logic[3:0] v;                  // a 4-bit vector made up of (from most to
                                           // least significant)v[3], v[2], v[1], and v[0]
            logic signed [3:0] signed_reg; // a 4-bit vector in range -8 to 7
            logic [-1:4] b;                // a 6-bit vector
            wire w1, w2;                   // declares two nets
            logic [4:0] x, y, z;           // declares three 5-bit variables"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"tri1 scalared [63:0] bus64; //a bus that will be expanded
            tri vectored [31:0] data;   //a bus that may or may not be expanded"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"int unsigned ui;
            int signed si;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"chandle variable_name ;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"parameter string default_name = "John Smith";
            string myName = default_name;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"byte c = "A";                // assigns to c "A"
            bit [10:0] b = "\x41";       // assigns to b 'b000_0100_0001
            bit [1:4][7:0] h = "hello" ; // assigns to h "ello""##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"string s0 = "String literal assign";// sets s0 to "String literal assign"
            string s1 = "hello\0world";         // sets s1 to "helloworld"
            bit [11:0] b = 12'ha41;
            string s2 = string'(b);             // sets s2 to 16'h0a41"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"typedef logic [15:0] r_t;
            r_t r;
            integer i = 1;
            string b = "";
            string a = {"Hi", b};

            r = r_t'(a);    // OK
            b = string'(r); // OK
            b = "Hi";       // OK
            b = {5{"Hi"}};  // OK
            a = {i{"Hi"}};  // OK (non-constant replication)
            r = {i{"Hi"}};  // invalid (non-constant replication)
            a = {i{b}};     // OK
            a = {a,b};      // OK
            a = {"Hi",b};   // OK
            r = {"H",""};   // yields "H\0". "" is converted to 8'b0
            b = {"H",""};   // yields "H". "" is the empty string
            a[0] = "h";     // OK, same as a[0] = "cough"
            a[0] = b;       // invalid, requires a cast
            a[1] = "\0";    // ignored, a is unchanged"##,
        Ok((_, _))
    );
    //test!(
    //    many1(module_item),
    //    r##"str = "123";
    //        int i = str.atoi(); // assigns 123 to i."##,
    //    Ok((_, _))
    //);
    test!(
        many1(module_item),
        r##"event done;            // declare a new event called done
            event done_too = done; // declare done_too as alias to done
            event empty = null;    // event variable with no synchronization object"##,
        Ok((_, _))
    );
    test!(many1(module_item), r##"typedef int intP;"##, Ok((_, _)));
    test!(many1(module_item), r##"intP a, b;"##, Ok((_, _)));
    test!(
        source_text,
        r##"interface intf_i;
              typedef int data_t;
            endinterface

            module sub(intf_i p);
              typedef p.data_t my_data_t;
              my_data_t data;
                // type of 'data' will be int when connected to interface above
            endmodule"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"typedef enum type_identifier;
            typedef struct type_identifier;
            typedef union type_identifier;
            typedef class type_identifier;
            typedef interface class type_identifier;
            typedef type_identifier;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"typedef C;
            C::T x;           // illegal; C is an incomplete forward type
            typedef C::T c_t; // legal; reference to C::T is made by a typedef
            c_t y;
            class C;
              typedef int T;
            endclass"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"enum {red, yellow, green} light1, light2; // anonymous int type"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"enum bit [1:0] {IDLE, XX='x, S1=2'b01, S2=2'b10} state, next;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"enum integer {IDLE, XX='x, S1='b01, S2='b10} state, next;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"enum integer {IDLE, XX='x, S1, S2} state, next;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"enum {bronze=3, silver, gold} medal; // silver=4, gold=5"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"enum {a=3, b=7, c} alphabet;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"enum {a=0, b=7, c, d=8} alphabet;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"enum {a, b=7, c} alphabet;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"enum bit [3:0] {bronze='h3, silver, gold='h5} medal2;

            // Correct declaration - bronze and gold sizes are redundant
            enum bit [3:0] {bronze=4'h3, silver, gold=4'h5} medal3;

            // Error in the bronze and gold member declarations
            enum bit [3:0] {bronze=5'h13, silver, gold=3'h5} medal4;

            // Error in c declaration, requires at least 2 bits
            enum bit [0:0] {a,b,c} alphabet;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"typedef enum {NO, YES} boolean;
            boolean myvar; // named type"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"typedef enum { add=10, sub[5], jmp[6:8] } E1;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"enum { register[2] = 1, register[2:4] = 10 } vr;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"typedef enum { red, green, blue, yellow, white, black } Colors;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"typedef enum { red, green, blue, yellow, white, black } Colors;

            Colors col;
            integer a, b;

            a = blue * 3;
            col = yellow;
            b = col + green;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"typedef enum {Red, Green, Blue} Colors;
            typedef enum {Mo,Tu,We,Th,Fr,Sa,Su} Week;
            Colors C;
            Week W;
            int I;

            C = Colors'(C+1);            // C is converted to an integer, then added to
                                         // one, then converted back to a Colors type

            C = Colors'(Su);             // Legal; puts an out of range value into C

            I = C + W;                   // Legal; C and W are automatically cast to int"##,
        Ok((_, _))
    );
    //test!(
    //    many1(module_item),
    //    r##"typedef enum { red, green, blue, yellow } Colors;
    //        Colors c = c.first;
    //        forever begin
    //          $display( "%s : %d\n", c.name, c );
    //          if( c == c.last ) break;
    //          c = c.next;
    //        end"##,
    //    Ok((_, _))
    //);
    test!(
        many1(module_item),
        r##"localparam byte colon1 = ":" ;
            specparam delay = 10 ; // specparams are used for specify blocks
            parameter logic flag = 1 ;"##,
        Ok((_, _))
    );
    test!(
        source_text,
        r##"class vector #(size = 1); // size is a parameter in a parameter port list
              logic [size-1:0] v;
            endclass
            interface simple_bus #(AWIDTH = 64, type T = word) // parameter port list
                                  (input logic clk) ; // port list
            endinterface"##,
        Ok((_, _))
    );
    //test!(
    //    source_text,
    //    r##"module mc #(int N = 5, M = N*16, type T = int, T x = 0)
    //        ();
    //        endmodule"##,
    //    Ok((_, _))
    //);
    test!(
        source_text,
        r##"class Mem #(type T, int size);
              T words[size];
            endclass

            typedef Mem#(byte, 1024) Kbyte;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"parameter msb = 7;       // defines msb as a constant value 7
            parameter e = 25, f = 9; // defines two constant numbers
            parameter r = 5.7;       // declares r as a real parameter
            parameter byte_size = 8,
                      byte_mask = byte_size - 1;
            parameter average_delay = (r + f) / 2;

            parameter signed [3:0] mux_selector = 0;
            parameter real r1 = 3.5e17;
            parameter p1 = 13'h7e;
            parameter [31:0] dec_const = 1'b1; // value converted to 32 bits
            parameter newconst = 3'h4;         // implied range of [2:0]
            parameter newconst = 4;            // implied range of at least [31:0]"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"parameter logic [31:0] P1 [3:0] = '{ 1, 2, 3, 4 } ; // unpacked array
                                                                // parameter declaration"##,
        Ok((_, _))
    );
    //test!(
    //    many1(module_item),
    //    r##"parameter r2 = $;
    //        property inq1(r1,r2);
    //          @(posedge clk) a ##[r1:r2] b ##1 c |=> d;
    //        endproperty
    //        assert property (inq1(3, r2));"##,
    //    Ok((_, _))
    //);
    //test!(
    //    many1(module_item),
    //    r##"interface quiet_time_checker #(parameter min_quiet = 0,
    //                                       parameter max_quiet = 0)
    //                                      (input logic clk, reset_n, logic [1:0]en);

    //          generate
    //            if ( max_quiet == 0) begin
    //              property quiet_time;
    //                @(posedge clk) reset_n |-> ($countones(en) == 1);
    //              endproperty
    //              a1: assert property (quiet_time);
    //            end
    //            else begin
    //              property quiet_time;
    //                @(posedge clk)
    //                  (reset_n && ($past(en) != 0) && en == 0)
    //                  |->(en == 0)[*min_quiet:max_quiet]
    //                ##1 ($countones(en) == 1);
    //              endproperty
    //              a1: assert property (quiet_time);
    //            end
    //            if ((min_quiet == 0) && ($isunbounded(max_quiet))
    //              $warning(warning_msg);
    //          endgenerate
    //        endinterface

    //        quiet_time_checker #(0, 0) quiet_never (clk,1,enables);
    //        quiet_time_checker #(2, 4) quiet_in_window (clk,1,enables);
    //        quiet_time_checker #(0, $) quiet_any (clk,1,enables);"##,
    //    Ok((_, _))
    //);
    //test!(
    //    many1(module_item),
    //    r##"interface width_checker #(parameter min_cks = 1, parameter max_cks = 1)
    //                                 (input logic clk, reset_n, expr);
    //          generate
    //            if ($isunbounded(max_cks)) begin
    //              property width;
    //                @(posedge clk)
    //                  (reset_n && $rose(expr)) |-> (expr [* min_cks]);
    //              endproperty
    //              a2: assert property (width);
    //            end
    //            else begin
    //              property assert_width_p;
    //                @(posedge clk)
    //                  (reset_n && $rose(expr)) |-> (expr[* min_cks:max_cks])
    //                    ##1 (!expr);
    //              endproperty
    //              a2: assert property (width);
    //            end
    //          endgenerate
    //        endinterface

    //        width_checker #(3, $) max_width_unspecified (clk,1,enables);
    //        width_checker #(2, 4) width_specified (clk,1,enables);"##,
    //    Ok((_, _))
    //);
    test!(
        source_text,
        r##"module ma #( parameter p1 = 1, parameter type p2 = shortint )
                       (input logic [p1:0] i, output logic [p1:0] o);
              p2 j = 0; // type of j is set by a parameter, (shortint unless redefined)
              always @(i) begin
                o = i;
                j++;
              end
            endmodule
            module mb;
              logic [3:0] i,o;
              ma #(.p1(3), .p2(int)) u1(i,o); //redefines p2 to a type of int
            endmodule"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"specify
              specparam tRise_clk_q = 150, tFall_clk_q = 200;
              specparam tRise_control = 40, tFall_control = 50;
            endspecify"##,
        Ok((_, _))
    );
    test!(
        source_text,
        r##"module RAM16GEN ( output [7:0] DOUT,
                              input [7:0] DIN,
                              input [5:0] ADR,
                              input WE, CE);
              specparam dhold = 1.0;
              specparam ddly = 1.0;
              parameter width = 1;
              parameter regsize = dhold + 1.0; // Illegal - cannot assign
                                               // specparams to parameters
            endmodule"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"const logic option = a.b.c ;"##,
        Ok((_, _))
    );
    //test!(
    //    many1(module_item),
    //    r##"const class_name object = new(5,3);"##,
    //    Ok((_, _))
    //);
    test!(
        source_text,
        r##"module msl;
              int st0;               // static
              initial begin
                int st1;             // static
                static int st2;      // static
                automatic int auto1; // automatic
              end
              task automatic t1();
                int auto2;           // automatic
                static int st3;      // static
                automatic int auto3; // automatic
              endtask
            endmodule"##,
        Ok((_, _))
    );
    test!(
        source_text,
        r##"module top_legal;
              int svar1 = 1;               // static keyword optional
              initial begin
                for (int i=0; i<3; i++) begin
                  automatic int loop3 = 0; // executes every loop
                  for (int j=0; j<3; j++) begin
                    loop3++;
                    $display(loop3);
                  end
                end // prints 1 2 3 1 2 3 1 2 3
                for (int i=0; i<3; i++) begin
                  static int loop2 = 0;    // executes once at time zero
                  for (int j=0; j<3; j++) begin
                    loop2++;
                    $display(loop2);
                  end
                end // prints 1 2 3 4 5 6 7 8 9
              end
            endmodule : top_legal

            module top_illegal;           // should not compile
              initial begin
                int svar2 = 2;            // static/automatic needed to show intent
                for (int i=0; i<3; i++) begin
                  int loop3 = 0;          // illegal statement
                  for (int i=0; i<3; i++) begin
                    loop3++;
                    $display(loop3);
                  end
                end
              end
            endmodule : top_illegal"##,
        Ok((_, _))
    );
    test!(
        source_text,
        r##"program automatic test ;
              int i;            // not within a procedural block - static
              task t ( int a ); // arguments and variables in t are automatic
              endtask
            endprogram"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"typedef bit node;    // 'bit' and 'node' are matching types
            typedef type1 type2; // 'type1' and 'type2' are matching types"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"struct packed {int A; int B;} AB1, AB2; // AB1, AB2 have matching types
            struct packed {int A; int B;} AB3; // the type of AB3 does not match
                                               // the type of AB1"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"typedef struct packed {int A; int B;} AB_t;
            AB_t AB1; AB_t AB2; // AB1 and AB2 have matching types

            typedef struct packed {int A; int B;} otherAB_t;
            otherAB_t AB3; // the type of AB3 does not match the type of AB1 or AB2"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"typedef bit signed [7:0] BYTE; // matches the byte type
            typedef bit signed [0:7] ETYB; // does not match the byte type"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"typedef byte MEM_BYTES [256];
            typedef bit signed [7:0] MY_MEM_BYTES [256]; // MY_MEM_BYTES matches
                                                         // MEM_BYTES

            typedef logic [1:0] [3:0] NIBBLES;
            typedef logic [7:0] MY_BYTE; // MY_BYTE and NIBBLES are not matching types

            typedef logic MD_ARY [][2:0];
            typedef logic MD_ARY_TOO [][0:2]; // Does not match MD_ARY"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"typedef byte signed MY_CHAR; // MY_CHAR matches the byte type"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"struct {int A; int B;} AB1, AB2; // AB1, AB2 have equivalent types
            struct {int A; int B;} AB3;      // AB3 is not type equivalent to AB1"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"typedef bit signed [7:0] BYTE; // equivalent to the byte type
            typedef struct packed signed {bit[3:0] a, b;} uint8;
                                           // equivalent to the byte type"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"bit [9:0] A [0:5];
            bit [1:10] B [6];
            typedef bit [10:1] uint10;
            uint10 C [6:1];          // A, B and C have equivalent types
            typedef int anint [0:0]; // anint is not type equivalent to int"##,
        Ok((_, _))
    );
    test!(
        source_text,
        r##"package p1;
              typedef struct {int A;} t_1;
            endpackage

            typedef struct {int A;} t_2;

            module sub();
              import p1::t_1;
              parameter type t_3 = int;
              parameter type t_4 = int;
              typedef struct {int A;} t_5;
              t_1 v1; t_2 v2; t_3 v3; t_4 v4; t_5 v5;
            endmodule

            module top();
              typedef struct {int A;} t_6;
              sub #(.t_3(t_6)) s1 ();
              sub #(.t_3(t_6)) s2 ();

              initial begin
                s1.v1 = s2.v1; // legal - both types from package p1 (rule 8)
                s1.v2 = s2.v2; // legal - both types from $unit (rule 4)
                s1.v3 = s2.v3; // legal - both types from top (rule 2)
                s1.v4 = s2.v4; // legal - both types are int (rule 1)
                s1.v5 = s2.v5; // illegal - types from s1 and s2 (rule 4)
              end
            endmodule"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"nettype nettypeid1 nettypeid2;"##,
        Ok((_, _))
    );
    //test!(
    //    many1(module_item),
    //    r##"var type(a+b) c, d;
    //        c = type(i+3)'(v[15:0]);"##,
    //    Ok((_, _))
    //);
    test!(
        many1(module_item),
        r##"localparam type T = type(bit[12:0]);"##,
        Ok((_, _))
    );
    //test!(
    //    many1(module_item),
    //    r##"bit [12:0] A_bus, B_bus;
    //        parameter type bus_t = type(A_bus);
    //        generate
    //          case (type(bus_t))
    //            type(bit[12:0]): addfixed_int #(bus_t) (A_bus,B_bus);
    //            type(real): add_float #(type(A_bus)) (A_bus,B_bus);
    //          endcase
    //        endgenerate"##,
    //    Ok((_, _))
    //);
    test!(
        many1(module_item),
        r##"A = cast_t1'(expr_1) + cast_t2'(expr_2);"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"cast_t1 temp1;
            cast_t2 temp2;

            temp1 = expr_1;
            temp2 = expr_2;
            A = temp1 + temp2;"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"logic [7:0] regA;
            logic signed [7:0] regS;

            regA = unsigned'(-4); // regA = 8'b11111100
            regS = signed'(4'b1100); // regS = -4"##,
        Ok((_, _))
    );
    test!(
        many1(module_item),
        r##"typedef struct {
              bit isfloat;
              union { int i; shortreal f; } n; // anonymous type
            } tagged_st;                       // named structure

            typedef bit [$bits(tagged_st) - 1 : 0] tagbits; // tagged_st defined above

            tagged_st a [7:0];                 // unpacked array of structures

            tagbits t = tagbits'(a[3]);        // convert structure to array of bits
            a[4] = tagged_st'(t);              // convert array of bits back to structure"##,
        Ok((_, _))
    );
    //test!(
    //    many1(module_item),
    //    r##"typedef enum { red, green, blue, yellow, white, black } Colors;
    //        Colors col;
    //        $cast( col, 2 + 3 );"##,
    //    Ok((_, _))
    //);
    //test!(
    //    many1(module_item),
    //    r##"if ( ! $cast( col, 2 + 8 ) ) // 10: invalid cast
    //          $display( "Error in cast" );"##,
    //    Ok((_, _))
    //);
    test!(many1(module_item), r##"col = Colors'(2 + 3);"##, Ok((_, _)));
    test!(many1(module_item), r##"B = dest_t'(A);"##, Ok((_, _)));
    test!(
        many1(module_item),
        r##"struct {bit[7:0] a; shortint b;} a;
            int b = int'(a);

            // Illegal conversion from 20-bit struct to int (32 bits) - run time error
            struct {bit a[$]; shortint b;} a = {{1,2,3,4}, 67};
            int b = int'(a);

            // Illegal conversion from int (32 bits) to struct dest_t (25 or 33 bits),
            // compile time error
            typedef struct {byte a[$]; bit b;} dest_t;
            int a;
            dest_t b = dest_t'(a);"##,
        Ok((_, _))
    );
    //test!(
    //    many1(module_item),
    //    r##"typedef struct {
    //          shortint address;
    //          logic [3:0] code;
    //          byte command [2];
    //        } Control;

    //        typedef bit Bits [36:1];

    //        Control p;
    //        Bits stream[$];

    //        stream.push_back(Bits'(p)); // append packet to unpacked queue of Bits
    //        Bits b;
    //        Control q;
    //        b = stream.pop_front();     // get packet (as Bits) from stream
    //        q = Control'(b);            // convert packet bits back to a Control packet"##,
    //    Ok((_, _))
    //);
    test!(
        many1(module_item),
        r##"typedef struct {
              byte length;
              shortint address;
              byte payload[];
              byte chksum;
            } Packet;"##,
        Ok((_, _))
    );
    //test!(
    //    many1(module_item),
    //    r##"function Packet genPkt();
    //          Packet p;

    //          void'( randomize( p.address, p.length, p.payload )
    //            with { p.length > 1 && p.payload.size == p.length; } );
    //          p.chksum = p.payload.xor();
    //          return p;
    //        endfunction"##,
    //    Ok((_, _))
    //);
    test!(
        many1(module_item),
        r##"typedef byte channel_type[$];
            channel_type channel;
            channel = {channel, channel_type'(genPkt())};"##,
        Ok((_, _))
    );
    //test!(
    //    many1(module_item),
    //    r##"Packet p;
    //        int size;

    //        size = channel[0] + 4;
    //        p = Packet'( channel[0 : size - 1] ); // convert stream to Packet
    //        channel = channel[ size : $ ];        // update the stream so it now
    //                                              // lacks that packet"##,
    //    Ok((_, _))
    //);
    test!(
        source_text,
        r##"virtual class C#(parameter type T = logic, parameter SIZE = 1);
              typedef logic [SIZE-1:0] t_vector;
              typedef T t_array [SIZE-1:0];
              typedef struct {
                t_vector m0 [2*SIZE-1:0];
                t_array m1;
              } t_struct;
            endclass"##,
        Ok((_, _))
    );
    test!(
        source_text,
        r##"module top ();
              typedef logic [7:0] t_t0;
              C#(t_t0,3)::t_vector v0;
              C#(t_t0,3)::t_array a0;
              C#(bit,4)::t_struct s0;
            endmodule"##,
        Ok((_, _))
    );
}

#[test]
fn test_debug() {
    test!(
        many1(module_item),
        r##"str = "123";
            int i = str.atoi(); // assigns 123 to i."##,
        Ok((_, _))
    );
}
