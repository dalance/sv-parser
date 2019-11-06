#![cfg(test)]

use crate::*;

macro_rules! test {
    ( $x:expr, $y:expr, $z:pat ) => {
        nom_packrat::init!();
        let info = SpanInfo::default();
        #[cfg(feature = "trace")]
        let info = info.set_tracable_info(
            info.get_tracable_info()
                //.fold("white_space")
                .fold("number")
                .fold("binary_operator")
                .fold("unary_operator"),
        );
        let ret = all_consuming($x)(Span::new_extra($y, info));
        if let $z = ret {
        } else {
            assert!(false, "{:?}", ret)
        }
    };
}

mod unit {
    use super::*;

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
    fn test_inout_declaration() {
        test!(inout_declaration, "inout a", Ok((_, _)));
        test!(inout_declaration, "inout [7:0] a", Ok((_, _)));
        test!(inout_declaration, "inout signed [7:0] a", Ok((_, _)));
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
        test!(comment, "//", Ok((_, _)));
        test!(comment, "/* comment\n\n */", Ok((_, _)));
        test!(comment, "/* comment\n//aaa\n */", Ok((_, _)));
        test!(comment, "/*! comment\n * aaa\n */", Ok((_, _)));
    }

    #[test]
    fn test_expression() {
        test!(expression, "(!a ? 0 : !b : 1 : c ? 0 : 1)", Ok((_, _)));
    }

    #[test]
    fn test_text_macro_definition() {
        test!(text_macro_definition, r##"`define a b c"##, Ok((_, _)));
        test!(
            text_macro_definition,
            r##"`define a b \
                          c"##,
            Ok((_, _))
        );
        test!(text_macro_definition, r##"`define a"##, Ok((_, _)));
        test!(
            source_text,
            r##"module test(out);
                  `define nest_two
                  `ifdef wow
                    initial $display("wow is defined");
                  `else
                    initial $display("wow is not defined");
                  `endif
                endmodule"##,
            Ok((_, _))
        );
    }

    #[test]
    fn test_regression() {
        test!(
            source_text,
            r##"package pkg; localparam [5:0] RES = RES5[0]; endpackage"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"interface intf (); localparam TYPE DEFAULT = TYPE'(0); endinterface"##,
            Ok((_, _))
        );
        test!(source_text, r##"`macro(A, B, logic, C)"##, Ok((_, _)));
        test!(source_text, r##"`macro(A, B, logic, a())"##, Ok((_, _)));
        test!(
            source_text,
            r##"module ibex_cs_registers;
                                 localparam logic [31:0] MISA_VALUE = 32'(RV32E);
                               endmodule"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"module ibex_cs_registers;
                                 localparam logic [31:0] MISA_VALUE = (32'(RV32E));
                               endmodule"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"module a; always_comb if ( a ? b : c ) begin end endmodule"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"module SimDTM; assign #0.1 debug_req_valid = __debug_req_valid; endmodule"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"`define LONG_MACRO(
                  a,
                  b, c) text goes here"##,
            Ok((_, _))
        );
    }
}

mod spec {
    use super::*;

    #[test]
    fn clause3() {
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
    fn clause4() {
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
    fn clause5() {
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
    fn clause6() {
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
        test!(
            many1(module_item),
            r##"str = "123";
                int i = str.atoi(); // assigns 123 to i."##,
            Ok((_, _))
        );
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
        test!(
            many1(module_item),
            r##"initial begin
                  typedef enum { red, green, blue, yellow } Colors;
                  Colors c = c.first;
                  forever begin
                    $display( "%s : %d\n", c.name, c );
                    if( c == c.last ) break;
                    c = c.next;
                  end
                end"##,
            Ok((_, _))
        );
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
        test!(
            source_text,
            r##"module mc #(int N = 5, M = N*16, type T = int, T x = 0)
                ();
                endmodule"##,
            Ok((_, _))
        );
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
        test!(
            many1(module_item),
            r##"parameter r2 = $;
                property inq1(r1,r2);
                  @(posedge clk) a ##[r1:r2] b ##1 c |=> d;
                endproperty
                assert property (inq1(3, r2));"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface quiet_time_checker #(parameter min_quiet = 0,
                                               parameter max_quiet = 0)
                                              (input logic clk, reset_n, logic [1:0]en);

                  generate
                    if ( max_quiet == 0) begin
                      property quiet_time;
                        @(posedge clk) reset_n |-> ($countones(en) == 1);
                      endproperty
                      a1: assert property (quiet_time);
                    end
                    else begin
                      property quiet_time;
                        @(posedge clk)
                          (reset_n && ($past(en) != 0) && en == 0)
                          |->(en == 0)[*min_quiet:max_quiet]
                        ##1 ($countones(en) == 1);
                      endproperty
                      a1: assert property (quiet_time);
                    end
                    if ((min_quiet == 0) && ($isunbounded(max_quiet)))
                      $warning(warning_msg);
                  endgenerate
                endinterface

                quiet_time_checker #(0, 0) quiet_never (clk,1,enables);
                quiet_time_checker #(2, 4) quiet_in_window (clk,1,enables);
                quiet_time_checker #(0, $) quiet_any (clk,1,enables);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface width_checker #(parameter min_cks = 1, parameter max_cks = 1)
                                         (input logic clk, reset_n, expr);
                  generate
                    if ($isunbounded(max_cks)) begin
                      property width;
                        @(posedge clk)
                          (reset_n && $rose(expr)) |-> (expr [* min_cks]);
                      endproperty
                      a2: assert property (width);
                    end
                    else begin
                      property assert_width_p;
                        @(posedge clk)
                          (reset_n && $rose(expr)) |-> (expr[* min_cks:max_cks])
                            ##1 (!expr);
                      endproperty
                      a2: assert property (width);
                    end
                  endgenerate
                endinterface

                width_checker #(3, $) max_width_unspecified (clk,1,enables);
                width_checker #(2, 4) width_specified (clk,1,enables);"##,
            Ok((_, _))
        );
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
        test!(
            many1(module_item),
            r##"const class_name object = new(5,3);"##,
            Ok((_, _))
        );
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
        test!(
            many1(module_item),
            r##"var type(a+b) c, d;
                c = type(i+3)'(v[15:0]);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"localparam type T = type(bit[12:0]);"##,
            Ok((_, _))
        );
        // TODO
        // What is addfixed_int/add_float? UDP?
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
        test!(
            many1(module_item),
            r##"initial begin
                  typedef enum { red, green, blue, yellow, white, black } Colors;
                  Colors col;
                  $cast( col, 2 + 3 );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  if ( ! $cast( col, 2 + 8 ) ) // 10: invalid cast
                    $display( "Error in cast" );
                end"##,
            Ok((_, _))
        );
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
        test!(
            many1(module_item),
            r##"typedef struct {
                  shortint address;
                  logic [3:0] code;
                  byte command [2];
                } Control;

                typedef bit Bits [36:1];

                Control p;
                Bits stream[$];

                initial begin
                  stream.push_back(Bits'(p)); // append packet to unpacked queue of Bits
                end

                initial begin
                  Bits b;
                  Control q;
                  b = stream.pop_front();     // get packet (as Bits) from stream
                  q = Control'(b);            // convert packet bits back to a Control packet
                end"##,
            Ok((_, _))
        );
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
        // TODO
        // randomize can't take hierarchical identifier
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
        // TODO
        // $ can't be parsed because it is not constant_primary
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          Packet p;
        //          int size;

        //          size = channel[0] + 4;
        //          p = Packet'( channel[0 : size - 1] ); // convert stream to Packet
        //          channel = channel[ size : $ ];        // update the stream so it now
        //                                                // lacks that packet
        //        end"##,
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
    fn clause7() {
        test!(
            many1(module_item),
            r##"struct { bit [7:0] opcode; bit [23:0] addr; }IR; // anonymous structure
                                                                 // defines variable IR
                initial begin
                  IR.opcode = 1; // set field in IR.
                end

                typedef struct {
                  bit [7:0] opcode;
                  bit [23:0] addr;
                } instruction; // named structure type
                instruction IR; // define variable"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"struct packed signed {
                  int a;
                  shortint b;
                  byte c;
                  bit [7:0] d;
                } pack1; // signed, 2-state

                struct packed unsigned {
                  time a;
                  integer b;
                  logic [31:0] c;
                } pack2; // unsigned, 4-state"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef struct packed { // default unsigned
                  bit [3:0] GFC;
                  bit [7:0] VPI;
                  bit [11:0] VCI;
                  bit CLP;
                  bit [3:0] PT ;
                  bit [7:0] HEC;
                  bit [47:0] [7:0] Payload;
                  bit [2:0] filler;
                } s_atmcell;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef struct {
                  int addr = 1 + constant;
                  int crc;
                  byte data [4] = '{4{1}};
                } packet1;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"packet1 p1; // initialization defined by the typedef.
                            // p1.crc will use the default value for an int"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"packet1 pi = '{1,2,'{2,3,4,5}}; //suppresses the typedef initialization"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef union { int i; shortreal f; } num; // named union type
                num n;

                initial begin
                  n.f = 0.0; // set n in floating point format
                end

                typedef struct {
                  bit isfloat;
                  union { int i; shortreal f; } n; // anonymous union type
                } tagged_st;                       // named structure"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef union packed { // default unsigned
                  s_atmcell acell;
                  bit [423:0] bit_slice;
                  bit [52:0][7:0] byte_slice;
                } u_atmcell;

                u_atmcell u1;
                byte b; bit [3:0] nib;
                b = u1.bit_slice[415:408]; // same as b = u1.byte_slice[51];
                nib = u1.bit_slice [423:420]; // same as nib = u1.acell.GFC;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef union tagged {
                  void Invalid;
                  int Valid;
                } VInt;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef union tagged {
                  struct {
                    bit [4:0] reg1, reg2, regd;
                  } Add;
                  union tagged {
                    bit [9:0] JmpU;
                    struct {
                      bit [1:0] cc;
                      bit [9:0] addr;
                    } JmpC;
                  } Jmp;
                } Instr;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [7:0] c1; // packed array of scalar bit types
                real u [7:0]; // unpacked array of real types"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"byte c2;    // same as bit signed [7:0] c2;
                integer i1; // same as logic signed [31:0] i1;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int Array[0:7][0:31]; // array declaration using ranges

                int Array[8][32];     // array declaration using sizes"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [7:0] mema [0:255]; // declares a memory array of 256 8-bit
                                          // elements. The array indices are 0 to 255

                mema[5] = 0;              // Write to word at address 5

                data = mema[addr];        // Read word at address indexed by addr"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [3:0] [7:0] joe [1:10]; // 10 elements of 4 8-bit bytes
                                            // (each element packed into 32 bits)"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"joe[9] = joe[8] + 1; // 4 byte add
                joe[7][3:2] = joe[6][1:0]; // 2 byte copy"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [1:10] v1 [1:5];  // 1 to 10 varies most rapidly; compatible with memory arrays

                bit v2 [1:5] [1:10];  // 1 to 10 varies most rapidly, compatible with C

                bit [1:5] [1:10] v3 ; // 1 to 10 varies most rapidly

                bit [1:5] [1:6] v4 [1:7] [1:8]; // 1 to 6 varies most rapidly, followed by
                                                // 1 to 5, then 1 to 8 and then 1 to 7"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef bit [1:5] bsix;
                bsix [1:10] v5; // 1 to 5 varies most rapidly"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef bsix mem_type [0:3]; // array of four 'bsix' elements
                mem_type ba [0:7];           // array of eight 'mem_type' elements"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int A[2][3][4], B[2][3][4], C[5][4];
                A[0][2] = B[1][1]; // assign a subarray composed of four ints
                A[1] = B[0];       // assign a subarray composed of three arrays of
                                   // four ints each
                A = B;             // assign an entire array
                A[0][1] = C[4];    // assign compatible subarray of four ints"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [7:0] [31:0] v7 [1:5] [1:10], v8 [0:255]; // two arrays declared"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [63:0] data;
                logic [7:0] byte2;
                byte2 = data[23:16]; // an 8-bit part-select from data"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [3:0] [7:0] j; // j is a packed array
                byte k;
                k = j[2]; // select a single 8-bit element from j"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit signed [31:0] busA [7:0] ; // unpacked array of 8 32-bit vectors
                int busB [1:0];                // unpacked array of 2 integers
                busB = busA[7:6];              // select a 2-vector slice from busA"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int i = bitvec[j +: k]; // k must be constant.
                int a[x:y], b[y:z], e;
                a = {b[c -: d], e};     // d must be constant"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [3:0] nibble[]; // Dynamic array of 4-bit vectors
                integer mem[2][];   // Fixed-size unpacked array composed
                                    // of 2 dynamic subarrays of integers"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int arr1 [][2][3] = new [4]; // arr1 sized to length 4; elements are
                                             // fixed-size arrays and so do not require
                                             // initializing

                int arr2 [][] = new [4];     // arr2 sized to length 4; dynamic subarrays
                                             // remain unsized and uninitialized"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int arr[2][][];
                initial begin
                  arr[0] = new [4];    // dynamic subarray arr[0] sized to length 4

                  arr[0][0] = new [2]; // legal, arr[0][n] created above for n = 0..3

                  arr[1][0] = new [2]; // illegal, arr[1] not initialized so arr[1][0] does
                                       // not exist

                  arr[0][1][1] = new[2]; // illegal, arr[0][1][1] is an int, not a dynamic
                                         // array
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int idest[], isrc[3] = '{5, 6, 7};
                initial begin
                  idest = new [3] (isrc); // set size and array element data values (5, 6, 7)
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int src[3], dest1[], dest2[];
                initial begin
                  src = '{2, 3, 4};
                  dest1 = new[2] (src); // dest1's elements are {2, 3}.
                  dest2 = new[4] (src); // dest2's elements are {2, 3, 4, 0}.
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"integer addr[];  // Declare the dynamic array.
                initial begin
                  addr = new[100]; // Create a 100-element array.
                  // Double the array size, preserving previous values.
                  // Preexisting references to elements of addr are outdated.
                  addr = new[200](addr);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  int j = addr.size;
                  addr = new[ addr.size() * 4 ] (addr); // quadruple addr array
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  int ab [] = new[ N ];      // create a temporary array of size N
                  // use ab
                  ab.delete;                 // delete the array contents
                  $display( "%d", ab.size ); // prints 0
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int A[10:1]; // fixed-size array of 10 elements
                int B[0:9];  // fixed-size array of 10 elements
                int C[24:1]; // fixed-size array of 24 elements
                A = B;       // ok. Compatible type and same size
                A = C;       // type check error: different sizes"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [7:0] V1[10:1];
                logic [7:0] V2[10];
                wire [7:0] W[9:0]; // data type is logic [7:0] W[9:0]
                assign W = V1;
                initial #10 V2 = W;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int A[2][100:1];
                int B[] = new[100];   // dynamic array of 100 elements
                int C[] = new[8];     // dynamic array of 8 elements
                int D [3][][];        // multidimensional array with dynamic subarrays
                initial begin
                  D[2] = new [2];     // initialize one of D's dynamic subarrays
                  D[2][0] = new [100];
                  A[1] = B;           // OK. Both are arrays of 100 ints
                  A[1] = C;           // type check error: different sizes (100 vs. 8 ints)
                  A = D[2];           // A[0:1][100:1] and subarray D[2][0:1][0:99] both
                                      // comprise 2 subarrays of 100 ints
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int A[100:1];     // fixed-size array of 100 elements
                int B[];          // empty dynamic array
                int C[] = new[8]; // dynamic array of size 8

                initial begin
                  B = A;          // ok. B has 100 elements
                  B = C;          // ok. B has 8 elements
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  B = new[ C.size ] (C);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"string d[1:5] = '{ "a", "b", "c", "d", "e" };
                string p[];
                p = { d[1:3], "hello", d[4:5] };"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int b[3:1][3:1];   // OK: same type, dimension, and size

                int b[1:3][0:2];   // OK: same type, dimension, & size (different ranges)

                logic b[3:1][3:1]; // error: incompatible element type

                event b[3:1][3:1]; // error: incompatible type

                int b[3:1];        // error: incompatible number of dimensions

                int b[3:1][4:1];   // error: incompatible size (3 vs. 4)"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"string b[4:1];       // OK: same type and size
                string b[5:2];       // OK: same type and size (different range)
                string b[] = new[4]; // OK: same type, number of dimensions, and
                                     // dimension size; requires run-time check"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"integer i_array[*];         // associative array of integer (unspecified
                                            // index)

                bit [20:0] array_b[string]; // associative array of 21-bit vector,
                                            // indexed by string

                event ev_array[myClass];    // associative array of event indexed by class
                                            // myClass"##,
            Ok((_, _))
        );
        test!(many1(module_item), r##"int array_name [*];"##, Ok((_, _)));
        test!(
            many1(module_item),
            r##"int array_name [ string ];"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int array_name [ some_Class ];"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int array_name1 [ integer ];
                typedef bit signed [4:1] SNibble;
                int array_name2 [ SNibble ];
                typedef bit [4:1] UNibble;
                int array_name3 [ UNibble ];"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef struct {byte B; int I[*];} Unpkt;
                int array_name [ Unpkt ];"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  int a[int] = '{default:1};
                  typedef struct { int x=1,y=2; } xy_t;
                  xy_t b[int];

                  begin
                    a[1]++;
                    b[2].x = 5;
                  end
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  int imem[int];
                  imem[ 3 ] = 1;
                  imem[ 16'hffff ] = 2;
                  imem[ 4'b1000 ] = 3;
                  $display( "%0d entries\n", imem.num ); // prints "3 entries"
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  int map[ string ];
                  map[ "hello" ] = 1;
                  map[ "sad" ] = 2;
                  map[ "world" ] = 3;
                  map.delete( "sad" ); // remove entry whose index is "sad" from "map"
                  map.delete;          // remove all entries from the associative array "map"
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  if ( map.exists( "hello" ))
                    map[ "hello" ] += 1;
                  else
                    map[ "hello" ] = 0;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  string s;
                  if ( map.first( s ) )
                    $display( "First entry is : map[ %s ] = %0d\n", s, map[s] );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  string s;
                  if ( map.last( s ) )
                    $display( "Last entry is : map[ %s ] = %0d\n", s, map[s] );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  string s;
                  if ( map.first( s ) )
                    do
                      $display( "%s : %d\n", s, map[ s ] );
                    while ( map.next( s ) );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  string s;
                  if ( map.last( s ) )
                    do
                      $display( "%s : %d\n", s, map[ s ] );
                    while ( map.prev( s ) );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  string aa[int];
                  byte ix;
                  int status;
                  aa[ 1000 ] = "a";
                  status = aa.first( ix );
                    // status is –1
                    // ix is 232 (least significant 8 bits of 1000)
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"string words [int] = '{default: "hello"};

                // an associative array of 4-state integers indexed by strings, default is –1
                integer tab [string] = '{"Peter":20, "Paul":22, "Mary":23, default:-1 };"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"byte q1[$];                  // A queue of bytes
                string names[$] = { "Bob" }; // A queue of strings with one element
                integer Q[$] = { 3, 2, 7 };  // An initialized queue of integers
                bit q2[$:255];               // A queue whose maximum size is 256 bits"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef mytype element_t; // mytype is any legal type for a queue
                typedef element_t queue_t[$];
                element_t e;
                queue_t Q;
                int i;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  for ( int j = 0; j < Q.size; j++ ) $display( Q[j] );
                end"##,
            Ok((_, _))
        );
        // TODO
        // $ can't be parsed because it is not constant_primary
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          int q[$] = { 2, 4, 8 };
        //          int e, pos;
        //          // assignment                    // method call yielding the
        //          //                               // same value in variable q
        //          // ----------------------------- // -------------------------
        //          q = { q, 6 };                    // q.push_back(6)
        //          q = { e, q };                    // q.push_front(e)
        //          q = q[1:$];                      // void'(q.pop_front()) or q.delete(0)
        //          q = q[0:$-1];                    // void'(q.pop_back()) or
        //                                           // q.delete(q.size-1)
        //          q = { q[0:pos-1], e, q[pos:$] }; // q.insert(pos, e)
        //          q = { q[0:pos], e, q[pos+1:$] }; // q.insert(pos+1, e)
        //          q = {};                          // q.delete()
        //        end"##,
        //    Ok((_, _))
        //);
        // TODO
        // $ can't be parsed because it is not constant_primary
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          q = q[2:$];   // a new queue lacking the first two items
        //          q = q[1:$-1]; // a new queue lacking the first and last items
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"initial begin
                  string SA[10], qs[$];
                  int IA[int], qi[$];

                  // Find all items greater than 5
                  qi = IA.find( x ) with ( x > 5 );
                  qi = IA.find( x ); // shall be an error

                  // Find indices of all items equal to 3
                  qi = IA.find_index with ( item == 3 );

                  // Find first item equal to Bob
                  qs = SA.find_first with ( item == "Bob" );

                  // Find last item equal to Henry
                  qs = SA.find_last( y ) with ( y == "Henry" );

                  // Find index of last item greater than Z
                  qi = SA.find_last_index( s ) with ( s > "Z" );

                  // Find smallest item
                  qi = IA.min;

                  // Find string with largest numerical value
                  qs = SA.max with ( item.atoi );

                  // Find all unique string elements
                  qs = SA.unique;

                  // Find all unique strings in lowercase
                  qs = SA.unique( s ) with ( s.tolower );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  string s[] = { "hello", "sad", "world" };
                  s.reverse;                              // s becomes { "world", "sad", "hello" };
                end

                initial begin
                  int q[$] = { 4, 5, 3, 1 };
                  q.sort;                                 // q becomes { 1, 3, 4, 5 }
                end

                initial begin
                  struct { byte red, green, blue; } c [512];
                  c.sort with ( item.red );               // sort c using the red field only
                  c.sort( x ) with ( {x.blue, x.green} ); // sort by blue then green
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  byte b[] = { 1, 2, 3, 4 };
                  int y;
                  y = b.sum ;                  // y becomes 10 => 1 + 2 + 3 + 4
                  y = b.product ;              // y becomes 24 => 1 * 2 * 3 * 4
                  y = b.xor with ( item + 4 ); // y becomes 12 => 5 ^ 6 ^ 7 ^ 8
                end

                initial begin
                  logic [7:0] m [2][2] = '{ '{5, 10}, '{15, 20} };
                  int y;
                  y = m.sum with (item.sum with (item)); // y becomes 50 => 5+10+15+20
                end

                initial begin
                  logic bit_arr [1024];
                  int y;
                  y = bit_arr.sum with ( int'(item) );   // forces result to be 32-bit
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  int arr[];
                  int q[$];

                  // find all items equal to their position (index)
                  q = arr.find with ( item == item.index );
                end"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause8() {
        test!(
            many1(module_item),
            r##"class Packet ;
                  //data or class properties
                  bit [3:0] command;
                  bit [40:0] address;
                  bit [4:0] master_id;
                  integer time_requested;
                  integer time_issued;
                  integer status;
                  typedef enum { ERR_OVERFLOW = 10, ERR_UNDERFLOW = 1123} PCKT_TYPE;
                  const integer buffer_size = 100;
                  const integer header_size;

                  // initialization
                  function new();
                    command = 4'd0;
                    address = 41'b0;
                    master_id = 5'bx;
                    header_size = 10;
                  endfunction

                  // methods
                  // public access entry points
                  task clean();
                    command = 0; address = 0; master_id = 5'bx;
                  endtask

                  task issue_request( int delay );
                    // send request to bus
                  endtask

                  function integer current_status();
                    current_status = status;
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"Packet p; // declare a variable of class Packet
                p = new;  // initialize variable to a new allocated object
                          // of the class Packet"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class obj_example;
                endclass

                task task1(integer a, obj_example myexample);
                  if (myexample == null) myexample = new;
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  Packet p = new;
                  int var1;
                  p.command = INIT;
                  p.address = $random;
                  packet_time = p.time_requested;
                  var1 = p.buffer_size;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial $display (p.ERR_OVERFLOW);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class vector #(parameter width = 7, type T = int);
                endclass

                vector #(3) v = new;
                initial $display (vector #(3)::T'(3.45)); // Typecasting
                initial $display ((v.T)'(3.45)); //ILLEGAL
                initial $display (v.width);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"Packet p = new;
                status = p.current_status();"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"status = current_status(p);"##,
            Ok((_, _))
        );
        test!(many1(module_item), r##"Packet p = new;"##, Ok((_, _)));
        test!(
            many1(module_item),
            r##"class Packet;
                  integer command;

                  function new();
                    command = IDLE;
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class C;
                  int c1 = 1;
                  int c2 = 1;
                  int c3 = 1;
                  function new(int a);
                    c2 = 2;
                    c3 = a;
                  endfunction
                endclass

                class D extends C;
                  int d1 = 4;
                  int d2 = c2;
                  int d3 = 6;
                  function new;
                    super.new(d3);
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"Packet p = new(STARTUP, $random, $time);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class c;
                  function new(int cmd = IDLE, bit[12:0] adrs = 0, int cmd_time );
                    command = cmd;
                    address = adrs;
                    time_requested = cmd_time;
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class C; endclass
                class D extends C; endclass
                C c = D::new; // variable c of superclass type C now references
                              // a newly constructed object of type D"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"D d = new;
                C c = d;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class E #(type T = int) extends C;
                  T x;
                  function new(T x_init);
                    super.new();
                    x = x_init;
                  endfunction
                endclass

                initial begin
                  c = E #(.T(byte))::new(.x_init(5));
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class Packet ;
                  static integer fileID = $fopen( "data", "r" );
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"Packet p;
                c = $fgetc( p.fileID );"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class id;
                  static int current = 0;
                  static function int next_id();
                    next_id = ++current; // OK to access static class property
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class TwoTasks;
                  static task t1(); endtask // static class method with
                                            // automatic variable lifetime

                  task static t2(); endtask // ILLEGAL: non-static class method with
                                            // static variable lifetime
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class Demo ;
                  integer x;

                  function new (integer x);
                    this.x = x;
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(many1(module_item), r##"Packet p1;"##, Ok((_, _)));
        test!(many1(module_item), r##"p1 = new;"##, Ok((_, _)));
        test!(
            many1(module_item),
            r##"Packet p2;
                p2 = p1;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"Packet p1;
                Packet p2;
                p1 = new;
                p2 = new p1;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class baseA ;
                  integer j = 5;
                endclass

                class B ;
                  integer i = 1;
                  baseA a = new;
                endclass
                class xtndA extends baseA;
                  rand int x;
                  constraint cst1 { x < 10; }
                endclass

                function integer test;
                  xtndA xtnd1;
                  baseA base2, base3;
                  B b1 = new;        // Create an object of class B
                  B b2 = new b1;     // Create an object that is a copy of b1
                  b2.i = 10;         // i is changed in b2, but not in b1
                  b2.a.j = 50;       // change a.j, shared by both b1 and b2
                  test = b1.i;       // test is set to 1 (b1.i has not changed)
                  test = b1.a.j;     // test is set to 50 (a.j has changed)
                  xtnd1 = new;       // create a new instance of class xtndA
                  xtnd1.x = 3;
                  base2 = xtnd1;     // base2 refers to the same object as xtnd1
                  base3 = new base2; // Creates a shallow copy of xtnd1
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  Packet p1 = new;
                  Packet p2 = new;
                  p2.copy(p1);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class LinkedPacket;
                  Packet packet_c;
                  LinkedPacket next;

                  function LinkedPacket get_next();
                    get_next = next;
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class LinkedPacket extends Packet;
                  LinkedPacket next;

                  function LinkedPacket get_next();
                    get_next = next;
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"LinkedPacket lp = new;
                Packet p = lp;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class Packet;
                  integer i = 1;
                  function integer get();
                    get = i;
                  endfunction
                endclass

                class LinkedPacket extends Packet;
                  integer i = 2;
                  function integer get();
                    get = -i;
                  endfunction
                endclass

                initial begin
                  LinkedPacket lp = new;
                  Packet p = lp;
                  j = p.i;     // j = 1, not 2
                  j = p.get(); // j = 1, not -1 or –2
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class Packet;                      // base class
                  integer value;
                  function integer delay();
                    delay = value * value;
                  endfunction
                endclass

                class LinkedPacket extends Packet; // derived class
                  integer value;
                  function integer delay();
                    delay = super.delay()+ value * super.value;
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class c;
                  function new();
                    super.new(5);
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class Packet;
                  local integer i;
                  function integer compare (Packet other);
                    compare = (this.i == other.i);
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class Jumbo_Packet;
                  const int max_size = 9 * 1024; // global constant
                  byte payload [];
                  function new( int size );
                    payload = new[ size > max_size ? max_size : size ];
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class Big_Packet;
                  const int size; // instance constant
                  byte payload [];
                  function new();
                    size = $urandom % 4096; //one assignment in new -> ok
                    payload = new[ size ];
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class BasePacket;
                  int A = 1;
                  int B = 2;
                  function void printA;
                    $display("BasePacket::A is %d", A);
                  endfunction : printA
                  virtual function void printB;
                    $display("BasePacket::B is %d", B);
                  endfunction : printB
                endclass : BasePacket

                class My_Packet extends BasePacket;
                  int A = 3;
                  int B = 4;
                  function void printA;
                    $display("My_Packet::A is %d", A);
                  endfunction: printA
                  virtual function void printB;
                    $display("My_Packet::B is %d", B);
                  endfunction : printB
                endclass : My_Packet

                BasePacket P1 = new;
                My_Packet P2 = new;

                initial begin
                  P1.printA; // displays 'BasePacket::A is 1'
                  P1.printB; // displays 'BasePacket::B is 2'
                  P1 = P2;   // P1 has a handle to a My_packet object
                  P1.printA; // displays 'BasePacket::A is 1'
                  P1.printB; // displays 'My_Packet::B is 4' – latest derived method
                  P2.printA; // displays 'My_Packet::A is 3'
                  P2.printB; // displays 'My_Packet::B is 4'
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef int T; // T and int are matching data types.
                class C;
                  virtual function C some_method(int a); endfunction
                endclass

                class D extends C;
                  virtual function D some_method(T a); endfunction
                endclass

                class E #(type Y = logic) extends C;
                  virtual function D some_method(Y a); endfunction
                endclass

                E #() v1;    // Illegal: type parameter Y resolves to logic, which is not
                             // a matching type for argument a
                E #(int) v2; // Legal: type parameter Y resolves to int"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"virtual class BasePacket;
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"virtual class BasePacket;
                  pure virtual function integer send(bit[31:0] data); // No implementation
                endclass

                class EtherPacket extends BasePacket;
                  virtual function integer send(bit[31:0] data);
                    // body of the function
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class c;
                  virtual function integer send(bit[31:0] data); // Will return 'x
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"BasePacket packets[100];"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"EtherPacket ep = new; // extends BasePacket
                TokenPacket tp = new; // extends BasePacket
                GPSPacket gp = new;   // extends EtherPacket
                packets[0] = ep;
                packets[1] = tp;
                packets[2] = gp;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  packets[1].send();
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class Base;
                  typedef enum {bin,oct,dec,hex} radix;
                  static task print( radix r, integer n ); endtask
                endclass

                initial begin
                  Base b = new;
                  int bin = 123;
                  b.print( Base::bin, bin ); // Base::bin and bin are different
                  Base::print( Base::hex, 66 );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class StringList;
                  class Node; // Nested class for a node in a linked list.
                    string name;
                    Node link;
                  endclass
                endclass

                class StringTree;
                  class Node; // Nested class for a node in a binary tree.
                    string name;
                    Node left, right;
                  endclass
                endclass
                // StringList::Node is different from StringTree::Node"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class Outer;
                  int outerProp;
                  local int outerLocalProp;
                  static int outerStaticProp;
                  static local int outerLocalStaticProp;
                  class Inner;
                    function void innerMethod(Outer h);
                      outerStaticProp = 0;
                        // Legal, same as Outer::outerStaticProp
                      outerLocalStaticProp = 0;
                        // Legal, nested classes may access local's in outer class
                      outerProp = 0;
                        // Illegal, unqualified access to non-static outer
                      h.outerProp = 0;
                        // Legal, qualified access.
                      h.outerLocalProp = 0;
                        // Legal, qualified access and locals to outer class allowed.
                    endfunction
                  endclass
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class Packet;
                  Packet next;
                  function Packet get_next();// single line
                    get_next = next;
                  endfunction

                  // out-of-body (extern) declaration
                  extern protected virtual function int send(int value);
                endclass

                function int Packet::send(int value);
                  // dropped protected virtual, added Packet::
                  // body of method
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef real T;

                class C;
                  typedef int T;
                  extern function T f();
                  extern function real f2();
                endclass

                function C::T C::f(); // the return must use the class scope resolution
                                      // operator, since the type is defined within the
                                      // class
                  return 1;
                endfunction

                function real C::f2();
                  return 1.0;
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef int T;
                class C;
                  extern function void f(T x);
                  typedef real T;
                endclass

                function void C::f(T x);
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class vector #(int size = 1);
                  bit [size-1:0] a;
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"vector #(10) vten;        // object with vector of size 10
                vector #(.size(2)) vtwo;  // object with vector of size 2
                typedef vector#(4) Vfour; // Class with vector of size 4"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class stack #(type T = int);
                  local T items[];
                  task push( T a ); endtask
                  task pop( ref T a ); endtask
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"stack is;             // default: a stack of ints
                stack#(bit[1:10]) bs; // a stack of 10-bit vectors
                stack#(real) rs;      // a stack of real numbers"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class vector #(int size = 1);
                  bit [size-1:0] a;
                  static int count = 0;
                  function void disp_count();
                    $display( "count: %d of size %d", count, size );
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef vector my_vector; // use default size of 1
                vector#(6) vx;            // use size 6"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef vector#(4) Vfour;
                typedef stack#(Vfour) Stack4;
                Stack4 s1, s2; // declare objects of type Stack4"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class C #(type T = bit); endclass                        // base class
                class D1 #(type P = real) extends C; endclass            // T is bit (the default)
                class D2 #(type P = real) extends C #(integer); endclass // T is integer
                class D3 #(type P = real) extends C #(P); endclass       // T is P
                class D4 #(type P = C#(real)) extends P; endclass        // for default, T is real"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class C #(int p = 1);
                endclass
                class D #(int p);
                endclass
                C obj; // legal; equivalent to "C#() obj";
                D obj; // illegal; D has no default specialization"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class C #(int p = 1);
                  parameter int q = 5; // local parameter
                  static task t;
                    int p;
                    int x = C::p; // C::p disambiguates p
                                  // C::p is not p in the default specialization
                  endtask
                endclass

                int x = C::p;     // illegal; C:: is not permitted in this context
                int y = C#()::p;  // legal; refers to parameter p in the default
                                  // specialization of C
                typedef C T;      // T is a default specialization, not an alias to
                                  // the name "C"
                int z = T::p;     // legal; T::p refers to p in the default specialization
                int v = C#(3)::p; // legal; parameter p in the specialization of C#(3)
                int w = C#()::q;  // legal; refers to the local parameter
                T obj = new();
                int u = obj.q;    // legal; refers to the local parameter
                bit arr[obj.q];   // illegal: local parameter is not a constant expression"##,
            Ok((_, _))
        );
        // BNF-WA
        // reported at https://accellera.mantishub.io/view.php?id=1642
        // class static method is denied because ps_or_hierarchical_tf_identifier doesn't have class_scope.
        test!(
            many1(module_item),
            r##"class C #(int p = 1, type T = int);
                  extern static function T f();
                endclass

                function C::T C::f();
                  return p + C::p;
                endfunction

                initial $display("%0d %0d", C#()::f(),C#(5)::f()); // output is "2 10""##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface class A;
                endclass

                class B implements A;
                endclass

                class C extends B;
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface class PutImp#(type PUT_T = logic);
                  pure virtual function void put(PUT_T a);
                endclass

                interface class GetImp#(type GET_T = logic);
                  pure virtual function GET_T get();
                endclass

                class Fifo#(type T = logic, int DEPTH=1) implements PutImp#(T), GetImp#(T);
                  T myFifo [$:DEPTH-1];
                  virtual function void put(T a);
                    myFifo.push_back(a);
                  endfunction
                  virtual function T get();
                    get = myFifo.pop_front();
                  endfunction
                endclass

                class Stack#(type T = logic, int DEPTH=1) implements PutImp#(T), GetImp#(T);
                  T myFifo [$:DEPTH-1];
                  virtual function void put(T a);
                    myFifo.push_front(a);
                  endfunction
                  virtual function T get();
                    get = myFifo.pop_front();
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface class PutImp#(type PUT_T = logic);
                  pure virtual function void put(PUT_T a);
                endclass

                interface class GetImp#(type GET_T = logic);
                  pure virtual function GET_T get();
                endclass

                class MyQueue #(type T = logic, int DEPTH = 1);
                  T PipeQueue[$:DEPTH-1];
                  virtual function void deleteQ();
                    PipeQueue.delete();
                  endfunction
                endclass

                class Fifo #(type T = logic, int DEPTH = 1)
                    extends MyQueue#(T, DEPTH)
                    implements PutImp#(T), GetImp#(T);
                  virtual function void put(T a);
                    PipeQueue.push_back(a);
                  endfunction
                  virtual function T get();
                    get = PipeQueue.pop_front();
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"virtual class XFifo#(type T_in = logic, type T_out = logic, int DEPTH = 1)
                                     extends MyQueue#(T_out)
                                     implements PutImp#(T_in), GetImp#(T_out);
                  pure virtual function T_out translate(T_in a);
                  virtual function void put(T_in a);
                    PipeQueue.push_back(translate(a));
                  endfunction
                  virtual function T_out get();
                    get = PipeQueue.pop_front();
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface class IntfClass;
                  pure virtual function bit funcBase();
                  pure virtual function bit funcExt();
                endclass

                class BaseClass;
                  virtual function bit funcBase();
                    return (1);
                  endfunction
                endclass

                class ExtClass extends BaseClass implements IntfClass;
                  virtual function bit funcExt();
                    return (0);
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface class IntfClass;
                  pure virtual function void f();
                endclass

                class BaseClass;
                  function void f();
                    $display("Called BaseClass::f()");
                  endfunction
                endclass

                class ExtClass extends BaseClass implements IntfClass;
                  virtual function void f();
                    $display("Called ExtClass::f()");
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface class IntfA #(type T1 = logic);
                  typedef T1[1:0] T2;
                  pure virtual function T2 funcA();
                endclass : IntfA

                interface class IntfB #(type T = bit) extends IntfA #(T);
                  pure virtual function T2 funcB(); // legal, type T2 is inherited
                endclass : IntfB"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface class IntfC;
                  typedef enum {ONE, TWO, THREE} t1_t;
                  pure virtual function t1_t funcC();
                endclass : IntfC

                class ClassA implements IntfC;
                  t1_t t1_i; // error, t1_t is not inherited from IntfC
                  virtual function IntfC::t1_t funcC(); // correct
                    return (IntfC::ONE); // correct
                  endfunction : funcC
                endclass : ClassA"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class Fifo #(type T = PutImp) implements T; endclass
                virtual class Fifo #(type T = PutImp) implements T; endclass
                interface class Fifo #(type T = PutImp) extends T; endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef interface class IntfD;

                class ClassB implements IntfD #(bit); // illegal
                  virtual function bit[1:0] funcD();
                  endfunction
                endclass : ClassB

                // This interface class declaration must be declared before ClassB
                interface class IntfD #(type T1 = logic);
                  typedef T1[1:0] T2;
                  pure virtual function T2 funcD();
                endclass : IntfD"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class Fifo #(type T = int) implements PutImp#(T), GetImp#(T);
                endclass
                Fifo#(int) fifo_obj = new;
                PutImp#(int) put_ref = fifo_obj;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  GetImp#(int) get_ref;
                  Fifo#(int) fifo_obj = new;
                  PutImp#(int) put_ref = fifo_obj;
                  $cast(get_ref, put_ref);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  $cast(fifo_obj, put_ref); // legal
                  $cast(put_ref, fifo_obj); // legal, but casting is not required
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"put_ref = new(); // illegal"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface class IntfBase1;
                  pure virtual function bit funcBase();
                endclass

                interface class IntfBase2;
                  pure virtual function bit funcBase();
                endclass

                virtual class ClassBase;
                  pure virtual function bit funcBase();
                endclass

                class ClassExt extends ClassBase implements IntfBase1, IntfBase2;
                  virtual function bit funcBase();
                    return (0);
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface class IntfBaseA;
                  pure virtual function bit funcBase();
                endclass

                interface class IntfBaseB;
                  pure virtual function string funcBase();
                endclass

                class ClassA implements IntfBaseA, IntfBaseB;
                  virtual function bit funcBase();
                    return (0);
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface class PutImp#(type T = logic);
                  pure virtual function void put(T a);
                endclass

                interface class GetImp#(type T = logic);
                  pure virtual function T get();
                endclass

                interface class PutGetIntf#(type TYPE = logic)
                                            extends PutImp#(TYPE), GetImp#(TYPE);
                  typedef TYPE T;
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface class IntfBase;
                  parameter SIZE = 64;
                endclass

                interface class IntfExt1 extends IntfBase;
                  pure virtual function bit funcExt1();
                endclass

                interface class IntfExt2 extends IntfBase;
                  pure virtual function bit funcExt2();
                endclass

                interface class IntfExt3 extends IntfExt1, IntfExt2;
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface class IntfBase #(type T = int);
                  pure virtual function bit funcBase();
                endclass

                interface class IntfExt1 extends IntfBase#(bit);
                  pure virtual function bit funcExt1();
                endclass

                interface class IntfExt2 extends IntfBase#(logic);
                  pure virtual function bit funcExt2();
                endclass

                interface class IntfFinal extends IntfExt1, IntfExt2;
                  typedef bit T; // Override the conflicting identifier name
                  pure virtual function bit funcBase();
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface class IntfClass;
                  pure virtual function bit funcA();
                  pure virtual function bit funcB();
                endclass

                // Partial implementation of IntfClass
                virtual class ClassA implements IntfClass;
                  virtual function bit funcA();
                    return (1);
                  endfunction
                  pure virtual function bit funcB();
                endclass

                // Complete implementation of IntfClass
                class ClassB extends ClassA;
                  virtual function bit funcB();
                    return (1);
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef class C2; // C2 is declared to be of type class
                class C1;
                  C2 c;
                endclass
                class C2;
                  C1 c;
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef class C ;
                module top ;
                  C#(1, real) v2 ; // positional parameter override
                  C#(.p(2), .T(real)) v3 ; // named parameter override
                endmodule

                class C #(parameter p = 2, type T = int);
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  myClass obj = new;
                  fork
                    task1( obj );
                    task2( obj );
                  join_none
                end"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause9() {
        test!(
            many1(module_item),
            r##"initial begin
                  a = 0; // initialize a
                  for (int index = 0; index < size; index++)
                    memory[index] = 0; // initialize memory word
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  inputs = 'b000000;     // initialize at time zero
                  #10 inputs = 'b011001; // first pattern
                  #10 inputs = 'b011011; // second pattern
                  #10 inputs = 'b011000; // third pattern
                  #10 inputs = 'b001000; // last pattern
                end"##,
            Ok((_, _))
        );
        test!(many1(module_item), r##"always areg = ~areg;"##, Ok((_, _)));
        test!(
            many1(module_item),
            r##"always #half_period areg = ~areg;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always_comb
                  a = b & c;
                always_comb
                  d <= #1ns b & c;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always_comb
                begin
                  a = b & c;
                  A1:assert (a != e) else if (!disable_error) $error("failed");
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always_latch
                  if(ck) q <= d;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always_ff @(posedge clock iff reset == 0 or posedge reset) begin
                  r1 <= reset ? 0 : r2 + 1;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"final
                  begin
                    $display("Number of cycles executed %d",$time/period);
                    $display("Final PC = %h",PC);
                  end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  areg = breg;
                  creg = areg; // creg stores the value of breg
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  areg = breg;
                  @(posedge clock) creg = areg; // assignment delayed until
                end                             // posedge on clock"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"parameter d = 50; // d declared as a parameter and
                logic [7:0] r;    // r declared as an 8-bit variable
                initial begin // a waveform controlled by sequential delays
                  #d r = 'h35;
                  #d r = 'hE2;
                  #d r = 'h00;
                  #d r = 'hF7;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fork
                    #50 r = 'h35;
                    #100 r = 'hE2;
                    #150 r = 'h00;
                    #200 r = 'hF7;
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fork
                    begin
                      statement1; // one process with 2 statements
                      statement2;
                    end
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fork
                    begin
                      $display( "First Block\n" );
                      # 20ns;
                    end
                    begin
                      $display( "Second Block\n" );
                      @eventA;
                    end
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task wait_20;
                  fork
                    # 20;
                    return ; // Illegal: cannot return; task lives in another process
                  join_none
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial
                  for( int j = 1; j <= 3; ++j )
                    fork
                      automatic int k = j; // local copy, k, for each value of j
                      #k $write( "%0d", k );
                      begin
                        automatic int m = j; // the value of m is undetermined
                      end
                    join_none"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fork
                    #200 r = 'hF7;
                    #150 r = 'h00;
                    #100 r = 'hE2;
                    #50 r = 'h35;
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fork
                    @Aevent;
                    @Bevent;
                  join
                  areg = breg;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fork
                    @enable_a
                      begin
                        #ta wa = 0;
                        #ta wa = 1;
                        #ta wa = 0;
                      end
                    @enable_b
                      begin
                        #tb wb = 1;
                        #tb wb = 0;
                        #tb wb = 1;
                      end
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin: blockB // block name after the begin or fork
                end: blockB"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  labelB: fork // label before the begin or fork
                  join_none : labelB
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  #10 rega = regb;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  #d rega = regb;         // d is defined as a parameter
                  #((d+e)/2) rega = regb; // delay is average of d and e
                  #regr regr = regr + 1;  // delay is the value in regr
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @r rega = regb;                       // controlled by any value change in the reg r
                  @(posedge clock) rega = regb;         // controlled by posedge on clock
                  forever @(negedge clock) rega = regb; // controlled by negedge on clock
                  forever @(edge clock) rega = regb;    // controlled by edge on clock
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"real AOR[];                       // dynamic array of reals
                byte stream[$];                   // queue of bytes
                initial wait(AOR.size() > 0);     // waits for array to be allocated
                initial wait($bits(stream) > 60); // waits for total number of bits
                                                  // in stream greater than 60

                Packet p = new; // Packet 1 -- Packet is defined in 8.2
                Packet q = new; // Packet 2
                initial fork
                  @(p.status); // Wait for status in Packet 1 to change
                  @p;          // Wait for a change to handle p
                  # 10 p = q;  // triggers @p.
                  // @(p.status) now waits for status in Packet 2 to change,
                  // if not already different from Packet 1
                join"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @(trig or enable) rega = regb; // controlled by trig or enable

                  @(posedge clk_a or posedge clk_b or trig) rega = regb;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(a, b, c, d, e);
                always @(posedge clk, negedge rstn);
                always @(a or b, c, d or e);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(*) // equivalent to @(a or b or c or d or f)
                    y = (a & b) | (c & d) | myfunction(f);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @* begin // equivalent to @(a or b or c or d or tmp1 or tmp2)
                  tmp1 = a & b;
                  tmp2 = c & d;
                  y = tmp1 | tmp2;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @* begin // equivalent to @(b)
                  @(i) kid = b; // i is not added to @*
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @* begin // equivalent to @(a or b or c or d)
                  x = a ^ b;
                  @*            // equivalent to @(c or d)
                  x = c ^ d;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @* begin // same as @(a or en)
                  y = 8'hff;
                  y[a] = !en;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @* begin // same as @(state or go or ws)
                  next = 4'b0;
                  case (1'b1)
                    state[IDLE]: if (go)  next[READ] = 1'b1;
                                 else     next[IDLE] = 1'b1;
                    state[READ]:          next[DLY ] = 1'b1;
                    state[DLY ]: if (!ws) next[DONE] = 1'b1;
                                 else     next[READ] = 1'b1;
                    state[DONE]:          next[IDLE] = 1'b1;
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module latch (output logic [31:0] y, input [31:0] a, input enable);
                  always @(a iff enable == 1)
                    y <= a; //latch is in transparent mode
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence abc;
                  @(posedge clk) a ##1 b ##1 c;
                endsequence

                program test;
                  initial begin
                    @ abc $display( "Saw a-b-c" );
                  end
                endprogram"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  wait (!enable) #10 a = b;
                  #10 c = d;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence abc;
                  @(posedge clk) a ##1 b ##1 c;
                endsequence

                sequence de;
                  @(negedge clk) d ##[2:5] e;
                endsequence

                program check;
                  initial begin
                    wait( abc.triggered || de.triggered );
                    if( abc.triggered )
                      $display( "abc succeeded" );
                    if( de.triggered )
                      $display( "de succeeded" );
                  end
                endprogram"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  repeat (3) @ (event_expression);
                    // will execute event_expression three times
                  repeat (-3) @ (event_expression);
                    // will not execute event_expression.
                  repeat (a) @ (event_expression);
                    // if a is assigned -3, it will execute the event_expression if a is
                    // declared as an unsigned variable, but not if a is signed
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fork
                    #5 a = b;
                    #5 b = a;
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fork // data swap
                    a = #5 b;
                    b = #5 a;
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fork // data shift
                    a = @(posedge clk) b;
                    b = @(posedge clk) c;
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  a <= repeat(5) @(posedge clk) data;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  a = repeat(num) @(clk) data;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  a <= repeat(a+b) @(posedge phi1 or negedge phi2) data;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  a <= repeat(a+b) @(edge phi1) data;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin : test
                  fork
                    child1();
                    child2();
                  join_none
                  do_test();
                end : test

                task do_test();
                  fork
                    child3();
                    child4();
                    fork : child5 // nested fork-join_none is a child process
                      descendant1();
                      descendant2();
                    join_none
                  join_none
                  do_sequence();
                  wait fork; // block until child1 ... child7 complete
                endtask

                function void do_sequence();
                  fork
                    child6();
                    child7();
                  join_none
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin : block_name
                  rega = regb;
                  disable block_name;
                  regc = rega; // this assignment will never execute
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin : block_name
                if (a == 0)
                  disable block_name;
                end // end of named block
                    // continue with code following named block"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m ();
                  always
                    begin : always1
                      t1: task1( ); // task call
                    end

                  always
                    begin
                      disable m.always1; // exit always1, which will exit task1,
                                         // if it was currently executing
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task proc_a;
                  begin
                    if (a == 0)
                      disable proc_a; // return if true
                  end
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin : outer_block
                  for (i = 0; i < n; i = i+1) begin : inner_block
                    @clk
                      if (a == 0) // "continue" loop
                        disable inner_block ;
                    @clk
                      if (a == b) // "break" from loop
                        disable outer_block;
                  end
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fork
                    begin : event_expr
                      @ev1;
                      repeat (3) @trig;
                      #d action (areg, breg);
                    end
                    @reset disable event_expr;
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always begin : monostable
                  #250 q = 0;
                end

                always @retrig begin
                  disable monostable;
                  q = 1;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task get_first( output int adr );
                  fork
                    wait_device( 1, adr );
                    wait_device( 7, adr );
                    wait_device( 13, adr );
                  join_any
                  disable fork;
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task automatic do_n_way( int N );
                  process job[] = new [N];

                  foreach (job[j])
                    fork
                      automatic int k = j;
                      begin job[k] = process::self(); end
                    join_none

                  foreach (job[j]) // wait for all processes to start
                    wait( job[j] != null );
                  job[1].await(); // wait for first process to finish

                  foreach (job[j]) begin
                    if ( job[j].status != process::FINISHED )
                      job[j].kill();
                  end
                endtask"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause10() {
        test!(
            many1(module_item),
            r##"initial begin
                  #1ns r = a;
                  r = #1ns a;
                  r <= #1ns a;
                end
                assign #2.5ns sum = a + b;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"wire (strong1, pull0) mynet = enable;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"wire mynet ;
                assign (strong1, pull0) mynet = enable;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module adder (sum_out, carry_out, carry_in, ina, inb);
                  output [3:0] sum_out;
                  output carry_out;
                  input [3:0] ina, inb;
                  input carry_in;

                  wire carry_out, carry_in;
                  wire [3:0] sum_out, ina, inb;

                  assign {carry_out, sum_out} = ina + inb + carry_in;
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module select_bus(busout, bus0, bus1, bus2, bus3, enable, s);
                  parameter n = 16;
                  parameter Zee = 16'bz;
                  output [1:n] busout;
                  input [1:n] bus0, bus1, bus2, bus3;
                  input enable;
                  input [1:2] s;

                  tri [1:n] data; // net declaration

                  // net declaration with continuous assignment
                  tri [1:n] busout = enable ? data : Zee;

                  // assignment statement with four continuous assignments
                  assign
                    data = (s == 0) ? bus0 : Zee,
                    data = (s == 1) ? bus1 : Zee,
                    data = (s == 2) ? bus2 : Zee,
                    data = (s == 3) ? bus3 : Zee;
                endmodule"##,
            Ok((_, _))
        );
        test!(many1(module_item), r##"wire #10 wireA;"##, Ok((_, _)));
        test!(
            many1(module_item),
            r##"initial begin
                  rega = 0;
                  rega[3] = 1;                // a bit-select
                  rega[3:5] = 7;              // a part-select
                  mema[address] = 8'hff;      // assignment to a mem element
                  {carry, acc} = rega + regb; // a concatenation
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module evaluates (out);
                  output out;
                  logic a, b, c;

                  initial begin
                    a = 0;
                    b = 1;
                    c = 0;
                  end

                  always c = #5 ~c;

                  always @(posedge c) begin
                    a <= b; // evaluates, schedules,
                    b <= a; // and executes in two steps
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module nonblock1;
                  logic a, b, c, d, e, f;

                  // blocking assignments
                  initial begin
                    a = #10 1; // a will be assigned 1 at time 10
                    b = #2 0; // b will be assigned 0 at time 12
                    c = #4 1; // c will be assigned 1 at time 16
                  end

                  // nonblocking assignments
                  initial begin
                    d <= #10 1; // d will be assigned 1 at time 10
                    e <= #2 0; // e will be assigned 0 at time 2
                    f <= #4 1; // f will be assigned 1 at time 4
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module nonblock2;
                  logic a, b;
                  initial begin
                    a = 0;
                    b = 1;
                    a <= b; // evaluates, schedules,
                    b <= a; // and executes in two steps
                  end

                  initial begin
                    $monitor ($time, ,"a = %b b = %b", a, b);
                    #100 $finish;
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module multiple;
                  logic a;
                  initial a = 1;
                    // The assigned value of the variable is determinate

                  initial begin
                    a <= #4 0; // schedules a = 0 at time 4
                    a <= #4 1; // schedules a = 1 at time 4
                  end          // At time 4, a = 1
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module multiple2;
                  logic a;

                  initial a = 1;
                  initial a <= #4 0; // schedules 0 at time 4
                  initial a <= #4 1; // schedules 1 at time 4

                  // At time 4, a = ??
                  // The assigned value of the variable is indeterminate
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module multiple3;
                  logic a;
                  initial #8 a <= #8 1;  // executed at time 8;
                                         // schedules an update of 1 at time 16
                  initial #12 a <= #4 0; // executed at time 12;
                                         // schedules an update of 0 at time 16

                  // Because it is determinate that the update of a to the value 1
                  // is scheduled before the update of a to the value 0,
                  // then it is determinate that a will have the value 0
                  // at the end of time slot 16.
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module multiple4;
                  logic r1;
                  logic [2:0] i;

                  initial begin
                    // makes assignments to r1 without cancelling previous assignments
                    for (i = 0; i <= 5; i++)
                      r1 <= # (i*10) i[0];
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"wire w = vara & varb;      // net with a continuous assignment

                logic v = consta & constb; // variable with initialization"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  force a = b + f(c) ;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module dff (q, d, clear, preset, clock);
                  output q;
                  input d, clear, preset, clock;
                  logic q;

                  always @(clear or preset)
                    if (!clear)
                      assign q = 0;
                    else if (!preset)
                      assign q = 1;
                    else
                      deassign q;

                  always @(posedge clock)
                    q = d;
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module test;
                  logic a, b, c, d;
                  wire e;

                  and and1 (e, a, b, c);

                  initial begin
                    $monitor("%d d=%b,e=%b", $stime, d, e);
                    assign d = a & b & c;
                    a = 1;
                    b = 0;
                    c = 1;
                    #10;
                    force d = (a | b | c);
                    force e = (a | b | c);
                    #10;
                    release d;
                    release e;
                    #10 $finish;
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [5:0] a;
                logic signed [4:0] b;

                initial begin
                  a = 8'hff; // After the assignment, a = 6'h3f
                  b = 8'hff; // After the assignment, b = 5'h1f
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [0:5] a;
                logic signed [0:4] b, c;

                initial begin
                  a = 8'sh8f; // After the assignment, a = 6'h0f
                  b = 8'sh8f; // After the assignment, b = 5'h0f
                  c = -113;   // After the assignment, c = 15
                              // 1000_1111 = (-'h71 = -113) truncates to ('h0F = 15)
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [7:0] a;
                logic signed [7:0] b;
                logic signed [5:0] c, d;

                initial begin
                  a = 8'hff;
                  c = a;     // After the assignment, c = 6'h3f
                  b = -113;
                  d = b;     // After the assignment, d = 6'h0f
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  var int A[N] = '{default:1};
                  var integer i = '{31:1, 23:1, 15:1, 8:1, default:0};

                  typedef struct {real r, th;} C;
                  var C x = '{th:PI/2.0, r:1.0};
                  var real y [0:1] = '{0.0, 1.1}, z [0:9] = '{default: 3.1416};
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  var int B[4] = '{a, b, c, d};
                  var C y = '{1.0, PI/2.0};
                  '{a, b, c, d} = B;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  typedef logic [1:0] [3:0] T;
                  a = shortint'({T'{1,2}, T'{3,4}}); // yields 16'sh1234
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  typedef byte U[3];
                  var U A = '{1, 2, 3};
                  var byte a, b, c;
                  U'{a, b, c} = A;
                  U'{c, a, b} = '{a+1, b+1, c+1};
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  bit unpackedbits [1:0] = '{1,1};        // no size warning required as
                                                          // bit can be set to 1
                  int unpackedints [1:0] = '{1'b1, 1'b1}; // no size warning required as
                                                          // int can be set to 1'b1
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  unpackedbits = '{2 {y}} ;        // same as '{y, y}
                  int n[1:2][1:3] = '{2{'{3{y}}}}; // same as '{'{y,y,y},'{y,y,y}}
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial unpackedints = '{default:2}; // sets elements to 2"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  struct {int a; time b;} abkey[1:0];
                  abkey = '{'{a:1, b:2ns}, '{int:5, time:$time}};
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module mod1;

                  typedef struct {
                    int x;
                    int y;
                  } st;

                  st s1;
                  int k = 1;

                  initial begin
                    #1 s1 = '{1, 2+k};        // by position
                    #1 $display( s1.x, s1.y);
                    #1 s1 = '{x:2, y:3+k};    // by name
                    #1 $display( s1.x, s1.y);
                    #1 $finish;
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial s1 = '{default:2}; // sets x and y to 2"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"ab abkey[1:0] = '{'{a:1, b:1.0}, '{int:2, shortreal:2.0}};"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  struct {
                    int A;
                    struct {
                      int B, C;
                    } BC1, BC2;
                  } ABC, DEF;

                  ABC = '{A:1, BC1:'{B:2, C:3}, BC2:'{B:4,C:5}};
                  DEF = '{default:10};
                end"##,
            Ok((_, _))
        );
        // TODO
        // string is not included in assignment_pattern_key
        //test!(
        //    many1(module_item),
        //    r##"typedef struct {
        //          logic [7:0] a;
        //          bit b;
        //          bit signed [31:0] c;
        //          string s;
        //        } sa;

        //        sa s2;
        //        initial s2 = '{int:1, default:0, string:""}; // set all to 0 except the
        //                                                     // array of bits to 1 and
        //                                                     // string to """##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"initial #10 s2 = '{default:'1, s : ""}; // set all to 1 except s to """##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  int A3[1:3];
                  A3 = {1, 2, 3}; // unpacked array concatenation: A3[1]=1, A3[2]=2, A3[3]=3
                  A3 = '{1, 2, 3}; // array assignment pattern: A3[1]=1, A3[2]=2, A3[3]=3
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  typedef int AI3[1:3];
                  AI3 A3;
                  int A9[1:9];

                  A3 = '{1, 2, 3};
                  A9 = '{3{A3}};                     // illegal, A3 is wrong element type
                  A9 = '{A3, 4, 5, 6, 7, 8, 9};      // illegal, A3 is wrong element type
                  A9 = {A3, 4, 5, A3, 6};            // legal, gives A9='{1,2,3,4,5,1,2,3,6}
                  A9 = '{9{1}};                      // legal, gives A9='{1,1,1,1,1,1,1,1,1}
                  A9 = {9{1}};                       // illegal, no replication in unpacked
                                                     // array concatenation
                  A9 = {A3, {4,5,6,7,8,9} };         // illegal, {...} is not self-determined here
                  A9 = {A3, '{4,5,6,7,8,9} };        // illegal, '{...} is not self-determined
                  A9 = {A3, 4, AI3'{5, 6, 7}, 8, 9}; // legal, A9='{1,2,3,4,5,6,7,8,9}
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  string S, hello;
                  string SA[2];
                  byte B;
                  byte BA[2];

                  hello = "hello";

                  S = {hello, " world"};  // string concatenation: "hello world"
                  SA = {hello, " world"}; // array concatenation:
                                          // SA[0]="hello", SA[1]=" world"

                  B = {4'h6, 4'hf};       // vector concatenation: B=8'h6f
                  BA = {4'h6, 4'hf};      // array concatenation: BA[0]=8'h06, BA[1]=8'h0f
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  string S1, S2;
                  typedef string T_SQ[$];
                  T_SQ SQ;

                  S1 = "S1";
                  S2 = "S2";
                  SQ = '{"element 0", "element 1"}; // assignment pattern, two strings
                  SQ = {S1, SQ, {"element 3 is ", S2} };
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  SQ = {S1, SQ, T_SQ'{"element 3 is ", S2} };
                    // result: '{"S1", "element 0", "element 1", "element 3 is ", "S2"}
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  typedef int T_QI[$];
                  T_QI jagged_array[$] = '{ {1}, T_QI'{2,3,4}, {5,6} };
                    // jagged_array[0][0] = 1 -- jagged_array[0] is a queue of 1 int
                    // jagged_array[1][0] = 2 -- jagged_array[1] is a queue of 3 ints
                    // jagged_array[1][1] = 3
                    // jagged_array[1][2] = 4
                    // jagged_array[2][0] = 5 -- jagged_array[2] is a queue of 2 ints
                    // jagged_array[2][1] = 6
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module byte_swap (inout wire [31:0] A, inout wire [31:0] B);
                  alias {A[7:0],A[15:8],A[23:16],A[31:24]} = B;
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module byte_rip (inout wire [31:0] W, inout wire [7:0] LSB, MSB);
                  alias W[7:0] = LSB;
                  alias W[31:24] = MSB;
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module overlap(inout wire [15:0] bus16, inout wire [11:0] low12, high12);
                  alias bus16[11:0] = low12;
                  alias bus16[15:4] = high12;
                endmodule

                module overlap(inout wire [15:0] bus16, inout wire [11:0] low12, high12);
                  alias bus16 = {high12, low12[3:0]};
                  alias high12[7:0] = low12[11:4];
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"alias bus16 = {high12[11:8], low12};
                alias bus16 = {high12, low12[3:0]};"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"alias bus16 = {high12, bus16[3:0]} = {bus16[15:12], low12};"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module lib1_dff(Reset, Clk, Data, Q, Q_Bar);
                endmodule

                module lib2_dff(reset, clock, data, q, qbar);
                endmodule

                module lib3_dff(RST, CLK, D, Q, Q_);
                endmodule

                module my_dff(rst, clk, d, q, q_bar); // wrapper cell
                  input rst, clk, d;
                  output q, q_bar;
                  alias rst = Reset = reset = RST;
                  alias clk = Clk = clock = CLK;
                  alias d = Data = data = D;
                  alias q = Q;
                  alias Q_ = q_bar = Q_Bar = qbar;
                  LIB_DFF my_dff (.*); // LIB_DFF is any of lib1_dff, lib2_dff or lib3_dff
                endmodule"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause11() {
        test!(
            many1(module_item),
            r##"initial begin
                  int IntA;
                  IntA = -12 / 3;      // The result is -4

                  IntA = -'d 12 / 3;   // The result is 1431655761

                  IntA = -'sd 12 / 3;  // The result is -4

                  IntA = -4'sd 12 / 3; // -4'sd12 is the negative of the 4-bit
                                       // quantity 1100, which is -4. -(-4) = 4
                                       // The result is 1
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  int n = 8, zero = 0;
                  int res = 'b01xz | n;      // res gets 'b11xz coerced to int, or 'b1100
                  int sum = n + n;           // sum gets 16 coerced to int, or 16
                  int sumx = 'x + n;         // sumx gets 'x coerced to int, or 0
                  int div2 = n/zero + n;     // div2 gets 'x coerced to int, or 0
                  integer div4 = n/zero + n; // div4 gets 'x
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic regA, regB, regC, result ;

                function logic myFunc(logic x);
                endfunction

                initial begin
                  result = regA & (regB | myFunc(regC)) ;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  if ((a=b)) b = (a+=1);

                  a = (b = (c = 5));
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  a[i]+=2; // same as a[i] = a[i] +2;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  i = 10;
                  j = i++ + (i = i - 1);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  integer intS;
                  var logic [15:0] U;
                  var logic signed [15:0] S;

                  intS = -4'd12;
                  U = intS / 3;      // expression result is -4,
                                     // intS is an integer data type, U is 65532

                    U = -4'd12;      // U is 65524
                  intS = U / 3;      // expression result is 21841,
                                     // U is a logic data type

                  intS = -4'd12 / 3; // expression result is 1431655761.
                                     // -4'd12 is effectively a 32-bit logic data type

                  U = -12 / 3;       // expression result is -4, -12 is effectively
                                     // an integer data type. U is 65532

                  S = -12 / 3;       // expression result is -4. S is a signed logic

                  S = -4'sd12 / 3;   // expression result is 1. -4'sd12 is actually 4.
                                     // The rules for integer division yield 4/3==1
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  regA = alpha && beta; // regA is set to 0
                  regB = alpha || beta; // regB is set to 1
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module shift;
                  logic [3:0] start, result;
                  initial begin
                    start = 1;
                    result = (start << 2);
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module ashift;
                  logic signed [3:0] start, result;
                  initial begin
                    start = 4'b1000;
                    result = (start >>> 2);
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"wire [15:0] busa = drive_busa ? data : 16'bz;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  logic log1, log2, log3;
                  {log1, log2, log3} = 3'b111;
                  {log1, log2, log3} = {1'b1, 1'b1, 1'b1}; // same effect as 3'b111
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  byte a, b ;
                  bit [1:0] c ;
                  c = {a + b}[1:0]; // 2 lsb's of sum of a and b
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"parameter P = 32;

                // The following is legal for all P from 1 to 32

                assign b[31:0] = { {32-P{1'b1}}, a[P-1:0] } ;

                // The following is illegal for P=32 because the zero
                // replication appears alone within a concatenation

                assign c[31:0] = { {{32-P{1'b1}}}, a[P-1:0] };

                // The following is illegal for P=32

                initial
                  $displayb({32-P{1'b1}}, a[P-1:0]);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  result = {4{func(w)}} ;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  y = func(w) ;
                  result = {y, y, y, y} ;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  string hello = "hello";
                  string s;
                  s = { hello, " ", "world" };
                  $display( "%s\n", s ); // displays 'hello world'
                  s = { s, " and goodbye" };
                  $display( "%s\n", s ); // displays 'hello world and goodbye'
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  int n = 3;
                  string s = {n { "boo " }};
                  $display( "%s\n", s ); // displays 'boo boo boo '
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  int a, b, c;
                  int array [$] = '{3,4,5};
                  if ( a inside {b, c} );
                  if ( ex inside {1, 2, array} ); // same as { 1, 2, 3, 4, 5}
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  logic [2:0] val;
                  while ( val inside {3'b1?1} ) ; // matches 3'b101, 3'b111, 3'b1x1, 3'b1z1
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"wire r;
                assign r=3'bz11 inside {3'b1?1, 3'b011}; // r = 1'bx"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  bit ba = a inside { [16:23], [32:47] };
                  string I;
                  if (I inside {["a rock":"hard place"]});
                    // I between "a rock" and a "hard place"
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  int a, b, c;
                  logic [10:0] up [3:0];
                  logic [11:1] p1, p2, p3, p4;
                  bit [96:1] y = {>>{ a, b, c }}; // OK: pack a, b, c
                  int j = {>>{ a, b, c }};        // error: j is 32 bits < 96 bits
                  bit [99:0] d = {>>{ a, b, c }}; // OK: d is padded with 4 bits
                  {>>{ a, b, c }} = 23'b1;        // error: too few bits in stream
                  {>>{ a, b, c }} = 96'b1;        // OK: unpack a = 0, b = 0, c = 1
                  {>>{ a, b, c }} = 100'b11111;   // OK: unpack a = 0, b = 0, c = 1
                                                  // 96 MSBs unpacked, 4 LSBs truncated
                  { >> {p1, p2, p3, p4}} = up;    // OK: unpack p1 = up[3], p2 = up[2],
                                                  // p3 = up[1], p4 = up[0]
                end"##,
            Ok((_, _))
        );
        // TODO
        // $ can't be parsed because it is not constant_primary
        //test!(
        //    many1(module_item),
        //    r##"byte stream[$]; // byte stream

        //        class Packet;
        //          rand int header;
        //          rand int len;
        //          rand byte payload[];
        //          int crc;

        //          constraint G { len > 1; payload.size == len ; }

        //          function void post_randomize; crc = payload.sum; endfunction
        //        endclass

        //        initial begin
        //          send: begin // Create random packet and transmit
        //            byte q[$];
        //            Packet p = new;
        //            void'(p.randomize());
        //            q = {<< byte{p.header, p.len, p.payload, p.crc}}; // pack
        //            stream = {stream, q};                             // append to stream
        //          end

        //          receive: begin // Receive packet, unpack, and remove
        //            byte q[$];
        //            Packet p = new;
        //            {<< byte{ p.header, p.len, p.payload with [0 +: p.len], p.crc }} = stream;
        //            stream = stream[ $bits(p) / 8 : $ ]; // remove packet
        //          end
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"initial begin
                  q = {<<byte{p.header, p.len, p.payload with [0 +: p.len], p.crc}};
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  q = {<<byte{p.header, p.len, p.payload with [0 : p.len-1], p.crc}};
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  q = {<<byte{p}};
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  logic [31: 0] a_vect;
                  logic [0 :31] b_vect;
                  logic [63: 0] dword;
                  integer sel;

                  a = a_vect[ 0 +: 8]; // == a_vect[ 7 : 0]
                  a = a_vect[15 -: 8]; // == a_vect[15 : 8]

                  a = b_vect[ 0 +: 8]; // == b_vect[0 : 7]
                  a = b_vect[15 -: 8]; // == b_vect[8 :15]

                  a = dword[8*sel +: 8]; // variable part-select with fixed width
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [15:0] acc;
                logic [2:17] acc;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  logic [7:0] vect;
                  vect = 4; // fills vect with the pattern 00000100
                            // msb is bit 7, lsb is bit 0
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [7:0] mem_name[0:1023];"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [7:0] twod_array[0:255][0:255];
                wire threed_array[0:255][0:255][0:7];"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  localparam p = 7;
                  reg [7:0] m [5:1][5:1];
                  integer i;

                  a = m[1][i]; // longest static prefix is m[1]

                  a = m[p][1]; // longest static prefix is m[p][1]

                  a = m[i][1]; // longest static prefix is m
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  logic [15:0] a, b; // 16-bit variables
                  logic [15:0] sumA; // 16-bit variable
                  logic [16:0] sumB; // 17-bit variable

                  sumA = a + b;      // expression evaluates using 16 bits
                  sumB = a + b;      // expression evaluates using 17 bits
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  logic [15:0] a, b, answer; // 16-bit variables
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  answer = (a + b) >> 1; // will not work properly
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  answer = (a + b + 0) >> 1; // will work correctly
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module bitlength();
                  logic [3:0] a, b, c;
                  logic [4:0] d;

                  initial begin
                    a = 9;
                    b = 8;
                    c = 1;
                    $display("answer = %b", c ? (a&b) : d);
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [3:0] a;
                logic [5:0] b;
                logic [15:0] c;

                initial begin
                  a = 4'hF;
                  b = 6'hA;
                  $display("a*b=%h", a*b); // expression size is self-determined
                  c = {a**b};              // expression a**b is self-determined
                                           // due to concatenation operator {}
                  $display("a**b=%h", c);
                  c = a**b;                // expression size is determined by c
                  $display("c=%h", c);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  logic [7:0] regA, regB;
                  logic signed [7:0] regS;

                  regA = $unsigned(-4);                 // regA = 8'b11111100
                  regB = $unsigned(-4'sd4);             // regB = 8'b00001100
                  regS = $signed (4'b1100);             // regS = -4

                  regA = unsigned'(-4);                 // regA = 8'b11111100
                  regS = signed'(4'b1100);              // regS = -4

                  regS = regA + regB;                   // will do unsigned addition
                  regS = byte'(regA) + byte'(regB);     // will do signed addition
                  regS = signed'(regA) + signed'(regB); // will do signed addition
                  regS = $signed(regA) + $signed(regB); // will do signed addition
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [15:0] a;
                logic signed [7:0] b;

                initial
                  a = b[7:0]; // b[7:0] is unsigned and therefore zero-extended"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  typedef union tagged {
                    void Invalid;
                    int Valid;
                  } VInt;

                  VInt vi1, vi2;

                  vi1 = tagged Valid (23+34); // Create Valid int
                  vi2 = tagged Invalid;       // Create an Invalid value
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  typedef union tagged {
                    struct {
                      bit [4:0] reg1, reg2, regd;
                    } Add;
                    union tagged {
                      bit [9:0] JmpU;
                      struct {
                        bit [1:0] cc;
                        bit [9:0] addr;
                      } JmpC;
                    } Jmp;
                  } Instr;

                  Instr i1, i2;

                  // Create an Add instruction with its 3 register fields
                  i1 = ( e
                    ? tagged Add '{ e1, 4, ed }                  // struct members by position
                    : tagged Add '{ reg2:e2, regd:3, reg1:19 }); // by name (order irrelevant)

                  // Create a Jump instruction, with "unconditional" sub-opcode
                  i1 = tagged Jmp (tagged JmpU 239);

                  // Create a Jump instruction, with "conditional" sub-opcode
                  i2 = tagged Jmp (tagged JmpC '{ 2, 83 });         // inner struct by position
                  i2 = tagged Jmp (tagged JmpC '{ cc:2, addr:83 }); // by name
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  x = i1.Add.reg1;
                  i1.Add = '{19, 4, 3};
                  i1.Add.reg2 = 4;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module string_test;
                  bit [8*14:1] stringvar;

                  initial begin
                    stringvar = "Hello world";
                    $display("%s is stored as %h", stringvar, stringvar);
                    stringvar = {stringvar,"!!!"};
                    $display("%s is stored as %h", stringvar, stringvar);
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [8*10:1] s1, s2;
                initial begin
                  s1 = "Hello";
                  s2 = " world!";
                  if ({s1,s2} == "Hello world!")
                    $display("strings are equal");
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  a = (a:b:c) + (d:e:f);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  a = val - (32'd 50: 32'd 75: 32'd 100);
                end"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"package pex_gen9_common_expressions;
                  let valid_arb(request, valid, override) = |(request & valid) || override;
                endpackage

                module my_checker;
                  import pex_gen9_common_expressions::*;
                  logic a, b;
                  wire [1:0] req;
                  wire [1:0] vld;
                  logic ovr;
                  initial begin
                    if (valid_arb(.request(req), .valid(vld), .override(ovr))) begin
                    end
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"let mult(x, y) = ($bits(x) + $bits(y))'(x * y);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"let at_least_two(sig, rst = 1'b0) = rst || ($countones(sig) >= 2);
                logic [15:0] sig1;
                logic [3:0] sig2;
                always_comb begin
                  q1: assert (at_least_two(sig1));
                  q2: assert (at_least_two(~sig2));
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task write_value;
                  input logic [31:0] addr;
                  input logic [31:0] value;
                endtask

                let addr = top.block1.unit1.base + top.block1.unit2.displ;

                initial begin
                  write_value(addr, 0);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m;
                  logic clk, a, b;
                  logic p, q, r;

                  // let with formal arguments and default value on y
                  let eq(x, y = b) = x == y;

                  // without parameters, binds to a, b above
                  let tmp = a && b;

                  a1: assert property (@(posedge clk) eq(p,q));
                  always_comb begin
                    a2: assert (eq(r)); // use default for y
                    a3: assert (tmp);
                  end
                endmodule : m"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m;
                  bit clk, a, b;
                  logic p, q, r;
                  // let eq(x, y = b) = x == y;
                  // let tmp = a && b;

                  a1: assert property (@(posedge clk) (m.p == m.q));
                  always_comb begin
                    a2: assert ((m.r == m.b)); // use default for y
                    a3: assert ((m.a && m.b));
                  end
                endmodule : m"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  logic x = 1'b1;
                  logic a, b;
                  let y = x;

                  always_comb begin
                    // y binds to preceding definition of x
                    // in the declarative context of let
                    bit x = 1'b0;
                    b = a | y;
                  end
                endmodule : top"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  bit x = 1'b1;
                  bit a;
                  // let y = x;

                  always_comb begin
                    // y binds to preceding definition of x
                    // in the declarative context of let
                    bit x = 1'b0;
                    b = a | (top.x);
                  end
                endmodule : top"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  logic a, b;
                  let x = a || b;
                  sequence s;
                    x ##1 b;
                  endsequence : s
                endmodule : top"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  logic a, b;
                  // let x = a || b;
                  sequence s;
                    (top.a || top.b) ##1 b;
                  endsequence : s
                endmodule : top"##,
            Ok((_, _))
        );
        // TODO
        // assign can't have block_identifier like assert
        //test!(
        //    many1(module_item),
        //    r##"module m();
        //          wire a, b;
        //          wire [2:0] c;
        //          wire [2:0] d;
        //          wire e;

        //          for (genvar i = 0; i < 3; i++) begin : L0
        //            if (i !=1) begin : L1
        //              let my_let(x) = !x || b && c[i];
        //              s1: assign d[2 - i] = my_let(a); // OK
        //            end : L1
        //          end : L0
        //          s2: assign e = L0[0].L1.my_let(a); // Illegal
        //        endmodule : m"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"assign d[2] = (!m.a || m.b && m.c[0]);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"assign d[0] = (!m.a || m.b && m.c[2]);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m(input clock);
                  logic [15:0] a, b;
                  logic c, d;
                  typedef bit [15:0] bits;

                  let ones_match(bits x, y) = x == y;
                  let same(logic x, y) = x === y;

                  always_comb
                    a1: assert(ones_match(a, b));

                  property toggles(bit x, y);
                    same(x, y) |=> !same(x, y);
                  endproperty

                  a2: assert property (@(posedge clock) toggles(c, d));
                endmodule : m"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m(input clock);
                  logic [15:0] a, b;
                  logic c, d;
                  typedef bit [15:0] bits;

                  // let ones_match(bits x, y) = x == y;
                  // let same(logic x, y) = x === y;

                  always_comb
                    a1:assert((bits'(a) == bits'(b)));

                  property toggles(bit x, y);
                    (logic'(x) === logic'(y)) |=> ! (logic'(x) === logic'(y));
                  endproperty

                  a2: assert property (@(posedge clock) toggles(c, d));
                  endmodule : m"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m(input clock);
                  logic a;
                  let p1(x) = $past(x);
                  let p2(x) = $past(x,,,@(posedge clock));
                  let s(x) = $sampled(x);
                  always_comb begin
                    a1: assert(p1(a));
                    a2: assert(p2(a));
                    a3: assert(s(a));
                  end
                  a4: assert property(@(posedge clock) p1(a));
                endmodule : m"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m(input clock);
                  logic a;
                  let p1(x) = $past(x);
                  let p2(x) = $past(x,,,@(posedge clock));
                  let s(x) = $sampled(x);
                  always_comb begin
                    a1: assert(($past(a))); // Illegal: no clock can be inferred
                    a2: assert(($past(a,,,@(posedge clock))));
                    a3: assert(($sampled (a)));
                  end
                  a4: assert property(@(posedge clock)($past(a))); // @(posedge clock)
                                                                   // is inferred
                endmodule : m"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause12() {
        test!(
            many1(module_item),
            r##"initial begin
                  if (index > 0)
                    if (rega > regb)
                      result = rega;
                    else // else applies to preceding if
                      result = regb;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  if (index > 0)
                    begin
                      if (rega > regb)
                        result = rega;
                    end
                  else result = regb;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  // declare variables and parameters
                  logic [31:0] instruction,
                               segment_area[255:0];
                  logic [7:0]  index;
                  logic [5:0]  modify_seg1,
                               modify_seg2,
                               modify_seg3;
                  parameter
                    segment1 = 0, inc_seg1 = 1,
                    segment2 = 20, inc_seg2 = 2,
                    segment3 = 64, inc_seg3 = 4,
                    data = 128;

                  // test the index variable
                  if (index < segment2) begin
                    instruction = segment_area [index + modify_seg1];
                    index = index + inc_seg1;
                  end
                  else if (index < segment3) begin
                    instruction = segment_area [index + modify_seg2];
                    index = index + inc_seg2;
                  end
                  else if (index < data) begin
                    instruction = segment_area [index + modify_seg3];
                    index = index + inc_seg3;
                  end
                  else
                    instruction = segment_area [index];
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  unique if ((a==0) || (a==1)) $display("0 or 1");
                  else if (a == 2) $display("2");
                  else if (a == 4) $display("4"); // values 3,5,6,7 cause a violation report

                  priority if (a[2:1]==0) $display("0 or 1");
                  else if (a[2] == 0) $display("2 or 3");
                  else $display("4 to 7"); // covers all other possible values,
                                           // so no violation report
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  unique0 if ((a==0) || (a==1)) $display("0 or 1");
                  else if (a == 2) $display("2");
                  else if (a == 4) $display("4"); // values 3,5,6,7
                                                  // cause no violation report
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always_comb begin
                  not_a = !a;
                end

                always_comb begin : a1
                  u1: unique if (a)
                    z = a | b;
                  else if (not_a)
                    z = a | c;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always_comb begin
                  for (int j = 0; j < 3; j++)
                  not_a[j] = !a[j];
                end

                always_comb begin : a1
                  for (int j = 0; j < 3; j++)
                    unique if (a[j])
                      z[j] = a[j] | b[j];
                    else if (not_a[j])
                      z[j] = a[j] | c[j];
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module fsm();
                  function bit f1(bit a, bit not_a);
                    a1: unique if (a);
                    else if (not_a);
                  endfunction

                  always_comb begin : b1
                    some_stuff = f1(c, d);
                  end

                  always_comb begin : b2
                    other_stuff = f1(e, f);
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  logic [15:0] data;
                  logic [9:0] result;
                  case (data)
                    16'd0: result = 10'b0111111111;
                    16'd1: result = 10'b1011111111;
                    16'd2: result = 10'b1101111111;
                    16'd3: result = 10'b1110111111;
                    16'd4: result = 10'b1111011111;
                    16'd5: result = 10'b1111101111;
                    16'd6: result = 10'b1111110111;
                    16'd7: result = 10'b1111111011;
                    16'd8: result = 10'b1111111101;
                    16'd9: result = 10'b1111111110;
                    default result = 'x;
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  case (select[1:2])
                    2'b00: result = 0;
                    2'b01: result = flaga;
                    2'b0x,
                    2'b0z: result = flaga ? 'x : 0;
                    2'b10: result = flagb;
                    2'bx0,
                    2'bz0: result = flagb ? 'x : 0;
                    default result = 'x;
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  case (sig)
                    1'bz: $display("signal is floating");
                    1'bx: $display("signal is unknown");
                    default: $display("signal is %b", sig);
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  logic [7:0] ir;

                  casez (ir)
                    8'b1???????: instruction1(ir);
                    8'b01??????: instruction2(ir);
                    8'b00010???: instruction3(ir);
                    8'b000001??: instruction4(ir);
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  logic [7:0] r, mask;

                  mask = 8'bx0x0x0x0;
                  casex (r ^ mask)
                    8'b001100xx: stat1;
                    8'b1100xx00: stat2;
                    8'b00xx0011: stat3;
                    8'bxx010100: stat4;
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  logic [2:0] encode ;

                  case (1)
                    encode[2] : $display("Select Line 2") ;
                    encode[1] : $display("Select Line 1") ;
                    encode[0] : $display("Select Line 0") ;
                    default $display("Error: One of the bits expected ON");
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  bit [2:0] a;
                  unique case(a) // values 3,5,6,7 cause a violation report
                    0,1: $display("0 or 1");
                    2: $display("2");
                    4: $display("4");
                  endcase

                  priority casez(a) // values 4,5,6,7 cause a violation report
                    3'b00?: $display("0 or 1");
                    3'b0??: $display("2 or 3");
                  endcase

                  unique0 case(a) // values 3,5,6,7 do not cause a violation report
                    0,1: $display("0 or 1");
                    2: $display("2");
                    4: $display("4");
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always_comb begin
                  not_a = !a;
                end

                always_comb begin : a1
                  unique case (1'b1)
                    a : z = b;
                    not_a : z = c;
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [2:0] status;
                always @(posedge clock)
                  priority case (status) inside
                  1, 3 : task1; // matches 'b001 and 'b011
                  3'b0?0, [4:7]: task2; // matches 'b000 'b010 'b0x0 'b0z0
                                        // 'b100 'b101 'b110 'b111
                  endcase // priority case fails all other values including
                          // 'b00x 'b01x 'bxxx"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  typedef union tagged {
                    void Invalid;
                    int Valid;
                  } VInt;

                  VInt v;

                  case (v) matches
                    tagged Invalid : $display ("v is Invalid");
                    tagged Valid .n : $display ("v is Valid with value %d", n);
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  typedef union tagged {
                    struct {
                      bit [4:0] reg1, reg2, regd;
                    } Add;
                    union tagged {
                      bit [9:0] JmpU;
                      struct {
                        bit [1:0] cc;
                        bit [9:0] addr;
                      } JmpC;
                    } Jmp;
                  } Instr;

                  Instr instr;

                  case (instr) matches
                    tagged Add '{.r1, .r2, .rd} &&& (rd != 0) : rf[rd] = rf[r1] + rf[r2];
                    tagged Jmp .j : case (j) matches
                                      tagged JmpU .a : pc = pc + a;
                                      tagged JmpC '{.c, .a}: if (rf[c]) pc = a;
                                    endcase
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  case (instr) matches
                    tagged Add '{.*, .*, 0} : ; // no op
                    tagged Add '{.r1, .r2, .rd} : rf[rd] = rf[r1] + rf[r2];
                    tagged Jmp .j : case (j) matches
                                      tagged JmpU .a : pc = pc + a;
                                      tagged JmpC '{.c, .a} : if (rf[c]) pc = a;
                                    endcase
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  case (instr) matches
                    tagged Add s: case (s) matches
                                    '{.*, .*, 0} : ; // no op
                                    '{.r1, .r2, .rd} : rf[rd] = rf[r1] + rf[r2];
                                  endcase
                    tagged Jmp .j: case (j) matches
                                     tagged JmpU .a : pc = pc + a;
                                     tagged JmpC '{.c, .a} : if (rf[c]) pc = a;
                                   endcase
                  endcase
                end"##,
            Ok((_, _))
        );
        // TODO
        // tagged can't have paren.
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          case (instr) matches
        //            tagged Add '{.r1, .r2, .rd} &&& (rd != 0) : rf[rd] = rf[r1] + rf[r2];
        //            tagged Jmp (tagged JmpU .a) : pc = pc + a;
        //            tagged Jmp (tagged JmpC '{.c, .a}) : if (rf[c]) pc = a;
        //          endcase
        //        end"##,
        //    Ok((_, _))
        //);
        // TODO
        // tagged can't have paren.
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          case (instr) matches
        //            tagged Add '{reg2:.r2,regd:.rd,reg1:.r1} &&& (rd != 0):
        //                                                     rf[rd] = rf[r1] + rf[r2];
        //            tagged Jmp (tagged JmpU .a) : pc = pc + a;
        //            tagged Jmp (tagged JmpC '{addr:.a,cc:.c}) : if (rf[c]) pc = a;
        //          endcase
        //        end"##,
        //    Ok((_, _))
        //);
        // TODO
        // tagged can't have paren.
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          if (e matches (tagged Jmp (tagged JmpC '{cc:.c,addr:.a})))
        //            ; // c and a can be used here
        //          else
        //            ;
        //        end"##,
        //    Ok((_, _))
        //);
        // TODO
        // tagged can't have paren.
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          if (e matches (tagged Jmp .j) &&&
        //              j matches (tagged JmpC '{cc:.c,addr:.a}))
        //            ; // c and a can be used here
        //          else
        //            ;
        //        end"##,
        //    Ok((_, _))
        //);
        // TODO
        // tagged can't have paren.
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          if (e matches (tagged Jmp (tagged JmpC '{cc:.c,addr:.a}))
        //            &&& (rf[c] != 0))
        //            ; // c and a can be used here
        //          else
        //            ;
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"module m;
                  initial begin
                    for (int i = 0; i <= 255; i++);
                  end

                  initial begin
                    loop2: for (int i = 15; i >= 0; i--);
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m;
                  initial begin
                    begin
                      automatic int i;
                      for (i = 0; i <= 255; i++);
                    end
                  end

                  initial begin
                    begin : loop2
                      automatic int i;
                      for (i = 15; i >= 0; i--);
                    end
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  for ( int count = 0; count < 3; count++ )
                    value = value +((a[count]) * (count+1));

                  for ( int count = 0, done = 0, j = 0; j * count < 125; j++, count++)
                    $display("Value j = %d\n", j );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  parameter size = 8, longsize = 16;
                  logic [size:1] opa, opb;
                  logic [longsize:1] result;

                  begin : mult
                    logic [longsize:1] shift_opa, shift_opb;
                    shift_opa = opa;
                    shift_opb = opb;
                    result = 0;
                    repeat (size) begin
                      if (shift_opb[1])
                        result = result + shift_opa;
                      shift_opa = shift_opa << 1;
                      shift_opb = shift_opb >> 1;
                    end
                  end
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  string words [2] = '{ "hello", "world" };
                  int prod [1:8] [1:3];

                  foreach( words [ j ] )
                    $display( j , words[j] ); // print each index and value

                  foreach( prod[ k, m ] )
                    prod[k][m] = k * m;       // initialize
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  begin : count1s
                    logic [7:0] tempreg;
                    count = 0;
                    tempreg = data;
                    while (tempreg) begin
                      if (tempreg[0])
                        count++;
                      tempreg >>= 1;
                    end
                  end
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  string s;
                  if ( map.first( s ) )
                    do
                      $display( "%s : %d\n", s, map[ s ] );
                    while ( map.next( s ) );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  clock1 <= 0;
                  clock2 <= 0;
                  fork
                    forever #10 clock1 = ~clock1;
                    #5 forever #10 clock2 = ~clock2;
                  join
                end"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause13() {
        test!(
            many1(module_item),
            r##"initial begin
                  switch_bytes (old_word, new_word);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  new_word = switch_bytes (old_word);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task mytask1 (output int x, input logic y);
                endtask

                task mytask2;
                  output x;
                  input y;
                  int x;
                  logic y;
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task mytask3(a, b, output logic [15:0] u, v);
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task mytask4(input [3:0][7:0] a, b[3:0], output [3:0][7:0] y[1:0]);
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task my_task;
                  input a, b;
                  inout c;
                  output d, e;
                  c = a; // the assignments that initialize result outputs
                  d = b;
                  e = c;
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task my_task (input a, b, inout c, output d, e);
                  c = a; // the assignments that initialize result variables
                  d = b;
                  e = c;
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial
                  my_task (v, w, x, y, z);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  a = v;
                  b = w;
                  c = x;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  x = c;
                  y = d;
                  z = e;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module traffic_lights;
                  logic clock, red, amber, green;
                  parameter on = 1, off = 0, red_tics = 350,
                            amber_tics = 30, green_tics = 200;

                  // initialize colors
                  initial red = off;
                  initial amber = off;
                  initial green = off;

                  always begin                // sequence to control the lights
                    red = on;                 // turn red light on
                    light(red, red_tics);     // and wait.
                    green = on;               // turn green light on
                    light(green, green_tics); // and wait.
                    amber = on;               // turn amber light on
                    light(amber, amber_tics); // and wait.
                  end

                  // task to wait for 'tics' positive edge clocks
                  // before turning 'color' light off
                  task light (output color, input [31:0] tics);
                    repeat (tics) @ (posedge clock);
                    color = off; // turn light off.
                  endtask: light

                  always begin   // waveform for the clock
                    #100 clock = 0;
                    #100 clock = 1;
                  end
                endmodule: traffic_lights"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"function logic [15:0] myfunc1(int x, int y);
                endfunction

                function logic [15:0] myfunc2;
                  input int x;
                  input int y;
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"function logic [15:0] myfunc3(int a, int b, output logic [15:0] u, v);
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"function [3:0][7:0] myfunc4(input [3:0][7:0] a, b[3:0]);
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"function [15:0] myfunc1 (input [7:0] x,y);
                  myfunc1 = x * y - 1; // return value assigned to function name
                endfunction

                function [15:0] myfunc2 (input [7:0] x,y);
                  return x * y - 1; //return value is specified using return statement
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  a = b + myfunc1(c, d); // call myfunc1 (defined above) as an expression

                  myprint(a);            // call myprint (defined below) as a statement
                end

                function void myprint (int a);
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  void'(some_function());
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module tryfact;
                  // define the function
                  function automatic integer factorial (input [31:0] operand);
                    if (operand >= 2)
                      factorial = factorial (operand - 1) * operand;
                    else
                      factorial = 1;
                  endfunction: factorial

                  // test the function
                  integer result;
                  initial begin
                    for (int n = 0; n <= 7; n++) begin
                      result = factorial(n);
                      $display("%0d factorial=%0d", n, result);
                    end
                  end
                endmodule: tryfact"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module ram_model (address, write, chip_select, data);
                  parameter data_width = 8;
                  parameter ram_depth = 256;
                  localparam addr_width = clogb2(ram_depth);
                  input [addr_width - 1:0] address;
                  input write, chip_select;
                  inout [data_width - 1:0] data;

                  //define the clogb2 function
                  function integer clogb2 (input [31:0] value);
                    value = value - 1;
                    for (clogb2 = 0; value > 0; clogb2 = clogb2 + 1)
                      value = value >> 1;
                  endfunction

                  logic [data_width - 1:0] data_store[0:ram_depth - 1];
                    //the rest of the ram model
                endmodule: ram_model"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"ram_model #(32,421) ram_a0(a_addr,a_wr,a_cs,a_data);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class IntClass;
                  int a;
                endclass

                IntClass address=new(), stack=new();

                function automatic bit watch_for_zero( IntClass p );
                  fork
                    forever @p.a begin
                      if ( p.a == 0 ) $display ("Unexpected zero");
                    end
                  join_none
                  return ( p.a == 0 );
                endfunction

                function bit start_check();
                  return ( watch_for_zero( address ) | watch_for_zero( stack ) );
                endfunction

                bit y = watch_for_zero( stack ); // illegal

                initial if ( start_check() ) $display ( "OK"); // legal

                initial fork
                  if (start_check() ) $display( "OK too"); // legal
                join_none"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"function automatic int crc( byte packet [1000:1] );
                  for( int j= 1; j <= 1000; j++ ) begin
                    crc ^= packet[j];
                  end
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"function automatic int crc( ref byte packet [1000:1] );
                  for( int j= 1; j <= 1000; j++ ) begin
                    crc ^= packet[j];
                  end
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  byte packet1[1000:1];
                  int k = crc( packet1 ); // pass by value or by reference: call is the same
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task automatic show ( const ref byte data [] );
                  for ( int j = 0; j < data.size ; j++ )
                    $display( data[j] ); // data can be read but not written
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task read(int j = 0, int k, int data = 1 );
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  read( , 5 );     // is equivalent to read( 0, 5, 1 );
                  read( 2, 5 );    // is equivalent to read( 2, 5, 1 );
                  read( , 5, );    // is equivalent to read( 0, 5, 1 );
                  read( , 5, 7 );  // is equivalent to read( 0, 5, 7 );
                  read( 1, 5, 2 ); // is equivalent to read( 1, 5, 2 );
                  read( );         // error; k has no default value
                  read( 1, , 7 );  // error; k has no default value
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m;
                  logic a, w;

                  task t1 (output o = a) ; // default binds to m.a
                  endtask :t1

                  task t2 (output o = b) ; // illegal, b cannot be resolved
                  endtask :t2

                  task t3 (inout io = w) ; // default binds to m.w
                  endtask :t1
                endmodule :m

                module n;
                  logic a;

                  initial begin
                    m.t1(); // same as m.t1(m.a), not m.t1(n.a);
                            // at end of task, value of t1.o is copied to m.a
                    m.t3(); // same as m.t3(m.w)
                            // value of m.w is copied to t3.io at start of task and
                            // value of t3.io is copied to m.w at end of task
                  end
                endmodule :n"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"function int fun( int j = 1, string s = "no" );
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fun( .j(2), .s("yes") ); // fun( 2, "yes" );
                  fun( .s("yes") );        // fun( 1, "yes" );
                  fun( , "yes" );          // fun( 1, "yes" );
                  fun( .j(2) );            // fun( 2, "no" );
                  fun( .s("yes"), .j(2) ); // fun( 2, "yes" );
                  fun( .s(), .j() );       // fun( 1, "no" );
                  fun( 2 );                // fun( 2, "no" );
                  fun( );                  // fun( 1, "no" );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  //fun( .s("yes"), 2 ); // illegal
                  fun( 2, .s("yes") ); // OK
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"virtual class C#(parameter DECODE_W, parameter ENCODE_W = $clog2(DECODE_W));
                  static function logic [ENCODE_W-1:0] ENCODER_f
                        (input logic [DECODE_W-1:0] DecodeIn);
                    ENCODER_f = '0;
                    for (int i=0; i<DECODE_W; i++) begin
                      if(DecodeIn[i]) begin
                        ENCODER_f = i[ENCODE_W-1:0];
                        break;
                      end
                    end
                  endfunction
                  static function logic [DECODE_W-1:0] DECODER_f
                        (input logic [ENCODE_W-1:0] EncodeIn);
                    DECODER_f = '0;
                    DECODER_f[EncodeIn] = 1'b1;
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        // TODO
        // class static method is denied because ps_or_hierarchical_tf_identifier doesn't have class_scope.
        //test!(
        //    many1(module_item),
        //    r##"module top ();
        //          logic [7:0] encoder_in;
        //          logic [2:0] encoder_out;
        //          logic [1:0] decoder_in;
        //          logic [3:0] decoder_out;

        //          // Encoder and Decoder Input Assignments
        //          assign encoder_in = 8'b0100_0000;
        //          assign decoder_in = 2'b11;

        //          // Encoder and Decoder Function calls
        //          assign encoder_out = C#(8)::ENCODER_f(encoder_in);
        //          assign decoder_out = C#(4)::DECODER_f(decoder_in);

        //          initial begin
        //            #50;
        //            $display("Encoder input = %b Encoder output = %b\n",
        //              encoder_in, encoder_out );
        //            $display("Decoder input = %b Decoder output = %b\n",
        //              decoder_in, decoder_out );
        //          end
        //        endmodule"##,
        //    Ok((_, _))
        //);
    }

    #[test]
    fn clause14() {
        test!(
            many1(module_item),
            r##"clocking ck1 @(posedge clk);
                  default input #1step output negedge; // legal
                  // outputs driven on the negedge clk
                endclocking

                clocking ck2 @(clk); // no edge specified!
                  default input #1step output negedge; // legal
                endclocking"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"clocking bus @(posedge clock1);
                  default input #10ns output #2ns;
                  input data, ready, enable = top.mem1.enable;
                  output negedge ack;
                  input #1step addr;
                endclocking"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"clocking dram @(clk);
                  input #1ps address;
                  input #5 output #6 data;
                endclocking"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"clocking cd1 @(posedge phi1);
                  input #1step state = top.cpu1.state;
                endclocking"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"clocking mem @(clock);
                  input instruction = { opcode, regA, regB[3:1] };
                endclocking"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"program test( input phi1, input [15:0] data, output logic write,
                  input phi2, inout [8:1] cmd, input enable
                );
                  reg [8:1] cmd_reg;

                  clocking cd1 @(posedge phi1);
                    input data;
                    output write;
                    input state = top.cpu1.state;
                  endclocking

                  clocking cd2 @(posedge phi2);
                    input #2 output #4ps cmd;
                    input enable;
                  endclocking

                  initial begin
                    // program begins here
                    // user can access cd1.data , cd2.cmd , etc…
                  end
                  assign cmd = enable ? cmd_reg: 'x;
                endprogram"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  logic phi1, phi2;
                  wire [8:1] cmd; // cannot be logic (two bidirectional drivers)
                  logic [15:0] data;

                  test main (phi1, data, write, phi2, cmd, enable);
                  cpu cpu1 (phi1, data, write);
                  mem mem1 (phi2, cmd, enable);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface bus_A (input clk);
                  logic [15:0] data;
                  logic write;
                  modport test (input data, output write);
                  modport dut (output data, input write);
                endinterface

                interface bus_B (input clk);
                  logic [8:1] cmd;
                  logic enable;
                  modport test (input enable);
                  modport dut (output enable);
                endinterface

                program test( bus_A.test a, bus_B.test b );
                  clocking cd1 @(posedge a.clk);
                    input data = a.data;
                    output write = a.write;
                    inout state = top.cpu1.state;
                  endclocking

                  clocking cd2 @(posedge b.clk);
                    input #2 output #4ps cmd = b.cmd;
                    input en = b.enable;
                  endclocking

                  initial begin
                    // program begins here
                    // user can access cd1.data, cd1.write, cd1.state,
                    // cd2.cmd, and cd2.en
                  end
                endprogram"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  logic phi1, phi2;

                  bus_A a (phi1);
                  bus_B b (phi2);

                  test main (a, b);
                  cpu cpu1 (a);
                  mem mem1 (b);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"clocking dram @(posedge phi1);
                  inout data;
                  output negedge #1 address;
                endclocking"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @(dram);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  ##5;       // wait 5 cycles (clocking events) using the default clocking

                  ##(j + 1); // wait j+1 cycles (clocking events) using the default clocking
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"program test(input logic clk, input logic [15:0] data);
                  default clocking bus @(posedge clk);
                    inout data;
                  endclocking

                  initial begin
                    ## 5;
                    if (bus.data == 10)
                      ## 1;
                  end
                endprogram"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module processor();
                  clocking busA @(posedge clk1); endclocking
                  clocking busB @(negedge clk2); endclocking
                  module cpu( interface y );
                    default clocking busA ;
                    initial begin
                      ## 5; // use busA => (posedge clk1)
                    end
                  endmodule
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"clocking cb @(negedge clk);
                  input v;
                endclocking

                always @(cb) $display(cb.v);

                always @(negedge clk) $display(cb.v);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  logic clk1, clk2;
                  global clocking sys @(clk1 or clk2); endclocking
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  subsystem1 sub1();
                  subsystem2 sub2();
                endmodule

                module subsystem1;
                  logic subclk1;
                  global clocking sub_sys1 @(subclk1); endclocking
                  common_sub common();
                endmodule

                module subsystem2;
                  logic subclk2;
                  global clocking sub_sys2 @(subclk2); endclocking
                  common_sub common();
                endmodule

                module common_sub;
                  always @($global_clock) begin
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  subsystem1 sub1();
                  subsystem2 sub2();
                endmodule

                module subsystem1;
                  logic subclk1, req, ack;
                  global clocking sub_sys1 @(subclk1); endclocking
                  common_checks checks(req, ack);
                endmodule

                module subsystem2;
                  logic subclk2, req, ack;
                  global clocking sub_sys2 @(subclk2); endclocking
                  common_checks checks(req, ack);
                endmodule

                module another_module;
                  logic another_clk;
                  global clocking another_clocking @(another_clk); endclocking
                  property p(req, ack);
                    @($global_clock) req |=> ack;
                  endproperty
                endmodule

                checker common_checks(logic req, logic ack);
                  assert property (another_module.p(req, ack));
                endchecker"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  subsystem1 sub1();
                  subsystem2 sub2();
                endmodule

                module subsystem1;
                  logic subclk1, req, ack;
                  global clocking sub_sys1 @(subclk1); endclocking
                  always another_module.t(req, ack);
                endmodule

                module subsystem2;
                  logic subclk2, req, ack;
                  global clocking sub_sys2 @(subclk2); endclocking
                  always another_module.t(req, ack);
                endmodule

                module another_module;
                  logic another_clk;
                  global clocking another_clocking @(another_clk); endclocking
                  task t(input req, input ack);
                    @($global_clock);
                  endtask
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  logic a, b, c, clk;
                  global clocking top_clocking @(clk); endclocking

                  property p1(req, ack);
                    @($global_clock) req |=> ack;
                  endproperty

                  property p2(req, ack, interrupt);
                    @($global_clock) accept_on(interrupt) p1(req, ack);
                  endproperty

                  my_checker check(
                    p2(a, b, c),
                    @($global_clock) a[*1:$] ##1 b);
                endmodule

                checker my_checker(property p, sequence s);
                  logic checker_clk;
                  global clocking checker_clocking @(checker_clk); endclocking
                  assert property (p);
                  cover property (s);
                endchecker"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @(ram_bus.ack_l);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @(ram_bus);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @(posedge ram_bus.enable);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @(negedge dom.sign[a]);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @(posedge dom.sig1 or dom.sig2);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @(negedge dom.sig1 or posedge dom.sig2);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @(edge dom.sig1);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @(negedge dom.sig1 or posedge dom.sig1);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  bus.data[3:0] <= 4'h5; // drive data in Re-NBA region of the current cycle

                  ##1 bus.data <= 8'hz;  // wait 1 default clocking cycle, then drive data

                  ##2; bus.data <= 2;    // wait 2 default clocking cycles, then drive data

                  bus.data <= ##2 r;     // remember the value of r and then drive
                                         // data 2 (bus) cycles later

                  bus.data <= #4 r;      // error: regular intra-assignment delay not allowed
                                         // in synchronous drives
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"default clocking cb @(posedge clk); // Assume clk has a period of #10 units
                  output v;
                endclocking

                initial begin
                  #3 cb.v <= expr1; // Matures in cycle 1; equivalent to ##1 cb.v <= expr1
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"clocking cb @(posedge clk);
                  inout a;
                  output b;
                endclocking

                initial begin
                  cb.a <= c;    // The value of a will change in the Re-NBA region
                  cb.b <= cb.a; // b is assigned the value of a before the change
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"default clocking pe @(posedge clk);
                  output nibble; // four bit output
                endclocking

                initial begin
                  ##2;
                  pe.nibble <= 4'b0101;
                  pe.nibble <= 4'b0011;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m;
                  bit a = 1'b1;
                  default clocking cb @(posedge clk);
                    output a;
                  endclocking

                  initial begin
                    ## 1;
                    cb.a <= 1'b0;
                    @(x); // x is triggered by reactive stimulus running in same time step
                    cb.a <= 1'b1;
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit v;
                default clocking cb @(posedge clk);
                  output v;
                endclocking

                initial begin
                  ##1;                   // Wait until cycle 1
                  cb.v <= expr1;         // Matures in cycle 1, v is assigned expr1
                  cb.v <= ##2 expr2;     // Matures in cycle 3
                  #1 cb.v <= ##2 expr3;  // Matures in cycle 3
                  ##1 cb.v <= ##1 expr4; // Matures in cycle 3, v is assigned expr4
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"reg j;

                clocking pe @(posedge clk);
                  output j;
                endclocking

                clocking ne @(negedge clk);
                  output j;
                endclocking"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"reg j;
                clocking e @(edge clk);
                  output j;
                endclocking"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause15() {
        test!(
            many1(module_item),
            r##"initial begin
                  semaphore smTx;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  mailbox mbxRcv;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  typedef mailbox #(string) s_mbox;

                  s_mbox sm = new;
                  string s;

                  sm.put( "hello" );
                  sm.get( s ); // s <- "hello"
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  @ hierarchical_event_identifier;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  wait ( hierarchical_event_identifier.triggered );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"event done, blast;     // declare two new events
                event done_too = done; // declare done_too as alias to done

                task trigger( event ev );
                  -> ev;
                endtask

                initial begin
                  fork
                    @ done_too;         // wait for done through done_too
                    #1 trigger( done ); // trigger done through task trigger
                  join

                  fork
                    -> blast;
                    wait ( blast.triggered );
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  wait_order( a, b, c);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  wait_order( a, b, c ) else $display( "Error: events out of order" );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  bit success;
                  wait_order( a, b, c ) success = 1; else success = 0;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  event a, b, c;
                  a = b;
                  -> c;
                  -> a; // also triggers b
                  -> b; // also triggers a
                  a = c;
                  b = a;
                  -> a; // also triggers b and c
                  -> b; // also triggers a and c
                  -> c; // also triggers a and b
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fork
                    T1: forever @ E2;
                    T2: forever @ E1;
                    T3: begin
                          E2 = E1;
                          forever -> E2;
                    end
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  event E1 = null;
                  @ E1;                 // undefined: might block forever or not at all
                  wait( E1.triggered ); // undefined
                  -> E1;                // no effect
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  event E1, E2;
                  if ( E1 ) // same as if ( E1 != null )
                    E1 = E2;
                  if ( E1 == E2 )
                    $display( "E1 and E2 are the same event" );
                end"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause16() {
        test!(
            many1(module_item),
            r##"initial begin
                  assert_f: assert(f) $info("passed"); else $error("failed");
                  assume_inputs: assume (in_a || in_b) $info("assumption holds");
                  else $error("assumption does not hold");
                  cover_a_and_b: cover (in_a && in_b) $info("in_a && in_b == 1 covered");
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"time t;

                always @(posedge clk)
                  if (state == REQ)
                    assert (req1 || req2)
                    else begin
                      t = $time;
                      #5 $error("assert failed at time %0t",t);
                    end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  assert (myfunc(a,b)) count1 = count + 1; else ->event1;
                  assert (y == 0) else flag = 1;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"assign not_a = !a;
                always_comb begin : b1
                  a1: assert (not_a != a);
                  a2: assert #0 (not_a != a); // Should pass once values have settled
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(a or b) begin : b1
                  a3: assert #0 (a == b) rptobj.success(0); else rptobj.error(0, a, b);
                  #1;
                  a4: assert #0 (a == b) rptobj.success(1); else rptobj.error(1, a, b);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always_comb begin : b1
                  c1: cover (b != a);
                  c2: cover #0 (b != a);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"function f(bit v);
                  p: assert #0 (v);
                endfunction
                always_comb begin: myblk
                  a = b || f(c);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"function int error_type (int opcode);
                  func_assert: assert (opcode < 64) else $display("Opcode error.");
                  if (opcode < 32)
                    return (0);
                  else
                    return (1);
                endfunction

                always_comb begin : b1
                  a1: assert #0 (my_cond) else
                  $error("Error on operation of type %d\n", error_type(opcode));
                  a2: assert #0 (my_cond) else
                  error_type(opcode);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module dut(input logic clk, input logic a, input logic b);
                  logic c;
                  always_ff @(posedge clk)
                    c <= b;
                  a1: assert #0 (!(a & c)) $display("Pass"); else $display("Fail");
                  a2: assert final (!(a & c)) $display("Pass"); else $display("Fail");
                endmodule

                program tb(input logic clk, output logic a, output logic b);
                  default clocking m @(posedge clk);
                    default input #0;
                    default output #0;
                    output a;
                    output b;
                  endclocking

                  initial begin
                    a = 1;
                    b = 0;
                    ##10;
                    b = 1;
                    ##1;
                    a = 0;
                  end
                endprogram

                module sva_svtb;
                  bit clk;
                  logic a, b;
                  dut dut (.*);
                  tb tb (.*);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m (input a, b);
                  a1: assert #0 (a == b);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m (input a, b);
                  always_comb begin
                    a1: assert #0 (a == b);
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(bad_val or bad_val_ok) begin : b1
                  a1: assert #0 (bad_val) else $fatal(1, "Sorry");
                  if (bad_val_ok) begin
                    disable a1;
                  end
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(a or b or c) begin : b2
                  if (c == 8'hff) begin
                    a2: assert #0 (a && b);
                  end else begin
                    a3: assert #0 (a || b);
                  end
                end

                always @(clear_b2) begin : b3
                  disable b2;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module fsm();
                  function bit f (int a, int b);
                    a1: assert #0 (a == b);
                  endfunction

                  always_comb begin : b1
                    some_stuff = f(x,y);
                  end

                  always_comb begin : b2
                    other_stuff = f(z,w);
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"global clocking @clk; endclocking
                assert property(@($global_clock) a);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"assert property(@clk a);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"base_rule1: assert property (cont_prop(rst,in1,in2)) $display("%m, passing");
                             else $display("%m, failed");"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit a;
                integer b;
                byte q[$];

                property p1;
                  $rose(a) |-> q[0];
                endproperty

                property p2;
                  integer l_b;
                  ($rose(a), l_b = b) |-> ##[3:10] q[l_b];
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [2:0] count;
                realtime t;

                initial count = 0;
                always @(posedge clk) begin
                  if (count == 0) t = $realtime; //capture t in a procedural context
                  count++;
                end

                property p1;
                  @(posedge clk)
                  count == 7 |-> $realtime - t < 50.5;
                endproperty

                property p2;
                  realtime l_t;
                  @(posedge clk)
                  (count == 0, l_t = $realtime) ##1 (count == 7)[->1] |->
                    $realtime - l_t < 50.5;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence delay_example(x, y, min, max, delay1);
                  x ##delay1 y[*min:max];
                endsequence

                // Legal
                a1: assert property (@(posedge clk) delay_example(x, y, 3, $, 2));

                int z, d;

                // Illegal: z and d are not elaboration-time constants
                a2_illegal: assert property (@(posedge clk) delay_example(x, y, z, $, d));"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence s1;
                  @(posedge clk) a ##1 b ##1 c;
                endsequence
                sequence s2;
                  @(posedge clk) d ##1 e ##1 f;
                endsequence
                sequence s3;
                  @(negedge clk) g ##1 h ##1 i;
                endsequence
                sequence s4;
                  @(edge clk) j ##1 k ##1 l;
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence s20_1(data,en);
                  (!frame && (data==data_bus)) ##1 (c_be[0:3] == en);
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence s;
                  a ##1 b ##1 c;
                endsequence
                sequence rule;
                  @(posedge sysclk)
                  trans ##1 start_trans ##1 s ##1 end_trans;
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence rule;
                  @(posedge sysclk)
                  trans ##1 start_trans ##1 (a ##1 b ##1 c) ##1 end_trans ;
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence s1;
                  @(posedge sysclk) (x ##1 s2);
                endsequence
                sequence s2;
                  @(posedge sysclk) (y ##1 s1);
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence s1(w, x, y);
                  w ##1 x ##[2:10] y;
                endsequence
                sequence s2(w, y, bit x);
                  w ##1 x ##[2:10] y;
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence delay_arg_example (max, shortint delay1, delay2, min);
                  x ##delay1 y[*min:max] ##delay2 z;
                endsequence

                parameter my_delay=2;
                cover property (delay_arg_example($, my_delay, my_delay-1, 3));"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"cover property (x ##2 y[*3:$] ##1 z);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence event_arg_example (event ev);
                  @(ev) x ##1 y;
                endsequence

                cover property (event_arg_example(posedge clk));"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"cover property (@(posedge clk) x ##1 y);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence event_arg_example2 (reg sig);
                  @(posedge sig) x ##1 y;
                endsequence

                cover property (event_arg_example2(clk));"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"cover property (@(posedge clk) x ##1 y);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence s(bit a, bit b);
                  bit loc_a;
                  (1'b1, loc_a = a) ##0
                  (t == loc_a) [*0:$] ##1 b;
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic b_d, d_d;
                sequence legal_loc_var_formal (
                  local inout logic a,
                  local logic b = b_d, // input inferred, default actual argument b_d
                              c,       // local input logic inferred, no default
                                       // actual argument
                              d = d_d, // local input logic inferred, default actual
                                       // argument d_d
                  logic e, f           // e and f are not local variable formal arguments
                );
                  logic g = c, h = g || d;
                  g ##1 h;
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence sub_seq2(local inout int lv);
                  (a ##1 !a, lv += data_in)
                  ##1 !b[*0:$] ##1 b && (data_out == lv);
                endsequence
                sequence seq2;
                  int v1;
                  (c, v1 = data)
                  ##1 sub_seq2(v1) // lv is initialized by assigning it the value of v1;
                                   // when the instance sub_seq2(v1) matches, v1 is
                                   // assigned the value of lv
                  ##1 (do1 == v1);
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence seq2_inlined;
                  int v1, lv;
                  (c, v1 = data) ##1
                  (
                    (1, lv = v1) ##0
                    (a ##1 !a, lv += data_in)
                    ##1 (!b[*0:$] ##1 b && (data_out == lv), v1 = lv)
                  )
                  ##1 (do1 == v1);
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic a, b, clk;
                // ...
                a1_bad: assert property (@clk a == b)
                  else $error("Different values: a = %b, b = %b", a, b);
                a2_ok: assert property (@clk a == b)
                  else $error("Different values: a = %b, b = %b",
                    $sampled(a), $sampled(b));"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(posedge clk)
                  reg1 <= a & $rose(b);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  $past(in1, , enable);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(posedge clk)
                  reg1 <= a & $past(b);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(posedge clk)
                  for (int i = 0; i < 4; i ++)
                    if (cond[i])
                      reg1[i] <= $past(b[i]);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(posedge clk)
                  if (enable) q <= d;

                always @(posedge clk)
                assert property (done |=> (out == $past(q, 2,enable)) );"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit clk, fclk, req, gnt, en;

                a1: assert property
                  (@(posedge clk) en && $rose(req) |=> gnt);
                a2: assert property
                  (@(posedge clk) en && $rose(req, @(posedge fclk)) |=> gnt);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always_ff @(posedge clk1)
                  reg1 <= $rose(b, @(posedge clk2));"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(posedge clk) begin
                  @(negedge clk2);
                  x = $past(y, 5); // illegal if not within default clocking
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"a1: assert property (@clk $future_gclk(a || $rising_gclk(b)));
                sequence s;
                  bit v;
                  (a, v = a) ##1 (b == v)[->1];
                endsequence : s

                // Illegal: a global clocking future sampled value function shall not
                // be used in an assertion containing sequence match items
                a2: assert property (@clk s |=> $future_gclk(c));"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"a1: assert property (@($global_clock) $changing_gclk(sig)
                                                 |-> $falling_gclk(clk))
                else $error("sig is not stable");"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"a2: assume property(@($global_clock)
                            $falling_gclk(clk) ##1 (!$falling_gclk(clk)[*1:$]) |->
                                                                  $steady_gclk(sig));"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"a3: assert property (@($global_clock) disable iff (rst) $changing_gclk(sig)
                                                     |-> $falling_gclk(clk))
                else $error("sig is not stable");"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"a4: assert property (##1 $stable_gclk(sig));
                // In a5, there is no issue at cycle 0
                a5: assert property ($steady_gclk(sig));"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence t1;
                  te1 ## [2:5] te2;
                endsequence
                sequence ts1;
                  first_match(te1 ## [2:5] te2);
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence t2;
                  (a ##[2:3] b) or (c ##[1:2] d);
                endsequence
                sequence ts2;
                  first_match(t2);
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence burst_rule1;
                  @(posedge mclk)
                    $fell(burst_mode) ##0
                    ((!burst_mode) throughout (##2 ((trdy==0)&&(irdy==0)) [*7]));
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence s;
                  a ##1 b ##1 c;
                endsequence
                sequence rule;
                  @(posedge sysclk)
                    trans ##1 start_trans ##1 s ##1 end_trans;
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence e1;
                  @(posedge sysclk) $rose(ready) ##1 proc1 ##1 proc2 ;
                endsequence
                sequence rule;
                  @(posedge sysclk) reset ##1 inst ##1 e1.triggered ##1 branch_back;
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence e2(a,b,c);
                  @(posedge sysclk) $rose(a) ##1 b ##1 c;
                endsequence
                sequence rule2;
                  @(posedge sysclk) reset ##1 inst ##1 e2(ready,proc1,proc2).triggered
                    ##1 branch_back;
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence e2_instantiated;
                  e2(ready,proc1,proc2);
                endsequence
                sequence rule2a;
                  @(posedge sysclk) reset ##1 inst ##1 e2_instantiated.triggered ##1
                branch_back;
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence e3(sequence a, untyped b);
                  @(posedge sysclk) a.triggered ##1 b;
                endsequence

                sequence rule3;
                  @(posedge sysclk) reset ##1 e3(ready ##1 proc1, proc2) ##1 branch_back;
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence zero_or_one_req;
                  (req==1'b1)[*0:1];
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence s;
                  logic u, v = a, w = v || b;
                  u;
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property e;
                  int x;
                  (valid_in, x = pipe_in) |-> ##5 (pipe_out1 == (x+1));
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence data_check;
                  int x;
                  a ##1 (!a, x = data_in) ##1 !b[*0:$] ##1 b && (data_out == x);
                endsequence
                property data_check_p;
                  int x;
                  a ##1 (!a, x = data_in) |=> !b[*0:$] ##1 b && (data_out == x);
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence rep_v;
                  int x = 0;
                  (a[->1], x += data)[*4] ##1 b ##1 c && (data_out == x);
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence count_a_cycles;
                  int x;
                  ($rose(a), x = 1)
                  ##1 (a, x++)[*0:$]
                  ##1 !a && (x <= MAX);
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence sub_seq1;
                  int v1;
                  (a ##1 !a, v1 = data_in) ##1 !b[*0:$] ##1 b && (data_out == v1);
                endsequence
                sequence seq1;
                  c ##1 sub_seq1 ##1 (do1 == v1); // error because v1 is not visible
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence sub_seq2(lv);
                  (a ##1 !a, lv = data_in) ##1 !b[*0:$] ##1 b && (data_out == lv);
                endsequence
                sequence seq2;
                  int v1;
                  c ##1 sub_seq2(v1) // v1 is bound to lv
                  ##1 (do1 == v1);   // v1 holds the value that was assigned to lv
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence seq2a;
                  int v1; c ##1 sub_seq2(v1).triggered ##1 (do1 == v1);
                  // v1 is now bound to lv
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence seq2b;
                  int v1; c ##1 !sub_seq2(v1).triggered ##1 (do1 == v1); // v1 unassigned
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence sub_seq3(lv);
                  int lv; // illegal because lv is a formal argument
                  (a ##1 !a, lv = data_in) ##1 !b[*0:$] ##1 b && (data_out == lv);
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence s4;
                  int x;
                  (a ##1 (b, x = data) ##1 c) or (d ##1 (e==x)); // illegal
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence s5;
                  int x,y;
                  ((a ##1 (b, x = data, y = data1) ##1 c)
                    or (d ##1 (true, x = data) ##0 (e==x))) ##1 (y==data2);
                  // illegal because y is not in the intersection
                endsequence
                sequence s6;
                  int x,y;
                  ((a ##1 (b, x = data, y = data1) ##1 c)
                    or (d ##1 (true, x = data) ##0 (e==x))) ##1 (x==data2);
                  // legal because x is in the intersection
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence s7;
                  int x,y;
                  ((a ##1 (b, x = data, y = data1) ##1 c)
                    and (d ##1 (true, x = data) ##0 (e==x))) ##1 (x==data2);
                  // illegal because x is common to both threads
                endsequence
                sequence s8;
                  int x,y;
                  ((a ##1 (b, x = data, y = data1) ##1 c)
                    and (d ##1 (true, x = data) ##0 (e==x))) ##1 (y==data2);
                  // legal because y is in the difference
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence s1;
                  logic v, w;
                  (a, v = e) ##1
                  (b[->1], w = f, $display("b after a with v = %h, w = %h\n", v, w));
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property p3;
                  b ##1 c;
                endproperty

                c1: cover property (@(posedge clk) a #-# p3);
                a1: assert property (@(posedge clk) a |-> p3);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"a1: assert property (@clk not a ##1 b);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"a2: assert property (@clk not strong(a ##1 b));"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"let ready_exp = (irdy == 0) && ($fell(trdy) || $fell(stop));
                property data_end;
                  @(posedge mclk)
                  $rose(data_phase) |-> ##[1:5] ready_exp;
                endproperty
                a1: assert property(data_end);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"let data_end_exp = data_phase && ready_exp;
                property data_end_rule1;
                  @(posedge mclk)
                  data_end_exp |-> ##[1:2] $rose(frame) ##1 $rose(irdy);
                endproperty
                a2: assert property(data_end_rule1);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property data_end_rule2;
                  @(posedge mclk) ##[1:2] $rose(frame) ##1 $rose(irdy);
                endproperty
                a3: assert property(data_end_rule2);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property write_to_addr;
                  (write_en & data_valid) ##0
                  (write_en && (retire_address[0:4]==addr)) [*2] |->
                  ##[3:8] write_en && !data_valid &&(write_address[0:4]==addr);
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property write_to_addr_nested;
                  (write_en & data_valid) |->
                    (write_en && (retire_address[0:4]==addr)) [*2] |->
                      ##[3:8] write_en && !data_valid && (write_address[0:4]==addr);
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property p1;
                  ##[0:5] done #-# always !rst;
                endproperty

                property p2;
                  ##[0:5] done #=# always !rst;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property p1;
                  nexttime a;
                endproperty

                // the clock shall tick once more and a shall be true at the next clock tick.
                property p2;
                  s_nexttime a;
                endproperty

                // as long as the clock ticks, a shall be true at each future clock tick
                // starting from the next clock tick
                property p3;
                  nexttime always a;
                endproperty

                // the clock shall tick at least once more and as long as it ticks, a shall
                // be true at every clock tick starting from the next one
                property p4;
                  s_nexttime always a;
                endproperty

                // if the clock ticks at least once more, it shall tick enough times for a to
                // be true at some point in the future starting from the next clock tick
                property p5;
                  nexttime s_eventually a;
                endproperty

                // a shall be true sometime in the strict future
                property p6;
                  s_nexttime s_eventually a;
                endproperty

                // if there are at least two more clock ticks, a shall be true at the second
                // future clock tick
                property p7;
                  nexttime[2] a;
                endproperty

                // there shall be at least two more clock ticks, and a shall be true at the
                // second future clock tick
                property p8;
                  s_nexttime[2] a;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"implicit_always: assert property(p);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial explicit_always: assert property(always p);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial a1: assume property( @(posedge clk) reset[*5] #=# always !reset);

                property p1;
                  a ##1 b |=> always c;
                endproperty

                property p2;
                  always [2:5] a;
                endproperty

                property p3;
                  s_always [2:5] a;
                endproperty

                property p4;
                  always [2:$] a;
                endproperty

                property p5;
                  s_always [2:$] a; // Illegal
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property p1;
                  a until b;
                endproperty

                property p2;
                  a s_until b;
                endproperty

                property p3;
                  a until_with b;
                endproperty

                property p4;
                  a s_until_with b;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property p1;
                  s_eventually a;
                endproperty

                property p2;
                  s_eventually always a;
                endproperty

                property p3;
                  always s_eventually a;
                endproperty

                property p4;
                  eventually [2:5] a;
                endproperty

                property p5;
                  s_eventually [2:5] a;
                endproperty

                //property p6;
                //  eventually [2:$] a; // Illegal
                //endproperty

                property p7;
                  s_eventually [2:$] a;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"assert property (@(clk) go ##1 get[*2] |-> reject_on(stop) put[->2]);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"assert property (@(clk) go ##1 get[*2] |-> sync_reject_on(stop) put[->2]);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"assert property (@(clk) go ##1 get[*2] |-> !stop throughout put[->2]);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property p; (accept_on(a) p1) and (reject_on(b) p2); endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property p; (accept_on(a) p1) or (reject_on(b) p2); endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property p; not (accept_on(a) p1); endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property p; accept_on(a) reject_on(b) p1; endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property p_delay(logic [1:0] delay);
                  case (delay)
                    2'd0 : a && b;
                    2'd1 : a ##2 b;
                    2'd2 : a ##4 b;
                    2'd3 : a ##8 b;
                    default: 0; // cause a failure if delay has x or z values
                  endcase
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property prop_always(p);
                  p and (1'b1 |=> prop_always(p));
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property p1(s,p);
                  s |=> prop_always(p);
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property prop_weak_until(p,q);
                  q or (p and (1'b1 |=> prop_weak_until(p,q)));
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property p2(s,p,q);
                  s |=> prop_weak_until(p,q);
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property check_phase1;
                  s1 |-> (phase1_prop and (1'b1 |=> check_phase2));
                endproperty
                property check_phase2;
                  s2 |-> (phase2_prop and (1'b1 |=> check_phase1));
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property illegal_recursion_1(p);
                  not prop_always(not p);
                endproperty

                property illegal_recursion_2(p);
                  p and (1'b1 |=> not illegal_recursion_2(p));
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property illegal_recursion_3(p);
                  disable iff (b)
                  p and (1'b1 |=> illegal_recursion_3(p));
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property legal_3(p);
                  disable iff (b) prop_always(p);
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property illegal_recursion_4(p);
                  p and (1'b1 |-> illegal_recursion_4(p));
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property fibonacci1 (local input int a, b, n, int fib_sig);
                  (n > 0)
                  |->
                  (
                    (fib_sig == a)
                    and
                    (1'b1 |=> fibonacci1(b, a + b, n - 1, fib_sig))
                  );
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property fibonacci2 (int a, b, n, fib_sig);
                  (n > 0)
                  |->
                  (
                    (fib_sig == a)
                    and
                    (1'b1 |=> fibonacci2(b, a + b, n - 1, fib_sig))
                  );
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property p3(p, bit b, abort);
                  (p and (1'b1 |=> p4(p, b, abort)));
                endproperty

                property p4(p, bit b, abort);
                  accept_on(b) reject_on(abort) p3(p, b, abort);
                endproperty"##,
            Ok((_, _))
        );
        // TODO
        // stack overflow (pass with RUST_MIN_STACK=33554432)
        //test!(
        //    many1(module_item),
        //    r##"property check_write;
        //          logic [0:127] expected_data; // local variable to sample model data
        //          logic [3:0] tag; // local variable to sample tag

        //          disable iff (reset)
        //          (
        //            write_request && write_request_ack,
        //            expected_data = model_data,
        //            tag = write_request_ack_tag
        //          )
        //          |=>
        //          check_write_data_beat(expected_data, tag, 4'h0);
        //        endproperty

        //        property check_write_data_beat
        //        (
        //          local input logic [0:127] expected_data,
        //          local input logic [3:0] tag, i
        //        );
        //          (
        //            (data_valid && (data_valid_tag == tag))
        //            ||
        //            (retry && (retry_tag == tag))
        //          )[->1]
        //          |->
        //          (
        //            (
        //              (data_valid && (data_valid_tag == tag))
        //              |->
        //              (data == expected_data[i*8+:8])
        //            )
        //            and
        //            (
        //              if (retry && (retry_tag == tag))
        //              (
        //                1'b1 |=> check_write_data_beat(expected_data, tag, 4'h0)
        //              )
        //              else if (!last_data_valid)
        //              (
        //                1'b1 |=> check_write_data_beat(expected_data, tag, i+4'h1)
        //              )
        //              else
        //              (
        //                ##1 (retry && (retry_tag == tag))
        //                |=>
        //                check_write_data_beat(expected_data, tag, 4'h0)
        //              )
        //            )
        //          );
        //        endproperty"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"property rule1;
                  @(posedge clk) a |-> b ##1 c ##1 d;
                endproperty
                property rule2;
                  @(clkev) disable iff (e) a |-> not(b ##1 c ##1 d);
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property rule3;
                  @(posedge clk) a[*2] |-> ((##[1:3] c) or (d |=> e));
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property rule4;
                  @(posedge clk) a[*2] |-> ((##[1:3] c) and (d |=> e));
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property rule5;
                  @(posedge clk)
                  a ##1 (b || c)[->1] |->
                    if (b)
                      (##1 d |-> e)
                    else // c
                      f ;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property rule6(x,y);
                  ##1 x |-> y;
                endproperty
                property rule5a;
                  @(posedge clk)
                  a ##1 (b || c)[->1] |->
                    if (b)
                      rule6(d,e)
                    else // c
                      f ;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence s1;
                  a ##1 b; // unclocked sequence
                endsequence
                sequence s2;
                  c ##1 d; // unclocked sequence
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence mult_s;
                  @(posedge clk) a ##1 @(posedge clk1) s1 ##1 @(posedge clk2) s2;
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property mult_p1;
                  @(posedge clk) a ##1 @(posedge clk1) s1 ##1 @(posedge clk2) s2;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property mult_p2;
                  mult_s;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property mult_p3;
                  @(posedge clk) a ##1 @(posedge clk1) s1 |=> @(posedge clk2) s2;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property mult_p6;
                  mult_s |=> mult_s;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property mult_p7;
                  @(posedge clk) a ##1 b |-> c ##1 @(posedge clk1) d;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property mult_p8;
                  @(posedge clk) a ##1 b |->
                  if (c)
                    (1 |=> @(posedge clk1) d)
                  else
                    e ##1 @(posedge clk2) f ;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence e1(a,b,c);
                  @(posedge clk) $rose(a) ##1 b ##1 c ;
                endsequence
                sequence e2;
                  @(posedge sysclk) reset ##1 inst ##1 e1(ready,proc1,proc2).matched [->1]
                    ##1 branch_back;
                endsequence"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence e1;
                  @(posedge sysclk) $rose(a) ##1 b ##1 c;
                endsequence

                sequence e2;
                  @(posedge sysclk) reset ##1 inst ##1 e1.triggered ##1 branch_back;
                endsequence

                sequence e3;
                  @(posedge clk) reset1 ##1 e1.matched ##1 branch_back1;
                endsequence

                sequence e2_with_arg(sequence subseq);
                  @(posedge sysclk) reset ##1 inst ##1 subseq.triggered ##1 branch_back;
                endsequence

                sequence e4;
                  e2_with_arg(@(posedge sysclk) $rose(a) ##1 b ##1 c);
                endsequence

                program check;
                  initial begin
                    wait (e1.triggered || e2.triggered);
                    if (e1.triggered)
                      $display("e1 passed");
                    if (e2.triggered)
                      $display("e2 passed");
                  end
                endprogram"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module mod_sva_checks;
                  logic a, b, c, d;
                  logic clk_a, clk_d, clk_e1, clk_e2;
                  logic clk_c, clk_p;

                  clocking cb_prog @(posedge clk_p); endclocking
                  clocking cb_checker @(posedge clk_c); endclocking

                  default clocking cb @(posedge clk_d); endclocking

                  sequence e4;
                    $rose(b) ##1 c;
                  endsequence

                  // e4 infers posedge clk_a as per clock flow rules
                  a1: assert property (@(posedge clk_a) a |=> e4.triggered);

                  sequence e5;
                    // e4 will infer posedge clk_e1 as per clock flow rules
                    // wherever e5 is instantiated (with/without a method)
                    @(posedge clk_e1) a ##[1:3] e4.triggered ##1 c;
                  endsequence

                  // e4, used in e5, infers posedge clk_e1 from e5
                  a2: assert property (@(posedge clk_a) a |=> e5.matched);

                  sequence e6(f);
                    @(posedge clk_e2) f;
                  endsequence

                  // e4 infers posedge clk_e2 as per clock flow rules
                  a3: assert property (@(posedge clk_a) a |=> e6(e4.triggered));

                  sequence e7;
                    e4 ##1 e6(d);
                  endsequence

                  // Leading clock of e7 is posedge clk_a as per clock flow rules
                  a4: assert property (@(posedge clk_a) a |=> e7.triggered);

                  // Illegal use in a disable condition, e4 is not explicitly clocked
                  a5_illegal: assert property (
                    @(posedge clk_a) disable iff (e4.triggered) a |=> b);

                  always @(posedge clk_a) begin
                    // e4 infers default clocking cb and not posedge clk_a as there is
                    // more than one event control in this procedure (16.14.6)
                    @(e4);
                    d = a;
                  end

                  program prog_e4;
                    default clocking cb_prog;
                    initial begin
                      // e4 infers default clocking cb_prog
                      wait (e4.triggered);
                      $display("e4 passed");
                    end
                  endprogram : prog_e4

                  checker check(input in1, input sequence s_f);
                    default clocking cb_checker;
                    always @(s_f)
                      $display("sequence triggered");
                    a4: assert property (a |=> in1);
                  endchecker : check

                  // e4 infers checker's default clocking cb_checker
                  check c1(e4.triggered, e4);

                  // e4 connected to port of a module instance infers default clocking cb
                  mod_adder ai1(e4.triggered);

                endmodule : mod_sva_checks"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property p;
                  logic v = e;
                  (@(posedge clk1) (a == v)[*1:$] |-> b)
                  and
                  (@(posedge clk2) c[*1:$] |-> d == v)
                  ;
                endproperty
                a1: assert property (@(posedge clk) f |=> p);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property p;
                  logic v;
                  (@(posedge clk1) (1, v = e) ##0 (a == v)[*1:$] |-> b)
                  and
                  (@(posedge clk2) (1, v = e) ##0 c[*1:$] |-> d == v)
                  ;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property abc(a, b, c);
                  disable iff (a==2) @(posedge clk) not (b ##1 c);
                endproperty
                env_prop: assert property (abc(rst, in1, in2))
                  $display("env_prop passed."); else $display("env_prop failed.");"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property abc(a, b, c);
                  disable iff (c) @(posedge clk) a |=> b;
                endproperty
                env_prop:
                  assume property (abc(req, gnt, rst)) else $error("Assumption failed.");"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"a1:assume property ( @(posedge clk) req dist {0:=40, 1:=60} ) ;
                property proto ;
                  @(posedge clk) req |-> req[*1:$] ##0 ack;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"a1_assertion:assert property ( @(posedge clk) req inside {0, 1} ) ;
                property proto_assertion ;
                  @(posedge clk) req |-> req[*1:$] ##0 ack;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property pr1;
                  @(posedge clk) !reset_n |-> !req; // when reset_n is asserted (0),
                                                    // keep req 0
                endproperty
                property pr2;
                  @(posedge clk) ack |=> !req; // one cycle after ack, req
                                               // must be deasserted
                endproperty
                property pr3;
                  @(posedge clk) req |-> req[*1:$] ##0 ack; // hold req asserted until
                                                            // and including ack asserted
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property pa1;
                  @(posedge clk) !reset_n || !req |-> !ack;
                endproperty
                property pa2;
                  @(posedge clk) ack |=> !ack;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"a1:assume property (@(posedge clk) req dist {0:=40, 1:=60} );
                assume_req1:assume property (pr1);
                assume_req2:assume property (pr2);
                assume_req3:assume property (pr3);

                assert_ack1:assert property (pa1)
                  else $error("ack asserted while req is still deasserted");
                assert_ack2:assert property (pa2)
                  else $error("ack is extended over more than one cycle");"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"restrict property (@(posedge clk) ctr == '0);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top(input logic clk);
                  logic a,b,c;
                  property rule3;
                    @(posedge clk) a |-> b ##1 c;
                  endproperty
                  a1: assert property (rule3);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top(input logic clk);
                  logic a,b,c;
                  sequence seq3;
                    @(posedge clk) b ##1 c;
                  endsequence
                  c1: cover property (seq3);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property rule;
                  a ##1 b ##1 c;
                endproperty
                always @(posedge clk) begin
                  assert property (rule);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property r1;
                  q != d;
                endproperty
                always @(posedge mclk) begin
                  q <= d1;
                  r1_p1: assert property (r1);
                  r1_p2: assert property (@(posedge scanclk)r1);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property r2;
                  q != d;
                endproperty
                always_ff @(posedge clock iff reset == 0 or posedge reset) begin
                  cnt <= reset ? 0 : cnt + 1;
                  q <= $past(d1);
                  r2_p: assert property (r2);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property r3;
                  q != d;
                endproperty
                always_ff @(clock iff reset == 0 or posedge reset) begin
                  cnt <= reset ? 0 : cnt + 1;
                  q <= $past(d1); // no inferred clock
                  r3_p: assert property (r3); // no inferred clock
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property r4;
                  q != d;
                endproperty
                always @(posedge mclk) begin
                  #10 q <= d1; // delay prevents clock inference
                  @(negedge mclk) // event control prevents clock inference
                  #10 q1 <= !d1;
                  r4_p: assert property (r4); // no inferred clock
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(posedge clk) begin
                  int i = 10;
                  for (i=0; i<10; i++) begin
                    a1: assert property (foo[i] && bar[i]);
                    a2: assert property (foo[const'(i)] && bar[i]);
                    a3: assert property (foo[const'(i)] && bar[const'(i)]);
                  end
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"default clocking @(posedge clk); endclocking
                generate for (genvar i=0; i<10; i++) begin
                  a1: assert property (foo[10] && bar[10]);
                  a2: assert property (foo[i] && bar[10]);
                  a3: assert property (foo[i] && bar[i]);
                end
                endgenerate"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(posedge clk) begin
                  // variable declared in for statement is automatic (see 12.7.1)
                  for (int i=0; i<10; i++) begin
                    a4: assert property (foo[i] && bar[i]);
                    a5: assert property (foo[const'(i)] && bar[i]);
                    a6: assert property (foo[const'(i)] && bar[const'(i)]);
                  end
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"wire w;
                always @(posedge clk) begin : procedural_block_1
                  if (my_activation_condition == 1) begin
                    for (int i=0; i<2; i++) begin
                      a7: assume property (foo[i] |=> bar[i] ##1 (w==1'b1));
                    end
                  end
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(posedge clk) begin
                  int i = 10;
                  for (i=0; i<10; i++) begin
                    a8: assert property (foo[const'(i)] && bar[i]) else
                      $error("a8 failed for const i=%d and i=%d",
                        const'(i), $sampled(i));
                  end
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(posedge clk) begin
                  if (en) begin
                    a9: assert property (p1(a,b,c));
                  end
                  if ($sampled(en)) begin
                    a10: assert property (p1(a,b,c));
                  end
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"assign not_a = !a;
                default clocking @(posedge clk); endclocking
                always_comb begin : b1
                  // Probably better to not use consts in this example
                  // ...but using them to illustrate effects of flushing method
                  a1: assert property (const'(not_a) != const'(a));
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"default clocking @(posedge clk); endclocking
                always @(a or b) begin : b1
                  a2: assert property (a == b) r.success(0); else r.error(0, a, b);
                  #1;
                  a3: assert property (a == b) r.success(1); else r.error(1, a, b);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"default clocking @(posedge clk); endclocking
                always_comb begin : b1
                  c1: cover property (const'(b) != const'(a));
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always_comb begin : procedural_block_1
                  if (en)
                    foo = bar;
                  end

                always_comb begin : procedural_block_2
                  p1: assert property ( @(posedge clk) (const'(foo) == const'(bar)) );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"default clocking @(posedge clk); endclocking
                always @(bad_val or bad_val_ok) begin : b1
                  a1: assert property (bad_val) else $fatal(1, "Sorry");
                  if (bad_val_ok) begin
                    disable a1;
                  end
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"default clocking @(posedge clk); endclocking
                always @(a or b or c) begin : b2
                  if (c == 8'hff) begin
                    a2: assert property (a && b);
                  end else begin
                    a3: assert property (a || b);
                  end
                end

                always @(clear_b2) begin : b3
                  disable b2;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m(logic a, b, c, d, rst1, clk1, clk2);
                  logic rst;

                  default clocking @(negedge clk1); endclocking
                  default disable iff rst1;

                  property p_triggers(start_event, end_event, form, clk = $inferred_clock,
                                      rst = $inferred_disable);
                    @clk disable iff (rst)
                      (start_event ##0 end_event[->1]) |=> form;
                  endproperty

                  property p_multiclock(clkw, clkx = $inferred_clock, clky, w, x, y, z);
                    @clkw w ##1 @clkx x |=> @clky y ##1 z;
                  endproperty

                  a1: assert property (p_triggers(a, b, c));
                  a2: assert property (p_triggers(a, b, c, posedge clk1, 1'b0) );

                  always @(posedge clk2 or posedge rst) begin
                  end

                  a4: assert property(p_multiclock(negedge clk2, , posedge clk1,
                                      a, b, c, d) );
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m(logic a, b, c, d, rst1, clk1, clk2);
                  logic rst;

                  a1: assert property (@(negedge clk1) disable iff (rst1)
                                       a ##0 b[->1] |=> c);

                  a2: assert property (@(posedge clk1) disable iff (1'b0)
                                       a ##0 b[->1] |=> c);

                  always @(posedge clk2 or posedge rst) begin
                  end

                  a3: assert property
                    (
                      @(posedge clk2) disable iff (rst1)
                      (a ##0 b[->1]) |=> c
                    );

                  a4: assert property (@(negedge clk2) a ##1 @(negedge clk1) b |=>
                    @(posedge clk1) c ##1 d);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m1;
                  bit clk, rst1;
                  default disable iff rst1;
                  a1: assert property (@(posedge clk) p1); // property p1 is
                                                           // defined elsewhere
                  module m2;
                    bit rst2;
                    a2: assert property (@(posedge clk) p2); // property p2 is
                                                             // defined elsewhere
                  endmodule
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m1;
                  bit clk, rst1;
                  default disable iff rst1;
                  a1: assert property (@(posedge clk) p1); // property p1 is
                                                           // defined elsewhere
                  module m2;
                    bit rst2;
                    default disable iff rst2;
                    a2: assert property (@(posedge clk) p2); // property p2 is
                                                             // defined elsewhere
                  endmodule
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module examples_with_default (input logic a, b, clk, rst, rst1);
                  default disable iff rst;
                  property p1;
                    disable iff (rst1) a |=> b;
                  endproperty

                  // Disable condition is rst1 - explicitly specified within a1
                  a1 : assert property (@(posedge clk) disable iff (rst1) a |=> b);

                  // Disable condition is rst1 - explicitly specified within p1
                  a2 : assert property (@(posedge clk) p1);

                  // Disable condition is rst - no explicit specification, inferred from
                  // default disable iff declaration
                  a3 : assert property (@(posedge clk) a |=> b);

                  // Disable condition is 1'b0. This is the only way to
                  // cancel the effect of default disable.
                  a4 : assert property (@(posedge clk) disable iff (1'b0) a |=> b);
                endmodule

                module examples_without_default (input logic a, b, clk, rst);
                  property p2;
                    disable iff (rst) a |=> b;
                  endproperty

                  // Disable condition is rst - explicitly specified within a5
                  a5 : assert property (@(posedge clk) disable iff (rst) a |=> b);

                  // Disable condition is rst - explicitly specified within p2
                  a6 : assert property (@ (posedge clk) p2);

                  // No disable condition
                  a7 : assert property (@ (posedge clk) a |=> b);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"sequence s2; @(posedge clk) a ##2 b; endsequence
                property p2; not s2; endproperty
                assert property (p2);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"property p3; @(posedge clk) not (a ##2 b); endproperty
                assert property (p3);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always @(posedge clk) assert property (not (a ##2 b));"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"clocking master_clk @(posedge clk);
                  property p3; not (a ##2 b); endproperty
                endclocking
                assert property (master_clk.p3);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"default clocking master_clk ; // master clock as defined above
                property p4; (a ##2 b); endproperty
                assert property (p4);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module examples_with_default (input logic a, b, c, clk);
                  property q1;
                    $rose(a) |-> ##[1:5] b;
                  endproperty

                  property q2;
                    @(posedge clk) q1;
                  endproperty

                  default clocking posedge_clk @(posedge clk);
                    property q3;
                      $fell(c) |=> q1;
                      // legal: q1 has no clocking event
                    endproperty

                    property q4;
                      $fell(c) |=> q2;
                      // legal: q2 has clocking event identical to that of
                      // the clocking block
                    endproperty

                    sequence s1;
                      @(posedge clk) b[*3];
                      // illegal: explicit clocking event in clocking block
                    endsequence
                  endclocking

                  property q5;
                    @(negedge clk) b[*3] |=> !b;
                  endproperty

                  always @(negedge clk)
                  begin
                    a1: assert property ($fell(c) |=> q1);
                      // legal: contextually inferred leading clocking event,
                      // @(negedge clk)
                    a2: assert property (posedge_clk.q4);
                      // legal: will be queued (pending) on negedge clk, then
                      // (if matured) checked at next posedge clk (see 16.14.6)
                    a3: assert property ($fell(c) |=> q2);
                      // illegal: multiclocked property with contextually
                      // inferred leading clocking event
                    a4: assert property (q5);
                      // legal: contextually inferred leading clocking event,
                      // @(negedge clk)
                  end

                  property q6;
                    q1 and q5;
                  endproperty

                  a5: assert property (q6);
                    // illegal: default leading clocking event, @(posedge clk),
                    // but semantic leading clock is not unique
                  a6: assert property ($fell(c) |=> q6);
                    // legal: default leading clocking event, @(posedge clk),
                    // is the unique semantic leading clock

                  sequence s2;
                    $rose(a) ##[1:5] b;
                  endsequence

                  c1: cover property (s2);
                    // legal: default leading clocking event, @(posedge clk)
                  c2: cover property (@(negedge clk) s2);
                    // legal: explicit leading clocking event, @(negedge clk)
                endmodule

                module examples_without_default (input logic a, b, c, clk);
                  property q1;
                    $rose(a) |-> ##[1:5] b;
                  endproperty

                  property q5;
                    @(negedge clk) b[*3] |=> !b;
                  endproperty

                  property q6;
                    q1 and q5;
                  endproperty

                  a5: assert property (q6);
                    // illegal: no leading clocking event
                  a6: assert property ($fell(c) |=> q6);
                    // illegal: no leading clocking event

                  sequence s2;
                    $rose(a) ##[1:5] b;
                  endsequence

                  c1: cover property (s2);
                    // illegal: no leading clocking event
                  c2: cover property (@(negedge clk) s2);
                    // legal: explicit leading clocking event, @(negedge clk)

                  sequence s3;
                    @(negedge clk) s2;
                  endsequence

                  c3: cover property (s3);
                    // legal: leading clocking event, @(negedge clk),
                    // determined from declaration of s3
                  c4: cover property (s3 ##1 b);
                    // illegal: no default, inferred, or explicit leading
                    // clocking event and maximal property is not an instance
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"wire clk1, clk2;
                logic a, b;
                assign clk2 = clk1;
                a1: assert property (@(clk1) a and @(clk2) b); // Illegal
                a2: assert property (@(clk1) a and @(clk1) b); // OK
                always @(posedge clk1) begin
                  a3: assert property(a and @(posedge clk2) b); //Illegal
                  a4: assert property(a and @(posedge clk1) b); // OK
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"program tst;
                  initial begin
                    # 200ms;
                    expect( @(posedge clk) a ##1 b ##1 c ) else $error( "expect failed" );
                  end
                endprogram"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"integer data;
                task automatic wait_for( integer value, output bit success );
                expect( @(posedge clk) ##[1:10] data == value ) success = 1;
                  else success = 0;
                endtask

                initial begin
                  bit ok;
                  wait_for( 23, ok ); // wait for the value 23
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module A;
                  logic a, clk;

                  clocking cb_with_input @(posedge clk);
                    input a;
                    property p1;
                      a;
                    endproperty
                  endclocking

                  clocking cb_without_input @(posedge clk);
                    property p1;
                      a;
                    endproperty
                  endclocking

                  property p1;
                    @(posedge clk) a;
                  endproperty

                  property p2;
                    @(posedge clk) cb_with_input.a;
                  endproperty

                  a1: assert property (p1);
                  a2: assert property (cb_with_input.p1);
                  a3: assert property (p2);
                  a4: assert property (cb_without_input.p1);
                endmodule"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause17() {
        test!(
            many1(module_item),
            r##"checker my_check1 (logic test_sig, event clock);
                  default clocking @clock; endclocking
                  property p(logic sig);
                    a;
                  endproperty
                  a1: assert property (p (test_sig));
                  c1: cover property (!test_sig ##1 test_sig);
                endchecker : my_check1"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"checker my_check2 (logic a, b);
                  a1: assert #0 ($onehot0({a, b}));
                  c1: cover #0 (a == 0 && b == 0);
                  c2: cover #0 (a == 1);
                  c3: cover #0 (b == 1);
                endchecker : my_check2"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"checker my_check3 (logic a, b, event clock, output bit failure, undef);
                  default clocking @clock; endclocking
                  a1: assert property ($onehot0({a, b})) failure = 1'b0; else failure = 1'b1;
                  a2: assert property ($isunknown({a, b})) undef = 1'b0; else undef = 1'b1;
                endchecker : my_check3"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"checker my_check4 (input logic in,
                                   en = 1'b1, // default value
                                   event clock,
                                   output int ctr = 0); // initial value
                  default clocking @clock; endclocking
                  always_ff @clock
                    if (en && in) ctr <= ctr + 1;
                  a1: assert property (ctr < 5);
                endchecker : my_check4"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m;
                  default clocking @clk1; endclocking
                  default disable iff rst1;
                  checker c1;
                    // Inherits @clk1 and rst1
                  endchecker : c1
                  checker c2;
                    // Explicitly redefines its default values
                    default clocking @clk2; endclocking
                    default disable iff rst2;
                  endchecker : c2
                endmodule : m"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"checker mutex (logic [31:0] sig, event clock, output bit failure);
                  assert property (@clock $onehot0(sig))
                  failure = 1'b0; else failure = 1'b1;
                endchecker : mutex

                module m(wire [31:0] bus, logic clk);
                  logic res, scan;
                  // ...
                  mutex check_bus(bus, posedge clk, res);
                  always @(posedge clk) scan <= res;
                endmodule : m"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"checker c1(event clk, logic[7:0] a, b);
                  logic [7:0] sum;
                  always_ff @(clk) begin
                    sum <= a + 1'b1;
                    p0: assert property (sum < MAX_SUM);
                  end
                  p1: assert property (@clk sum < MAX_SUM);
                  p2: assert property (@clk a != b);
                  p3: assert #0 ($onehot(a));
                endchecker

                module m(input logic rst, clk, logic en, logic[7:0] in1, in2,
                         in_array [20:0]);
                  c1 check_outside(posedge clk, in1, in2);
                  always @(posedge clk) begin
                    automatic logic [7:0] v1=0;
                    if (en) begin
                      // v1 is automatic, so current procedural value is used
                      c1 check_inside(posedge clk, in1, v1);
                    end
                    for (int i = 0; i < 4; i++) begin
                      v1 = v1+5;
                      if (i != 2) begin
                        // v1 is automatic, so current procedural value is used
                        c1 check_loop(posedge clk, in1, in_array[v1]);
                      end
                    end
                  end
                endmodule : m"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"checker check_in_context (logic test_sig,
                                          event clock = $inferred_clock,
                                          logic reset = $inferred_disable);
                  property p(logic sig);
                    a;
                  endproperty
                  a1: assert property (@clock disable iff (reset) p(test_sig));
                  c1: cover property (@clock !reset throughout !test_sig ##1 test_sig);
                endchecker : check_in_context

                module m(logic rst);
                  wire clk;
                  logic a, en;
                  wire b = a && en;
                  // No context inference
                  check_in_context my_check1(.test_sig(b), .clock(clk), .reset(rst));
                  always @(posedge clk) begin
                    if (en) begin
                      // inferred from context:
                      // .clock(posedge clk)
                      // .reset(1'b0)
                      check_in_context my_check2(a);
                    end
                  end
                endmodule : m"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"checker check(logic a, b, c, clk, rst);
                  logic x, y, z, v, t;
                  assign x = a; // current value of a
                  always_ff @(posedge clk or negedge rst) // current values of clk and rst
                  begin
                    a1: assert (b); // sampled value of b
                    if (rst) // current value of rst
                      z <= b; // sampled value of b
                    else z <= !c; // sampled value of c
                  end

                  always_comb begin
                    a2: assert (b); // current value of b
                    if (a) // current value of a
                      v = b; // current value of b
                    else v = !b; // current value of b
                  end

                  always_latch begin
                    a3: assert (b); // current value of b
                    if (clk) // current value of clk
                      t <= b; // current value of b
                  end
                  // ...
                endchecker : check"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"checker clocking_example (logic sig1, sig2, default_clk, rst,
                                          event e1, e2, e3 );
                  bit local_sig;
                  default clocking @(posedge default_clk); endclocking

                  always_ff @(e1) begin: p1_block
                    p1a: assert property (sig1 == sig2);
                    p1b: assert property (@(e1) (sig1 == sig2));
                  end
                  always_ff @(e2 or e3) begin: p2_block
                    local_sig <= rst;
                    p2a: assert property (sig1 == sig2);
                    p2b: assert property (@(e2) (sig1 == sig2));
                  end
                  always_ff @(rst or e3) begin: p3_block
                    local_sig <= rst;
                    p3a: assert property (sig1 == sig2);
                    p3b: assert property (@(e3) (sig1 == sig2));
                  end
                endchecker

                clocking_example c1 (s1, s2, default_clk, rst,
                                     posedge clk1 or posedge clk2,
                                     posedge clk1,
                                     negedge rst);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"checker my_check(logic clk, active);
                  bit active_d1 = 1'b0;

                  always_ff @(posedge clk) begin
                    active_d1 <= active;
                  end

                  covergroup cg_active @(posedge clk);
                    cp_active : coverpoint active
                    {
                      bins idle = { 1'b0 };
                      bins active = { 1'b1 };
                    }
                    cp_active_d1 : coverpoint active_d1
                    {
                      bins idle = { 1'b0 };
                      bins active = { 1'b1 };
                    }
                    option.per_instance = 1;
                  endgroup
                  cg_active cg_active_1 = new();
                endchecker : my_check"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"checker op_test (logic clk, vld_1, vld_2, logic [3:0] opcode);
                  bit [3:0] opcode_d1;

                  always_ff @(posedge clk) opcode_d1 <= opcode;

                  covergroup cg_op;
                    cp_op : coverpoint opcode_d1;
                  endgroup: cg_op
                  cg_op cg_op_1 = new();

                  sequence op_accept;
                    @(posedge clk) vld_1 ##1 (vld_2, cg_op_1.sample());
                  endsequence
                  cover property (op_accept);
                endchecker"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"checker op_test (logic clk, vld_1, vld_2, logic [3:0] opcode);
                  bit [3:0] opcode_d1;

                  always_ff @(posedge clk) opcode_d1 <= opcode;

                  covergroup cg_op with function sample(bit [3:0] opcode_d1);
                    cp_op : coverpoint opcode_d1;
                  endgroup: cg_op
                  cg_op cg_op_1 = new();

                  sequence op_accept;
                    @(posedge clk) vld_1 ##1 (vld_2, cg_op_1.sample(opcode_d1));
                  endsequence
                  cover property (op_accept);
                endchecker"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"checker counter_model(logic flag);
                  bit [2:0] counter = '0;
                  always_ff @($global_clock)
                    counter <= counter + 1'b1;
                  assert property (@($global_clock) counter == 0 |-> flag);
                endchecker : counter_model"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"checker observer_model(bit valid, reset);
                  default clocking @($global_clock); endclocking
                  rand bit flag;

                  m1: assume property (reset |=> !flag);
                  m2: assume property (!reset && flag |=> flag);
                  m3: assume property ($rising_gclk(flag) |-> valid);
                endchecker : observer_model"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"checker reason_about_one_bit(bit [63:0] data1, bit [63:0] data2,
                                             event clock);
                  rand const bit [5:0] idx;
                  a1: assert property (@clock data1[idx] == data2[idx]);
                endchecker : reason_about_one_bit"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"checker reason_about_all_bit(bit [63:0] data1, bit [63:0] data2,
                                             event clock);
                  a1: assert property (@clock data1 == data2);
                endchecker : reason_about_all_bit"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"checker data_legal(start_ev, end_ev, in_data, out_data);
                  rand const bit [$bits(in_data)-1:0] mem_data;
                  sequence transaction;
                    start_ev && (in_data == mem_data) ##1 end_ev[->1];
                  endsequence
                  a1: assert property (@clock transaction |-> out_data == mem_data);
                endchecker : data_legal"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"checker data_legal_with_loc(start_ev, end_ev, in_data, out_data);
                  sequence transaction (loc_var);
                    (start_ev, loc_var = in_data) ##1 end_ev[->1];
                  endsequence
                  property data_legal;
                    bit [$bits(in_data)-1:0] mem_data;
                    transaction(mem_data) |-> out_data == mem_data;
                  endproperty
                  a1: assert property (@clock data_legal);
                endchecker : data_legal_with_loc"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"checker check;
                  bit a;
                endchecker

                module m;
                  check my_check;
                  wire x = my_check.a; // Illegal
                  bit y;
                  always @(posedge clk) begin
                    my_check.a = y; // Illegal
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"checker check1(bit a, b, event clk);
                  rand bit x, y, z, v;
                  assign x = a & b; // Illegal
                  always_comb
                    y = a & b; // Illegal
                  always_ff @clk
                    z <= a & b; // OK
                endchecker : check1"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module my_mod();
                  bit mclk, v1, v2;
                  checker c1(bit fclk, bit a, bit b);
                    default clocking @ (posedge fclk); endclocking
                    checker c2(bit bclk, bit x, bit y);
                      default clocking @ (posedge bclk); endclocking
                      rand bit m, n;
                      u1: assume property (f1(x,m));
                      u2: assume property (f2(y,n));
                    endchecker
                    rand bit q, r;
                    c2 B1(fclk, q+r, r);
                    always_ff @ (posedge fclk)
                      r <= a || q; // assignment makes r inactive
                    u3: assume property (f3(a, q));
                    u4: assume property (f4(b, r));
                  endchecker
                  c1 F1(mclk, v1, const'(v2));
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"checker my_check;
                  sequence s;
                    a;
                  endsequence
                  always_ff @clk a <= s.triggered;
                endchecker"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"checker check(bit clk1); // clk1 assigned in the Active region
                  rand bit v, w;
                  assign clk2 = clk1;
                  m1: assume property (@clk1 !(v && w));
                  m2: assume property (@clk2 v || w);
                  a1: assert property (@clk1 v != w);
                  // ...
                endchecker : check"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef enum { cover_none, cover_all } coverage_level;
                checker assert_window1 (
                  logic test_expr,     // Expression to be true in the window
                  untyped start_event, // Window opens at the completion of the start_event
                  untyped end_event,   // Window closes at the completion of the end_event
                  event clock = $inferred_clock,
                  logic reset = $inferred_disable,
                  string error_msg = "violation",
                  coverage_level clevel = cover_all // This argument should be bound to an
                                                    // elaboration time constant expression
                );
                  default clocking @clock; endclocking
                  default disable iff reset;
                  bit window = 1'b0, next_window = 1'b1;

                  // Compute next value of window
                  always_comb begin
                    if (reset || window && end_event)
                      next_window = 1'b0;
                    else if (!window && start_event)
                      next_window = 1'b1;
                    else
                      next_window = window;
                  end

                  always_ff @clock
                    window <= next_window;

                  property p_window;
                    start_event && !window |=> test_expr[+] ##0 end_event;
                  endproperty

                  a_window: assert property (p_window) else $error(error_msg);

                  generate if (clevel != cover_none) begin : cover_b
                    cover_window_open: cover property (start_event && !window)
                    $display("window_open covered");
                    cover_window: cover property (
                      start_event && !window
                      ##1 (!end_event && window) [*]
                      ##1 end_event && window
                    ) $display("window covered");
                    end : cover_b
                  endgenerate
                endchecker : assert_window1"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef enum { cover_none, cover_all } coverage_level;
                checker assert_window2 (
                  logic test_expr,      // Expression to be true in the window
                  sequence start_event, // Window opens at the completion of the start_event
                  sequence end_event,   // Window closes at the completion of the end_event
                  event clock = $inferred_clock,
                  logic reset = $inferred_disable,
                  string error_msg = "violation",
                  coverage_level clevel = cover_all // This argument should be bound to an
                                                    // elaboration time constant expression
                );
                  default clocking @clock; endclocking
                  default disable iff reset;
                  bit window = 0;
                  let start_flag = start_event.triggered;
                  let end_flag = end_event.triggered;

                  // Compute next value of window
                  function bit next_window (bit win);
                    if (reset || win && end_flag)
                      return 1'b0;
                    if (!win && start_flag)
                      return 1'b1;
                    return win;
                  endfunction

                  always_ff @clock
                    window <= next_window(window);

                  property p_window;
                    start_flag && !window |=> test_expr[+] ##0 end_flag;
                  endproperty

                  a_window: assert property (p_window) else $error(error_msg);

                  generate if (clevel != cover_none) begin : cover_b
                    cover_window_open: cover property (start_flag && !window)
                    $display("window_open covered");
                    cover_window: cover property (
                      start_flag && !window
                      ##1 (!end_flag && window) [*]
                      ##1 end_flag && window
                    ) $display("window covered");
                    end : cover_b
                  endgenerate
                endchecker : assert_window2"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause18() {
        test!(
            many1(module_item),
            r##"class Bus;
                  rand bit[15:0] addr;
                  rand bit[31:0] data;

                  constraint word_align {addr[1:0] == 2'b0;}
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  Bus bus = new;

                  repeat (50) begin
                    if ( bus.randomize() == 1 )
                      $display ("addr = %16h data = %h\n", bus.addr, bus.data);
                    else
                      $display ("Randomization failed.\n");
                  end
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef enum {low, mid, high} AddrType;
                class MyBus extends Bus;
                  rand AddrType atype;
                  constraint addr_range
                  {
                    (atype == low ) -> addr inside {  [0 : 15] };
                    (atype == mid ) -> addr inside { [16 : 127]};
                    (atype == high) -> addr inside {[128 : 255]};
                  }
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task exercise_bus (MyBus bus);
                  int res;

                  // EXAMPLE 1: restrict to low addresses
                  res = bus.randomize() with {atype == low;};

                  // EXAMPLE 2: restrict to address between 10 and 20
                  res = bus.randomize() with {10 <= addr && addr <= 20;};

                  // EXAMPLE 3: restrict data values to powers-of-two
                  res = bus.randomize() with {(data & (data - 1)) == 0;};
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task exercise_illegal(MyBus bus, int cycles);
                  int res;

                  // Disable word alignment constraint.
                  bus.word_align.constraint_mode(0);

                  repeat (cycles) begin
                    // CASE 1: restrict to small addresses.
                    res = bus.randomize() with {addr[0] || addr[1];};
                  end

                  // Reenable word alignment constraint
                  bus.word_align.constraint_mode(1);
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class XYPair;
                  rand integer x, y;
                endclass

                class MyXYPair extends XYPair;
                  function void pre_randomize();
                    super.pre_randomize();
                    $display("Before randomize x=%0d, y=%0d", x, y);
                  endfunction

                  function void post_randomize();
                    super.post_randomize();
                    $display("After randomize x=%0d, y=%0d", x, y);
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class packet;
                  typedef struct {
                    randc int addr = 1 + constant;
                    int crc;
                    rand byte data [] = {1,2,3,4};
                  } header;
                  rand header h1;
                endclass
                packet p1=new;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef enum bit [1:0] { A=2'b00, B=2'b11 } ab_e;
                typedef struct packed {
                  ab_e ValidAB;
                } VStructEnum;
                typedef union packed {
                  ab_e ValidAB;
                } VUnionEnum;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class C;
                  rand int x;
                  constraint proto1;        // implicit form
                  extern constraint proto2; // explicit form
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"virtual class D;
                  pure constraint Test;
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class c;
                  rand integer x, y, z;
                  constraint c1 {x inside {3, 5, [9:15], [24:32], [y:2*y], z};}

                  rand integer a, b, c;
                  constraint c2 {a inside {b, c};}

                  integer fives[4] = '{ 5, 10, 15, 20 };
                  rand integer v;
                  constraint c3 { v inside {fives}; }
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class c;
                  rand byte a[5];
                  rand byte b;
                  rand byte excluded;
                  constraint u { unique {b, a[2:3], excluded}; }
                  constraint exclusion { excluded == 5; }
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class c;
                  rand bit [3:0] a, b;
                  constraint c { (a == 0) -> (b == 1); }
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class C;
                  rand byte A[] ;

                  constraint C1 { foreach ( A [ i ] ) A[i] inside {2,4,8,16}; }
                  constraint C2 { foreach ( A [ j ] ) A[j] > 2 * j; }
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class C;
                  rand int A[] ;

                  constraint c1 { A.size inside {[1:10]}; }
                  constraint c2 { foreach ( A[ k ] ) (k < A.size - 1) -> A[k + 1] > A[k]; }
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class C;
                  rand bit [7:0] A[] ;
                  constraint c1 { A.size == 5; }
                  constraint c2 { A.sum() with (int'(item)) < 1000; }
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class A; // leaf node
                  rand bit [7:0] v;
                endclass

                class B extends A; // heap node
                  rand A left;
                  rand A right;

                  constraint heapcond {left.v <= v; right.v > v;}
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class B;
                  rand bit s;
                  rand bit [31:0] d;

                  constraint c { s -> d == 0; }
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class B;
                  rand bit s;
                  rand bit [31:0] d;
                  constraint c { s -> d == 0; }
                  constraint order { solve s before d; }
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"function int count_ones ( bit [9:0] w );
                  for( count_ones = 0; w != 0; w = w >> 1 )
                    count_ones += w & 1'b1;
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class B;
                  rand int x, y;
                  constraint C { x <= F(y); }
                  constraint D { y inside { 2, 4, 8 } ; }
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class SList;
                  rand int n;
                  rand Slist next;

                  constraint sort { n < next.n; }
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class D;
                  int x;
                endclass

                class C;
                  rand int x, y;
                  D a, b;
                  constraint c1 { (x < y || a.x > b.x || a.x == 5 ) -> x+y == 10; }
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class D;
                  int x;
                endclass

                class C;
                  rand int x, y;
                  D a, b;
                  constraint c1 { (x < y && a.x > b.x && a.x == 5 ) -> x+y == 10; }
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class D;
                  int x;
                endclass

                class C;
                  rand int x, y;
                  D a, b;
                  constraint c1 { (x < y && (a.x > b.x || a.x ==5)) -> x+y == 10; }
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class Packet;
                  rand bit mode;
                  rand int length;
                  constraint deflt {
                    soft length inside {32,1024};
                    soft mode -> length == 1024;
                    // Note: soft mode -> {length == 1024;} is not legal syntax,
                    // as soft must be followed by an expression
                  }
                endclass

                initial begin
                  Packet p = new();
                  p.randomize() with { length == 1512;};            // mode will randomize to 0
                  p.randomize() with { length == 1512; mode == 1;}; // mode will randomize to 1
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class B1;
                  rand int x;
                  constraint a { soft x > 10 ; soft x < 100 ; }
                endclass /* a1 */ /* a2 */
                class D1 extends B1;
                  constraint b { soft x inside {[5:9]} ; }
                endclass /* b1 */
                class B2;
                  rand int y;
                  constraint c { soft y > 10 ; }
                endclass /* c1 */
                class D2 extends B2;
                  constraint d { soft y inside {[5:9]} ; }
                  constraint e ; /* d1 */
                  rand D1 p1;
                  rand B1 p2;
                  rand D1 p3;
                  constraint f { soft p1.x < p2.x ; }
                endclass /* f1 */
                constraint D2::e { soft y > 100 ; }
                /* e1 */
                D2 d = new();
                initial begin
                  d.randomize() with { soft y inside {10,20,30} ; soft y < p1.x ; };
                end /* i1 */ /* i2 */"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class A;
                  rand int x;
                  constraint A1 { soft x == 3; }
                  constraint A2 { disable soft x; } // discard soft constraints
                  constraint A3 { soft x inside { 1, 2 }; }
                endclass

                initial begin
                  A a = new();
                  a.randomize();
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class B;
                  rand int x;
                  constraint B1 { soft x == 5; }
                  constraint B2 { disable soft x; soft x dist {5, 8};}
                endclass

                initial begin
                  B b = new();
                  b.randomize();
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class B;
                  rand int x;
                  constraint B1 { soft x == 5; }
                  constraint B3 { soft x dist {5, 8}; }
                endclass

                initial begin
                  B b = new();
                  b.randomize();
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class SimpleSum;
                  rand bit [7:0] x, y, z;
                  constraint c {z == x + y;}
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class SimpleSum;
                  rand bit [7:0] x, y, z;
                  constraint c {z == x + y;}
                endclass

                task InlineConstraintDemo(SimpleSum p);
                  int success;
                  success = p.randomize() with {x < y;};
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class C1;
                  rand integer x;
                endclass

                class C2;
                  integer x;
                  integer y;

                  task doit(C1 f, integer x, integer z);
                    int result;
                    result = f.randomize() with {x < y + z;};
                  endtask
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class C;
                  rand integer x;
                endclass

                function int F(C obj, integer y);
                  F = obj.randomize() with (x) { x < y; };
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class C;
                  rand integer x;
                endclass

                function int F(C obj, integer x);
                  F = obj.randomize() with { x < local::x; };
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class Packet;
                  rand integer source_value, dest_value;
                endclass

                initial begin
                  int ret;
                  Packet packet_a = new;
                  // Turn off all variables in object
                  packet_a.rand_mode(0);
                  // ... other code
                  // Enable source_value
                  packet_a.source_value.rand_mode(1);
                  ret = packet_a.dest_value.rand_mode();
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class Packet;
                  rand integer source_value;
                  constraint filter1 { source_value > 2 * m; }
                endclass

                function integer toggle_rand( Packet p );
                  if ( p.filter1.constraint_mode() )
                    p.filter1.constraint_mode(0);
                  else
                    p.filter1.constraint_mode(1);
                  toggle_rand = p.randomize();
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class CA;
                  rand byte x, y;
                  byte v, w;
                  constraint c1 { x < v && y > w; };
                endclass

                initial begin
                  CA a = new;
                  a.randomize();       // random variables: x, y state variables: v, w
                  a.randomize( x );    // random variables: x    state variables: y, v, w
                  a.randomize( v, w ); // random variables: v, w state variables: x, y
                  a.randomize( w, x ); // random variables: w, x state variables: y, v
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module stim;
                  bit [15:0] addr;
                  bit [31:0] data;

                  function bit gen_stim();
                    bit success, rd_wr;

                    success = randomize( addr, data, rd_wr ); // call std::randomize
                    return rd_wr ;
                  endfunction
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class stimc;
                  rand bit [15:0] addr;
                  rand bit [31:0] data;
                  rand bit rd_wr;
                endclass

                function bit gen_stim( stimc p );
                  bit [15:0] addr;
                  bit [31:0] data;
                  bit success;
                  success = p.randomize();
                  addr = p.addr;
                  data = p.data;
                  return p.rd_wr;
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task stimulus( int length );
                  int a, b, c, success;

                  success = std::randomize( a, b, c ) with { a < b ; a + b < length ; };
                  success = std::randomize( a, b ) with { b - a > length ; };
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  bit [64:1] addr;
                  bit [ 3:0] number;
                  addr[32:1] = $urandom( 254 ); // Initialize the generator,
                                                // get 32-bit random number
                  addr = {$urandom, $urandom }; // 64-bit random number
                  number = $urandom & 15;       // 4-bit random number
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  integer x, y, z;
                  fork //set a seed at the start of a thread
                    begin process::self.srandom(100); x = $urandom; end
                       //set a seed during a thread
                    begin y = $urandom; process::self.srandom(200); end
                       // draw 2 values from the thread RNG
                    begin z = $urandom + $urandom ; end
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class C1;
                  rand integer x;
                endclass

                class C2;
                  rand integer y;
                endclass

                initial begin
                  C1 c1 = new();
                  C2 c2 = new();
                  integer z;
                  void'(c1.randomize());
                  // z = $random;
                  void'(c2.randomize());
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class C3;
                  function new (integer seed);
                    //set a new seed for this instance
                    this.srandom(seed);
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class Packet;
                  rand bit[15:0] header;
                  function new (int seed);
                    this.srandom(seed);
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  randcase
                    3 : x = 1;
                    1 : x = 2;
                    4 : x = 3;
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  byte a, b;
                  randcase
                    a + b : x = 1;
                    a - b : x = 2;
                    a ^ ~b : x = 3;
                    12'h800 : x = 4;
                  endcase
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  randsequence( main )
                    main   : first second done ;
                    first  : add | dec ;
                    second : pop | push ;
                    done   : { $display("done"); } ;
                    add    : { $display("add");  } ;
                    dec    : { $display("dec");  } ;
                    pop    : { $display("pop");  } ;
                    push   : { $display("push"); } ;
                  endsequence
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  randsequence()
                    PP_OP : if ( depth < 2 ) PUSH else POP ;
                    PUSH  : { ++depth; do_push(); };
                    POP   : { --depth; do_pop(); };
                  endsequence
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  randsequence()
                    SELECT : case ( device & 7 )
                      0       : NETWORK ;
                      1, 2    : DISK ;
                      default : MEMORY ;
                    endcase ;
                  endsequence
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  randsequence()
                    PUSH_OPER : repeat( $urandom_range( 2, 6 ) ) PUSH ;
                  endsequence
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  randsequence( TOP )
                    TOP : rand join S1 S2 ;
                    S1  : A B ;
                    S2  : C D ;
                  endsequence
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  randsequence()
                    WRITE : SETUP DATA ;
                    SETUP : { if( fifo_length >= max_length ) break; } COMMAND ;
                  endsequence
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  randsequence()
                    TOP : P1 P2 ;
                    P1  : A B C ;
                    P2  : A { if( flag == 1 ) return; } B C ;
                    A   : { $display( "A" ); } ;
                    B   : { if( flag == 2 ) return; $display( "B" ); } ;
                    C   : { $display( "C" ); } ;
                  endsequence
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  randsequence( main )
                    main                     : first second gen ;
                    first                    : add | dec ;
                    second                   : pop | push ;
                    add                      : gen("add") ;
                    dec                      : gen("dec") ;
                    pop                      : gen("pop") ;
                    push                     : gen("push") ;
                    gen( string s = "done" ) : { $display( s ); } ;
                  endsequence
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  randsequence( bin_op )
                    void bin_op : value operator value // void type is optional
                                  { $display("%s %b %b", operator, value[1], value[2]); }
                                  ;
                    bit [7:0] value : { return $urandom; } ;
                    string operator : add := 5 { return "+" ; }
                                    | dec := 2 { return "-" ; }
                                    | mult := 1 { return "*" ; }
                                    ;
                  endsequence
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  int cnt;
                  randsequence( A )
                    void A  : A1 A2;
                    void A1 : { cnt = 1; } B repeat(5) C B
                            { $display("c=%d, b1=%d, b2=%d", C, B[1], B[2]); }
                            ;
                    void A2 : if (cond) D(5) else D(20)
                            { $display("d1=%d, d2=%d", D[1], D[2]); }
                            ;
                    int B   : C { return C;}
                            | C C { return C[2]; }
                            | C C C { return C[3]; }
                            ;
                    int C   : { cnt = cnt + 1; return cnt; };
                    int D (int prm) : { return prm; };
                  endsequence
                end"##,
            Ok((_, _))
        );
        // TODO
        // function can't return queue
        //test!(
        //    many1(module_item),
        //    r##"function int[$] GenQueue(int low, int high);
        //          int[$] q;

        //          randsequence()
        //            TOP      : BOUND(low) LIST BOUND(high) ;
        //            LIST     : LIST ITEM := 8 { q = { q, ITEM }; }
        //                          | ITEM := 2 { q = { q, ITEM }; }
        //                       ;
        //            int ITEM : { return $urandom_range( low, high ); } ;

        //            BOUND(int b) : { q = { q, b }; } ;
        //          endsequence
        //          GenQueue = q;
        //        endfunction"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"class DSL; endclass // class that creates valid DSL packets

                initial begin
                  randsequence (STREAM)
                    STREAM : GAP DATA := 80
                           | DATA := 20 ;
                    DATA   : PACKET(0) := 94 { transmit( PACKET ); }
                           | PACKET(1) := 6 { transmit( PACKET ); } ;

                    DSL PACKET (bit bad) : { DSL d = new;
                                           if( bad ) d.crc ^= 23; // mangle crc
                                           return d;
                                           };
                    GAP: { ## ($urandom_range( 1, 20 )); };
                  endsequence
                end"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause19() {
        test!(
            many1(module_item),
            r##"covergroup cg; endgroup
                cg cg_inst = new;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"enum { red, green, blue } color;

                covergroup g1 @(posedge clk);
                  c: coverpoint color;
                endgroup"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"enum { red, green, blue } color;
                bit [3:0] pixel_adr, pixel_offset, pixel_hue;

                covergroup g2 @(posedge clk);
                  Hue: coverpoint pixel_hue;
                  Offset: coverpoint pixel_offset;
                  AxC: cross color, pixel_adr;   // cross 2 variables (implicitly declared
                                                 // coverpoints)
                  all: cross color, Hue, Offset; // cross 1 variable and 2 coverpoints
                endgroup"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class xyz;
                  bit [3:0] m_x;
                  int m_y;
                  bit m_z;

                  covergroup cov1 @m_z; // embedded covergroup
                    coverpoint m_x;
                    coverpoint m_y;
                  endgroup

                  function new(); cov1 = new; endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class MC;
                  logic [3:0] m_x;
                  local logic m_z;
                  bit m_e;
                  covergroup cv1 @(posedge clk); coverpoint m_x; endgroup
                  covergroup cv2 @m_e ; coverpoint m_z; endgroup
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class Helper;
                  int m_ev;
                endclass

                class MyClass;
                  Helper m_obj;
                  int m_a;
                  covergroup Cov @(m_obj.m_ev);
                    coverpoint m_a;
                  endgroup

                  function new();
                    m_obj = new;

                    Cov = new; // Create embedded covergroup after creating m_obj
                  endfunction
                endclass"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class C1;
                  bit [7:0] x;

                  covergroup cv (int arg) @(posedge clk);
                    option.at_least = arg;
                    coverpoint x;
                  endgroup

                  function new(int p1);
                    cv = new(p1);
                  endfunction
                endclass

                initial begin
                  C1 obj = new(4);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"covergroup cg ( ref int x , ref int y, input int c);

                  coverpoint x;      // creates coverpoint "x" covering the formal "x"
                  x: coverpoint y;   // INVALID: coverpoint label "x" already exists
                  b: coverpoint y;   // creates coverpoint "b" covering the formal "y"

                  cx: coverpoint x;  // creates coverpoint "cx" covering the formal "x"

                  option.weight = c; // set weight of "cg" to value of formal "c"

                  bit [7:0] d: coverpoint y[31:24]; // creates coverpoint "d" covering the
                                                    // high order 8 bits of the formal "y"
                  e: coverpoint x {
                    option.weight = 2; // set the weight of coverpoint "e"
                  }
                  //e.option.weight = 2; // INVALID use of "e", also syntax error

                  cross x, y {         // Creates implicit coverpoint "y" covering
                                       // the formal "y". Then creates a cross of
                                       // coverpoints "x", "y"
                    option.weight = c; // set weight of cross to value of formal "c"
                  }
                  b: cross y, x;       // INVALID: coverpoint label "b" already exists
                endgroup"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"covergroup g4;
                  coverpoint s0 iff(!reset);
                endgroup"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [9:0] v_a;

                covergroup cg @(posedge clk);

                  coverpoint v_a
                  {
                    bins a = { [0:63],65 };
                    bins b[] = { [127:150],[148:191] }; // note overlapping values
                    bins c[] = { 200,201,202 };
                    bins d = { [1000:$] };
                    bins others[] = default;
                  }
                endgroup"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"covergroup cg (ref int ra, input int low, int high ) @(posedge clk);
                  coverpoint ra // sample variable passed by reference
                  {
                    bins good = { [low : high] };
                    bins bad[] = default;
                  }
                endgroup

                int va, vb;
                cg c1 = new( va, 0, 50 );    // cover variable va in the range 0 to 50
                cg c2 = new( vb, 120, 600 ); // cover variable vb in the range 120 to 600"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [4:1] v_a;
                covergroup cg @(posedge clk);
                  coverpoint v_a
                  {
                    bins sa = (4 => 5 => 6), ([7:9],10=>11,12);
                    bins sb[] = (4=> 5 => 6), ([7:9],10=>11,12);
                    bins sc = (12 => 3 [-> 1]);
                    bins allother = default sequence ;
                  }
                endgroup"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"covergroup sg @(posedge clk);
                  coverpoint v
                  {
                    bins b2 = ( 2 [-> 3:5] );          // 3 to 5 nonconsecutive 2's
                    bins b3 = ( 3 [-> 3:5] );          // 3 to 5 nonconsecutive 3's
                    bins b5 = ( 5 [* 3] );             // 3 consecutive 5's
                    bins b6 = ( 1 => 3 [-> 4:6] => 1); // 1 followed by
                                                       // 4 to 6 goto nonconsecutive 3's
                                                       // followed immediately by a 1
                    bins b7 = ( 1 => 2 [= 3:6] => 5);  // 1 followed by
                                                       // 3 to 6 non consecutive 2's
                                                       // followed sometime later by a 5
                  }
                endgroup"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"covergroup cg23;
                  coverpoint a
                  {
                    ignore_bins ignore_vals = {7,8};
                    ignore_bins ignore_trans = (1=>3=>5);
                  }
                endgroup"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"covergroup cg3;
                  coverpoint b
                  {
                    illegal_bins bad_vals = {1,2,3};
                    illegal_bins bad_trans = (4=>5=>6);
                  }
                endgroup"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [2:0] p1; // type expresses values in the range 0 to 7
                bit signed [2:0] p2; // type expresses values in the range –4 to 3
                covergroup g1 @(posedge clk);
                  coverpoint p1 {
                    bins b1 = { 1, [2:5], [6:10] };
                    bins b2 = { -1, [1:10], 15 };
                  }
                  coverpoint p2 {
                    bins b3 = {1, [2:5], [6:10] };
                    bins b4 = { -1, [1:10], 15 };
                  }
                endgroup"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [3:0] a, b;

                covergroup cov @(posedge clk);
                  aXb : cross a, b;
                endgroup"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [3:0] a, b, c;

                covergroup cov2 @(posedge clk);
                  BC: coverpoint b+c;
                  aXb : cross a, BC;
                endgroup"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [31:0] a_var;
                bit [3:0] b_var;

                covergroup cov3 @(posedge clk);
                  A: coverpoint a_var { bins yy[] = { [0:9] }; }
                  CC: cross b_var, A;
                endgroup"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int i,j;
                covergroup ct;
                  coverpoint i { bins i[] = { [0:1] }; }
                  coverpoint j { bins j[] = { [0:1] }; }
                  x1: cross i,j;
                  x2: cross i,j {
                    bins i_zero = binsof(i) intersect { 0 };
                  }
                endgroup"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [7:0] v_a, v_b;

                covergroup cg @(posedge clk);
                  a: coverpoint v_a
                  {
                    bins a1 = { [0:63] };
                    bins a2 = { [64:127] };
                    bins a3 = { [128:191] };
                    bins a4 = { [192:255] };
                  }

                  b: coverpoint v_b
                  {
                    bins b1 = {0};
                    bins b2 = { [1:84] };
                    bins b3 = { [85:169] };
                    bins b4 = { [170:255] };
                  }

                  c : cross a, b
                  {
                    bins c1 = ! binsof(a) intersect {[100:200]};// 4 cross products
                    bins c2 = binsof(a.a2) || binsof(b.b2);// 7 cross products
                    bins c3 = binsof(a.a1) && binsof(b.b4);// 1 cross product
                  }
                endgroup"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [0:7] a, b;
                parameter [0:7] mask;

                covergroup cg;
                  coverpoint a
                  {
                    bins low[] = {[0:127]};
                    bins high = {[128:255]};
                  }
                  coverpoint b
                  {
                    bins two[] = b with (item % 2 == 0);
                    bins three[] = b with (item % 3 == 0);
                  }
                  X: cross a,b
                  {
                    bins apple = X with (a+b < 257) matches 127;
                    bins cherry = ( binsof(b) intersect {[0:50]}
                                 && binsof(a.low) intersect {[0:50]} with (a==b) );
                    bins plum = binsof(b.two) with (b > 12)
                             || binsof(a.low) with (a & b & mask);
                  }
                endgroup"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"int a;
                logic [7:0] b;
                covergroup cg;
                  coverpoint a { bins x[] = {[0:10]}; }
                  coverpoint b { bins y[] = {[0:20]}; }
                  aXb : cross a, b
                  {
                    bins one = '{ '{1,2}, '{3,4}, '{5,6} };
                  }
                endgroup"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module mod_m;
                  logic [31:0] a, b;

                  covergroup cg(int cg_lim);
                    coverpoint a;
                    coverpoint b;
                    aXb : cross a, b
                    {
                      function CrossQueueType myFunc1(int f_lim);
                        for (int i = 0; i < f_lim; ++i)
                          myFunc1.push_back('{i,i});
                      endfunction

                      bins one = myFunc1(cg_lim);
                      bins two = myFunc2(cg_lim);

                      function CrossQueueType myFunc2(logic [31:0] f_lim);
                        for (logic [31:0] i = 0; i < f_lim; ++i)
                          myFunc2.push_back('{2*i,2*i});
                      endfunction
                    }
                  endgroup

                  cg cg_inst = new(3);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"covergroup yy;
                  cross a, b
                  {
                    ignore_bins ignore = binsof(a) intersect { 5, [1:3] };
                  }
                endgroup"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"covergroup zz(int bad);
                  cross x, y
                  {
                    illegal_bins illegal = binsof(y) intersect {bad};
                  }
                endgroup"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"covergroup g1 (int w, string instComment) @(posedge clk) ;
                  // track coverage information for each instance of g1 in addition
                  // to the cumulative coverage information for covergroup type g1
                  option.per_instance = 1;

                  // comment for each instance of this covergroup
                  option.comment = instComment;

                  a : coverpoint a_var
                  {
                    // Create 128 automatic bins for coverpoint “a” of each instance of g1
                    option.auto_bin_max = 128;
                  }
                  b : coverpoint b_var
                  {
                    // This coverpoint contributes w times as much to the coverage of an
                    // instance of g1 as coverpoints "a" and "c1"
                    option.weight = w;
                  }
                  c1 : cross a_var, b_var ;
                endgroup"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"covergroup gc (int maxA, int maxB) @(posedge clk) ;
                  a : coverpoint a_var;
                  b : coverpoint b_var;
                endgroup

                initial begin
                  gc g1 = new (10,20);
                  g1.option.comment = "Here is a comment set for the instance g1";
                  g1.a.option.weight = 3; // Set weight for coverpoint "a" of instance g1
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"covergroup g1 (int w, string instComment) @(posedge clk) ;
                  // track coverage information for each instance of g1 in addition
                  // to the cumulative coverage information for covergroup type g1
                  option.per_instance = 1;

                  type_option.comment = "Coverage model for features x and y";

                  type_option.strobe = 1; // sample at the end of the time slot

                  // compute type coverage as the merge of all instances
                  type_option.merge_instances = 1;

                  // comment for each instance of this covergroup
                  option.comment = instComment;

                  a : coverpoint a_var
                  {
                    // Use weight 2 to compute the coverage of each instance
                    option.weight = 2;
                    // Use weight 3 to compute the cumulative (type) coverage for g1
                    type_option.weight = 3;
                    // NOTE: type_option.weight = w would cause syntax error.
                  }
                  b : coverpoint b_var
                  {
                    // Use weight w to compute the coverage of each instance
                    option.weight = w;
                    // Use weight 5 to compute the cumulative (type) coverage of g1
                    type_option.weight = 5;
                  }
                endgroup"##,
            Ok((_, _))
        );
        //test!(
        //    many1(module_item),
        //    r##"covergroup gc @(posedge clk) ;
        //          a : coverpoint a_var;
        //          b : coverpoint b_var;
        //        endgroup

        //        initial begin
        //          // Set the comment for all covergroups of type "gc"
        //          gc::type_option.comment = "Here is a comment for covergroup g1";
        //          // Set the weight for coverpoint "a" of all covergroups of type gc
        //          gc::a::type_option.weight = 3;
        //          gc g1 = new;
        //        end"##,
        //    Ok((_, _))
        //);
        //test!(
        //    many1(module_item),
        //    r##"covergroup cg (int xb, yb, ref int x, y) ;
        //          coverpoint x {bins xbins[] = { [0:xb] }; }
        //          coverpoint y {bins ybins[] = { [0:yb] }; }
        //        endgroup
        //        cg cv1 = new (1,2,a,b); // cv1.x has 2 bins, cv1.y has 3 bins
        //        cg cv2 = new (3,6,c,d); // cv2.x has 4 bins, cv2.y has 7 bins

        //        initial begin
        //          cv1.x.get_inst_coverage(covered,total); // total = 2
        //          cv1.get_inst_coverage(covered,total);   // total = 5
        //          cg::x::get_coverage(covered,total);     // total = 6
        //          cg::get_coverage(covered,total);        // total = 16
        //        end"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"covergroup p_cg with function sample(bit a, int x);
                  coverpoint x;
                  cross x, a;
                endgroup : p_cg

                p_cg cg1 = new;

                property p1;
                  int x;
                  @(posedge clk)(a, x = b) ##1 (c, cg1.sample(a, x));
                endproperty : p1

                c1: cover property (p1);

                function automatic void F(int j);
                  bit d;
                  cg1.sample( d, j );
                endfunction"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"covergroup C1 (int v) with function sample (int v, bit b); // error (v)
                  coverpoint v;
                  option.per_instance = b;// error: b may only designate a coverpoint
                  option.weight = v; // error: v is ambiguous
                endgroup"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"struct // covergroup option declaration
                {
                  string name ;
                  int weight ;
                  int goal ;
                  string comment ;
                  int at_least ;
                  int auto_bin_max ;
                  int cross_num_print_missing ;
                  bit detect_overlap ;
                  bit per_instance ;
                  bit get_inst_coverage ;
                } option;

                struct // coverpoint option declaration
                {
                  int weight ;
                  int goal ;
                  string comment ;
                  int at_least ;
                  int auto_bin_max ;
                  bit detect_overlap ;
                } option;

                struct // cross option declaration
                {
                  int weight ;
                  int goal ;
                  string comment ;
                  int at_least ;
                  int cross_num_print_missing ;
                } option;

                struct // covergroup type_option declaration
                {
                  int weight ;
                  int goal ;
                  string comment ;
                  bit strobe ;
                  bit merge_instances ;
                  bit distribute_first ;
                } type_option;

                struct // coverpoint and cross type_option declaration
                {
                  int weight ;
                  int goal ;
                  string comment ;
                } type_option;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [2:0] a, b;
                covergroup ct;
                  coverpoint b {
                    option.auto_bin_max = 4;
                    ignore_bins ig = { [0:1], [5:6] };
                  }
                endgroup"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"covergroup gt ( int l, h);
                  coverpoint a { bins b[] = { [l:h] }; }
                endgroup
                gt gv1 = new (0,1);
                gt gv2 = new (1,2);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bit [7:0] a;
                covergroup ga ( int abm);
                  option.auto_bin_max = abm;
                  coverpoint a { ignore_bins i = {3}; }
                endgroup
                ga gv1 = new (64);
                ga gv2 = new (32);"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause20() {
        test!(
            source_text,
            r##"`timescale 10 ns / 1 ns
                module test;
                  logic set;
                  parameter p = 1.55;
                  initial begin
                    $monitor($time,,"set=", set);
                    #p set = 0;
                    #p set = 1;
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"`timescale 10 ns / 1 ns
                module test;
                  logic set;
                  parameter p = 1.55;
                  initial begin
                    $monitor($realtime,,"set=", set);
                    #p set = 0;
                    #p set = 1;
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"`timescale 1 ms / 1 us
                module a_dat;
                  initial
                    $printtimescale(b_dat.c1);
                endmodule

                `timescale 10 fs / 1 fs
                module b_dat;
                  c_dat c1 ();
                endmodule

                `timescale 1 ns / 1 ns
                module c_dat;
                endmodule"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"`timescale 1 ms / 1 ns
                module cntrl;
                  initial
                    $timeformat(-9, 5, " ns", 10);
                endmodule

                `timescale 1 fs / 1 fs
                module a1_dat;
                  logic in1;
                  integer file;
                  buf #10000000 (o1,in1);
                  initial begin
                    file = $fopen("a1.dat");
                    #00000000 $fmonitor(file,"%m: %t in1=%d o1=%h", $realtime,in1,o1);
                    #10000000 in1 = 0;
                    #10000000 in1 = 1;
                  end
                endmodule

                `timescale 1 ps / 1 ps
                module a2_dat;
                  logic in2;
                  integer file2;
                  buf #10000 (o2,in2);
                  initial begin
                    file2=$fopen("a2.dat");
                    #00000 $fmonitor(file2,"%m: %t in2=%d o2=%h",$realtime,in2,o2);
                    #10000 in2 = 0;
                    #10000 in2 = 1;
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module driver (net_r);
                  output [64:1] net_r;
                  real r;
                  wire [64:1] net_r = $realtobits(r);
                endmodule

                module receiver (net_r);
                  input [64:1] net_r;
                  wire [64:1] net_r;
                  real r;
                  initial assign r = $bitstoreal(net_r);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"typedef bit node; // "bit"
                node [2:0] X; // "bit [2:0]"
                int signed Y; // "int"
                package A;
                  enum {A,B,C=99} X; // "enum{A=32'sd0,B=32'sd1,C=32'sd99}A::e$1"
                  typedef bit [9:1'b1] word; // "A::bit[9:1]"
                endpackage : A
                import A::*;
                module top;
                  typedef struct {node A,B;} AB_t;
                  AB_t AB[10]; // "struct{bit A;bit B;}top.AB_t$[0:9]"
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"typedef bit[$bits(MyType):1] MyBits; //same as typedef bit [9:1] MyBits;
                MyBits b;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [3:0][2:1] n [1:5][2:8];
                typedef logic [3:0][2:1] packed_reg;
                packed_reg n[1:5][2:8]; // same dimensions as in the lines above"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  int a[3][][5]; // array dimension 2 has variable size
                  $display( $unpacked_dimensions(a) ); // displays 3
                  a[2] = new[4];
                  a[2][2][0] = 220;           // OK, a[2][2] is a 5-element array
                  $display( $size(a, 1) );    // OK, displays 3
                  $display( $size(a, 2) );    // ERROR, dimension 2 is dynamic
                  $display( $size(a[2], 1) ); // OK, displays 4 (a[2] is
                                              // a 4-element dynamic array)
                  $display( $size(a[1], 1) ); // OK, displays 0 (a[1] is
                                              // an empty dynamic array)
                  $display( $size(a, 3) );    // OK, displays 5 (fixed-size dimension)
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  integer result;
                  result = $clog2(n);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"logic [1:0] bad_bits;
                logic [31:0] myvec;
                logic design_initialization_done;

                always_comb begin
                  if (!design_initialization_done) begin
                    bad_bits[0] = 'x;
                    bad_bits[1] = 'x; // Repeated control_bit same as single occurrence
                  end else begin
                    bad_bits[0] = 'x;
                    bad_bits[1] = 'z;
                  end

                  // Z allowed during initialization, but no Z or X allowed afterwards
                  a1: assert ($countbits(myvec,bad_bits[0],bad_bits[1]) == 0);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module test #(N = 1) (input [N-1:0] in, output [N-1:0] out);
                  if ((N < 1) || (N > 8)) // conditional generate construct
                    $error("Parameter N has an invalid value of %0d", N);
                  assign out = in;
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"generate
                  if ($bits(vect) == 1) begin : err $error("Only a 1-bit vector"); end
                  for (genvar i = 0; i < $bits(vect); i++) begin : Loop
                    if (i==0) begin : Cond
                      sequence t; vect[0]; endsequence
                      $info("i=0 branch generated");
                    end : Cond
                    else begin : Cond
                      sequence t; vect[i] ##1 Loop[i-1].Cond.t; endsequence
                      $info("i = %0d branch generated", i);
                    end : Cond
                  end : Loop
                endgenerate

                // instantiate the last generated sequence in a property
                property p;
                  @(posedge clk) trig |-> Loop[$bits(vect)-1].Cond.t;
                endproperty"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module test;
                  logic clk;
                  logic a, b;
                  logic c, d;

                  // Define lets to make the code more readable.
                  let LOCK = 1;
                  let UNLOCK = 2;
                  let ON = 3;
                  let OFF = 4;
                  let KILL = 5;

                  let CONCURRENT = 1;
                  let S_IMMEDIATE = 2; // simple immediate
                  let D_IMMEDIATE = 12; // Final and Observed deferred immediate
                  let EXPECT = 16;
                  let UNIQUE = 32; // unique if and case violation
                  let UNIQUE0 = 64; // unique0 if and case violation
                  let PRIORITY = 128; // priority if and case violation
                  let ASSERT = 1;
                  let COVER = 2;
                  let ASSUME = 4;

                  let ALL_DIRECTIVES = (ASSERT|COVER|ASSUME);
                  let ALL_ASSERTS = (CONCURRENT|S_IMMEDIATE|D_IMMEDIATE|EXPECT);

                  let VACUOUSOFF = 11;

                  a1: assert property (@(posedge clk) a |=> b) $info("assert passed");
                      else $error("assert failed");
                  c1: cover property (@(posedge clk) a ##1 b);

                  always @(posedge clk) begin
                    ia1: assert (a);
                  end

                  always_comb begin
                    if (c)
                      df1: assert #0 (d);
                    unique if ((a==0) || (a==1)) $display("0 or 1");
                    else if (a == 2) $display("2");
                    else if (a == 4) $display("4"); // values 3,5,6,7 cause a violation
                                                    // report
                  end

                  initial begin
                    // The following systasks affect the whole design so no modules
                    // are specified

                    // Disable vacuous pass action for all the concurrent asserts,
                    // covers and assumes in the design. Also disable vacuous pass
                    // action for expect statements.
                    $assertcontrol(VACUOUSOFF, CONCURRENT | EXPECT);

                    // Disable concurrent and immediate asserts and covers.
                    // This will also disable violation reporting.
                    // The following systask does not affect expect
                    // statements as control type is Off.
                    $assertcontrol(OFF); // using default values of all the
                                         // arguments after first argument

                    // After 20 time units, enable assertions,
                    // This will not enable violation reporting.
                    // explicitly specifying second, third and fourth arguments
                    // in the following task call
                    #20 $assertcontrol(ON, CONCURRENT|S_IMMEDIATE|D_IMMEDIATE,
                                       ASSERT|COVER|ASSUME, 0);

                    // Enable violation reporting after 20 time units.
                    #20 $assertcontrol(ON, UNIQUE|UNIQUE0|PRIORITY);

                    // Kill currently executing concurrent assertions after
                    // 100 time units but do not kill concurrent covers/assumes
                    // and immediate/deferred asserts/covers/assumes
                    // using appropriate values of second and third arguments.
                    #100 $assertcontrol(KILL, CONCURRENT, ASSERT, 0);

                    // The following assertion control task does not have any effect as
                    // directive_type is assert but it has selected cover directive c1.
                    #10 $assertcontrol(ON, CONCURRENT|S_IMMEDIATE|D_IMMEDIATE, ASSERT, 0,
                                       c1);

                    // Now, after 10 time units, enable all the assertions except a1.
                    // To accomplish this, first we’ll lock a1 and then we’ll enable all
                    // the assertions and then unlock a1 as we want future assertion
                    // control tasks to affect a1.
                    #10 $assertcontrol(LOCK, ALL_ASSERTS, ALL_DIRECTIVES, 0, a1);
                    $assertcontrol(ON); // enable all the assertions except a1
                    $assertcontrol(UNLOCK, ALL_ASSERTS, ALL_DIRECTIVES, 0, a1);
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"wire a1, a2, a3, a4, a5, a6, a7;
                logic b1, b2, b3;
                wire [1:7] awire;
                logic [1:3] breg;

                initial begin
                  $async$and$array(mem,{a1,a2,a3,a4,a5,a6,a7},{b1,b2,b3});
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module async_array(a1,a2,a3,a4,a5,a6,a7,b1,b2,b3);
                  input a1, a2, a3, a4, a5, a6, a7 ;
                  output b1, b2, b3;
                  logic [1:7] mem[1:3]; // memory declaration for array personality
                  logic b1, b2, b3;
                  initial begin
                    // set up the personality from the file array.dat
                    $readmemb("array.dat", mem);
                    // set up an asynchronous logic array with the input
                    // and output terms expressed as concatenations
                    $async$and$array(mem,{a1,a2,a3,a4,a5,a6,a7},{b1,b2,b3});
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module sync_array(a1,a2,a3,a4,a5,a6,a7,b1,b2,b3,clk);
                  input a1, a2, a3, a4, a5, a6, a7, clk;
                  output b1, b2, b3;
                  logic [1:7] mem[1:3]; // memory declaration
                  logic b1, b2, b3;
                  initial begin
                    // set up the personality
                    $readmemb("array.dat", mem);
                    // set up a synchronous logic array to be evaluated
                    // when a positive edge on the clock occurs
                    forever @(posedge clk)
                      $async$and$array(mem,{a1,a2,a3,a4,a5,a6,a7},{b1,b2,b3});
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module pla;
                  logic [1:cols] a, mem[1:rows];
                  logic [1:rows] b;
                  initial begin
                    // PLA system call
                    $async$and$plane(mem,a[1:3],b[1:4]);
                    mem[1] = 3'b10?;
                    mem[2] = 3'b??1;
                    mem[3] = 3'b0?0;
                    mem[4] = 3'b???;
                    // stimulus and display
                    #10 a = 3'b111;
                    #10 $displayb(a, " -> ", b);
                    #10 a = 3'b000;
                    #10 $displayb(a, " -> ", b);
                    #10 a = 3'bxxx;
                    #10 $displayb(a, " -> ", b);
                    #10 a = 3'b101;
                    #10 $displayb(a, " -> ", b);
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  initial $system("mv design.v adder.v");
                endmodule"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause21() {
        test!(
            many1(module_item),
            r##"module disp;
                  initial begin
                    $display("\\\t\\\n\"\123");
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module disp;
                  logic [31:0] rval;
                  pulldown (pd);
                  initial begin
                    rval = 101;
                    $display("rval = %h hex %d decimal",rval,rval);
                    $display("rval = %o octal\nrval = %b bin",rval,rval);
                    $display("rval has %c ascii character value",rval);
                    $display("pd strength value is %v",pd);
                    $display("current scope is %m");
                    $display("%s is ascii value for 101",101);
                    $display("simulation time is %t", $time);
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module printval;
                  logic [11:0] r1;
                  initial begin
                    r1 = 10;
                    $display( "Printing with maximum size - :%d: :%h:", r1,r1 );
                    $display( "Printing with minimum size - :%0d: :%0h:", r1,r1 );
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"always
                  #15 $display($time,,"group=%b signals=%v %v %v",{s1,s2,s3},s1,s2,s3);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  typedef enum {ON, OFF} switch_e;
                  typedef struct {switch_e sw; string s;} pair_t;
                  pair_t va[int] = '{10:'{OFF, "switch10"}, 20:'{ON, "switch20"}};

                  initial begin
                    $display("va[int] = %p;",va);
                    $display("va[int] = %0p;",va);
                    $display("va[10].s = %p;", va[10].s);
                  end
                endmodule : top"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  forever @(negedge clock)
                    $strobe ("At time %d, data is %h",$time,data);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"integer
                  messages, broadcast,
                  cpu_chann, alu_chann, mem_chann;
                initial begin
                  cpu_chann = $fopen("cpu.dat");
                  if (cpu_chann == 0) $finish;
                  alu_chann = $fopen("alu.dat");
                  if (alu_chann == 0) $finish;
                  mem_chann = $fopen("mem.dat");
                  if (mem_chann == 0) $finish;
                  messages = cpu_chann | alu_chann | mem_chann;
                  // broadcast includes standard output
                  broadcast = 1 | messages;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  integer c;
                  c = $fgetc ( fd );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  integer code;
                  code = $ungetc ( c, fd );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  integer code;
                  code = $fgets ( str, fd );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  integer code ;
                  code = $fscanf ( fd, format, args );
                  code = $sscanf ( str, format, args );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  integer code ;
                  code = $fread( integral_var, fd);
                  code = $fread( mem, fd);
                  code = $fread( mem, fd, start);
                  code = $fread( mem, fd, start, count);
                  code = $fread( mem, fd, , count);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  integer pos ;
                  pos = $ftell ( fd );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  integer code ;
                  code = $fseek ( fd, offset, operation );
                  code = $rewind ( fd );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  $fflush ( mcd );
                  $fflush ( fd );
                  $fflush ( );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  integer errno ;
                  errno = $ferror ( fd, str );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  integer code;
                  code = $feof ( fd );
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial $readmemh("mem.data", mem);
                initial $readmemh("mem.data", mem, 16);
                initial $readmemh("mem.data", mem, 128, 1);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  if ($test$plusargs("HELLO")) $display("Hello argument found.");
                  if ($test$plusargs("HE")) $display("The HE subset string is detected.");
                  if ($test$plusargs("H")) $display("Argument starting with H found.");
                  if ($test$plusargs("HELLO_HERE")) $display("Long argument.");
                  if ($test$plusargs("HI")) $display("Simple greeting.");
                  if ($test$plusargs("LO")) $display("Does not match.");
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module goodtasks;
                  STRING str;
                  integer i1;
                  logic [31:0] vect;
                  real realvar;

                  initial
                    begin
                      if ($value$plusargs("TEST=%d", i1))
                        $display("value was %d", i1);
                      else
                        $display("+TEST= not found");
                      #100 $finish;
                    end
                endmodule

                module ieee1364_example;
                  real frequency;
                  logic [8*32:1] testname;
                  logic [64*8:1] pstring;
                  logic clk;

                  initial
                    begin
                      if ($value$plusargs("TESTNAME=%s",testname))
                        begin
                          $display(" TESTNAME= %s.",testname);
                          $finish;
                        end

                      if (!($value$plusargs("FREQ+%0F",frequency)))
                        frequency = 8.33333; // 166 MHz
                      $display("frequency = %f",frequency);

                      pstring = "TEST%d";
                      if ($value$plusargs(pstring, testname))
                        $display("Running test number %0d.",testname);
                    end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial $dumpfile ("module1.dump") ;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  $dumpvars (1, top);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  $dumpvars (0, top.mod1, top.mod2.net1);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  #10 $dumpvars();

                  #200 $dumpoff;

                  #800 $dumpon;

                  #900 $dumpoff;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  $dumpvars ;
                  $dumpflush ;
                  //$(applications program) ;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module dump;
                  event do_dump;
                  initial $dumpfile("verilog.dump");
                  initial @do_dump
                    $dumpvars; //dump variables in the design

                  always @do_dump //to begin the dump at event do_dump
                    begin
                      $dumpon; //no effect the first time through
                      repeat (500) @(posedge clock); //dump for 500 cycles
                      $dumpoff; //stop the dump
                    end

                  initial @(do_dump)
                    forever #10000 $dumpall; // checkpoint all variables
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module test_device(count_out, carry, data, reset);
                  output count_out, carry ;
                  input [0:3] data;
                  input reset;
                  initial
                    begin
                      $dumpports(testbench.DUT, "testoutput.vcd");
                    end
                endmodule"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause22() {
        test!(
            source_text,
            r##"`define D(x,y) initial $display("start", x , y, "end");"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"`define MACRO1(a=5,b="B",c) $display(a,,b,,c);
                `define MACRO2(a=5, b, c="C") $display(a,,b,,c);
                `define MACRO3(a=5, b=0, c="C") $display(a,,b,,c);"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"`define wordsize 8
                `define var_nand(dly) nand #dly"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"`define max(a,b)((a) > (b) ? (a) : (b))"##,
            Ok((_, _))
        );
        test!(source_text, r##"`define TOP(a,b) a + b"##, Ok((_, _)));
        test!(
            source_text,
            r##"`define msg(x,y) `"x: `\`"y`\`"`""##,
            Ok((_, _))
        );
        test!(source_text, r##"`define append(f) f``_master"##, Ok((_, _)));
        test!(
            source_text,
            r##"`define home(filename) `"/home/mydir/filename`""##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"module and_op (a, b, c);
                  output a;
                  input b, c;

                  `ifdef behavioral
                    wire a = b & c;
                  `else
                    and a1 (a,b,c);
                  `endif
                endmodule"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"module test(out);
                  output out;
                  `define wow
                  `define nest_one
                  `define second_nest
                  `define nest_two
                  `ifdef wow
                    initial $display("wow is defined");
                    `ifdef nest_one
                      initial $display("nest_one is defined");
                      `ifdef nest_two
                        initial $display("nest_two is defined");
                      `else
                        initial $display("nest_two is not defined");
                      `endif
                    `else
                      initial $display("nest_one is not defined");
                    `endif
                  `else
                    initial $display("wow is not defined");
                    `ifdef second_nest
                      initial $display("second_nest is defined");
                    `else
                      initial $display("second_nest is not defined");
                    `endif
                  `endif
                endmodule"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"module test;
                  `ifdef first_block
                    `ifndef second_nest
                      initial $display("first_block is defined");
                    `else
                      initial $display("first_block and second_nest defined");
                    `endif
                  `elsif second_block
                    initial $display("second_block defined, first_block is not");
                  `else
                    `ifndef last_result
                      initial $display("first_block, second_block,",
                        " last_result not defined.");
                    `elsif real_last
                      initial $display("first_block, second_block not defined,",
                        " last_result and real_last defined.");
                    `else
                      initial $display("Only last_result defined!");
                    `endif
                  `endif
                endmodule"##,
            Ok((_, _))
        );
        test!(source_text, r##"`timescale 1 ns / 1 ps"##, Ok((_, _)));
        test!(source_text, r##"`timescale 10 us / 100 ns"##, Ok((_, _)));
        test!(
            source_text,
            r##"`timescale 10 ns / 1 ns
                module test;
                  logic set;
                  parameter d = 1.55;

                  initial begin
                    #d set = 0;
                    #d set = 1;
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"`line 3 "orig.v" 2
                // This line is line 3 of orig.v after exiting include file"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"`begin_keywords "1364-2001" // use IEEE Std 1364-2001 Verilog keywords
                module m2;
                  reg [63:0] logic; // OK: "logic" is not a keyword in 1364-2001
                endmodule
                `end_keywords"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"`begin_keywords "1800-2005" // use IEEE Std 1800-2005 SystemVerilog keywords
                module m2;
                  reg [63:0] logic; // ERROR: "logic" is a keyword in 1800-2005
                endmodule
                `end_keywords"##,
            Err(_)
        );
        test!(
            source_text,
            r##"`begin_keywords "1800-2005" // use IEEE Std 1800-2005 SystemVerilog keywords
                interface if1;
                endinterface
                `end_keywords"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause23() {
        test!(
            many1(module_item),
            r##"typedef struct {
                  bit isfloat;
                  union { int i; shortreal f; } n;
                } tagged_st; // named structure

                module mh1 (input var int in1,
                            input var shortreal in2,
                            output tagged_st out);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module test(a,b,c,d,e,f,g,h);
                  input [7:0] a;         // no explicit net declaration - net is unsigned
                  input [7:0] b;
                  input signed [7:0] c;
                  input signed [7:0] d;  // no explicit net declaration - net is signed
                  output [7:0] e;        // no explicit net declaration - net is unsigned
                  output [7:0] f;
                  output signed [7:0] g;
                  output signed [7:0] h; // no explicit net declaration - net is signed

                  wire signed [7:0] b; // port b inherits signed attribute from net decl.
                  wire [7:0] c;        // net c inherits signed attribute from port
                  logic signed [7:0] f;// port f inherits signed attribute from logic decl.
                  logic [7:0] g;       // logic g inherits signed attribute from port
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module complex_ports ( {c,d}, .e(f) );
                  // Nets {c,d} receive the first port bits.
                  // Name 'f' is declared inside the module.
                  // Name 'e' is defined outside the module.
                  // Cannot use named port connections of first port
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module split_ports (a[7:4], a[3:0]);
                  // First port is upper 4 bits of 'a'.
                  // Second port is lower 4 bits of 'a'.
                  // Cannot use named port connections because
                  // of part-select port 'a'.
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module same_port (.a(i), .b(i));
                  // Name 'i' is declared inside the module as an inout port.
                  // Names 'a' and 'b' are defined for port connections.
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module renamed_concat (.a({b,c}), f, .g(h[1]));
                  // Names 'b', 'c', 'f', 'h' are defined inside the module.
                  // Names 'a', 'f', 'g' are defined for port connections.
                  // Can use named port connections.
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module same_input (a,a);
                  input a; // This is legal. The inputs are tied together.
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module mixed_direction (.p({a, e}));
                  input a; // p contains both input and output directions.
                  output e;
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module test (
                  input [7:0] a,
                  input signed [7:0] b, c, d, // Multiple ports that share all
                                              // attributes can be declared together.
                  output [7:0] e,             // Every attribute of the declaration
                                              // must be in the one declaration.
                  output var signed [7:0] f, g,
                  output signed [7:0] h) ;

                  // It is illegal to redeclare any ports of
                  // the module in the body of the module.
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module cpuMod(interface d, interface j);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module mymod (
                  output .P1(r[3:0]),
                  output .P2(r[7:4]),
                  ref .Y(x),
                  input R );
                  logic [7:0] r;
                  int x;
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module mh_nonansi(x, y);
                  input wire x;
                  output tri0 y;
                endmodule

                module mh0 (wire x); endmodule               // inout wire logic x

                module mh1 (integer x); endmodule            // inout wire integer x

                module mh2 (inout integer x); endmodule      // inout wire integer x

                module mh3 ([5:0] x); endmodule              // inout wire logic [5:0] x

                module mh4 (var x); endmodule                // ERROR: direction defaults to inout,
                                                             // which cannot be var

                module mh5 (input x); endmodule              // input wire logic x

                module mh6 (input var x); endmodule          // input var logic x

                module mh7 (input var integer x); endmodule  // input var integer x

                module mh8 (output x); endmodule             // output wire logic x

                module mh9 (output var x); endmodule         // output var logic x

                module mh10(output signed [5:0] x); endmodule// output wire logic signed [5:0] x

                module mh11(output integer x); endmodule     // output var integer x

                module mh12(ref [5:0] x); endmodule          // ref var logic [5:0] x

                module mh13(ref x [5:0]); endmodule          // ref var logic x [5:0]"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module mh14(wire x, y[7:0]); endmodule              // inout wire logic x
                                                                    // inout wire logic y[7:0]

                module mh15(integer x, signed [5:0] y); endmodule   // inout wire integer x
                                                                    // inout wire logic signed [5:0] y

                module mh16([5:0] x, wire y); endmodule             // inout wire logic [5:0] x
                                                                    // inout wire logic y

                module mh17(input var integer x, wire y); endmodule // input var integer x
                                                                    // input wire logic y

                module mh18(output var x, input y); endmodule       // output var logic x
                                                                    // input wire logic y

                module mh19(output signed [5:0] x, integer y); endmodule
                                                                    // output wire logic signed [5:0] x
                                                                    // output var integer y

                module mh20(ref [5:0] x, y); endmodule              // ref var logic [5:0] x
                                                                    // ref var logic [5:0] y

                module mh21(ref x [5:0], y); endmodule              // ref var logic x [5:0]
                                                                    // ref var logic y"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module mh22 (input wire integer p_a, .p_b(s_b), p_c);
                  logic [5:0] s_b;
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"parameter logic [7:0] My_DataIn = 8'hFF;

                module bus_conn (
                  output logic [7:0] dataout,
                  input [7:0] datain = My_DataIn);
                  assign dataout = datain;
                endmodule

                module bus_connect1 (
                  output logic [31:0] dataout,
                  input [ 7:0] datain);
                  parameter logic [7:0] My_DataIn = 8'h00;

                  bus_conn bconn0 (dataout[31:24], 8'h0F);
                    // Constant literal overrides default in bus_conn definition

                  bus_conn bconn1 (dataout[23:16]);
                    // Omitted port for datain, default parameter value 8'hFF in
                    // bus_conn used

                  bus_conn bconn2 (dataout[15:8], My_DataIn);
                    // The parameter value 8'h00 from the instantiating scope is used

                  bus_conn bconn3 (dataout[7:0]);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module generic_fifo (clk, read, write, reset, out, full, empty );
                  parameter MSB=3, LSB=0, DEPTH=4; // these parameters can be redefined
                  input [MSB:LSB] in;
                  input clk, read, write, reset;
                  output [MSB:LSB] out;
                  output full, empty;
                  wire [MSB:LSB] in;
                  wire clk, read, write, reset;
                  logic [MSB:LSB] out;
                  logic full, empty;
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module generic_fifo
                #(parameter MSB=3, LSB=0, DEPTH=4) // these parameters can be redefined
                  (input wire [MSB:LSB] in,
                   input wire clk, read, write, reset,
                   output logic [MSB:LSB] out,
                   output logic full, empty );
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module generic_decoder
                  #(num_code_bits = 3, localparam num_out_bits = 1 << num_code_bits)
                   (input [num_code_bits-1:0] A, output reg [num_out_bits-1:0] Y);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"parameter logic [7:0] My_DataIn = 8'hFF;

                module alu (
                  output reg [7:0] alu_out,
                  output reg zero,
                  input [7:0] ain, bin,
                  input [2:0] opcode);
                  // RTL code for the alu module
                endmodule

                module accum (
                  output reg [7:0] dataout,
                  input [7:0] datain = My_DataIn,
                  input clk, rst_n = 1'b1);
                  // RTL code for the accumulator module
                endmodule

                module xtend (
                  output reg [7:0] dout,
                  input din,
                  input clk, rst = 1'b0 );
                  // RTL code for the sign-extension module
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module alu_accum1 (
                  output [15:0] dataout,
                  input [7:0] ain, bin,
                  input [2:0] opcode,
                  input clk, rst_n, rst);
                  wire [7:0] alu_out;

                  alu alu (alu_out, , ain, bin, opcode); // zero output is unconnected

                  accum accum (dataout[7:0], alu_out, clk, rst_n);
                  xtend xtend (dataout[15:8], alu_out[7], clk); // rst gets default
                                                                // value 1'b0
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module alu_accum2 (
                  output [15:0] dataout,
                  input [7:0] ain, bin,
                  input [2:0] opcode,
                  input clk, rst_n, rst);
                  wire [7:0] alu_out;

                  alu alu (.alu_out(alu_out), .zero(),
                           .ain(ain), .bin(bin), .opcode(opcode));
                    // zero output is unconnected

                  accum accum (.dataout(dataout[7:0]), .datain(alu_out),
                               .clk(clk));
                    // rst_n is not in the port list and so gets default value 1'b1

                  xtend xtend (.dout(dataout[15:8]), .din(alu_out[7]),
                               .clk(clk), .rst() );
                    // rst has a default value, but has an empty port connection,
                    // therefore it is left unconnected
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module test;
                  A ia ( .i (a), .i (b), // illegal connection of input port twice
                         .o (c), .o (d), // illegal connection of output port twice
                         .e (e), .e (f)); // illegal connection of inout port twice
                endmodule

                module A (input i, output o, inout e);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module alu_accum3 (
                  output [15:0] dataout,
                  input [7:0] ain, bin,
                  input [2:0] opcode,
                  input clk, rst_n);
                  wire [7:0] alu_out;

                  alu alu (.alu_out, .zero(), .ain, .bin, .opcode);
                  accum accum (.dataout(dataout[7:0]), .datain(alu_out), .clk, .rst_n());
                  xtend xtend (.dout(dataout[15:8]), .din(alu_out[7]), .clk, .rst);
                    // Error: rst does not exist in the instantiation module
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module alu_accum4 (
                  output [15:0] dataout,
                  input [7:0] ain, bin,
                  input [2:0] opcode,
                  input clk);
                  wire [7:0] alu_out;

                  alu alu (.*, .zero());
                  accum accum (.*, .dataout(dataout[7:0]), .datain(alu_out));
                  xtend xtend (.*, .dout(dataout[15:8]), .din(alu_out[7]));
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module alu_accum5 (
                  output [15:0] dataout,
                  input [7:0] ain, bin,
                  input [2:0] opcode,
                  input clk, rst_n);
                  wire [7:0] alu_out;

                  // mixture of named port connections and
                  // implicit .name port connections
                  alu alu (.ain(ain), .bin(bin), .alu_out, .zero(), .opcode);

                  // positional port connections
                  accum accum (dataout[7:0], alu_out, clk, rst_n);

                  // mixture of named port connections and implicit .* port connections
                  xtend xtend (.dout(dataout[15:8]), .*, .din(alu_out[7]));
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module child(output o, input i[5]);
                  //...
                endmodule : child

                module parent(output o[8][4],
                              input i[8][4][5] );
                              child c[8][4](o,i);
                  //...
                endmodule : parent"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module MxN_pipeline #(M=3,N=4)
                  (input [M-1:0] in, output [M-1:0] out, input clk);
                  typedef logic T [M-1:0][1:N];
                  T Ins, Outs;

                  DFF dff[M-1:0][1:N](Outs, Ins, clk);

                  for (genvar I = M-1; I >= 0; I--) begin
                    for (genvar J = 1; J <= N; J++) begin
                      case (J)
                        1: begin
                             assign out[I] = Outs[I][1];
                             assign Ins[I][J] = Outs[I][2];
                           end
                        default: assign Ins[I][J] = Outs[I][J+1];
                              N: assign Ins[I][N] = in[I];
                      endcase
                    end
                  end
                endmodule : MxN_pipeline"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module netlist;
                  interconnect iwire;
                  dut1 child1(iwire);
                  dut2 child2(iwire);
                endmodule

                module dut1(inout wire w);
                  assign w = 1;
                endmodule

                module dut2(inout wand w);
                  assign w = 0;
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module dff_flat(input d, ck, pr, clr, output q, nq);
                  wire q1, nq1, q2, nq2;

                  nand g1b (nq1, d, clr, q1);
                  nand g1a (q1, ck, nq2, nq1);

                  nand g2b (nq2, ck, clr, q2);
                  nand g2a (q2, nq1, pr, nq2);

                  nand g3a (q, nq2, clr, nq);
                  nand g3b (nq, q1, pr, q);
                endmodule

                // This example shows how the flip-flop can be structured into 3 RS latches.
                module dff_nested(input d, ck, pr, clr, output q, nq);
                  wire q1, nq1, nq2;

                  module ff1;
                    nand g1b (nq1, d, clr, q1);
                    nand g1a (q1, ck, nq2, nq1);
                  endmodule
                  ff1 i1();

                  module ff2;
                    wire q2; // This wire can be encapsulated in ff2
                    nand g2b (nq2, ck, clr, q2);
                    nand g2a (q2, nq1, pr, nq2);
                  endmodule
                  ff2 i2();

                  module ff3;
                    nand g3a (q, nq2, clr, nq);
                    nand g3b (nq, q1, pr, q);
                  endmodule
                  ff3 i3();
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module part1();
                  module and2(input a, b, output z);
                  endmodule
                  module or2(input a, b, output z);
                  endmodule
                  and2 u1(), u2(), u3();
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"extern module m (a,b,c,d);
                extern module a #(parameter size= 8, parameter type TP = logic [7:0])
                                (input [size:0] a, output TP b);

                module top ();
                  wire [8:0] a;
                  logic [7:0] b;
                  wire c, d;
                  m mm (.*);
                  a aa (.*);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top ();
                  wire [8:0] a;
                  logic [7:0] b;
                  wire c, d;

                  m mm (a,b,c,d);
                  a aa (a,b);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"extern module m (a,b,c,d);
                extern module a #(parameter size = 8, parameter type TP = logic [7:0])
                                (input [size:0] a, output TP b);

                module m (.*);
                  input a,b,c;
                  output d;
                endmodule

                module a (.*);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m (a,b,c,d);
                  input a,b,c;
                  output d;
                endmodule

                module a #(parameter size = 8, parameter type TP = logic [7:0])
                         (input [size:0] a, output TP b);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module cct (stim1, stim2);
                  input stim1, stim2;
                  // instantiate mod
                  mod amod(stim1),
                  bmod(stim2);
                endmodule

                module mod (in);
                  input in;
                  always @(posedge in) begin : keep
                    logic hold;
                    hold = in;
                  end
                endmodule

                module wave;
                  logic stim1, stim2;
                  cct a(stim1, stim2); // instantiate cct
                  initial begin :wave1
                    #100 fork :innerwave
                      reg hold;
                    join
                    #150 begin
                      stim1 = 0;
                    end
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  fork : mod_1
                    reg x;
                    mod_2.x = 1;
                  join
                  fork : mod_2
                    reg x;
                    mod_1.x = 0;
                  join
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top();
                  logic clk, x, y, z;
                  m m_i(clk, x, y, z);
                endmodule

                module m(input logic clk, a, b, c);
                  assert #0 (a^b);     // no label, assertion cannot be referred to
                  A1: assert #0 (a^b); // assertion can be accessed in control tasks

                  initial begin : B1
                    assert (a);    // cannot be accessed in control tasks
                    A1: assert (a) // can be accessed, e.g., top.m_i.B1.A1
                      begin        // unnamed block, d cannot be accessed
                        bit d;
                        d = a ^ b;
                      end
                    else
                      begin : B2 // name required to access items in action block
                        bit d;   // d can be accessed using, e.g., top.m_i.B1.A1.B2.d
                        d = a ^ b;
                      end
                  end

                  logic e;
                  always_ff @(posedge clk) begin // unnamed block, no scope created
                    e <= a && c;
                    C1: cover property(e)        // C1 and A2 can be referred to
                      begin                      // hierarchical name top.m_i.C1.A2
                        A2: assert (m_i.B1.A1.B2.d);
                      end
                  end

                  always_ff @(posedge clk) begin // unnamed block, scope created
                    // declaration of f causes begin-end to create scope
                    static logic f;
                    f <= a && c;
                    C2: cover property(f) // C2 and A3 cannot be referred to
                      begin
                        A3: assert (m_i.B1.A1.B2.d);
                      end
                  end

                  always_ff @(posedge clk) begin : B2 // named block and scope created
                    static logic f;
                    f <= a && c;
                    C3: cover property(f) // C3 and A4 can be referred to
                      begin               // hierarchical name top.m_i.B2.C3.A4
                        A4: assert (m_i.B1.A1.B2.d);
                      end
                  end

                  assert property(@(posedge clk) a |-> b) else // unnamed assertion
                    begin: B3
                      static bit d;  // d can be referred to, e.g., top.m_i.B3.d
                      A5: assert(d); // hierarchical name top.m_i.B3.A5
                    end
                  // Any other labelled object with name B3 at the module
                  // level shall be an error
                endmodule"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"package p;
                  struct { int x; } s1;
                  struct { int x; } s2;
                  function void f();
                    int x;
                  endfunction
                endpackage

                module m;
                  import p::*;
                  if (1) begin : s1
                    initial begin
                      s1.x = 1; // dotted name 1
                      s2.x = 1; // dotted name 2
                      f.x = 1;  // dotted name 3
                      f2.x = 1; // dotted name 4
                    end
                    int x;
                    some_module s2();
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module a;
                  integer i;
                  b a_b1();
                endmodule

                module b;
                  integer i;
                  c b_c1(),
                  b_c2();
                  initial           // downward path references two copies of i:
                    #10 b_c1.i = 2; // a.a_b1.b_c1.i, d.d_b1.b_c1.i
                endmodule

                module c;
                  integer i;
                  initial begin // local name references four copies of i:
                    i = 1;      // a.a_b1.b_c1.i, a.a_b1.b_c2.i,
                                // d.d_b1.b_c1.i, d.d_b1.b_c2.i
                    b.i = 1;    // upward path references two copies of i:
                                // a.a_b1.i, d.d_b1.i
                  end
                endmodule

                module d;
                  integer i;
                  b d_b1();
                  initial begin // full path name references each copy of i
                    a.i = 1; d.i = 5;
                    a.a_b1.i = 2; d.d_b1.i = 6;
                    a.a_b1.b_c1.i = 3; d.d_b1.b_c1.i = 7;
                    a.a_b1.b_c2.i = 4; d.d_b1.b_c2.i = 8;
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task t;
                  int x;
                  x = f(1); // valid reference to function f in $unit scope
                endtask

                function int f(int y);
                  return y+1;
                endfunction"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"package p;
                  function void f();
                    $display("p::f");
                  endfunction
                endpackage

                module top;
                  import p::*;
                  if (1) begin : b // generate block
                    initial f(); // reference to “f”
                    function void f();
                      $display("top.b.f");
                    endfunction
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"task t;
                  logic s;
                  begin : b
                    logic r;
                    t.b.r = 0;// These three lines access the same variable r
                    b.r = 0;
                    r = 0;
                    t.s = 0;// These two lines access the same variable s
                    s = 0;
                  end
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module generic_fifo
                  #(MSB=3, LSB=0) // parameter port list parameters
                   (input wire [MSB:LSB] in,
                    input wire clk, read, write, reset,
                    output logic [MSB:LSB] out,
                    output logic full, empty );

                  parameter DEPTH=4; // module item parameter

                  localparam FIFO_MSB = DEPTH*MSB;
                  localparam FIFO_LSB = LSB;
                    // These constants are local, and cannot be overridden.
                    // They can be affected by altering the value parameters above

                  logic [FIFO_MSB:FIFO_LSB] fifo;
                  logic [LOG2(DEPTH):0] depth;

                  always @(posedge clk or posedge reset) begin
                    //casez ({read,write,reset})
                    //  // implementation of fifo
                    //endcase
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m1 (a,b);
                  real r1,r2;
                  parameter [2:0] A = 3'h2;
                  parameter B = 3'h2;
                  initial begin
                    r1 = A;
                    r2 = B;
                    $display("r1 is %f r2 is %f",r1,r2);
                  end
                endmodule: m1

                module m2;
                  wire a,b;
                  defparam f1.A = 3.1415;
                  defparam f1.B = 3.1415;
                  m1 f1(a,b);
                endmodule: m2"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"genvar i;

                generate
                  for (i = 0; i < 8; i = i + 1) begin : somename
                    flop my_flop(in[i], in1[i], out1[i]);
                    defparam somename[i+1].my_flop.xyz = i ;
                  end
                endgenerate"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  logic clk;
                  logic [0:4] in1;
                  logic [0:9] in2;
                  wire [0:4] o1;
                  wire [0:9] o2;

                  vdff m1 (o1, in1, clk);
                  vdff m2 (o2, in2, clk);
                endmodule

                module vdff (out, in, clk);
                  parameter size = 1, delay = 1;
                  input [0:size-1] in;
                  input clk;
                  output [0:size-1] out;
                  logic [0:size-1] out;

                  always @(posedge clk)
                    # delay out = in;
                endmodule

                module annotate;
                  defparam
                    top.m1.size = 5,
                    top.m1.delay = 10,
                    top.m2.size = 10,
                    top.m2.delay = 20;
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module tb1;
                  wire [9:0] out_a, out_d;
                  wire [4:0] out_b, out_c;
                  logic [9:0] in_a, in_d;
                  logic [4:0] in_b, in_c;
                  logic clk;

                  // testbench clock & stimulus generation code ...

                  // Four instances of vdff with parameter value assignment by ordered list

                  // mod_a has new parameter values size=10 and delay=15
                  // mod_b has default parameters (size=5, delay=1)
                  // mod_c has one default size=5 and one new delay=12
                  //   In order to change the value of delay,
                  //   it is necessary to specify the (default) value of size as well.
                  // mod_d has a new parameter value size=10.
                  //   delay retains its default value

                  vdff #(10,15) mod_a (.out(out_a), .in(in_a), .clk(clk));
                  vdff mod_b (.out(out_b), .in(in_b), .clk(clk));
                  vdff #( 5,12) mod_c (.out(out_c), .in(in_c), .clk(clk));
                  vdff #(10) mod_d (.out(out_d), .in(in_d), .clk(clk));
                endmodule

                module vdff (out, in, clk);
                  parameter size=5, delay=1;
                  output [size-1:0] out;
                  input [size-1:0] in;
                  input clk;
                  logic [size-1:0] out;

                  always @(posedge clk)
                    #delay out = in;
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module my_mem (addr, data);
                  parameter addr_width = 16;
                  localparam mem_size = 1 << addr_width;
                  parameter data_width = 8;
                endmodule

                module top;
                  my_mem #(12, 16) m(addr,data);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module tb2;
                  wire [9:0] out_a, out_d;
                  wire [4:0] out_b, out_c;
                  logic [9:0] in_a, in_d;
                  logic [4:0] in_b, in_c;
                  logic clk;

                  // testbench clock & stimulus generation code ...

                  // Four instances of vdff with parameter value assignment by name

                  // mod_a has new parameter values size=10 and delay=15
                  // mod_b has default parameters (size=5, delay=1)
                  // mod_c has one default size=5 and one new delay=12
                  // mod_d has a new parameter value size=10.
                  //   delay retains its default value

                  vdff #(.size(10),.delay(15)) mod_a (.out(out_a),.in(in_a),.clk(clk));
                  vdff mod_b (.out(out_b),.in(in_b),.clk(clk));
                  vdff #(.delay(12)) mod_c (.out(out_c),.in(in_c),.clk(clk));
                  vdff #(.delay( ),.size(10) ) mod_d (.out(out_d),.in(in_d),.clk(clk));
                endmodule

                module vdff (out, in, clk);
                  parameter size=5, delay=1;
                  output [size-1:0] out;
                  input [size-1:0] in;
                  input clk;
                  logic [size-1:0] out;

                  always @(posedge clk)
                    #delay out = in;
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module tb3;

                  // declarations & code

                  // legal mixture of instance with positional parameters and
                  // another instance with named parameters

                  vdff #(10, 15) mod_a (.out(out_a), .in(in_a), .clk(clk));
                  vdff mod_b (.out(out_b), .in(in_b), .clk(clk));
                  vdff #(.delay(12)) mod_c (.out(out_c), .in(in_c), .clk(clk));
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"parameter
                  word_size = 32,
                  memory_size = word_size * 4096;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"parameter p = 1;
                parameter [p:0] p2 = 4;
                parameter type T = int;
                parameter T p3 = 7;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"class C ;
                endclass

                module M #( type T = C, T p = 4,
                            type T2, T2 p2 = 4
                          ) () ;
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m;
                  m1 n();
                endmodule

                module m1;
                  parameter p = 2;

                  defparam m.n.p = 1;
                  initial $display(m.n.p);

                  generate
                    if (p == 1) begin : m
                      m2 n();
                    end
                  endgenerate
                endmodule

                module m2;
                  parameter p = 3;
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bind cpu fpu_props fpu_rules_1(a,b,c);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bind cpu: cpu1 fpu_props fpu_rules_1(a, b, c);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bind cpu: cpu1, cpu2, cpu3 fpu_props fpu_rules_1(a, b, c);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface range (input clk, enable, input var int minval, expr);
                  property crange_en;
                    @(posedge clk) enable |-> (minval <= expr);
                  endproperty
                  range_chk: assert property (crange_en);
                endinterface

                bind cr_unit range r1(c_clk,c_en,v_low,(in1&&in2));"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bind targetmod
                mycheck #(.param1(const4), .param2(8'h44))
                i_mycheck(.*, .p1(f1({v1, 1'b0, b1.c}, v2 & v3)), .p2(top.v4));"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause24() {
        test!(
            many1(module_item),
            r##"program test (input clk, input [16:1] addr, inout [7:0] data);
                endprogram"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"program test ( interface device_ifc );
                endprogram"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module test;
                  int shared; // variable shared by programs p1 and p1
                  program p1;
                  endprogram
                  program p2;
                  endprogram // p1 and p2 are implicitly instantiated once in module test
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m;
                  logic r;
                  wire dw1, dw2;

                  initial begin
                    r = 0;
                    #10 r = 1;
                  end

                  assign dw1 = r;

                  p p_i(dw2, dw1);

                  always @(dw2)
                    $display("dw2 is %b", dw2);
                endmodule

                program p(output pw2, input pw1);
                  assign pw2 = pw1;
                endprogram"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m;
                  task T;
                    S1: a = b; // executes in reactive region set if called from a program
                    #5;
                    S2: b <= 1'b1; // executes in reactive region set if called from a program
                  endtask
                endmodule"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause25() {
        test!(
            many1(module_item),
            r##"myinterface #(100) scalar1(), vector[9:0]();"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module memMod( input  logic req,
                                      logic clk,
                                      logic start,
                                      logic [1:0] mode,
                                      logic [7:0] addr,
                               inout  wire [7:0] data,
                               output bit gnt,
                                      bit rdy );
                  logic avail;
                endmodule

                module cpuMod(
                  input  logic clk,
                         logic gnt,
                         logic rdy,
                  inout  wire [7:0] data,
                  output logic req,
                         logic start,
                         logic [7:0] addr,
                         logic [1:0] mode );
                endmodule

                module top;
                  logic req, gnt, start, rdy;
                  logic clk = 0;
                  logic [1:0] mode;
                  logic [7:0] addr;
                  wire [7:0] data;

                  memMod mem(req, clk, start, mode, addr, data, gnt, rdy);
                  cpuMod cpu(clk, gnt, rdy, data, req, start, addr, mode);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface simple_bus; // Define the interface
                  logic req, gnt;
                  logic [7:0] addr, data;
                  logic [1:0] mode;
                  logic start, rdy;
                endinterface: simple_bus

                module memMod(simple_bus a, // Access the simple_bus interface
                              input logic clk);
                  logic avail;
                  // When memMod is instantiated in module top, a.req is the req
                  // signal in the sb_intf instance of the 'simple_bus' interface
                  always @(posedge clk) a.gnt <= a.req & avail;
                endmodule

                module cpuMod(simple_bus b, input logic clk);
                endmodule

                module top;
                  logic clk = 0;
                  simple_bus sb_intf(); // Instantiate the interface
                  memMod mem(sb_intf, clk); // Connect the interface to the module instance
                  cpuMod cpu(.b(sb_intf), .clk(clk)); // Either by position or by name
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module memMod (simple_bus sb_intf, input logic clk);
                endmodule

                module cpuMod (simple_bus sb_intf, input logic clk);
                endmodule

                module top;
                  logic clk = 0;

                  simple_bus sb_intf();

                  memMod mem (.*); // implicit port connections
                  cpuMod cpu (.*); // implicit port connections
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module memMod (interface a, input logic clk);
                endmodule

                module cpuMod(interface b, input logic clk);
                endmodule

                interface simple_bus; // Define the interface
                  logic req, gnt;
                  logic [7:0] addr, data;
                  logic [1:0] mode;
                  logic start, rdy;
                endinterface: simple_bus

                module top;
                  logic clk = 0;

                  simple_bus sb_intf(); // Instantiate the interface

                  // Reference the sb_intf instance of the simple_bus
                  // interface from the generic interfaces of the
                  // memMod and cpuMod modules
                  memMod mem (.a(sb_intf), .clk(clk));
                  cpuMod cpu (.b(sb_intf), .clk(clk));
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module memMod (interface a, input logic clk);
                endmodule

                module cpuMod (interface b, input logic clk);
                endmodule

                module top;
                  logic clk = 0;

                  simple_bus sb_intf();

                  memMod mem (.*, .a(sb_intf)); // partial implicit port connections
                  cpuMod cpu (.*, .b(sb_intf)); // partial implicit port connections
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface i1 (input a, output b, inout c);
                  wire d;
                endinterface"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface simple_bus (input logic clk); // Define the interface
                  logic req, gnt;
                  logic [7:0] addr, data;
                  logic [1:0] mode;
                  logic start, rdy;
                endinterface: simple_bus

                module memMod(simple_bus a); // Uses just the interface
                  logic avail;
                  always @(posedge a.clk)    // the clk signal from the interface
                    a.gnt <= a.req & avail;  // a.req is in the 'simple_bus' interface
                endmodule

                module cpuMod(simple_bus b);
                endmodule

                module top;
                  logic clk = 0;

                  simple_bus sb_intf1(clk);  // Instantiate the interface
                  simple_bus sb_intf2(clk);  // Instantiate the interface

                  memMod mem1(.a(sb_intf1)); // Reference simple_bus 1 to memory 1
                  cpuMod cpu1(.b(sb_intf1));
                  memMod mem2(.a(sb_intf2)); // Reference simple_bus 2 to memory 2
                  cpuMod cpu2(.b(sb_intf2));
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface i2;
                  wire a, b, c, d;
                  modport master (input a, b, output c, d);
                  modport slave (output a, b, input c, d);
                endinterface"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m (i2.master i);
                endmodule

                module s (i2.slave i);
                endmodule

                module top;
                  i2 i();
                  m u1(.i(i));
                  s u2(.i(i));
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m (i2 i);
                endmodule

                module s (i2 i);
                endmodule

                module top;
                  i2 i();
                  m u1(.i(i.master));
                  s u2(.i(i.slave));
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface i;
                  wire x, y;
                  interface illegal_i;
                    wire a, b, c, d;
                    // x, y not declared by this interface
                    modport master(input a, b, x, output c, d, y);
                    modport slave(output a, b, x, input c, d, y);
                  endinterface : illegal_i
                endinterface : i

                interface illegal_i;
                  // a, b, c, d not declared by this interface
                  modport master(input a, b, output c, d);
                  modport slave(output a, b, input c, d);
                endinterface : illegal_i"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface simple_bus (input logic clk); // Define the interface
                  logic req, gnt;
                  logic [7:0] addr, data;
                  logic [1:0] mode;
                  logic start, rdy;
                  modport slave (input req, addr, mode, start, clk,
                                 output gnt, rdy,
                                 ref data);
                  modport master(input gnt, rdy, clk,
                                 output req, addr, mode, start,
                                 ref data);
                endinterface: simple_bus

                module memMod (simple_bus.slave a); // interface name and modport name
                  logic avail;
                  always @(posedge a.clk) // the clk signal from the interface
                    a.gnt <= a.req & avail; // the gnt and req signal in the interface
                endmodule

                module cpuMod (simple_bus.master b);
                endmodule

                module top;
                  logic clk = 0;

                  simple_bus sb_intf(clk); // Instantiate the interface

                  initial repeat(10) #10 clk++;

                  memMod mem(.a(sb_intf)); // Connect the interface to the module instance
                  cpuMod cpu(.b(sb_intf));
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface simple_bus (input logic clk); // Define the interface
                  logic req, gnt;
                  logic [7:0] addr, data;
                  logic [1:0] mode;
                  logic start, rdy;
                  modport slave (input req, addr, mode, start, clk,
                                 output gnt, rdy,
                                 ref data);
                  modport master(input gnt, rdy, clk,
                                 output req, addr, mode, start,
                                 ref data);
                endinterface: simple_bus

                module memMod(simple_bus a); // Uses just the interface name
                  logic avail;
                  always @(posedge a.clk) // the clk signal from the interface
                    a.gnt <= a.req & avail; // the gnt and req signal in the interface
                endmodule

                module cpuMod(simple_bus b);
                endmodule

                module top;
                  logic clk = 0;

                  simple_bus sb_intf(clk); // Instantiate the interface

                  initial repeat(10) #10 clk++;

                  memMod mem(sb_intf.slave); // Connect the modport to the module instance
                  cpuMod cpu(sb_intf.master);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface simple_bus (input logic clk); // Define the interface
                  logic req, gnt;
                  logic [7:0] addr, data;
                  logic [1:0] mode;
                  logic start, rdy;
                  modport slave (input req, addr, mode, start, clk,
                                 output gnt, rdy,
                                 ref data);
                  modport master(input gnt, rdy, clk,
                                 output req, addr, mode, start,
                                 ref data);
                endinterface: simple_bus

                module memMod(interface a); // Uses just the interface
                  logic avail;
                  always @(posedge a.clk) // the clk signal from the interface
                    a.gnt <= a.req & avail; // the gnt and req signal in the interface
                endmodule

                module cpuMod(interface b);
                endmodule

                module top;
                  logic clk = 0;

                  simple_bus sb_intf(clk); // Instantiate the interface

                  memMod mem(sb_intf.slave); // Connect the modport to the module instance
                  cpuMod cpu(sb_intf.master);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface I;
                  logic [7:0] r;
                  const int x=1;
                  bit R;
                  modport A (output .P(r[3:0]), input .Q(x), R);
                  modport B (output .P(r[7:4]), input .Q(2), R);
                endinterface

                module M ( interface i);
                  initial i.P = i.Q;
                endmodule

                module top;
                  I i1 ();
                  M u1 (i1.A);
                  M u2 (i1.B);
                  initial #1 $display("%b", i1.r); // displays 00100001
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface A_Bus( input logic clk );
                  wire req, gnt;
                  wire [7:0] addr, data;

                  clocking sb @(posedge clk);
                    input gnt;
                    output req, addr;
                    inout data;

                    property p1; req ##[1:3] gnt; endproperty
                  endclocking

                  modport DUT ( input clk, req, addr, // Device under test modport
                                output gnt,
                                inout data );

                  modport STB ( clocking sb ); // synchronous testbench modport

                  modport TB ( input gnt, // asynchronous testbench modport
                               output req, addr,
                               inout data );
                endinterface"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module dev1(A_Bus.DUT b); // Some device: Part of the design
                endmodule

                module dev2(A_Bus.DUT b); // Some device: Part of the design
                endmodule

                module top;
                  logic clk;
                  A_Bus b1( clk );
                  A_Bus b2( clk );
                  dev1 d1( b1 );
                  dev2 d2( b2 );
                  T tb( b1, b2 );
                endmodule

                program T (A_Bus.STB b1, A_Bus.STB b2 ); // testbench: 2 synchronous ports
                  assert property (b1.sb.p1); // assert property from within program

                  initial begin
                    b1.sb.req <= 1;
                    wait( b1.sb.gnt == 1 );
                    b1.sb.req <= 0;
                    b2.sb.req <= 1;
                    wait( b2.sb.gnt == 1 );
                    b2.sb.req <= 0;
                  end
                endprogram"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface itf;
                  logic c,q,d;
                  modport flop (input c,d, output q);
                endinterface

                module dtype (itf.flop ch);
                  always_ff @(posedge ch.c) ch.q <= ch.d;
                  specify
                    ( posedge ch.c => (ch.q+:ch.d)) = (5,6);
                    $setup( ch.d, posedge ch.c, 1 );
                  endspecify
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface simple_bus (input logic clk); // Define the interface
                  logic req, gnt;
                  logic [7:0] addr, data;
                  logic [1:0] mode;
                  logic start, rdy;

                  task masterRead(input logic [7:0] raddr); // masterRead method
                    // ...
                  endtask: masterRead

                  task slaveRead; // slaveRead method
                    // ...
                  endtask: slaveRead
                endinterface: simple_bus

                module memMod(interface a); // Uses any interface
                  logic avail;

                  always @(posedge a.clk)   // the clk signal from the interface
                    a.gnt <= a.req & avail; // the gnt and req signals in the interface

                  always @(a.start)
                    a.slaveRead;
                endmodule

                module cpuMod(interface b);
                  enum {read, write} instr;
                  logic [7:0] raddr;
                  always @(posedge b.clk)
                    if (instr == read)
                      b.masterRead(raddr); // call the Interface method
                endmodule

                module top;
                  logic clk = 0;
                  simple_bus sb_intf(clk); // Instantiate the interface
                  memMod mem(sb_intf);
                  cpuMod cpu(sb_intf);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface simple_bus (input logic clk); // Define the interface
                  logic req, gnt;
                  logic [7:0] addr, data;
                  logic [1:0] mode;
                  logic start, rdy;

                  modport slave (input req, addr, mode, start, clk,
                                 output gnt, rdy,
                                 ref data,
                                 import slaveRead,
                                        slaveWrite);
                    // import into module that uses the modport

                  modport master(input gnt, rdy, clk,
                                 output req, addr, mode, start,
                                 ref data,
                                 import masterRead,
                                        masterWrite);
                    // import into module that uses the modport

                  task masterRead(input logic [7:0] raddr); // masterRead method
                    // ...
                  endtask

                  task slaveRead; // slaveRead method
                    // ...
                  endtask

                  task masterWrite(input logic [7:0] waddr);
                    //...
                  endtask

                  task slaveWrite;
                    //...
                  endtask
                endinterface: simple_bus

                module memMod(interface a); // Uses just the interface
                  logic avail;

                  always @(posedge a.clk) // the clk signal from the interface
                    a.gnt <= a.req & avail; // the gnt and req signals in the interface

                  always @(a.start)
                    if (a.mode[0] == 1'b0)
                      a.slaveRead;
                    else
                      a.slaveWrite;
                endmodule

                module cpuMod(interface b);
                  enum {read, write} instr;
                  logic [7:0] raddr = $random();

                  always @(posedge b.clk)
                    if (instr == read)
                      b.masterRead(raddr); // call the Interface method
                    else
                      b.masterWrite(raddr);
                endmodule

                module omniMod( interface b);
                  //...
                endmodule: omniMod

                module top;
                  logic clk = 0;
                  simple_bus sb_intf(clk); // Instantiate the interface
                  memMod mem(sb_intf.slave); // only has access to the slave tasks
                  cpuMod cpu(sb_intf.master); // only has access to the master tasks
                  omniMod omni(sb_intf); // has access to all master and slave tasks
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface simple_bus (input logic clk); // Define the interface
                  logic req, gnt;
                  logic [7:0] addr, data;
                  logic [1:0] mode;
                  logic start, rdy;

                  modport slave( input req, addr, mode, start, clk,
                                 output gnt, rdy,
                                 ref data,
                                 export Read,
                                        Write);
                    // export from module that uses the modport

                  modport master(input gnt, rdy, clk,
                                 output req, addr, mode, start,
                                 ref data,
                                 import task Read(input logic [7:0] raddr),
                                        task Write(input logic [7:0] waddr));
                    // import requires the full task prototype
                endinterface: simple_bus

                module memMod(interface a); // Uses just the interface keyword
                  logic avail;

                  task a.Read; // Read method
                    avail = 0;
                    avail = 1;
                  endtask

                  task a.Write;
                    avail = 0;
                    avail = 1;
                  endtask
                endmodule

                module cpuMod(interface b);
                  enum {read, write} instr;
                  logic [7:0] raddr;

                  always @(posedge b.clk)
                    if (instr == read)
                      b.Read(raddr); // call the slave method via the interface
                    else
                      b.Write(raddr);
                endmodule

                module top;
                  logic clk = 0;
                  simple_bus sb_intf(clk); // Instantiate the interface
                  memMod mem(sb_intf.slave); // exports the Read and Write tasks
                  cpuMod cpu(sb_intf.master); // imports the Read and Write tasks
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface simple_bus (input logic clk); // Define the interface
                  logic req, gnt;
                  logic [7:0] addr, data;
                  logic [1:0] mode;
                  logic start, rdy;
                  int slaves = 0;

                  // tasks executed concurrently as a fork-join block
                  extern forkjoin task countSlaves();
                  extern forkjoin task Read (input logic [7:0] raddr);
                  extern forkjoin task Write (input logic [7:0] waddr);

                  modport slave (input req,addr, mode, start, clk,
                                 output gnt, rdy,
                                 ref data, slaves,
                                 export Read, Write, countSlaves);
                    // export from module that uses the modport

                  modport master ( input gnt, rdy, clk,
                                   output req, addr, mode, start,
                                   ref data,
                                   import task Read(input logic [7:0] raddr),
                                          task Write(input logic [7:0] waddr));
                    // import requires the full task prototype

                  initial begin
                    slaves = 0;
                    countSlaves;
                    $display ("number of slaves = %d", slaves);
                  end
                endinterface: simple_bus

                module memMod #(parameter int minaddr=0, maxaddr=0) (interface a);
                  logic avail = 1;
                  logic [7:0] mem[255:0];

                  task a.countSlaves();
                    a.slaves++;
                  endtask

                  task a.Read(input logic [7:0] raddr); // Read method
                    if (raddr >= minaddr && raddr <= maxaddr) begin
                      avail = 0;
                      #10 a.data = mem[raddr];
                      avail = 1;
                    end
                  endtask

                  task a.Write(input logic [7:0] waddr); // Write method
                    if (waddr >= minaddr && waddr <= maxaddr) begin
                      avail = 0;
                      #10 mem[waddr] = a.data;
                      avail = 1;
                    end
                  endtask
                endmodule

                module cpuMod(interface b);
                  typedef enum {read, write} instr;
                  instr inst;
                  logic [7:0] raddr;
                  integer seed;

                  always @(posedge b.clk) begin
                    inst = instr'($dist_uniform(seed, 0, 1));
                    raddr = $dist_uniform(seed, 0, 3);
                    if (inst == read) begin
                      $display("%t begin read %h @ %h", $time, b.data, raddr);
                      callr:b.Read(raddr);
                      $display("%t end read %h @ %h", $time, b.data, raddr);
                    end
                    else begin
                      $display("%t begin write %h @ %h", $time, b.data, raddr);
                      b.data = raddr;
                      callw:b.Write(raddr);
                      $display("%t end write %h @ %h", $time, b.data, raddr);
                    end
                  end
                endmodule

                module top;
                  logic clk = 0;

                  function void interrupt();
                    disable mem1.a.Read; // task via module instance
                    disable sb_intf.Write; // task via interface instance
                    if (mem1.avail == 0) $display ("mem1 was interrupted");
                    if (mem2.avail == 0) $display ("mem2 was interrupted");
                  endfunction

                  always #5 clk++;

                  initial begin
                    #28 interrupt();
                    #10 interrupt();
                    #100 $finish;
                  end

                  simple_bus sb_intf(clk);

                  memMod #(0, 127) mem1(sb_intf.slave);
                  memMod #(128, 255) mem2(sb_intf.slave);
                  cpuMod cpu(sb_intf.master);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface simple_bus #(AWIDTH = 8, DWIDTH = 8)
                                     (input logic clk); // Define the interface
                  logic req, gnt;
                  logic [AWIDTH-1:0] addr;
                  logic [DWIDTH-1:0] data;
                  logic [1:0] mode;
                  logic start, rdy;

                  modport slave( input req, addr, mode, start, clk,
                                 output gnt, rdy,
                                 ref data,
                                 import task slaveRead,
                                        task slaveWrite);
                    // import into module that uses the modport

                  modport master(input gnt, rdy, clk,
                                 output req, addr, mode, start,
                                 ref data,
                                 import task masterRead(input logic [AWIDTH-1:0] raddr),
                                        task masterWrite(input logic [AWIDTH-1:0] waddr));
                    // import requires the full task prototype

                  task masterRead(input logic [AWIDTH-1:0] raddr); // masterRead method
                  endtask

                  task slaveRead; // slaveRead method
                  endtask

                  task masterWrite(input logic [AWIDTH-1:0] waddr);
                  endtask

                  task slaveWrite;
                  endtask
                endinterface: simple_bus

                module memMod(interface a); // Uses just the interface keyword
                  logic avail;

                  always @(posedge a.clk) // the clk signal from the interface
                    a.gnt <= a.req & avail; //the gnt and req signals in the interface

                  always @(a.start)
                    if (a.mode[0] == 1'b0)
                      a.slaveRead;
                    else
                      a.slaveWrite;
                endmodule

                module cpuMod(interface b);
                  enum {read, write} instr;
                  logic [7:0] raddr;
                  always @(posedge b.clk)
                    if (instr == read)
                      b.masterRead(raddr); // call the Interface method
                    else
                      b.masterWrite(raddr);
                endmodule

                module top;
                  logic clk = 0;

                  simple_bus sb_intf(clk); // Instantiate default interface
                  simple_bus #(.DWIDTH(16)) wide_intf(clk); // Interface with 16-bit data

                  initial repeat(10) #10 clk++;

                  memMod mem(sb_intf.slave); // only has access to the slaveRead task
                  cpuMod cpu(sb_intf.master); // only has access to the masterRead task
                  memMod memW(wide_intf.slave); // 16-bit wide memory
                  cpuMod cpuW(wide_intf.master); // 16-bit wide cpu
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface SBus; // A Simple bus interface
                  logic req, grant;
                  logic [7:0] addr, data;
                endinterface

                class SBusTransactor; // SBus transactor class
                  virtual SBus bus; // virtual interface of type SBus

                  function new( virtual SBus s );
                    bus = s; // initialize the virtual interface
                  endfunction

                  task request(); // request the bus
                    bus.req <= 1'b1;
                  endtask

                  task wait_for_bus(); // wait for the bus to be granted
                    @(posedge bus.grant);
                  endtask
                endclass

                module devA( SBus s ); endmodule // devices that use SBus
                module devB( SBus s ); endmodule

                module top;
                  SBus s[1:4] (); // instantiate 4 interfaces
                  devA a1( s[1] ); // instantiate 4 devices
                  devB b1( s[2] );
                  devA a2( s[3] );
                  devB b2( s[4] );
                  initial begin
                    SBusTransactor t[1:4]; // create 4 bus-transactors and bind
                    t[1] = new( s[1] );
                    t[2] = new( s[2] );
                    t[3] = new( s[3] );
                    t[4] = new( s[4] );
                    // test t[1:4]
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface PBus #(parameter WIDTH=8); // A parameterized bus interface
                  logic req, grant;
                  logic [WIDTH-1:0] addr, data;
                  modport phy(input addr, ref data);
                endinterface

                module top;
                  PBus #(16) p16();
                  PBus #(32) p32();
                  virtual PBus v8;        // legal declaration, but no legal assignments
                  virtual PBus #(35) v35; // legal declaration, but no legal assignments
                  virtual PBus #(16) v16;
                  virtual PBus #(16).phy v16_phy;
                  virtual PBus #(32) v32;
                  virtual PBus #(32).phy v32_phy;
                  initial begin
                    v16 = p16;     // legal – parameter values match
                    v32 = p32;     // legal – parameter values match
                    v16 = p32;     // illegal – parameter values don't match
                    v16 = v32;     // illegal – parameter values don't match
                    v16_phy = v16; // legal assignment from no selected modport to
                                   // selected modport
                    v16 = v16_phy; // illegal assignment from selected modport to
                                   // no selected modport
                    v32_phy = p32; // legal assignment from no selected modport to
                                   // selected modport
                    v32 = p32.phy; // illegal assignment from selected modport to
                                   // no selected modport
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface SyncBus( input logic clk );
                  wire a, b, c;
                  clocking sb @(posedge clk);
                    input a;
                    output b;
                    inout c;
                  endclocking
                endinterface

                typedef virtual SyncBus VI; // A virtual interface type

                task do_it( VI v ); // handles any SyncBus via clocking sb
                  if( v.sb.a == 1 )
                    v.sb.b <= 0;
                  else
                    v.sb.c <= ##1 1;
                endtask"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  logic clk;

                  SyncBus b1( clk );
                  SyncBus b2( clk );

                  initial begin
                    VI v[2] = '{ b1, b2 };
                    repeat( 20 )
                      do_it( v[ $urandom_range( 0, 1 ) ] );
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface A_Bus( input logic clk );
                  wire req, gnt;
                  wire [7:0] addr, data;

                  clocking sb @(posedge clk);
                    input gnt;
                    output req, addr;
                    inout data;
                    property p1; req ##[1:3] gnt; endproperty
                  endclocking

                  modport DUT ( input clk, req, addr, // Device under test modport
                                output gnt,
                                inout data );

                  modport STB ( clocking sb ); // synchronous testbench modport

                  modport TB ( input gnt, // asynchronous testbench modport
                               output req, addr,
                               inout data );
                endinterface"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module dev1(A_Bus.DUT b); // Some device: Part of the design
                endmodule

                module dev2(A_Bus.DUT b); // Some device: Part of the design
                endmodule

                program T (A_Bus.STB b1, A_Bus.STB b2 ); // Testbench: 2 synchronous ports
                endprogram

                module top;
                  logic clk;
                  A_Bus b1( clk );
                  A_Bus b2( clk );
                  dev1 d1( b1 );
                  dev2 d2( b2 );
                  T tb( b1, b2 );
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"program T (A_Bus.STB b1, A_Bus.STB b2 ); // Testbench: 2 synchronous ports
                  typedef virtual A_Bus.STB SYNCTB;

                  task request( SYNCTB s );
                    s.sb.req <= 1;
                  endtask

                  task wait_grant( SYNCTB s );
                    wait( s.sb.gnt == 1 );
                  endtask

                  task drive(SYNCTB s, logic [7:0] adr, data );
                    if( s.sb.gnt == 0 ) begin
                      request(s); // acquire bus if needed
                      wait_grant(s);
                    end
                    s.sb.addr = adr;
                    s.sb.data = data;
                    repeat(2) @s.sb;
                    s.sb.req = 0; //release bus
                  endtask

                  assert property (b1.sb.p1); // assert property from within program

                  initial begin
                    drive( b1, $random, $random );
                    drive( b2, $random, $random );
                  end
                endprogram"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"interface ebus_i;
                  integer I; // reference to I not allowed through modport mp
                  typedef enum {Y,N} choice;
                  choice Q;
                  localparam True = 1;
                  modport mp(input Q);
                endinterface

                module Top;
                  ebus_i ebus ();
                  sub s1 (ebus.mp);
                endmodule

                module sub(interface.mp i);
                  typedef i.choice yes_no; // import type from interface
                  yes_no P;
                  assign P = i.Q;          // refer to Q with a port reference
                  initial
                    Top.ebus.Q = i.True;   // refer to Q with a hierarchical reference
                  initial
                    Top.ebus.I = 0;        // referring to i.I would not be legal because
                                           // is not in modport mp
                endmodule"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause26() {
        test!(
            source_text,
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
            many1(module_item),
            r##"import ComplexPkg::Complex;
                import ComplexPkg::add;"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"package p;
                  typedef enum { FALSE, TRUE } bool_t;
                endpackage

                package q;
                  typedef enum { ORIGINAL, FALSE } teeth_t;
                endpackage

                module top1 ;
                  import p::*;
                  import q::teeth_t;
                  teeth_t myteeth;
                  initial begin
                    myteeth = q:: FALSE; // OK:
                    myteeth = FALSE; // ERROR: Direct reference to FALSE refers to the
                  end // FALSE enumeration literal imported from p
                endmodule

                module top2 ;
                  import p::*;
                  import q::teeth_t, q::ORIGINAL, q::FALSE;
                  teeth_t myteeth;
                  initial begin
                    myteeth = FALSE; // OK: Direct reference to FALSE refers to the
                  end // FALSE enumeration literal imported from q
                endmodule"##,
            Ok((_, _))
        );
        test!(many1(module_item), r##"import ComplexPkg::*;"##, Ok((_, _)));
        test!(
            source_text,
            r##"package p;
                  int x;
                endpackage

                module top;
                  import p::*;     // line 1

                  if (1) begin : b
                    initial x = 1; // line 2
                    int x;         // line 3
                    initial x = 1; // line 4
                  end
                  int x;           // line 5
                endmodule"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"package p;
                  int x;
                endpackage

                package p2;
                  int x;
                endpackage

                module top;
                  import p::*;     // line 1
                  if (1) begin : b
                    initial x = 1; // line 2
                    import p2::*;  // line 3
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"package p;
                  function int f();
                    return 1;
                  endfunction
                endpackage

                module top;
                  int x;
                  if (1) begin : b
                    initial x = f(); // line 2
                    import p::*;     // line 3
                  end

                  function int f();
                    return 1;
                  endfunction
                endmodule"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"package p;
                  function int f();
                    return 1;
                  endfunction
                endpackage

                package p2;
                  function int f();
                    return 1;
                  endfunction
                endpackage

                module top;
                  import p::*;
                  int x;
                  if (1) begin : b
                    initial x = f(); // line 1
                  end
                  import p2::*;
                endmodule"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"package A;
                  typedef struct {
                    bit [ 7:0] opcode;
                    bit [23:0] addr;
                  } instruction_t;
                endpackage: A

                package B;
                  typedef enum bit {FALSE, TRUE} boolean_t;
                endpackage: B

                module M import A::instruction_t, B::*;
                  #(WIDTH = 32)
                  (input [WIDTH-1:0] data,
                   input instruction_t a,
                   output [WIDTH-1:0] result,
                   output boolean_t OK
                  );
                endmodule: M"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"package p;
                  typedef enum { FALSE, TRUE } BOOL;
                  const BOOL c = FALSE;
                endpackage

                package q;
                  const int c = 0;
                endpackage"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module m;
                  import q::*;
                  wire a = c;  // This statement forces the import of q::c;
                  import p::c; // The conflict with q::c and p::c creates an error.
                endmodule"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"package p1;
                  int x, y;
                endpackage

                package p2;
                  import p1::x;
                  export p1::*; // exports p1::x as the name "x";
                                // p1::x and p2::x are the same declaration
                endpackage

                package p3;
                  import p1::*;
                  import p2::*;
                  export p2::*;
                  int q = x;
                  // p1::x and q are made available from p3. Although p1::y
                  // is a candidate for import, it is not actually imported
                  // since it is not referenced. Since p1::y is not imported,
                  // it is not made available by the export.
                endpackage

                package p4;
                  import p1::*;
                  export p1::*;
                  int y = x; // y is available as a direct declaration;
                             // p1::x is made available by the export
                endpackage

                package p5;
                  import p4::*;
                  import p1::*;
                  export p1::x;
                  export p4::x; // p4::x refers to the same declaration
                                // as p1::x so this is legal.
                endpackage

                package p6;
                  import p1::*;
                  export p1::x;
                  int x; // Error. export p1::x is considered to
                         // be a reference to "x" so a subsequent
                         // declaration of x is illegal.
                endpackage

                package p7;
                  int y;
                endpackage

                package p8;
                  export *::*; // Exports both p7::y and p1::x.
                  import p7::y;
                  import p1::x;
                endpackage

                module top;
                  import p2::*;
                  import p4::*;
                  int y = x; // x is p1::x
                endmodule"##,
            Ok((_, _))
        );
        // TODO
        // Syntax 26-5 (not in Annex A)
        //test!(
        //    many1(module_item),
        //    r##"initial begin
        //          std::sys_task();
        //        end"##,
        //    Ok((_, _))
        //);
    }

    #[test]
    fn clause27() {
        test!(
            many1(module_item),
            r##"module mod_a;
                  genvar i;
                  // "generate", "endgenerate" keywords are not required
                  for (i=0; i<5; i=i+1) begin:a
                    for (i=0; i<5; i=i+1) begin:b
                    end
                  end
                endmodule

                module mod_b;
                  genvar i;
                  logic a;
                  for (i=1; i<0; i=i+1) begin: a
                  end
                endmodule

                module mod_c;
                  genvar i;
                  for (i=1; i<5; i=i+1) begin: a
                  end
                  for (i=10; i<15; i=i+1) begin: a
                  end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module gray2bin1 (bin, gray);
                  parameter SIZE = 8; // this module is parameterizable
                  output [SIZE-1:0] bin;
                  input [SIZE-1:0] gray;

                  genvar i;
                  generate
                    for (i=0; i<SIZE; i=i+1) begin:bitnum
                      assign bin[i] = ^gray[SIZE-1:i];
                        // i refers to the implicitly defined localparam whose
                        // value in each instance of the generate block is
                        // the value of the genvar when it was elaborated.
                    end
                  endgenerate
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module addergen1 (co, sum, a, b, ci);
                  parameter SIZE = 4;
                  output [SIZE-1:0] sum;
                  output co;
                  input [SIZE-1:0] a, b;
                  input ci;
                  wire [SIZE :0] c;
                  wire [SIZE-1:0] t [1:3];
                  genvar i;

                  assign c[0] = ci;

                  // Hierarchical gate instance names are:
                  // xor gates: bitnum[0].g1 bitnum[1].g1 bitnum[2].g1 bitnum[3].g1
                  // bitnum[0].g2 bitnum[1].g2 bitnum[2].g2 bitnum[3].g2
                  // and gates: bitnum[0].g3 bitnum[1].g3 bitnum[2].g3 bitnum[3].g3
                  // bitnum[0].g4 bitnum[1].g4 bitnum[2].g4 bitnum[3].g4
                  // or gates: bitnum[0].g5 bitnum[1].g5 bitnum[2].g5 bitnum[3].g5
                  // Generated instances are connected with
                  // multidimensional nets t[1][3:0] t[2][3:0] t[3][3:0]
                  // (12 nets total)

                  for(i=0; i<SIZE; i=i+1) begin:bitnum
                    xor g1 ( t[1][i], a[i], b[i]);
                    xor g2 ( sum[i], t[1][i], c[i]);
                    and g3 ( t[2][i], a[i], b[i]);
                    and g4 ( t[3][i], t[1][i], c[i]);
                    or  g5 ( c[i+1], t[2][i], t[3][i]);
                  end

                  assign co = c[SIZE];
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module addergen1 (co, sum, a, b, ci);
                  parameter SIZE = 4;
                  output [SIZE-1:0] sum;
                  output co;
                  input [SIZE-1:0] a, b;
                  input ci;
                  wire [SIZE :0] c;
                  genvar i;

                  assign c[0] = ci;

                  // Hierarchical gate instance names are:
                  // xor gates: bitnum[0].g1 bitnum[1].g1 bitnum[2].g1 bitnum[3].g1
                  // bitnum[0].g2 bitnum[1].g2 bitnum[2].g2 bitnum[3].g2
                  // and gates: bitnum[0].g3 bitnum[1].g3 bitnum[2].g3 bitnum[3].g3
                  // bitnum[0].g4 bitnum[1].g4 bitnum[2].g4 bitnum[3].g4
                  // or gates: bitnum[0].g5 bitnum[1].g5 bitnum[2].g5 bitnum[3].g5
                  // Gate instances are connected with nets named:
                  // bitnum[0].t1 bitnum[1].t1 bitnum[2].t1 bitnum[3].t1
                  // bitnum[0].t2 bitnum[1].t2 bitnum[2].t2 bitnum[3].t2
                  // bitnum[0].t3 bitnum[1].t3 bitnum[2].t3 bitnum[3].t3

                  for(i=0; i<SIZE; i=i+1) begin:bitnum
                    wire t1, t2, t3;
                    xor g1 ( t1, a[i], b[i]);
                    xor g2 ( sum[i], t1, c[i]);
                    and g3 ( t2, a[i], b[i]);
                    and g4 ( t3, t1, c[i]);
                    or  g5 ( c[i+1], t2, t3);
                  end

                  assign co = c[SIZE];
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"parameter SIZE = 2;
                genvar i, j, k, m;
                generate
                  for (i=0; i<SIZE; i=i+1) begin:B1 // scope B1[i]
                    M1 N1(); // instantiates B1[i].N1
                    for (j=0; j<SIZE; j=j+1) begin:B2 // scope B1[i].B2[j]
                      M2 N2(); // instantiates B1[i].B2[j].N2
                      for (k=0; k<SIZE; k=k+1) begin:B3 // scope B1[i].B2[j].B3[k]
                        M3 N3(); // instantiates
                      end // B1[i].B2[j].B3[k].N3
                    end
                    if (i>0) begin:B4 // scope B1[i].B4
                      for (m=0; m<SIZE; m=m+1) begin:B5 // scope B1[i].B4.B5[m]
                        M4 N4(); // instantiates
                      end // B1[i].B4.B5[m].N4
                    end
                  end
                endgenerate"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module test;
                  parameter p = 0, q = 0;
                  wire a, b, c;

                  //---------------------------------------------------------
                  // Code to either generate a u1.g1 instance or no instance.
                  // The u1.g1 instance of one of the following gates:
                  // (and, or, xor, xnor) is generated if
                  // {p,q} == {1,0}, {1,2}, {2,0}, {2,1}, {2,2}, {2, default}
                  //---------------------------------------------------------
                  if (p == 1)
                    if (q == 0)
                      begin : u1            // If p==1 and q==0, then instantiate
                        and g1(a, b, c);    // AND with hierarchical name test.u1.g1
                      end
                    else if (q == 2)
                      begin : u1            // If p==1 and q==2, then instantiate
                        or g1(a, b, c);     // OR with hierarchical name test.u1.g1
                      end
                                            // "else" added to end "if (q == 2)" statement
                    else ;                  // If p==1 and q!=0 or 2, then no instantiation
                  else if (p == 2)
                    case (q)
                      0, 1, 2:
                        begin : u1          // If p==2 and q==0,1, or 2, then instantiate
                          xor g1(a, b, c);  // XOR with hierarchical name test.u1.g1
                        end
                      default:
                        begin : u1          // If p==2 and q!=0,1, or 2, then instantiate
                          xnor g1(a, b, c); // XNOR with hierarchical name test.u1.g1
                        end
                    endcase
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module multiplier(a,b,product);
                  parameter a_width = 8, b_width = 8;
                  localparam product_width = a_width+b_width;
                    // cannot be modified directly with the defparam
                    // statement or the module instance statement #
                  input [a_width-1:0] a;
                  input [b_width-1:0] b;
                  output [product_width-1:0] product;

                  generate
                    if((a_width < 8) || (b_width < 8)) begin: mult
                      CLA_multiplier #(a_width,b_width) u1(a, b, product);
                      // instantiate a CLA multiplier
                    end
                    else begin: mult
                      WALLACE_multiplier #(a_width,b_width) u1(a, b, product);
                      // instantiate a Wallace-tree multiplier
                    end
                  endgenerate
                  // The hierarchical instance name is mult.u1
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"generate
                  case (WIDTH)
                    1: begin: adder // 1-bit adder implementation
                         adder_1bit x1(co, sum, a, b, ci);
                       end
                    2: begin: adder // 2-bit adder implementation
                         adder_2bit x1(co, sum, a, b, ci);
                       end
                    default:
                      begin: adder // others - carry look-ahead adder
                        adder_cla #(WIDTH) x1(co, sum, a, b, ci);
                      end
                  endcase
                  // The hierarchical instance name is adder.x1
                endgenerate"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module dimm(addr, ba, rasx, casx, csx, wex, cke, clk, dqm, data, dev_id);
                  parameter [31:0] MEM_WIDTH = 16, MEM_SIZE = 8; // in mbytes
                  input [10:0] addr;
                  input ba, rasx, casx, csx, wex, cke, clk;
                  input [ 7:0] dqm;
                  inout [63:0] data;
                  input [ 4:0] dev_id;
                  genvar i;

                  case ({MEM_SIZE, MEM_WIDTH})
                    {32'd8, 32'd16}: // 8Meg x 16 bits wide
                      begin: memory
                        for (i=0; i<4; i=i+1) begin:word16
                          sms_08b216t0 p(.clk(clk), .csb(csx), .cke(cke),.ba(ba),
                                         .addr(addr), .rasb(rasx), .casb(casx),
                                         .web(wex), .udqm(dqm[2*i+1]), .ldqm(dqm[2*i]),
                                         .dqi(data[15+16*i:16*i]), .dev_id(dev_id));
                          // The hierarchical instance names are:
                          // memory.word16[3].p, memory.word16[2].p,
                          // memory.word16[1].p, memory.word16[0].p,
                          // and the task memory.read_mem
                        end
                        task read_mem;
                          input [31:0] address;
                          output [63:0] data;
                          begin // call read_mem in sms module
                            word16[3].p.read_mem(address, data[63:48]);
                            word16[2].p.read_mem(address, data[47:32]);
                            word16[1].p.read_mem(address, data[31:16]);
                            word16[0].p.read_mem(address, data[15: 0]);
                          end
                        endtask
                      end
                    {32'd16, 32'd8}: // 16Meg x 8 bits wide
                      begin: memory
                        for (i=0; i<8; i=i+1) begin:word8
                          sms_16b208t0 p(.clk(clk), .csb(csx), .cke(cke),.ba(ba),
                                         .addr(addr), .rasb(rasx), .casb(casx),
                                         .web(wex), .dqm(dqm[i]),
                                         .dqi(data[7+8*i:8*i]), .dev_id(dev_id));
                          // The hierarchical instance names are
                          // memory.word8[7].p, memory.word8[6].p,
                          // ...
                          // memory.word8[1].p, memory.word8[0].p,
                          // and the task memory.read_mem
                        end
                        task read_mem;
                          input [31:0] address;
                          output [63:0] data;
                          begin // call read_mem in sms module
                            word8[7].p.read_mem(address, data[63:56]);
                            word8[6].p.read_mem(address, data[55:48]);
                            word8[5].p.read_mem(address, data[47:40]);
                            word8[4].p.read_mem(address, data[39:32]);
                            word8[3].p.read_mem(address, data[31:24]);
                            word8[2].p.read_mem(address, data[23:16]);
                            word8[1].p.read_mem(address, data[15: 8]);
                            word8[0].p.read_mem(address, data[ 7: 0]);
                          end
                        endtask
                      end
                    // Other memory cases ...
                  endcase
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module top;
                  parameter genblk2 = 0;
                  genvar i;

                  // The following generate block is implicitly named genblk1
                  if (genblk2) logic a; // top.genblk1.a
                  else logic b;         // top.genblk1.b

                  // The following generate block is implicitly named genblk02
                  // as genblk2 is already a declared identifier
                  if (genblk2) logic a; // top.genblk02.a
                  else logic b;         // top.genblk02.b

                  // The following generate block would have been named genblk3
                  // but is explicitly named g1
                  for (i = 0; i < 1; i = i + 1) begin : g1 // block name
                    // The following generate block is implicitly named genblk1
                    // as the first nested scope inside g1
                    if (1) logic a; // top.g1[0].genblk1.a
                  end

                  // The following generate block is implicitly named genblk4 since
                  // it belongs to the fourth generate construct in scope "top".
                  // The previous generate block would have been
                  // named genblk3 if it had not been explicitly named g1
                  for (i = 0; i < 1; i = i + 1)
                    // The following generate block is implicitly named genblk1
                    // as the first nested generate block in genblk4
                    if (1) logic a; // top.genblk4[0].genblk1.a

                  // The following generate block is implicitly named genblk5
                  if (1) logic a; // top.genblk5.a
                endmodule"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause28() {
        test!(
            many1(module_item),
            r##"module driver (in, out, en);
                  input [3:0] in;
                  output [3:0] out;
                  input en;

                  bufif0 ar[3:0] (out, in, en); // array of three-state buffers
                endmodule

                module driver_equiv (in, out, en);
                  input [3:0] in;
                  output [3:0] out;
                  input en;

                  bufif0 ar3 (out[3], in[3], en); // each buffer declared separately
                  bufif0 ar2 (out[2], in[2], en);
                  bufif0 ar1 (out[1], in[1], en);
                  bufif0 ar0 (out[0], in[0], en);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module busdriver (busin, bushigh, buslow, enh, enl);
                  input [15:0] busin;
                  output [ 7:0] bushigh, buslow;
                  input enh, enl;

                  driver busar3 (busin[15:12], bushigh[7:4], enh);
                  driver busar2 (busin[11:8], bushigh[3:0], enh);
                  driver busar1 (busin[7:4], buslow[7:4], enl);
                  driver busar0 (busin[3:0], buslow[3:0], enl);
                endmodule

                module busdriver_equiv (busin, bushigh, buslow, enh, enl);
                  input [15:0] busin;
                  output [ 7:0] bushigh, buslow;
                  input enh, enl;

                  driver busar[3:0] (.out({bushigh, buslow}), .in(busin),
                                     .en({enh, enh, enl, enl}));
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module dffn (q, d, clk);
                  parameter bits = 1;
                  input [bits-1:0] d;
                  output [bits-1:0] q;
                  input clk ;

                  DFF dff[bits-1:0] (q, d, clk); // create a row of D flip-flops
                endmodule

                module MxN_pipeline (in, out, clk);
                  parameter M = 3, N = 4; // M=width,N=depth
                  input [M-1:0] in;
                  output [M-1:0] out;
                  input clk;
                  wire [M*(N-1):1] t;

                  // #(M) redefines the bits parameter for dffn
                  // create p[1:N] columns of dffn rows (pipeline)

                  dffn #(M) p[1:N] ({out, t}, {t, in}, clk);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"and a1 (out, in1, in2);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"buf b1 (out1, out2, in);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"bufif1 bf1 (outw, inw, controlw);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"pmos p1 (out, data, control);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"tranif1 t1 (inout1,inout2,control);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"cmos (w, datain, ncontrol, pcontrol);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"nmos (w, datain, ncontrol);
                pmos (w, datain, pcontrol);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"pullup (strong1) p1 (neta), p2 (netb);"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"and #(10) a1 (out, in1, in2);          // only one delay
                and #(10,12) a2 (out, in1, in2);       // rise and fall delays
                bufif0 #(10,12,11) b3 (out, in, ctrl); // rise, fall, and turn-off delays"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module tri_latch (qout, nqout, clock, data, enable);
                  output qout, nqout;
                  input clock, data, enable;
                  tri qout, nqout;

                  not #5           n1 (ndata, data);
                  nand #(3,5)      n2 (wa, data, clock),
                                   n3 (wb, ndata, clock);
                  nand #(12,15)    n4 (q, nq, wa),
                                   n5 (nq, q, wb);
                  bufif1 #(3,7,13) q_drive (qout, q, enable),
                                   nq_drive (nqout, nq, enable);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module iobuf (io1, io2, dir);
                  bufif0 #(5:7:9, 8:10:12, 15:18:21) b1 (io1, io2, dir);
                  bufif1 #(6:8:10, 5:7:9, 13:17:19) b2 (io2, io1, dir);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"parameter min_hi = 97, typ_hi = 100, max_hi = 107;
                logic clk;
                always begin
                  #(95:100:105) clk = 1;
                  #(min_hi:typ_hi:max_hi) clk = 0;
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"trireg (large) #(0,0,50) cap1;"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module capacitor;
                  logic data, gate;

                  // trireg declaration with a charge decay time of 50 time units
                  trireg (large) #(0,0,50) cap1;

                  nmos nmos1 (cap1, data, gate); // nmos that drives the trireg

                  initial begin
                    $monitor("%0d data=%v gate=%v cap1=%v", $time, data, gate, cap1);
                    data = 1;
                    // Toggle the driver of the control input to the nmos switch
                    gate = 1;
                    #10 gate = 0;
                    #30 gate = 1;
                    #10 gate = 0;
                    #100 $finish;
                  end
                endmodule"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause29() {
        test!(
            source_text,
            r##"primitive multiplexer (mux, control, dataA, dataB);
                  output mux;
                  input control, dataA, dataB;
                  table
                    // control dataA dataB mux
                       0       1     0    : 1 ;
                       0       1     1    : 1 ;
                       0       1     x    : 1 ;
                       0       0     0    : 0 ;
                       0       0     1    : 0 ;
                       0       0     x    : 0 ;
                       1       0     1    : 1 ;
                       1       1     1    : 1 ;
                       1       x     1    : 1 ;
                       1       0     0    : 0 ;
                       1       1     0    : 0 ;
                       1       x     0    : 0 ;
                       x       0     0    : 0 ;
                       x       1     1    : 1 ;
                  endtable
                endprimitive"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"primitive multiplexer (mux, control, dataA, dataB);
                  output mux;
                  input control, dataA, dataB;
                  table
                    // control dataA dataB mux
                       0       1     ?    : 1 ; // ? = 0 1 x
                       0       0     ?    : 0 ;
                       1       ?     1    : 1 ;
                       1       ?     0    : 0 ;
                       x       0     0    : 0 ;
                       x       1     1    : 1 ;
                  endtable
                endprimitive"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"primitive latch (q, ena_, data);
                  output q; reg q;
                  input ena_, data;
                  table
                    // ena_ data : q : q+
                       0    1    : ? : 1 ;
                       0    0    : ? : 0 ;
                       1    ?    : ? : - ; // - = no change
                  endtable
                endprimitive"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"primitive d_edge_ff (q, clock, data);
                  output q; reg q;
                  input clock, data;
                  table
                    // clock data q q+
                    // obtain output on rising edge of clock
                    (01) 0 : ? : 0 ;
                    (01) 1 : ? : 1 ;
                    (0?) 1 : 1 : 1 ;
                    (0?) 0 : 0 : 0 ;
                    // ignore negative edge of clock
                    (?0) ? : ? : - ;
                    // ignore data changes on steady clock
                    ? (??) : ? : - ;
                  endtable
                endprimitive"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"primitive srff (q, s, r);
                  output q; reg q;
                  input s, r;
                  initial q = 1'b1;
                  table
                    // s r q q+
                    1 0 : ? : 1 ;
                    f 0 : 1 : - ;
                    0 r : ? : 0 ;
                    0 f : 0 : - ;
                    1 1 : ? : 0 ;
                  endtable
                endprimitive"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"primitive dff1 (q, clk, d);
                  input clk, d;
                  output q; reg q;
                  initial q = 1'b1;
                  table
                    // clk d q q+
                    r 0 : ? : 0 ;
                    r 1 : ? : 1 ;
                    f ? : ? : - ;
                    ? * : ? : - ;
                  endtable
                endprimitive

                module dff (q, qb, clk, d);
                  input clk, d;
                  output q, qb;
                  dff1 g1 (qi, clk, d);
                  buf #3 g2 (q, qi);
                  not #5 g3 (qb, qi);
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module flip;
                  reg clock, data;
                  parameter p1 = 10;
                  parameter p2 = 33;
                  parameter p3 = 12;

                  d_edge_ff #p3 d_inst (q, clock, data);

                  initial begin
                    data = 1;
                    clock = 1;
                    #(20 * p1) $finish;
                  end

                  always #p1 clock = ~clock;
                  always #p2 data = ~data;
                endmodule"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"primitive jk_edge_ff (q, clock, j, k, preset, clear);
                  output q; reg q;
                  input clock, j, k, preset, clear;
                  table
                    // clock jk pc state output/next state
                    ? ?? 01 : ? : 1 ; // preset logic
                    ? ?? *1 : 1 : 1 ;
                    ? ?? 10 : ? : 0 ; // clear logic
                    ? ?? 1* : 0 : 0 ;
                    r 00 00 : 0 : 1 ; // normal clocking cases
                    r 00 11 : ? : - ;
                    r 01 11 : ? : 0 ;
                    r 10 11 : ? : 1 ;
                    r 11 11 : 0 : 1 ;
                    r 11 11 : 1 : 0 ;
                    f ?? ?? : ? : - ;
                    b *? ?? : ? : - ; // j and k transition cases
                    b ?* ?? : ? : - ;
                  endtable
                endprimitive"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause30() {
        test!(
            many1(module_item),
            r##"specify
                  specparam tRise_clk_q = 150, tFall_clk_q = 200;
                  specparam tSetup = 70;

                  (clk => q) = (tRise_clk_q, tFall_clk_q);

                  $setup(d, posedge clk, tSetup);
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module XORgate (a, b, out);
                  input a, b;
                  output out;

                  xor x1 (out, a, b);

                  specify
                    specparam noninvrise = 1, noninvfall = 2;
                    specparam invertrise = 3, invertfall = 4;
                    if (a) (b => out) = (invertrise, invertfall);
                    if (b) (a => out) = (invertrise, invertfall);
                    if (~a)(b => out) = (noninvrise, noninvfall);
                    if (~b)(a => out) = (noninvrise, noninvfall);
                  endspecify
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module ALU (o1, i1, i2, opcode);
                  input [7:0] i1, i2;
                  input [2:1] opcode;
                  output [7:0] o1;

                  //functional description omitted
                  specify
                    // add operation
                    if (opcode == 2'b00) (i1,i2 *> o1) = (25.0, 25.0);
                    // pass-through i1 operation
                    if (opcode == 2'b01) (i1 => o1) = (5.6, 8.0);
                    // pass-through i2 operation
                    if (opcode == 2'b10) (i2 => o1) = (5.6, 8.0);
                    // delays on opcode changes
                    (opcode *> o1) = (6.1, 6.5);
                  endspecify
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  ( posedge clk => ( q[0] : data ) ) = (10, 5);
                  ( negedge clk => ( q[0] : data ) ) = (20, 12);
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  if (reset)
                    (posedge clk => ( q[0] : data ) ) = (15, 8);
                  if (!reset && cntrl)
                    (posedge clk => ( q[0] : data ) ) = (6, 2);
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  if (reset)
                    (posedge clk => (q[3:0]:data)) = (10,5);
                  if (!reset)
                    (posedge clk => (q[0]:data)) = (15,8);
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module mux8 (in1, in2, s, q) ;
                  output [7:0] q;
                  input [7:0] in1, in2;
                  input s;
                  // Functional description omitted ...
                  specify
                    (in1 => q) = (3, 4) ;
                    (in2 => q) = (2, 3) ;
                    (s *> q) = 1;
                  endspecify
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  // Specify Parameters
                  specparam tRise_clk_q = 45:150:270, tFall_clk_q=60:200:350;
                  specparam tRise_Control = 35:40:45, tFall_control=40:50:65;

                  // Module Path Assignments
                  (clk => q) = (tRise_clk_q, tFall_clk_q);
                  (clr, pre *> q) = (tRise_control, tFall_control);
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  // one expression specifies all transitions
                  (C => Q) = 20;
                  (C => Q) = 10:14:20;

                  // two expressions specify rise and fall delays
                  specparam tPLH1 = 12, tPHL1 = 25;
                  specparam tPLH2 = 12:16:22, tPHL2 = 16:22:25;
                  (C => Q) = ( tPLH1, tPHL1 ) ;
                  (C => Q) = ( tPLH2, tPHL2 ) ;

                  // three expressions specify rise, fall, and z transition delays
                  specparam tPLH1 = 12, tPHL1 = 22, tPz1 = 34;
                  specparam tPLH2 = 12:14:30, tPHL2 = 16:22:40, tPz2 = 22:30:34;
                  (C => Q) = (tPLH1, tPHL1, tPz1);
                  (C => Q) = (tPLH2, tPHL2, tPz2);

                  // six expressions specify transitions to/from 0, 1, and z
                  specparam t01 = 12, t10 = 16, t0z = 13,
                            tz1 = 10, t1z = 14, tz0 = 34 ;
                  (C => Q) = ( t01, t10, t0z, tz1, t1z, tz0) ;
                  specparam T01 = 12:14:24, T10 = 16:18:20, T0z = 13:16:30 ;
                  specparam Tz1 = 10:12:16, T1z = 14:23:36, Tz0 = 15:19:34 ;
                  (C => Q) = ( T01, T10, T0z, Tz1, T1z, Tz0) ;

                  // twelve expressions specify all transition delays explicitly
                  specparam t01=10, t10=12, t0z=14, tz1=15, t1z=29, tz0=36,
                  t0x=14, tx1=15, t1x=15, tx0=14, txz=20, tzx=30 ;
                  (C => Q) = (t01, t10, t0z, tz1, t1z, tz0,
                              t0x, tx1, t1x, tx0, txz, tzx) ;
                endspecify"##,
            Ok((_, _))
        );
        // TODO
        // specify_input_terminal_descriptor can have $
        //test!(
        //    many1(module_item),
        //    r##"specify
        //        (clk => q) = 12;
        //        (data => q) = 10;
        //        (clr, pre *> q) = 4;

        //        specparam
        //          PATHPULSE$clk$q = (2,9),
        //          PATHPULSE$clr$q = (0,4),
        //          PATHPULSE$ = 3;
        //        endspecify"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"specify
                  (a=>out)=(2,3);
                  (b =>out)=(3,4);
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  (a=>out)=(2,3);
                  showcancelled out;
                  (b =>out)=(3,4);
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  showcancelled out;
                  pulsestyle_ondetect out;
                  (a => out) = (2,3);
                  (b => out) = (4,5);
                  showcancelled out_b;
                  pulsestyle_ondetect out_b;
                  (a => out_b) = (3,4);
                  (b => out_b) = (5,6);
                endspecify

                specify
                  showcancelled out,out_b;
                  pulsestyle_ondetect out,out_b;
                  (a => out) = (2,3);
                  (b => out) = (4,5);
                  (a => out_b) = (3,4);
                  (b => out_b) = (5,6);
                endspecify"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause31() {
        test!(
            many1(module_item),
            r##"specify
                  $setuphold( posedge clk, data, tSU, tHLD );
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  $setup( data, posedge clk, tSU );
                  $hold( posedge clk, data, tHLD );
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  $recrem( posedge clear, posedge clk, tREC, tREM );
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  $removal( posedge clear, posedge clk, tREM );
                  $recovery( posedge clear, posedge clk, tREC );
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  $timeskew (posedge CP &&& MODE, negedge CPN, 50, , event_based_flag,
                             remain_active_flag);
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  $fullskew (posedge CP &&& MODE, negedge CPN, 50, 70,, event_based_flag,
                             remain_active_flag);
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  $width (posedge clk, 6, 0, ntfr_reg);
                endspecify"##,
            Ok((_, _))
        );
        // TODO
        // $width must have threshold
        //test!(
        //    many1(module_item),
        //    r##"specify
        //          // Legal Calls
        //          $width ( negedge clr, lim );
        //          $width ( negedge clr, lim, thresh, notif );
        //          $width ( negedge clr, lim, 0, notif );
        //          // Illegal Calls
        //          //$width ( negedge clr, lim, , notif );
        //          //$width ( negedge clr, lim, notif );
        //        endspecify"##,
        //    Ok((_, _))
        //);
        test!(
            many1(module_item),
            r##"specify
                  $nochange( posedge clk, data, 0, 0) ;
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  $setup( data, posedge clk, 10, notifier ) ;
                  $width( posedge clk, 16, 0, notifier ) ;
                endspecify"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"primitive posdff_udp(q, clock, data, preset, clear, notifier);
                  output q; reg q;
                  input clock, data, preset, clear, notifier;
                  table
                    //clock data p c notifier state q
                    //-------------------------------------
                    r 0 1 1 ? : ? : 0 ;
                    r 1 1 1 ? : ? : 1 ;
                    p 1 ? 1 ? : 1 : 1 ;
                    p 0 1 ? ? : 0 : 0 ;
                    n ? ? ? ? : ? : - ;
                    ? * ? ? ? : ? : - ;
                    ? ? 0 1 ? : ? : 1 ;
                    ? ? * 1 ? : 1 : 1 ;
                    ? ? 1 0 ? : ? : 0 ;
                    ? ? 1 * ? : 0 : 0 ;
                    ? ? ? ? * : ? : x ;// At any notifier event
                    // output x
                  endtable
                endprimitive

                module dff(q, qbar, clock, data, preset, clear);
                  output q, qbar;
                  input clock, data, preset, clear;
                  reg notifier;
                  and (enable, preset, clear);
                  not (qbar, ffout);
                  buf (q, ffout);
                  posdff_udp (ffout, clock, data, preset, clear, notifier);

                  specify
                    // Define timing check specparam values
                    specparam tSU = 10, tHD = 1, tPW = 25, tWPC = 10, tREC = 5;
                    // Define module path delay rise and fall min:typ:max values
                    specparam tPLHc = 4:6:9 , tPHLc = 5:8:11;
                    specparam tPLHpc = 3:5:6 , tPHLpc = 4:7:9;
                    // Specify module path delays
                    (clock *> q,qbar) = (tPLHc, tPHLc);
                    (preset,clear *> q,qbar) = (tPLHpc, tPHLpc);
                    // Setup time : data to clock, only when preset and clear are 1
                    $setup(data, posedge clock &&& enable, tSU, notifier);
                    // Hold time: clock to data, only when preset and clear are 1
                    $hold(posedge clock, data &&& enable, tHD, notifier);
                    // Clock period check
                    $period(posedge clock, tPW, notifier);
                    // Pulse width : preset, clear
                    $width(negedge preset, tWPC, 0, notifier);
                    $width(negedge clear, tWPC, 0, notifier);
                    // Recovery time: clear or preset to clock
                    $recovery(posedge preset, posedge clock, tREC, notifier);
                    $recovery(posedge clear, posedge clock, tREC, notifier);
                  endspecify
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  $setup( data, posedge clk, 10 );
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  $setup( data, posedge clk &&& clr, 10 ) ;
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  $setup( data, posedge clk &&& (~clr), 10 ) ;
                  $setup( data, posedge clk &&& (clr===0), 10 );
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  $setup( data, posedge clk &&& clr_and_set, 10 );
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module DFF (Q, CLK, DAT);
                  input CLK;
                  input [7:0] DAT;
                  output [7:0] Q;
                  always @(posedge clk)
                    Q = DAT;
                  specify
                    $setup (DAT, posedge CLK, 10);
                  endspecify
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  $setuphold(posedge CLK, DATA, -10, 20);
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  $setuphold(posedge CLK, DATA1, -10, 20);
                  $setuphold(posedge CLK, DATA2, -15, 18);
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  $setuphold(posedge CLK, DATA1, -10, 20,,,, del_CLK, del_DATA1);
                  $setuphold(posedge CLK, DATA2, -15, 18);
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  (CLK => Q) = 6;
                  $setuphold (posedge CLK, posedge D, -3, 8, , , , dCLK, dD);
                  $setuphold (posedge CLK, negedge D, -7, 13, , , , dCLK, dD);
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  $setup (data, clk &&& cond1, tsetup, ntfr);
                  $hold (clk, data &&& cond1, thold, ntfr);
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specify
                  $setuphold( clk, data, tsetup, thold, ntfr, , cond1);
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"assign TE_cond_D = (dTE !== 1'b1);
                assign TE_cond_TI = (dTE !== 1'b0);
                assign DXTI_cond = (dTI !== dD);

                specify
                  $setuphold(posedge CP, D, -10, 20, notifier, ,TE_cond_D, dCP, dD);
                  $setuphold(posedge CP, TI, 20, -10, notifier, ,TE_cond_TI, dCP, dTI);
                  $setuphold(posedge CP, TE, -4, 8, notifier, ,DXTI_cond, dCP, dTE);
                endspecify"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause32() {
        test!(
            many1(module_item),
            r##"specify
                  $setuphold (posedge clk &&& mode, data, 1, 1, ntfr);
                  $setuphold (negedge clk &&& !mode, data, 1, 1, ntfr);
                  $setuphold (edge clk, data, 1, 1, ntfr);
                endspecify"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"module clock(clk);
                  output clk;
                  reg clk;
                  specparam dhigh=0, dlow=0;
                  initial clk = 0;
                  always
                    begin
                      #dhigh clk = 1; // Clock remains low for time dlow
                                      // before transitioning to 1
                      #dlow clk = 0;  // Clock remains high for time dhigh
                                      // before transitioning to 0
                    end
                endmodule"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"specparam cap = 0;
                specify
                  (A => Z) = 1.4 * cap + 0.7;
                endspecify"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause33() {
        test!(
            source_text,
            r##"config cfg1; // specify rtl adder for top.a1, gate-level adder for top.a2
                  design rtlLib.top;
                  default liblist rtlLib;
                  instance top.a2 liblist gateLib;
                endconfig"##,
            Ok((_, _))
        );
        test!(
            library_text,
            r##"library rtlLib *.v;     // matches all files in the current directory with
                                        // a .v suffix
                library gateLib ./*.vg; // matches all files in the current directory with
                                        // a .vg suffix"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"config bot;
                  design lib1.bot;
                  default liblist lib1 lib2;
                  instance bot.a1 liblist lib3;
                endconfig

                config top;
                  design lib1.top;
                  default liblist lib2 lib1;
                  instance top.bot use lib1.bot:config;
                  instance top.bot.a1 liblist lib4;
                  // ERROR - cannot set liblist for top.bot.a1 from this config
                endconfig"##,
            Ok((_, _))
        );
        // TODO
        // use don't have #()
        //test!(
        //    source_text,
        //    r##"config cfgl;
        //          design rtlLib.top;
        //          instance top use #(.WIDTH(32));
        //          instance top.a1 use #(.W(top.WIDTH));
        //        endconfig"##,
        //    Ok((_, _))
        //);
        // TODO
        // use don't have #()
        //test!(
        //    source_text,
        //    r##"module top4 ();
        //          parameter S = 16;
        //          adder a1 #(.ID("a1"))();
        //          adder a2 #(.ID("a2"))();
        //          adder a3 #(.ID("a3"))();
        //          adder a4 #(.ID("a4"))();
        //        endmodule

        //        config cfg2;
        //          localparam S = 24;
        //          design rtlLib.top4;
        //          instance top4.a1 use #(.W(top4.S));
        //          instance top4.a2 use #(.W(S));
        //        endconfig"##,
        //    Ok((_, _))
        //);
        // TODO
        // use don't have #()
        //test!(
        //    source_text,
        //    r##"config cfg3;
        //          design rtlLib.top5;
        //          instance top5.a1 use #(.W()); // set only parameter W back to its default
        //        endconfig"##,
        //    Ok((_, _))
        //);
        // TODO
        // use don't have #()
        //test!(
        //    source_text,
        //    r##"config cfg4;
        //          design rtlLib.top;
        //          instance top.a1 use #(); // set all parameters in instance a1
        //                                   // back to their defaults
        //        endconfig"##,
        //    Ok((_, _))
        //);
        // TODO
        // use don't have #()
        //test!(
        //    source_text,
        //    r##"module test;
        //          top8 t();
        //          defparam t.WIDTH = 64;
        //          defparam t.a1.W = 16;
        //        endmodule

        //        module top8 ();
        //          parameter WIDTH = 32;
        //          adder a1 #(.ID("a1")) ();
        //          adder a2 #(.ID("a2"),.W(WIDTH))();
        //        endmodule

        //        module adder #(parameter ID = "id",
        //                                 W = 8,
        //                                 D = 512)
        //                     ();
        //          $display("ID = %s, W = %d, D = %d", ID, W, D);
        //        endmodule

        //        config cfg6;
        //          design rtlLib.test;
        //          instance test.t use #(.WIDTH(48));
        //        endconfig"##,
        //    Ok((_, _))
        //);
        test!(
            source_text,
            r##"config cfg1;
                  design rtlLib.top ;
                  default liblist aLib rtlLib;
                endconfig"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"config cfg2;
                  design rtlLib.top ;
                  default liblist gateLib aLib rtlLib;
                endconfig"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"config cfg3;
                  design rtlLib.top ;
                  default liblist aLib rtlLib;
                  cell m use gateLib.m ;
                endconfig"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"config cfg4;
                  design rtlLib.top ;
                  default liblist gateLib rtlLib;
                  instance top.a2 liblist aLib;
                endconfig"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"config cfg5;
                  design aLib.adder;
                  default liblist gateLib aLib;
                  instance adder.f1 liblist rtlLib;
                endconfig"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"config cfg6;
                  design rtlLib.top;
                  default liblist aLib rtlLib;
                  instance top.a2 use work.cfg5:config ;
                endconfig"##,
            Ok((_, _))
        );
        test!(
            library_text,
            r##"library lib1 "/proj/lib/foo*.v";
                library lib2 "/proj/lib/foo.v";
                library lib3 "../lib/";
                library lib4 "/proj/lib/*ver.v";"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause34() {
        test!(
            source_text,
            r##"module secret (a, b);
                  input a;
                  output b;

                  `pragma protect encoding=(enctype="raw")
                  `pragma protect data_method="x-caesar", data_keyname="rot13", begin
                  `pragma protect
                  runtime_license=(library="lic.so",feature="runSecret",entry="chk", match=42)
                    logic b;
                    initial
                      begin
                        b = 0;
                      end

                    always
                      begin
                        #5 b = a;
                      end
                  `pragma protect end
                endmodule // secret"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"module secret (a, b);
                  input a;
                  output b;
                  `pragma protect encoding=(enctype="raw")
                  `pragma protect data_method="x-caesar", data_keyname="rot13",
                  begin_protected
                  `pragma protect encoding=(enctype="raw", bytes=190), data_block
                  //`centzn cebgrpg ehagvzr_yvprafr=(yvoenel="yvp.fb",srngher="ehaFrperg",
                  //ragel="pux",zngpu=42)
                  //  ert o;
                  //  vavgvny
                  //    ortva
                  //      o = 0;
                  //    raq

                  //  nyjnlf
                  //    ortva
                  //      #5 o = n;
                  //    raq
                  `pragma protect end_protected
                  `pragma reset protect
                endmodule // secret"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause35() {
        // TODO
        // c_identifier can't accept \begin.
        //test!(
        //    source_text,
        //    r##"export "DPI-C" f_plus = function \f+ ; // "f+" exported as "f_plus"
        //        export "DPI-C" function f; // "f" exported under its own name
        //        import "DPI-C" init_1 = function void \init[1] (); // "init_1" is a linkage name
        //        import "DPI-C" \begin = function void \init[2] (); // "begin" is a linkage name"##,
        //    Ok((_, _))
        //);
        test!(
            source_text,
            r##"import "DPI-C" function void myInit();

                // from standard math library
                import "DPI-C" pure function real sin(real);

                // from standard C library: memory management
                import "DPI-C" function chandle malloc(int size); // standard C function
                import "DPI-C" function void free(chandle ptr); // standard C function

                // abstract data structure: queue
                import "DPI-C" function chandle newQueue(input string name_of_queue);

                // Note the following import uses the same foreign function for
                // implementation as the prior import, but has different SystemVerilog name
                // and provides a default value for the argument.
                import "DPI-C" newQueue=function chandle newAnonQueue(input string s=null);
                import "DPI-C" function chandle newElem(bit [15:0]);
                import "DPI-C" function void enqueue(chandle queue, chandle elem);
                import "DPI-C" function chandle dequeue(chandle queue);

                // miscellanea
                import "DPI-C" function bit [15:0] getStimulus();
                import "DPI-C" context function void processTransaction(chandle elem,
                output logic [64:1] arr [0:63]);
                import "DPI-C" task checkResults(input string s, bit [511:0] packet);"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"import "DPI-C" function void f1(input logic [127:0]);
                import "DPI-C" function void f2(logic [127:0] i []); //open array of 128-bit"##,
            Ok((_, _))
        );
        test!(
            source_text,
            r##"import "DPI-C" function void f3(input MyType i [][]);
                  /* 2-dimensional unsized unpacked array of MyType */"##,
            Ok((_, _))
        );
    }

    #[test]
    fn clause36() {
        test!(
            many1(module_item),
            r##"initial begin
                  $get_vector("test_vector.pat", input_bus);
                end"##,
            Ok((_, _))
        );
        test!(
            many1(module_item),
            r##"initial begin
                  for (i = 1; i <= 1024; i = i + 1)
                    @(posedge clk) $get_vector("test_vector.pat", input_bus);
                end"##,
            Ok((_, _))
        );
    }
}

#[test]
fn debug() {
    test!(
        source_text,
        r##"module top (); initial begin p.randomize() with { length == 1512;}; end endmodule"##,
        Ok((_, _))
    );
    nom_tracable::cumulative_histogram();
}
