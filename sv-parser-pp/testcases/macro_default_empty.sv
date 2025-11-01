// IEEE 1800-2017 Clause 22.5 `define, `undef, and `undefineall
// The directive `define allows formal arguments to have default values.
// The default value may be an empty token sequence.
// This test verifies that `define M(a=)` and `define M(a=, b=)` are accepted
// and expand as expected without errors.
`define LOGIC(name, prefix=) logic prefix``name;
`define REAL(name, prefix=, suffix=) real prefix``name``suffix;
module test;
  `LOGIC(signal)
  `LOGIC(signal, my_)
  `REAL(analog)
  `REAL(analog, my_, $real)
endmodule
