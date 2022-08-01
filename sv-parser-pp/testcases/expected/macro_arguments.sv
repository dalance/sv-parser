// Macro with parameters with usage spread over multiple lines.
// Final line of macro is line14.
// Argument value `clk` is equal to its name.
// Argument value of exp contains matching brackets and parentheses.
// Bracketed value of msg is required to avoid being parsed as a parameterized
// macro instead of argumnts to $display.
// NOTE: Trailing whitespace is not exercised here, i.e. continuations
// immediately follow non-whitespace.
`define disp(clk, exp, msg)\
  always @(posedge clk)\
    if (exp) begin\
      $display msg;\
    end\

module M ();

  always @(posedge clk)
    if (!(a[i].b && c[i])) begin
      $display ("xxx(()[]]{}}}", a[i].b, c[i]);
    end
; // NOTE: Semi-colon is unnecessary.

endmodule
