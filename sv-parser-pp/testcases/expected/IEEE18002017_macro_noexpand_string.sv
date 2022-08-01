/* IEEE1800-2017 Clause 22.5.1 page 679
*/

module main;
`define HI Hello
`define LO "`HI, world"
`define H(x) "Hello, x"
initial begin
  $display("`HI, world");
  $display("`HI, world");
  $display("Hello, x");
end
endmodule
