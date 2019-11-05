module a;
`define HI Hello
`define LO "`HI, world"
`define H(x) "Hello, x"
initial begin
$display("`HI, world");
$display(`LO);
$display(`H(world));
end
endmodule
