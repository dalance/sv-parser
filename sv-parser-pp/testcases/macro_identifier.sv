module a;
`define A "aaa"
`define \B "bbb"
initial begin
$display(`A);
$display(`\A );
$display(`B);
$display(`\B );
end
endmodule
