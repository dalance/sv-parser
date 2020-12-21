module a;
`define HELLO0 "HELLO"
`define \HELLO1 "HELLO"
initial begin
$display(`HELLO0);
$display(`\HELLO0 );
$display(`HELLO1);
$display(`\HELLO1 );
end
endmodule
