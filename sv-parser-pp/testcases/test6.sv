`define msg(x,y) `"x: `\`"y`\`"`"

module a;
initial begin
$display(`msg(left side,right side));
end
endmodule
