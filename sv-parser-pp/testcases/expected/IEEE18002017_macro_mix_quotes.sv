/* IEEE1800-2017 Clause 22.5.1 page 680
*/

`define msg(x,y) `"x: `\`"y`\`"`"

module a;
initial begin
$display("left side: \"right side\"");
end
endmodule
