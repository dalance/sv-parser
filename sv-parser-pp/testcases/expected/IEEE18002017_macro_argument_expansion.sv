/* IEEE1800-2017 Clause 22.5.1 page 679
*/

`define max(a,b)((a) > (b) ? (a) : (b))
`define TOP(a,b) a + b

module m;
assign n = ((p+q) > (r+s) ? (p+q) : (r+s)) ;
assign z = b + 1 + 42 + a;
endmodule
