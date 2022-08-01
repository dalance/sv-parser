/* IEEE1800-2017 Clause 22.5.1 page 679
*/

`define max(a,b)((a) > (b) ? (a) : (b))
`define TOP(a,b) a + b

module m;
assign n = `max(p+q, r+s) ;
assign z = `TOP( `TOP(b,1), `TOP(42,a) );
endmodule
