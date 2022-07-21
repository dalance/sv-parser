/* IEEE1800-2017 Clause 22.5.1 page 677
* NOTE: Illegal cases are not included in this testcase.
*/

`define D(x,y) initial $display("start", x , y, "end");

module m;
initial begin
  `D( "msg1" , "msg2" )
  `D( " msg1", )
  `D(, "msg2 ")
  `D(,)
  `D( , )
end
endmodule
