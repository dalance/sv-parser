/* IEEE1800-2017 Clause 22.5.1 page 677
* NOTE: Illegal cases are not included in this testcase.
*/

`define D(x,y) initial $display("start", x , y, "end");

module m;
  initial $display("start", "msg1"  , "msg2", "end");
  initial $display("start", " msg1"  , , "end");
  initial $display("start",  , "msg2 ", "end");
  initial $display("start",  , , "end");
  initial $display("start",  , , "end");
endmodule
