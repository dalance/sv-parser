`define disp(clk, exp, msg) \
    always @(posedge clk) begin \
        if (!(exp)) begin \
            $display msg; \
        end \
    end \

module a ();

always @(posedge clk) begin 
        if (!(!(a[i].b && c[i]))) begin 
            $display ("xxx(()[]]{}}}", a[i].b, c[i]); 
        end 
    end 
 ;

endmodule
