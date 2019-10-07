interface simple_bus (input logic clk); // Define the interface
  logic req, gnt;
  logic [7:0] addr, data;
  logic [1:0] mode;
  logic start, rdy;
  int slaves = 0;

  // tasks executed concurrently as a fork-join block
  extern forkjoin task countSlaves();
  extern forkjoin task Read (input logic [7:0] raddr);
  extern forkjoin task Write (input logic [7:0] waddr);

  modport slave (input req,addr, mode, start, clk,
                 output gnt, rdy,
                 ref data, slaves,
                 export Read, Write, countSlaves);
    // export from module that uses the modport

  modport master ( input gnt, rdy, clk,
                   output req, addr, mode, start,
                   ref data,
                   import task Read(input logic [7:0] raddr),
                          task Write(input logic [7:0] waddr));
    // import requires the full task prototype

  initial begin
    slaves = 0;
    countSlaves;
    $display ("number of slaves = %d", slaves);
  end
endinterface: simple_bus

module memMod #(parameter int minaddr=0, maxaddr=0) (interface a);
  logic avail = 1;
  logic [7:0] mem[255:0];

  task a.countSlaves();
    a.slaves++;
  endtask

  task a.Read(input logic [7:0] raddr); // Read method
    if (raddr >= minaddr && raddr <= maxaddr) begin
      avail = 0;
      #10 a.data = mem[raddr];
      avail = 1;
    end
  endtask

  task a.Write(input logic [7:0] waddr); // Write method
    if (waddr >= minaddr && waddr <= maxaddr) begin
      avail = 0;
      #10 mem[waddr] = a.data;
      avail = 1;
    end
  endtask
endmodule

module cpuMod(interface b);
  typedef enum {read, write} instr;
  instr inst;
  logic [7:0] raddr;
  integer seed;

  always @(posedge b.clk) begin
    inst = instr'($dist_uniform(seed, 0, 1));
    raddr = $dist_uniform(seed, 0, 3);
    if (inst == read) begin
      $display("%t begin read %h @ %h", $time, b.data, raddr);
      callr:b.Read(raddr);
      $display("%t end read %h @ %h", $time, b.data, raddr);
    end
    else begin
      $display("%t begin write %h @ %h", $time, b.data, raddr);
      b.data = raddr;
      callw:b.Write(raddr);
      $display("%t end write %h @ %h", $time, b.data, raddr);
    end
  end
endmodule

module top;
  logic clk = 0;

  function void interrupt();
    disable mem1.a.Read; // task via module instance
    disable sb_intf.Write; // task via interface instance
    if (mem1.avail == 0) $display ("mem1 was interrupted");
    if (mem2.avail == 0) $display ("mem2 was interrupted");
  endfunction

  always #5 clk++;

  initial begin
    #28 interrupt();
    #10 interrupt();
    #100 $finish;
  end

  simple_bus sb_intf(clk);

  memMod #(0, 127) mem1(sb_intf.slave);
  memMod #(128, 255) mem2(sb_intf.slave);
  cpuMod cpu(sb_intf.master);
endmodule
