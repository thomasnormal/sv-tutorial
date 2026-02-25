// Testbench for sram_core.
// Writes three values to different addresses, then reads them back.
// Registered reads have 1-cycle latency: drive addr on cycle N,
// rdata reflects that address on cycle N+1.
module tb;
  logic       clk = 0;   // driven by always block below
  logic       we  = 0;   // write-enable
  logic [3:0] addr  = 0; // byte address (0..15)
  logic [7:0] wdata = 0; // data to write
  logic [7:0] rdata;     // data read out — valid 1 cycle after addr

  // Clock generator: period = 10 time units
  always #5 clk = ~clk;

  // Connect all ports by name (shorthand: .port matches variable of same name)
  sram_core dut(.*);

  // Write one byte: assert we, drive addr/wdata, wait for rising edge
  task do_write(input [3:0] a, input [7:0] d);
    we = 1; addr = a; wdata = d;
    @(posedge clk); #1;
    we = 0;
  endtask

  // Read one byte and check result; print PASS or FAIL
  task do_read(input [3:0] a, input [7:0] expected);
    addr = a; @(posedge clk); #1;
    if (rdata === expected)
      $display("PASS  mem[%0d] = %0d", a, rdata);
    else
      $display("FAIL  mem[%0d] = %0d  (expected %0d)", a, rdata, expected);
  endtask

  initial begin
    do_write(4'd2, 8'd42);
    do_write(4'd7, 8'd99);
    do_write(4'd0, 8'd13);

    do_read(4'd2, 8'd42);
    do_read(4'd7, 8'd99);
    do_read(4'd0, 8'd13);

    $finish;
  end
endmodule
