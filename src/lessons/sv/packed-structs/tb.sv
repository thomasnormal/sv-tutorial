import mem_pkg::*;

module tb;
  logic clk = 0;
  always #5 clk = ~clk;

  mem_cmd_t cmd = '0;
  logic [7:0] rdata;

  sram_cmd dut(.clk, .cmd, .rdata);

  initial begin
    // Struct literal write
    cmd = '{we: 1'b1, addr: 4'd3, wdata: 8'd55};
    @(posedge clk); #1;

    // Raw bit assignment write — we=1, addr=5, wdata=77 packed as 13'b1_0101_01001101
    cmd = 13'b1_0101_01001101;
    @(posedge clk); #1;

    // Read back addr 3
    cmd = '{we: 1'b0, addr: 4'd3, wdata: '0};
    @(posedge clk); #1;
    $display("mem[3] = %0d (expect 55)", rdata);

    // Read back addr 5
    cmd.addr = 4'd5;
    @(posedge clk); #1;
    $display("mem[5] = %0d (expect 77)", rdata);

    $finish;
  end
endmodule
