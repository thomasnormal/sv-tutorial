// Two writes and reads exercise both formal-argument call sites.
module tb;
  logic clk = 0, we = 0;
  logic [3:0] addr = 0;
  logic [7:0] wdata = 0;
  logic [7:0] rdata;

  always #5 clk = ~clk;

  sram_check dut(.clk, .we, .addr, .wdata, .rdata);

  initial begin
    @(posedge clk); #1;
    we = 1; addr = 4'd0; wdata = 8'hA5;
    @(posedge clk); #1;
    we = 0; addr = 4'd0;
    @(posedge clk); #1;
    if (rdata !== 8'hA5) begin $display("FAIL: address 0 readback was wrong"); $finish; end

    we = 1; addr = 4'hF; wdata = 8'hFF;
    @(posedge clk); #1;
    we = 0; addr = 4'hF;
    @(posedge clk); #1;
    if (rdata !== 8'hFF) begin $display("FAIL: address F readback was wrong"); $finish; end

    $display("TODO: complete the formal sequence arguments, then rerun these SRAM transactions.");
    $finish;
  end
endmodule
