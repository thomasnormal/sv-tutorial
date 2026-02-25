module cov_intro;
  logic clk = 0;
  always #5 clk = ~clk;

  // The SRAM we've been building — now we measure how well our test covers it
  logic       we   = 0;
  logic [3:0] addr = 0;
  logic [7:0] wdata = 0, rdata;

  sram dut(.clk, .we, .addr, .wdata, .rdata);

  // TODO: define a covergroup sram_cg that samples at posedge clk
  //       with coverpoints for addr and we, then instantiate it as 'cov'

  initial begin
    // Drive a mix of reads and writes to random addresses
    repeat (20) begin
      @(posedge clk);
      we   <= $random;
      addr <= $random;
      wdata <= $random;
    end
    #1 $finish;
  end
endmodule
