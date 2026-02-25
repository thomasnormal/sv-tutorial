module cov_bins;
  logic clk = 0;
  always #5 clk = ~clk;

  logic       we   = 0;
  logic [3:0] addr = 0;
  logic [7:0] wdata = 0, rdata;

  sram dut(.clk, .we, .addr, .wdata, .rdata);

  covergroup sram_cg @(posedge clk);
    cp_addr: coverpoint addr {
      // TODO: add bins for lo_half (0–7) and hi_half (8–13)
      // TODO: use ignore_bins to exclude reserved addresses 14 and 15
    }
    cp_we: coverpoint we {
      bins reads  = {0};
      bins writes = {1};
    }
  endgroup

  sram_cg cov = new;

  initial begin
    repeat (32) begin
      @(posedge clk);
      we   <= $random;
      addr <= $random;
      wdata <= $random;
    end
    #1 $finish;
  end
endmodule
