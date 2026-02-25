module cov_cross;
  logic clk = 0;
  always #5 clk = ~clk;

  logic       we   = 0;
  logic [3:0] addr = 0;
  logic [7:0] wdata = 0, rdata;

  sram dut(.clk, .we, .addr, .wdata, .rdata);

  covergroup sram_cg @(posedge clk);
    cp_addr: coverpoint addr {
      bins lo_half = {[0:7]};
      bins hi_half = {[8:15]};
    }
    cp_we: coverpoint we {
      bins reads  = {0};
      bins writes = {1};
    }
    addr_x_we: cross cp_addr, cp_we;
  endgroup

  sram_cg cov = new;

  initial begin
    repeat (64) begin
      @(posedge clk);
      we   <= $random;
      addr <= $random;
      wdata <= $random;
    end
    #1 $finish;
  end
endmodule
