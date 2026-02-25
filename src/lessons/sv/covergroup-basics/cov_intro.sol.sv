module cov_intro;
  logic clk = 0;
  always #5 clk = ~clk;

  logic       we   = 0;
  logic [3:0] addr = 0;
  logic [7:0] wdata = 0, rdata;

  sram dut(.clk, .we, .addr, .wdata, .rdata);

  covergroup sram_cg @(posedge clk);
    cp_addr: coverpoint addr;
    cp_we:   coverpoint we;
  endgroup

  sram_cg cov = new;

  initial begin
    repeat (20) begin
      @(posedge clk);
      we   <= $random;
      addr <= $random;
      wdata <= $random;
    end
    #1 $finish;
  end
endmodule
