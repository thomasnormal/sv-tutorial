module cov_bins;
  bit clk = 0;
  bit [1:0] burst;
  always #5 clk = ~clk;

  covergroup cg_burst @(posedge clk);
    coverpoint burst {
      // TODO: bins low = {2'd0, 2'd1};
      // TODO: bins high = {2'd2};
      // TODO: ignore_bins idle = {2'd3};
    }
  endgroup

  cg_burst cov = new;

  initial begin
    burst = 0;
    repeat (8) begin
      @(posedge clk);
      burst <= burst + 1'b1;
    end
    #1 $finish;
  end
endmodule
