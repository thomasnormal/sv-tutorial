// One active-low chip-select edge followed by an acknowledgement rising edge.
module tb;
  logic clk = 0, cs_n = 1, ack = 0;

  always #5 clk = ~clk;

  edge_check dut(.clk, .cs_n, .ack);

  initial begin
    @(posedge clk); #1;
    cs_n = 0;
    @(posedge clk); #1;
    cs_n = 1; ack = 1;
    @(posedge clk); #1;
    if (ack !== 1) begin
      $display("FAIL: ack did not rise on the first legal response edge");
      $finish;
    end
    ack = 0;

    $display("TODO: complete ack_rise and cs_ack_p, then rerun this edge trace.");
    $finish;
  end
endmodule
