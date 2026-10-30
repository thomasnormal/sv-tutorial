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

    $display("PASS: $fell(cs_n) was followed by $rose(ack) in the legal window");
    $finish;
  end
endmodule
