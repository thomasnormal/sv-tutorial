// One concrete trace for the cStart -> req -> (two cycles) -> gnt sequence.
module tb;
  logic clk = 0, cStart = 0, req = 0, gnt = 0;

  always #5 clk = ~clk;

  grant_check dut(.clk, .cStart, .req, .gnt);

  initial begin
    @(posedge clk); #1;
    cStart = 1; req = 1;
    @(posedge clk); #1;
    cStart = 0; req = 0;
    @(posedge clk); #1;
    gnt = 1;
    @(posedge clk); #1;
    gnt = 0;

    $display("TODO: complete the sequence, property, and assertion, then rerun this trace.");
    $finish;
  end
endmodule
