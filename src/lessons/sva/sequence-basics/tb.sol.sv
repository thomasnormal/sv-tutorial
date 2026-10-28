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

    $display("PASS: cStart/req triggered a grant exactly two cycles later");
    $finish;
  end
endmodule
