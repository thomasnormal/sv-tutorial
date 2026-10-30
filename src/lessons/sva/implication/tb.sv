// One request with ack high on the same edge and the following edge.
module tb;
  logic clk = 0, req = 0, ack = 0;

  always #5 clk = ~clk;

  implication dut(.clk, .req, .ack);

  initial begin
    @(posedge clk); #1;
    req = 1; ack = 1;
    @(posedge clk); #1;
    req = 0; ack = 1;
    @(posedge clk); #1;
    ack = 0;

    $display("TODO: complete |-> and |=>, then rerun this same-edge/next-edge trace.");
    $finish;
  end
endmodule
