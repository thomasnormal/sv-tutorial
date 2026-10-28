// A request during reset is ignored; the post-reset request must be acknowledged.
module tb;
  logic clk = 0, rst_n = 0, req = 0, ack = 0;

  always #5 clk = ~clk;

  reset_check dut(.clk, .rst_n, .req, .ack);

  initial begin
    @(posedge clk); #1;
    rst_n = 0; req = 1; ack = 0;
    @(posedge clk); #1;
    rst_n = 1; req = 1; ack = 0;
    @(posedge clk); #1;
    req = 0; ack = 1;
    @(posedge clk); #1;
    rst_n = 0; ack = 0;
    @(posedge clk); #1;

    $display("TODO: complete ack_next and req_ack_p, then rerun this reset-gated trace.");
    $finish;
  end
endmodule
