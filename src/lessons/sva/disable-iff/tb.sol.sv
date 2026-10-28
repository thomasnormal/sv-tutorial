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

    $display("PASS: reset disabled the first request and the active request received ack");
    $finish;
  end
endmodule
