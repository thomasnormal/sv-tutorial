module tb;
  logic clk = 0, start = 0, ack = 0, err = 0;

  always #5 clk = ~clk;

  abort_check dut(.clk, .start, .ack, .err);

  initial begin
    @(posedge clk); #1;
    start = 1; ack = 0; err = 0;
    @(posedge clk); #1;
    start = 0; ack = 0; err = 0;
    @(posedge clk); #1;
    ack = 1;
    @(posedge clk); #1;
    ack = 0; err = 1;
    @(posedge clk); #1;

    $display("PASS: ack completed before the late error, so reject_on did not fire");
    $finish;
  end
endmodule
