// One start pulse followed by three consecutive busy samples.
module tb;
  logic clk = 0, start = 0, busy = 0;

  always #5 clk = ~clk;

  hold_check dut(.clk, .start, .busy);

  initial begin
    @(posedge clk); #1;
    start = 1;
    @(posedge clk); #1;
    start = 0; busy = 1;
    @(posedge clk); #1;
    @(posedge clk); #1;
    @(posedge clk); #1;
    if (busy !== 1) begin
      $display("FAIL: busy was not high on the third consecutive sample");
      $finish;
    end
    busy = 0;

    $display("TODO: complete busy_run and busy_hold_p, then rerun this repetition trace.");
    $finish;
  end
endmodule
