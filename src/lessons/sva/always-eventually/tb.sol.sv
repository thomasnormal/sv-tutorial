module tb;
  logic clk = 0, rst_n = 0, lock = 0;
  int fail = 0;

  always #5 clk = ~clk;
  liveness dut(.clk, .rst_n, .lock);

  initial begin
    @(posedge clk); #1;
    rst_n = 0;
    lock = 0;
    @(posedge clk); #1;
    rst_n = 1;
    lock = 0;
    @(posedge clk); #1;
    lock = 1;
    repeat (3) @(posedge clk);
    #1;
    $display("lock trace: rst_n=%0b lock=%0b (expect 1,1)", rst_n, lock);
    if (rst_n !== 1 || lock !== 1) begin
      $display("FAIL: lock did not arrive and remain asserted");
      fail++;
    end

    if (fail == 0) $display("PASS: lock eventually arrived and stayed high");
    else $display("FAIL: %0d liveness trace checks were wrong", fail);
    $finish;
  end
endmodule
