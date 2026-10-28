module tb;
  logic clk = 0;
  logic rst_n = 0;
  logic en = 0;
  logic [7:0] count;
  int fail = 0;

  counter dut(.*);
  always #5 clk = ~clk;

  initial begin
    @(posedge clk); #1;
    if (count !== 8'd0) fail++;

    rst_n = 1;
    en = 1;
    repeat (4) @(posedge clk);
    #1;
    $display("counting: count=%0d (expect 4)", count);
    if (count !== 8'd4) fail++;

    en = 0;
    repeat (2) @(posedge clk);
    #1;
    $display("holding: count=%0d (expect 4)", count);
    if (count !== 8'd4) fail++;

    rst_n = 0;
    @(posedge clk); #1;
    $display("reset: count=%0d (expect 0)", count);
    if (count !== 8'd0) fail++;

    if (fail == 0) $display("PASS");
    else $display("FAIL: %0d bound-counter checks were wrong", fail);
    $finish;
  end
endmodule
