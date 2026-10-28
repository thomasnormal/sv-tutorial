module tb;
  logic clk = 0;
  logic burst_start = 0;
  logic burst_beat = 0;
  logic data_ok = 0;
  int fail = 0;

  top dut(.*);
  always #5 clk = ~clk;

  initial begin
    // A three-sample burst: start, beat, beat.  Keep data_ok high through
    // both the endpoint and the following sample for the two followed-by forms.
    @(posedge clk); #1;
    burst_start = 1; burst_beat = 0; data_ok = 0;
    $display("cycle 0 (start): burst_start=%0b burst_beat=%0b data_ok=%0b", burst_start, burst_beat, data_ok);
    if (burst_start !== 1 || burst_beat !== 0 || data_ok !== 0) fail++;

    @(posedge clk); #1;
    burst_start = 0; burst_beat = 1; data_ok = 1;
    $display("cycle 1 (first beat): burst_start=%0b burst_beat=%0b data_ok=%0b", burst_start, burst_beat, data_ok);
    if (burst_start !== 0 || burst_beat !== 1 || data_ok !== 1) fail++;

    @(posedge clk); #1;
    burst_beat = 1; data_ok = 1;
    $display("cycle 2 (sequence endpoint): burst_start=%0b burst_beat=%0b data_ok=%0b  <-- #-#", burst_start, burst_beat, data_ok);
    if (burst_start !== 0 || burst_beat !== 1 || data_ok !== 1) fail++;

    @(posedge clk); #1;
    burst_beat = 0; data_ok = 1;
    $display("cycle 3 (next sample): burst_start=%0b burst_beat=%0b data_ok=%0b  <-- #=#", burst_start, burst_beat, data_ok);
    if (burst_start !== 0 || burst_beat !== 0 || data_ok !== 1) fail++;

    if (fail == 0) $display("TODO: complete burst_read and the three followed-by properties, then rerun this trace.");
    else $display("FAIL: %0d followed-by timing checks were wrong", fail);
    $finish;
  end
endmodule
