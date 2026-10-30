module tb;
  logic clk = 0;
  logic valid = 0;
  logic ready = 0;
  // Seed the payload before valid rises so the first held sample is stable.
  logic [7:0] data = 8'h31;
  int fail = 0;

  let_check dut(.*);
  always #5 clk = ~clk;

  initial begin
    @(posedge clk); #1;
    valid = 1;
    ready = 0;
    @(posedge clk); #1;
    $display("held bus: data=%h (expect 31)", data);
    if (data !== 8'h31) fail++;

    // A ready handshake permits the next value to change.
    ready = 1;
    data = 8'hA6;
    @(posedge clk); #1;
    $display("accepted bus: data=%h (expect A6)", data);
    if (data !== 8'hA6) fail++;

    valid = 0;
    ready = 0;
    data = 8'h5C;
    @(posedge clk); #1;
    $display("invalid bus: data=%h (expect 5C)", data);
    if (data !== 8'h5C) fail++;

    if (fail == 0) $display("TODO: define hold_bus and use it in data_stable_p, then rerun this held-bus trace.");
    else $display("FAIL: %0d bus-trace checks were wrong", fail);
    $finish;
  end
endmodule
