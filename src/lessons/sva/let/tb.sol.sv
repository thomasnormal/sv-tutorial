module tb;
  logic clk = 0;
  logic valid = 0;
  logic ready = 0;
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
    if (data !== 8'h31) begin
      $display("FAIL: held payload changed while waiting");
      fail++;
    end

    // A ready handshake permits the next value to change.
    ready = 1;
    data = 8'hA6;
    @(posedge clk); #1;
    $display("accepted bus: data=%h (expect A6)", data);
    if (data !== 8'hA6) begin
      $display("FAIL: accepted payload did not advance");
      fail++;
    end

    valid = 0;
    ready = 0;
    data = 8'h5C;
    @(posedge clk); #1;
    $display("invalid bus: data=%h (expect 5C)", data);
    if (data !== 8'h5C) begin
      $display("FAIL: invalid payload was unexpectedly held");
      fail++;
    end

    if (fail == 0) $display("PASS: let hold_bus guarded only the valid, unaccepted phase");
    else $display("FAIL: %0d let-expression checks were wrong", fail);
    $finish;
  end
endmodule
