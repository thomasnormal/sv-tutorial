module tb;
  logic clk = 0;
  always #5 clk = ~clk;

  logic rst_n = 0;
  logic req = 0;
  logic ack = 0;
  logic grant, done, busy;
  int fail = 0;

  mealy_ctrl dut(.*);

  initial begin
    // Hold reset for a complete edge so the state starts at IDLE.
    @(posedge clk); #1;
    rst_n = 1;

    $display("IDLE without request: grant=%b busy=%b (expect 0, 0)", grant, busy);
    if (grant !== 1'b0 || busy !== 1'b0) fail++;

    // A Mealy output responds to req before the next clock edge.
    req = 1;
    #1;
    $display("IDLE with request: grant=%b busy=%b (expect 1, 0)", grant, busy);
    if (grant !== 1'b1 || busy !== 1'b0) fail++;

    @(posedge clk); #1;
    req = 0;
    $display("BUSY after accept: grant=%b busy=%b (expect 0, 1)", grant, busy);
    if (grant !== 1'b0 || busy !== 1'b1) fail++;

    // done is also a Mealy output: ack is visible while BUSY.
    ack = 1;
    #1;
    $display("BUSY with ack: done=%b busy=%b (expect 1, 1)", done, busy);
    if (done !== 1'b1 || busy !== 1'b1) fail++;

    @(posedge clk); #1;
    ack = 0;
    $display("IDLE after done: grant=%b done=%b busy=%b (expect 0, 0, 0)",
             grant, done, busy);
    if (grant !== 1'b0 || done !== 1'b0 || busy !== 1'b0) fail++;

    // Toggling req again changes grant without another clock.
    req = 1;
    #1;
    if (grant !== 1'b1) fail++;
    req = 0;
    #1;
    if (grant !== 1'b0) fail++;

    if (fail == 0) $display("PASS");
    else $display("FAIL: %0d Mealy FSM checks were wrong", fail);
    $finish;
  end
endmodule
