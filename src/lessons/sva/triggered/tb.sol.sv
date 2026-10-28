// A request leaves its busy phase, then receives an acknowledgement.
module tb;
  logic clk = 0, req = 0, busy = 0, ack = 0;

  always #5 clk = ~clk;

  trigger_check dut(.clk, .req, .busy, .ack);

  initial begin
    @(posedge clk); #1;
    req = 1; busy = 1; ack = 0;
    @(posedge clk); #1;
    req = 0; busy = 0; ack = 0;
    @(posedge clk); #1;
    ack = 1;
    @(posedge clk); #1;
    if (ack !== 1) begin
      $display("FAIL: ack did not arrive after the sequence endpoint");
      $finish;
    end

    $display("PASS: .triggered opened the response window after req ##1 !busy");
    $finish;
  end
endmodule
