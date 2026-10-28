// Three separated acknowledgement pulses, then a deliberately late done.
module tb;
  logic clk = 0, start = 0, ack = 0, done = 0;

  always #5 clk = ~clk;

  multi_ack2 dut(.clk, .start, .ack, .done);

  initial begin
    @(posedge clk); #1;
    start = 1;
    @(posedge clk); #1;
    start = 0; ack = 0; done = 0;
    @(posedge clk); #1;
    ack = 1;
    @(posedge clk); #1;
    ack = 0;
    @(posedge clk); #1;
    ack = 1;
    @(posedge clk); #1;
    ack = 0;
    @(posedge clk); #1;
    ack = 1;
    @(posedge clk); #1;
    ack = 0; done = 0;
    @(posedge clk); #1;
    done = 1;
    @(posedge clk); #1;
    if (done !== 1) begin
      $display("FAIL: done did not arrive after the third ack pulse");
      $finish;
    end
    done = 0;

    $display("TODO: complete ack_burst and three_acks_p, then rerun this variable-latency trace.");
    $finish;
  end
endmodule
