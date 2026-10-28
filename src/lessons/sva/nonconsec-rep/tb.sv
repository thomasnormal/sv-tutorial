// Three separated acknowledgement pulses, followed by done on the next edge.
module tb;
  logic clk = 0, req = 0, ack = 0, done = 0;

  always #5 clk = ~clk;

  multi_ack dut(.clk, .req, .ack, .done);

  initial begin
    @(posedge clk); #1;
    req = 1;
    @(posedge clk); #1;
    req = 0; ack = 0; done = 0;
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
    ack = 0; done = 1;
    @(posedge clk); #1;
    if (done !== 1) begin
      $display("FAIL: done was not high after the third ack pulse");
      $finish;
    end
    done = 0;

    $display("TODO: complete three_acks and three_acks_p, then rerun this gapped pulse trace.");
    $finish;
  end
endmodule
