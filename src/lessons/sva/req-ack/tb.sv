// A request rises once; the acknowledgement arrives on the third legal edge.
module tb;
  logic clk = 0, req = 0, ack = 0;

  always #5 clk = ~clk;

  req_ack dut(.clk, .req, .ack);

  initial begin
    @(posedge clk); #1;
    req = 1;
    @(posedge clk); #1;
    req = 0; ack = 0;
    @(posedge clk); #1;
    ack = 0;
    @(posedge clk); #1;
    ack = 1;
    @(posedge clk); #1;
    if (ack !== 1) begin
      $display("FAIL: ack was not high on the third legal response edge");
      $finish;
    end
    ack = 0;

    $display("TODO: complete ack_window and req_ack_p, then rerun this handshake trace.");
    $finish;
  end
endmodule
