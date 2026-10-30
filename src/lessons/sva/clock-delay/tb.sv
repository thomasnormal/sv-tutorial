// One request and an acknowledgement exactly two sampled edges later.
module tb;
  logic clk = 0, mem_req = 0, mem_ack = 0;

  always #5 clk = ~clk;

  delay_check dut(.clk, .mem_req, .mem_ack);

  initial begin
    @(posedge clk); #1;
    mem_req = 1;
    @(posedge clk); #1;
    mem_req = 0; mem_ack = 0;
    @(posedge clk); #1;
    mem_ack = 1;
    @(posedge clk); #1;
    if (mem_ack !== 1) begin
      $display("FAIL: acknowledgement was not present at the two-cycle edge");
      $finish;
    end
    mem_ack = 0;

    $display("TODO: complete delayed_ack and mem_latency_p, then rerun this timing trace.");
    $finish;
  end
endmodule
