// Two legal ownership decisions followed by an idle bus.
module tb;
  logic clk = 0;
  logic [3:0] req = 4'b0, grant = 4'b0;
  logic any_grant = 0;

  always #5 clk = ~clk;

  arbiter_check dut(.clk, .req, .grant, .any_grant);

  initial begin
    @(posedge clk); #1;
    req = 4'b0010; grant = 4'b0010; any_grant = 1;
    @(posedge clk); #1;
    req = 4'b1001; grant = 4'b1000; any_grant = 1;
    @(posedge clk); #1;
    req = 4'b0000; grant = 4'b0000; any_grant = 0;
    @(posedge clk); #1;

    $display("TODO: complete grant_onehot_p and grant_idle_p, then rerun this one-owner trace.");
    $finish;
  end
endmodule
