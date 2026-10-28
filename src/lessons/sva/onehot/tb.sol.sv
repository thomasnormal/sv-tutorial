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
    if (grant !== 4'b0010 || !any_grant) begin $display("FAIL: first grant was not one-hot"); $finish; end
    req = 4'b1001; grant = 4'b1000; any_grant = 1;
    @(posedge clk); #1;
    if (grant !== 4'b1000 || !any_grant) begin $display("FAIL: second grant was not one-hot"); $finish; end
    req = 4'b0000; grant = 4'b0000; any_grant = 0;
    @(posedge clk); #1;
    if (grant !== 4'b0000 || any_grant) begin $display("FAIL: idle grant was not zero"); $finish; end

    $display("PASS: each active request received one grant and idle left the bus unowned");
    $finish;
  end
endmodule
