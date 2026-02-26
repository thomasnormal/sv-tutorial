module tb;
  logic       clk = 0;
  always #5 clk = ~clk;   // clock toggles every 5 time units

  logic [3:0] req;
  logic [1:0] grant;
  logic       valid;

  int fail = 0;

  priority_enc dut(.req, .grant, .valid);

  initial begin
    // Set input, wait for the next rising clock edge, then sample outputs
    req = 4'b0000; @(posedge clk);
    $display("req=%b → grant=%0d valid=%b (expect valid=0)", req, grant, valid);
    if (valid !== 1'b0) fail++;
    req = 4'b0001; @(posedge clk);
    $display("req=%b → grant=%0d valid=%b (expect grant=0)", req, grant, valid);
    if (grant !== 2'd0 || valid !== 1'b1) fail++;
    req = 4'b0110; @(posedge clk);
    $display("req=%b → grant=%0d valid=%b (expect grant=2)", req, grant, valid);
    if (grant !== 2'd2 || valid !== 1'b1) fail++;
    req = 4'b1010; @(posedge clk);
    $display("req=%b → grant=%0d valid=%b (expect grant=3)", req, grant, valid);
    if (grant !== 2'd3 || valid !== 1'b1) fail++;
    if (fail == 0) $display("PASS");
    $finish;
  end
endmodule
