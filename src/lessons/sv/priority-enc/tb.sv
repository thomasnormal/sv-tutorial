module tb;
  logic [3:0] req;
  logic [1:0] grant;
  logic       valid;
  int         fail = 0;

  priority_enc dut(.req, .grant, .valid);

  initial begin
    // No request: no winner.
    req = 4'b0000; #1;
    $display("req=%b -> valid=%b grant=%0d (expect 0, 0)", req, valid, grant);
    if (valid !== 1'b0 || grant !== 2'd0) fail++;

    // Single requests establish the encoding: bit 0..3 map to grant 0..3.
    req = 4'b0001; #1;
    $display("req=%b -> valid=%b grant=%0d (expect 1, 0)", req, valid, grant);
    if (valid !== 1'b1 || grant !== 2'd0) fail++;
    req = 4'b0010; #1;
    $display("req=%b -> valid=%b grant=%0d (expect 1, 1)", req, valid, grant);
    if (valid !== 1'b1 || grant !== 2'd1) fail++;
    req = 4'b0100; #1;
    $display("req=%b -> valid=%b grant=%0d (expect 1, 2)", req, valid, grant);
    if (valid !== 1'b1 || grant !== 2'd2) fail++;
    req = 4'b1000; #1;
    $display("req=%b -> valid=%b grant=%0d (expect 1, 3)", req, valid, grant);
    if (valid !== 1'b1 || grant !== 2'd3) fail++;

    // Multiple requests demonstrate the priority: the highest bit wins.
    req = 4'b0111; #1;
    $display("req=%b -> valid=%b grant=%0d (expect 1, 2)", req, valid, grant);
    if (valid !== 1'b1 || grant !== 2'd2) fail++;
    req = 4'b1010; #1;
    $display("req=%b -> valid=%b grant=%0d (expect 1, 3)", req, valid, grant);
    if (valid !== 1'b1 || grant !== 2'd3) fail++;
    req = 4'b1111; #1;
    $display("req=%b -> valid=%b grant=%0d (expect 1, 3)", req, valid, grant);
    if (valid !== 1'b1 || grant !== 2'd3) fail++;

    if (fail == 0) $display("PASS");
    else $display("FAIL: %0d priority cases were wrong", fail);
    $finish;
  end
endmodule
