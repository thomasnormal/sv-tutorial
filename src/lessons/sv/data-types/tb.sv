module tb;
  logic passed;

  top dut(.passed(passed));

  initial begin
    #1;
    if (passed === 1'b1) $display("PASS");
    else $display("FAIL: one or more data-type checks failed");
    $finish;
  end
endmodule
