module tb;
  logic greeted;

  // The testbench drives the simulation boundary; the DUT reports its result.
  top dut(.greeted(greeted));

  initial begin
    #1;
    $display("greeted=%b (expect 1)", greeted);
    if (greeted === 1'b1) $display("PASS");
    else $display("FAIL: top did not report its greeting");
    $finish;
  end
endmodule
