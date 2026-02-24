module grant_check(input logic clk, cStart, req, gnt);

  sequence sr1;
    req ##2 gnt;
  endsequence

  property pr1;
    @(posedge clk) cStart |-> sr1;
  endproperty

  reqGnt: assert property (pr1)
    $display("PASS at %0t", $time);
  else
    $display("FAIL at %0t", $time);

endmodule
