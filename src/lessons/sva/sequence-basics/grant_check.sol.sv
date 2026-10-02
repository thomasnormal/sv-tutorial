module grant_check(input logic clk, cStart, req, gnt);

  sequence sr1;
    req ##2 gnt;
  endsequence

  property pr1;
    @(posedge clk) cStart |-> sr1;
  endproperty

  reqGnt: assert property (pr1);

endmodule
