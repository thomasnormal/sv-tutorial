module xcheck(input logic clk, rst_n, input logic [7:0] data);

  property p_no_x;
    @(posedge clk) disable iff (!rst_n)
      // TODO: assert that data contains no X or Z bits
      ;
  endproperty

  no_x_a: assert property (p_no_x);

endmodule
