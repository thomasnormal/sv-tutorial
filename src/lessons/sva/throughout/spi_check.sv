module spi_check(input logic clk, cs_n, mosi);

  property p_cs_stable;
    @(posedge clk)
      // TODO: when cs_n falls, cs_n must stay low throughout an 8-cycle MOSI transfer
      ;
  endproperty

  cs_stable_a: assert property (p_cs_stable);

endmodule
