module spi_check(input logic clk, cs_n, mosi);

  property p_cs_stable;
    @(posedge clk) $fell(cs_n) |=> (!cs_n) throughout (1'b1[*8]);
  endproperty

  cs_stable_a: assert property (p_cs_stable);

endmodule
