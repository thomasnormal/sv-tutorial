module xcheck(
  input  logic       clk, rst_n,
  input  logic       we,
  input  logic [3:0] addr,
  input  logic [7:0] rdata
);

  property p_no_x_we;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(we);
  endproperty

  property p_no_x_addr;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(addr);
  endproperty

  property p_no_x_rdata;
    @(posedge clk) disable iff (!rst_n)
      !$isunknown(rdata);
  endproperty

  we_a:    assert property (p_no_x_we);
  addr_a:  assert property (p_no_x_addr);
  rdata_a: assert property (p_no_x_rdata);

endmodule
