module xcheck(
  input  logic       clk, rst_n,
  input  logic       we,
  input  logic [3:0] addr,
  input  logic [7:0] rdata
);

  // All three SRAM output signals must be known (not X, not Z) after reset.
  // $isunknown(expr) returns 1 if ANY bit of expr is X or Z.

  property p_no_x_we;
    @(posedge clk) disable iff (!rst_n)
      // TODO 1: we must never be X or Z
      ;
  endproperty

  property p_no_x_addr;
    @(posedge clk) disable iff (!rst_n)
      // TODO 2: addr must never contain X or Z
      ;
  endproperty

  property p_no_x_rdata;
    @(posedge clk) disable iff (!rst_n)
      // TODO 3: rdata must never contain X or Z
      ;
  endproperty

  we_a:    assert property (p_no_x_we);
  addr_a:  assert property (p_no_x_addr);
  rdata_a: assert property (p_no_x_rdata);

endmodule
