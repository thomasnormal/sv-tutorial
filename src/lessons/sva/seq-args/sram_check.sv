module sram_check (
  input  logic        clk, we,
  input  logic [3:0]  addr,
  input  logic [7:0]  wdata,
  output logic [7:0]  rdata
);

  // Inline SRAM model with combinational read
  logic [7:0] mem [0:15];
  always_ff @(posedge clk) if (we) mem[addr] <= wdata;
  assign rdata = mem[addr];

  // Named sequences with formal arguments act like reusable templates:
  // 'a' and 'd' are placeholders replaced with the actual value at every call site.

  // TODO: fill in the write_txn body
  // Spec: we is asserted, addr equals a, and wdata equals d
  sequence write_txn(logic [3:0] a, logic [7:0] d);

  endsequence

  // TODO: fill in the read_txn body
  // Spec: addr equals a and rdata equals d
  // (no we check — combinational read returns the value regardless of we)
  sequence read_txn(logic [3:0] a, logic [7:0] d);

  endsequence

  // TODO: fill in the property body
  // Spec: after write_txn(a, d) fires, one cycle later: if addr matches a, read_txn must hold
  property wr_rd_p(logic [3:0] a, logic [7:0] d);

  endproperty

  // TODO: assert wr_rd_p for two address/data scenarios:
  //   addr0_check:  address 4'd0, data 8'hA5
  //   addr15_check: address 4'hF, data 8'hFF

endmodule
