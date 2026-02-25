// sram_core — a synchronous 16-byte memory.
// All reads and writes are edge-triggered: state only changes at posedge clk.
//
// Port directions: every module port must be declared as one of:
//   input  — data flows into this module from outside
//   output — data flows out of this module to the rest of the design
//   inout  — bidirectional (rare; used for tri-state buses)
module sram_core (
  input  logic       clk,    // clock: all state updates happen on the rising edge
  input  logic       we,     // write-enable: 1 = write wdata to mem[addr] this cycle
  input  logic [3:0] addr,   // address: selects which of the 16 bytes to access (0..15)
  input  logic [7:0] wdata,  // write data: stored in mem[addr] when we = 1
  output logic [7:0] rdata   // read data: contains mem[addr] from the previous cycle
);
  // Memory array: 16 entries, each 8 bits wide.
  // Syntax: logic [WIDTH-1:0] name [0:DEPTH-1]
  logic [7:0] mem [0:15];

  // @(posedge clk): this block evaluates only on the rising edge of clk —
  // the moment clk transitions from 0 to 1. Between edges all registers hold
  // their values. This is what makes the logic "sequential" (clock-driven)
  // rather than "combinational" (always reacting to input changes).
  always_ff @(posedge clk) begin
    // TODO: if we is high, write wdata into mem[addr]
    rdata <= '0; // TODO: replace with mem[addr] (this creates 1-cycle read latency)
  end
endmodule
