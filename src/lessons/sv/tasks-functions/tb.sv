interface mem_if (input logic clk);
  logic        we;
  logic [3:0]  addr;
  logic [7:0]  wdata;
  logic [7:0]  rdata;
endinterface

module tb;
  logic clk = 0;
  always #5 clk = ~clk;

  mem_if vif(.clk(clk));

  // The SRAM from Part 1 — the tasks below drive it through the interface
  sram dut(
    .clk   (vif.clk),
    .we    (vif.we),
    .addr  (vif.addr),
    .wdata (vif.wdata),
    .rdata (vif.rdata)
  );

  // A function returns a value immediately — no simulation time consumed.
  function automatic logic parity_check(input logic [7:0] d);
    // TODO: return 1 if d has an odd number of set bits (reduction XOR)
  endfunction

  // A task can wait for clock edges — it drives the SRAM bus protocol.
  task automatic write_word(input logic [3:0] a, input logic [7:0] data);
    // TODO: drive vif.we=1, vif.addr, vif.wdata for one rising edge, then de-assert we
  endtask

  task automatic read_word(input  logic [3:0] a, output logic [7:0] data);
    // TODO: set vif.addr, wait one rising edge, capture vif.rdata into data
  endtask

  initial begin
    logic [7:0] result;
    write_word(4'd5, 8'd42);
    read_word (4'd5, result);
    $display("mem[5] = %0d  parity=%b (expect 42, parity=%b)",
             result, parity_check(result), ^8'd42);
    $finish;
  end
endmodule
