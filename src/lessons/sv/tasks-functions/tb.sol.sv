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

  sram dut(
    .clk   (vif.clk),
    .we    (vif.we),
    .addr  (vif.addr),
    .wdata (vif.wdata),
    .rdata (vif.rdata)
  );

  function automatic logic parity_check(input logic [7:0] d);
    return ^d;
  endfunction

  task automatic write_word(input logic [3:0] a, input logic [7:0] data);
    vif.we = 1; vif.addr = a; vif.wdata = data;
    @(posedge vif.clk); #1;
    vif.we = 0;
  endtask

  task automatic read_word(input  logic [3:0] a, output logic [7:0] data);
    vif.addr = a;
    @(posedge vif.clk); #1;
    data = vif.rdata;
  endtask

  int fail = 0;

  initial begin
    logic [7:0] result;

    write_word(4'd5, 8'd42);
    read_word (4'd5, result);
    $display("mem[5] = %0d  parity=%b (expect 42, parity=%b)",
             result, parity_check(result), ^8'd42);
    if (result !== 8'd42 || parity_check(result) !== ^8'd42) fail++;

    write_word(4'd0, 8'hFF);
    read_word (4'd0, result);
    $display("mem[0] = %0d  parity=%b (expect 255, parity=%b)",
             result, parity_check(result), ^8'hFF);
    if (result !== 8'hFF || parity_check(result) !== ^8'hFF) fail++;

    write_word(4'd12, 8'd100);
    read_word (4'd12, result);
    $display("mem[12] = %0d  parity=%b (expect 100, parity=%b)",
             result, parity_check(result), ^8'd100);
    if (result !== 8'd100 || parity_check(result) !== ^8'd100) fail++;

    if (fail == 0) $display("PASS");
    $finish;
  end
endmodule
