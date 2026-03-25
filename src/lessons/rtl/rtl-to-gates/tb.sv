module tb;
  logic clk = 0;
  logic sel;
  logic [7:0] a, b, q;

  mux_reg dut (.clk, .sel, .a, .b, .q);

  always #5 clk = ~clk;

  initial begin
    a = 8'hA5; b = 8'h5A;

    sel = 0; @(posedge clk); #1;
    if (q !== 8'hA5) begin $display("FAIL: sel=0 expected 0xA5, got 0x%02h", q); $finish; end

    sel = 1; @(posedge clk); #1;
    if (q !== 8'h5A) begin $display("FAIL: sel=1 expected 0x5A, got 0x%02h", q); $finish; end

    $display("PASS");
    $finish;
  end
endmodule
