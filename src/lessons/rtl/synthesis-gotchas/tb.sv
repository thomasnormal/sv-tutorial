module tb;
  logic [1:0] sel;
  logic [3:0] y;

  decoder dut (.sel, .y);

  initial begin
    sel = 2'b00; #5;
    if (y !== 4'b0001) begin $display("FAIL 00: got %04b", y); $finish; end

    sel = 2'b01; #5;
    if (y !== 4'b0010) begin $display("FAIL 01: got %04b", y); $finish; end

    sel = 2'b10; #5;
    if (y !== 4'b0100) begin $display("FAIL 10: got %04b", y); $finish; end

    sel = 2'b11; #5;
    if (y !== 4'b1000) begin $display("FAIL 11: got %04b (latch?)", y); $finish; end

    $display("PASS");
    $finish;
  end
endmodule
