module tb;
  logic [7:0] data;
  int base;
  logic [3:0] inside_slice;
  logic [3:0] partial_slice;

  initial begin
    data = 8'b1101_0110;
    base = 4;
    inside_slice = data[base +: 4];
    partial_slice = data[8 +: 4];
    if (inside_slice !== 4'b1101 || partial_slice !== 4'bxxxx)
      $display("FAIL: inside=%b partial=%b", inside_slice, partial_slice);
    else
      $display("PASS");
    $finish;
  end
endmodule
