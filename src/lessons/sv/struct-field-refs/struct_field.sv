typedef struct packed {
  logic [31:0] exp_bits;
  logic [31:0] man_bits;
} pair_t;

module field_driver(input pair_t src, inout pair_t dst);
  assign dst.exp_bits = src.man_bits;
endmodule

module tb;
  pair_t src;
  tri pair_t dst;
  field_driver driver(src, dst);

  initial begin
    src = '0;
    src.exp_bits = 32'hA5;
    #1;
    if (dst.exp_bits !== 32'hA5)
      $display("FAIL: got %h", dst.exp_bits);
    else
      $display("PASS");
    $finish;
  end
endmodule
