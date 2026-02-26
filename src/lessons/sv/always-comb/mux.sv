module mux4 (
  input  logic [1:0] sel,
  input  logic [7:0] a, b, c, d,
  output logic [7:0] y
);
  always_comb begin
    case (sel)
      // 2'b00 is the binary representation of 0.
      // We could also write 2'b0 or just 0
      2'b00: y = a;  // if sel is 0, output a
      // TODO: add the remaining three branches for b, c, and d
    endcase
  end
endmodule
