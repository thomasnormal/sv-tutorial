module mux4 (
  input  logic [1:0]   sel,
  input  logic [7:0] a, b, c, d,
  output logic [7:0] y
);
  always_comb begin
    case (sel)
      2'b00: y = a;
      2'b01: y = b;
      2'b10: y = c;
      2'b11: y = d;
    endcase
  end
endmodule
