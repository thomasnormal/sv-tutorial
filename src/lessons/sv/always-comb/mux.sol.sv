module mux4 #(parameter W = 8) (
  input  logic [1:0]   sel,
  input  logic [W-1:0] a, b, c, d,
  output logic [W-1:0] y
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
