module mux4 #(parameter W = 8) (
  input  logic [1:0]   sel,
  input  logic [W-1:0] a, b, c, d,
  output logic [W-1:0] y
);
  always_comb begin
    case (sel)
      2'b00: y = a;
      // TODO: add the remaining three branches for b, c, and d
    endcase
  end
endmodule
