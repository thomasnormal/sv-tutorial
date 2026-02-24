module mux4 #(parameter W = 8) (
  input  logic [1:0]   sel,
  input  logic [W-1:0] a, b, c, d,
  output logic [W-1:0] y
);
  always_comb begin
    case (sel)
      // TODO: four cases mapping sel to a/b/c/d
    endcase
  end
endmodule
