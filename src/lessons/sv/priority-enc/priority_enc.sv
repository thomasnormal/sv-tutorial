module priority_enc (
  input  logic [3:0] req,
  output logic [1:0] grant,
  output logic       valid
);
  always_comb begin
    grant = 2'd0;
    valid = 1'b0;
    casez (req)
      // TODO: four casez branches, highest index wins
    endcase
  end
endmodule
