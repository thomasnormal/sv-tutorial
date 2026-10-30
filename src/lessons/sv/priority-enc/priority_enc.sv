module priority_enc (
  input  logic [3:0] req,
  output logic [1:0] grant,
  output logic       valid
);
  always_comb begin
    grant = 2'd0;
    valid = 1'b0;

    casez (req)
      // TODO: add four branches in descending priority (3, 2, 1, 0).
      //       Use ? for the lower request bits and set grant plus valid.
      default: begin
        grant = 2'd0;
        valid = 1'b0;
      end
    endcase
  end
endmodule
