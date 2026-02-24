module priority_enc (
  input  logic [3:0] req,
  output logic [1:0] grant,
  output logic       valid
);
  always_comb begin
    grant = 2'd0;
    valid = 1'b0;
    casez (req)
      4'b1???: begin grant = 2'd3; valid = 1'b1; end
      4'b01??: begin grant = 2'd2; valid = 1'b1; end
      4'b001?: begin grant = 2'd1; valid = 1'b1; end
      4'b0001: begin grant = 2'd0; valid = 1'b1; end
    endcase
  end
endmodule
