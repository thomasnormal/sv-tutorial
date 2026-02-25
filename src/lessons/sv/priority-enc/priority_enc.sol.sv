module priority_enc (
  input  logic [3:0] req,    // request lines: bit N = 1 means requester N wants the bus
  output logic [1:0] grant,  // grant: index of the highest-priority active requester
  output logic       valid   // valid: 1 when at least one request is active
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
