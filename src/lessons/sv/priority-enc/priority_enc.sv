module priority_enc (
  input  logic [3:0] req,    // request lines: bit N = 1 means requester N wants the bus
  output logic [1:0] grant,  // grant: index of the highest-priority active requester
  output logic       valid   // valid: 1 when at least one request is active
);
  always_comb begin
    grant = 2'd0;
    valid = 1'b0;
    casez (req)
      // TODO: four casez branches, highest index wins
    endcase
  end
endmodule
