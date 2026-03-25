// 2-to-4 one-hot decoder.
// WARNING: this module currently infers a latch — fix it!
module decoder (
  input  logic [1:0] sel,
  output logic [3:0] y
);
  // TODO: this case statement is missing a branch for 2'b11.
  //       Add it (y = 4'b1000) — or add a default — to eliminate the latch.
  //       Then change `case` to `unique case` to tell the synthesiser
  //       the branches are mutually exclusive (parallel mux, not priority chain).
  always_comb begin
    case (sel)
      2'b00: y = 4'b0001;
      2'b01: y = 4'b0010;
      2'b10: y = 4'b0100;
      // 2'b11 is missing here
    endcase
  end

endmodule
