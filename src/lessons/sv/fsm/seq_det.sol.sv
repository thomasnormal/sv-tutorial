// Detects the sequence: 1 -> 0 -> 1
typedef enum logic [1:0] { S0, S1, S2, S3 } state_t;

module seq_det (
  input  logic clk, rst_n, din,
  output logic detected
);
  state_t state, next;

  always_ff @(posedge clk)
    if (!rst_n) state <= S0;
    else        state <= next;

  always_comb begin
    next     = state;
    detected = 1'b0;
    case (state)
      S0: next = din ? S1 : S0;
      S1: next = din ? S1 : S2;
      S2: next = din ? S3 : S0;
      S3: begin detected = 1'b1; next = din ? S1 : S0; end
      default: next = S0;
    endcase
  end
endmodule
