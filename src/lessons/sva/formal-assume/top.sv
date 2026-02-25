module top(
  input  logic clk, rst,
  output logic [1:0] state  // 0=RED 1=GREEN 2=YELLOW
);
  always_ff @(posedge clk) begin
    if (rst) state <= 2'd0;
    else case (state)
      2'd0: state <= 2'd1;
      2'd1: state <= 2'd2;
      2'd2: state <= 2'd0;
      default: state <= 2'd0;
    endcase
  end

  // TODO: assume property — when rst is high, state must be 0 (constrains BMC's initial states)
  // TODO: assert property — state 3 is never reached (disable during rst)
endmodule
