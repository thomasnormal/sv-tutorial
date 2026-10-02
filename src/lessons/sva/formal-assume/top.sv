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

  // TODO: assume property — rst is high at the first clock edge (constrains BMC's initial states)
  initial assume property (@(posedge clk) rst);

  no_invalid: assert property (
    @(posedge clk) disable iff (rst)
      // TODO: state 3 is never reached
      ;
  );
endmodule
