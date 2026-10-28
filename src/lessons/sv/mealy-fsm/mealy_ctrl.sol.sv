typedef enum logic { IDLE, BUSY } ctrl_state_t;

module mealy_ctrl (
  input  logic clk,
  input  logic rst_n,
  input  logic req,
  input  logic ack,
  output logic grant,
  output logic done,
  output logic busy
);
  ctrl_state_t state;

  always_ff @(posedge clk) begin
    if (!rst_n) state <= IDLE;
    else begin
      case (state)
        IDLE: if (req) state <= BUSY;
        BUSY: if (ack) state <= IDLE;
        default: state <= IDLE;
      endcase
    end
  end

  assign grant   = (state == IDLE) && req;
  assign done = (state == BUSY) && ack;
  assign busy    = (state == BUSY);
endmodule
