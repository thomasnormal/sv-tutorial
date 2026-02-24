typedef enum logic [1:0] { IDLE, RUNNING, DONE, ERROR } status_t;

module status_display(
  input  status_t  st,
  output logic     active,
  output logic     err
);
  always_comb begin
    active = 1'b0;
    err    = 1'b0;
    case (st)
      RUNNING: active = 1'b1;
      ERROR:   err    = 1'b1;
      default: ;
    endcase
  end
endmodule
