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
      // TODO: RUNNING: active = 1'b1;
      // TODO: ERROR:   err    = 1'b1;
      default: ; // all other states: keep defaults
    endcase
  end
endmodule
