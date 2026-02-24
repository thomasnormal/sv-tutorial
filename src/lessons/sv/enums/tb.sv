module tb;
  status_t st;
  logic active, err;
  status_display dut(.st,.active,.err);
  initial begin
    st = IDLE;    #1 $display("IDLE:    active=%b err=%b", active, err);
    st = RUNNING; #1 $display("RUNNING: active=%b err=%b", active, err);
    st = DONE;    #1 $display("DONE:    active=%b err=%b", active, err);
    st = ERROR;   #1 $display("ERROR:   active=%b err=%b", active, err);
  end
endmodule
