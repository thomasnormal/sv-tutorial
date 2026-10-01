module tb;
//pragma protect begin_protected
//pragma protect data_block
BBBB
//pragma protect end_data_block
  initial begin
    $display("FAIL: protected envelope is unterminated");
    $finish;
  end
endmodule
