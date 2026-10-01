module tb;
//pragma protect begin_protected
//pragma protect data_block
BBBB
//pragma protect end_data_block
//pragma protect end_protected
  initial begin
    $display("PASS: opaque protected wrapper");
    $finish;
  end
endmodule
