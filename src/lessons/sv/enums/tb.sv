module tb;
  logic [1:0] state;
  logic       reading, writing;

  ctrl_display dut(.state, .reading, .writing);

  initial begin
    state = 2'd0; #1;  // IDLE — neither reading nor writing
    $display("%s IDLE:  reading=%b writing=%b",
             (reading===0 && writing===0) ? "PASS" : "FAIL", reading, writing);

    state = 2'd2; #1;  // READ (enum value 2) — reading should be 1
    $display("%s READ:  reading=%b writing=%b",
             (reading===1 && writing===0) ? "PASS" : "FAIL", reading, writing);

    state = 2'd3; #1;  // WRITE (enum value 3) — writing should be 1
    $display("%s WRITE: reading=%b writing=%b",
             (reading===0 && writing===1) ? "PASS" : "FAIL", reading, writing);

    state = 2'd1; #1;  // CMD (enum value 1) — neither reading nor writing
    $display("%s CMD:   reading=%b writing=%b",
             (reading===0 && writing===0) ? "PASS" : "FAIL", reading, writing);

    $finish;
  end
endmodule
