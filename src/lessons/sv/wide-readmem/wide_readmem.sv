module tb;
  logic [63:0] memory [0:2];
  integer fd;

  initial begin
    fd = $fopen("/tmp/sv_tutorial_wide_readmem.hex", "w");
    $fwrite(fd, "1_0123456789abcdef\n");
    $fwrite(fd, "0_fedcba9876543210\n");
    $fwrite(fd, "z_0000000000000000\n");
    $fclose(fd);
    $readmemh("/tmp/sv_tutorial_wide_readmem.hex", memory, 0, 2);

    if (memory[0] !== 65'h1_0123456789abcdef ||
        memory[1] !== 65'h0_fedcba9876543210 ||
        memory[2] !== 65'hz_0000000000000000) begin
      $display("FAIL: %h %h %h", memory[0], memory[1], memory[2]);
      $finish;
    end
    $display("PASS");
    $finish;
  end
endmodule
