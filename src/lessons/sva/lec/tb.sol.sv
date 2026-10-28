module tb;
  logic a, b, c;
  logic spec_nand, spec_nor, spec_mux;
  logic impl_nand, impl_nor, impl_mux;
  int fail = 0;

  Spec spec(.a, .b, .c, .nand_y(spec_nand), .nor_y(spec_nor), .mux_y(spec_mux));
  Impl impl(.a, .b, .c, .nand_y(impl_nand), .nor_y(impl_nor), .mux_y(impl_mux));

  initial begin
    for (int i = 0; i < 8; i++) begin
      {a, b, c} = i[2:0];
      #1;
      $display("a=%0b b=%0b c=%0b | spec=%0b%0b%0b impl=%0b%0b%0b",
        a, b, c, spec_nand, spec_nor, spec_mux, impl_nand, impl_nor, impl_mux);
      if ({spec_nand, spec_nor, spec_mux} !== {impl_nand, impl_nor, impl_mux}) begin
        $display("FAIL: mismatch for a=%0b b=%0b c=%0b", a, b, c);
        fail++;
      end
    end

    if (fail == 0) $display("PASS: Impl matched Spec for all eight input combinations");
    else $display("FAIL: %0d Boolean combinations disagreed", fail);
    $finish;
  end
endmodule
