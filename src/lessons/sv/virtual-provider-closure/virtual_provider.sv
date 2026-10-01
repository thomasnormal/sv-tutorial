package virtual_provider_pkg;
  int implementation_id;

  class base;
    virtual function int f();
      return 1;
    endfunction
  endclass

  class derived extends base;
    virtual function int f();
      implementation_id = 606;
      return 6;
    endfunction
  endclass
endpackage

module tb;
  import virtual_provider_pkg::*;

  initial begin
    base value;
    derived concrete;
    concrete = new();
    value = concrete;

    if (value.f() != 7 || implementation_id != 707) begin
      $display("FAIL: virtual provider value=%0d id=%0d", value.f(), implementation_id);
      $finish;
    end
    $display("PASS: virtual provider value=%0d id=%0d", value.f(), implementation_id);
    $finish;
  end
endmodule
