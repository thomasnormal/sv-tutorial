import uvm_pkg::*;
`include "uvm_macros.svh"
`include "adder_item.sv"

module tb_top;
  initial begin
    adder_item item;
    repeat (5) begin
      item = adder_item::type_id::create("item");
      void'(item.randomize());
      $display("%s  expected_sum=%0d", item.convert2string(), item.a + item.b);
    end
  end
endmodule
