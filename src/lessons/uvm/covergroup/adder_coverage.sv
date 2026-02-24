import uvm_pkg::*;
`include "uvm_macros.svh"

class adder_coverage extends uvm_subscriber #(adder_item);
  `uvm_component_utils(adder_coverage)

  adder_item item;

  covergroup adder_cg;
    // TODO: cp_a: coverpoint item.a {
    //         bins lo  = {[0:85]};
    //         bins mid = {[86:170]};
    //         bins hi  = {[171:255]};
    //       }
    // TODO: cp_b: coverpoint item.b {
    //         bins lo  = {[0:85]};
    //         bins mid = {[86:170]};
    //         bins hi  = {[171:255]};
    //       }
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    adder_cg = new();
  endfunction

  function void write(adder_item t);
    item = t;
    adder_cg.sample();
  endfunction
endclass
