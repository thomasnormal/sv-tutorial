class mem_test_ral extends uvm_test;
  `uvm_component_utils(mem_test_ral)
  function new(string name, uvm_component parent); super.new(name, parent); endfunction

  task run_phase(uvm_phase phase);
    sram_reg_block ral;
    phase.raise_objection(this);
    ral = sram_reg_block::type_id::create("ral", this);
    ral.build();

    // UVM RAL API: call .set() on uvm_reg_field, then .get() on uvm_reg
    // TODO: change ctrl_reg to extend uvm_reg (not uvm_object) and declare
    //       enable and mode as uvm_reg_field — then these calls will compile.
    ral.ctrl.enable.set(1);
    ral.ctrl.mode.set(2'b10);

    if (ral.ctrl.get() == 8'h05)
      `uvm_info("RAL_TEST", $sformatf("PASS: ctrl=0x%02h", ral.ctrl.get()), UVM_NONE)
    else
      `uvm_error("RAL_TEST", $sformatf("FAIL: expected 0x05, got 0x%02h", ral.ctrl.get()))

    phase.drop_objection(this);
  endtask
endclass
