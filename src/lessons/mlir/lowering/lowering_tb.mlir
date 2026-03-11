// Testbench: verify @dff_before (the seq.compreg form) from lowering.mlir.
// Drive D=0xAA, apply one posedge, confirm Q==0xAA.
//
// Note: @dff_after uses sv.reg + sv.always posedge which requires SV-to-LLHD
// lowering passes not run by circt-sim in standalone mode.  The testbench
// therefore exercises only @dff_before (which uses seq.compreg directly).
hw.module @tb() {
  %false   = hw.constant false
  %true    = hw.constant true
  %c0_i8   = hw.constant 0   : i8
  %cAA     = hw.constant 170 : i8   // 0xAA
  %eps     = llhd.constant_time <0ns, 0d, 1e>
  %c5ns    = hw.constant  5000000 : i64   // 5 ns half-period
  %c11ns   = hw.constant 11000000 : i64   // 11 ns — after posedge at 5 ns
  %c30ns   = hw.constant 30000000 : i64   // termination timeout

  // Clock and data signals.
  %clk_sig = llhd.sig %false : i1
  %d_sig   = llhd.sig %cAA  : i8   // D always 0xAA

  %clk_val = llhd.prb %clk_sig : i1
  %clk     = seq.to_clock %clk_val
  %d_val   = llhd.prb %d_sig   : i8

  // DUT: @dff_before (seq.compreg — the high-level form before lowering).
  %q = hw.instance "dut" @dff_before(d: %d_val : i8, clk: %clk : !seq.clock) -> (q: i8)

  // Shadow signal for probing in processes.
  %q_sig = llhd.sig %c0_i8 : i8
  llhd.drv %q_sig, %q after %eps : i8

  // Clock generator: toggle every 5 ns.
  llhd.process {
    cf.br ^loop
  ^loop:
    %d = llhd.int_to_time %c5ns
    llhd.wait delay %d, ^flip
  ^flip:
    %v  = llhd.prb %clk_sig : i1
    %nv = comb.xor %v, %true : i1
    llhd.drv %clk_sig, %nv after %eps : i1
    cf.br ^loop
  }

  // Check Q at 11 ns (after posedge at 5 ns).
  llhd.process {
    %d = llhd.int_to_time %c11ns
    llhd.wait delay %d, ^check
  ^check:
    %qv = llhd.prb %q_sig : i8
    %ok = comb.icmp eq %qv, %cAA : i8
    cf.cond_br %ok, ^pass, ^fail
  ^pass:
    %pm = sim.fmt.literal "PASS\0A"
    sim.proc.print %pm
    sim.terminate success, quiet
    llhd.halt
  ^fail:
    %fm = sim.fmt.literal "FAIL: dff_before expected Q=0xAA\0A"
    sim.proc.print %fm
    sim.terminate success, quiet
    llhd.halt
  }

  // Terminate after 30 ns (safety timeout).
  llhd.process {
    %d = llhd.int_to_time %c30ns
    llhd.wait delay %d, ^end
  ^end:
    sim.terminate success, quiet
    llhd.halt
  }

  hw.output
}
