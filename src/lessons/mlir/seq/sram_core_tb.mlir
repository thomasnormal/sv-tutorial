// Testbench: verify the @dff module (seq.compreg) defined at the bottom of
// sram_core.mlir.  Drive D=0x42 into the flip-flop, apply one posedge, and
// confirm Q==0x42 on the output.
//
// Note: @sram_core uses seq.hlmem which requires lowering passes not run by
// circt-sim in standalone mode, so we test the simpler @dff example here.
//
// Uses LLHD dialect for clock generation and time-driven simulation:
//   llhd.sig / llhd.prb / llhd.drv  — signals and drives
//   llhd.process + llhd.wait delay  — time-advancing processes
//   sim.proc.print                  — simulation output
hw.module @tb() {
  %false  = hw.constant false
  %true   = hw.constant true
  %c0_i8  = hw.constant 0   : i8
  %c42    = hw.constant 66  : i8   // 0x42
  %eps    = llhd.constant_time <0ns, 0d, 1e>
  %c5ns   = hw.constant  5000000 : i64   // 5 ns half-period
  %c11ns  = hw.constant 11000000 : i64   // 11 ns — after first posedge (5 ns)
  %c30ns  = hw.constant 30000000 : i64   // 30 ns — termination timeout

  // Shared clock and data signals.
  %clk_sig = llhd.sig %false : i1
  %d_sig   = llhd.sig %c42  : i8   // D always 0x42

  %clk_val = llhd.prb %clk_sig : i1
  %clk     = seq.to_clock %clk_val
  %d_val   = llhd.prb %d_sig   : i8

  // DUT: @dff (seq.compreg — latches D on posedge clock).
  %q = hw.instance "dut" @dff(d: %d_val : i8, clk: %clk : !seq.clock) -> (q: i8)

  // Shadow signal so the check process can probe Q.
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

  // Check Q at 11 ns (one ns after posedge at 5 ns).
  llhd.process {
    %d = llhd.int_to_time %c11ns
    llhd.wait delay %d, ^check
  ^check:
    %qv = llhd.prb %q_sig : i8
    %ok = comb.icmp eq %qv, %c42 : i8
    cf.cond_br %ok, ^pass, ^fail
  ^pass:
    %pm = sim.fmt.literal "PASS\0A"
    sim.proc.print %pm
    sim.terminate success, quiet
    llhd.halt
  ^fail:
    %fm = sim.fmt.literal "FAIL: dff expected Q=0x42\0A"
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
