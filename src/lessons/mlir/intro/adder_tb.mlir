// Testbench: instantiate @adder with a=5, b=3 and verify sum==8.
//
// Uses LLHD dialect for signal-driven simulation compatible with circt-sim.
// The hw.instance output is driven onto a signal so the check process can
// probe it after epsilon time, then print PASS or FAIL.
hw.module @tb() {
  %c0_i8 = hw.constant 0 : i8
  %c5    = hw.constant 5 : i8
  %c3    = hw.constant 3 : i8
  %c8    = hw.constant 8 : i8
  %eps   = llhd.constant_time <0ns, 0d, 1e>
  %c1ns  = hw.constant 1000000 : i64

  %sum = hw.instance "dut" @adder(a: %c5 : i8, b: %c3 : i8) -> (sum: i8)

  // Drive sum onto a signal so the check process can probe it.
  %sum_sig = llhd.sig %c0_i8 : i8
  llhd.drv %sum_sig, %sum after %eps : i8

  llhd.process {
    %delay = llhd.int_to_time %c1ns
    llhd.wait delay %delay, ^check
  ^check:
    %sv = llhd.prb %sum_sig : i8
    %ok = comb.icmp eq %sv, %c8 : i8
    cf.cond_br %ok, ^pass, ^fail
  ^pass:
    %pm = sim.fmt.literal "PASS\0A"
    sim.proc.print %pm
    sim.terminate success, quiet
    llhd.halt
  ^fail:
    %fm = sim.fmt.literal "FAIL: adder expected sum=8\0A"
    sim.proc.print %fm
    sim.terminate success, quiet
    llhd.halt
  }

  hw.output
}
