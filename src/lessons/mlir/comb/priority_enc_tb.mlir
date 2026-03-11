// Testbench: instantiate @priority_enc with req=0b0010; verify grant==1, valid==1.
//
// Uses LLHD dialect for signal-driven simulation compatible with circt-sim.
hw.module @tb() {
  %c0_i2 = hw.constant 0 : i2
  %c0_i1 = hw.constant false
  %c1_i2 = hw.constant 1 : i2   // expected grant
  %c1_i1 = hw.constant true      // expected valid
  %req   = hw.constant 2 : i4   // 0b0010 — bit 1 set
  %eps   = llhd.constant_time <0ns, 0d, 1e>
  %c1ns  = hw.constant 1000000 : i64

  %grant, %valid = hw.instance "dut" @priority_enc(req: %req : i4) -> (grant: i2, valid: i1)

  // Drive outputs onto signals so the check process can probe them.
  %grant_sig = llhd.sig %c0_i2 : i2
  %valid_sig = llhd.sig %c0_i1 : i1
  llhd.drv %grant_sig, %grant after %eps : i2
  llhd.drv %valid_sig, %valid after %eps : i1

  llhd.process {
    %delay = llhd.int_to_time %c1ns
    llhd.wait delay %delay, ^check
  ^check:
    %gv   = llhd.prb %grant_sig : i2
    %vv   = llhd.prb %valid_sig : i1
    %ok_g = comb.icmp eq %gv, %c1_i2 : i2
    %ok_v = comb.icmp eq %vv, %c1_i1 : i1
    %ok   = comb.and %ok_g, %ok_v : i1
    cf.cond_br %ok, ^pass, ^fail
  ^pass:
    %pm = sim.fmt.literal "PASS\0A"
    sim.proc.print %pm
    sim.terminate success, quiet
    llhd.halt
  ^fail:
    %fm = sim.fmt.literal "FAIL: priority_enc unexpected output\0A"
    sim.proc.print %fm
    sim.terminate success, quiet
    llhd.halt
  }

  hw.output
}
