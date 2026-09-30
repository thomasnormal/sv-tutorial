# sv-tutorial CONTENT census

## Current-main refresh — 2026-09-30

The prior full lesson audit remains the authoritative per-lesson matrix below.
This refresh adds the current-main execution status: native Mox is the landing
build at `/var/tmp/thomas-ahle/wt/landing/build-dev-fast`; Xcelium is invoked
through `/var/tmp/thomas-ahle/fleet/bin/refdiff`; examples are bounded to 30 s
and CPU affinity `0-79`. The browser cannot prove current native behaviour
because the checked-in WASM predates the landing tip.

## New landed-capability chapters

These four short chapters correspond to capabilities present on Mox `origin/main`
(`bcdf57717c1`) by September 30, 2026. They deliberately exclude the later
landing-only UDP change at `36b040f6190`. Every solution passes Mox in both
interpreter and compile mode and passes Xcelium through `refdiff`; every starter
prints a failing check.

| Lesson | Landed capability / Mox evidence | IEEE claim | Mox interpreter | Mox compile | Xcelium/refdiff | Fix |
|---|---|---|---|---|---|---|
| `sv/macro-formal-continuation` | `bcdf57717c1`, `test/Conversion/ImportVerilog/macro-formal-continuation.sv` | §22.5.1: backslash-newline continues macro text; formal arguments and token pasting are substituted before compilation. | solution PASS; starter FAIL | solution PASS; starter FAIL | both PASS, output equal | added runnable macro exercise |
| `sv/struct-field-refs` | `0585a62233b`, `test/mox-verilog/struct-extract-ref-module-level.sv` | §7.2.1: packed structs are vectors with named members; members can be selected by name. | solution PASS; starter FAIL | solution PASS; starter FAIL | both PASS, output equal | added module-level packed-struct field exercise |
| `sv/indexed-part-select` | `5a49d2b68cf`, `test/Tools/mox-sim/dyn-extract-unsigned-partial-runtime.sv` | §11.5.1: indexed part-select width is constant, base may vary, and a wholly out-of-range read is `x`. | solution PASS; starter FAIL | solution PASS; starter FAIL | both PASS, output equal | uses a variable in-range base and unambiguous wholly out-of-range read |
| `sv/nested-child-input` | `5fdce05081e`, `test/Tools/mox-sim/nested-child-input-propagation-runtime.sv` | §§23.2.2, 9.4.2: child inputs are connected expressions and clocked procedures sample them on edges. | solution PASS; starter FAIL | solution PASS; starter FAIL | both PASS, output equal | added direct and nested sink propagation exercise |

This census covers every lesson in `src/lessons/` (meta.js, 73 lessons) and CURRICULUM.md, checked against
IEEE 1800-2023 (`spec/ieee-1800-2023.txt`) and IEEE 1800.2-2020 (UVM).

Each row gives: lesson | claim/example | what is wrong | IEEE clause | evidence | proposed fix | severity.

Method: each lesson was flattened, then its solution and starter were run on native Mox (landing
build-dev-fast) and on Xcelium via `refdiff`/`refsim`. Mutation runs checked whether the testbench accepts
wrong designs, and BMC runs used the browser flags. Evidence paths are under `/tmp/tut/`.

Crashes and red CI are in **broken-census.md**. Mox defects found on the way are in **GAPS.md**.

## Fixed on fleet/tutorial-fixes (see SUMMARY.md)
- queues-arrays: static initializer loop (§6.21), `logic'(i)` 1-bit cast (§6.24.1), no size check.
- randomization: infeasible hard constraint vs inline constraint (§18.7). `low_bank_c` is now `soft` (§18.5.13).
- UVM: `uvm_top`/`finish_on_completion` not in IEEE 1800.2 (F.7). Fields used before their declaration (§6.5).
- MLIR: the `*_tb.mlir` checks were never run in the browser (adapter fix).
- All other rows are **open**: they need author decisions, and several change what a lesson teaches.

---

## SV Basics audit (src/lessons/sv/*, meta.js, CURRICULUM.md Part 1)

Method: every lesson flattened (`/tmp/tut/bin/flatten-lesson.py`) and run as solution and starter through
native `mox-run` (landing build-dev-fast) and `refdiff` (Mox vs Xcelium, cached). Run dirs:
`/tmp/tut/runs/sv_<lesson>_<mode>/` (mox.log, refdiff.txt, refdiff.json/). Mutation tests (wrong designs that
still print PASS) were built as copies under `/tmp/tut/audit/mut/<name>/` (lesson copy + flattened .sv + mox.log)
with `/tmp/tut/audit/mut.sh`; the repo was not modified. Standard: IEEE 1800-2023 (`/var/tmp/thomas-ahle/spec/ieee-1800-2023.txt`).

Pass detector note: the repo's `scripts/test-all-lessons.mjs` counts a run as passing if *any* output line
`startsWith('PASS')`. Several testbenches print per-check lines `PASS  ...`, so a partially correct design
satisfies the detector (counter mutation below demonstrates it).

### Run matrix

| run | Xcelium | Mox (refdiff) | category | output equal | Mox-run prints a PASS line |
|---|---|---|---|---|---|
| sv_always-comb_solution | PASS | PASS | both_pass | True | True |
| sv_always-comb_starter | PASS | PASS | both_pass | True | False |
| sv_always-ff_solution | PASS | PASS | both_pass | True | True |
| sv_always-ff_starter | FAIL | FAIL | both_fail | True | False |
| sv_classes_solution | PASS | PASS | both_pass | True | True |
| sv_classes_starter | FAIL | FAIL | both_fail | True | False |
| sv_counter_solution | PASS | PASS | both_pass | True | True |
| sv_counter_starter | FAIL | FAIL | both_fail | True | False |
| sv_covergroup-basics_solution | PASS | PASS | both_pass | True | True |
| sv_covergroup-basics_starter | PASS | PASS | both_pass | True | False |
| sv_coverpoint-bins_solution | PASS | PASS | both_pass | True | True |
| sv_coverpoint-bins_starter | PASS | PASS | both_pass | True | False |
| sv_cross-coverage_solution | PASS | PASS | both_pass | True | True |
| sv_cross-coverage_starter | PASS | PASS | both_pass | True | False |
| sv_data-types_solution | PASS | PASS | both_pass | True | True |
| sv_data-types_starter | FAIL | FAIL | both_fail | True | False |
| sv_enums_solution | PASS | PASS | both_pass | True | True |
| sv_enums_starter | FAIL | FAIL | both_fail | True | False |
| sv_events_solution | PASS | PASS | both_pass | True | True |
| sv_events_starter | PASS | PASS | both_pass | True | False |
| sv_fork-join_solution | PASS | PASS | both_pass | True | True |
| sv_fork-join_starter | FAIL | FAIL | both_fail | False | False |
| sv_fsm_solution | PASS | PASS | both_pass | True | True |
| sv_fsm_starter | PASS | PASS | both_pass | True | False |
| sv_interfaces_solution | PASS | PASS | both_pass | True | True |
| sv_interfaces_starter | FAIL | FAIL | both_fail | True | False |
| sv_modports_solution | PASS | PASS | both_pass | True | True |
| sv_modports_starter | FAIL | FAIL | both_fail | True | False |
| sv_modules-and-ports_solution | PASS | PASS | both_pass | True | True |
| sv_modules-and-ports_starter | PASS | PASS | both_pass | True | False |
| sv_packed-structs_solution | PASS | PASS | both_pass | True | True |
| sv_packed-structs_starter | FAIL | FAIL | both_fail | True | False |
| sv_parameters_solution | PASS | PASS | both_pass | True | True |
| sv_parameters_starter | FAIL | FAIL | both_fail | True | False |
| sv_queues-arrays_solution | TIMEOUT | TIMEOUT | both_fail | False | False |
| sv_queues-arrays_starter | FAIL | FAIL | both_fail | True | False |
| sv_randomization_solution | PASS | PASS | both_pass | False | True |
| sv_randomization_starter | FAIL | FAIL | both_fail | True | False |
| sv_tasks-functions_solution | PASS | PASS | both_pass | True | True |
| sv_tasks-functions_starter | PASS | PASS | both_pass | True | False |
| sv_welcome_solution | PASS | PASS | both_pass | True | False |
| sv_welcome_starter | PASS | PASS | both_pass | True | False |

sv_queues-arrays_solution: both simulators TIMEOUT (infinite `pop: x` loop), see findings. Every other solution is both_pass with equal output. randomization output differs only in random values (different RNG). Starters that are both_fail are compile errors or $fatal, which is expected. No starter prints a PASS line. welcome prints no PASS by design (SKIP_SOL_PASS).

**Concurrency note:** the tutorial lane edited the working tree while this audit ran. randomization/* now has an uncommitted `soft` fix (verified both_pass), and commit 67d45ef (--coverage-report) landed at 10:47. Findings are against HEAD 67d45ef plus the working tree as of 10:55 UTC; the randomization row describes the committed version.

### Findings

| lesson | claim/example | what is wrong | IEEE clause | evidence | proposed fix | severity |
|---|---|---|---|---|---|---|
| queues-arrays | solution `while (q.size() > 0) begin logic [3:0] v = q.pop_front(); ...` | Static variable declared with an initializer inside a procedural block without `static`. That is illegal, and both simulators accept it with a warning and run the initializer once at time 0, when q is empty. The loop body never pops, so the solution never terminates: it prints `pop: x` forever and never prints PASS. The "solve" button therefore loads a hanging program, and a student who declares the popped value the same way hits the same hang. | 6.21: "an explicit static keyword shall be required when an initialization value is specified as part of a static variable's declaration"; the spec's top_illegal example is marked "// should not compile" | refdiff: reference=TIMEOUT, mox=TIMEOUT (`/tmp/tut/runs/sv_queues-arrays_solution/refdiff.txt`); Xcelium printed 191M lines of `pop: x` (`xcelium.head.txt`, `xcelium.lines.txt` in the same dir). Minimal repro: `/tmp/tut/audit/repro/static-init-in-procedural-block.sv` (Xcelium *W,VARIST; Mox -Wexplicit-static; both v=0 size=3 x3) | `logic [3:0] v; v = q.pop_front();` (or `automatic logic [3:0] v = q.pop_front();`) | high |
| queues-arrays | `addrs[i] = logic'(i);` "fill with 0..7" | `logic'(i)` casts to a 1-bit logic, so the array holds 0,1,0,1,... Both simulators print `first=0 last=1`, which contradicts the diagram and comments. | 6.24.1: the cast shall "return the value that a variable of the casting type would hold after being assigned the expression" | Output head on both simulators: `Array size: 8  first=0  last=1` | `addrs[i] = 4'(i);` or `addrs[i] = i;` | high |
| queues-arrays | testbench | The only check is `q.size()==0` at the end. A student who declares `addrs`/`q` and does no push or pop still gets PASS; the array contents and the pop order are never checked. | RUBRIC: PASS iff correct | Code reading (the assert is independent of the push/pop TODOs) | Check `addrs[7]==7`, `q.size()==4` after the pushes, and the popped sequence 0,1,2,3 | high |
| queues-arrays | "new[n] allocates n elements — all zeroed" | The elements are `logic`, so they start as 'x, not 0. | 7.5.1: elements are "initialized to the default value for their type"; 6.8 Table 6-7 (logic = 'x) | spec | "initialized to the element type's default ('x for logic, 0 for bit/int)" | med |
| queues-arrays | an empty dynamic array is called a "null handle" | A dynamic array is not a class handle. Its default is an empty array of size 0. | 7.5 | spec | "empty (size 0)" | low |
| randomization (HEAD 67d45ef) | `constraint low_bank_c { addr inside {[0:7]}; }` plus `randomize() with { addr inside {[8:15]}; }`, taught as an "Inline override … high bank for this call only" | Inline constraints are added to the class constraints, so this set is infeasible. randomize fails, addr keeps its old value, and the `addr >= 8` assert calls $fatal. The committed solution fails on both simulators. | 18.7: "These additional constraints are applied along with the object constraints."; 18.6.3: "If randomize() fails, the constraints are infeasible, and the random variables retain their previous values." | Committed solution rerun (`/tmp/tut/audit/mut/rand_head/`): Mox `*W,SVRNDF … Fatal: FAIL: addr not in high bank`; Xcelium `*W,RNDOCS` conflict (lines 6/24), exit 2 | Already fixed in the **uncommitted** working tree by the tutorial lane (`soft addr inside {[0:7]}` plus an explanatory paragraph). That version gives both_pass. Commit it. | high |
| randomization | "The return value indicates success — always check it", while the solution uses `void'(t.randomize())` | The solution contradicts the advice in its own text. With a check, the conflict above would have been visible. | 18.6.1 | code | `if (!t.randomize() with {...}) $fatal(...)` | low |
| fork-join | solution drops the starter's `if ($time != 40) $fatal(...)` | The solution contains no check at all: `$display("PASS")` is unconditional. Using `join` instead of `join_any`, or omitting join_none, still prints PASS. | RUBRIC | diff concurrent.sv vs concurrent.sol.sv | Keep the $time==40 check in the solution, and add a check that "parent continues" happens at 40 (e.g. `$time==40` right after join_none) | med |
| fork-join | `$display("[%0t ns] ...", $time)` | %t prints in the global time precision, not in ns. Under refdiff's Xcelium setup it prints `[10000 ns] thread B (10 ns)`, while `mox-run --timescale=1ns/1ns` prints `[10 ns]`. The hard-coded "ns" suffix is wrong under any precision finer than 1ns. | 20.4.3 Table 20-3: units_number default is "The smallest time precision argument of all the `timescale compiler directives" | Xcelium reference.log for sv_fork-join_{solution,starter} | Use `%0d` with `$time`, or `$timeformat(-9,0," ns")` and drop the literal "ns" | low |
| fork-join | thread A and the background thread both finish at t=60 | Their print order is not defined by the standard. Both simulators happen to agree. | 4.7 (nondeterminism) | output_equal=True | Stagger the delays | low |
| covergroup-basics / coverpoint-bins / cross-coverage | starter vs solution PASS | The starters never print PASS and their TODOs don't ask for it. The only difference between starter and solution besides the TODO is an unconditional `$display("PASS")`. A student who completes the TODO never sees PASS, and PASS doesn't depend on the covergroup at all. The comment in test-all-lessons.mjs that says the starters print PASS is untrue. | RUBRIC (coverage lessons may print PASS unconditionally, but then the starter should print it too) | summ: `*_starter both_pass, PASS line = False` | Put the `$display("PASS")` in the starter's non-TODO code | med |
| covergroup-basics / coverpoint-bins | "Run and observe the coverage percentage" / "Run to see whether 64 cycles hit all four" | At the time of my runs, nothing printed a percentage and there was no `get_coverage()` call. **Fixed in app commit 67d45ef (10:47 today)**, which passes `--coverage-report` when a design contains a covergroup. Native Mox with that flag now prints e.g. "cp_addr … 81.25%". Xcelium only prints it with `-coverage`, and that was not verified. | 19.8 | `mox-run --coverage-report` output (this audit) | Also print `cg.get_coverage()` from the tb so the number is simulator-independent and portable | low (after 67d45ef) |
| coverpoint-bins | the lesson is titled "Bins and ignore_bins"; the TODO asks for "hi_half (8–13)" plus "ignore_bins to exclude 14 and 15"; the description has `hi_half = {[8:15]}` and also says to exclude 14/15 | The solution has `bins hi_half = {[8:15]};` and **no ignore_bins**. The solution skips the lesson's own concept, and the starter, description and solution disagree on the range. | 19.5.5: "All values or transitions associated with ignored bins are excluded from coverage. For state bins, each ignored value is removed from the set of values associated with any coverage bin." | cov_bins.sv:13-14 vs cov_bins.sol.sv:13-14 | Solution: `bins hi_half = {[8:15]}; ignore_bins reserved = {14,15};` (by 19.5.5, hi_half is then 8..13). Make the text and the TODO say that. | high |
| coverpoint-bins / covergroup-basics | "an 8-bit signal gets 256 bins" (auto bins) | The number of automatic bins is min(2^M, auto_bin_max), and auto_bin_max defaults to 64, so an 8-bit signal gets 64 bins. | 19.5.3: "N is the minimum of 2M and the value of the auto_bin_max option"; 19.7 Table 19-2 default 64 | spec | "min(2^M, auto_bin_max=64) bins; 256 values are grouped 4 per bin" | med |
| welcome | "Without [$finish] the simulator would run forever waiting for events that never come" | Simulation ends when no events remain. The welcome starter has no $finish and still completes at time 0. | 4.5 reference algorithm: `while (some time slot is nonempty) {…}` | sv_welcome_starter: both simulators complete | "…$finish ends simulation explicitly; without it the run ends when nothing is left to do (a free-running clock would keep it alive forever)" | med |
| welcome | "syntax is identical to C's printf" | Not identical: %b, %t, %m and %0d-style width suppression differ from C, and $display appends a newline. | 21.2.1.1 | spec | "similar to C's printf" | low |
| welcome | "One tight paragraph on printf/display notation:" | Leftover authoring note is visible to students. The HTML is also malformed (`<code><dfn>` mis-nested, `<pre>` inside `<p>`). | — | description.html | Remove the note and fix the nesting | low |
| welcome | "synthesis tools ignore initial blocks" | Overstated: FPGA flows use initial blocks to set register and memory initial values. | — | — | "ASIC synthesis ignores…; FPGA tools may use them for power-up values" | low |
| modules-and-ports | the testbench's only vector is 10+32=42 | `a|b` and `a^b` also give 42, so a wrong adder prints PASS. | RUBRIC | Mutation `/tmp/tut/audit/mut/mp_or/` (`assign sum = a \| b;`) prints `sum = 42` and `PASS` | Add vectors with carries, e.g. 200+100 (wraps to 44) and 15+1 | med |
| modules-and-ports | `sum` is called an "output wire" | `output logic sum` is a variable, not a net. | 6.5, 23.2.2.3 | code | "output (a logic variable driven by assign)" | low |
| data-types | `logic [7:0] mem` is called "a scalar" | It is an 8-bit packed vector. | 7.4.1 | starter comment and description | "a single 8-bit vector" | low |
| data-types | the SVG labels `int` "Testbench only"; a dfn says "unpacked arrays of int or other 2-state types are testbench-only" | 2-state types (`bit`, `int`) are synthesizable. What differs is X/Z modelling, not synthesizability. | 6.11 | — | "int/bit: 2-state; common in testbenches, synthesizable but hide X" | med |
| always-comb | `data-card="TODO"` on "multiplexer"; "TODO: What other procedural statements are there?" | Unfinished placeholder text is visible to students. | — | description.html | Write the cards | med |
| always-comb | always_comb semantics | The text omits that always_comb runs once at time zero, which is the key difference from `always @*`. | 9.2.2.2: "The procedure is automatically triggered once at time zero, after all initial and always procedures…" | spec | Add one sentence | low |
| always-comb | "casez block" | casez is a statement, not a block. | 12.5.1 | — | "casez statement" | low |
| events | "posedge… whenever clk transitions from 0 to 1" | Also 0→x/z and x/z→1. | 9.4.2 / Table 9-2: "A posedge shall be detected on the transition from 0 to x, z, or 1, and from x or z to 1" | spec | Quote the rule, or say "(for a clean 0/1 clock)" | med |
| events | "If you add @(write_done) but forget -> write_done… the simulation never finishes" | With nothing left scheduled, simulation ends. The waiting process just never resumes, so PASS is never printed. | 4.5 | events starter completes on both simulators | "…the waiting process never resumes, so PASS is never printed" | med |
| events | "This even is generated", "brackets… universal convention" | Typo. They are parentheses, and "universal" is overstated. | — | — | Fix wording | low |
| always-ff | per-check lines `PASS  mem[2] = 42` | These lines satisfy the repo detector's `startsWith('PASS')` even when a later check fails. | RUBRIC | tb.sv | Use `ok  mem[2]…`/`FAIL…`, or `[PASS]`-style prefixes | med |
| always-ff | testbench vs "1-cycle read latency" and write-enable | A design that ignores `we`, or one with a combinational read (`assign rdata = mem[addr]`, no latency), still prints PASS. The first works because the old value is read on the same edge as the write; the second because addr is held and sampled at posedge+1. | RUBRIC | Mutations `/tmp/tut/audit/mut/aff_nowe/` and `/tmp/tut/audit/mut/aff_comb/`: both print all 3 PASS lines plus PASS | Check rdata **before** the second edge (latency), and re-read an address after a `we=0` cycle with a different wdata | med |
| always-ff | "all writes happen together at the end of the time step" | NBA updates happen in the NBA region, which is not the end of the time slot: active, inactive and later regions can follow. | 4.4.2.x, 4.5 | spec | "after all blocking/active code of that time step has run" | low |
| always-ff | "An SRAM is an array of flip-flops" | Real SRAM uses 6T bit cells, not flip-flops. The model is a register file. | — | — | "modelled here as an array of registers" | low |
| counter | per-check lines `%s …` printed with "PASS"/"FAIL" | A design that only implements reset prints `PASS rst_n=0 holds…` and `PASS sync reset clears…`. That satisfies the repo detector `some(line.startsWith('PASS'))` even though the final bare PASS is missing. | RUBRIC | Mutation `/tmp/tut/audit/mut/cnt_resetonly/`: 2 PASS lines, 2 FAIL lines | Use `ok`/`FAIL` for per-check lines | med |
| counter | the `_n` dfn says "CMOS NOR gates are faster than NAND gates" | Backwards: NAND is faster (series NMOS vs series PMOS). | — | — | Remove, or reverse the claim | med |
| parameters | $bits dfn: "$bits(n) computes the number of bits needed to represent n distinct values… $bits(16)=4" | $bits returns the storage width of an expression. `$bits(16)` is 32 (an int literal). The function the text describes is `$clog2`. | 20.6.2: "The $bits system function returns the number of bits required to hold an expression as a bit stream" | spec | Delete it, or correct it to "$bits(x) is the width of x's type" | high |
| parameters | "we will discuss include dynamic arrays"; "The solution testbench instantiates…" (the tb is shared) | Typo, and the tb is in the starter too. | — | — | Fix wording | low |
| parameters | `localparam AW = $clog2(DEPTH)` | DEPTH=1 gives `[-1:0]`. | 20.8.1 | — | Mention it, or use `$clog2(DEPTH>1?DEPTH:2)` | low |
| packed-structs | "you should see two PASS lines" | The testbench prints only one. | — | solution output | "a PASS line" | low |
| packed-structs | `'{we:…}` is called a "struct literal" | The standard term is assignment pattern. | 10.9.2 | spec | "assignment pattern" | low |
| interfaces | "These functions are not synthesisable" | Interface functions and tasks can be synthesized (see the 25.7 examples). This particular function only fails because it returns `string`. | 25.7 | spec | "This one isn't (it returns a string), but interface functions in general can be" | med |
| interfaces | "structs are passed by value (copy)" when contrasting ports with interfaces | Misleading: a port connection is continuous, not a one-time copy. | 23.3.3 | — | Rephrase | low |
| interfaces | testbench never checks the output of `sprint()` | `function string sprint(); return ""; endfunction` passes. The TODO is exactly that function. | RUBRIC | Mutation `/tmp/tut/audit/mut/if_empty_sprint/`: 4 blank lines, then PASS | Compare `bus.sprint()` to the expected string | med |
| interfaces | "struts", "write out sram" | Typos. | — | — | — | low |
| modports | the description snippet `modport target (input we, addr, wdata, output rdata);` | It omits `clk`, but the given `sram.sv` uses `bus.clk`. A student who copies the snippet gets a compile error on both simulators. | 25.5 (the modport restricts access; the 25.5.1 example lists `clk` in `target`) | Mutation `/tmp/tut/audit/mut/mp_noclk/`: Mox `cannot access 'clk' via modport 'mem_if.target'`; Xcelium `*E,CUVUNF … lookup failed for 'clk' at 'tb.dut'` (refdiff both_fail) | Add `clk` to the snippet's input list (the solution already has it) | high |
| modports | "the unqualified form is still legal on the initiator side" | The tb uses the bare instance, so it gets full inout/ref access (25.5: "If no modport is specified… all the nets and variables… are accessible with direction inout or ref"). The initiator modport is never exercised, so no direction enforcement is shown on that side. | 25.5 | spec | Say the tb has unrestricted access; or connect a small driver module through `mem_if.initiator` | low |
| modports | "type error" | It is a port-direction error (Mox: `cannot assign to input port 'addr'`). | 25.5 | Mutation `/tmp/tut/audit/mut/mp_wr_input/` | "direction error" | low |
| tasks-functions | `mem_if vif(...)` called "the shared mem_if virtual interface"; CURRICULUM says "driving DUT via virtual interface" | This is an interface instance. A virtual interface is a variable (`virtual mem_if vif`). | 25.9: "A virtual interface is a variable that represents an interface instance." | spec | "interface instance (named vif)" | med |
| tasks-functions | signatures `write_word(vif, addr, data)` / `read_word(vif, …)` in the text | The real tasks take no vif argument. | — | tb.sv | Match the code | med |
| tasks-functions | "advance a small delta — #1" | `#1` is one time unit, not a delta cycle. | 4.4 | — | "one time unit" | low |
| tasks-functions | "Simulation hang disclaimer" paragraph | Speculative, environment-specific advice. The tb uses `vif.clk`, which is the same net as `clk`. | — | — | Remove | low |
| tasks-functions | the starter `tb.sv` (the file the student edits) has a single check on 42 | `return 1;` passes as the parity function (^42 = 1). The solution's extra vectors (FF, 100) are only in `tb.sol.sv`, so they never judge the student's code. | RUBRIC | Mutation `/tmp/tut/audit/mut/tf_starter_ret1/` prints PASS | Move the 3-vector checks into the starter's non-TODO code | med |
| enums | per-check lines start with "PASS" | Same detector problem as counter. | RUBRIC | tb.sv | `ok`/`FAIL` | med |
| enums | "the encoding is chosen by synthesis unless you specify the base type" | The base type sets the width and value set in simulation. Synthesis FSM re-encoding is a tool option, not governed by the base type. | 6.19 | — | Rephrase | low |
| enums | the typedef is in $unit and tb.sv uses it with no import | This only works if all files form one compilation unit, which is tool-dependent. | 3.12.1 | — | Put it in a package | low |
| enums | "The enum you define here becomes the state register type" (for fsm) | The fsm lesson defines a different enum (IDLE, READING, WRITING). | — | fsm/mem_ctrl.sol.sv | Align them | low |
| fsm | Moore dfn "outputs glitch-free and registered" | In this lesson the outputs are combinational (`always_comb` decode of state), so they are neither registered nor guaranteed glitch-free. | — | mem_ctrl.sol.sv | "outputs depend only on state" | med |
| fsm | "A Moore FSM separates state memory from output computation into two always blocks" | This confuses the Moore/Mealy distinction (whether outputs depend on inputs) with the two-process coding style. | — | — | Separate the two ideas | med |
| fsm | testbench | Reset is never asserted: `rst_n=1` before the first edge, and state leaves 'x through the `default:` arm. READING→IDLE and `ready==0` while busy are never checked. A design with no reset **and** READING stuck forever (ready=1) prints PASS. | RUBRIC | Mutation `/tmp/tut/audit/mut/fsm_stuck_noreset/` prints PASS | Hold rst_n=0 for 2 edges; check ready==0 in WRITING/READING and ready==1 one cycle after the read | med |
| fsm | fsm/sram.sv comment "The SRAM from the parameters lesson" | It is a different SRAM (combinational read, initialised mem), and rdata is never checked. | — | — | Fix the comment | low |
| classes | "leave rdata at its default (0)" (description and starter comment) | `logic [7:0]` defaults to 'x. The solution explicitly sets 8'h00, which contradicts "leave at default". | 6.8 Table 6-7 | spec | "default 'x; set it to 0 explicitly" or make it `bit [7:0]` | med |
| classes | `$display(t1.wdata); // prints FF` | With no format, $display prints decimal: 255. | 21.2.1.1 "displayed using the default decimal format in $display" | spec | `$display("%h", t1.wdata)` or "prints 255" | med |
| classes | "To get an independent copy, call new(...) again" | That creates a fresh object. A copy is `t2 = new t1;` (a shallow copy). | 8.12 | spec | Mention `new t1` | med |
| classes | testbench only checks handle sharing | An empty constructor and an empty `convert2string` still print PASS. The asserts only use `wdata` written by the tb itself. | RUBRIC | Mutation `/tmp/tut/audit/mut/cls_empty/`: `t1: ` / `t2: ` / PASS | Assert `t1.addr==5`, `t1.convert2string()=="WR[5]=a5"`, `t2.convert2string()=="RD[3]"` | med |
| CURRICULUM.md Part 1 | `sv/priority-enc` marked ✅ with score 22/27 | No such lesson exists (it is not in src/lessons/sv or meta.js). | — | ls src/lessons/sv | Mark 📝, or remove it | low |
| CURRICULUM.md Part 1 | "Teaches" column: data-types `$isunknown()`, enums "apostrophe cast `state_t'(bits)`", covergroup-basics `$get_coverage()`, tasks-functions "via virtual interface", counter "address stepping" | None of these appear in the lessons (grep finds no `$isunknown`, no `_t'(`, and no `get_coverage` in src/lessons/sv). `$get_coverage` is also a system function, while the lesson API would be `cg.get_coverage()`. | 19.9 | grep | Correct the Teaches column | low |
| CURRICULUM.md Part 1 | data-types "2-state `int`/`bit` (testbench)" | Same misconception as the lesson: 2-state types are synthesizable. | 6.11 | — | Drop "(testbench)" | low |

### Mox bugs

No SV-basics solution diverges between Mox and Xcelium. The cases below are places where **both** simulators deviate from the standard. They are recorded for completeness; neither is a Mox-only divergence.

1. **Static variable with an initializer in a procedural block is accepted.** Repro: `/tmp/tut/audit/repro/static-init-in-procedural-block.sv`.
   - Expected (6.21: "an explicit static keyword shall be required when an initialization value is specified as part of a static variable's declaration"; the spec example `top_illegal` is marked "should not compile"): compile error.
   - Mox actual: `warning: initializing a static variable in a procedural context requires an explicit 'static' keyword [-Wexplicit-static]`, then v is treated as static and initialized once at time 0. The output is `v=0 size=3` three times (pop never runs).
   - Xcelium actual: `*W,VARIST: Local static variable with initializer requires 'static' keyword.` with identical output. refdiff: both_pass, output equal.
   - Consequence: sv/queues-arrays hangs on both simulators. Making it an error (at least under a strict mode) would have caught the lesson bug. Low priority, since Mox matches the reference.

Checked and **not** a Mox bug:
- The infeasible `randomize() with` (committed randomization lesson): Mox reports `*W,SVRNDF`, keeps the previous values, and the assert fires, as 18.6.3 requires. Xcelium gives `*W,RNDOCS` and fails the same way. The old note about Mox issue #69 (inline constraints) does not reproduce.
- Modport access checks: Mox rejects `bus.clk` when it is not in the modport, and rejects writes to a modport `input`, as Xcelium does.

### Lessons with no issues

Every lesson has at least one finding, so no lesson gets a plain OK line. Parts that were checked and found correct:
- data-types: 2-state default '0 / 4-state 'x (6.8 Table 6-7), and X→0 on 4-state to 2-state assignment.
- always-comb: testbench is sound.
- events: testbench is sound.
- parameters: `$clog2` (20.8.1, "ceiling of the log base 2").
- packed-structs: MSB-first field layout (7.2.1), and the raw pattern 13'b1_0101_01001101.
- tasks-functions: automatic vs static explanation (13.3.1).
- coverpoint-bins: illegal_bins claim (19.5.6); cross-coverage m×n bins claim (19.6).
- fork-join: automatic-task claim (13.3.1).
- randomization (working-tree version): soft-constraint explanation (18.5.13, 18.7).

---

## SVA lessons audit (src/lessons/sva/*, 30 lessons + CURRICULUM.md SVA section)

Spec: IEEE 1800-2023. Sim evidence: refdiff (Xcelium vs Mox), tbs in /tmp/tut/audit/sva-tb/{sem,sem2,cov}/.
BMC evidence: native mox-bmc with the browser flags (`--assume-known-inputs -b 20`), driver
/tmp/tut/audit/sva-bmc/bmc.sh, results in /tmp/tut/audit/sva-bmc/all.txt plus one directory per lesson.

### Findings

| lesson | claim/example | what is wrong | IEEE clause | evidence | proposed fix | severity |
|---|---|---|---|---|---|---|
| (all BMC lessons) | Clicking "Verify" should prove the solution and give a counterexample for the starter | Almost every BMC lesson asserts a monitor whose ports are all free inputs. So the solution property can be violated, and BMC reports a counterexample (SAT) for the **solution**. Starters that compile have no property, so they "pass". The outcome is inverted. | 16.12.2 (an assert must hold on all traces), 16.14.2 (assume constrains the traces) | sva-bmc/all.txt: solution SAT for implication, clock-delay, rose-fell, req-ack, consecutive-rep, nonconsec-rep, nonconsec-eq, throughout, sequence-ops, stable-past, changed, disable-iff, abort, cover-property, local-vars, onehot, triggered, checker, always-eventually, until. Only formal-intro and seq-args give UNSAT. | Give each BMC lesson a small DUT that drives the checked signals, or add `assume property` constraints on the inputs. Alternatively, reword the lessons so that Verify is expected to find a counterexample. | high |
| checker | "Click Verify to confirm BMC proves both properties" | False: SAT, because of free inputs. | 16.12.2 | sva-bmc/checker_solution | as above | high |
| checker | `req \|=> ##[1:3] ack` = "ack within 1–3 cycles" | `\|=>` adds a cycle, so the window is 2–4 cycles after req. | 16.12.7 ("`\|=>` ... `\|-> ##1`") | sem.sv p5: ack 1 cycle after req. Xcelium fails at 305, Mox fails at 305. | `req \|-> ##[1:3] ack` | high |
| checker | `valid \|-> $stable(data)` = "data must not change on the next cycle while valid" | $stable compares with the previous tick, not the next one. With data loaded in the same cycle that valid rises, it fails. | 16.9.3 | sem.sv p6: Xcelium fails at 335, Mox fails at 335. | `valid \|=> $stable(data)`, or reword the spec to "since the previous cycle" | med |
| checker | "checker is automatically excluded from synthesis" | The LRM does not state this. Synthesis support is tool-defined. | 17 | – | Reword to "typically ignored by synthesis tools" | low |
| throughout | `$fell(cs_n) \|=> (!cs_n) throughout (mosi[*8])` for "an 8-bit transfer" | `mosi[*8]` requires **mosi==1** on all 8 cycles. Any 0 data bit fails. | 16.9.9: "exp throughout seq is an abbreviation for (exp)[*0:$] intersect seq"; 16.9.2 | sem.sv p1, data 1011_0010: Xcelium fails at 35 ("3 cycles, starting 15"). Mox fails at 95 (see Mox bug 5). | `(!cs_n)[*8]` or `(!cs_n) throughout (1'b1[*8])` / `##7 1'b1` | high |
| throughout | "throughout ≡ sync_reject_on(!expr) seq" | throughout is a sequence operator, whereas sync_reject_on is a property operator. The two are only equivalent as a top-level property. | 16.9.9, 16.12.14 | – | Say "as a property, behaves like ..." | low |
| sequence-ops | `valid \|-> (valid[*4]) intersect (ready[*4])` for "a 4-cycle burst" | Every cycle with valid high starts a new attempt, so the lesson's own 4-cycle burst fails for the attempts started on cycles 2, 3 and 4. | 16.12.6 (a new attempt at every tick), 16.9.6 intersect | sem.sv p2: Xcelium reports 3 failures at 155 (attempts starting 125, 135 and 145). Mox reports failures at 155, 165 and 175. | `$rose(valid) \|-> ...` | high |
| nonconsec-eq | `start \|=> ack[=3] ##[0:$] done` = "exactly 3 acks, then done must arrive" | The consequent is weak and can never fail. `b[=3] ##[0:$] c` ≡ `b[->3] ##[0:$] c` because the trailing `!b[*0:$]` is absorbed. It allows a 4th ack and never requires done. | 16.9.2 ("[=] ... allows the match to be extended by arbitrarily many clock ticks provided the Boolean expression is false"), 16.12.2 (weak) | sem.sv p3, 4 acks and no done: no failure on either Xcelium or Mox | `start \|=> ack[=3] ##1 done` (bounded), or `s_eventually`/`strong(...)` if liveness is intended. Drop "exactly". | high |
| nonconsec-eq / CURRICULUM | "[=m] equality across non-consecutive occurrences" | [=m] is nonconsecutive repetition. "Equality" is not a meaningful description of it. | 16.9.2 | – | "nonconsecutive repetition" | low |
| consecutive-rep | `start \|=> busy[*3]` = "busy high for exactly 3 cycles" | This enforces only "at least 3". busy can stay high longer. | 16.9.2 | sem.sv p7, busy high 6 cycles: no failure on either tool | Add `##1 !busy`, or say "at least" | med |
| consecutive-rep | SVG shows busy rising exactly on a posedge | Under Preponed sampling the edge where busy rises samples 0, so the diagram as drawn would fail | 16.5.1 | – | Draw the transition after the edge | low |
| recursive | `property p_lock_hold; lock && !unlock \|=> p_lock_hold;` | This is a tautology: it imposes no obligation, so it can never fail. The description says it is "equivalent" to `lock && !unlock \|=> lock`, which is false. | 16.12.17 | sem2.sv p12_rec_desc: Xcelium reports no failure when lock drops without unlock. The fixed form (next row) fails at 145. | `property p_held; unlock or (lock and nexttime p_held); endproperty` (i.e. `lock until unlock`) | high |
| recursive | "must use \|=> to avoid a zero-time loop" | Too strong. The restriction is only that each recursive instance occurs after a positive advance in time, which `##1` or `nexttime` also satisfy. | 16.12.17 Restriction 3: "every instance of p shall occur after a positive advance in time" | – | Reword | low |
| recursive | "BMC proves all three hold" | False: free inputs give SAT, and Mox crashes on the `disable iff` Boolean property (Mox bug 3) | 16.12.2 | sva-bmc/recursive_solution | see the systemic row | high |
| formal-assume | `assume property (rst \|-> state==0)`; "Verify to formally prove state 3 is unreachable" | The assume does not constrain cycle 0 when rst=0, so the initial state is free and state 3 is reachable. In simulation the assume itself fails at 5ns because state is X at the first edge. | 16.14.2 | fa/fa1.sv, a disable-iff-free equivalent of the solution: SAT. fa2/fa3.sv with `initial assume property (@(posedge clk) rst);`: UNSAT. Sim: Xcelium "__assert_1 has failed" at 5 NS; Mox "SVA assumption failed at time 5000000 fs". The actual solution crashes Mox BMC (bug 3). | Add `initial assume property (@(posedge clk) rst);`, or have the DUT reset through an initialised register | high |
| disable-iff | "While the reset condition is true, the property evaluates as vacuously true" | A disabled evaluation is neither a success nor a vacuous success: no action block runs, and it does not count. It also applies to in-flight attempts whenever the condition becomes true during the evaluation. | 16.12: "A disabled evaluation of a property does not result in success or failure"; 16.14.3 | – | "the attempt is *disabled* (neither pass nor fail)" | med |
| disable-iff | Lesson intends the starter (no disable iff) to fail and the solution to pass under BMC | Both give SAT, so the lesson cannot show what disable iff does | – | sva-bmc/disable-iff_{starter,solution} | Drive the inputs from a DUT with a reset | med |
| abort | "reject_on(cond) seq is equivalent to (!cond) throughout seq" | reject_on is **asynchronous**: it checks at every time step, not only at clock ticks. Only sync_reject_on matches the throughout form. | 16.12.14: "accept_on and reject_on ... represent asynchronous resets"; the LRM's own example: `sync_reject_on(stop) put[->2]` "can also be written as ... !stop throughout put[->2]" | sem2.sv p10, err glitch between ticks: Xcelium fails p10_reject at 35 and does not fail the sync or throughout forms. Mox misses it (Mox bug 6). | Replace with sync_reject_on in the equivalence | med |
| triggered | ".triggered can only be used in the antecedent ... not inside another sequence" | False. `s.triggered` is a Boolean that may appear in consequents and in other sequences. | 16.13.6 ("detect its end point in another sequence ... triggered") | sem2.sv p11 `a \|=> s_b.triggered`: accepted and fails at 85 on both Xcelium and Mox | Delete the restriction | med |
| triggered | .matched description | Loose: .matched is for sequences clocked by a different clock, and it is only allowed in sequence expressions | 16.13.5 | – | Tighten | low |
| always-eventually | "weak property (eventually) ... satisfied vacuously" | Unranged `eventually` is illegal (only `eventually [range]` or `s_eventually`). "Vacuously" is a misuse: weak means no finite trace can refute it. | 16.12.13 grammar (`eventually [ constant_range ]`), 16.14.8 | – | "weak `eventually [m:n]`", "cannot fail on a finite trace" | med |
| always-eventually | "BMC can only falsify them within its bound" | A finite prefix cannot falsify liveness (s_eventually). Refuting it needs a lasso/loop. A BMC "counterexample" at the bound is not a real violation. | 16.12.2, 16.12.13 | Mox BMC reports SAT at the bound | Explain bounded liveness / lasso counterexamples | med |
| always-eventually | "IEEE 1800-2012 features" | always/s_eventually/until were introduced in 1800-2009 | – | – | "1800-2009" | low |
| until | "If q never occurs the property still holds (vacuously)" | Misuse of "vacuous": weak until holds when p holds forever | 16.12.12, 16.14.8 | – | "weak until holds if p holds forever" | low |
| clock-delay | Implies that only a wrong range gives a counterexample | Free mem_ack gives SAT even for the solution | 16.12.2 | sva-bmc/clock-delay_solution | see the systemic row | med |
| rose-fell | Spec says "rise within 1–2 cycles" (the solution `\|=> ##[0:1]` matches), but the starter TODO says "within 0–1 cycles" | Inconsistent | – | – | Align the TODO text | low/med |
| rose-fell | data-card: $rose = "was 0 the previous cycle" | $rose is true when the LSB changed to 1, which includes X→1 | 16.9.3 | – | "was not 1" | low |
| stable-past | $past "is evaluated in SVA's Observed region" | Its operand values come from the Preponed region | 16.5.1, 16.9.3 | – | "uses sampled (Preponed) values" | low/med |
| stable-past | Blockquote: `$stable(d)` ≡ `d == $past(d)` (the data-card says `===`) | $stable uses case equality, so X→X is stable, whereas `==` yields X and the check fails | 16.9.3 | sem.sv p9, X→X: $stable passes, `==` fails at 465 on both tools | Use `===` consistently | low/med |
| changed | "to ignore X transitions use !=" | `!=` involving X yields X, which is treated as false, so the check fails rather than ignoring the transition | 11.4.5, 16.3 | – | Reword or drop | low |
| vacuous-pass | "cover ... pass action only fires when the antecedent actually matched" | The LRM does not guarantee this: the pass action runs "once for each successful evaluation attempt", and pass actions include vacuous successes by default. Xcelium and Mox happen to skip vacuous successes. | 16.14.3, 20.11 | cov.sv, Xcelium with -abvcoveron | Cover a sequence (`cover property ($rose(req) ##[1:2] gnt)`) rather than an implication | low/med |
| cover-property | Same pass-action claim | Same as vacuous-pass | 16.14.3 | – | Same | low |
| concurrent-sim | "cover counts how many times the property was exercised" / "we now formally verify" | Imprecise: the count is per successful attempt, with vacuous successes counted separately. This is also a simulation lesson, not formal verification. | 16.14.3 | – | Reword | low |
| immediate-assert / CURRICULUM | Curriculum lists deferred assertions (#0/final) | The lesson does not cover them | 16.4 | – | Align | low |
| immediate-assert | Solution is immediate asserts on free inputs | Violable under BMC. Mox BMC also crashes (bug 3b). | 16.3 | sva-bmc/immediate-assert_solution | see the systemic row | med |
| sequence-basics | Solution has a pass action | Mox BMC crashes (bug 4). It would be SAT anyway. | 16.14.1 | sva-bmc/sequence-basics_solution | Remove the pass action, or fix Mox | med |
| lec | "in seconds, for any circuit size" | Overclaim | – | – | Soften | low |
| isunknown | "formal tools use two-state logic where X and Z do not exist" | Imprecise: many formal tools model X. Mox BMC uses `--assume-known-inputs`. | 20.13 | – | Reword | low |

Starter check: all BMC starters with an empty property body fail to compile, which counts as not passing. The starters that do compile (immediate-assert, cover-property, onehot, formal-assume, formal-intro) "pass" because they have no property to check. The concurrent-sim and formal-assume sim starters pass (no assertions). The isunknown sim starter does not compile.

### Mox bugs

| # | repro | expected (clause) | Mox actual | Xcelium actual |
|---|---|---|---|---|
| 1 | /tmp/tut/audit/repro/cov_seq.sv | c_fixed, c_range, c_rose and c_seqk all hit at t=35000 (16.14.3: pass action for each successful attempt) | Only c_fixed and c_rose hit. `cover property (a ##[1:2] b)` and `cover sequence (a ##[1:2] b)` never fire. | All 4 hit (cov_seq.xrun.log, `-abvcoveron`) |
| 2 | /tmp/tut/audit/repro/bmc_weak_goto.sv (`a \|-> b[->1]`) | UNSAT: a weak sequence has no finite refutation (16.12.2) | `BMC_RESULT=SAT Assertion can be violated!` (b stays 0 until the bound). The same happens with `a \|=> ##[0:$] b`, `weak(##[1:$] b)` and nonconsec-eq. | n/a (BMC) |
| 3a | /tmp/tut/audit/repro/bmc_disable_bool.sv (`disable iff (rst) a`) | Legal (16.12); SAT | Crash: `failed to legalize operation 'ltl.not' ... (!smt.bv<1>) -> !ltl.property`. Works as `1'b1 \|-> a`. | n/a |
| 3b | /tmp/tut/audit/repro/bmc_imm_compound.sv (`always @(posedge clk) assert (!(a && b));`) | Legal (16.3); SAT | Same `ltl.not` legalize crash. `assert(a)` and `assert(!a)` work. | n/a |
| 4 | /tmp/tut/audit/repro/bmc_pass_action.sv (assert with pass and fail actions) | Legal (16.14.1); SAT, with action blocks ignored | Crash: `'llhd.process' op cannot be handed off from llhd-structuralize-processes to llhd-eliminate-processes`. A fail-only action works. | n/a |
| 5 | /tmp/tut/audit/repro/late_failure.sv (`a \|=> b[*4]`, b drops on the 2nd cycle) | Failure reported at 35ns, when a match becomes impossible (16.14.1, 16.9.2) | Failure reported at 55ns, the end of the bounded window. The same happens for sem.sv p1 (95 vs 35) and p2 (155/165/175 vs 155). | Fails at 35 NS |
| 6 | /tmp/tut/audit/repro/reject_on_async.sv | a_async fails, because reject_on is asynchronous and err is high between ticks during the evaluation (16.12.14) | No failure: reject_on is treated like sync_reject_on | "(time 35 NS) Assertion tb.a_async has failed (3 cycles, starting 15 NS)" |

Harness note (not a Mox bug): refdiff/refsim does not pass `-abvcoveron`, so Xcelium prints no cover pass actions and cover lessons always diff against Mox.

### OK

- OK: req-ack
- OK: nonconsec-rep
- OK: seq-args (BMC proves it: UNSAT)
- OK: formal-intro (UNSAT; the starter "passes" only with a no-property warning)
- OK: implication (semantics correct; BMC SAT only because of the systemic free-input issue)
- OK: onehot (semantics correct; the systemic BMC issue applies)
- OK: local-vars (minor: in the template, `\|=> ##N` means N+1 cycles)
- OK: isunknown (sim: Mox and Xcelium agree; one low wording note above)
- OK: lec (low overclaim only)
- OK: CURRICULUM followed-by (`#-#`/`#=#`) description

---

## Tutorial audit: uvm / rtl / cocotb / mlir

**Method**
- **Simulators:** Mox is native `wt/landing/build-dev-fast`. Xcelium is `refsim -uvm -uvmhome CDNS-IEEE`, run through `/tmp/tut/bin/run-lesson.sh`. Coverage lessons were rerun with `/tmp/tut/audit/run-cov.sh`, which adds `--coverage-report` / `-coverage functional`. The browser adds the coverage flag automatically via `coverageArgs()`.
- **UVM scratch copies:** the UVM lessons were run from scratch copies in `/tmp/tut/audit/uvm-scratch/<lesson>/`, made with `mkscratch.py`. The copies work around the two known issues (a) and (b).
- **Evidence locations:**
  - Run directories: `/tmp/tut/runs/uvm_*`, `/tmp/tut/runs/cov_*` and `/tmp/tut/runs/rtl_*`.
  - Logs: `/tmp/tut/audit/logs/`.
  - cocotb runs (real cocotb 2.0.1 + Icarus): `/tmp/tut/audit/cocotbchk/`.
  - MLIR runs: `/tmp/tut/audit/mlir/`.
- **Budget:** about 30 Xcelium runs, all sequential.

**Known issues (not re-investigated; affected lessons listed)**
- **(a) mem_item field macros come before the field declarations.** Affected lessons:
  - seq-item (both `.sv` and `.sol.sv`, and the description.html example)
  - sequence, driver, constrained-random, monitor, env
  - covergroup, cross-coverage, coverage-driven, factory-override
- **(b) `uvm_top.finish_on_completion = 0;` in tb_top.** Affected: tb_top in all 12 UVM lessons.

**Transcripts:** after the workarounds, the Mox and Xcelium UVM_INFO transcripts match line for line in every lesson. The differences are:
- the random values;
- Xcelium's extra CATCHER summary line;
- Xcelium drops non-ASCII characters (`—`, `→`, `×`) from string literals, with *W,NONPRT.

### Findings

| lesson | claim/example | what is wrong | clause/source | evidence | proposed fix | severity |
|---|---|---|---|---|---|---|
| uvm/cross-coverage | The starter should fail until the cross is added | With the missing `;` fixed, the **starter prints PASS on both simulators** (100%). cp_addr and cp_we alone reach the 100% goal, so the cross is never required. | LRM §19.11: the type coverage is the weighted average of the items. With no cross item, the covergroup reaches 100% from its coverpoints. | `cov_` run of `uvm-scratch-semi/cross-coverage` starter: "PASS" on Mox and Xcelium | Add `option.weight = 0;` to cp_addr and cp_we. The covergroup score then equals the cross score, and the starter reads 0%. Alternatively, check `mem_cg.addr_x_we.get_coverage()`. | high |
| uvm/covergroup, uvm/cross-coverage | The starter compiles and runs (the student only fills in bins) | The starter has `$fatal(0, $sformatf(...))` with no `;` before `endfunction`, so it does not compile. | LRM A.6.4: statement_item requires `;` | Xcelium: *E,EXPSMC. Mox: "expected ';'". | Add the `;`. | high |
| uvm/reporting | The solution prints PASS iff the test passed (RUBRIC) | The solution prints PASS unconditionally, even though its own run has UVM_ERROR=1. | RUBRIC.md: PASS iff UVM_ERROR==0 | Both simulators: "UVM_ERROR : 1" followed by "PASS" | Gate PASS on `uvm_report_server::get_server().get_severity_count(UVM_ERROR)==0`, or remove the demo error. | med |
| uvm/reporting | "run_phase is the only time-consuming phase" | There are 12 runtime task phases (reset/configure/main/shutdown, each with pre_ and post_) running in parallel with run_phase. | uvm-core `src/base/uvm_runtime_phases.svh`; 1800.2 §9.8.2 | – | Say "run_phase (and the runtime sub-phases) are the only task phases". | low |
| uvm/reporting | "Forgetting drop_objection → simulation runs forever" | UVM stops the run with a `PH_TIMEOUT` fatal at `UVM_DEFAULT_TIMEOUT` (9200 s). | `uvm_phase_hopper.svh:562-587`; `uvm_objection_defines`/`UVM_DEFAULT_TIMEOUT` | – | "…hangs until the phase timeout (9200 s by default) fires a fatal". | low |
| uvm/reporting | "`uvm_fatal immediately calls $finish" | `uvm_root::die()` first runs pre_abort on all components and report_summarize, then calls $finish. | `uvm_root.svh:157-182` | – | "…ends the test (after printing the report summary)". | low |
| uvm/driver (also the monitor/env/cov lessons that reuse sram.sv) | "The SRAM has a 1-cycle (registered) read latency". The waveform shows rdata one cycle late. | The UVM `sram.sv` reads combinationally: `assign rdata = mem[addr];`. Note that the Part 1 `sv/always-ff/sram_core` does have a registered read, so the two DUTs disagree. | `src/lessons/uvm/*/sram.sv` | The driver's sampled timing is the same on both simulators; rdata is valid in the same cycle. | Either make the UVM sram register rdata, or fix the text and figure. | med |
| uvm/driver | The test checks that the driver works | `read_c` is active, so every item is a read of zero-initialized memory and rdata is always 0. A starter that only fixes the config_db get() passes without driving anything meaningful. | lesson files | The transcripts show only RD items. | Disable read_c, or write then read back and compare. | low-med |
| uvm/monitor | "// Enable writes too". The description example says "driver writes addr=3 …". | read_c is still active, so no writes happen. The scoreboard's write branch is never exercised and the description example never occurs. | lesson files | 0 writes on both simulators | Call `read_c.constraint_mode(0)`, or remove the stale comment and example. | med |
| uvm/monitor | The monitor "reconstructs completed transactions" | The monitor samples every clock, not once per handshake. 8 items produce 14 scoreboard checks, including duplicates. | lesson monitor run_phase | 14 checks from 8 items on both Mox and Xcelium | Sample only on a valid/handshake cycle (for example, when the driver-asserted strobe is seen). | med |
| uvm/monitor | The card calls `uvm_analysis_imp` an "import" | "imp" is short for implementation. | uvm-core `uvm_analysis_port.svh` (`uvm_analysis_imp`: "implementation") | – | Change the wording. | low |
| uvm/covergroup, uvm/cross-coverage | "Complete report_phase …" | The starter's report_phase is already complete. The TODO is only in the bins/cross. | lesson files | – | Remove the step. | low |
| uvm/cross-coverage | "28 required bins", and step 3 says "naming which bins were missed" | There are 30 bins including the ignored/illegal ones, so the label is ambiguous. The solution never names missed bins. | lesson files | – | Clarify the count, or drop the "naming" claim. | low |
| uvm/constrained-random | Scenario 3: disabling weighted_c with `constraint_mode(0)` makes interior addresses appear | The check (`interior>0`) cannot detect whether constraint_mode(0) was called: with weighted_c on, the dist still gives about 70% interior per draw. The FAIL message's explanation is therefore wrong. | LRM §18.5.3 (dist: `:=` vs `:/`), §18.9 | The starter (no constraint_mode call) got "PASS: 12/16 interior". Separately, `dbg/dist.sv` confirms Mox's dist frequencies are correct. | Test something that only holds with the constraint off (for example, a uniform histogram), or have weighted_c force boundaries only. | med |
| uvm/constrained-random | Scenario 2 prints "PASS: all 4 items were boundary writes" | The message is printed unconditionally. | lesson file | – | Count boundary writes and check the count. | low |
| uvm/constrained-random | The inline `with` constraint "overrides for that one call" | Inline constraints are AND-ed with the class constraints; they do not override them. | LRM §18.7: "the inline constraints … are applied along with the object constraints" | – | Change the wording. | low |
| uvm/factory-override | "convert2string() calls get_type_name() … you'll see [mem_item]/[corner_mem_item]" | convert2string prints only `"WR [a] = d"` / `"RD [a]"`. No type name appears in the output. | lesson mem_item.sv | No type name in either transcript | Prepend `get_type_name()` in convert2string, or fix the text. | med |
| uvm/ral | "This lesson ships a hand-rolled register model that already compiles and simulates in MOX" | The starter `mem_test_ral.sv` calls `.set()`/`.get()` on `logic` variables, so it does not compile on either simulator. | lesson files | Starter compile errors on Mox and Xcelium | Change the wording ("…once you complete the TODOs"). | low-med |
| uvm/ral | The mirror value is "what software wrote" | The UVM mirrored value is the model's best estimate of the DUT register value. It is updated by reads, writes and predict(). | 1800.2 §18.5 (`uvm_reg_field::get_mirrored_value`); uvm-core `uvm_reg_field.svh` | – | Change the wording. | low |
| uvm/* | Non-ASCII characters (`—`, `→`, `×`) in `$display` / `uvm_info` strings | Non-ASCII characters in string literals are not portable. Xcelium drops them (*W,NONPRT). | LRM §5.9 (string literals are ASCII) | xrun logs | Use ASCII. | low |
| rtl/synthesis-gotchas | "It will fail on sel=2'b11 because the missing case produces an X output" | In simulation, `y` **holds its previous value** (0100). It is a latch in simulation too, not X. | LRM §12.5 (no matching item → no statement executes); §9.2.2.2 | Both simulators: `FAIL 11: got 0100 (latch?)` | "…y keeps its old value (0100) — that *is* the latch". | med |
| rtl/synthesis-gotchas | "Two fixes … 2. Add unique", and unique lets the tool "build a parallel MUX tree instead of a priority chain" | `unique` does not fix a latch in simulation. On an incomplete case it only adds a violation report; synthesis tools may treat it as full_case, which causes a sim/synth mismatch. For this decoder the case items are already constant and mutually exclusive, so `unique` changes no hardware. | LRM §12.5.3: unique-case asserts that the case_items do not overlap and (§12.5.3 with §12.4.2) reports a violation if none match | – | Present `unique` as a checking aid, and cover-all/default as the latch fix. | low-med |
| rtl/synthesis-gotchas | "if … none matches, the simulator reports an **error**" | The LRM requires a "violation report" whose form is tool-specific. It is commonly reported as a warning. | LRM §12.4.2.1: "A tool-specific violation report mechanism is then used" | – | Say "reports a violation". | low |
| rtl/rtl-to-gates | "The non-blocking `<=` is the key: it means latch this value at the clock edge"; "Every line maps to exactly one primitive" | The flip-flop comes from the edge event control `@(posedge clk)`, not from `<=`. A W-bit mux_reg is W muxes plus W DFFs. | LRM §9.4.2 (edge event control), §10.4.2 (NBA only defers the update) | – | Change the wording. | low |
| cocotb/edge-triggers, cocotb/clockcycles-patterns | Run in the browser | The browser shim has **no `ReadOnly`**, and `Clock()` accepts only `units=`, not `unit=`. Both tests fail immediately in the browser with ImportError (and would then hit a TypeError). | `src/runtime/cocotb-shim.py`: the triggers module exports only Timer, RisingEdge, FallingEdge and ClockCycles; `Clock.__init__(self, signal, period, units='ns')` | Loading the shim in Python: `ImportError cannot import name 'ReadOnly' from 'cocotb.triggers'`, `TypeError … unexpected keyword argument 'unit'` (`cocotbchk/chk.py`). Real cocotb 2.0.1 + Icarus passes the solution and fails the starter for both lessons. | Add `ReadOnly` (VPI cbReadOnlySynch; `vpi-abi.js` already defines it) and accept both `unit`/`units` in the shim's Timer and Clock. | high |
| cocotb/first-test, cocotb/clock-and-timing vs edge-triggers, clockcycles-patterns | API style | The lessons mix `units=` (cocotb 1.x; deprecated in 2.0, which emits DeprecationWarning) with `unit=` (2.0 only; TypeError on 1.x). No single cocotb version runs all four lessons cleanly. | cocotb 2.0.1 signatures: `Timer(time, unit='step', *, units=None)`, `Clock(signal, period, unit='step', …)` | DeprecationWarning in `cocotbchk/*` runs | Standardize on `unit=` and make the shim accept it. | low-med |
| cocotb/first-test | `__main__` block: `from cocotb.runner import get_runner`; `runner.build(verilog_sources=…, toplevel=…)`; `runner.test(toplevel=…)` | `cocotb.runner` no longer exists in 2.x (it is now `cocotb_tools.runner`). The `toplevel=` keyword was renamed `hdl_toplevel=` (1.8+ and 2.x), so the block fails on every released version with a runner. | cocotb 2.0.1: `Runner.build(..., sources, hdl_toplevel, ...)`, `Runner.test(test_module, hdl_toplevel, ...)` | `ModuleNotFoundError: No module named 'cocotb.runner'`; with a module alias, `TypeError build() got an unexpected keyword argument 'toplevel'` | Use `cocotb_tools.runner` and `hdl_toplevel=`. | low |
| cocotb/clock-and-timing | "Higher-level helpers like RisingEdge and Clock are built on top of [Timer]" (also on the card) | RisingEdge/FallingEdge are GPI value-change callback triggers and are independent of Timer. In 2.x, Clock defaults to a C++ GPI clock (`impl='gpi'`). Only ClockCycles is built on another trigger (RisingEdge). | cocotb `triggers.py` (`RisingEdge` is a `_EdgeBase`/GPI trigger); cocotb 2.0.1 `Clock(..., impl=None → 'gpi')` | – | Change the wording. | low-med |
| cocotb/first-test | "Add the missing `assign` statement" | The solution uses `always @(*) X = A + B;`. | lesson files | – | Align the text with the solution. | low |
| mlir (all 4) | Run executes the testbench | In the browser, Run simulates only the design file. `pickTopModules()` picks the alphabetically first `hw.module` (adder, priority_enc, sram_core, dff_before), and `pickMlirSourcePath()` passes only that one file to mox-sim. The `*_tb.mlir` files (the PASS/FAIL checks) never run, and output is empty. | `src/runtime/mox-adapter.js:137-155, 366-391, 1631` | `mox-sim adder.mlir --top adder` gives no output. Concatenating design and tb with `--top tb` gives PASS for all 4 lessons, and a mutated DUT gives FAIL (`/tmp/tut/audit/mlir/`). | Concatenate all .mlir files and use top `tb`. | med |
| mlir/lowering | "The left branch (LowerSeqToSV → ExportVerilog) is used when you click **Run**" | Run uses `mox-verilog --ir-llhd` and then `mox-sim` on LLHD. It never goes through the sv dialect or ExportVerilog. | `mox-adapter.js:1438` (`design.llhd.mlir`), ~1660 (mox-sim) | – | "Run takes a third path: Moore → LLHD → mox-sim". | med |
| mlir/lowering | Stage 3 "ExportVerilog output": `output [7:0] q); reg [7:0] q; always @(posedge clk) q <= d;` | This redeclares an ANSI port in the module body, which is illegal SV. It is also not what ExportVerilog emits; the real output is `reg [7:0] q_0; always @(posedge clk) q_0 <= d; assign q = q_0;` (and `always_ff` for dff_before). | LRM §23.2.2.2: "The port identifier shall not be redeclared, in part or in full, inside the module body." | `mox-opt lowering.mlir --lower-seq-to-sv --export-verilog` | Paste the real output. | med |
| mlir/lowering | "LowerSeqToSV converts every seq.compreg into sv.reg plus sv.always" | By default the pass emits `sv.alwaysff` (always_ff) for compreg. | `lib/Conversion/SeqToSV/SeqToSV.cpp:135-190` ("Lower CompRegOp to sv.reg and sv.alwaysff") | `mox-opt --lower-seq-to-sv` output | Say sv.alwaysff. | low |
| mlir/lowering | Pass names `LowerHWtoBMC`, `LowerBMCToSMT` | No such passes exist. The real ones are `--lower-to-bmc` and `--convert-verif-to-smt` (plus convert-hw/comb-to-smt), followed by the SMTLIB export. | `mox-opt --help` | – | Rename. | low |
| mlir/comb | `comb.icmp eq, %a, %b : i1` | Wrong syntax on two counts. There is no comma after the predicate, and the type annotation is the operand type (`comb.icmp eq %a, %b : i8`). | mox-opt | "expected SSA operand"; without the comma, "'i1' vs 'i8'" | Fix the snippet. | low-med |
| mlir/seq | Description snippets: `seq.hlmem @sram_core<i8, 16>[%clk]`, `seq.write %mem[%addr], %wdata, %we : <i8, 16>`, `seq.read %mem[%addr], latency 0 : <i8, 16>` | None of the three parse. The correct forms are in `sram_core.mlir`: `seq.hlmem @n %clk, %rst : <16xi8>`, `seq.write %m[%a] %d wren %we { latency = 1 } : !seq.hlmem<16xi8>`, and `seq.read %m[%a] { latency = 0 } : !seq.hlmem<16xi8>`. | mox-opt | "expected SSA operand" / "expected ':'" (`/tmp/tut/audit/mlir/t.mlir` checks) | Copy the working syntax from the file. | low-med |
| mlir/seq | sram_core.mlir: "compreg stands for compiled register: reset handling and clock-enable are optional fields added later in the lowering pipeline" | compreg is the "computational register". Reset and clock-enable are optional operands of `seq.compreg` and a separate `seq.compreg.ce` op, not something added later. (description.html itself states this correctly.) | `docs/Dialects/Seq/RationaleSeq.md` ("The computational register operation"); `SeqOps.td:26-53` | – | Fix the comment. | low |
| mlir/intro | The MOX card says "(Circuit IR Compilers and Tools)"; the pipeline shows the SMT export coming out of the sv dialect | "Circuit IR Compilers and Tools" is a leftover of the CIRCT expansion. The SMT path branches from hw/comb/seq, not from sv. SV import also goes through Moore first. | – | – | Fix the card and diagram. | low |
| mlir/*_tb.mlir | The FAIL branch uses `sim.terminate success, quiet` | A failing check exits with success. It still prints FAIL. | – | – | Use `failure`. | low |
| CURRICULUM.md | Status of uvm/ral; sections | uvm/ral is marked 💡 (planned) and listed as a gap, but the lesson exists. There are no rtl or mlir sections. The cocotb/edge-triggers title differs from meta.js ("Edge Triggers and Clock"). | CURRICULUM.md vs `src/lessons/meta.js` | – | Update the curriculum. | low |

### Mox bugs

1. **Semantic diagnostics are lost under `--uvm-path`** (repro: `/tmp/tut/audit/repro/undeclared_member_diag.sv`).
   - **Without `--uvm-path`:** mox-run correctly reports slang's "use of undeclared identifier" and "no member named".
   - **With `--uvm-path` (every UVM lesson):** those messages are replaced by "invalid expression" / "convertFunction failed".
   - **In the seq-item starter (line 59) and ral starter (line 53):** the only message is a misleading `cannot convert '!moore.i1' to class handle type '!moore.class<@mem_item>'` at a use site.
   - **Xcelium:** reports *E,UNDIDN / *E,NOTCLM.
   - **Impact:** the error students most often hit in the UVM lessons produces a useless message.
2. **(low) get_coverage() returns 0.0 silently without `--coverage-report`.** Xcelium prints *N,COVNSM in the same situation. The browser is not affected because `coverageArgs()` adds the flag. A warning would still help native users.
3. No simulation mismatches: in every UVM, rtl and MLIR lesson run, the Mox output matched Xcelium's apart from random values.

### docs/mox-bugs status (current native Mox)

| file | status | evidence |
|---|---|---|
| bug-automatic-task-outer-interface-mlir-region-isolation.md | **FIXED**, including the follow-up sim hang (GitHub #8) | `/tmp/tut/audit/repro/mb/auto.sv` (the doc's example) compiles and prints PASS at 16 ns |
| bug-bits-hierarchical-parameterized-port.md | **FIXED** | `/tmp/tut/audit/repro/mb/bits.sv` prints PASS (`$bits(u_small.addr)==3`) |
| bug-virtual-if-in-class-method-mlir-region-isolation.md | **FIXED** | The driver, monitor, env, covergroup, cross-coverage and coverage-driven lessons (vif accessed in run_phase) compile and run, with timing identical to Xcelium |
| bug-uvm-constraint-mode-unimplemented.md | **FIXED** | constraint_mode(0) and randomize() with {…} behave correctly in seq-item Check 2 and constrained-random; `dbg/dist.sv` shows correct frequencies and mode switching |
| bug-uvm-phase-cleanup-hangs-and-factory-override.md | **FIXED** (both parts) | run_test() returns with a forever driver (sequence and driver lessons end normally); factory-override produces corner_mem_item addresses {0,15} on both simulators |
| bug-mox-sim-global-state-not-reset-between-callmain.md | **Not testable natively** | This is WASM-only (repeated `Module.callMain`); not exercised here |

All five natively testable docs describe fixed bugs. They should be marked FIXED or removed.

### OK
- **uvm/sequence:** OK apart from known issue (a). The handshake description is accurate, and the ordering is identical on both simulators.
- **uvm/seq-item:** OK apart from known issue (a) and Mox bug 1 on the starter.
- **uvm/env:** OK apart from (a), (b) and the shared SRAM latency text. Build is top-down and connect is bottom-up, as described.
- **uvm/coverage-driven:** OK apart from (a) and (b). The starter reaches 53-55% and fails with $fatal; the solution reaches 100% and prints PASS.
- **rtl/rtl-to-gates:** functionally OK. The solution passes and the starter fails (X) on both simulators; only low-severity wording issues.
- **cocotb/first-test, cocotb/clock-and-timing:** functionally OK in the shim and in real cocotb 2.0.1 (the solution passes, the starter fails).
- **mlir/intro, comb, seq, lowering:** all `.mlir` files parse with mox-opt. Every design+tb pair prints PASS under mox-sim with `--top tb`, and a mutated DUT prints FAIL.
