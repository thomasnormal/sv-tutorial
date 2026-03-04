# Curriculum Tracker

Status of every lesson and a roadmap of what still needs to be written.
Lessons are keyed by slug (matches `src/lessons/index.js`). Reference material
from https://github.com/karimmahmoud22/SystemVerilog-For-Verification (KM repo)
and *SystemVerilog Assertions and Functional Coverage* by Ashok B. Mehta,
3rd ed. (Springer, 2020) — cited as **Mehta §N** throughout — are noted
where they are directly usable as a basis for a lesson.

Legend: ✅ exists · 📝 planned (prioritised) · 💡 optional/stretch

Scores are out of 27 (9 dimensions × 3 max). See `RUBRIC.md` for the rubric.
Flag numbers identify the weak dimension(s): 1=Concept Focus, 2=Starter Calibration,
3=Description Quality, 4=Progression, 5=Dual Coding, 6=Solution Idiom,
7=Concept Importance, 8=Lesson Novelty, 9=Visual Novelty.

---

## Part 1 — SystemVerilog Basics

### Chapter: Introduction
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `sv/welcome` | Welcome | ✅ | 23/27 ⚠️4,5 | — | `module`/`endmodule`, `$display`, simulation loop, tutorial roadmap |
| `sv/modules-and-ports` | Modules and Ports | ✅ | 25/27 ⚠️1,4 | `sv/welcome` | port directions (`input`/`output`), `logic`, vectors, `assign`, module instantiation |
| `sv/data-types` | Data Types | ✅ | 25/27 ⚠️5 | `sv/modules-and-ports` | 4-state `logic` (RTL) vs 2-state `int`/`bit` (testbench), X state, `$isunknown()` |

### Chapter: Combinational Logic
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `sv/always-comb` | always_comb and case | ✅ | 27/27 | `sv/modules-and-ports` | `always_comb`, `case`/`if` in procedural block, combinational output |
| `sv/priority-enc` | Priority Encoder (casez) | ✅ | 22/27 | `sv/always-comb` | `casez`, `?` wildcard match, priority-ordered selection |
| `sv/assign-operators` | Operators & Arithmetic | 📝 | — | `sv/modules-and-ports` | `assign`, bit/reduction/ternary operators, signed arithmetic, overflow |

> Cover reduction operators (`|req`), ternary, signed arithmetic,
> overflow — sets up concepts used in SVA and UVM lessons.
> Ref: `TipsAndTricks/ExpressionWidth.sv`, `TipsAndTricks/Casting.sv`

### Chapter: Sequential Logic
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `sv/events` | Events | ✅ | 24/27 ⚠️4,5,7 | `sv/modules-and-ports` | `event`, `->` (post), `@(event_name)` (wait), concurrent-process synchronization |
| `sv/always-ff` | Flip-Flops with always_ff | ✅ | 26/27 ⚠️1 | `sv/modules-and-ports`, `sv/always-comb` | `always_ff`, `posedge`, non-blocking `<=`, unpacked array `mem[]`, 1-cycle read latency |
| `sv/counter` | Up-Counter | ✅ | 23/27 ⚠️1,8,9 | `sv/always-ff` | enable/reset counter, address stepping, `@(posedge clk)` in `initial` |
| `sv/shift-reg` | Shift Register | 📝 | — | `sv/always-ff` | bit shift, concatenation `{}`, serial-in/serial-out |

> Introduces `[*]` bus shift and multi-bit `always_ff`; prerequisite
> for pipeline assertions in Part 2.

### Chapter: Parameterized Modules
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `sv/parameters` | Parameters and localparam | ✅ | 24/27 ⚠️2,9 | `sv/always-ff` | `parameter`, `localparam`, `$clog2()`, parameterized port widths, generic instantiation |
| `sv/generate` | generate for / if | 📝 | — | `sv/parameters` | `generate for`/`if`, replicated instances, conditional elaboration |

> `for generate` to replicate instances; used in every real chip.
> A parameterised N-bit adder array is a natural exercise.

### Chapter: Data Types
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `sv/packed-structs` | Packed Structs | ✅ | 26/27 ⚠️4 | `sv/parameters`, `sv/always-ff` | `struct`, `packed`, `typedef`, `package`, bit-field layout, struct literal |
| `sv/typedef` | typedef and type aliases | 📝 | — | `sv/packed-structs` | standalone `typedef`, type parameters, abstract type reuse |
| `sv/arrays-static` | Static Arrays (packed & unpacked) | 📝 | — | `sv/always-ff`, `sv/packed-structs` | packed vs unpacked, multi-dimensional arrays, `$size`/`$dimensions` |

> `sv/typedef` and `sv/arrays-static` remain open.
> Packed arrays underpin multi-bit signals.
> Ref: `DataTypes/DataTypes.sv`, `Arrays/PackedArrays.sv`,
> `Arrays/Packed_UnpackedArrays.sv`

### Chapter: Interfaces & Procedures
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `sv/interfaces` | Interfaces | ✅ | 25/27 ⚠️2,9 | `sv/modules-and-ports`, `sv/parameters` | `interface`, signal bundling, interface functions (`sprint()`), dot-notation access |
| `sv/modports` | Modports | ✅ | 25/27 ⚠️2,9 | `sv/interfaces` | `modport` (initiator/target), direction enforcement, `virtual interface` for UVM |
| `sv/tasks-functions` | Tasks | ✅ | 24/27 ⚠️1,9 | `sv/interfaces`, `sv/parameters` | `task` (automatic, timing-aware), `function` (pure), driving DUT via virtual interface |
| `sv/clocking-blocks` | Clocking Blocks | 💡 | — | `sv/interfaces` | `clocking` block, input/output skew, synchronous testbench sampling |

### Chapter: State Machines
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `sv/enums` | typedef enum | ✅ | 24/27 ⚠️2,9 | `sv/always-ff`, `sv/always-comb` | `typedef enum`, named constants, enum in `case`, apostrophe cast `state_t'(bits)` |
| `sv/fsm` | Two-Always Moore FSM | ✅ | 27/27 | `sv/enums`, `sv/always-ff`, `sv/always-comb` | two-always Moore pattern (FF state + comb output), FSM-gated SRAM write/read |
| `sv/mealy-fsm` | Mealy FSM | 📝 | — | `sv/fsm` | Mealy output depends on current input, single-always style |

> Moore-only leaves students unable to recognise the more common Mealy
> pattern in real codebases.

### Chapter: Covergroups
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `sv/covergroup-basics` | covergroup and coverpoint | ✅ | 24/27 ⚠️2,9 | `sv/parameters` | `covergroup`, `coverpoint`, `sample()`, `$get_coverage()`, functional coverage concept |
| `sv/coverpoint-bins` | Bins and ignore_bins | ✅ | 23/27 ⚠️7,8,9 | `sv/covergroup-basics` | explicit `bins`, range bins, `ignore_bins`, auto bins |
| `sv/cross-coverage` | Cross coverage | ✅ | 25/27 ⚠️9 | `sv/coverpoint-bins` | `cross`, 2D coverage matrix, identifying uncovered `{addr, we}` pairs |

### Chapter: Testbench Essentials
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `sv/classes` | Classes and Objects | ✅ | 27/27 | `sv/tasks-functions` | `class`/`endclass`, fields, `function new()`, `this.`, handle semantics, `convert2string` |
| `sv/queues-arrays` | Dynamic Arrays and Queues | ✅ | 27/27 | `sv/classes` | `type name[]`, `new[n]`, `.size()`, `type name[$]`, `push_back`, `pop_front` |
| `sv/fork-join` | Concurrent Processes: fork...join | ✅ | 27/27 | `sv/tasks-functions` | `fork...join`, `fork...join_any`, `fork...join_none`, `automatic` tasks |
| `sv/randomization` | Constrained Randomization | ✅ | 27/27 | `sv/classes` | `rand`, `randomize()`, `constraint`, `inside`, inline `with {}`, `constraint_mode(0)` |

---

## Part 2 — SystemVerilog Assertions

### Chapter: Runtime Assertions
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `sva/concurrent-sim` | Concurrent Assertions in Simulation | ✅ | 26/27 ⚠️2 | `sv/always-ff`, `sv/parameters` | `assert property`, `@(posedge clk)`, concurrent assertion semantics in simulation |
| `sva/vacuous-pass` | Vacuous Pass | ✅ | 24/27 ⚠️4,8,9 | `sva/concurrent-sim` | vacuous satisfaction, antecedent never fires, silent pass hazard |
| `sva/isunknown` | $isunknown — Detecting X and Z | ✅ | 25/27 ⚠️5,7 | `sva/concurrent-sim` | `$isunknown()`, X/Z detection, X-optimism hazard |

### Chapter: Your First Formal Assertion
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `sva/immediate-assert` | Immediate Assertions | ✅ | 25/27 ⚠️5 | `sv/always-comb`, `sv/always-ff` | `assert` (immediate), deferred (`#0`/final), procedural assertion context |
| `sva/sequence-basics` | Sequences and Properties | ✅ | 24/27 ⚠️5,9 | `sva/concurrent-sim` | `sequence` keyword, `property` keyword, named reuse |

### Chapter: Implication & BMC
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `sva/implication` | Implication: \|->, \|=> | ✅ | 23/27 ⚠️5,8,9 | `sva/sequence-basics` | `\|->` (overlapping), `\|=>` (non-overlapping), antecedent/consequent |
| `sva/formal-intro` | Bounded Model Checking | ✅ | 22/27 ⚠️2,4,5,9 | `sva/implication` | BMC, `circt-bmc`, exhaustive proof vs simulation, bounded depth |

### Chapter: Core Sequences
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `sva/clock-delay` | Clock Delay ##m and ##[m:n] | ✅ | 23/27 ⚠️2,5,9 | `sva/sequence-basics` | `##m`, `##[m:n]`, clock-cycle delay in sequences |
| `sva/rose-fell` | $rose and $fell | ✅ | 24/27 ⚠️2,5 | `sva/clock-delay` | `$rose()`, `$fell()`, edge detection within sequences |
| `sva/req-ack` | Request / Acknowledge | ✅ | 23/27 ⚠️2,5,8 | `sva/implication`, `sva/clock-delay` | handshake protocol assertion, delay-bounded acknowledgement |

### Chapter: Repetition Operators
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `sva/consecutive-rep` | Consecutive Repetition [*m] | ✅ | 24/27 ⚠️2,5 | `sva/clock-delay` | `[*m]`, `[*m:n]`, consecutive cycle repetition |
| `sva/nonconsec-rep` | Goto Repetition [->m] | ✅ | 24/27 ⚠️2,5 | `sva/consecutive-rep` | `[->m]`, goto (non-consecutive) repetition |
| `sva/nonconsec-eq` | Non-Consecutive Equal Repetition [=m] | ✅ | 22/27 ⚠️2,5,7,8 | `sva/nonconsec-rep` | `[=m]`, equality across non-consecutive occurrences |

### Chapter: Sequence Operators
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `sva/throughout` | throughout — Stability During a Sequence | ✅ | 23/27 ⚠️4,5,9 | `sva/clock-delay` | `throughout`, signal stability constraint over sequence duration |
| `sva/sequence-ops` | Sequence Composition: intersect, within, and, or | ✅ | 24/27 ⚠️4,5 | `sva/throughout` | `intersect`, `within`, `and`, `or` — sequence algebra |
| `sva/seq-args` | Sequence Formal Arguments | ✅ | 25/27 ⚠️5 | `sva/sequence-ops` | typed formal arguments in named sequences, reusable parameterised patterns |

### Chapter: Sampled Value Functions
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `sva/stable-past` | $stable and $past | ✅ | 22/27 ⚠️3,4,5,9 | `sva/concurrent-sim` | `$stable()`, `$past(n)`, sampled-value semantics |
| `sva/changed` | $changed and $sampled | ✅ | 22/27 ⚠️3,4,5,9 | `sva/stable-past` | `$changed()`, `$sampled()` |

### Chapter: Protocols & Coverage
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `sva/disable-iff` | disable iff — Reset Handling | ✅ | 22/27 ⚠️2,4,5,9 | `sva/implication` | `disable iff`, async reset gating of properties |
| `sva/abort` | Aborting Properties: reject_on and accept_on | ✅ | 23/27 ⚠️4,5,9 | `sva/disable-iff` | `reject_on`, `accept_on`, mid-sequence abort |
| `sva/cover-property` | cover property | ✅ | 23/27 ⚠️4,5,9 | `sva/sequence-basics` | `cover property`, reachability vs correctness, cover vs assert intent |

### Chapter: Advanced Properties
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `sva/local-vars` | Local Variables in Sequences | ✅ | 24/27 ⚠️5,9 | `sva/clock-delay` | `local var`, data capture across sequence steps |
| `sva/onehot` | $onehot, $onehot0, $countones | ✅ | 24/27 ⚠️5,9 | `sva/concurrent-sim` | `$onehot()`, `$onehot0()`, `$countones()` — bit-count system functions |
| `sva/triggered` | .triggered — Sequence Endpoint Detection | ✅ | 23/27 ⚠️5,7,9 | `sva/sequence-basics` | `.triggered`, detecting sequence completion at a named endpoint |
| `sva/checker` | The checker Construct | ✅ | 23/27 ⚠️5,6,7 | `sva/implication`, `sva/disable-iff` | `checker` construct, encapsulating assertions into reusable modules |
| `sva/recursive` | Recursive Properties | ✅ | 23/27 ⚠️5,6,7 | `sva/implication` | recursive `property`, inductive-style reasoning |
| `sva/bind` | bind — Non-Invasive Assertion Attachment | 📝 | — | `sva/checker` | `bind` statement, attaching checkers without modifying RTL source |
| `sva/let` | let Declarations | 💡 | — | `sva/sequence-basics` | `let` declaration, scoped parameterisable macro alternative to `` `define `` |

**`sva/bind`** (Mehta §6.12-6.14, p. 79-82)
> `bind target_module checker_or_module inst_name (port_connections);`
> attaches assertion logic to any module without touching its source.
> Exercise: bind a property checker to the existing `counter` module
> from Part 1.

**`sva/let`** (Mehta §21, p. 325-333)
> `let name [(ports)] = expression;` — scoped, parameterisable macro
> alternative to `` `define `` without text-substitution pitfalls.

### Chapter: Formal Verification
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `sva/formal-assume` | assume property | ✅ | 25/27 ⚠️4,9 | `sva/formal-intro` | `assume property`, constraining formal input space |
| `sva/always-eventually` | always and s_eventually | ✅ | 22/27 ⚠️4,5,7,9 | `sva/formal-assume` | `always`/`s_eventually`, liveness vs safety properties |
| `sva/until` | until and s_until | ✅ | 23/27 ⚠️4,5,9 | `sva/always-eventually` | `until`, `s_until`, weak/strong until |
| `sva/lec` | Logical Equivalence Checking | ✅ | 24/27 ⚠️5,6 | `sva/formal-intro` | LEC, two-module equivalence, miter circuit concept |
| `sva/followed-by` | Followed-By: #-# and #=# | 📝 | — | `sva/implication`, `sva/formal-intro` | `#-#`, `#=#`, non-vacuous implication operators |

**`sva/followed-by`** (Mehta §20.8, p. 295-296)
> `seq #-# prop` and `seq #=# prop` fail if the antecedent doesn't
> match — unlike `|->` / `|=>` which pass vacuously.
> Exercise: compare the two forms on a burst read; observe the `#=#`
> failure when the burst never occurs vs the `|=>` silent pass.
> *Requires circt-bmc for the formal comparison half.*

---

## Part 3 — Universal Verification Methodology

### Chapter: UVM Foundations
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `uvm/reporting` | The First UVM Test | ✅ | 24/27 ⚠️4,9 | `sv/modules-and-ports`, `sv/interfaces` | `uvm_component`, `uvm_test`, `` `uvm_info/warning/error ``, severity levels, `build_phase`/`run_phase`, objections |
| `uvm/seq-item` | Sequence Items | ✅ | 24/27 ⚠️4,5,9 | `uvm/reporting`, `sv/packed-structs` | `uvm_sequence_item`, `` `uvm_object_utils ``, `rand` fields, constraints, `convert2string` |

### Chapter: Stimulus
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `uvm/sequence` | Sequences | ✅ | 25/27 ⚠️9 | `uvm/seq-item` | `uvm_sequence`, `body()`, `start_item`/`randomize`/`finish_item` loop |
| `uvm/driver` | The Driver | ✅ | 24/27 ⚠️2,8,9 | `uvm/sequence`, `sv/interfaces`, `sv/always-ff` | `uvm_driver`, `get_next_item`/`item_done`, virtual interface driving, 1-cycle latency capture |
| `uvm/constrained-random` | Constrained-Random Scenarios | ✅ | 25/27 ⚠️5,9 | `uvm/seq-item` | `dist`, inline `randomize() with {}`, `constraint_mode()` |

### Chapter: Checking
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `uvm/monitor` | Monitor and Scoreboard | ✅ | 25/27 ⚠️5,9 | `uvm/driver`, `uvm/seq-item` | `uvm_monitor`, `uvm_analysis_port`, `write()`, `uvm_scoreboard`, shadow memory |
| `uvm/env` | Environment and Test | ✅ | 23/27 ⚠️5,8,9 | `uvm/monitor` | `uvm_env`, `uvm_agent`, analysis port → scoreboard wiring |

### Chapter: Functional Coverage
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `uvm/covergroup` | Functional Coverage | ✅ | 25/27 ⚠️5,9 | `uvm/monitor`, `sv/covergroup-basics` | functional coverage in UVM, `uvm_subscriber`, sampling transactions |
| `uvm/cross-coverage` | Cross Coverage | ✅ | 24/27 ⚠️5,9 | `uvm/covergroup`, `sv/cross-coverage` | cross in UVM context, `addr × we` 2D coverage |
| `uvm/coverage-driven` | Coverage-Driven Verification | ✅ | 25/27 ⚠️6,9 | `uvm/cross-coverage` | coverage-driven loop, `get_coverage()` exit condition |

### Chapter: Advanced UVM
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `uvm/factory-override` | Factory Overrides | ✅ | 25/27 ⚠️5,9 | `uvm/seq-item` | `uvm_factory`, `type_id::set_type_override`, corner-case testing via type substitution |
| `uvm/virtual-seq` | Virtual Sequences | 💡 | — | `uvm/env` | `uvm_virtual_sequencer`, coordinating stimulus across multiple agents |
| `uvm/ral` | Register Abstraction Layer (RAL) | 💡 | — | `uvm/driver` | `uvm_reg_block`, `uvm_reg`, frontdoor/backdoor register access |

---

## Part 4 — cocotb

### Chapter: cocotb Basics
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `cocotb/first-test` | Your First cocotb Test | ✅ | 22/27 ⚠️2,4,9 | `sv/always-ff` (Python basics assumed) | `@cocotb.test()`, `dut.signal.value`, `await Timer()`, VCD generation |
| `cocotb/clock-and-timing` | Clock and Timing | ✅ | 24/27 ⚠️4,9 | `cocotb/first-test` | `Clock()`, `start_soon()`, `await ClockCycles()`, sim time queries |

### Chapter: Triggers & Clocks
| Slug | Title | Status | Score | Prereqs | Teaches |
|---|---|---|---|---|---|
| `cocotb/edge-triggers` | Edge Triggers | ✅ | 24/27 ⚠️4,9 | `cocotb/clock-and-timing` | `RisingEdge`, `FallingEdge`, awaiting edge trigger objects |
| `cocotb/clockcycles-patterns` | Clock Cycles & Patterns | ✅ | 25/27 ⚠️9 | `cocotb/edge-triggers` | multi-cycle sequences, burst patterns, structured test routines |

---

## Diagram opportunities (from MIT 6.111 research)

Reference PDFs in `reference/mit-6111/` (CC BY-NC-SA 4.0, Chandrakasan, Spring 2006).
Listed by lesson, in priority order:

| Lesson | Diagram to add | Source |
|--------|---------------|--------|
| `sv/always-ff` | D latch vs. D register schematics — "level-sensitive vs. edge-triggered" side-by-side | L5 p2 |
| `sv/always-ff` | Pipeline timing: one stage with Tcq, Tlogic, Tsu labeled; formula T > Tcq+Tlogic+Tsu | L5 p3-5 |
| `sv/always-ff` | Synchronous vs. async reset waveform comparison | L5 |
| `sv/fsm` | ✅ Moore block diagram SVG added (Comb. Logic ↔ State Reg, inputs/outputs) | L6 p6 |
| `sv/fsm` | Level-to-pulse edge-detector as a 2-state worked example before the SRAM controller | L6 p7 |
| `sv/welcome` | HDL design flow: Problem → Behavioral → HDL → Synthesis → Implementation | L1 p12 |
| `sv/data-types` | Two's complement circular number line (overflow wraparound visualised) | L8-9 p3 |
| `sv/modules-and-ports` | Common logic gates table: NAND/AND/NOR/OR with symbol + truth table + Boolean expression | L2 p9 |
| `sv/always-comb` | Gate-level mux diagram (AND/OR/NOT tree) matching the case statement | L3 |
| `sv/interfaces` | Two module boxes wired through a named interface bundle | — |

---

## Remaining gaps / priority order

### SV Basics
1. `sv/mealy-fsm` — completes the FSM chapter
2. `sv/shift-reg` — completes Sequential Logic
3. `sv/generate` — common RTL pattern
4. `sv/typedef` + `sv/arrays-static` — complete the Data Types chapter
5. `sv/assign-operators` — arithmetic foundation

### SVA
6. `sva/followed-by` (`#-#` / `#=#`) — no-vacuous-pass operators; pairs with `sva/formal-assume`
7. `sva/bind` — non-invasive attachment; reuses Part 1 `counter` module
8. `sva/let` — optional polish

### UVM
9. `uvm/virtual-seq` — orchestrates multiple agents
10. `uvm/ral` — register model; needed for IP-level verification

### TB-focused SV (potential new Part 5)
> OOP fundamentals, randomization techniques, dynamic arrays/queues,
> fork/join concurrency — bridging SV basics and UVM.
> Ref: `OOP/`, `Randomization/`, `Arrays/`, `ThreadsAndInterProcessCommunication/`
