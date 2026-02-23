# Curriculum Tracker

Status of every lesson and a roadmap of what still needs to be written.
Lessons are keyed by slug (matches `tutorial-data.js`). Reference material
from https://github.com/karimmahmoud22/SystemVerilog-For-Verification (KM repo)
and *SystemVerilog Assertions and Functional Coverage* by Ashok B. Mehta,
3rd ed. (Springer, 2020) — cited as **Mehta §N** throughout — are noted
where they are directly usable as a basis for a lesson.

## Runtime note: simulation vs. formal

Most SVA lessons use **circt-sim** (simulation). Lessons that hinge on
formal semantics — particularly `assume property`, `restrict property`,
`strong`/`weak`, and `s_eventually` — should additionally (or exclusively)
run through **circt-bmc** (bounded model checking). Set `waveform: 'off'`
for pure-formal lessons; the `[circt] compile started` / `running...` log
flow still works, and the lesson can explain the tool's PASS/FAIL output.

Legend: ✅ exists · 📝 planned (prioritised) · 💡 optional/stretch

---

## Part 1 — SystemVerilog Basics

### Chapter: Introduction
| Slug | Title | Status |
|---|---|---|
| `sv/welcome` | Welcome | ✅ |
| `sv/modules-and-ports` | Modules and Ports | ✅ |

### Chapter: Combinational Logic
| Slug | Title | Status |
|---|---|---|
| `sv/always-comb` | always_comb and case | ✅ |
| `sv/priority-enc` | Priority Encoder (casez) | ✅ |
| `sv/assign-operators` | Operators & Arithmetic | 📝 |

> Cover reduction operators (`|req`), ternary, signed arithmetic,
> overflow — sets up concepts used in SVA and UVM lessons.
> Ref: `TipsAndTricks/ExpressionWidth.sv`, `TipsAndTricks/Casting.sv`

### Chapter: Sequential Logic
| Slug | Title | Status |
|---|---|---|
| `sv/always-ff` | Flip-Flops with always_ff | ✅ |
| `sv/counter` | Up-Counter | ✅ |
| `sv/shift-reg` | Shift Register | 📝 |

> Introduces `[*]` bus shift and multi-bit `always_ff`; prerequisite
> for pipeline assertions in Part 2.

### Chapter: Parameterized Modules
| Slug | Title | Status |
|---|---|---|
| `sv/parameters` | Parameters and localparam | ✅ |
| `sv/generate` | generate for / if | 📝 |

> `for generate` to replicate instances; used in every real chip.
> A parameterised N-bit adder array is a natural exercise.

### Chapter: Data Types
| Slug | Title | Status |
|---|---|---|
| `sv/packed-structs` | Packed Structs and Unions | 📝 |
| `sv/typedef` | typedef and type aliases | 📝 |
| `sv/arrays-static` | Static Arrays (packed & unpacked) | 📝 |

> Structs are pervasive in RTL (AXI, APB). Packed arrays underpin
> multi-bit signals. Ref: `DataTypes/DataTypes.sv`,
> `Arrays/PackedArrays.sv`, `Arrays/Packed_UnpackedArrays.sv`

### Chapter: Interfaces
| Slug | Title | Status |
|---|---|---|
| `sv/interfaces` | Interfaces and modport | 📝 |
| `sv/clocking-blocks` | Clocking Blocks | 💡 |

> **Critical gap.** `adder_if` is used fully-formed in all UVM lessons
> without ever being taught. Must come before Part 3.
> Ref: `ConnectingTBAndDesign/AdderWithModPort.sv`,
> `ConnectingTBAndDesign/ArbiterAndTBUsingInterface/`,
> `AdvancedInterfaces/TBWithVirtualInterface.sv`

### Chapter: Procedures
| Slug | Title | Status |
|---|---|---|
| `sv/tasks-functions` | Tasks and Functions | 📝 |

> The `task automatic send(...)` pattern already appears in the
> FSM testbench without explanation. `automatic` keyword, input/output
> arguments, return values.
> Ref: `TasksAndFunctions/` (9 files covering argument directions,
> default values, named arguments, returning arrays)

### Chapter: State Machines
| Slug | Title | Status |
|---|---|---|
| `sv/enums` | typedef enum | ✅ |
| `sv/fsm` | Two-Always Moore FSM | ✅ |
| `sv/mealy-fsm` | Mealy FSM | 📝 |

> Moore-only leaves students unable to recognise the more common Mealy
> pattern in real codebases.

---

## Part 2 — SystemVerilog Assertions

### Chapter: Your First Assertion
| Slug | Title | Status |
|---|---|---|
| `sva/immediate-assert` | Immediate Assertions | ✅ |
| `sva/sequence-basics` | Sequences and Properties | ✅ |

> **Deferred immediate assertions** (Mehta §5.1-5.2): `assert #0` and
> `assert final` fire at the end of the time-step rather than instantly —
> useful for avoiding sensitivity-list false firings. Worth a blockquote
> note in the immediate-assert lesson.

### Chapter: Clock Delay & Sequences
| Slug | Title | Status |
|---|---|---|
| `sva/clock-delay` | Clock Delay ##m and ##[m:n] | ✅ |
| `sva/consecutive-rep` | Consecutive Repetition [*m] | ✅ |
| `sva/nonconsec-rep` | Goto Repetition [->m] | ✅ |
| `sva/nonconsec-eq` | Non-Consecutive Equal Repetition [=m] | 📝 |
| `sva/throughout` | throughout | 📝 |
| `sva/sequence-ops` | Sequence Composition: and, or, intersect, within | 📝 |

**`sva/nonconsec-eq`** (Mehta §8.10-8.12, p. 125-129)
> `[=m]` requires a signal to occur exactly *m* times non-consecutively,
> but the window can extend past the last occurrence — the qualifying event
> may arrive any time after the last match. Contrast with `[->m]` where the
> window ends on the last match. Exercise: after `nBurstRead`, exactly 8
> non-consecutive `RdAck` pulses then `ReadDone`.
> Key distinction table: `[*m]` consecutive · `[->m]` goto · `[=m]` equals.

**`sva/throughout`** (Mehta §8.16-8.17, p. 133-135)
> `expr throughout seq` — the boolean expression must remain true at every
> clock tick for the entire duration of `seq`. Classic use: a mode signal
> must not change while a multi-cycle burst is in progress.
> Exercise: `(!bMode) throughout data_transfer[*4]`.
> Blockquote: `throughout` is syntactic sugar for `reject_on` abort
> (introduced in `sva/abort`); knowing both forms helps when reading tools'
> error messages.

**`sva/sequence-ops`** (Mehta §8.20-8.29, p. 141-155)
> Four binary operators that compose sequences:
> - `and` — both sub-sequences must match starting at the same clock;
>   they may end at different times; the composite ends at the later one.
> - `or` — at least one sub-sequence must match.
> - `intersect` — like `and` but both must also end at the same clock.
> - `within seq1` — a weaker form: seq1 must fit entirely inside the
>   enclosing sequence window.
> Also covers `first_match(seq)` — returns the first completion of a
> sequence that has multiple possible end points (useful with `[m:n]`).
> Exercise: use `intersect` to assert that `valid[*4]` and `ready[*4]`
> hold for exactly the same 4 cycles (i.e., a valid/ready handshake
> requires both to be high simultaneously).

### Chapter: Properties & Implication
| Slug | Title | Status |
|---|---|---|
| `sva/implication` | Implication: \|->, \|=> | ✅ |
| `sva/req-ack` | Request / Acknowledge | ✅ |
| `sva/disable-iff` | disable iff — Reset Handling | ✅ |
| `sva/vacuous-pass` | Vacuous Pass and the assert/cover Pair | 📝 |
| `sva/followed-by` | Followed-By: #-# and #=# | 📝 |

**`sva/vacuous-pass`** (Mehta §17.15-17.19, p. 260-263)
> When an implication's antecedent never matches, the property **passes
> vacuously** — the pass action fires even though nothing was checked.
> This can flood logs with false PASSes. The canonical fix: remove the
> pass action from `assert` and add a companion `cover property` (which
> does not vacuously pass) to confirm the antecedent was actually
> exercised. Also introduce `$assertvacuousoff` for bulk suppression.
> Exercise: write a property that is trivially vacuous (antecedent never
> true in the testbench), observe the spurious PASS messages, then apply
> the assert+cover pair pattern.

**`sva/followed-by`** (Mehta §20.8, p. 295-296)
> `seq #-# prop` (overlapped) and `seq #=# prop` (non-overlapped) are
> like `|->` / `|=>` but with one crucial difference: if the antecedent
> sequence does NOT match, the property **fails** instead of passing
> vacuously. This makes them natural in formal verification where vacuous
> passes are undesirable.
> Exercise: write a `#=#` property for a burst read and observe it fails
> when the burst never occurs — then show the `|=>` version silently
> passes in the same scenario.
> *Requires circt-bmc for the formal comparison half.*

### Chapter: Sampled Value Functions
| Slug | Title | Status |
|---|---|---|
| `sva/rose-fell` | $rose and $fell | ✅ |
| `sva/stable-past` | $stable and $past | ✅ |
| `sva/isunknown` | $isunknown — X/Z Detection | 📝 |
| `sva/changed-sampled` | $changed and $sampled | 📝 |

**`sva/isunknown`** (Mehta §9.2, p. 165; KM: `TipsAndTricks/IsUnknownFunction.sv`)
> `$isunknown(expr)` returns true if any bit is X or Z. Use it to catch
> X-propagation from uninitialized registers or floating buses — one of
> the most common simulation-only bugs invisible in formal.
> Exercise: assert that `data` is never unknown after reset is released:
> `@(posedge clk) disable iff (!rst_n) ##1 !$isunknown(data)`.

**`sva/changed-sampled`** (Mehta §20.2-20.3, p. 287-290)
> - `$changed(sig)` — true when the sampled value changed from the
>   previous clock tick. Cleaner than `sig != $past(sig)` for toggle
>   checks, and avoids the common mistake of writing `sig ##1 !sig`
>   (which checks levels, not transitions).
> - `$sampled(expr)` — returns the preponed-region value of an expression,
>   most useful in **action blocks** to display the values that were
>   actually used during evaluation (rather than the reactive-region
>   values that may differ).
> Exercise: assert that `toggleSig` changes every cycle using
> `$changed`; then intentionally display `$sampled(data)` vs bare `data`
> in the pass action and observe the difference.

### Chapter: Coverage
| Slug | Title | Status |
|---|---|---|
| `sva/cover-property` | cover property | ✅ |
| `sva/assume-property` | assume property and restrict — Formal Verification | 📝 |

**`sva/assume-property`** (Mehta §15.1-15.3, p. 221-226)
> `assume` is the third pillar of the assert/cover/assume triad.
> In **simulation** it behaves identically to `assert` (fails if
> violated). In **formal verification** (circt-bmc) it constrains the
> state space — the tool only explores traces where the assumption holds,
> allowing you to restrict stimulus to legal protocol transactions.
> Also covers `restrict property` (ignored in simulation; formal-only
> constraint, no action block) and the `dist`/`inside` operators in
> assertion contexts (weights in `dist` are ignored; both become
> membership tests).
> *This lesson runs through circt-bmc to demonstrate formal semantics.*
> Exercise: assert a property about a counter with an unbounded input;
> observe the counterexample; then add an `assume` to bound the input and
> see the property proved.

### Chapter: Advanced Properties
| Slug | Title | Status |
|---|---|---|
| `sva/local-vars` | Local Variables in Sequences | ✅ |
| `sva/onehot` | $onehot, $onehot0, $countones | ✅ |
| `sva/bind` | bind — Non-Invasive Assertion Attachment | 📝 |
| `sva/abort` | Abort Properties: reject_on and accept_on | 📝 |
| `sva/always-eventually` | always, s_always, s_eventually | 📝 |
| `sva/recursive` | Recursive Properties | 📝 |
| `sva/triggered-matched` | .triggered and .matched | 📝 |
| `sva/checker` | The checker Construct | 📝 |
| `sva/let` | let Declarations | 💡 |

**`sva/bind`** (Mehta §6.12-6.14, p. 79-82; book LAB1 §23.1-23.3)
> `bind target_module checker_or_module inst_name (port_connections);`
> attaches assertion logic to any module without touching its source.
> Essential for asserting IP you cannot modify. The bound module sees
> all signals of the target as if it were instantiated inside it.
> Exercise: bind a property checker to the existing `counter` module from
> Part 1, asserting that `count` never overflows when `en` is low.

**`sva/abort`** (Mehta §20.16, p. 314-317)
> Four operators that preempt a property mid-evaluation:
> - `reject_on(cond) prop` — abort → **FAIL** (asynchronous)
> - `accept_on(cond) prop` — abort → **PASS** (asynchronous)
> - `sync_reject_on(cond) prop` — abort → FAIL (synchronous, sampled)
> - `sync_accept_on(cond) prop` — abort → PASS (synchronous, sampled)
> Unlike `disable iff` (which suppresses the whole assertion), these
> abort only the associated property expression and can be nested.
> `reject_on(bMode) data_transfer[*4]` is exactly equivalent to
> `(!bMode) throughout data_transfer[*4]`, making abort operators the
> building blocks that `throughout` is built on.
> Exercise: use `reject_on` to abort a burst-transfer property when an
> error signal fires mid-burst.

**`sva/always-eventually`** (Mehta §20.8-20.10, p. 295-301)
> - `always prop` — property must hold at every current and future clock.
>   Inside an implication it means "once triggered, must hold forever."
> - `s_always [n:m] prop` — strong, bounded: must hold from clock n to m.
> - `s_eventually [n:m] prop` — strong: property must occur at least once
>   within the bounded window; fails if window closes without a match.
> - `eventually [n:$] prop` — weak: non-occurrence is not a failure.
> *`s_eventually` and `strong` semantics require circt-bmc to observe the
> difference from weak forms.*
> Exercise: assert that after power-on-reset, `lock` eventually goes high
> (`s_eventually [1:100] lock`) and then stays high forever
> (`|-> always lock`).

**`sva/recursive`** (Mehta §12, p. 197-200)
> A property that instantiates itself. Must use non-overlapping `|=>`
> (not `|->`, which would loop at zero delay). Two canonical patterns:
> 1. "Signal holds forever": `ra and (1'b1 |=> rc1(ra))`
> 2. "Hold until condition": `iack or (intr and (1'b1 |=> rc1(intr, iack)))`
>    — models "intr must stay asserted until iack arrives."
> Exercise: write a recursive property that verifies `lock` stays high
> until `unlock` is asserted, using the hold-until pattern.
> *Requires circt-bmc or a long-running simulation to fully exercise.*

**`sva/triggered-matched`** (Mehta §13, p. 203-216)
> - `.triggered` — a Boolean method on a named sequence instance; true
>   when the sequence reached its endpoint at the current simulation time.
>   Usable in procedural `wait` statements as well as properties.
> - `.matched` — like `.triggered` but bridges two different clocks;
>   holds the result until the next tick of the destination clock.
> Exercise: model a read-state-machine check using chained
> `.triggered` calls; then use `.matched` to verify a cross-clock
> handshake where the request fires on `clk_a` and ack on `clk_b`.

**`sva/checker`** (Mehta §22, p. 335-352; book LAB1 §23.1-23.3)
> A `checker` is a named, encapsulated assertion block. Key advantages
> over an assertion module:
> - Can be instantiated from a **procedural block** (modules cannot).
> - Formal arguments can be **sequences, properties, or events** (module
>   ports cannot accept these types).
> - Synthesis tools skip it entirely.
> - Clock and reset are inferred from the instantiation context.
> Exercise: refactor the `grant_check` module from the first sequence
> lesson into a parameterised checker; instantiate it from both a static
> context and from inside an `always @(posedge clk)` block to show the
> difference.
> Advanced: show a checker in a package imported by multiple modules.

**`sva/let`** (Mehta §21, p. 325-333)
> `let name [(ports)] = expression;` — a scoped, parameterisable macro
> alternative to `` `define ``. Unlike `` `define ``, `let` has local scope
> (does not bleed across block boundaries) and supports named default
> parameters. Useful for factoring out recurring sub-expressions in
> assertion code without the text-substitution pitfalls of macros.
> Exercise: replace a repeated `($rose(req) && !rst_n)` antecedent
> pattern with a `let` declaration and show the scope difference versus a
> `` `define ``.

---

## Part 3 — Universal Verification Methodology

### Chapter: UVM Foundations
| Slug | Title | Status |
|---|---|---|
| `uvm/reporting` | The First UVM Test | ✅ |
| `uvm/seq-item` | Sequence Items | ✅ |

### Chapter: Stimulus
| Slug | Title | Status |
|---|---|---|
| `uvm/sequence` | Sequences | ✅ |
| `uvm/driver` | The Driver | ✅ |
| `uvm/constrained-random` | Constrained-Random Scenarios | 📝 |

> Build on the existing seq_item lesson: `randomize() with {}` inline
> overrides, weighted distributions (`dist`), `solve…before`, turning
> constraints on/off with `constraint_mode()`.
> Ref: `Randomization/RandomizeWith.sv`, `Randomization/SolveBefore1.sv`,
> `Randomization/TurnConstarintsOnOff.sv`,
> `Randomization/Distributions/`

### Chapter: Checking
| Slug | Title | Status |
|---|---|---|
| `uvm/monitor` | Monitor and Scoreboard | ✅ |
| `uvm/env` | Environment and Test | ✅ |

### Chapter: Functional Coverage *(entirely missing)*
| Slug | Title | Status |
|---|---|---|
| `uvm/covergroup` | covergroup and coverpoint | 📝 |
| `uvm/cross-coverage` | Cross Coverage | 📝 |
| `uvm/coverage-driven` | Coverage-Driven Verification | 📝 |

> **The single biggest gap in the tutorial.** Functional coverage is *why*
> UVM exists — random stimulus is useless without a measure of what has
> been exercised. Three lessons minimum:
>
> 1. `covergroup` / `coverpoint` / bins — write a covergroup for the
>    adder (cover `a` in ranges 0–63, 64–127, 128–255; same for `b`).
> 2. `cross` — cross `a_cp` × `b_cp`; understand the coverage hole.
> 3. Coverage-driven loop — run sequences until coverage hits 100 %.
>
> Ref: `Coverage/CrossCoverage.sv`, `Coverage/CrossCoverageTechniques.sv`,
> `Coverage/ConditionalCoverage.sv`, `Coverage/WeightedCoverage.sv`,
> `Coverage/CoverGroupInClass/`, `Coverage/FunctionalCoverageExample/`

### Chapter: Advanced UVM
| Slug | Title | Status |
|---|---|---|
| `uvm/factory-override` | Factory Overrides | 📝 |
| `uvm/virtual-seq` | Virtual Sequences | 💡 |
| `uvm/ral` | Register Abstraction Layer (RAL) | 💡 |

> **Factory overrides** are the most important "advanced" topic here —
> factory registration is already taught but the payoff (swap a class at
> test level without touching the sequence) is never shown.
> Ref: `AdvancedOOP/GeneratorFactoryPattern.sv`,
> `AdvancedOOP/InjectingExtendedTransaction.sv`

---

## Part 4 — SystemVerilog for Verification (TB-focused SV) *(not yet started)*

This material lives between Part 1 (RTL SV) and Part 3 (UVM) and is
largely what the reference repo covers. It could be a new Part 2, pushing
the current SVA content to Part 3 and UVM to Part 4.

### Chapter: OOP Fundamentals
| Slug | Title | Status |
|---|---|---|
| `tb/classes` | Classes and Objects | 📝 |
| `tb/inheritance` | Inheritance and Polymorphism | 📝 |
| `tb/callbacks` | Callbacks | 💡 |

> Ref: `OOP/FirstClass.sv`, `OOP/GoodGenerator.sv`,
> `AdvancedOOP/Inheritance.sv`, `AdvancedOOP/CallBacks.sv`

### Chapter: Randomization
| Slug | Title | Status |
|---|---|---|
| `tb/rand-basics` | rand, randc, and constraints | 📝 |
| `tb/rand-advanced` | Constraint Techniques | 💡 |

> Ref: `Randomization/SimpleRandomClass.sv`,
> `Randomization/ImplicationAndBidirectional.sv`

### Chapter: Dynamic Data Structures
| Slug | Title | Status |
|---|---|---|
| `tb/dyn-arrays` | Dynamic Arrays and Queues | 📝 |
| `tb/assoc-arrays` | Associative Arrays | 📝 |

> Ref: `Arrays/DynamicArrays.sv`, `Arrays/AssociativeArrays.sv`,
> `Queues/Queue1.sv`–`Queue3.sv`

### Chapter: Concurrency
| Slug | Title | Status |
|---|---|---|
| `tb/fork-join` | fork/join and fork/join_any | 📝 |
| `tb/events` | Events and Semaphores | 📝 |
| `tb/mailbox` | Mailboxes | 📝 |

> Ref: `ThreadsAndInterProcessCommunication/Threads/`,
> `ThreadsAndInterProcessCommunication/Events/`,
> `ThreadsAndInterProcessCommunication/Semaphores/`,
> `ThreadsAndInterProcessCommunication/Mailbox/`

---

## Priority Order

Based on dependencies and impact, the recommended order for new lessons:

### SVA — near-term additions (all simulation-runnable unless noted)
1. `sva/vacuous-pass` — fixes a conceptual hole already visible in the cover-property lesson; pure simulation
2. `sva/throughout` — widely used; short lesson; builds on existing `[*m]` knowledge
3. `sva/nonconsec-eq` — completes the repetition trilogy (`[*]`, `[->]`, `[=]`)
4. `sva/abort` — `reject_on`/`accept_on`; shows what `throughout` is built on
5. `sva/sequence-ops` — `and`/`or`/`intersect`/`first_match`; enables compound specs
6. `sva/isunknown` — practical X-detection; short lesson
7. `sva/changed-sampled` — `$changed` / `$sampled`; short lesson; fixes common toggle-check mistake
8. `sva/assume-property` — introduce formal context; *use circt-bmc*
9. `sva/followed-by` — `#-#` / `#=#`; no-vacuous-pass operators; pairs with `sva/assume-property`
10. `sva/triggered-matched` — `.triggered` in procedural code; `.matched` for cross-clock
11. `sva/always-eventually` — `always` / `s_eventually`; *use circt-bmc for strong/weak demo*
12. `sva/bind` — non-invasive attachment; reuses Part 1 `counter` module
13. `sva/checker` — the `checker` construct; bundles everything learned so far
14. `sva/recursive` — advanced; *circt-bmc recommended*
15. `sva/let` — optional polish

### SV Basics — blocking gaps
16. `sv/tasks-functions` — used but never taught; blocks FSM TB understanding
17. `sv/interfaces` — used but never taught; blocks all UVM lessons
18. `sv/packed-structs` + `sv/arrays-static` — essential RTL data types

### UVM — largest functional gap
19. `uvm/covergroup` + `uvm/cross-coverage` + `uvm/coverage-driven` — functional coverage
20. `uvm/factory-override` — completes the factory story begun in seq-item

### SV Basics — secondary gaps
21. `sv/generate` + `sv/mealy-fsm`

### TB-focused SV (Part 4)
22. `tb/classes` + `tb/rand-basics` — bridge SV→UVM gap
23. `tb/fork-join` + `tb/mailbox` + `tb/events` — TB concurrency model
24. Remainder (optional/stretch) as bandwidth allows
