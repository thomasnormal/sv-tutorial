# pc-runner d0: commit 36b040f6190

| row | row_id | interp (UVM verdict) | compile verdict | status | triage owner | compile stage | provider-dirty | interp invocations | compiled fn calls | entry-table native | parity | replay agrees |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 0001:35objections-01timeout | pass (banner True, E0/F0) | fail rc 1 | **HELD** | rev-compile2/pc-0142 | apply-demotions | 0 | absent | absent | absent | SKIP_NONPASS | True |
| 1 | 0876:60inventory-55object_macro-281field_queue_int_set_contract | pass (banner True, no UVM counts) | fail rc 1 | **HELD** | rev-compile2/pc-0141 | no-reentry-closure-after-process-externalization | 7 | absent | absent | absent | SKIP_NONPASS | True |
| 2 | 1713:60inventory-100mem-95backdoor_read_missing_path_status | pass (banner True, no UVM counts) | fail rc 1 | **HELD** | rev-compile2/pc-0142 | apply-demotions | 0 | absent | absent | absent | SKIP_NONPASS | True |
| 3 | 2535:60inventory-8_2-08abstract_component_default_tname | pass (banner True, no UVM counts) | fail rc 1 | **HELD** | rev-compile2/pc-0141 | no-reentry-closure-after-process-externalization | 7 | absent | absent | absent | SKIP_NONPASS | True |
| 4 | 3346:60inventory-110common_phases-03bottomup_dispatches | pass (banner True, no UVM counts) | fail rc 1 | **HELD** | rev-compile2/pc-0141 | no-reentry-closure-after-process-externalization | 5 | absent | absent | absent | SKIP_NONPASS | True |

First compile diagnostic per row:

- row 0: mandatory-retain live-slot native promise 'uvm_pkg::uvm_mem_single_access_seq::body' cannot be demoted: reason 'runtime:caller_retry_required' additional-reasons 'runtime:delay'
- row 1: live-slot native obligation provider 'uvm_pkg::uvm_bottomup_phase::exec_func$vtable_abi$uvm_pkg::uvm_phase' is provider-dirty path=['uvm_pkg::uvm_bottomup_phase::exec_func$vtable_abi$uvm_pkg::uvm_phase', 'uvm_pkg::uvm_bottomup_phase::exec_func', 'uvm_pkg::uvm_phase::exec_func']
- row 2: mandatory-retain live-slot native promise 'uvm_pkg::uvm_mem_single_access_seq::body' cannot be demoted: reason 'runtime:caller_retry_required' additional-reasons 'runtime:delay'
- row 3: live-slot native obligation provider 'uvm_pkg::uvm_bottomup_phase::exec_func$vtable_abi$uvm_pkg::uvm_phase' is provider-dirty path=['uvm_pkg::uvm_bottomup_phase::exec_func$vtable_abi$uvm_pkg::uvm_phase', 'uvm_pkg::uvm_bottomup_phase::exec_func', 'uvm_pkg::uvm_phase::exec_func']
- row 4: live-slot native obligation provider 'uvm_pkg::uvm_sequence_base::is_item$vtable_abi$uvm_pkg::uvm_sequence_item' is provider-dirty path=['uvm_pkg::uvm_sequence_base::is_item$vtable_abi$uvm_pkg::uvm_sequence_item', 'uvm_pkg::uvm_sequence_base::is_item']

Inputs identical to frozen manifest: True; harness drift: none
Controls: {"ok": {"pos": true, "neg": true}, "pos_key": {"AOT interpreter invocations total": "0", "Compiled function calls": "0", "Compiled process activations": "1", "Entry-table native calls": "0", "Trampoline calls": "0", "indirect_calls_total": "0", "indirect_calls_native": "0", "native_dispatch_abi_demotions": "0", "Initializer interpreter operations": "0"}, "rc": {"pos": "0", "neg": "0"}}

