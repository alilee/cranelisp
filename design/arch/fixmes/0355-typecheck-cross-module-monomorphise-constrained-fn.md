---
number: 0355
target: /typecheck
filed_by: /dev
filed_at: 2026-06-14
sprint_filed: 82
refers_to: crates/cranelisp-typecheck/src/program.rs §pass4_monomorphise (~:2103) + §constrained-fn detection (~:867/:1027), crates/cranelisp-typecheck/src/traits.rs §monomorphise_call/recheck_body_for_mono/get_constrained_fn (:1259/:1493/:1581), tests/spec_07_traits.rs::cross_module_stacked_trait_bound_call_runs_to_clean_exit, design/arch/fixmes/0354 (the SIGSEGV defect — RESOLVED + closed)
status: open
---

# Cross-module monomorphisation of constrained (trait-bound) functions

## Issue

A constrained (trait-bound) function defined in an imported module and called
from another module is currently **cleanly rejected** — the call cannot run,
because no cross-module monomorphisation variant is ever produced. This is the
*feature* half of the now-resolved 0354 SIGSEGV defect.

The shape (from 0354's repro):

`helper.cl`:
```clojure
(import [compare.eq [Eq =]])
(import [text.display [Display show]])
(defn cmp [:Eq :Display a :Eq :Display b] :String (str-concat (show a) (show b)))
```

Entry module:
```clojure
(import [helper [cmp]])
(defn main [] (Pure (str-len (cmp 1 1))))   ; cmp 1 1 = "11"; str-len = 2 ⇒ should exit 2
```

Same-module define-and-call works (the mono variant `cmp$Int+Int` is created
and compiled). Cross-module, `cmp` is an `ModuleEntry::Import` in the entry
cluster, so:
- `check_program`'s constrained-fn detection inspects only the current
  cluster's own defns + the current module's own `Def` entries — it never sees
  the imported `cmp` (`constrained_fn_names={}` for the entry module).
- `pass4_monomorphise` therefore collects no call site → `cmp$Int+Int` is never
  created → `derive_codegen_batch` correctly skips the un-compilable constrained
  template → the call has no populated callable slot.

Before 0354's fix, this lowered to a null `call_indirect` (SIGSEGV). 0354 is now
**structurally fixed**: `resolve_got_target` reads `callable_got_slot()` (which
returns `None` for a constrained template), the Pass-2 flip clears the phantom
slot via `mark_constrained_template`, and the call lowers to a **clean typed
error** instead of a crash. This FIXME tracks the remaining work to make the
call **run** (eventual exit 2).

## Proposed resolution

Cross-module monomorphisation is a typecheck mono-architecture change:

1. Make constrained-fn detection (program.rs ~:867/:1027) and/or
   `pass4_monomorphise` (~:2103) collect call sites for **imported** callees
   that chain-resolve to a constrained `Def` (follow the import chain via
   `resolve_terminal_entry_and_home` rather than `probe_module_entry_owned`).
2. `monomorphise_call` → `recheck_body_for_mono` (traits.rs:1493) MUST re-check
   the constrained fn's body **in its DEFINING module's import context** (where
   its trait-method + helper references resolve), NOT the caller's. 0354's
   isolation hit exactly this wall: re-checking `cmp`'s body in `entry`'s scope
   mis-resolves `show`/`str-concat` (`no impl of trait Display for type IO`).
3. The generated `cmp$Int+Int` mono entry + the trait-method callees it
   dispatches to (`Display.show$Int`, …) must be reachable from the caller's
   GOT — likely a `/backend` follow-on for the cross-module mono-variant
   GOT/dispatch wiring once the correctly-scoped mono entry exists.

A contrast that proves the diagnosis: an imported *plain parametric*
polymorphic fn (`(defn ident [x] x)` called as `(ident 5)`) already WORKS
cross-module — its template is not skipped by `derive_codegen_batch` (no
`constrained_fn`), so its slot is populated. Only the *constrained* case has the
missing-mono hole.

## Operational implication / Context

`stdlib/testing/assertions.cl::assert-eq` (`[:Eq :Display a :Eq :Display b]`)
lives in a module and every caller imports it, so it cannot be invoked
cross-module until this lands — `assert-eq`-based stdlib self-tests stay
deferred. The guard
`tests/spec_07_traits.rs::cross_module_stacked_trait_bound_call_runs_to_clean_exit`
currently pins the SAFE behavior (no SIGSEGV); when this feature lands it should
be upgraded to assert the program runs to exit 2.

See 0354 for the full slot-level diagnosis (now closed — the SIGSEGV is fixed;
the run-the-program feature carries here).
