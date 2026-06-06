---
number: 0268
target: /int
filed_by: /sprint
filed_at: 2026-06-05
sprint_filed: 76
refers_to: design/arch/facades/int.md §"process_cluster" gap-orchestration (MacroInMem arm, "cross-module FQ half" retention note, the orchestrator-owns-macro-vs-fn-discrimination rationale), spec/08-modules.md §8.5.4, spec/09-macros.md §9.3.6, design/int/step5-lazy-discovery.md, tests/s76_macro_availability.rs::fq_macro_reference_expands_without_import
status: open
---

# Implement FQ auto-loading (spec §8.5.4 / §9.3.6) — the facade's retained "cross-module FQ half" gap orchestration

## Issue

**User-decided 2026-06-05: implement (do not defer).** Spec §8.5.4 Auto-Loading
("when a qualified name references a module that has not yet been loaded, the
implementation SHOULD attempt to load that module on demand"; REPL qualified refs
SHOULD trigger lazy loading) is unimplemented for **every symbol kind in every
mode**. S76 probes against the live binary:

- `(mac/twice 21)` (FQ macro, no import, `--run`) →
  `type error: module 'mac' referenced by 'mac/twice' is not loaded`
- `(mac/helper 41)` (FQ **function**, no import, `--run`) → same error
- same FQ function ref in the REPL → same error

§8.5.4 carries no `[Tested]` annotation — this never worked; it is not a Wave-2
regression. §9.3.6 (new S76 spec text, the locked macro decision's FQ clause) sits
on this missing foundation, and is the remaining genuinely-failing
`s76_macro_availability` capability case (`fq_macro_reference_expands_without_import`).

**The design already exists in the facade** — this is the unimplemented half of
`facades/int.md`'s gap orchestration, explicitly retained through the S76 W-Macro
lock: "The `priority_boost_jit` + `wait_for_inmem` gap remains for the
**cross-module FQ** half (lazy-load + wait on a dependency module's macro)."

## Proposed resolution

Land the facade's own contract on the live worker path:

1. An FQ reference to an unloaded module surfaces as a **gap** the orchestrator
   catches (today it is a hard typecheck error — coordinate the smallest change:
   int may pre-scan FQ heads in Pass-1/parse-time, or the resolution error is
   mapped to the gap at the int boundary; do NOT add typecheck surface).
2. Orchestrator registers + loads the module file using the **same module-file
   resolution rules as `import`** (no new search semantics), typechecks-and-compiles
   it (the existing dependency-module compile machinery; block/resume per
   `design/int/step5-lazy-discovery.md`), then retries the referencing form.
3. **Macro-vs-fn discrimination stays orchestrator-owned** (facade rationale,
   unqualified): after the module's typecheck completes, peek the entry — only a
   macro with missing clause code gets the JIT force (`priority_boost_jit` +
   `wait_for_inmem` or their as-built equivalents); functions are NOT speculatively
   JIT-pushed.
4. **Scope**: all FQ references (functions, types via FQ where legal, macros) — the
   §8.5.4 SHOULD; the macro arm is the §9.3.6 acceptance case.
5. **Failure semantics**: module file not found → the existing module-not-found
   error shape at the referencing span; a lazy-loaded module that (transitively)
   imports the referencing module violates acyclicity (§9.3.4) → the existing
   cycle rejection.
6. Acceptance: `s76_macro_availability::fq_macro_reference_expands_without_import`
   goes green; add int unit tests for the gap→load→retry mechanism; add (via /qa)
   an FQ **function** auto-load e2e + REPL case so §8.5.4 gains its first
   `[Tested]` annotations.
7. Update the stale "architecture wall" note in `src/CLAUDE.md` (the wall language
   overstates — staging/read-union is live; the residue was THIS capability +
   0262's message + 0267's fixture).

## Operational implication / Context

S76 Wave-3/4 int fire (user-decided in-sprint). Replaces the "three-pass loop
walled to S77" framing: probes showed the wall decomposes into this one capability
(+ 0262 message-only + 0267 fixture-retype). `spec_09_macros.rs::cross_module_macro_transitive_via_reexport_chain`
should be re-triaged once this lands — the gate review attributed it to the wall.
