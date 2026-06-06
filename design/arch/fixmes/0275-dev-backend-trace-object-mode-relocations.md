---
number: 0275
target: /dev (backend)
filed_by: /sprint
filed_at: 2026-06-06
sprint_filed: 76
refers_to: crates/cranelisp-backend/src/compiler/trace_codegen.rs (:602 :616-:619 :649 :838-:865), design/arch/tracing.md §3.3 §3.4 §5, design/arch/fixmes/0258-qa-trace-nested-error-linked-binary-swap-all-tests.md (NOTE-4 — now CONFIRMED), spec/04-expressions.md §4.12.9
status: open
---

# Object-mode trace emission must use relocations — baked iconst absolutes SIGBUS in linked binaries (NOTE-4 confirmed at runtime)

## Issue

**User-decided 2026-06-06: fix in-sprint (S76 Wave 3/4).** The Wave-1.5 gate
review's NOTE-4 is now confirmed by runtime probe: a `--link` binary containing
`(trace …)` (match-consumption shape, so emission succeeds) builds and links
cleanly, then **crashes with SIGBUS (exit 138)** in the trace machinery. Plain
`--link` (no trace) is healthy (exit 42).

Root cause (source-confirmed): `trace_codegen.rs` bakes compiling-process
absolute addresses as `iconst`s into the emitted code —

- `got_base` (:616, :649) — the live session's GOT base, garbage in the target
  process;
- each traced fn's `code_ptr` (:865) — read from the live GOT at codegen;
- the leaked `slots_ptr` / `wrappers_buf` (:602, :618) and per-wrapper name
  strings (:849) — compiling-process heap.

The traced SET is correct (discovery off the live session is fine — the set is
static at link time); every ADDRESS is wrong for the target process.

## Proposed resolution

Use the relocation pattern the descriptor blob in the SAME file already gets
right (`declare_anonymous_data` + `declare_data_in_func` + `global_value`,
:810-:814 — mode-agnostic by construction):

1. `got_base` → reference the module's GOT **data symbol**
   (`cranelisp_types::got_data_symbol_name`) via `global_value`.
2. Traced-fn code addresses → `func_addr` against declared func refs
   (the wrapper-buffer fill at :608 already does this for wrapper ptrs —
   extend the discipline to the callee `code_ptr`s).
3. The leaked slots / name / wrappers buffers → emitted read-only (or mutable,
   for the wrapper-fill buffer) **data symbols**, referenced via relocation.
4. JIT mode keeps working identically (JITModule patches `global_value`s) —
   the uniform path, no mode fork.
5. Acceptance: FIXME 0258 item 2's linked-binary trace e2e goes green
   (it lands failing first, per repros-join-suite); REPL/`--run` trace e2e
   unchanged; `cargo nextest run -p cranelisp-backend` green; baseline-diff
   discipline if the surface changes (it should not).

NOTE: a SECOND, separate defect sits in front of accessor-consumption shapes
(`can't resolve symbol nanos` + worker park — FIXME 0276); do not conflate.
The match-consumption repro isolates THIS defect.

## Operational implication / Context

Probe record (2026-06-06, /sprint): `/tmp` 3-line repro — `(defn main []
(match (trace (work 41)) [(TraceCall n p r c ns) ns]))` + `--link` → SIGBUS.
The repro joins the suite via 0258 item 2. §4.12.9's all-modes promise stays;
this fix is what makes it true.
