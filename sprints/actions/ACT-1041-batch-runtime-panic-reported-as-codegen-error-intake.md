---
id: ACT-1041
title: Under --run an uncaught runtime panic is reported as a codegen error at 0..0 with a doubled prefix, and the three modes disagree on the panic prefix
status: open
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - spec/12-runtime.md §12.7.5
  - spec/12-runtime.md §12.7.4
  - repl/spec/10-terminal-styling.md §10.3
  - src/session_v4/lifecycle.rs::trampoline
  - src/pipeline.rs::program_outcome_to_result
  - tests/spec_12_runtime.rs
  - design/arch/fixmes/0915-codegen-diagnostic-exposes-mangled-doubled-internal-subjects.md
---

## Observation

QA found this on 2026-09-30 in the control leg of
[ACT-1040](ACT-1040-panic-sentinel-reaches-heap-consumer-intake.md), with a
copy of `target/debug/cranelisp` built after `88bbbd12` and the primitives-only
prelude (`.local/qa-s122-6b/sentinel/cases2.py`, cell B1c). The program's
`main` returns `(Pure (add-i64 1 (h [1 2] 9)))`, with
`(defn h [v i] (vec-get v i))`.

| Mode | Uncaught-panic output |
|---|---|
| `--run` | `user.cl:1:1: error: codegen error at 0..0: runtime panic: runtime panic: vec-get: index out of bounds`, exit 1 |
| `--link` | `runtime panic: vec-get: index out of bounds`, exit 1 |
| REPL | `runtime error: vec-get: index out of bounds` |
| §12.7.5 | `error: runtime panic: <message>`, in both REPL and batch |

- The `--run` line is wrong under any reading. It files a runtime panic under
  the codegen category, at the synthetic span, with the prefix doubled.
- The requirements disagree on the prefix. §12.7.5 gives
  `error: runtime panic:`; the REPL styling table (§10.3, row R8) names
  `runtime error:`, as the REPL prints.

## Attribution

- **Status: confirmed in source.** Two readers drain the one runtime-error
  slot. `src/pipeline.rs::program_outcome_to_result` strips the slot's
  `runtime panic: ` prefix and returns a trap. Its comment names the exact
  rendering this defect produces as the thing to avoid.
  `src/session_v4/lifecycle.rs::trampoline`, the `--run` driver, wraps the raw
  slot text in `CranelispError::CodegenError` at `Span::SYNTHETIC` and adds
  the prefix again.
- **Class:** `display-envelope-mirror`, two paths rendering one display
  concept. **Entered at** `trampoline`.
- **Refuted if** `--run` reaches `program_outcome_to_result` for this program.
- **Coverage gap.** `uncaught_runtime_panic_surfaces_message_and_clean_exit_run`
  asserts the message only as a substring. No cell asserts the §12.7.5 form.
- **0915 witness.** This is a public codegen error with a `0..0` span. It is a
  third witness for the falsifier of FIXME 0915's K9 carry, beside ACT-1034's
  and ACT-1036's.

## Evidence allocation

- **`spec` first:** reconcile §12.7.5 with REPL §10.3 R8, and bring the prefix
  question to the user if the answer is not settled. Until then, no cell
  asserts a prefix.
- **`test` (allocated now):** a failing, un-ignored `--run` cell in
  `tests/spec_12_runtime.rs` citing `// spec: spec/12-runtime.md §12.7.5`, with
  `class=display-envelope-mirror locus=src/session_v4/lifecycle.rs::trampoline found=S122 owner=/dev`.
  - Stderr contains the message exactly once.
  - Stderr names neither `codegen error` nor `0..0`.
  - The exit is non-zero.
  - The `--link` leg is the passing control on these three assertions.
- After `spec`'s answer, `test` adds the prefix assertion in every mode.
  **`dev`**(src) routes `trampoline` through the single slot reader and adds
  the unit row.

## Disposition

Not memory-unsafe. Fix or carry is the user's decision under METHOD §2.4. QA
retains this intake.

## Completion evidence

The `--run` cell goes RED, then GREEN, with the `--link` control unchanged. QA
annotates §12.7.5 once `spec` settles the prefix.
