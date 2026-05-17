---
number: 0209
target: /spec
filed_by: /dev (frontend, int)
filed_at: 2026-05-17
sprint_filed: 67
refers_to: spec/04-expressions.md §4.12.9, design/arch/decisions/0040-runtime-trace-io-trace-relocate-to-int.md, crates/cranelisp-backend/src/compiler/trace_codegen.rs:51-58
status: open
---

# §4.12.9 — reword "compile-time error" to reflect actual rejection mechanism

## Issue

§4.12.9 currently says `(trace ...)` in `--link` mode is a "compile-time error".
The architecture rejects at LINK time, not parse/typecheck/compile time:

- Backend's `compile_trace_no_swap` emits `cranelisp_collect_trace` as
  `Linkage::Import` regardless of mode (one codegen source path; Module
  as generic param).
- JIT path (REPL, `--run`): imports resolve at finalize via
  `JITBuilder::symbol()` (int_intrinsics provides trace symbols).
- Object path (`--link`): imports written to `.o`; exe-bundle force-link
  for trace deleted in 0202; system linker errors with "undefined symbol
  cranelisp_collect_trace".

## Proposed resolution

Reword §4.12.9 to align with the actual rejection mechanism:

> In `--link` standalone-binary mode, `(trace ...)` is rejected at link
> time: the trace runtime is not included in the staticlib produced for
> standalone binaries. Programs using `(trace ...)` and built with
> `--link` will fail with an unresolved-symbol error from the system
> linker. The form remains available in REPL and `--run` modes where
> the trace runtime is resolved at JIT-build time.

The link-time rejection IS the architectural enforcement — no compile-time
pre-pass is needed. Future toolchain UX work may intercept the linker
error to produce a clearer message; that is independent of the spec
clause.

## Context

User direction 2026-05-17: the entire `link_mode` pre-pass validator
(introduced FIXME 0199 → inlined at `build_trace` in commit `4191374`)
was engineering around a failure mode the architecture already produces
naturally. The subtraction refactor (this fire) removes the validator,
the inline check, the frontend mode parameter, and the 8 unit tests.
Spec wording is the remaining textual debt.
