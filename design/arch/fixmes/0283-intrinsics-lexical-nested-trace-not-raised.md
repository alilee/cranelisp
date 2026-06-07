---
number: 0283
target: /dev (intrinsics)
filed_by: /qa
filed_at: 2026-06-07
sprint_filed: 76
refers_to: tests/trace.rs::trace_nested_lexical_raises_runtime_error (FAILING), spec/04-expressions.md §4.12.5, crates/cranelisp-intrinsics/src/trace.rs (TRACE_BODY_RUNNING guard), design/arch/tracing.md §6
status: open
---

# Lexical nested trace `(trace (trace e))` does NOT raise — guard misses the no-wrapper-yet case

## Issue

§4.12.5 requires BOTH lexical and dynamic nesting to raise the nested-trace
runtime error. The dynamic case works (Wave-1.5 guard). The pure-lexical case
does NOT: no wrapper has fired before the inner `swap_got` executes, so
`TRACE_BODY_RUNNING` is still false and the inner trace is treated as a
legitimate multi-module swap — it silently returns an empty trace.

Failing test: `tests/trace.rs::trace_nested_lexical_raises_runtime_error`.

## Proposed resolution

The guard must also catch the lexical case — e.g. the swap-loop's role-acquire
distinguishes "same thread already holds the role from an OUTER trace form"
(the per-form swap sequence completed → a second full swap sequence beginning
on the same thread while the role is held = nested form) from the multi-module
swaps WITHIN one form. A per-form sequence marker or counting swap groups are
candidate mechanisms — /dev's call. Natural home: S77's 0270 panic-hygiene
change-set (same file, same thread-locals) or a narrow S76 W4 fix.

## Operational implication / Context

Found by /qa S76 W3 (0258 item 1). The failing test is the durable record.
