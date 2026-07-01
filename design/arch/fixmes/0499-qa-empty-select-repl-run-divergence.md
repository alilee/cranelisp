---
number: 0499
target: /qa
filed_by: /repl
filed_at: 2026-07-01
sprint_filed: 98
refers_to: spec/10-io.md §10.12.8 ("Empty `select`"), spec/12-runtime.md §12.7.4 (REPL-vs-batch error behavior), tests/concurrency_v9_select.rs (empty_select_heap_typed_* cover --run only), user/guide/concurrency.md §"select — n-ary race over a Vec"
status: open
---

# Empty `(select [])` is fatal under `--run` but returns an unsound-null value in the REPL (REPL/`--run` divergence + spec violation)

## Issue

Spec §10.12.8 ("Empty `select`") ruling (a) — settled this sprint via FIXME 0487 —
requires an empty `(select [])` to be a **fatal, non-catchable** runtime error:
"process-terminating in batch, **expression-aborting in the REPL** (§12.7.4)".
Returning a synthesised value is explicitly called non-conforming ("at a heap-typed
`a` an `Int`-`0` placeholder is an unsound null pointer").

**Batch `--run` conforms.** With the passing e2e shape
(`tests/concurrency_v9_select.rs::empty_select_heap_typed_fatal_runtime_error`):

```
cranelisp --run es.cl
es.cl:1:1: error: codegen error at 0..0: runtime panic: select over empty collection
exit=1
```

**The REPL does NOT.** The same construction, typed either heap (`String`) or scalar
(`Int`), returns the synthesised unsound-null `0` instead of aborting the expression:

```
> (import [primitives [select Pure bind Int]])
> (select :(primitives/Vec (primitives/IO primitives/Int)) [])
:primitives/Int 0            ;; WRONG — spec requires expression-abort with
                             ;; "select over empty collection"
> (bind (select :(primitives/Vec (primitives/IO primitives/String)) []) (fn [s] (Pure 0)))
:primitives/Int 0            ;; WRONG — heap-typed unsound-null, silently returns
```

The REPL demonstrably runs IO through the trampoline (`(sleep 100)` parks ~100ms and
resolves `0`; `(select [(Pure 1) (Pure 2)])` resolves the winner `1`), so the
non-empty select execution path is live — but the count-zero raise
(`io.rs` `run_select_node`, per `design/int/reactor.md §9`) that fires under `--run`
is **not reached on the REPL's IO-execution path**. This is a REPL/`--run` divergence
and a direct §10.12.8 violation (unsound-null returned where a fatal abort is
required). Contradicts the Design Principle "self-documenting REPL" and the ruling the
sprint just settled.

## Proposed resolution

Narrow e2e repro (failing, un-ignored, `// spec: spec/10-io.md §10.12.8`) asserting
the REPL path: pipe `(select :(primitives/Vec (primitives/IO primitives/Int)) [])`
into the REPL and assert the output **contains** the "select over empty collection"
runtime-error message and does **not** contain a synthesised `:primitives/Int 0`
result line. Mirror the existing `--run` guard so the two modes are pinned equivalent.
Owning skill for the fix: the empty-select raise is backend-emitted runtime
(`io.rs`, per FIXME 0486/0475 mis-ownership diagnosis) — route the resolution to
`/backend` (intrinsics), since the REPL's IO driver must reach the same count-zero
guard the `--run` path reaches.

## Operational implication / Context

- Discovered during the S98 Phase-6 `/repl` concurrency-surface assessment. Everything
  else on the settled concurrency surface confirmed GREEN: `Connection` opaque-but-
  user-readable (`(match c [(Connection fd) fd])` → `7`); `race`/`select`/`timeout`/
  `sleep` self-doc + execution (fast winner ~38ms, loser cancelled; `timeout`
  deadline→`None`, work-wins→`Some`); all combinator `/info`/`/doc`/`/sig`/bare-name
  introspection coherent. This is the **sole** defect found.
- **S99 input, not S98 rework** — the sprint's `--run` guards are green and the ruling
  is settled; this is an uncovered REPL-mode divergence surfaced by the assessment.
- No hang risk in the repro (the REPL returns promptly today — it just returns the
  wrong thing).
