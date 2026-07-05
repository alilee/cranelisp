---
number: 0524
target: /typecheck
filed_by: /dev
filed_at: 2026-07-05
sprint_filed: 102
refers_to: design/typecheck/ownership-inference.md §3.3 (Lambda escape) / §4.2 (result-mode escape edges), design/arch/ownership-inference.md §R6 (suspension/escape edges), design/backend/ownership-codegen.md §4 (B3.4 AS-BUILT blocker)
status: open
---

# Escape fact unsound for lambda-returned / HOF-returned constructors (0523 sibling) — blocks B3.4 activation

## Issue

FIXME 0523 (`be6cff4`/`d0c7684`) cured the escape gap for values **captured** by
an escaping closure (capture-is-an-escape-edge, spine R6). The B3.4-ACTIVATION
attempt (Wave 11, 2026-07-05) — flipping `STACK_ALLOC_ESCAPE_FACT_SOUND` to
`true` in `crates/cranelisp-backend/src/compiler/fn_compiler.rs` — verified that
fix held (both 0523 killer shapes classify `escapes = Some(true)`, stay heap, run
correct under `MALLOC_PERTURB_`), and confirmed the win (a genuinely-NoEscape
scalar ADT stack-allocates) plus every adversarial stay-heap shape (constructor
RETURNED from a NAMED `defn`, heap-typed-field ADT, TCO-loop local, extern/VecLit)
and the full 13-entry golden corpus (ON==OFF, byte-identical-OFF).

**But the full test suite surfaced a SECOND, distinct escape-soundness gap** — a
0523 sibling. A constructor that is the **return value of a lambda** (`(fn [y]
(Some y))`), or that **flows out through a higher-order call**
(`(apply-it (fn [y] (Some y)) 7)`), is classified `escapes = Some(false)`, so
B3.4 stack-allocates it; it then dangles once the lambda/callee frame pops — a
hard UAF that manifests as `runtime panic: match failed`.

Three existing tests pass with the flag OFF and FAIL under activation:

- `tests/regression.rs::constructor_wrapped_in_lambda_applied_indirectly_works`
  — `(match (apply-it (fn [y] (Some y)) 7) [(Some v) (Pure v) None (Pure 2)])`
- `tests/spec_03_types.rs::polymorphic_higher_order_returning_adt`
  — `(match (apply-fn (fn [x] (Some x)) 42) [(Some x) x None 0])`
- `tests/spec_06_pattern_matching.rs::nested_match_in_arm_body`
  — Option/Some construction consumed by a matching function.

**Key contrast (localizes the gap):** a monomorphic constructor RETURNED from a
NAMED `defn` (`(defn mk [:Int n] (Rect n n))`) is correctly `Some(true)` and
stays heap — verified in the adversarial re-confirm. Only the **lambda /
HOF-returned** constructor path is unsound. In `CRANELISP_OWNERSHIP_TRACE` the
anonymous lambda `(fn [y] (Some y))` does **not** appear in the cluster
summaries at all, so its body-return `(Some y)` node never receives the escape
edge its named-`defn` sibling gets from result-mode classification.

The backend CANNOT gate around this: the escape happens across a lambda/closure
boundary (the constructor is the lambda's return, reached only when the closure
is called through a HOF), and re-deriving that escape backend-side would require
interprocedural/lambda-return escape reasoning — outside the narrowness budget
(`design/backend/ownership-codegen.md` §4.3). The fix must land in the analysis:
a constructor (or any fresh allocation) that is the return value of a `Lambda`
body must be classified as an escape edge for that lambda's frame, exactly as a
named `defn`'s returned allocation is (result-mode `Fresh`/escape handling).
Whether the lambda is currently analysed as its own callable (with a
`ModeSummary` + result mode) or is skipped entirely is the first thing to
establish — the trace suggests it is skipped, which would explain why the escape
edge is never emitted.

## Proposed resolution

`/typecheck` extends the escape analysis so a `Lambda`'s body-return allocation
is an escape edge (the lambda frame is popped when the closure returns, and the
returned value outlives it). If lambdas are not currently in the ownership
cluster, they need a result-mode/escape pass over their bodies analogous to named
`defn`s — the returned constructor node gets `escapes = Some(true)`. Preserve the
0523 over-widen pins (a non-escaping local lambda whose result stays in-frame must
keep the B3.4 win) and the NAMED-`defn`-returned-constructor `Some(true)` result.
Failing-first, strategy-matrix cells (lambda-returned ctor direct + via-HOF +
nested + polymorphic-`Some` + the negative in-frame-only lambda), mirroring the
0520/0523 arcs.

Consider the comprehensive pass5-classifier soundness audit the a162490 note
flagged (result-mode / escape / confinement / param-modes) — this is now the
THIRD classifier gap (0520 result-mode, 0523 capture, 0524 lambda/HOF return)
surfaced by a first-hard-consumer after the 8b review declared the analysis
sound.

## Operational implication / Context

B3.4 stack allocation stays HELD OFF (`STACK_ALLOC_ESCAPE_FACT_SOUND = false`,
byte-identical to pre-B3.4) until this lands. The mechanism is complete and
unit-tested; the resolving change-set flips one flag and re-runs the
killer/win/adversarial + full-corpus behavioral suite
(`design/backend/ownership-codegen.md` §4 AS-BUILT) before landing. `/qa` owes the
narrow UAF repro (the failing-not-ignored record) per the defect-handoff protocol;
the three tests above are the current observable signature.
