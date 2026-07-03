---
number: 0483
target: /qa
filed_by: /examples
filed_at: 2026-07-03
sprint_filed: 101
refers_to: tests/vec_query_value_use.rs, design/backend/ownership-codegen.md §12.7, spec/04-expressions.md §4.6.2
status: open
---

# vec-get/vec-set/vec-push as a value at TWO instantiations of one HOF → SIGBUS

## Issue

The S101 fn-as-value fix (`fn_as_value.rs::emit_wrapper_call`) flipped the
four `tests/vec_query_value_use.rs` guards green — but those guards each pass
a vec-trio primitive through a HOF at **one** monomorphic instantiation. The
Phase-6a examples replay probed one shape further and found a **new crash**
just past the pinned boundary:

**A vec NULL-slot-trio primitive (`vec-get`/`vec-set`/`vec-push`) used as a
value through the SAME polymorphic HOF at TWO different instantiations
SIGBUSes (exit 135, "Bus error", both `--run` and REPL).**

## Minimal repro (crashes, both modes)

Same op, two element types, one generic HOF — `--run`:

```
(import [primitives [*]])
(defn apply2 [f v i] (f v i))
(defn main []
  (let [a (apply2 vec-get [10 20 30] 1)
        s (apply2 vec-get ["x" "yy"] 1)]
    (Pure (add-i64 a (str-len s)))))
```

→ SIGBUS, exit 135 (want 22). REPL equivalent (piped, clean cwd) also
SIGBUSes after the two `apply2` uses:

```
(import [primitives [*]])
(defn apply2 [f v i] (f v i))
(add-i64 (apply2 vec-get [10 20 30] 1) (str-len (apply2 vec-get ["x" "yy"] 1)))
```

Second crashing shape — two DIFFERENT trio ops through one HOF, each at one
type (`vec-get` `(Vec Int, Int) → Int` + `vec-push` `(Vec Int, Int) → Vec Int`):

```
(import [primitives [*]])
(defn apply2 [f v i] (f v i))
(defn main []
  (let [a (apply2 vec-get [10 20 30] 1)
        v3 (apply2 vec-push [10 20] 99)]
    (Pure (add-i64 a (vec-len v3)))))
```

→ SIGBUS, exit 135 (want 23).

## Green controls (all verified passing on the same binary, 2026-07-03)

| Shape | Result |
|---|---|
| Each trio op via its OWN monomorphic HOF (all three ops in one program) | PASS |
| Same op (`vec-get`), same instantiation, called twice through one HOF | PASS |
| One HOF at two instantiations: `vec-get` + a USER fn | PASS |
| `vec-len` (populated-slot control) at two element types through one HOF | PASS |
| The four single-instantiation shapes pinned in `tests/vec_query_value_use.rs` | PASS |

So the trigger is precisely: **≥2 monomorphic instantiations of one generic
HOF, each receiving a vec NULL-slot-trio primitive as the fn argument** —
either the same op at two element types or two different trio ops. One
wrapper per program is fine; the crash needs two wrapper-backed
instantiations of the same HOF. The signature smells like a wrapper-name or
slot collision across monomorphisations (cf. the S96 `race` inline-bind-lambda
"incompatible with previous declaration" collision — same family of
per-instantiation naming bugs), but that is a hypothesis, not a finding.

## Proposed resolution

`/qa` authors narrow failing-not-ignored guards next to the existing family
in `tests/vec_query_value_use.rs` (the two crashing shapes above + keep the
green controls), `// spec: spec/04-expressions.md §4.6.2`, resolver
`/backend` — the same `fn_as_value.rs` seam as the S101 fix, per
`design/backend/ownership-codegen.md` §12.7.

## Operational implication / Context

Found during S101 Phase 6a while assessing whether the vec-as-value fix
unlocks a cleaner HOF sub-test for `examples/14-vecs.cl`. It does — but only
single-instantiation shapes are safe, so any 6b example addition will keep to
one instantiation per HOF until this is fixed. No shipped example currently
hits the crashing shape (full 32/32 replay green).

## /qa guard batch (S101 6b, 2026-07-03): guards LANDED — this file is now redundant as a record

3 failing-not-ignored guards + 1 two-instantiation green control in
`tests/vec_query_value_use.rs` (`vec_get_as_value_two_instantiations_of_one_hof_repl`,
`…_run_mode`, `vec_get_and_vec_push_as_values_through_one_hof_run_mode`;
control `vec_len_as_value_two_instantiations_of_one_hof_control`). RED-first
verified (SIGBUS; run-mode observed as signal termination, `code()=None`).
Ledger: `tests/plan/ledger.md` §"Sprint 101 Phase 6a/6b defect set". Per
`memory/feedback_no_fixme_with_failing_test.md` the tests are the record +
trigger; resolver /backend deletes this file with the fix.
