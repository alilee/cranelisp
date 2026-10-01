---
id: ACT-1040
title: A runtime panic in a callee returns a null sentinel that the caller dereferences, so the process dies with SIGSEGV instead of reporting the panic
status: open
priority: blocking
from: qa
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - spec/12-runtime.md §12.7.8
  - spec/12-runtime.md §12.7.2
  - spec/12-runtime.md §12.7.4
  - design/backend/backend.md §7
  - crates/cranelisp-backend/src/compiler/vec_codegen.rs::emit_vec_bounds_panic
  - crates/cranelisp-backend/src/primitives_inline.rs::emit_panic_return
  - crates/cranelisp-backend/src/compiler/match_codegen.rs
  - tests/spec_12_runtime.rs
---

## Observation

`design`(backend) found the lead and recorded it as a falsification in
`design/backend/backend.md` §7. QA reproduced it on 2026-09-30 with a copy of
`target/debug/cranelisp` built after `88bbbd12`, with the primitives-only
prelude and one fresh directory per session
(`.local/qa-s122-6b/sentinel/cases1.py`, `cases2.py`).

`h` is `(defn h [v i] (vec-get v i))`. `d` is
`(defn d [n] (if (eq-i64 (div-i64 10 n) 0) "a" "bc"))`.

| Cell | Form | Observed | Required |
|---|---|---|---|
| R1 | `(str-len (h ["a" "bc"] 9))` | REPL dies, SIGSEGV, no message | panic reported; session continues |
| R2 | `(str-len (d 0))` | REPL dies, SIGSEGV | same |
| R3 | `(let [s (h ["a" "bc"] 9)] 5)`: the sentinel is only released | REPL dies, SIGSEGV | same |
| R4 | `(str-len (g ["a" "bc"]))`, with `g` calling `h` | REPL dies, SIGSEGV | same |
| R5 | `(catch-runtime-error (fn [] (str-len (h ["a" "bc"] 9))))` | REPL dies; `--run` exits −11 | `(Err "…index out of bounds")` |
| R6 | `main` returns `(Pure (str-len (h ["a" "bc"] 9)))` | `--run` exits −11, empty stderr | non-zero exit, message on stderr |
| C1 | `(h ["a" "bc"] 9)` | panic reported; session continues | same |
| C2 | `(add-i64 1 (h [1 2] 9))` | panic reported; session continues | same |
| C3 | `(str-len (h ["a" "bc"] 1))` | 2 | same |
| C4 | `(str-len (vec-get ["a" "bc"] 9))`, with the panic in the consumer's own frame | panic reported; session continues | same |
| C5 | R5 with a scalar consumer | `--run` exits 77 (the `Err` arm) | same |

- Violations: §12.7.8 items 1, 2 and 4, §12.7.4 in both modes, and the
  `catch-runtime-error` bracket of §12.7.2.
- The fault is also present in a release binary built on 2026-09-29 at 09:31.
  It is not an S122 regression.
- `--link` was not probed: the bundle archive was absent at probe time.

## Attribution

- **Status: confirmed at the emission seam.** The CLIF of R1's top-level
  function calls `h` through its GOT slot and passes the result straight to
  `str-len`. It does not consult the panic slot. `h`'s bounds block calls
  `runtime/panic` and returns `0`.
- **Discriminator:** the panic is raised in a *callee's* frame, and the caller
  uses the result as a heap value. C1–C4 each change one of these and behave.
  R2 changes the panic source and fails the same way.
- **Entered at** the panic shape of `design/backend/backend.md` §7, which stops
  only the faulting function. No caller-side check or unwind exists. Every
  emitter shares the shape: `emit_vec_bounds_panic`, `emit_panic_return` and
  the match-failure panic.
- **Face.** The consumer dereferences or RC-adjusts address 0 plus a small
  offset. That faults deterministically on this host. No silent corruption was
  observed, but the null dereference is undefined behavior under §12.7.8
  item 4.
- **Refuted if** some caller path consults the panic slot after a call and
  these probes did not reach it.
- **Coverage gap.** Every panic cell raises in the top-level frame or returns a
  scalar. No cell consumes a heap-typed result from a panicking callee.
- **Interaction with ACT-1037.** Once `vec-set` panics, a function that returns
  the Vec from an out-of-range `vec-set` reaches this fault. ACT-1037's cells
  are unaffected: each consumes the result in the panicking frame, or receives
  an `Int`.

## Evidence allocation

- **`test` (allocated now):** failing, un-ignored cells in
  `tests/spec_12_runtime.rs` citing `// spec: spec/12-runtime.md §12.7.8`,
  with
  `class=unpropagated-panic locus=design/backend/backend.md §7 panic shape found=S122 owner=/dev`.
  - R1, R2 and R3 through the existing `bounds_panic_then_session_continues`
    predicate, or a sibling that matches the division message.
  - R5 in every mode through `catch-runtime-error`, so each mode compares a
    value (77), as the ACT-1037 dynamic-index cell does.
  - R6 in `--run` and `--link`: a non-zero exit and the panic message on
    stderr.
  - C2 and C3 as passing controls.
  - After ACT-1037's correction lands, add the `vec-set` sibling
    `(defn s [v i] (vec-set v i 9))`, then `(vec-len (s [1 2] 9))`.
    Committed as
    `callee_vec_set_bounds_panic_with_vec_consumer_is_reported`; QA observed
    it RED for the intended reason (the REPL dies with SIGSEGV) on
    2026-10-01, after the correction.
- **`design`(backend):** choose the propagation mechanism so that no frame
  consumes a sentinel. Route to `arch` if it adds an intrinsic or changes the
  panic ABI, which is the public-API user gate. `dev` adds the unit row at the
  chosen seam.

## Disposition

- The fault is memory-unsafe (a null dereference) and kills the process.
  Ordinary programs reach it whenever a helper function returning a String,
  Vec or closure panics. It also defeats `catch-runtime-error`, the only
  recovery construct.
- It returns to the user as a fix decision. QA recommends committing the RED
  in S122 now, and having `design`(backend) cost the mechanism before the user
  chooses between an S122 fix and a carry.
- `design`(backend)'s costing is
  [s122-closure §10](../../design/backend/s122-closure.md#10-act-1040--panic-propagation-proposal).
  The scalar-result faces it measured, a hang and an overwritten message, are
  [ACT-1042](ACT-1042-callee-panic-with-scalar-result-resumes-caller-intake.md).
  Option A0 closes this filing but not ACT-1042.
- QA retains this intake.

## Completion evidence

The cells go RED for the intended reason, then GREEN after the correction in
every mode, with the controls still passing. QA restores the §12.7.8 band.
