---
number: 0817
target: /qa
filed_by: /stdlib
filed_at: 2026-07-21
sprint_filed: 115
refers_to: stdlib/collections/vec.cl:147-155 (vec-flatten, the 0488 NOTE);
  repl/spec.md §1.1 (Universal Output Format), §1.3;
  design/int/ (per-turn codegen batch derivation)
status: open
---

# One failed codegen batch is STICKY — every later REPL turn re-reports the identical error, including `(+ 1 2)`

## Issue

After a single turn fails at codegen, the REPL session is unusable: every
subsequent turn — including turns that mention nothing related, and including a
bare literal — re-emits the **byte-identical** error from the first failure, at
the first failure's span.

Probed at HEAD (2026-07-21, `target/release/cranelisp`, **pristine dir**: fresh
directory, no persisted `user.cl`, no `.cranelisp-cache`,
`CRANELISP_LIB=/home/alilee/cranelisp/stdlib`):

```
(import [collections.vec [vec-flatten]])
(vec-flatten [[1 2] [3 4]])
⇒ Error: codegen error at 5843..5853: codegen failed for /: codegen error at
   5843..5853: generic value reference 'vec-concat' reached codegen without a
   mono instance
(+ 1 2)
⇒ Error: codegen error at 5843..5853: … 'vec-concat' … (identical)
"still alive"
⇒ Error: codegen error at 5843..5853: … 'vec-concat' … (identical)
```

Three faces:

1. **Stickiness.** The failed definition stays in the codegen batch and is
   retried on every later turn, so one bad turn ends the session. Nothing the
   user types afterwards can recover it.
2. **A bare literal cannot fail codegen.** `"still alive"` needs no code
   generated at all; reporting a codegen error for it is self-evidently wrong,
   and it is the cheapest possible detector for this class.
3. **`codegen failed for /`** — the mangled owner is reported as `/`, the
   division operator, in an error about `vec-concat`. Whatever names the failing
   unit is picking up the wrong symbol, which is a second, independent
   wrong-message bug in the same line.

The span `5843..5853` is inside `stdlib/collections/vec.cl`, i.e. a **library**
offset, presented to the user with no file name — a user who typed `(+ 1 2)` is
shown a bare offset into a file they never opened.

## Relationship to 0488

The underlying trigger is the long-standing 0488 class (a same-module generic
passed as a value to `vec-reduce` loses its mono instance) — `vec-flatten` is the
stdlib function that carries it, and the `NOTE(0488)` at `vec.cl:147` documents
it as still live. **That part is confirmed unchanged this sprint and is not what
this FIXME asks for.** The composed use the same NOTE guards is healthy:
`(count (vec-concat [1 2] [3 4 5])) ⇒ 5` and `(get (vec-concat [1 2] [3 4 5]) 3)
⇒ 4` both work in a pristine dir.

What is new here is the **blast radius**: 0488's own record describes a failing
call, not a session that never recovers. The stickiness is separable from 0488's
root cause and is worth fixing on its own — it will outlive that one defect,
because *any* future codegen failure inherits it.

## Request

1. `/qa` attributes and routes (candidate seam: the per-turn codegen batch
   retains failed entries instead of dropping/quarantining them).
2. `/testing`: a repro that (a) triggers any codegen failure, then (b) asserts a
   subsequent independent turn succeeds. Face 2 (`"still alive"` after a failure)
   is the tightest assertion and does not depend on 0488 surviving — it stays
   valid as a regression guard after 0488 is fixed, which a `vec-flatten`-shaped
   test would not.
3. Separately, the `codegen failed for /` mis-naming deserves its own cell.

## Context

Found by `/stdlib` during the S115 Phase-6a assessment while re-probing the
standing 0488 workaround NOTEs in `collections/vec.cl` to see whether this
sprint's RC/codegen wave had retired them. It had not — but the sweep surfaced
this larger, defect-independent behaviour instead.
