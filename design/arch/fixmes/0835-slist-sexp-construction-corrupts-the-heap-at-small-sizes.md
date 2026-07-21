---
number: 0835
target: /qa
filed_by: /stdlib
filed_at: 2026-07-21
sprint_filed: 115
refers_to: src/bootstrap.rs:435-545 (synthetic `macros` module — SList/Sexp
  ADTs + `sconcat`); stdlib/derive/helpers.cl (the surface that fails);
  design/arch/fixmes/0815 (the derive-visible face of this);
  design/arch/safety-invariants.md (memory-safety invariant register)
status: open
---

# Building a ~6-cell `SList` of `Sexp` corrupts the heap — in ORDINARY code, no macro involved

## Issue

`macros/SList`/`macros/Sexp` values built by the ordinary combination of
`SCons` + `macros/sconcat` corrupt the glibc heap once the result reaches
roughly six cells. This is the ROOT of FIXME 0815 and of the entire
`derive` breakage; 0815 saw only its macro-expansion face and could not
attribute it, because in that face the corruption surfaces as a *logic*
symptom ("runtime panic: match failed") with no location.

Probed at HEAD (2026-07-21, `target/release/cranelisp`, **pristine
per-probe directory**, no persisted `user.cl`, no `.cranelisp-cache`,
`CRANELISP_LIB=/home/alilee/cranelisp/stdlib`).

## Minimal repro A — a TWO-cell list, freed on the test-runner path

The smallest cell found. Put this one `test-*` function in any stdlib module's
self-test file and run the module through the standard runner recipe:

```
(defn- slen [xs] :Int (sfold (fn [n _] (add-i64 n 1)) 0 xs))
(defn test-two-cell [] :(Option String)
  (assert-eq 2 (slen (SCons (SexpSym "a") (SCons (SexpSym "b") SNil)))))
```

```
⇒ :primitives/String "6 passed, 0 failed, 0 panicked"
   corrupted double-linked list          ← process aborts AFTER the tally
```

**Note where it dies.** Every assertion passes and the tally prints; the abort
is in glibc, on teardown. This is drop-glue/RC over a nested heap ADT
(`SCons` → `SCons` → heap `SexpSym` → heap `String`), not a logic error.

Three controls narrow it sharply:

- a **ONE**-cell list (`(SCons (SexpSym "a") SNil)`) is fine;
- the identical fold run **directly at the REPL** is fine (returns 2, no abort);
- constructing the two-cell value at the REPL without folding is fine.

So repro A specifically needs the value to be built and dropped inside a
function invoked through `discover-tests` → `run-one`. That is the same
marshaling/GOT path the S87 `collections/either` SIGBUS note blamed — a note
this sprint retired as stale because the either tests now pass. They pass
because `(Either String Int)` is one level of heap nesting; this is two.

## Minimal repro B — 6 lines, no macro, no runner, plain REPL

```
(import [macros [*]])
(import [core.syntax [sfold]])
(defn- slen [xs] (sfold (fn [n _] (+ n 1)) 0 xs))
(defn step [acc] (macros/sconcat acc (SCons (SexpSym "x") (SCons (SexpBool true) SNil))))
(slen (step (step SNil)))          ⇒ :primitives/Int 4
(slen (step (step (step SNil))))   ⇒ free(): chunks in smallbin corrupted
```

The process aborts inside glibc. A sibling probe over the same shape produced
`corrupted size vs. prev_size while consolidating` instead, so the two
allocator faces are both reachable.

**`sconcat` alone is NOT sufficient** — a hand-chained
`(sconcat (sconcat (sconcat (two) (two)) (two)) (two))` returns 4/6/8
correctly. The corrupting ingredient is the freshly-allocated `SCons`/`Sexp`
cells being consumed by `sconcat` in the same expression, i.e. an RC/ownership
question about `sconcat`'s arguments, not `sconcat`'s list-walking.

**It is layout-sensitive, not shape-deterministic.** The identical probe with
`` `true `` (quasiquote) in place of `(SexpBool true)` survives to 6 cells; with
`(SexpBool true)` it dies at 6. Two different reshapes of the real
`derive/helpers.cl` builders moved the failure between *silent process exit*,
*macro-expansion panic*, and *deterministic hang* without moving the arity
ceiling. That signature — same logical computation, different allocation
layout, different crash face — is memory corruption, not a partial `match`.

## The derive-visible face (supersedes 0815's attribution question)

With the S115 `/stdlib` conformance fixes in place, the ceiling is:

| shape | result |
|---|---|
| nullary enum, 1–2 ctors, all three macros | green |
| nullary enum, 3 ctors — `derive-Eq`, `derive-Display` | green |
| nullary enum, 3 ctors — `derive-Ord` | macro-expansion `runtime panic: match failed` |
| data ctor, 1 field, all three macros | green |
| **data ctor, 2 fields, all three macros** | **compiler process dies silently — no diagnostic, REPL exits** |

0815 asked `/qa` to attribute between "a partial `match` in
`stdlib/derive/helpers.cl`" and "the macro-expansion runtime". **Neither.** Two
independent controls rule out the stdlib helpers:

1. **The generated code is correct.** Hand-writing the exact impl each blocked
   builder emits compiles and evaluates correctly — both the 3-arm nested-match
   `Ord` and the 2-field `Eq`. Only *building* it fails.
2. **The macro layer is not required.** The repro above is ordinary top-level
   code.

0815's one useful stdlib finding was real and is FIXED: an `snth`-based index
walk in `build-later-arms` was the 2-constructor `derive-Ord` panic (`/stdlib`
owned it; removed S115, that cell is now green). Everything above it is this
defect.

## Why this outranks its symptoms

This is a **memory-safety** defect reachable from ordinary Cranelisp source
with two imports and four lines. `safety-invariants.md` §4's register exists
for exactly this class, and the S111 finding it records — memory-safety defects
found only incidentally, never structurally — repeats here: this one was found
while writing self-tests for a module that had none, three sprints after the
`derive` surface it silently disables was declared delivered.

## Blast radius already measured

This is not confined to `derive`. Writing the FIRST self-tests for
`stdlib/core/syntax.cl` — the SList substrate `derive.helpers`, `defs` and
`derive` all stand on — hit it immediately: `sreverse`, `slist`, and `sfold`'s
inductive case have **no coverage at all** in the shipped module because every
drafted case aborts the process. `core/syntax/test.cl`'s header lists the exact
ten cases withheld, so they can be restored verbatim when this closes.

## Request

1. `/testing` lands **both** repros as failing-not-ignored tests. Each needs a
   **process-abort guard**, not a value assertion — the failure is a SIGABRT
   from glibc, and a bare assertion would take the harness down with it. Repro A
   is the higher-value one: it is smaller, and its "passes then aborts on
   teardown" signature points straight at drop glue.
2. `/qa` attributes. The suspect seam is RC/ownership on `sconcat`'s arguments
   (a `cranelisp-intrinsics` C-ABI function taking two heap ADTs and returning
   a third) — specifically whether it consumes, borrows, or double-frees cells
   that the caller also holds. `ownership-inference.md` §3.1(a)'s declared-leaf
   fact table for extern primitives is the natural place for `sconcat`'s
   per-param convention to be wrong or absent.
3. Re-point FIXME 0815 at this file, or close it into this one — its 2-ctor cell
   is fixed and its 1-ctor cell was the stdlib conformance gap (also fixed).

## Context

Found by `/stdlib` during S115 Phase 6b while building `stdlib/derive/test.cl`,
the consumer self-test module `plan-stdlib.md` §26.4 has specified since S87 and
that was never built. That module now exists and is green at the arities that
run (28 tests); its header enumerates the specific cells owed the moment this
FIXME closes. `derive.cl` is one of the 12 stdlib modules the Phase-6a sweep
found carrying NO self-tests, and every defect that sweep found lives in that
set — this one included.
