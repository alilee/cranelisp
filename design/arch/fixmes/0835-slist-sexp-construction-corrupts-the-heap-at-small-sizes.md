---
number: 0835
target: /dev (runtime pair — /design(intrinsics) ruled the contract S118 W2b;
  see design/runtime/s118-structural-embedding-ownership.md)
filed_by: /stdlib
filed_at: 2026-07-21
sprint_filed: 115
refers_to: crates/cranelisp-primitives/src/marshal.rs:160-217
  (deep_rc_inc_slist, sconcat — the confirmed asymmetry writer);
  crates/cranelisp-intrinsics/src/drop.rs:134-155 (consume_slist — the
  consume-owner contract in question); src/bootstrap.rs:435-545 (synthetic
  `macros` module — SList/Sexp ADTs + `sconcat`); stdlib/derive/helpers.cl
  (the surface that fails); design/arch/safety-invariants.md (memory-safety
  invariant register); tests/plan/s118-test-plan.md §4.5 (the attribution
  ruling of record); design/runtime/s118-structural-embedding-ownership.md
  (the W2b contract ruling — seams, invariant, unit matrix, acceptance);
  design/primitives/primitives.md §4 #13 (the invariant row)
status: open
---

> **S118 W2b /design(intrinsics) CONTRACT RULING (2026-07-26). Ruled:
> structural tail-embedding takes a HEAD-ONLY inc — candidate (a).**
> `consume_slist` is CORRECT tree-ownership drop glue and does **not** change;
> deep-consume is rejected on three independent grounds (it would ratify the
> over-inc, it would tear down genuinely shared tails — the committed control
> `control_slist_built_without_sconcat_balances_green` is the fence — and it is
> non-local). The full ruling, with the declarative invariant (RE-1/RE-2/RE-3),
> the four exact seams (all in `crates/cranelisp-primitives/src/marshal.rs`;
> `deep_rc_inc_slist` is DELETED), the unit matrix, the acceptance set, the
> abort-face detector-pointing plan and the Branch-F contingency, is
> **`design/runtime/s118-structural-embedding-ownership.md`**. Invariant row
> landed at `design/primitives/primitives.md` §4 #13.
>
> Two ruling notes worth carrying at the FIXME:
>
> 1. **Why the existing unit row missed it.** `marshal/tests.rs::
>    decision24_sconcat_rc_balanced` uses a ONE-cell `ys` with BARE-TAG
>    elements, and `over-incs = (n−1) interior nodes + h heap elements` = 0 at
>    exactly that point. The seam's only unit row sits on the blind point.
> 2. **The abort face is NOT explained by the over-inc, by reading.** Surplus
>    references are monotone in the safe direction — they can only delay a
>    free, never advance one — so RE-1 violations produce leaks, and glibc
>    smallbin/double-linked-list aborts require a write into a freed chunk or a
>    double free. A second ingredient is needed; two candidates survive reading
>    with OPPOSITE predictions (a co-present premature-free defect the leak is
>    currently *masking* — the FIXME-0810-FaceB/0782 match-owned-scrutinee seam
>    that every repro-A cell runs through `sfold` — versus the deep walk itself
>    being the wild write, which the fix removes). `/dev` takes the §4.1 D0–D3
>    detector measurements BEFORE the fix; the pre-fix state is unrecoverable
>    afterwards. A repro-A cell that stays RED after the fix is an EXPECTED
>    possible outcome and a new `/qa` attribution — never a backend re-open,
>    and never a reason to roll back a fix that is correct against RE-1 and
>    pinned by repro B.
>
> **Status stays `open`:** the ruling is design only; implementation
> (`/dev`, runtime pair) + the `/testing` prelude-face cell remain.

> **S118 /qa ATTRIBUTION RULING (2026-07-25; supersedes the request-2 open
> question below; FIXME 0877 disposed into this).** The mechanism is
> **runtime-library-owned**, not backend: `marshal::deep_rc_inc_slist`
> (called by `sconcat` for its `ys` tail-embed) adds +1 to every interior
> `SCons` node and every element — references no structural owner holds —
> while intrinsics `consume_slist` correctly implements tree-ownership drop
> glue (dec the head; descend only on last ref), so the interior +1s are
> undischargeable: a per-call leak proportional to `|ys|`. Confirmed
> empirically at HEAD `4c1aa80b` via 0877's falsification recipe (repro-B
> shape under `CRANELISP_RC_STATS=1`, fresh tempdir per session): residual
> `allocs - deallocs` grows per `sconcat` call (+3, then +4) and doubles
> when `|ys|` doubles (+3 → +6) at CONSTANT type nesting depth — falsifying
> the transitive-discharge (backend glue) hypothesis, whose residual would
> track type depth. Full evidence table: `tests/plan/s118-test-plan.md`
> §4.5.
>
> Dispositions: (1) Track-B backend slice S2 is REMOVED from the backend
> wave — order S0→S1→S3→S4→S5→S6, no waiting (arch ruling 1(d)'s "0835
> first" ordered the transitive-discharge class, which 0835 does not join).
> (2) `/testing` lands repros A + B below as failing-not-ignored cells with
> process-abort guards in S118 W1 (satisfies FIXME 0765's precondition).
> (3) `/design`(intrinsics) — the new target — rules the consume-owner
> contract first: does embedding a list as a shared tail take a HEAD-ONLY
> inc (making `deep_rc_inc_slist`'s deep walk the defect; fix in primitives
> `marshal.rs`) or does `consume_*` become deep (wrong for genuinely shared
> tails)? Then `/dev` on the runtime pair. (4) Honesty caveat: the probe
> confirms the LEAK face; the abort face (glibc corruption at ~6 cells) is
> characterized by the committed repro's reduction — if it survives the
> runtime fix, that is a NEW `/qa` attribution question, not a re-opening of
> the migrated backend seams.

> **S118 /qa SCOPE NOTE — the AMBIENT PRELUDE-LOAD FACE (2026-07-25; probe
> evidence, plan of record `tests/plan/s118-test-plan.md` §2.5).** This
> defect has a THIRD face beyond leak + abort: the program-independent
> **1143-allocation residual** every stdlib-prelude `--run` child carries
> (baseline cells `ms_p8_conj_leak` ×3, `intrinsics_m3_detection_s116`
> clean control, and a term of the exemplar residue cell). The user's
> directed lead — only macro expansion *executes* during prelude load — is
> confirmed by discriminating probes (fresh tempdir, controlled env,
> `--run --no-cache`, `CRANELISP_RC_STATS=1`, trivial `Int` child, HEAD
> debug binary):
>
> | prelude contents | residual |
> |---|---:|
> | empty | 0 |
> | macro-free subset (8 real stdlib modules + 7 test children: traits, impls, deftypes, defns) | 0 |
> | + one `defmacro` DEFINED, never invoked | 0 |
> | + ONE macro invocation in a loaded module body | +2 |
> | two invocations | +4 |
> | one invocation, larger argument sexp | +23 |
> | full stdlib | 1143 |
>
> Compiling the entire macro-free surface leaks nothing; macro DEFINITION
> leaks nothing; the residual appears with the first macro EXPANSION and is
> linear in expansion count and in marshalled-sexp size — this FIXME's own
> signature (per-call, per-|structure|, constant type depth) on the same
> Sexp↔SList marshal path. No new FIXME is filed: the prelude face is THIS
> defect's face until falsified. **Binding prediction on the W2b fix:** the
> consume-owner-contract fix collapses the ambient residual to 0; W2b
> acceptance re-runs the full-stdlib probe shape, and `/testing` lands one
> prelude-face exact-balance cell in the W2b change-set. A residual
> surviving W2b is a NEW `/qa` attribution question (and unblocks nothing:
> baseline cells #10/#19/#20/#21/#23 then have no scoped flip track —
> user scope decision required; plan §2.5 branch F).

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
