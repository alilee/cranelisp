---
number: 0926
target: /qa
filed_by: /design (typecheck)
filed_at: 2026-07-26
sprint_filed: 119
refers_to: design/typecheck/non-concrete-producer-obligations.md §4.3, §6.4;
  design/arch/fixmes/0924-*.md, 0867-*.md;
  tests/plan/s119-test-plan.md (the G1 corpus gate + its extension clause after
  rider 1);
  design/backend/non-concrete-release-contract.md §2.4 (the unguarded four-line
  accessor repro)
status: open
---

# The 0867 corpus extension needs a named shape, and the cheapest guard for the whole accessor family is a unit-tier gate cell nobody has planned

## Issue

`/qa`'s S119 plan carries a corpus **extension clause** after rider 1 because 0867
widens family 1's surface. `/design`(typecheck) has now ruled that disposition
(`non-concrete-producer-obligations.md` §2, §4) and the ruling changes what the
extension should assert and when it can be authored. Three cells, one of which is a
genuine coverage gap.

## 1. The extension clause's shape — a **sum-arm** accessor, authored WITH 0867

0867's widening mints accessors from every constructor arm, and four of the five
stdlib types it newly covers are polymorphic. The family it adds is therefore a
*sum-type arm* accessor over a polymorphic type — a shape that **does not compile
today** (nothing mints `v`), so the cell cannot be authored before 0867's
change-set. Proposed:

```lisp
(import [primitives [IO Pure]])
(deftype (Mb a) Nn (Jj [:a v]))
(defn get [m] (v m))
(defn main [] (Pure (get (Jj 1024))))
```

A/B on the payload, asserting the exit **status**: `1023` exits 255, `1024` must not
SIGSEGV. It is the direct sibling of the four-line product repro
(`non-concrete-release-contract.md` §2.4) that `/testing` already owes and that is
**still unguarded** — that one is the precondition for this one's legibility, exactly
as 0916's plain-`defn` control is for its trait-method subject.

RED-then-GREEN inside one change-set is the correct shape here, because 0867 is the
thing that makes the surface reachable at all.

## 2. The coverage gap — a unit-tier **gate cell**, and why it is the real fence

The ruling's safety mechanism is **P-1**: no site constructs
`UserFnState::Concrete { got_slot }` for a scheme whose type is not
`Type::is_concrete()`. Every e2e cell above tests a *consequence* of P-1 through a
program run, an exit status and a 1023/1024 payload boundary. The invariant itself is
a two-line assertion on a symbol-table entry:

- a **polymorphic** product's / sum arm's accessor entry is
  `UserFnState::Polymorphic` and `callable_got_slot()` is `None`;
- a **concrete** product's accessor entry is `Concrete { got_slot }`, unchanged;
- likewise for a residual vs concrete trait-impl method entry.

Sibling to the existing slot-gate pins in
`crates/cranelisp-typecheck/src/program/finalize/tests.rs`. No program run, no
allocator counters, no payload boundary. **This is the cheapest possible guard for
the most expensive possible defect in the class, and it is what makes rider 0867's
early landing assessable rather than hoped** — the ruling (§4.2) unblocks 0867 on P-1
alone, and this cell is the evidence P-1 holds.

It is `/dev`(typecheck)'s to author as a unit row (`non-concrete-producer-obligations.md`
§6.4), but it is filed here because it is a *coverage-process* claim: the plan's G1
gate should name it, so that "P-1 asserted in prose, instrument missing" is caught by
`tests/plan/s119-test-plan.md` §11.2's own rule.

## 3. The stdlib cross-module bare-alias cell — 0867's other regression risk

Not a memory-safety cell, and nothing currently covers it. `/stdlib`'s blast-radius
appendix on 0867 records that `head` would be minted bare by **both**
`collections.list` and `seq.lazy`, and `rest` by `seq.lazy` while `collections.list`
already exports a `defn` of that name. Neither is an ambiguity *within* one module,
so the §8.6.5 duplicate-field classification does not fire, and `stdlib_conformance`
imports each module's `[*]` separately so it structurally cannot see the contest.

One consumer module `[*]`-importing both is the cell. `/stdlib` asked for it; it
belongs in 0867's change-set.

## Ask

Place all three in `tests/plan/s119-test-plan.md`: (1) as the extension clause's
named shape, gated on 0867's change-set; (2) as a G1-named unit instrument, authored
in the P-1 change-set; (3) as 0867's own regression cell.
