---
number: 0883
target: /arch
filed_by: /design (intrinsics)
filed_at: 2026-07-26
sprint_filed: 118
refers_to: design/arch/safety-invariants.md §4 (invariant register R1–R13);
  design/runtime/s118-structural-embedding-ownership.md §2 (RE-1/RE-2/RE-3);
  design/primitives/primitives.md §4 #13; FIXME 0835
status: open
---

# Candidate register row: "structural embedding takes exactly one reference"

## Issue

`safety-invariants.md` §4's register exists for the class the S111 finding
named — memory-safety defects found only incidentally, never structurally. The
S118 W2b ruling on FIXME 0835 produced a rule that is a natural member and is
currently recorded only in the two per-crate design docs
(`design/runtime/s118-structural-embedding-ownership.md` §2 and
`design/primitives/primitives.md` §4 #13):

> **RE-1.** When a runtime helper embeds an existing heap structure into a new
> structure **by pointer** (structural sharing, not copying), it takes exactly
> **one** `rc_inc` — on the node it stores. Interior nodes are owned by their
> parent node; elements by the node that holds them; those owners are unchanged
> by the embedding and MUST NOT be re-counted.
>
> **Auditable corollary:** the inc count for one embed is **1, independent of
> the size and depth of the embedded structure**. A producer whose inc count
> scales with `|structure|` is by construction minting references no owner
> holds.
>
> **Dual (RE-2):** every `cranelisp-intrinsics::drop::consume_*` is
> tree-ownership drop glue — it releases the one reference handed to it and
> descends only on the last one — and is therefore structurally incapable of
> discharging a reference no owner holds. RE-1 is not a convention the consumer
> could be relaxed to tolerate.

It fits the register's shape well: the violation is silent (a leak, not a
fault), the corollary is a *mechanical* check (count the incs; it must not be a
function of `|structure|`), and the defect it names went three sprints
undetected behind a unit row that happened to sit on its blind point (a
one-cell `ys` with bare-tag elements ⇒ zero surplus incs).

## Proposed resolution

`/arch` rules whether this becomes register row **R14** — status
"asserted" once the S118 W2b `/dev` change-set lands its counter-based
inc-count fence, which is the tier-3 seam assert form of the corollary. If it
does, `design/runtime/s118-structural-embedding-ownership.md` §2 stays the full
statement and the register row cites it (the §4 convention).

This is a filing, not a request to change any `/arch`-owned text before the
ruling; `/design` cannot edit `design/arch/`. Nothing in the S118 W2b
implementation is gated on it.

## Context

FIXME 0835's W2b contract ruling (`/design`(intrinsics), 2026-07-26). Principle
18 (enforce invariants structurally), Principle 25 (narrowing carries its
check) — the producer-side over-inc is not a narrowing, but the register's
purpose (make this class findable structurally rather than incidentally) is the
same one.
