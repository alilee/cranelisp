---
number: 0922
target: /arch
filed_by: /design
filed_at: 2026-07-26
sprint_filed: 119
refers_to: design/int/macro-turn-ownership.md §3 Rule 0 and §8 D0/D4;
  src/expander.rs (MacroClauseAbi::SexpListToSexpI64V1, invoke_clause:512-549);
  crates/cranelisp-backend/src/compiler/fn_compiler.rs:696-706, :773-790;
  design/arch/ownership-inference.md §2.1 (monotone soundness), §3.1(a) (declared leaf facts)
status: open
---

# The macro-clause ABI must DECLARE its parameter ownership; today it is inferred, and inference is per-function

**Target: `/arch`** — this is the tranche-B boundary question `/arch` reserved
(`ownership-stratum-options.md` §2.3: "`/arch` holds the boundary question").
Filed by `/design`(int) with the tranche B-int ownership ruling
(`design/int/macro-turn-ownership.md`); it is that ruling's **Rule 0**, and the
one part of it int cannot settle inside its own bounded context.

## Issue

`invoke_clause` calls a compiled macro clause through a `transmute`d
`extern "C" fn(i64) -> i64` witnessed by `MacroClauseAbi::SexpListToSexpI64V1`.
That witness names the *calling convention* and says nothing about **ownership**:
whether the callee consumes the `(SList Sexp)` argument word, and whether the
returned `Sexp` word is transferred to the caller.

Int must know, because the two answers demand opposite host-side code:

| Callee convention | Correct host behaviour | Wrong host behaviour |
|---|---|---|
| consumes the arg (`Owned` param) | transfer and hold nothing | retain-and-release ⇒ **double free** |
| borrows the arg (`Borrowed` param) | retain and release after the call | transfer ⇒ **leak** |

Today nothing pins it, and the fact is **inferred per function**:

- `Mode::Borrowed` is live and produced by typecheck's ownership fixpoint
  (`crates/cranelisp-typecheck/src/ownership/{fixpoint,transfer}.rs`);
- backend **elides** the parameter release for a `Borrowed` heap param
  (`fn_compiler.rs:773-790`);
- a clause that returns part of its argument is widened off `Borrowed` by the
  escape rule (`fn_compiler.rs:696-706` — the `debug_assert!` at `:705` states
  it), but **a clause that builds a fresh result and returns no argument part
  need not be**.

So two clauses of the same macro can legitimately differ, and no fixed host-side
protocol is correct for both. Worse, the failure mode is silent in both
directions: the leak direction moves an allocation count that only the two 0889
pins measure, and those pins measure *cells*, not *conventions* — a future
widening of ownership inference could flip this seam from consuming to borrowing
and re-introduce the argument-term leak with no pin firing.

## Proposed resolution

Rule the macro-clause boundary a **declared** ownership contract, not an inferred
one, and state where the declaration is enforced.

`/design`(int) has ruled the int side already (Rule 0): the ABI witness carries
the statement *"argument word is owned and consumed by the callee; result word is
owned and transferred to the caller"*, and int transfers unconditionally.
Declaring the parameter `Owned` is a **widening**, and widening toward Owned is
always sound (`ownership-inference.md` §2.1) — the callee releases a reference it
was given, correct whether or not inference could have proven a borrow. The model
already has the shape: §3.1(a)'s hand-declared per-param facts for extern
primitives are the mirror case (a JIT-called host function); a macro clause is a
host-called JIT function.

What `/arch` is asked to rule is the **enforcement seam**, since it crosses int,
typecheck (which computes the summary) and backend (which acts on it):

1. Is the declaration satisfied *today* by construction — e.g. the synthesized
   `__macro_*_clause_*` defns carry no `ModeSummary`, so the Decision-24 Owned
   default applies? If so, say so normatively, so it is a stated invariant rather
   than an accident that the next inference widening can silently retract.
2. If not, where does the declaration live — a mode-summary pin at clause
   synthesis, an exemption in the ownership walk, or a declared-fact channel?
3. Either way, **what can int assert?** Int needs a standing fence that fails if
   a macro clause ever compiles with a `Borrowed` `(SList Sexp)` parameter
   (`macro-turn-ownership.md` §8 D4). If int cannot see a clause's `Mode` from
   its own side, the fence has to live elsewhere and `/arch` should name where.

## Context

This gates nothing in Phase 3 — the tranche B-int protocol is ruled and severable
without it. It gates the **implementation**: `macro-turn-ownership.md` §8 D0 is a
hard measurement gate that reads the convention out of two clause shapes' CLIF
before Rules 1–3 land, and D4 is the standing fence. A `/dev` measurement can
answer question 1 for today; only `/arch` can make the answer binding.

No `cranelisp-types` delta is expected in the "already satisfied by construction"
disposition, which is the expected one — this is a statement-and-fence request,
not a mechanism request. Sprint scope authorizes no types delta and exactly one
schema window (23→24, 0869's), so if the resolution needs either, it belongs to
S120.
