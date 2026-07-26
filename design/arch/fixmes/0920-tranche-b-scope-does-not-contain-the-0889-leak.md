---
number: 0920
target: /arch
filed_by: /sprint
filed_at: 2026-07-26
sprint_filed: 119
refers_to: design/arch/ownership-stratum-options.md:25-36,236-237 + src/marshal.rs + crates/cranelisp-primitives/src/marshal.rs
status: open
---

# Option-1 tranche B's scope does not contain the FIXME 0889 leak it is designated to recover

## Severity

Blocker for the Sprint 119 scope as approved.

## Issue

Found while verifying S119 scope carries against source (METHOD §3.3), 2026-07-26.

`design/arch/ownership-stratum-options.md:236-237` scopes tranche B as:

> **Tranche B — `marshal.rs`** (339 lines, the macro-expansion data path).

and §6.3 states that this tranche **is** the FIXME 0889 recovery vehicle: typed handles make
argument-tree and result-tree counts truthful, after which the turn exit is plain
`consume`-per-tree.

Measured against the tree, the two halves of that sentence name **different files in
different crates**:

| File | Lines | What it is |
|---|---|---|
| `crates/cranelisp-primitives/src/marshal.rs` | **339** | the runtime `quote_sexp` / `sconcat` helpers |
| `src/marshal.rs` | **732** | the macro-expansion data path — **where the 0889 leak lives** |
| `crates/cranelisp-types/src/marshal.rs` | 80 | tag constants |

`crates/cranelisp-intrinsics/src/marshal.rs` does not exist.

The 339-line figure identifies the **primitives** file; "the macro-expansion data path" and
the 0889 leak identify `src/marshal.rs`, whose own header states the claim verbatim
(`src/marshal.rs:4-5`: *"Marshalled values are 'leaked' -- their RC is never decremented"*),
with the FIXME-0638 `protect_marshalled_cell` +1 note at `:7-14`. The leak's other half is
`src/expander.rs::invoke_clause`.

**The consequence is structural, not clerical.** `src/` is the **int binary**, which §1.1
(`:25-36`) explicitly excludes from the definition of "the hand-written runtime pair" that
option 1 is scoped to. So tranche B as written either:

- covers `crates/cranelisp-primitives/src/marshal.rs`, in which case it is inside option 1's
  stated boundary but **does not contain the 0889 leak**, and the §6.3 recovery claim is
  false; or
- covers `src/marshal.rs`, in which case it **does** contain the leak but sits outside the
  stratum option 1 was scoped to, is ~732 lines rather than 339, involves a different crate
  and a different `/dev` surface, and needs `/design`(int) — not `/design`(runtime pair) — to
  rule the ownership protocol first, exactly as 0889 itself requires.

Either way the tranche-B size is understated and its owning surface is misassigned.

## Why this matters now

The user approved the **structural-first** S119 shape (2026-07-26 Phase 1) specifically on
the strength of tranches A+B landing the 0889 recovery this sprint. That approval rests on
the §6.3 claim. The scope must be corrected before Phase 3 dispatch, or the sprint's
headline deliverable is scoped at the wrong file.

## Proposed resolution

`/arch` re-scopes tranche B in the option paper, choosing explicitly between:

1. **Tranche B = `src/marshal.rs` + `src/expander.rs::invoke_clause`** (the leak). Then
   option 1's boundary widens to name the int marshal path as a third typed surface, the
   `/design` owner for the contract is `/design`(int) with `/arch` on the boundary question,
   and the tranche is re-sized (~732 lines, plus the expander seam).
2. **Tranche B = `crates/cranelisp-primitives/src/marshal.rs`** (inside the pair). Then §6.3
   is corrected to withdraw the 0889-recovery claim, and 0889's route reverts to the user's
   decision-4 alternative (the arena/epoch turn allocator) or to a separately scoped int
   tranche.
3. **Both, as B1 and B2**, sequenced — the pair-side first (inside the existing boundary),
   the int-side second with its own `/design`(int) ruling.

Whichever is chosen, the ~83 `extern "C"` / ~131 `i64`-taking / ~31 `consume_*` sizing
figures in §2.3 should be re-pinned against measurement: verified 2026-07-26 as **83**
`extern "C" fn` (intrinsics 81 + primitives 2 — exact match), **136** non-extern
`i64`-taking single-line fn declarations (166 including extern), and **36** `consume_*` call
sites in primitives (`string.rs` 27, `marshal.rs` 8, `int.rs` 1). Tranche A's sizing is
sound; only tranche B's is wrong.

## Note

Tranche A is unaffected and can proceed on its stated scope
(`cranelisp-intrinsics::drop` + the primitives `consume_*` call sites).
