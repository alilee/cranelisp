# Macro-turn ownership protocol

**Owner:** `design` (int). **Status:** current contract, verified against source
on 2026-09-21. **Subordinate to:** [`int.md`](int.md) §6.2.
**Seam:** `src/expander.rs::invoke_clause`, `invoke_jit_protected` and
`src/marshal.rs`; the clause-preparation pin in `src/process_form/macro_clause.rs`.

Governing inputs, not restated here:

- `design/arch/bounded-contexts.md` §6 — the macro-clause ABI ownership ruling.
- [Typed consume funnel](../runtime/s119-typed-consume-funnel.md) — `Owned`,
  `Borrowed`, `Owned::from_abi`, `Owned::into_raw` and the `consume_*` releasers.
- [Program-result ownership](result-owner.md) §1 — the observe-then-release
  discipline Rule 4 applies to expansion results.

Section numbers are stable because source, tests and filings cite them. Retired
numbers (§1, §2, §4, §6, §7, §10–§13) are not reused.

---

## 0. Actors and the function between them

A **macro turn** is one `invoke_clause` call. Three actors meet there:

| Actor | Role |
|---|---|
| The marshaller (`src/marshal.rs`) | Builds a runtime Sexp tree from the compiler `Sexp` arguments. |
| The compiled clause | Receives one `(SList Sexp)` word, runs ordinary compiled RC code and returns one `Sexp` word. |
| The unmarshaller (`marshal::runtime_to_sexp`) | Reads the result tree into a fresh compiler `Sexp`. It takes no ownership. |

The function between them is a **transfer discipline**: at every moment each
live runtime cell has exactly one accounted owner, and the turn ends with no
cell owned by int.

A compiler `Sexp` is a value, not a view: `runtime_to_sexp` deep-copies
structure and strings. Nothing the expander returns to Pass 1 points into the
runtime heap, which is what makes the whole turn's heap reclaimable at turn
exit.

---

## 3. The protocol

### Rule 0 — the macro-clause ABI declares its ownership; it is never inferred

> **`MacroClauseAbi::SexpListToSexpI64V1`**: `extern "C" fn(i64) -> i64`. The
> argument word is an **owned** `(SList Sexp)` reference, **consumed** by the
> callee. The result word is an **owned** `Sexp` reference, **transferred** to
> the caller.

- Typecheck's ownership inference can classify a clause parameter `Borrowed`,
  and backend then elides its release. A clause that returns part of its
  argument is widened to owned by escape; a clause that builds a fresh result
  need not be. Without a pin the convention could differ per clause, and no
  fixed host protocol is correct for both: transfer to a borrowing callee
  leaks, retention from a consuming callee double-frees.
- **The pin is int's, at clause preparation.** After `check_forms` returns and
  before the clause entry reaches codegen, int clears the synthesized clause's
  inferred `mode_summary`. An absent summary compiles all-Owned, which is
  exactly the declared convention. Int knows clause-ness by construction
  because it synthesized the definition, so no name-prefix privilege enters
  typecheck or backend (**Principle 19**). The cost is a few redundant RC
  operations inside clause bodies, at compile time only.
- Declaring the parameter owned is a widening, which ownership inference treats
  as always sound: the callee releases a reference it was given.

### Rule 1 — the marshaller produces owned trees and retains nothing

- `sexp_to_runtime` returns an `Owned` root of a single-owner tree: every cell
  at RC = 1, held by its unique parent.
- `marshal_children_to_slist` and `build_runtime_slist` consume child handles.
  Storing a child into a parent field is its discharge, so only the root is an
  outstanding `Owned` in a marshal frame.
- **Completeness.** This holds for every cell kind the marshaller allocates:
  `SexpInt`/`SexpFloat`/`SexpBool` (one cell), `SexpStr`/`SexpSym` (cell and its
  `HeapString`), `SexpList`/`SexpBracket` (cell, payload spine and each element,
  recursively), `Sexp::Annotated` (the one two-field cell) and the argument
  `SList` spine. A bare nullary tag is not a cell (Rule 6).
- An early return partway through building a tree trips the debug drop-bomb at
  that frame.

### Rule 2 — no marshalled cell is protected

The marshaller applies no protective increment to any cell. A count for a
reference nobody holds is not a count of a real reference.

**Why this does not reopen the 0638 double-free.** That defect came from an
asymmetric state: the old marshaller retained the whole tree but counted its
retention only on each argument's top cell. A clause that matched its argument
several times and consumed a deep interior alias (for example, folding over a
returned tail) drove an interior cell to zero while it was still reachable,
the freed block was reused, and a later decrement double-freed it. The
negative-control twin — the same helper logic reached through an ordinary
function call — passes the argument as a single-owner tree at RC = 1,
transferred consuming, and runs with no leak and no double-free. Compiled clause
code is therefore net-balanced to one decrement per cell for a single-owner
input. Rule 1 gives the clause exactly that input. The five pins in
`tests/macro_expansion_interior_alias_double_free.rs` guard it.

Deep-copying the arguments or the result would not help: the arguments are
already a disjoint copy, and the aliasing arises inside the clause.

### Rule 3 — the argument tree is discharged by crossing the ABI

`invoke_clause` moves the argument `Owned` by value into
`invoke_jit_protected`, which converts it with `Owned::into_raw` at the call.
**Crossing the C ABI is the discharge.** After the call begins, int holds no
argument reference.

- Nothing is released at turn exit, so there is no turn-exit ordering question
  and no aliasing analysis.
- **A trapped or panicking invocation forfeits the argument tree.** When the
  clause traps (`SIGFPE`, `SIGILL` or `SIGBUS`, recovered by `siglongjmp`) or
  panics, ownership has already left int and the JIT frames are abandoned. Int
  releases nothing: any host cleanup would be a double-free or a traversal of a
  possibly corrupt tree. This is a named, bounded residual: at most one argument
  tree per failed expansion, which the user sees as an error.
- **A clause-reported runtime error is a different path, with no bound.**
  `runtime/panic` records the error in a thread-local and *returns*; the
  panicking function alone returns a dummy `0`, skipping its own compiled
  cleanup, and its callers continue normally. The clause may therefore still
  return an ordinary word to int. Int discards that word without release
  (Rule 4). Whatever the panicking frame owned is not released, and the
  discarded result word is not released; neither quantity is bounded here.
- Zero-residue claims extend to neither path, and an instrument must not
  attribute either residue to a regression of this protocol.

### Rule 4 — the result tree is owned by int and discharged exactly once

`invoke_clause` wraps the returned word with `Owned::from_abi`, then:

1. **Validate.** A word below `NULLARY_TAG_THRESHOLD` is the existing "macro
   returned invalid value" error; its discharge is a no-op.
2. **Observe.** `runtime_to_sexp` reads through a `Borrowed` and copies the tree
   out.
3. **Release.** Discharge the `Owned` with `cranelisp_intrinsics::drop::consume_sexp`,
   once, after the copy completes.

- `consume_sexp` is transitive over every cell kind the seam produces,
  including both fields of `Sexp::Annotated`, and stops at any live shared
  reference.
- The unmarshaller is a reader. There is exactly one releaser, and it lives in
  intrinsics. Int must not grow a second traversal.
- On a clause-reported runtime error, `invoke_jit_protected` checks
  `take_runtime_error()` before returning the word, so `invoke_clause` never
  wraps it. The word is discarded without release: the clause continued past a
  dummy `0`, so the word is not a trustworthy tree to traverse. This joins the
  Rule 3 runtime-error residual.

### Rule 5 — `src/marshal.rs` owns no RC primitive

- Int does not open-code RC. Any future increment at this seam routes through
  `Borrowed::to_owned()` or `cranelisp_intrinsics::rc::rc_inc`.
- The raw `read_i64`/`write_i64` helpers remain: they are the reader half of the
  seam and mirror an intrinsics-private primitive int cannot call. Their layout
  constants are guarded by unit rows against `HeapHeader` drift; a new layout
  constant needs its own guard row.

### Rule 6 — a bare nullary tag is a value, never a handle

Every word below `NULLARY_TAG_THRESHOLD`, `SNil` included, is data.
`build_runtime_slist` over no items legitimately yields `TAG_SNIL`. A handle may
hold such a word; discharging it is a no-op, as every intrinsics consume entry
already guards. Refusing it would force a second path for nullary macros.

### Rule 7 — no marshal handle outlives its invocation

No `Owned` or `Borrowed` from this seam is stored beyond one `invoke_clause`
frame: not in `ExecutableMacroClause`, `PreparedCommit`, a source retry
continuation, `SharedState` or any introspection record. The ownership extent is
the invocation, not a macro publication checkpoint or source-processing attempt
(§9).

`ExecutableMacroClause.owner: Code` and `invoke_clause`'s code lease are a
code-lifetime guard (**Principle 22**), not a heap handle.

---

## 5. Rejected alternatives

- **Retain the arguments and release them at turn exit.** Two owners stay live
  for the call and the ordering question reopens. Transfer leaves one owner. It
  is rejected as strictly weaker, not as unsafe under correct counting.
- **A turn-scoped arena or epoch.** Clause-allocated cells come from the shared
  `alloc_with_rc` funnel, which knows no turns, so an arena needs a second
  allocation regime. Clauses run arbitrary code: `trace` cells land in an
  int-side ring buffer and lenient-evaluation sparks allocate on other threads,
  so wholesale reclaim would trade a leak class for use-after-free. A second
  regime also bypasses or duplicates the M1/M2/M3 allocator ledger and hides
  over-increment defects instead of making counts true. Reconsider only with a
  written answer for which objects escape the turn and how the ledger sees
  arena memory.

---

## 8. Standing evidence

Labels are stable because source and filings cite them.

- **D0 — the emitted clause convention.** The clause-frame golden
  (`tests/fixtures/clif_w0b/`) shows the all-Owned clause releasing its
  parameter.
- **D2 — `Sexp::Annotated` discharge.** Intrinsics' tag dispatch discharges both
  fields; the marshal completeness row visits the annotated root, both children
  and both strings. A compensating release walk in `src/marshal.rs` is a
  `review` reject.
- **D3 — drop-bomb detection proof.**
  `marshal::tests::undisposed_marshaled_root_triggers_the_drop_bomb` proves a
  leaked `Owned` at this seam is caught at its frame.
- **D4 — the Rule-0 fence.**
  `macro_clause::tests::macro_clause_preparation_clears_inferred_ownership_summary`
  fails if clause preparation ever publishes an inferred mode summary.

Balance and aliasing are pinned by:

- `tests/macro_turn_marshal_leak_0889.rs` — one-argument and nullary expansions
  are exactly balanced against a marginal twin;
- `tests/macro_expansion_interior_alias_double_free.rs` — the five 0638
  interior-alias pins;
- the marshal unit rows asserting RC = 1 on every cell
  (`marshalled_tree_is_single_owner_at_every_depth`,
  `single_owner_completeness_over_cell_kinds`,
  `args_slist_spine_is_single_owner`).

The Rule-3 trap forfeit has no zero-residue test. What is structural is that int
cannot release the argument after the move: the handle is moved into the call
and cannot be named afterwards. The Rule-3 runtime-error residual has no test
and no bound.

No `cranelisp-types`, schema or `public-api.txt` change is involved: `expander`
and `marshal` are crate-private in a binary.

---

## 9. Interaction with macro checkpoints

Clause invocation and clause publication are different ownership extents. A
macro checkpoint prepares and publishes compiler state; `invoke_clause`
temporarily transfers a runtime argument and result tree. No marshal handle
enters `PreparedCommit`, the source retry continuation, the table,
introspection or a code-owner record.

Replacement safety uses the ordinary module guard:

- The macro reader holds one read guard while it snapshots the parent clause
  metadata and the selected clause's validated origin, ABI, GOT pointer and
  cloned `Code` owner. It releases the guard before marshalling or invoking.
  The owner clone keeps code alive through the whole Rule-3/Rule-4 window.
- The replacement writer holds the matching write guard from before backend
  finalization can patch a reused slot through the one-module
  `publish_compiled_staged` call. A reader therefore sees one complete
  generation.

Clause-set shrink is part of that publication:

- Int derives surplus keys only from the prior parent's exact clause indices,
  validates each as a private same-parent `MacroClause`, and submits absent-key
  `ChangeAbi` decisions with the replacement parent and active clauses.
- Publication returns each surplus clause's displaced `Code` owner; the writer
  moves those owners into session retention before releasing the guard. Their
  GOT cells stay at the old pointers and their slots stay tombstoned, so a
  reader holding a snapshot stays executable and later growth cannot reuse a
  retired index. This does not authorize removing any ordinary callable.
- If any shrink decision fails, parent, clauses, owners, GOT cells and
  tombstones are unchanged.

Further constraints:

1. Macro publication moves generated drop-glue rows as `{artifact, owner}`
   pairs through the ordinary publication seam. Marshal handles never join
   them.
2. A publication failure restores any touched GOT cell while candidate code
   owners are alive. Rule 3's trap forfeit is independent: neither path cleans
   up the other's resource.
3. A `ResolutionGap` parks source continuation only. No marshalled value, JIT
   owner, checked candidate world or invocation frame survives the retry.

`TurnCheckWorld`, `TurnDelta`, `PreparedMacroTurn`, candidate invocation and
reserved unpublished GOT cells are prohibited by the checkpoint design
(`s117-conformance-recovery.md` §1.1.2).
