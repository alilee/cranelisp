# The macro-turn ownership protocol (FIXME 0889; Spine 2 tranche B-int)

> Subordinate topic doc, cited from `design/int/int.md` §6.2 and §16, and from
> `src/CLAUDE.md` §"Macro expansion". Owned by `/design`(int). Authored S119
> Phase 3 against `sprints/SPRINT.md` §Architecture review (`/arch`'s Phase-2
> ruling, binding) and FIXME 0889's own precondition — *the ownership protocol is
> ruled before any `/dev` dispatch*.
>
> **Status: RULED, pre-implementation.** §3 is normative. §8 is the ordered
> `/dev` obligation set, and **§8 D0 is a hard gate: the protocol does not bind
> until D0's measurement is on the record** (the sprint's measure-before-binding
> discipline; the S118 §4.1 falsification is the precedent).
>
> **S121:** both open dependencies returned settled — §12 records the answers,
> §3 Rule 0 absorbs the `/arch` enforcement ruling (FIXME 0927), and §8 D2's
> intrinsics gap is now a scheduled precondition rather than a discovery. The
> §3 protocol is unchanged. The implementation is bundle **N4** of
> `design/int/s121-c6-visit.md` §6, which also records the as-built
> preconditions re-verified in that window.
>
> **S121 macro-checkpoint reconciliation (user-approved 2026-09-03).** The
> invocation ownership protocol remains unchanged, but the adjacent 0863
> temporary publication design does not. A successful `defmacro` now publishes
> as an immediate one-module checkpoint. Section 9 replaces the former
> must-not-interleave guidance; no `PreparedMacroTurn`, `TurnCheckWorld`,
> candidate invocation, or reserved unpublished GOT stack remains.
>
> Supersedes `design/int/macro-marshal-rc-protection.md` §2 (the deep
> `protect_marshalled_cell` +1). That doc's diagnosis stands and its history is
> load-bearing; its *mechanism* is retired by §3 Rule 2 here.

---

## 0. Actors, and the function between them (Principle 21)

A **macro turn** is one execution of `expander::invoke_clause`
(`src/expander.rs:512-549`) — the only production caller of `src/marshal.rs`.
Three actors meet there:

| # | Actor | What it does with heap memory |
|---|---|---|
| 1 | **The marshaller** (`src/marshal.rs`) | Builds a runtime Sexp ADT tree from a compiler `Sexp`. It is the tree's **producer and, today, its permanent retainer**. |
| 2 | **The JIT-compiled clause** (`__macro_{name}_clause_{i}`) | Receives the args as one `(SList Sexp)` word, runs ordinary compiled RC codegen, returns one `Sexp` word. |
| 3 | **The unmarshaller** (`marshal::runtime_to_sexp`, `:89`) | **Reads** the result tree into a fresh Rust `Sexp`. It never dec's, never frees, and takes no ownership. |

The function that must hold between them is a **transfer discipline**: at every
moment, each live runtime cell has exactly one accounted owner, and the turn ends
with none of them owned by int. Today it holds for none of them.

**A `Sexp` on the Rust side is a value, not a view.** `runtime_to_sexp` deep-copies
structure and copies strings out (`read_runtime_string`, `:269`). Nothing the
expander returns to Pass 1 points into runtime heap. That single fact is what makes
the whole turn's heap footprint reclaimable at turn exit, and it is the premise the
rest of this document rests on.

---

## 1. The as-built accounting, and where 1,143 comes from

Every runtime cell is born at RC = 1 (`alloc::alloc_with_rc`). Structurally that
one count is *the reference its unique parent holds* — an `SCons`'s head/tail
fields, a `SexpList`'s payload spine, a `SexpStr`'s `HeapString` — with the root's
count held by the caller. `alloc_scons` / `alloc_sexp_cell` **store the child
pointer without an inc**, so birth-RC and parent-reference are the same count.
That is a well-formed single-owner tree.

`protect_marshalled_cell` (`src/marshal.rs:204`, applied at `:220`, `:234`,
`:251`, `:264`) then adds **+1 to every cell**, accounting the marshaller's own
retention (the leak, stated in the module header at `:4-18`). So the tree the
clause receives is uniformly RC = 2, and after the clause's net one-dec-per-cell
every marshalled cell rests at RC = 1 — live, unreachable, never dec'd again.
That is the **argument term** of the closed form.

The **result term** is `invoke_clause:548`: `runtime_to_sexp(result_i64)` copies
the tree out and the `i64` is dropped. The clause transferred an owned reference
across the ABI and int discarded it.

```
residual per expansion
  = |marshalled arg cells + args spine|          (argument term)
  + |result-tree cells not aliased into the args| (result term)
```

Committed pins (`tests/macro_turn_marshal_leak_0889.rs`) isolate the two terms:
one one-argument expansion whose result aliases its argument = **+2** (argument
term alone); one nullary constructor-built expansion = **+1** (result term alone).
Full stdlib prelude = **1,143** per session, compile-time bounded (P1/P2 probes 0).

### 1.1 Two defects hiding inside the residual

Neither is the leak, and both close with it:

- **`marshal::rc_inc` (`:316-324`) is a non-atomic `*rc_ptr += 1`** on a cell the
  JIT and its sparks manipulate with `fetch_add(1, Release)`. It is a
  Principle-7 mirror of `cranelisp_intrinsics::rc::rc_inc` that additionally
  drops the A1 seam precheck and the atomicity. Its **only caller is
  `protect_marshalled_cell`**; no other `src/` site calls it. Deleting the
  protection deletes it (Rule 5).
- **The marshaller's "retention" is notional.** After `invoke_clause` returns,
  nothing in Rust holds `marshalled` or `args_slist` — they are plain `i64`s that
  go out of scope. The +1 accounts a reference that no frame, structure, or
  session store actually holds. It is not a wrong count of a real reference; it
  is a count of a reference that does not exist.

---

## 2. Why the naive cure is the trap, and why this one is not

The recorded hazard (FIXME 0638, `macro-marshal-rc-protection.md`) is interior
aliasing: the expansion result can share cells with its arguments, so *releasing
the argument trees at turn exit* can double-free. That history is real and the
`protect_marshalled_cell` +1 is its scar.

But look at what makes it a hazard: it requires **two owners of one cell whose RC
counts only one of them**. Under §3 there is never more than one:

- the argument tree is transferred **into** the clause at the call, so at turn
  exit it does not exist as an ownership domain int can double-release;
- whatever the clause retained from the arguments and placed into the result was
  retained *by the clause's own inc*, so it is covered by the single result
  reference int holds;
- sharing **inside** the result tree is counted sharing, and
  `intrinsics::consume_sexp`/`consume_slist` (`drop.rs:214`/`:156`) stop at
  `old_rc != 1`, i.e. at a live second reference, by construction.

**The 0638-class danger is the miscounting, not the releasing.** The option paper
(`design/arch/ownership-stratum-options.md` §6.3) argues exactly this; this
document carries the argument, and §8 D1 is the obligation to falsify it against
the five committed 0638 pins before it binds.

The distinction that matters and that the paper does not draw: the cure is **not**
"release the args at turn exit with better counting". It is **"do not retain the
args at all"**. Retaining and releasing leaves two owners for the extent of the
call and re-opens the ordering question. Transferring leaves one.

---

## 3. The protocol (normative)

### Rule 0 — the macro-clause ABI declares its ownership; it is never inferred

`MacroClauseAbi::SexpListToSexpI64V1` (`src/expander.rs`) witnesses the calling
convention `extern "C" fn(i64) -> i64`. It is hereby extended to witness the
**ownership** half of that convention, which was previously unstated:

> **`SexpListToSexpI64V1`**: the argument word is an **owned** `(SList Sexp)`
> reference, **consumed** by the callee. The result word is an **owned** `Sexp`
> reference, **transferred** to the caller.

This is a *declaration at a host↔JIT boundary*, in the same model as
`ownership-inference.md` §3.1(a)'s hand-declared per-param facts for extern
primitives — the mirror case (a host-called JIT function rather than a
JIT-called host function). Declaring the parameter `Owned` is a **widening**, and
widening toward Owned is always sound (`ownership-inference.md` §2.1 monotone
soundness): the callee releases a reference it was given, which is correct
whether or not inference could have proven a borrow.

**This rule is load-bearing and is the reason the protocol is a ruling rather
than a patch.** `Mode::Borrowed` is live and produced per-function by typecheck's
ownership fixpoint (`crates/cranelisp-typecheck/src/ownership/`), and backend
elides the parameter release for a `Borrowed` heap param
(`fn_compiler.rs:773-790`). A macro clause that returns part of its argument is
widened off `Borrowed` by the escape rule (`fn_compiler.rs:696-706`); a clause
that builds a fresh result from scratch **need not be**. Without Rule 0 the
callee's convention could differ *per clause*, and no fixed host-side protocol
could be correct for both: transferring to a borrowing callee leaks, retaining
from a consuming callee double-frees. The seam must be pinned, not sampled.

#### Rule 0's enforcement — the pin is int's, at clause preparation (S121, FIXME 0927)

`/arch` ruled the boundary question at the S119 Phase-3 exit gate; the canonical
statement is `design/arch/bounded-contexts.md` §6. Absorbed here:

1. **Not satisfied by construction today.** Clause defns run the full
   `check_forms` path and the ownership fixpoint publishes summaries onto
   callable entries (`crates/cranelisp-typecheck/src/ownership/publish.rs:38`),
   so a fresh-result clause can legally classify `Mode::Borrowed` and backend
   elides its parameter release. The declaration needs a **structural pin**, not
   a normative statement about an accident.
2. **The pin lives at int's clause-preparation seam.** After `check_forms`
   returns and before the clause entry is published for codegen, int **clears**
   the synthesized clause entry's mode summary. Summary-absent ⇒ the all-Owned
   Decision-24 compilation — exactly the convention `SexpListToSexpI64V1`
   declares. The cost is a few redundant RC ops inside clause bodies,
   compile-time only. It is structural under **Principle 19** because int knows
   clause-ness by construction: it synthesized the defn. No name-prefix
   privileging enters typecheck or backend. No `cranelisp-types`, schema or
   public-API delta.
3. **D4's fence lives in int** — a unit row over the prepared turn asserting the
   published clause entry carries no mode summary, so a future widening of
   inference that reattaches one fails loudly. **D0's CLIF measurement stands
   unchanged** as the binding emission-side gate before Rules 1–3 land: the pin
   makes the convention uniform, D0 confirms what that uniform convention
   actually emits.

**As built (verified S121):** not implemented. The only non-test `mode_summary`
mention in `src/process_form/macro_clause.rs` is the `set_callable_slot`
destructure at `:455`, which explicitly *preserves* the summary while
overwriting the slot. Under the S121 C1 lifecycle wash the same act becomes a
field clear at the settlement funnel (`Life::Concrete`'s `mode_summary`); the
seam does not move, only the spelling.

`/dev` obligations D0 and D4 below discharge this rule.

### Rule 1 — the marshaller produces owned trees and retains nothing

`sexp_to_runtime` returns an `Owned` handle to a well-formed single-owner tree:
every cell at RC = 1, held by its unique parent, root held by the returned handle.
`marshal_children_to_slist` / `build_runtime_slist` **consume** the element
handles — a store into a parent cell's field *is* the discharge, exactly as
tranche A's vocabulary defines it — so only the root is ever an outstanding
`Owned` in a marshal frame.

Consequence: an early return partway through building a tree is a drop-bomb in
the debug profile, at the exact frame. There are no such returns today; the
discipline is for the ones a future variant adds.

### Rule 2 — no marshalled cell is protected

`protect_marshalled_cell` and its four call sites are **deleted**. The +1 it
applied accounted a reference nobody holds (§1.1); Rule 1 makes the count true by
removing the retention rather than by counting it.

This is not a revert to the pre-0638 state. Pre-0638 protection was *asymmetric*
— top-level arg cells at RC = 2, interiors at RC = 1 — which is neither a
single-owner tree nor a uniformly-retained one, and that inconsistency is what
0638 pinned. Rule 2 produces the **uniform** state the S114 negative-control twin
proved correct (`macro-marshal-rc-protection.md` §2 "Why +1 per cell is provably
sufficient": the twin passes the same argument shape at RC = 1 as a single owner,
transfers it consuming, and runs clean — no leak, no double-free). Neither the
old code nor the current code has ever had that state at this seam.

### Rule 3 — the argument tree is discharged by crossing the ABI

`invoke_clause` passes the single args `Owned` **by value** into
`invoke_jit_protected`, which converts it to the raw `i64` at the shim and calls
the clause. **Crossing the C ABI is the discharge.** After the conversion int
holds no argument reference at all.

Two consequences, both wanted:

- there is nothing to release at turn exit, and therefore no turn-exit ordering
  question and no aliasing analysis (§2);
- **the trap/panic path is correct by construction.** When the clause traps
  (`SIGFPE`/`SIGILL`/`SIGBUS` via `siglongjmp`) or panics, ownership of the
  argument tree already left int and is forfeit inside the abandoned frame. Int
  releases nothing, because it holds nothing. Doing anything else on that path
  would be a guaranteed double-free or an unbounded traversal of a
  possibly-corrupt tree.

**The trap-path forfeit is a named, bounded residual, not an oversight.** It is
one tree per *failed* expansion — an error the user is shown — and it must be
recorded as such so a future instrument does not read it as a regression of 0889.

### Rule 4 — the result tree is owned by int and discharged exactly once

`invoke_jit_protected` returns the result word; int wraps it as an `Owned` at the
shim. Then, in order:

1. **Validate** — a result word below `NULLARY_TAG_THRESHOLD` is the existing
   `MacroError` ("macro returned invalid value"). A bare tag is a value, not a
   handle (Rule 6); the handle's discharge is a no-op and the error path is
   unchanged.
2. **Observe** — `runtime_to_sexp` takes a `Borrowed`, not an `Owned`: it copies
   structure out and takes no ownership. This is the same *observe-then-release*
   ordering `result-owner.md` §1 makes binding for program results, applied to
   the expansion result. It is one discipline, two seams, not two disciplines.
3. **Release** — discharge the `Owned` with `intrinsics::consume_sexp`. One call,
   after the copy is complete, on every path that produced a valid result word.

`consume_sexp` is transitively correct for every cell kind the seam can produce
(`SexpStr`/`SexpSym` → `consume_shallow` on the `HeapString`; `SexpList`/
`SexpBracket` → `consume_slist` over the payload spine; scalar tags → nothing)
and it stops at any live shared reference. Int never walks the tree itself, and
must not grow a second traversal: the existing `runtime_to_sexp` walk is a
**reader**, and there is exactly one releaser and it lives in intrinsics.

`Sexp::Annotated` is the one two-field runtime cell (`alloc_sexp_pair`, tag
`TAG_SEXP_ANNOTATED`). Confirm `consume_sexp`'s tag dispatch discharges **both**
fields of that tag; if it does not, that is an intrinsics defect this tranche
surfaces and must be fixed there, not worked around here (§8 D2).

### Rule 5 — `src/marshal.rs` owns no RC primitive

With Rule 2, `marshal::rc_inc` (`:316-324`) has no caller and is **deleted**. Int
does not open-code RC. Any future inc at this seam routes through
`cranelisp_intrinsics::rc::rc_inc` (atomic, A1-prechecked) or through the typed
vocabulary's `Borrowed::to_owned()`, which tranche A makes the single home of
`rc_inc`.

The raw `read_i64`/`write_i64` helpers (`:292`/`:302`) stay: they are the
*reader* half of the seam, they mirror an intrinsics-crate-private
(`heap_access`, `pub(crate)`) primitive that int cannot call, and their layout
constants are already guarded against `HeapHeader` drift by the four unit rows at
`:350-410`. Do not delete them and do not add a fifth layout constant without a
guard row.

### Rule 6 — a bare nullary tag is a value, never a handle

Every word below `NULLARY_TAG_THRESHOLD` (`SNil` = 0 among them) is data, not a
pointer. `build_runtime_slist(&[])` legitimately yields `TAG_SNIL`. The typed
handle must **tolerate** such a word: constructing it is legal and discharging it
is a no-op. Every intrinsics consume entry already guards this
(`ptr < NULLARY_THRESHOLD → return`), so tolerance costs nothing and refusing it
would force a second code path at the one place the seam is most likely to be
exercised (a nullary macro).

### Rule 7 — no marshal handle outlives its invocation

No `Owned`/`Borrowed` from this seam is stored in any structure with a lifetime
longer than one `invoke_clause` frame: not in `ExecutableMacroClause`,
`PreparedCommit`, a source retry continuation, `SharedState`, or any
introspection record. The turn's ownership extent is **the invocation**, not a
macro publication checkpoint or source-processing attempt. Section 9 explains
why those lifetimes remain independent.

`ExecutableMacroClause.owner: Code` and `invoke_clause`'s `let _code_lease =
&clause.owner;` are untouched by this tranche. That borrow is a *code*-lifetime
guard (Principle 22), not a heap handle, and its acquisition is 0863's seam.

---

## 4. What the pins read after this lands

| Pin | Today | After |
|---|---|---|
| `…_one_expansion_with_one_marshalled_arg_is_two` | +2 | **0** (Rules 1–3) |
| `…_one_nullary_expansion_is_one` | +1 | **0** (Rule 4) |
| Full stdlib prelude ambient | 1,143 | **0** |

The two pins are the model's two independent terms, which is why they are the
right acceptance instrument: a fix that lands only Rule 4 flips one and holds the
other, visibly. The fixing change-set flips both `assert_residual` values to `0`,
updates `tests/plan/s118-test-plan.md` §2.5 and FIXME 0889, and re-derives the
ambient term that `tests/ms_p8_conj_leak.rs` and
`tests/intrinsics_m3_detection_s116.rs` subtract. The marginal harness itself
stays valid unchanged — the common term simply goes to zero
(`tests/CLAUDE.md` §"Allocator balance is measured MARGINALLY").

---

## 5. Recommendation: typed handles, not arena/epoch

**Recommendation: the typed-transfer protocol above. Arena/epoch is rejected as
the primary and retained only as the §7 fallback.**

The arena/epoch alternative (allocate every turn object from a turn-scoped arena;
reclaim wholesale at turn exit) was assessed against the same seam:

1. **It cannot reach the allocations that matter without a second allocation
   regime.** The residual's larger term is cells allocated by *compiled clause
   code* through the shared `alloc::alloc_with_rc` funnel, which has no notion of
   a turn. Arena-allocating them requires a thread-local "current arena" consulted
   inside that funnel — precisely the second regime `/arch` prices as strictly
   more machinery.
2. **It must still answer the escape question, and the answer is not "no".**
   Expansion results are copied out by `runtime_to_sexp`, so *results* do not
   escape as heap objects — the favourable case. But a clause runs arbitrary
   compiled code inside the dynamic extent: `trace` builds `TraceCall` cells that
   land in an int-side ring buffer, `catch-runtime-error` and lenient-eval sparks
   allocate on other threads. Every one of those is a candidate arena object that
   outlives the turn or is allocated off the arena-owning thread. Wholesale
   reclaim turns each into a use-after-free — a memory-safety defect class traded
   for a leak class, in the sprint whose stated outcome is control.
3. **It blinds the instruments this sprint exists to make truthful.** M1
   quarantine, M2 scrub, and M3 parity all hook `alloc_with_rc`/`dealloc`
   (`crates/cranelisp-intrinsics/src/diagnostics.rs`). A second regime either
   bypasses the ledger — and the 0889 pins, the marginal harness, and the armed
   lane all stop seeing this seam — or replicates every hook.
4. **It hides the counts instead of making them true.** The RE-1/0835 over-inc
   class stays invisible under wholesale reclaim; a surplus reference costs
   nothing when the whole region is dropped. That is the opposite of the
   simplification-and-control outcome the sprint is chartered on, and it would
   make this seam permanently exempt from the ownership stratum's discipline.
5. **It is larger, and the typed route is a net deletion here.** Rules 2 and 5
   delete `protect_marshalled_cell`, its four call sites, and `marshal::rc_inc`.
   Rules 3 and 4 change one function, `invoke_clause` — the **only** production
   caller of `src/marshal.rs` (verified: `sexp_to_runtime` /
   `build_runtime_slist` / `runtime_to_sexp` have exactly one non-test call site
   each, all in `invoke_clause`). Complexity has a budget (Principle 6); this
   spends negative.

A third alternative — **retain the args and release them at turn exit** — is the
shape 0889's own text names and 0638's history warns against. It is rejected in
favour of Rule 3 for the reason in §2: it keeps two owners alive across the call
and re-opens the ordering question that transfer closes. It is *not* rejected as
unsafe under correct counting; it is rejected as strictly weaker.

---

## 6. Severability

`/arch` ruled tranche B-int **best-effort, not guaranteed**, and it is the first
structural item to drop if capacity binds (`sprints/SPRINT.md` §Open items ②).
This document is therefore written to stand alone: **if only the ruling lands,
§3 is a complete, usable artefact** and S120's implementing wave needs no second
design pass — only the §8 gates, which are measurements, not decisions.

Within the implementation, the two rules are severable and the safe order is:

1. **Rule 4 first (the result term, +1 → 0).** Local, additive, and independent
   of the argument-side accounting: with the protection still in place, an
   argument cell aliased into the result sits at RC ≥ 2, so `consume_sexp` dec's
   it and stops. No double-free is reachable in this interim.
2. **Rules 0–3 + 5 second (the argument term, +2 → 0).** This is the half that
   must re-clear the 0638 pins (§8 D1).

Caveat, stated because it is measurement-dependent and `/dev` must not assume it:
in the Rule-4-only interim the *one-argument pin* may read 2 or 1 depending on
whether the clause's returned reference to the aliased argument cell was minted
by an inc or transferred. Either is fine; the pin is the arbiter and its value in
the interim is a recorded measurement, not a prediction. **Landing both halves as
one change-set avoids the question entirely and is preferred.**

---

## 7. The fallback, and its entry condition

If §8 D1 shows the 0638 pins do **not** re-clear under Rules 0–3, the cause is an
imbalance in the clause's own RC codegen independent of the marshaller — in which
case the honest move is **re-attribution to `/dev`(backend) with the D1 trace as
the handoff brief** (the same branch `macro-marshal-rc-protection.md` §4 D2 named
and judged unlikely), *not* a fallback to arena/epoch.

Arena/epoch is entered only if that re-attribution is itself refused, and then
only after §5 items 2 and 3 are answered in writing — which objects escape the
turn, and how the M1/M2/M3 ledger sees arena memory. Entering it without those
answers trades a bounded compile-time leak for an unbounded memory-safety class.

---

## 8. Implementation obligations for `/dev`(int), in order

Each step is a gate; a step that does not produce its stated evidence stops the
wave rather than proceeding on assumption.

- **D0 — pin the clause-side convention (Rule 0; the binding gate).** Determine
  whether a compiled macro clause consumes its `(SList Sexp)` parameter. Read it
  at source, not by inference: `CRANELISP_CODEGEN_DUMP` filtered to a
  `__macro_*_clause_*` symbol, for **two clause shapes** — one that returns part
  of its argument (`` (defmacro ident [x] `~x) ``) and one that builds a fresh
  result and returns no argument part (`(defmacro two [] (SexpInt 2))` with a
  one-argument sibling). Record the parameter's `Mode` and whether a release is
  emitted at clause exit, for each. **If the two disagree, Rule 0 must be made
  structural before Rules 1–3 land** (see D4). *The protocol does not bind until
  this measurement is recorded.*
- **D1 — falsify the 0638 dissolution.** Apply Rules 1–3 + 5 and re-run all five
  pins in `tests/macro_expansion_interior_alias_double_free.rs`, both mode faces,
  serially, and additionally under `CRANELISP_QUARANTINE_FREED=1` +
  `CRANELISP_SCRUB_FREED=1` (M1+M2 make a premature free deterministic rather
  than symptom-polymorphic). **All five green under both plain and armed lanes**
  ⇒ §2's argument is confirmed. Any red ⇒ §7.
- **D2 — confirm `consume_sexp` covers `TAG_SEXP_ANNOTATED`.** Rule 4 discharges
  the result through intrinsics' tag dispatch; the two-field annotated cell
  (`alloc_sexp_pair`) must have both fields discharged. **Confirmed absent, and
  now scheduled (S121):** `crates/cranelisp-intrinsics/src/drop.rs:242-255` has
  two arms plus a scalar catch-all, and `TAG_SEXP_ANNOTATED` is not imported
  (`drop.rs:45`), so an annotated cell today deallocs its parent and leaks both
  halves. The arm is C5 bundle I1
  (`design/intrinsics/s121-c5-intrinsics-visit.md` §5). D2 becomes a
  **precondition check**, not a discovery: it must be landed before Rules 3/4
  bind, because Rule 4 makes the gap definitely reachable. The fix stays in
  `drop.rs`; a compensating walk in `src/marshal.rs` is a `/review` reject.
- **D3 — the drop-bomb detection proof (gate G4's per-tranche obligation).**
  Plant a deliberate leaked-on-the-floor `Owned` at this seam and prove the debug
  bomb catches it, at the frame. Per the 0768 rule an instrument is unverified
  until proven to detect; a typed layer landing with no executing consumer is the
  S118 failure this sprint is structured to avoid.
- **D4 — the standing fence for Rule 0.** A unit-tier row that fails if a macro
  clause ever compiles with a `Borrowed` `(SList Sexp)` parameter. This is the
  structural expression of Rule 0 and the guard against a future widening of
  ownership inference silently converting the seam from consuming to borrowing —
  which would re-introduce the argument-term leak with no pin firing, because the
  pins measure cells and not conventions. If int cannot see the fact from its own
  side, that is the FIXME to `/arch` (see §12).
- **D5 — flip the pins and the record.** Both `assert_residual` values to `0`;
  update FIXME 0889, `tests/plan/s118-test-plan.md` §2.5, and the four
  retrofitted marginal cells' ambient term; re-run the S118 instrument set and
  confirm it is **byte-identical** across the churn (the acceptance criterion for
  churn masking behaviour change).
- **D6 — record the trap-path forfeit.** Rule 3's named residual goes in the
  `invoke_clause` rustdoc and in this document's §3 Rule 3, so the next
  instrument reader does not attribute it to 0889.

Unit tests are `/dev`'s and mandatory (`sprints/METHOD.md` §2.2). The seam is
unit-testable with no JIT session for Rules 1/2/5 (the existing `#[cfg(test)]`
rows at `src/marshal.rs:330-732` are the template — note that
`deep_protect_survives_consuming_teardown`,
`deep_protect_completeness_over_cell_kinds`, and
`deep_protect_covers_args_slist_spine` assert `RC == 2` and are **retired by Rule
2**; their replacement asserts the single-owner invariant `RC == 1` on every
cell, which is the same completeness obligation with the correct number).

**No `cranelisp-types` delta. No schema delta. No `public-api.txt` delta** — both
`expander` and `marshal` are `pub(crate)` in `src/lib.rs` and int is a binary.

---

## 9. Interaction with macro checkpoints

Clause invocation and clause publication remain different ownership extents.
A macro checkpoint prepares and publishes compiler state; `invoke_clause`
temporarily transfers a runtime argument/result tree. No marshal handle enters
`PreparedCommit`, the source retry continuation, the table, introspection, or a
code-owner record.

Replacement safety now uses the ordinary module guard. The macro reader holds
one read guard while it snapshots parent clause metadata and the selected
clause's validated origin, ABI, GOT pointer, and cloned `Code` owner. It releases
the guard before marshalling or invoking. The owner clone keeps code alive for
the complete Rule-3/Rule-4 window. The replacement writer holds the matching
write guard before backend finalization can patch a reused slot and through the
one-module `publish_compiled_staged` call. A reader therefore observes one
complete generation without extending any runtime heap handle.

Clause-set shrink is part of that same publication. Int derives surplus keys
only from the prior parent's exact `M..N` clause indices, validates each as a
private same-parent `MacroClause`, and submits absent-key `ChangeAbi` decisions
with the replacement parent and active clauses. Publication returns each
surplus clause's displaced `Code` owner; the writer moves those owners into
session retention before releasing the guard. Their GOT cells stay frozen at
the old pointers and their slots remain tombstoned, so an already-snapshotted
reader stays executable and later clause growth cannot reuse the retired
indices. This does not authorize removal of any ordinary callable.

The interaction constraints are:

1. `ExecutableMacroClause` owns a code lease, not a marshalled value. Its owner
   remains live through argument transfer, protected invocation, result copy and
   discharge.
2. Macro publication moves generated drop-glue rows as `{artifact, owner}`
   pairs through the ordinary publication seam. Marshal handles never join
   those rows.
3. A publication failure restores any touched GOT cell while candidate code
   owners remain alive. Rule 3's trap-path forfeit is independent: neither path
   cleans up the other's resource class.
4. A `ResolutionGap` parks source continuation only. No marshalled value, JIT
   owner, checked candidate world, or invocation frame survives the retry.
5. Failure of any shrink decision leaves parent, clauses, owners, GOT cells and
   tombstones unchanged; no reader can observe a partially retired generation.

`TurnCheckWorld`, `TurnDelta`, `PreparedMacroTurn`, candidate invocation and
reserved unpublished GOT cells are prohibited by the S121 checkpoint design,
not alternate implementations of this ownership protocol.

---

## 10. Quality attributes

| Attribute | Assessment |
|---|---|
| **Simplicity** | Net deletion: `protect_marshalled_cell` + 4 call sites + `marshal::rc_inc` + 3 unit rows out; one `consume_sexp` call and a handle type in. One production call site changes. Principle 6 spent negative. |
| **Maintainability** | Blast radius is one function (`invoke_clause`) and one module (`src/marshal.rs`), both `pub(crate)`. Rule 7 structurally separates invocation memory from the adjacent macro-checkpoint publication change. |
| **Observability** | The two 0889 pins become ordinary balance guards on this boundary permanently, and the marginal harness's ambient term goes to zero — which makes *every* prelude-loading balance cell in the suite an instrument again rather than a measurement of this residual. That is the largest single observability gain available at this seam. |
| **Concurrency-safety** | Improved and named: Rule 5 removes a non-atomic host RMW on cells the JIT and its lenient-eval sparks touch atomically (§1.1). No new shared state; handles are frame-local by Rule 7. |
| **Performance** | Strictly fewer RC operations (one inc per marshalled cell removed) and one bounded `consume_sexp` walk added per expansion, over trees that are small by construction. Compile-time only; no runtime path. |
| **Testability** | Rules 1/2/5 are unit-testable at the marshal seam with no JIT session (Principle 5, as the existing rows demonstrate). Rules 0/3/4 need the JIT and are covered by the two 0889 pins plus the five 0638 pins. D3 and D4 are the two instruments that must themselves be proven. |

---

## 11. Principles cited

- **Principle 21 (actors and functions before mechanism)** — §0 names the three
  actors and the transfer discipline between them before any mechanism.
- **Principle 26 (record from settled state)** — Rule 2 removes a count of a
  reference nobody holds; Rule 0 declares the convention rather than sampling it.
- **Principle 20 (model invariants by representation)** and **Principle 18
  (enforce invariants structurally)** — the transfer is the signature; the
  drop-bomb and `#[must_use]` are the enforcement; D4 is Rule 0's structural
  expression.
- **Principle 7 (single source of truth)** — Rule 5 removes int's private RC
  primitive; Rule 4 keeps exactly one releaser and it lives in intrinsics.
- **Principle 6 (complexity has a budget)** — §5's arena/epoch rejection is a
  budget argument as much as a safety one.
- **Principle 5 (testability is structural)** — §8's unit tier exists because the
  seam is a pure transform over a heap layout, JIT-independent for two of the
  three rules.
- **Principle 22 (published pointers have retention owners)** — untouched and
  preserved: `ExecutableMacroClause.owner` remains the code-lifetime guard, and
  Rule 7 forbids conflating it with a heap handle.

---

## 12. Dependencies — both returned settled (S121)

- **FIXME 0921 to `/design`(runtime pair) — ANSWERED.** All three requirements
  are met by `design/runtime/s119-typed-consume-funnel.md` §3: the ABI-crossing
  pair is `Owned::from_abi` (the one raw entry) / `Owned::into_raw` (the one raw
  exit, `#[must_use]`, and the crate's only handle-related `mem::forget`), which
  is what makes Rule 3's transfer — and therefore the JIT trap path's
  correctness by construction — expressible at a `transmute`d call site with no
  shim; `from_abi` is nullary-tag-safe and `is_nullary_tag` single-sources the
  `< NULLARY_TAG_THRESHOLD` predicate, satisfying Rule 6; and
  `consume_sexp`/`consume_slist` stay `pub` with typed signatures — tranche A's
  own signatures are what force the handle types public, so Rule 4's single
  releaser stays reachable from int. **No gap remains to state.** The filing's
  separately-confirmed intrinsics finding (the missing `TAG_SEXP_ANNOTATED`
  arm) is D2 above.
- **FIXME 0927 to `/arch`, then here — ABSORBED.** The macro-clause ABI
  ownership declaration is ruled: the pin is int's, at clause preparation, by
  clearing the synthesized clause entry's mode summary. Absorbed at §3 Rule 0's
  enforcement subsection, with D4 as its standing fence.

One item is **not** closed by either: `src/marshal.rs:316`'s non-atomic
`*rc_ptr += 1` — re-verified live at S121, as `s119-typed-consume-funnel.md`
asked. Rule 5 deletes it and the typed mint replaces it; it is an obligation,
not a dependency.

---

## 13. Cross-references

- `design/arch/ownership-stratum-options.md` §2.3 (tranche B, as amended
  `3232a061`), §2.4, §6.3 — the routing this ruling implements.
- `design/int/macro-marshal-rc-protection.md` — the 0638 history; its §2
  mechanism is superseded by Rule 2, its §0/§1 diagnosis and its
  negative-control-twin argument are load-bearing here.
- `design/int/result-owner.md` §1 — the observe-then-release discipline Rule 4
  applies at a second seam.
- `design/int/s117-conformance-recovery.md` §1.1.2, §2.1, §6.5 — the current
  macro-checkpoint and presentation design; §9 is the interaction statement.
- `src/marshal.rs`, `src/expander.rs:512-549` (`invoke_clause`) — the seam.
- `crates/cranelisp-intrinsics/src/drop.rs:156` (`consume_slist`), `:214`
  (`consume_sexp`) — the single releaser.
- `tests/macro_turn_marshal_leak_0889.rs` — the two exact-value pins (§4).
- `tests/macro_expansion_interior_alias_double_free.rs` — the five 0638 pins
  (§8 D1).
- `design/arch/safety-invariants.md` §2 — the trust-boundary tier this seam sits
  in.
