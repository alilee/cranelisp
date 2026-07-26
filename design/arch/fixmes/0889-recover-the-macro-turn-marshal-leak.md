---
number: 0889
target: /dev
filed_by: /sprint
filed_at: 2026-07-26
sprint_filed: 118
refers_to: design/int/macro-turn-ownership.md (the S119 /design(int) protocol ruling — READ FIRST);
  src/marshal.rs (header: "their RC is never decremented");
  src/expander.rs §invoke_clause (result tree dropped unconsumed);
  design/arch/fixmes/0835-slist-sexp-construction-corrupts-the-heap-at-small-sizes.md §Branch-F falsification pointer;
  tests/plan/s118-test-plan.md §2.5 (Branch-F execution record);
  sprints/archive/sprint-118.md §Notes 2026-07-26 (user decision)
status: open
---

# Recover the macro-turn marshal leak (the ambient 1143 prelude residue)

Surface: Binary/int (`src/marshal.rs` + `src/expander.rs`). `/design`(int)
rules the ownership protocol BEFORE any `/dev` dispatch.

**USER DECISION (2026-07-26, S118 Branch-F closure):** S118 makes the
exit-balance *instrument* truthful (marginal/twin-control accounting in the
affected cells) and explicitly accepts the leak for now; this FIXME is the
user-required record that the leak itself must be recovered in a future
sprint — accounting around it is not closure.

## The defect

Every macro expansion leaks, by documented design, at the int-side macro-turn
marshal boundary:

- marshalled argument trees are never RC-decremented (`src/marshal.rs` header
  states this as intent; each cell further pinned by the FIXME-0638
  `protect_marshalled_cell` +1);
- the expansion-result tree is never consumed after `runtime_to_sexp` copies
  it (`src/expander.rs` `invoke_clause` drops the `i64`).

Closed-form residual, exact on every S118 probe point: **|marshalled arg
cells + args spine| + |non-aliased result-tree cells|, per expansion.** Full
stdlib prelude: 1,143 allocations per session. Compile-time bounded; does not
grow with runtime execution (P1/P2 probes = 0).

## Resolution requirements

- True balance at the macro-turn boundary: post-turn deep-release of the
  marshalled argument trees + consume of the expansion result, with
  result↔argument **aliasing** handled (P3c's result aliases its arg — a
  naive release double-frees; the FIXME-0638 interior-alias double-free
  history shows this has burned once already), OR an arena/epoch expansion
  allocator that reclaims the whole turn wholesale (see
  `design/arch/` S119 structural option paper, marginal-balance/arena
  options).
- The S118 exact-value probe pins (P3 +2, no-quote +1 class) flip from
  documented-residual to zero in the fixing change-set.
- The S118 marginal-accounting instrument remains valid afterwards (it
  measures runtime behavior either way).

Scheduled: S119, under the structural option paper's disposition.

## `/design`(int) ruling — S119 Phase 3 (the precondition is DISCHARGED)

This FIXME's precondition — *the ownership protocol is ruled before any `/dev`
dispatch* — is met by **`design/int/macro-turn-ownership.md`**. Target moves to
`/dev`(int); the design question is closed, the implementation is not.

The ruling in four lines (§3 is normative; read it, not this summary):

- **Rule 0** — the macro-clause ABI *declares* its ownership (arg consumed,
  result transferred). It is not inferred; `Mode::Borrowed` is live and
  per-function, so an inferred seam could differ per clause. FIXME 0922 to
  `/arch` holds the enforcement question.
- **Rules 1–3** — the marshaller produces **single-owner** trees (every cell at
  RC = 1, held by its unique parent) and **transfers** them by crossing the C
  ABI. `protect_marshalled_cell`, its four call sites, and `marshal::rc_inc` are
  deleted. Int retains nothing and releases nothing on the argument side; the
  JIT trap path is therefore correct by construction.
- **Rule 4** — the result word is an `Owned` int observes via `runtime_to_sexp`
  (a borrowing read) and then discharges **exactly once** through
  `cranelisp_intrinsics::consume_sexp` — the observe-then-release order
  `result-owner.md` §1 already makes binding, applied at a second seam.
- **The 0638 trap is dissolved, not braved.** Interior aliasing is only a hazard
  with two owners of one under-counted cell; after Rule 3 the argument tree is
  not an ownership domain int holds at turn exit, and sharing inside the result
  is counted sharing that `consume_sexp` stops at. **This is not a revert to
  pre-0638 top-only protection** (asymmetric, and that asymmetry is what 0638
  pinned) — it is the uniform single-owner state the S114 negative-control twin
  proved correct and that neither the old nor the current code has ever had.

**Arena/epoch is REJECTED as the primary** (§5): it cannot reach clause-code
allocations without a second regime inside the shared alloc funnel, it must still
answer escape (trace cells and lenient-eval sparks *do* escape the turn), it
blinds the M1/M2/M3 ledger and every instrument built on it, and it hides counts
rather than making them true. Retained as a fallback only under §7's entry
condition, which is stricter than "tranche B was hard".

**Gates before this binds** (§8): D0 pins the clause-side convention out of two
clause shapes' CLIF; D1 re-clears all five `macro_expansion_interior_alias_double_free`
pins under plain **and** M1+M2-armed lanes. A D1 failure re-attributes to
`/dev`(backend) with the trace as the brief — it does not fall back to arena.

Acceptance is unchanged: both `tests/macro_turn_marshal_leak_0889.rs` pins flip
to `0`, the record is re-derived, and the S118 instrument set re-runs
byte-identically across the churn.
