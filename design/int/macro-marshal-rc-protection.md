# Macro-clause marshal RC protection — the interior-alias double-free (S114 Track C, FIXME 0638)

> Subordinate topic doc, cited from `design/int/int.md` §6.2 (worker dispatch +
> `process_form`) and the CLAUDE.md macro-expansion section. Owned by
> `/design`(int). Authored S114 Phase 3 against SPRINT.md §Scope-C ("0638
> macro-alias double-free ×5 — MUST ship") and the `/arch` Phase-2 F-nothing
> constraint (root-cause design, not symptom patch).
>
> **Status: LANDED (S114); §2's MECHANISM SUPERSEDED (S119) — history retained.**
>
> As landed, the deep-protection mechanism is in source —
> `src/marshal.rs::protect_marshalled_cell` (`:204`) applied per marshalled cell
> (`:220`/`:234`/`:251`/`:264`; module rustdoc `:7`), curing the interior-alias
> double-free at the marshal boundary. §4's discriminating step was run before
> landing. Five pins in `tests/macro_expansion_interior_alias_double_free.rs` are
> the trigger + regression record. (Banner refreshed S115, FIXME 0699 item 4.)
>
> **S119 supersession (`design/int/macro-turn-ownership.md`, FIXME 0889).** The +1
> per cell accounts a retention the marshaller does not actually hold: after
> `invoke_clause` returns, no Rust frame, structure, or session store holds any
> marshalled word. That untrue count IS the 1,143-allocation compile-time leak
> (the argument term of 0889's closed form). The successor ruling **deletes**
> `protect_marshalled_cell` and its four call sites (Rule 2) and makes the count
> true by removing the retention instead of counting it: the marshaller produces
> a **single-owner** tree and **transfers** it by crossing the C ABI (Rules 1/3).
>
> Read §2 as the record of why top-only protection was wrong and of what a
> well-formed input to the clause looks like — **not** as current mechanism. Two
> parts of this document remain load-bearing and are cited by the successor:
> §0/§1's actor analysis, and §2's negative-control-twin argument (a tree at
> RC = 1 per cell, transferred consuming, runs clean — which is precisely the
> state Rule 2 restores; it is the twin, not the +1, that the successor rests on).
> §3's third bullet ("stop leaking / free the marshalled tree after expansion") is
> **retracted**: it rejected a *retain-and-release* shape, and the successor does
> not release — it never retains. §5's three `RC == 2` unit rows retire with the
> mechanism; their replacements assert `RC == 1` under the same completeness
> obligation.

## 0. The actors and the function between them (Principle 21)

Three actors meet at the macro-clause invocation boundary (`src/expander.rs`
`invoke_clause` + `src/marshal.rs`):

1. **The marshaller** (`src/marshal.rs`) — builds a runtime Sexp ADT heap tree
   from the compiler `Sexp` argument, and **retains that tree for the life of the
   session** (it is *leaked* — `//!` header: "their RC is never decremented").
2. **The JIT-compiled macro clause** — receives the arg tree as an `(SList Sexp)`
   under the **consuming calling convention** (callee owns heap params; its
   parameter drop glue recursively decrements the whole args tree at clause exit),
   runs ordinary compiled RC codegen internally, and returns a result Sexp tree.
3. **The unmarshaller** (`marshal::runtime_to_sexp`) — *reads* the result tree
   into a fresh Rust `Sexp` (it never dec/frees a runtime cell).

The one function that must hold between actors 1 and 2 is the **RC contract**:
*every runtime cell the marshaller retains must survive the clause's consuming
teardown and any interior consumption inside the clause.* The defect is that this
function is only **shallowly** satisfied.

## 1. The defect — shallow protection over a deep, aliasing tree

`invoke_clause` (`src/expander.rs:466`) protects the marshalled args like this:

```rust
let marshalled: Vec<i64> = args.iter().map(marshal::sexp_to_runtime).collect();
for &val in &marshalled {
    marshal::rc_inc(val);           // <-- ONLY the top-level arg cell of each arg
}
let args_slist = marshal::build_runtime_slist(&marshalled);   // spine cells: RC=1
let result_i64 = invoke_jit_protected(clause.func_ptr, args_slist, span)?;
```

Every runtime cell is born at **RC = 1** (`alloc_with_rc`, `alloc.rs:187`). The
protect loop bumps **only the top-level cell of each argument** (e.g. the
`SexpList` cell of `dt`) to RC = 2. It leaves at RC = 1:

- the args-SList **spine** SCons cells (built by `build_runtime_slist`);
- every **interior** cell of the argument — the argument's own SList spine, each
  element cell, nested lists, and the `HeapString` cells for symbols/strings.

The rustdoc justification ("elements extracted from the args and stored in the
result would be freed during parameter cleanup") is the tell: the protection was
sized for the case where the clause extracts a **top-level** element and returns
it. It does **not** cover a clause that:

1. matches its argument **multiple times** (0638's `dt` is matched by
   `dt-head`, `dt-has-docstring`, `dt-body`, `dt-name`, `dt-constructors`),
   inc/dec-ing shared interior cells across several sites, **and**
2. returns / consumes a **deep interior alias** — `dt-body` returns `rest`, an
   interior tail SCons of `dt`; `smap` then folds over it (`sfold` consumes each
   SCons, allocating fresh cells over the interior structure).

The 0638 repro's helper logic is **memory-correct through a plain cross-module
function call** (the committed negative-control twin exits 3). The *only*
difference on the corrupting path is the marshaller's RC starting state: a
normally-constructed argument is a single-owner tree at RC = 1 throughout, passed
consuming (ownership genuinely transferred); the marshalled argument carries an
**untracked external reference** — the marshaller keeps the whole tree alive but
RC-counts only the top of each arg. Under multi-match + interior-alias
consumption inside the clause, an interior cell's inc/dec accounting reaches
**0 while the cell is still reachable** (from the retained arg tree and/or the
result); `sfold`'s allocation reuses the just-freed block (the RC trace's
"same-address alloc/free ping-pong"), and a later dec **double-frees** it —
symptom-polymorphic (`double free` / `SIGSEGV` / `match failed` under
`RC_TRACE`; garbage header tags).

## 2. The mechanism — deep protection makes the marshaller's RC honest

The marshaller **retains a reference to every cell in the tree** (it never frees
any of them). The correct RC state is therefore **RC ≥ 2 on every marshalled
cell** before the clause runs: one count for the marshaller's own retention, one
for the reference the consuming clause will drop. Today the code counts the
marshaller's retention on the top-level cell only; the fix is to count it on
**every** cell — i.e. **deep, recursive protection of the whole marshalled tree**
(argument interiors *and* the args-SList spine).

This is not raising a floor to hide an off-by-one; it is **correcting an
under-count** — the marshaller genuinely holds those references (Principle 26:
count the reference actually held; `safety-invariants.md` §2 trust-boundary
framing — the leak IS a retained reference and must be RC-visible). With every
marshalled cell at RC ≥ 2:

- the clause's parameter drop glue decrements each retained cell at most to
  RC ≥ 1 → **no marshalled cell is ever freed** by the teardown;
- any interior consumption inside the clause (`sfold` folding over an aliased
  interior list) decrements shared cells at most to RC ≥ 1 → **no premature
  free**, hence no reuse-ping-pong, hence no double-free;
- fresh cells the clause allocates itself (RC = 1) are freed normally — deep
  protection touches only marshalled cells, so the clause's own intermediates
  are unaffected;
- the result tree is either fresh (unaffected) or an interior marshalled alias
  (now RC ≥ 2 → survives to be *read* by `runtime_to_sexp`, then leaked with the
  rest of the tree — the already-accepted bounded-per-expansion leak model,
  `marshal.rs` `//!`).

The invariant becomes **structural**: *the marshal boundary protects the entire
tree it hands to a consuming callee, symmetric with the fact that it retains the
entire tree.* Shallow top-only protection is the bug precisely because retention
is deep while protection was not.

### Why +1 per cell is provably *sufficient*, not a hopeful floor

The negative-control twin (identical helper logic via a plain cross-module
function call, committed GREEN, exit 3) passes the argument at RC = 1 as a single
owner and transfers ownership consuming. It runs to completion with **no leak and
no double-free** — which means the clause's RC codegen is **net-balanced to
exactly one decrement per cell** (each cell reaches 0 once, freed once, the
caller having given up ownership). That balance holds for the *shared interior*
cells too (multi-matched, interior-aliased — the twin exercises them and still
exits clean).

The marshaller retains **exactly one** reference to each cell (it built the tree
and holds the root; every cell is reachable through that one retained root). So
the correct protection is **exactly +1 on each cell** — one count for the
retained reference the marshaller holds. After the clause's proven one-net-dec per
cell, every cell lands at RC ≥ 1 (the retained floor) and survives. The bug today
is that this +1 is applied only to the top-level cell; the interior +1s are
missing, so the clause's correct one-net-dec frees interiors to 0 while the
marshaller (and often the result) still points at them. Deep protection is the
*exact* correction the twin's balance guarantees — not a floor raised in hope.

### 2.1 Where the deep protection lives

Two equivalent shapes; the designer inclines to (a):

- **(a) protect-on-build (preferred).** `sexp_to_runtime` /
  `marshal_children_to_slist` / `build_runtime_slist` already visit every cell as
  they allocate the tree — protect there (allocate at RC = 2, or add one
  `rc_inc` per cell at its construction site). Single-pass, no second walk, and
  the protection is co-located with the allocation whose retention it accounts
  for (Principle 7 / P18: one place owns the layout and its RC). `invoke_clause`
  then drops its bespoke top-level protect loop.
- **(b) protect-by-post-walk.** Keep construction as-is and add a
  `marshal::deep_protect(root)` that recursively increments every reachable cell
  (SList spine SCons, `SexpList`/`SexpBracket` payload spines, element cells,
  `HeapString` cells), invoked in `invoke_clause` over each marshalled arg and
  over `args_slist`. Simpler diff; requires the walker to know the full runtime
  layout (tag-dispatched, mirroring `read_slist_to_vec`/`runtime_to_sexp`).

Either way the **completeness obligation** (0660 discipline) applies: the deep
protection must reach **every runtime cell kind the marshaller can allocate** —
`SexpInt`/`Float`/`Bool` (leaf, one cell), `SexpStr`/`SexpSym` (cell + its
`HeapString`), `SexpList`/`SexpBracket` (cell + SList spine + each element,
recursively), and the args-SList spine. The change-set names every cell kind or a
legal skip (a bare nullary tag `< NULLARY_TAG_THRESHOLD` — e.g. `SNil` — is not a
heap pointer and is correctly skipped by `rc_inc`'s existing guard).

## 3. Why not the alternatives

- **Deep-copy the result out after invocation** — too late: the consuming
  teardown and the interior free happen *inside* the JIT clause, before
  `invoke_clause` regains control. A post-call copy cannot un-free a cell.
- **Deep-copy the argument tree** — the argument is *already* a fresh, fully
  disjoint deep copy (nothing external aliases it). The corrupting aliasing is
  created *inside* the clause between the arg and the result; copying the arg
  again changes nothing.
- **Stop leaking / free the marshalled tree after expansion** — a larger change
  (introduces a free path with its own aliasing hazards against the retained
  result) and orthogonal to the double-free. The leak model is accepted
  (`marshal.rs` `//!`); deep protection keeps it and only makes the count honest.

## 4. The discriminating step `/dev` runs FIRST (à la the RC_TRACE discriminators)

The pins are symptom-polymorphic, so `/dev` confirms mechanism **before** landing,
in this order, serial (`--test-threads=1` for any `RC_TRACE` read):

- **D1 — locate the premature free.** Run the `--run` pin under
  `CRANELISP_RC_TRACE=1` and (for the deterministic face) `CRANELISP_QUARANTINE_FREED=1`
  (exit 134 "double free" at the faulting op). Identify the **first marshalled
  interior cell that reaches RC = 0 and is freed while still reachable** from the
  retained arg tree or the pending result. This pins the exact cell + the
  inc/dec site whose accounting is short. Expected: an interior SCons of `dt`
  (the `rest`/`body`/`items` tail), freed inside the `smap`→`sfold` consumption.
- **D2 — apply deep protection, re-run all five pins.** With every marshalled
  cell at RC ≥ 2:
  - **all five green** ⇒ mechanism confirmed and the fix is *sufficient*; land
    §2 with the §5 unit tests. The negative-control twin (identical helper logic
    via a plain function call, already GREEN) is the proof deep-protect is a
    correction, not a mask: the clause codegen is correct for a well-formed RC
    input, and deep protection *gives* it a well-formed input (every input cell
    externally owned, exactly as a normal caller's transferred tree is not — but
    now every input cell survives its single consuming dec).
  - **still RED under deep protection** ⇒ the imbalance is inside the clause's
    own RC codegen, independent of the marshaller floor. Re-attribute to
    `/dev`(backend) with the **D1 trace as the cross-crate handoff brief** (root
    CLAUDE.md minimal-repro requirement); the function-call twin is the negative
    control that localizes it. This branch is judged **unlikely** (the twin
    passes), but naming it keeps the attribution honest and avoids a
    false-green from perturbation (`feedback_verify_fix_not_symptom_absence`).

## 5. Testability (Principle 5) — the mandatory unit tier

Deep protection is unit-testable at the marshal seam with no session:

- **`deep_protect_survives_consuming_teardown`** — marshal a nested arg
  (`(SexpList [a (SexpList [b c]) d])` shape), apply the deep protection, then
  simulate one consuming dec of the whole tree (the drop-glue teardown a clause
  performs) and assert **every** interior cell's RC is still ≥ 1 (fail-on-revert:
  with the old top-only protection an interior cell reaches 0). This pins the
  boundary at the exact seam the bug lived, independent of the JIT.
- **completeness cell** — one arg of each cell kind (Int/Str/Sym/List/Bracket
  nested) round-trips through marshal → deep-protect → a simulated consuming
  teardown → unmarshal, asserting structural equality (the existing
  `roundtrip_*` tests extend with the protection applied).

The five e2e pins (`tests/macro_expansion_interior_alias_double_free.rs`, both
mode-faces) are `/qa`+`/testing`'s acceptance; both faces MUST green in the one
change-set (the §2.2 R-1 rule — a partial fix greening one face is caught by the
other; SPRINT.md Track-C §4.1).

## 6. Principles cited

- **Principle 21** — actors + the function between them named before the
  mechanism (§0).
- **Principle 26** — protect by counting the reference the marshaller actually
  holds, not by a floor heuristic (`safety-invariants.md` §2: the leak is a
  retained reference the RC must reflect).
- **Principle 18 / Principle 7** — the deep protection is single-sourced with the
  allocation whose retention it accounts for (§2.1(a)); the completeness
  obligation names every cell kind (§2.1) so no variant grows an unprotected slot.
- **Principle 5** — the seam is a pure marshal-level transform, unit-testable
  without a JIT session (§5).

## 7. Cross-references

- `src/marshal.rs` — the marshaller (`sexp_to_runtime`, `build_runtime_slist`,
  `rc_inc`); §2.1(a) protects here.
- `src/expander.rs:466` (`invoke_clause`) — the top-only protect loop §1 quotes;
  §2.1(b) would protect here.
- `crates/cranelisp-intrinsics/src/alloc.rs:168/:222` — `alloc_with_rc` (RC init
  = 1) + the `dealloc` double-free assert the pins trip.
- `tests/macro_expansion_interior_alias_double_free.rs` — the five pins (record +
  trigger; both mode-faces).
- `tests/plan/memory-safety-coverage.md` (macro-expansion marshalling row) +
  `tests/plan/s114-test-plan.md` §4.1 — the coverage frame + acceptance.
- `design/arch/safety-invariants.md` §2 — the trust-boundary assertion tier the
  "leak is a counted reference" argument rests on.
