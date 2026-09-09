# Ownership inference — the typecheck-crate proposal (parts 6–11)

**Status:** DESIGN (S100 Phase 3, stage 2) — the per-crate inference proposal for the
interprocedural ownership-inference analysis. Authored by `/design` narrow-deployed on
`cranelisp-typecheck`, against the S100 sprint scope (`sprints/SPRINT.md` parts 6–11).
**S102 Phase 3 addendum: §13 is the implementation-ready change-set staging for
increment I's typecheck half (Sprint 102 Block B2)** — ordered change-sets, the
types-crate dependency pin, the graph-feed verification against the S101 `callees`
widening (0470/0472), the fact-table coverage verdict, the toggle-off semantics pin,
and the Principle-23 scenario space (the 0497 rider). §§0–12 stand unchanged except
where §13.6 records refinements the implementation problem forces.
**S103 Phase 3 addendum: §14 is the implementation-ready change-set staging for
increment II's typecheck half (Sprint 103 Block B1)** — the typecheck-drain quartet
disposition (0509/0511/0513; 0510 coordinated), the write-path query emission
(static-uniqueness subset + `result_unique` chaining + `unique_static` site facts,
the uniqueness stratum, cap-reset), the dynamic rc==1 handoff to the backend, the
R5 `value_layout` coordination, and — the trigger check /arch is waiting on — the
**FIXME 0521 verdict (NO; deferred)**. §7 (the S100 write-path ruling) is unchanged;
§14 makes it implementation-ready.
**Governing authority:** `design/arch/ownership-inference.md` (the S100 master spine, as amended
2026-07-02). Where this proposal and the spine disagree, **the spine governs**; this proposal
resolves the spine's §10 typecheck items 1–6 and elaborates within the spine's lattice
(§2), contract (§3), and sequencing (§4) rulings. Pre-implementation; no source, no
`cranelisp-types` edit, no `public-api.txt` movement lands in S100.
**Peers:** `design/backend/ownership-codegen.md` (parts 12–16 — not yet authored; §8.4 and §12
of this doc name its inputs) and the `/qa` verification plan (parts 17–18).
**Subordinate to:** `design/typecheck/typecheck.md` (the crate master doc; §9/§10 there index
this doc). Grounding docs: `design/typecheck/monomorphisation.md` (the mono spine this pass
rides), `design/backend/ring2-rc.md` §3/§5.5 (Decision 24, `borrowed_vars`, spark-capture
borrow), `design/backend/lenient-eval.md` (spark placement is codegen-internal — §5.2 here).

---

## §0. Scope and the increment frame

This doc designs the **inference pass**: one interprocedural lifetime/flow analysis computed in
`cranelisp-typecheck`, post-monomorphisation, over the mono call graph, emitting the spine's
five query outputs. It answers the spine's §10 items 1–6:

| Spine item | Where answered | Ruling in one line |
|---|---|---|
| 1. Summary/fixpoint representation + cost budget | §2, §3 | Dense per-callable `OwnershipSummary`; post-pass worklist fixpoint per cluster riding `Def.callees` + `resolved_call`; one extra annotation-only body walk per visit; interactive budget bounded by the §5.4 cone + the summary-diff gate |
| 2. Borrow-through-projection | §4 | Provenance-rooted borrows; transitive by provenance composition; escape ⇒ materialize (inc at the escape edge, never at the projection); interprocedural via a **result mode** on the summary (FIXME 0467) |
| 3. Per-cell confinement join + `Transferred` | §5 | Op-wise join over surviving RC-op sites classified by strand context, with **potential-fork over-approximation**; `Transferred` carried in the internal lattice, **collapsed to `Crossing` at emission for increment I** (promotion is measurement-gated) |
| 4. Instantiation summary dedup | §6 | Keyed by the existing mangled name; session memo on the checker env; deterministic re-inference makes cross-module duplicates benign; persisted on the mono entry like every other payload |
| 5. Write-path three mechanisms + static-uniqueness subset | §7 | (a) one-body + dynamic rc==1 is the increment-II default; (b) static proving scoped to the **single-syntactic-use fresh-chain subset**, success metric = proof chaining; (c) adopted only as (a)-with-hoisted-check; mode stays out of the mono key pending increment-II measurement |
| 6. HOF/closure-conversion under R2 | §8 | **Moded native body + Decision-24 value wrapper** (the primitives' dual-path precedent); join-to-Owned rejected (non-local performance + R3 amplification); coordination interface for backend part 12 stated |

Plus the typecheck side of the spine's **§3.1(a) hand-declared primitive fact table** (§9).

**Increment staging (binding, spine §7).** Increment I ships **Q1 + Q2 + Q3 + the fact table**
only: `Borrowed`/`Owned` param vectors on statically-resolved calls, escape site facts,
confinement site facts, borrow-through-projection, declared primitive leaves. Increment II adds
Q4 (uniqueness/reuse) and Q5's classification consumer (R5 flattening is backend part 12/16).
**Nothing in this design places reuse tokens or any increment-II plumbing on the call ABI**
(spine §3.5) — the increment-II sections below (§7, the `result_unique` bit in §2.2) are
designed-now/emitted-later, and their carriers are advisory-class or summary-internal. Every
section below is tagged I or II where the distinction bites.

---

## §1. Actors and functions first (Principle 21)

Before mechanism, the actors this pass sits among and the functions between them — all real
seams in today's source:

**The actors:**

- **The mono spine** (`traits/monomorphise.rs`) — mints concrete instances at use sites:
  `pass4_monomorphise` (`program.rs:3132`) → `monomorphise_call` (P0–P7) →
  `monomorphise_inner_parametric_hops` (the multi-hop recursion) → `register_mono_entry`
  (the single registration seam; builds the `ModuleEntry::Def` with
  `UserFnState::Concrete { got_slot }` + `codegen_view`). Every instance passes through
  `finalize_mono_codegen_view` → `MonoExpr::from_expr` — so **every codegen-bound body the
  analysis walks is a `MonoDefnVariant` whose nodes are concretely typed by construction**
  (Principle 18/20; `mono_expr.rs`). The analysis never sees a `Type::Var`.
- **The finalisation pass** (`program/finalize.rs::finalize_check_result_inner`) — the post-pass
  sequence the analysis joins: Pass-4 mono runs before
  `program/finalize.rs::finalize_annotations_and_publish`, which consumes each checked ledger
  record and publishes its final canonical callees with its AST (Decision 21). The ownership fixpoint slots
  **after both** — at that point the cluster's callable set, call edges, and concrete bodies
  are all settled.
- **The cluster orchestration** (Decision 44; `cluster.rs::SymbolTableAccess`) — the pass reads
  and writes through the same staging-vs-live choke point every other typecheck write uses
  (`current_symbol_table`/`current_symbol_table_mut`); in cluster mode its summary writes land
  in the orchestrator-handed staging table and commit atomically with the cluster (Principle 17
  module locality — the pass is per-cluster, imported summaries are boundary conditions read by
  the ordinary per-symbol chain-follow, `resolve_terminal_entry_and_home`).
- **The call-graph carrier** (`cranelisp-types::module.rs`) — forward edges already persisted:
  `ModuleEntry::Def.callees: Vec<FQSymbol>` (`module.rs:725`, serde-visible). Per-node
  resolution rides `MonoExpr::Apply.resolved_call` / `MonoExpr::Var.resolved_call`
  (`ResolvedCall::{TraitMethod, SigDispatch, AutoCurry, BuiltinFn}`, `check.rs:106`). The
  ownership fixpoint walks these same edges the R3 reverse index derives from — one graph, two
  consumers (spine §5.3).
- **The leaf table** (`cranelisp-primitives`' static `SymbolTable`, Decision 48) — declared
  per-primitive facts seed the fixpoint (§9); the `ring2-rc.md` §3.3 extern audit is the seed
  content.
- **The consumers** — the backend (site facts on `MonoExpr` nodes + the summary on the entry;
  advisory vs ABI-bearing per spine §3), the cache (`.meta.json` — the summary is ordinary
  serde-visible entry payload, spine §5.1), and the R3 redefinition transaction (the
  summary-diff gate reads the ABI surface this pass produces, spine §5.4 step 2).

**The functions between them:** bodies + declared leaves + imported summaries → *(fixpoint)* →
per-callable `OwnershipSummary` (§2) + per-site facts (§2.3) → entries/`MonoExpr` → backend
mechanisms / cache / R3 gate. The pass adds **no new graph, no new store, no new pipeline
stage** — it is a post-pass over structures that exist (Principle 7).

---

## §2. The summary and the site facts (parts 6 + 7 groundwork)

### 2.1 The static-call classifier (R2, applied to the real node taxonomy)

Per-param modes attach only to statically-resolved calls (spine R2). On the as-built
`MonoExpr`, "statically resolved" is decided per `Apply` node:

| `Apply` shape | Classification | Why |
|---|---|---|
| callee `Var`, `resolved_call = Some(SigDispatch)` | **static** (moded) | mangled mono/multi-sig target, direct |
| callee `Var`, `resolved_call = Some(TraitMethod)` | **static** (moded) | post-mono trait dispatch is a named impl |
| callee `Var`, `resolved_call = Some(BuiltinFn)` | **declared leaf** | inline lowering; facts come from the §9 table, not a summary |
| callee `Var`, `resolved_call = None`, name chain-resolves to a callable `DefKind` (`UserFn`-`Concrete` / `Primitive` / `Constructor` / `PlatformEffect`) | **static** for `UserFn`; **pinned boundary** for the rest | `callable_got_slot()` (`module.rs:1303`) is the discriminator; constructors/externs/platform stay Decision-24-pinned per spine §3.1 |
| callee `Var` resolving to a `let`/param binding (a closure value), or callee non-`Var` (computed) | **Decision-24** | closure-valued call site; no modes on arrow types |
| `resolved_call = Some(AutoCurry)` | **Decision-24** | the partial application is a closure value by construction |

`Lambda` bodies are analysed like any function body (they produce internal summaries used for
the sites where the lambda is *directly* applied or sparked); a lambda that flows as a value is
a closure — its entry stays Decision-24 (§8 covers named functions that need both).

### 2.2 `OwnershipSummary` — the internal representation

One summary per **callable instance** (concrete `UserFn` incl. mono instances, accessor `Def`s,
declared primitives). Dense, positional, small:

```rust
// cranelisp-typecheck internal (not a boundary type in S100)
struct OwnershipSummary {
    /// ABI-bearing half (spine §3.1): what the compiled body's convention IS.
    param_modes: Vec<Mode>,          // Copy | Borrowed | Owned  — per param
    result: ResultMode,              //  ← ABI-bearing; see FIXME 0467
    /// Advisory/analysis half — inputs to CALLERS' site classification:
    param_flow: Vec<ParamFlow>,      // per param, for Owned params
    spark_ops: BitVec,               // per param: may the callee run RC ops on it
                                     // off the calling strand? (§5.3)
    result_unique: bool,             // increment II only (§7.2); false in I
}

enum ResultMode {
    Fresh,                // owned rc=1 temporary (Decision-24 as-built)
    ProjectionOf(usize),  // borrowed view rooted in param i (accessors — §4.4).
                          // UNCONDITIONAL: reserved for a provable borrowed view
                          // (`vec-get`, a bare field accessor).
    AliasOf(usize),       // param i returned as-is, ownership flows through —
                          // UNCONDITIONAL (`string-identity`).
    MayAliasOf(usize),    // S111 §15/§3.7-spine: the result is EITHER a fresh
                          // materialization OR param i's own reference, decided
                          // dynamically (the COW shape — `vec-set`/`vec-push`).
                          // The consumer MUST keep protect and must never assume
                          // it IS the param. Absent this point, the COW truth had
                          // no representation and was falsely declared `Fresh`.
}

enum ParamFlow {          // where an Owned param's reference goes
    Consumed,             // dec'd inside; lifetime ends in the call (str-concat)
    IntoResult,           // stored into / embedded in the returned value (Some x)
    Retained,             // stored beyond the call's extent (runtime-owned store,
                          // suspension capture) — an escape edge for the caller
}
```

Justification per field: `param_modes` + `result` are the spine's ABI vector (with the result
extension argued in §4.4 and filed as **FIXME 0467** — the spine's §3.3 sketch is explicitly
illustrative, and its narrowness counterweight routes every proposed boundary field through an
`/arch` FIXME). `param_flow` is what makes **Q2 interprocedural**: `Owned` alone tells a caller
nothing about escape — `(defn keep [x] (Some x))` has `x: Owned/IntoResult` (the arg escapes
exactly as far as the result does), while `(str-len s)` has `s: Owned/Consumed` (no escape edge
at all; spine §2.2 rule 5 stops firing at summarised leaves). `spark_ops` is what makes **Q3
interprocedural** (spine §2.3: "does this callee spark over its param, and does the spark side
hold RC ops on it?" rides the summary). Everything else the backend can derive in-function
stays out (Principle 2; the spine's narrowness counterweight) — no last-use, no site lists, no
per-node data in the summary.

The **absent summary is ⊤**: all-`Owned`, `result: Fresh`, all-flow-`Retained`, all
`spark_ops` set — byte-for-byte Decision 24 + conservative escape/confinement. Old caches,
unresolved edges, HOF targets are all at this point by construction (spine §2.1).

**Copy-ness classification (sprint part 6).** `Copy` is a per-concrete-type structural
predicate: `Copy(T)` ⟺ T is a scalar (`Int`/`Bool`/`Float`) or an ADT/Vec all of whose field
element types are transitively `Copy` **and** whose representation is a value. Until R5
value-flattening lands (spine §6.3, backend part 12/16), the representation clause fails for
every heap type, so **the increment-I classifier is exactly `ConcreteType::{Int,Bool,Float}`**
— stated so the `Copy` lattice point is never load-bearing-but-mechanismless. The classifier is
a memoized function over `ConcreteType` (post-mono ⇒ total; no `Type::Var` can reach it),
implemented next to `HeapCategory`'s typecheck-side type walks and shared with the backend via
the site facts, never recomputed there from scratch for mode purposes. When R5 lands, the
predicate gains the size-bound + all-fields-Copy recursion and the classification becomes an
input to layout — deterministic, hence cache-key-safe (spine §6.3's parity requirement).

### 2.3 Site facts (advisory, spine §3.2)

Per allocation / capture / binding / projection site, the pass computes and (at the
implementing sprint, via the `/arch`-landed §3.3 fields) attaches to `MonoExpr` nodes:

- `escapes: Option<bool>` — §2.2-spine escape edges, with rule-5 refined through `ParamFlow`.
- `confined: Option<bool>` — the §5 join's per-cell verdict projected onto the cell's sites.
- `unique_static: Option<bool>` — increment II (§7.2); never emitted in I.
- **provenance** (new, advisory; part of FIXME 0467's designed shape): for a borrowed
  projection, the root binding it is a view into (§4.2) — the one fact the backend cannot
  derive locally when the projection crossed a call (accessor shape, §4.4).

`None` ⇒ conservative on every axis. A backend ignoring any/all of these is correct
(monotone-soundness, spine §2.1).

---

## §3. The fixpoint (spine §10 item 1)

### 3.1 Placement — a post-pass on the existing finalisation seam

The pass runs inside `finalize_check_result_inner`, **after** `pass4_monomorphise` (`:1901`)
and the callee write-back (`:1999`), as `pass5_ownership` (name illustrative). At that point:
every callable the cluster defines has its `codegen_view` populated (mono instances via
`register_mono_entry`; ordinary concrete defns via `build_concrete_codegen_view`); every
`Def.callees` edge is written; imported callees resolve by chain-follow. No pipeline
re-sequencing (spine §4.1). Writes go through `current_symbol_table_mut` exactly as
`program/finalize.rs::finalize_annotations_and_publish` does — staging-aware,
cluster-atomic, no new mutation path
(Decision 44; Principle 17).

Instantiation minting is recursive (`monomorphise_inner_parametric_hops` mints inner hops
during P4 re-checks), so instances minted mid-P4 are already registered by the time pass5
runs — the pass sees the complete instance set of the cluster. Summaries for instances are
*computed* in pass5 with everything else (not inside `monomorphise_call`), keeping the mono
spine untouched and the analysis in one place; §6 covers the memo that makes repeated mints
free.

### 3.2 The per-cluster worklist

- **Universe:** the cluster's codegen-bound callables (the `defined_symbols()` predicate +
  `codegen_view.is_some()`), plus declared leaves (primitives — constants, never on the
  worklist) and imported summaries (boundary conditions — read once, never on the worklist).
- **Init (optimistic):** every param `Borrowed` (or `Copy` by type), `result` provisionally
  `ProjectionOf`/`Fresh` per the body's return shape, `param_flow` all `Consumed`, `spark_ops`
  clear.
- **Transfer function:** one walk of the callable's `MonoExpr` body (§3.3), producing (i) a
  possibly-widened own summary and (ii) the site facts. Widening only (joins move toward
  `Owned`/`Escapes`/`Crossing`); the lattice per param has height 2, escape/flow ≤ 2,
  confinement ≤ 2 — the whole summary's descent chain is O(params).
- **Worklist discipline:** seeded with all cluster members in reverse-topological order over
  `callees` (callees first — most summaries converge in one visit); when a member's summary
  changes, its **intra-cluster callers** re-enter the list. Caller lookup inverts the cluster's
  `callees` edges — a cluster-local, throwaway index (the session-lifetime reverse index is the
  R3 subsystem's, `/int`-owned; this pass does not build or own it, it merely walks the same
  forward edges — spine §5.3 "one graph, two consumers").
- **Termination:** the mode, escape/flow and spark axes are finite lattices under a monotone
  transfer, so on those axes each callable re-visits at most O(Σ per-param heights) times; in
  practice ≤ 2–3 visits for recursive clusters, 1 otherwise. **The result axis is not covered by
  that argument, and the visit cap is a live backstop rather than a defensive-unreachable one**
  — the seed `Fresh` is a claim about the result, not the axis's ⊥, so the iteration is an
  optimistic-init fixpoint and not a Kleene ascent. §19 gives the axis a real ⊤ and a truthful
  join, which removes the measured non-convergent class; §19.5 is what makes reaching the cap
  safe. Section §19.8 states the residual precisely.
- **Stratification:** modes/escape/flow converge **first**; the confinement join (§5) runs
  **second**, over the surviving-RC-op set the converged modes determine. Confinement never
  feeds back into modes (nothing in the mode transfer reads confinement), so the
  stratification is exact, not an approximation.

### 3.3 The transfer function — what one body walk computes

A single pre-order walk of the `MonoDefnVariant.body`, tracking per-binding abstract state
(mode + provenance root). Node cases, on the real variants (`mono_expr.rs`):

- `Var` (use): a use of a param/binding. In callee-arg position, classified by §2.1 + the
  callee summary's param mode/flow; a `Borrowed` handoff to a summarised callee is a **non-edge**
  (spine §2.2); an `Owned` handoff joins the arg's mode to `Owned` and applies the callee's
  `ParamFlow` to the escape classification. Value-position use of a callable name = a
  value-use mark for §8.
- `Apply`: per §2.1. For static calls, propagate through the callee summary; result provenance
  from `ResultMode`. For Decision-24 sites (closure calls), every heap arg joins
  `Owned`+`Retained` (rule 5).
- `Let` / `Match` scrutinee + arm bindings / `VecLit` / `ConstrADT` fields: binding
  introduction, projection (§4), or store escape edges (constructor field-store = `Owned`,
  spine §3.1 boundary pin; storing into an escaping aggregate escapes the stored value).
- `Lambda`: capture set = free vars; captures of an escaping closure escape (rule 3); the
  closure value itself is an allocation site.
- `ParBind` / `LaunchContinue` / potential-spark subtrees: fork/suspension classification for
  §5; `LaunchContinue.launched` and trampoline-deferred continuations are suspension **escape**
  edges (spine R6 — classification, never borrow-widening).
- `If` / `Trace` / literals: structural recursion.
- Return position: the returned value's provenance decides `ResultMode`; returning a projection
  of param i yields `ProjectionOf(i)` (§4.4); returning param i itself yields `AliasOf(i)`;
  anything else `Fresh`. Returning a borrowed projection of a **local** (not a param) is an
  escape of the local's root — the root materializes (§4.3), result is `Fresh`.

Cost per visit: **one linear walk, no unification, no substitution, no allocation beyond the
per-binding state map and the site-fact writes**. Compare: the same body has already been
walked several times this compile (annotation, `apply_subst_to_defn`, `from_expr`), each doing
strictly more work per node (type traffic). The pass adds well under one `recheck_body_for_mono`
of cost per callable.

### 3.4 The cost budget — batch and interactive (the §5.4 shared budget)

**Batch:** O(cluster nodes × avg revisits) ≈ 1–3 linear body walks per callable per compile,
amortised against a pipeline that already does ≥ 4 (check, annotate, subst, `from_expr`).
Budget pin: **the pass must stay an annotation-only walk — no subst application, no scheme
instantiation, no `Type` traffic** (`ConcreteType` reads only). Any design change that would
make the transfer function unify or instantiate has left the budget and needs a fresh ruling.

**Interactive (the binding half — spine §5.4 shares this budget):** the R3 slow path re-runs
the fixpoint **incrementally from the edit**: worklist seeded with the redefined symbol only;
its cluster fixpoint re-converges; the **summary-diff gate** (type scheme + `param_modes` +
`result` — the ABI surface of §2.2) decides whether anything else runs. What keeps a REPL turn
responsive, in order of leverage:

1. **The summary-diff gate** — body-only edits (the overwhelming majority) cost one transfer
   walk beyond today's recompile: the summary is recomputed, compares equal, done.
2. **Cone-bounding** — an ABI-changing edit costs the true dependency cone (spine §5.4 sizing
   honesty), with the ownership re-inference adding ≤ one walk per cone member per fixpoint
   round on top of the re-typecheck/recompile that dominates the turn.
3. **Optimistic re-init from prior summaries** — re-inference of an edited symbol starts from
   its callees' *current* (already-converged) summaries, not from scratch; ping-ponging is
   structurally impossible (monotone within a run; each run is fresh-init per edited body).
4. **The instantiation memo (§6)** — unchanged instantiations reached from the cone are
   summary-cache hits, not re-inferences.

No wall-clock number is pinned pre-implementation; the *structural* budget is pinned: the
ownership addition to a REPL turn is O(cone size) linear walks, and the cone is the same set R3
must re-typecheck anyway — the analysis never enlarges the affected set, it only rides it.
`/qa`'s part-17 plan should carry a turn-latency lane on the F1 fixture's REPL path to hold
this (routed in §12).

---

## §4. Borrow-through-projection — the precise rule (spine §10 item 2, §4.4)

### 4.1 The projection sites

On the as-built AST, a projection is one of: a **match-arm constructor-field binding**
(`MonoMatchArm` pattern binding — today's `borrowed_vars`, ring2-rc §5.5), a **field-accessor
call** (`Type.field` canonical accessor `Def`s — `fixme-0365-field-accessor-dotted.md`; these
are ordinary compiled functions, hence §4.4), and a **vec element read** (`vec-get` — inline
lowering, declared facts §9). There is no dedicated projection node; the rule attaches to these
three shapes.

### 4.2 The composition rule

Every borrowed value carries a **provenance root** — the owning binding whose reference covers
it. The rule, in full:

1. **Projection out of `Borrowed`:** `proj(x)` where `x` is `Borrowed` with root `r` yields
   `Borrowed` with root `r` (**not** root `x`). Provenance composes through the *root*, so
   chained projections (`(vec-get (gcells g) i)`) collapse to one root (`g`) — this is what
   "composes transitively" means mechanically: the chain is flattened at analysis time, and the
   soundness obligation is always against the single root's extent.
2. **Projection out of `Owned`:** `proj(x)` where `x` is an `Owned` local yields `Borrowed`
   with root `x`. Sound while `x` is live; the interaction with last-use is rule 4.
3. **No RC ops at projection:** a borrowed projection emits no inc at extraction and no dec at
   release — the root's single owning reference is the entire accounting (the §5.5
   `borrowed_vars` discipline, generalised from "match scrutinee field" to every projection).
4. **Last-use interaction (the seam with the backend):** a borrowed projection is **never
   eligible for last-use ownership transfer** (it owns nothing — the existing §5.5 gate), and —
   the new obligation rule 2 creates — **every use of a borrowed projection is a use of its
   root** for the backend's `compute_last_uses`: the root's last use (hence its release, or its
   COW mutate-in-place eligibility) must order **after** the last use of every projection rooted
   in it. Typecheck emits the provenance fact (§2.3); the backend extends its existing
   intra-function last-use walk to count provenance-rooted uses against the root. The analysis
   split honours the spine's narrowness counterweight: interprocedural provenance above the
   boundary, all ordering/emission decisions below it. (Without this rule, rule 2 recreates the
   Sprint-61 aliased-COW regression one level up: root reaches `is_last_use + rc==1` while a
   projected borrow is still live, mutates in place, corrupts the view.)
5. **Escape ⇒ materialize:** a borrowed projection that reaches an escape edge (returned,
   stored into an escaping value, captured by an escaping closure, crosses a suspension) does
   **not** widen the root or the projection chain — it **materializes at the edge**: one
   `rc_inc` emitted at the escape site converts the borrowed view into an owned reference, and
   from there ordinary Decision-24 accounting applies. This is the load-bearing asymmetry: the
   read path stays rc-free; only genuine escapes pay, exactly once, exactly where they escape.
   (This inc is the same *adaptation* shape as the spine's §4.3 caller-side adaptation and the
   §3.1(a) extern-site inc — one idiom, three sites.)

### 4.3 The lifetime-nesting proof

Obligation: a borrowed projection is never read after its root's owning reference is released.
Discharge, by cases over where the borrow can flow under rules 1–5:

- **Within the root's frame:** the root is a param or local of the same frame; rule 4 orders
  the root's release (scope-cleanup dec / last-use transfer / COW reuse) after every
  provenance-rooted use. Frame-local reads are therefore covered by the root's live reference.
- **Into a synchronous static call (as a `Borrowed` arg):** the callee's dynamic extent nests
  inside the caller's frame extent (synchronous call), and the caller's root reference is live
  across the call — the same structural argument as `borrowed_vars` and spark-capture borrow
  (ring2-rc §5.5.2.3). Transitivity through the callee: the callee sees a `Borrowed` param
  (root = its param), and its own projections chain to that param; the callee's frame extent
  nests in the caller's, so the nesting composes inductively down any static call chain.
- **Into a joined spark:** the join is within the capturing frame's dynamic extent (structured
  fork-join, spec §12.4.3); the root outlives the spark by the §5.5.2.1 structural-join gate.
- **Across any escape edge:** impossible by rule 5 — the borrow was materialized at the edge;
  what crossed is an owned reference.

Every case reduces to "the borrow's extent nests inside the root's owning reference's extent",
and rule 1's root-flattening means there is exactly one such obligation per chain, not one per
link. ∎

### 4.4 Interprocedural projection — the result mode (and FIXME 0467)

The S99 read shape is `(vec-get (gcells g) 0)` — and `gcells` is a **compiled accessor
function**, not a syntactic projection. For the read path to be rc-free through it, the
accessor's summary must say *"my result is a borrowed view rooted in param 0"* —
`param_modes[0] = Borrowed`, `result = ProjectionOf(0)` — and the caller must root the call's
result at its own arg's root (rule 1 across the call). A **borrowed result is ABI-bearing**: a
caller compiled against `Fresh` decs the result as a temporary (double-free against the still-
owned field); a caller compiled against `ProjectionOf` emits no dec (leak if the callee
actually returned fresh). It therefore rides the summary's ABI half, participates in the R3
summary-diff gate, and — like the param vector — is Decision-24-defaulted when absent
(`Fresh`). The spine's §3.3 `ModeSummary` sketch carries `param_modes` only; the extension
(result mode + the advisory `param_flow`/`spark_ops` analysis facts, §2.2) is proposed as
**FIXME 0467** (`target: /arch`) for the implementing sprint's §3.3 pass — this proposal is
designed against it, and degrades cleanly without it (accessors fall back to Decision-24
`Fresh`: correct, two RC ops per projection, the S99 read-path win shrinks to intra-function
and `vec-get`-direct shapes).

**Subsumption check (spine §8.2):** with rules 1–5, `borrowed_vars` is rule 2 + rule 3 at the
match-arm site; spark-capture borrow is rule 3 at the joined-spark capture site with the §4.3
join-extent case; the vec-op temporary-vs-borrowed-field hazard (ring2-rc §3.3 "Vec-op caller
handling") is rule 4's ordering discharged rc-checked at runtime today and statically here. The
three ad-hoc instances are reproduced as inferred cases, none widened.

---

## §5. Confinement — the per-cell op-wise join (spine §10 item 3, §2.3)

### 5.1 What a "cell" is, and which sites join

A **cell** is an allocation site's value together with everything provenance-rooted in it
(§4.2) — the unit that shares one refcount word... more precisely, the join is computed per
allocation site, and projections contribute their ops to the *root's* cell (a projected field
is its own heap cell with its own count word; its *extraction* ops were already elided by §4,
and its *retained-elsewhere* ops belong to the site where it was materialized — rule 5 — which
is itself classified). The facts that join, for a given cell, are **the RC-op sites that
survive the converged mode/escape assignment**: consuming incs at Decision-24/adaptation
sites, scope-cleanup decs, capture incs + drop-glue decs for retained captures,
materialization incs (§4.2 rule 5), COW-path ops. Elided ops (borrow handoffs, projection
reads, borrowed captures) contribute nothing — that is the entire point of running confinement
**after** modes converge (§3.2 stratification).

### 5.2 Strand-context classification — with the potential-fork over-approximation

Each surviving op site is classified by the strand it can execute on:

- **Parent-strand:** ordinary body code outside any fork construct.
- **Joined-spark:** inside a `ParBind` binding expression, or inside a subtree the backend's
  lenient lowering **could** spark. Spark placement is a codegen-internal decision
  (`lenient-eval.md` §2 — `find_sparkable_bindings` + the cost heuristic run at IR-generation
  time; typecheck cannot see it). The analysis therefore **over-approximates**: every
  lenient-eligible position (independent/dependent `let` binding RHS, apply-argument — the
  §4.2/§4.4/§4.5 emission sites) is treated as potentially off-strand. Monotone-sound
  (assuming off-strand can only widen toward `Crossing`), and cheap in precision: the F2-shape
  proof (§5.3) works on **op existence**, not spark placement — a subtree with no surviving
  ops on the cell is harmless whether sparked or not.
- **Deferred:** inside `LaunchContinue.launched`, a trampoline-deferred `ParBind` continuation,
  or any IO-tree capture — suspension contexts (spine §2.2 rule 4). These were already
  classified as escapes; their cells take the conservative point.

### 5.3 The join, and the "no RC ops on other threads" proof obligation

```
confined(cell) ⟺ every surviving RC-op site on the cell, across ALL frames that can
                 reach the cell, is parent-strand of the cell's owning strand
```

Intra-function, that is the §5.2 classification over the local sites. **Interprocedurally**,
a cell handed to a callee acquires the callee's ops: the summary's `spark_ops[i]` bit answers
"may the callee (transitively) execute an RC op on param i off the calling strand?" — set when
the callee's body has a surviving op on (anything rooted in) param i inside a joined-spark or
deferred context, or passes it onward to a callee whose corresponding bit is set. Declared
leaves have it clear (primitives neither spark nor defer). The per-cell join then reads: local
sites all parent-strand ∧ every callee receiving the cell has `spark_ops` clear for that
position ∧ the cell does not itself cross a deferred edge.

**The confinement stratum is a WORKLIST FIXPOINT, not a single unordered pass** (as-built
S102, FIXME 0512 blocker 2). Because `spark_ops` is interprocedural — a caller inherits a
callee whose bit is set — a single pass over the callables in symbol-table hash order reads a
caller *before* its callee, sees the callee's not-yet-computed bit (init `false`), sets nothing,
and never re-runs: transitive `Crossing` under-reports as `Confined` AND the result is
order-dependent (a determinism/cache hazard). The stratum therefore runs the same worklist
shape as the modes stratum, seeded with the whole universe and re-entering a callable's callers
(the harvested `DepSet` edges the modes stratum already built) whenever its `spark_ops` widens.
It is monotone (bits only flip `false`→`true`) so it converges in O(universe × maxp) visits; it
remains **stratified after** the modes fixpoint (never feeds back into modes, §3.2).

**Discharging the obligation on the S99 F2 shape** (the spine's target): the shared board `g`
is captured by guess sparks **borrowed** (capture-by-borrow, subsumed §8.2-spine), read inside
the spark via projections (`gcells`/`vec-get`) that are rc-free under §4 — the spark side has
**zero surviving ops** on `g`'s cell; the surviving ops (caller-scope inc/dec) are all
parent-strand ⇒ `Confined` ⇒ non-atomic — even while a live borrow crosses a thread, exactly
as the spine's op-wise §2.3 demands. A spark-side path that materializes (§4.2 rule 5 inside
the spark — e.g. the guess's fresh COW copy *retains* `Cell`s from the shared grid) puts
surviving incs on the **retained cells'** counts on the spark strand ⇒ those cells widen to
`Crossing`/atomic — correctly: those are precisely the concurrently-bumped cells of the S99
(b) term, cured by Q4/R5 (write path), not by Q3.

### 5.4 `Transferred` — the ruling (spine routes the commit-vs-collapse decision here)

**Ruling: carry `Transferred` in the internal lattice; collapse it to `Crossing` at emission
for increment I.** The internal confinement domain is
`Confined ⊑ Transferred ⊑ Crossing`; the transfer functions may *produce* `Transferred` (it
falls out naturally: a fresh value built on a spark strand whose remaining ops are all
post-join parent-side has its op pairs ordered by the join's happens-before edge); the
emitted site fact in increment I maps it to `Crossing` (atomic). Reasoning:

- **The measured target does not need it.** The S99 (b) term's contended cells are genuinely
  `Crossing` (concurrent incs from parallel sparks); the F2 read-shape win is served by
  `Confined` under the op-wise definition (§5.3). No fixture currently demonstrates a material
  atomic-op population that is `Transferred`-but-not-`Confined`.
- **Its proof obligation is a different weight class.** `Confined` is site-local: enumerate
  surviving ops, check strand contexts. `Transferred` requires that **every inter-strand op
  pair on the cell, over the cell's whole lifetime, is ordered by a synchronization edge**
  (IVar put→force, spark join) — a per-cell whole-lifetime happens-before argument that
  interacts with *later* re-sharing (a join-transferred value subsequently captured by new
  sparks re-creates concurrency). Carrying that proof in increment I buys unmeasured benefit
  for a qualitatively harder obligation — Principle 6 (complexity has a budget) and Principle
  21 (the spine's measure-first discipline) both say no.
- **Collapse is monotone-sound and additive to reverse** (spine §2.3): the internal domain
  already names the point; promotion is emission-side only — no summary field changes
  (confinement is advisory, never ABI), no contract migration.
- **The named promotion trigger:** post-increment-I F-series measurement showing a material
  share of surviving atomic ops on **join-transferred fresh results** (the "spark builds a
  value, hands it across the join, all subsequent ops parent-side" shape — the one
  `Transferred` population with plausible volume). `/qa`'s part-17 RC-stats lanes can count it
  cheaply (an "atomic ops on cells whose fork edges are all joins" attribution); routed in §12.

---

## §6. Generic-instantiation summary dedup at mint sites (spine §10 item 4, §4.2)

- **The key is the existing one.** A mono instance's identity is its mangled name
  (`build_mangled_name`, `monomorphise.rs:1033` — `name$Type1+Type2`), and mint-site dedup
  already exists (`register_mono_entry` preserves an existing entry + its slot; the `seen`
  gates in `pass4_monomorphise`/`monomorphise_inner_parametric_hops`). The summary is
  **per-instance state on the instance's entry** and inherits this dedup: computed once per
  registered instance per cluster (§3.1), persisted with the entry.
- **Cross-module duplicate instances are benign.** Instances register in the **caller's**
  module (`crates/cranelisp-typecheck/CLAUDE.md` §cross-module-mono), so `cmp$Int+Int` can
  exist in two importing modules. Re-inference is deterministic over the same inputs (same
  template `ast`, same callee summaries — spine §4.2 pins this), so duplicates carry equal
  summaries; no cross-module instance store is added (Principle 7 is satisfied by determinism,
  not by a registry).
- **The session memo.** To make repeated mints and the R3 incremental path cheap, the checker
  env carries a memo `DashMap<(FQSymbol template-home, JitSymbol mangled), OwnershipSummary>`
  (the same concurrency shape as the env's other caches). Hits skip the transfer walk
  entirely. **Invalidation is subsumption, not machinery:** the memo is keyed within a session
  and entries for a template are dropped when the template's module recompiles — which the
  existing recompiled-set cascade (spine §5.1) and the R3 transaction already force for every
  affected module; a dropped-and-recomputed summary that comes back equal re-arms the
  summary-diff fast path.
- **Recursive instance clusters** (mono instances calling each other — the `reduce$… →
  reduce-loop$…` shape) are ordinary cluster-fixpoint members: the memo holds the in-flight
  optimistic value during the fixpoint, the converged value after — standard
  fixpoint-with-memo, no special casing.

---

## §7. The write path — three mechanisms, the static subset, mode-in-key (spine §10 item 5) — increment II

All of §7 is **increment II**; none of it emits in I, and none of it touches the call ABI
(§3.5 — reuse tokens are intra-function, backend part 16).

### 7.1 The three-mechanism ruling (under the spine's framing)

- **(a) One body + dynamic rc==1 entry check — the default, confirmed.** Eligibility is
  static (layout compatibility per instantiation, decided at mono — see §7.3); permission is
  the dynamic check, one branch per **call**, not per element (`vec-set-copy` is the in-tree
  precedent and already makes a set-loop adaptive). This is the mechanism every eligible site
  gets unless (b) proves the site.
- **(b) Static-proof uniqueness — adopted for a narrow, chaining-shaped subset (§7.2).** The
  success metric is **proof chaining across call boundaries** (spine framing): a static proof
  whose *result* is also provably unique composes (`(map inc (map dec v))` → two in-place
  passes); a proof that only elides one entry check does not pay for its machinery. Increment
  II implements the subset and instruments it; body-duplication (uniqueness-specialized
  second bodies) is **not** part of the subset's initial landing — the proof feeds (a)'s
  check-elision first (see (c)).
- **(c) Callee-demands-unique — rejected pure (spine's ruling stands); its refined form is
  adopted as an emission variant of (a):** where the caller holds a static proof, the
  call-site check is elided (proof ⇒ permission); where it holds none, the check runs
  callee-entry-side as (a). There is no third mechanism — (c)-refined *is* (a) with the check
  hoisted/elided, and uniqueness never enters the ABI (R4).

### 7.2 The static-uniqueness subset increment II should prove

**The subset: single-syntactic-use, fresh-or-unique-derived values flowing through
statically-resolved calls.** Precisely, `unique_static(v)` at a use site when:

1. **Provenance:** `v` is (i) a fresh allocation / `Fresh`-result of a static call, (ii) a
   freshly-COW'd copy, or (iii) a param received with a caller-side static proof — AND no
   intervening op can have raised its count: every other reference taken from `v` between
   birth and this use is `Borrowed`/projection-covered (rc-invisible by §4).
2. **Single syntactic use:** this is `v`'s only consuming use in the body, on every path —
   checkable **flow-insensitively** (count consuming-use sites; a projection read is not a
   consuming use). This is the deliberate scope cut: multi-use values, conditional consume
   patterns, and loop-carried accumulators need use-*ordering* (last-use), which is
   backend-local by the spine's narrowness counterweight — they take the dynamic check (a),
   which is exactly the mechanism built for them.
3. **Chaining:** the callee's summary carries `result_unique = true` when its returned value
   is (1)-fresh inside the callee or an in-place-reused unique param — so the proof re-emerges
   from the call and feeds the next link. `result_unique` is advisory-class (a false value is
   always sound; it degrades to the dynamic check), lives in the §2.2 summary's analysis half
   (FIXME 0467's shape), and is emitted `false` throughout increment I.

This subset is small, sound without duplicating last-use above the boundary, and shaped
exactly like the chaining metric: the acceptance witness is the fused
`(map inc (map dec v))`-class pipeline measured as two in-place passes (zero intermediate
allocation), not a per-site elision count. The Sudoku write shape (`(vec-set g …)` on a
freshly-COW'd grid inside a leaf) is case (1)(ii) + (2) and is the S99-funded target.

### 7.3 Eligibility vs permission, and the mode-in-key data question

**Eligibility is static, at mono** (binding, spine): per instantiation, "is in-place layout-
compatible" (`inc : Int→Int` over a `Vec Int` slot — yes; `Int→String` — never). The
eligibility classification is computed where instantiations are minted (the §3.1 pass over
instances; the concrete param/return types are on the entry) and is advisory. **Permission is
per call**: proof (§7.2) or rc==1 check (a). And R2 is not a blocker for the HOF shapes that
matter: `map` **called by name is statically resolved** — its vec param carries a mode; only
its closure argument rides Decision-24 (spine §10.5 pin, restated so part-12 doesn't
re-litigate it).

**Mode-in-mono-key stays OUT in increment I (spine §4.3) and is a measurement question in II.**
The data that would fund it: per-instance counters (a `CRANELISP_RC_STATS` extension) of
(i) dynamic-check executions, (ii) check hit-rate (unique at entry), (iii) the residual
check-branch cost on the F-series fixtures after (a)+(b) land. Mode-in-key pays only if a hot
instance shows a high-volume, high-hit-rate check that a duplicated unique-entry body would
remove — and §7.2's chaining already removes the *provable* population, so the expectation
recorded here is that the key extension does **not** clear the bar. If it does, the key is
mono-internal (`build_mangled_name` gains a mode component for the duplicated instances only)
— invisible on the boundary, no contract migration (spine §4.3 kept-open-by-design).

---

## §8. HOF / closure-conversion mechanics under R2 (spine §10 item 6)

### 8.1 The problem shape

A named function `f` with a non-trivial inferred summary (some param `Borrowed`, or
`result: ProjectionOf`) is **both** statically called (callers compile against its moded ABI)
**and** used as a value (`(map f xs)`, stored in a structure, returned) — and every
closure-path invocation must see a Decision-24-conformant entry (R2: no modes on arrow types).

### 8.2 The ruling: moded native body + synthesized Decision-24 value wrapper

**The canonical body compiles against its inferred moded ABI, and its GOT slot targets that
body. Value-use synthesizes a zero-capture closure whose code pointer is a Decision-24
adapter wrapper** that (i) accepts every param `Owned` per the uniform convention, (ii) calls
the moded body — GOT-indirect through `f`'s slot, so late binding is preserved — passing
borrowed params as bare pointers, (iii) emits the adaptation ops the ABI delta requires
(post-call dec for each `Borrowed` param it received `Owned`; materialization inc when
wrapping a `ProjectionOf` result into the `Fresh` the closure protocol promises), and
(iv) returns. This **is** the in-tree primitive dual path the spine pins as precedent
(inline/moded at static sites + GOT-backed Decision-24 value wrapper —
`compile_operator_as_value`, the operator wrapper map, `literals.rs:239/263`), applied to
user functions — with the spine's recorded as-built gap (NULL vec-family slots) inherited as
`/qa`'s triage item, not this design's.

**Join-to-Owned is rejected.** Widening `f`'s whole summary to Decision-24 because a value-use
exists anywhere would make performance non-local and non-monotone in source: adding one
`(map f …)` in any module silently degrades **every static call site of `f` across the
program** — a spooky-action regression class. Worse, it amplifies R3: under join-to-Owned, an
edit that merely *adds a value-use* is an ABI-changing event for `f`, triggering the §5.4 slow
path across `f`'s whole caller cone. Under the wrapper design, value-uses are
**ABI-neutral by construction** — `f`'s mode vector is derived from its body alone, the
summary-diff gate stays quiet, and the affected set of an edit never grows because of how the
function is consumed. (Principle 1/4: the design keeps callers decoupled from each other's
usage patterns.)

**Mode-erased wrapper vs dual entry:** these converge — the wrapper *is* the second entry.
What this ruling pins beyond "wrapper exists": the **GOT slot carries the moded body** (static
callers dispatch GOT-indirect today and keep doing so, now against the moded convention —
slot identity = ABI identity, exactly the §5.6 slot-versioning model, so a mode-changing
redefinition freshens the slot and old wrappers/closures keep old-ABI consistency
transitively), and the **wrapper is emitted lazily, only for functions with (a) a value-use
and (b) a non-Decision-24 summary** — a summary-trivial function's value-use synthesizes the
closure directly over the body as today, zero new artifacts.

### 8.3 What typecheck provides (this crate's half)

1. **The value-use mark:** a `Var` referencing a callable `Def` in non-callee position is
   already detected by the mono machinery (fn-passed-as-value minting, `program.rs:3308`);
   the pass records value-use as a per-entry fact alongside the summary so the backend knows
   wrapper emission is required without re-deriving it.
2. **The summary itself** (§2.2) — from which the backend computes the wrapper's adaptation
   sequence mechanically (per-param: `Owned→Borrowed` ⇒ post-call dec; result
   `ProjectionOf→Fresh` ⇒ inc; everything else pass-through).
3. **The invariant, stated for `/review` and part 12:** *every code pointer that can reach a
   closure value (HeapClosure code-ptr, IO-tree continuation) targets a
   Decision-24-conformant entry; moded bodies are reachable only through statically-resolved
   call sites and wrappers.* Typecheck's summaries + value-use marks make this checkable; the
   backend's emission discipline makes it true.

### 8.4 The coordination interface with `design/backend/ownership-codegen.md` (part 12 input)

The backend proposal consumes, from this section: the §8.2 mechanism choice (wrapper, not
join); the lazy-emission condition; the GOT-slot-carries-moded-body pin + its §5.6 slot-
versioning interplay; the §8.3 inputs (summary, value-use mark, adaptation algebra). It owes
back (part 12/7): the wrapper emission site + naming/caching (per-function-per-ABI-epoch;
the operator-wrapper map is the precedent), the wrapper's interaction with auto-curry wrappers
(`ResolvedCall::AutoCurry` targets — same adapter family, compose don't stack), and the
borrow-elision emission keyed off the vector at static sites (part 7 proper).

---

## §9. The hand-declared primitive fact table — typecheck side (spine §3.1(a); REQUIRED, increment I)

### 9.1 Where the declared facts live

**On the primitive's own registration, in `cranelisp-primitives`' statically-constructed
`SymbolTable`** (Decision 48) — each `DefKind::Primitive` entry carries its declared
`OwnershipSummary`-equivalent as ordinary entry payload when the §3.3 `/arch` change-set lands
(the same carrier inferred summaries ride; FIXME 0467 names the needed fields). Facts live
where the entity is declared (Principle 7), flow to the analysis through the same chain-follow
every cross-module fact uses (Principle 17), and **typecheck contains no name-keyed primitive
table** (Principle 19 — no module privileged by name; the pass cannot tell a declared leaf
from an inferred summary except by `DefKind`). The declaration syntax is a Rust-side builder
argument at the existing registration sites (`bootstrap.rs`-family), reviewed against the
`ring2-rc.md` §3.3 extern-consumption audit — **the audit table is the seed**: its
"Returns arg unchanged?" column is `ResultMode::AliasOf`, its "Retains arg?" column is
`ParamFlow::Retained`, its dec-before-return default is `ParamFlow::Consumed`, and only-read
params that today consume-by-convention are declared `Borrowed` (analysis fact) while the
extern body keeps consuming (convention unchanged — the split ruling).

### 9.2 How the pass consumes them

As **constant leaf boundary conditions**: never on the worklist, zero fixpoint cost, read at
`Apply` classification (§2.1) exactly like an imported summary. With the table present,
spine §2.2 rule 5 stops firing at primitive leaves — `(vec-len xs)` reads
`xs: Borrowed(analysis)/Consumed`, so `xs` neither widens to `Owned` nor escapes, and the
flagship sum-loop inference survives. Because the extern **convention** is unchanged
(Decision 24 at the ABI — the spine's boundary pin), a caller holding `xs` borrowed adapts at
the extern site (inc before the consuming call — the §4.2-rule-5 idiom); the declared fact's
value is that the *analysis* is not poisoned, not that the ops vanish (op elision at extern
sites is the optional §3.1(b) sibling-symbol refinement, backend part 14, explicitly not this
crate's concern). **No R3 exposure:** primitives are never redefined; a fact change is a
compiler-version change under the `CACHE_SCHEMA_VERSION` bump (spine §3.1(a)).

### 9.3 The inline family vs the extern-shimmed leaves

Two consumption shapes, distinguished by how the call reaches codegen — not by special-casing
in the pass:

- **`vec-get` / `vec-set` / `vec-push` (inline-lowered):** classified at `Apply` via
  `ResolvedCall::BuiltinFn`/the vec-codegen path; their declared facts are the projection
  vocabulary — `vec-get: params [Borrowed], result ProjectionOf(0)` (§4.4-projection-covered:
  the element read is rc-free against the vec's root); `vec-set`/`vec-push`
  (`…-copy` semantics): `params [Owned/Consumed, …]`, **`result MayAliasOf(0)`** (S111 —
  §15 / spine §3.7). **This corrects the former `result Fresh` declaration, which was FALSE:**
  COW is dynamic — the rc==1 in-place arm returns param 0's OWN reference, only the rc>1 arm
  materializes a fresh copy. Declaring `Fresh` let the B3.2 return-protect elision drop a needed
  protect on the in-place arm (the vec-assoc UAF class). `MayAliasOf(0)` is the honest point:
  either-fresh-or-param-0, consumer keeps protect. The in-place reuse itself remains the
  increment-II Q4 target; the read-path fact is unchanged.
  Their facts drive **site classification only**; there is no callee body and no summary walk.
  (Their GOT value-path gap — NULL slots on value-use — is the spine §9 `/qa` triage item.)
- **`vec-len`, `eq`, `display`/`trace`-family, the string family (extern-shimmed):** ordinary
  declared leaves per §9.1/§9.2 — `vec-len: [Borrowed(analysis)/Consumed] → Fresh(Int)`;
  `str-concat: [Owned/Consumed ×2] → Fresh`; `string-identity: [Owned] → AliasOf(0)` (the
  audit's one alias case, which is why `AliasOf` is in the vocabulary at all).

---

## §10. What increment I ships from this crate — and what it must not

**Ships (I):** the §3 pass (modes/escape/flow fixpoint + confinement join), §4 projection
rules incl. provenance site facts, §5 confinement with `Transferred` collapsed, §6 memo, §9
declared-leaf consumption, `Copy` = scalars-only classifier (§2.2), value-use marks (§8.3) —
all gated on the `/arch` §3.3 carrier fields landing in the same implementation sprint, and
sequenced **after** the R3 machinery per spine §5.7 (an increment-I build without the
redefinition transaction must keep the analysis-off toggle on for the dev session).

**Must not (I):** no `unique_static`/`result_unique` emission (II); no reuse tokens anywhere
near a summary or a param (they are backend-intra-function, part 16, per §3.5); no mode in the
mono key (§7.3); no `Transferred` emission (§5.4); no typecheck-side last-use or per-site
ordering analysis (backend-local, §4.2 rule 4); no summary field the backend can derive
in-function (the narrowness counterweight — any candidate is an `/arch` FIXME first).

---

## §11. Quality attributes (per-crate stewardship)

- **Simplicity (P6):** one post-pass, one internal summary struct, one walk; no new store, no
  new pipeline stage; `Transferred` and static-uniqueness deliberately scoped down to what the
  measured targets fund.
- **Maintainability:** the pass touches three seams (`finalize_check_result_inner`,
  `register_mono_entry`-adjacent memo, entry payload); the ABI surface is exactly the
  summary-diff gate's input — one definition serves analysis, cache, and R3.
- **Observability:** summaries are serde-visible entry payload ⇒ `/info`-class introspection
  and `.meta.json` diffing get them for free; a `CRANELISP_OWNERSHIP_TRACE` dump of per-cluster
  summaries + per-site verdicts is the designed debug hook (sibling of
  `CRANELISP_CODEGEN_TRACE`); the analysis-off toggle (spine §3.4) is the differential anchor.
- **Concurrency-safety:** the pass runs inside the cluster's single-worker processing window,
  writes through `SymbolTableAccess` staging (no new shared state); the memo is a `DashMap`
  with last-write-wins-safe (deterministic) values.
- **Performance:** §3.4's structural budget — annotation-only walks, cone-bounded interactive
  cost, memoized instantiations.
- **Testability (P5):** the transfer function is a pure function
  `(body: &MonoExpr, leaves+imports: &impl Fn(FQSymbol)->Summary) → (Summary, SiteFacts)` —
  unit-testable in-crate with `TestFixture` and hand-built `MonoExpr` bodies, no backend, no
  session. Fixpoint tests: recursive two-function clusters with known joins. Negative tests:
  escape-edge widening (return/store/suspension), the §4.2-rule-4 aliased-root shape, the
  `LaunchContinue` conservative point. Coverage gaps routed to `/qa` (§12).

---

## §12. Open questions routed onward

**Filed now:**

- **FIXME 0467 (`target: /arch`)** — the persisted summary's designed shape for the §3.3
  implementing-sprint pass: ABI half gains `result: ResultMode` (interprocedural
  borrow-through-projection — the accessor shape, §4.4; ABI-bearing, summary-diff-gated,
  `Fresh`-defaulted); analysis half gains `param_flow` / `spark_ops` / `result_unique`
  (advisory, `#[serde(default)]`-conservative). `design/arch/fixmes/0467-…`.

**To `design/backend/ownership-codegen.md` (cited as part-12/13/14/16 inputs):**

1. §8.4's owed items: wrapper emission/caching/naming, auto-curry adapter composition, the
   borrow-elision emission keyed off the vector.
2. §4.2 rule 4's backend half: `compute_last_uses` counts provenance-rooted uses against the
   root (the site-fact consumption contract).
3. §5's emission half: non-atomic op selection gated on the `confined` site fact; the
   analysis-off toggle must also force `confined = None` paths (one master switch, spine §6.2).
4. §9.2's adaptation-inc emission at extern sites (and the optional part-14 sibling-symbol
   refinement, with the when-worth-it data burden the spine assigns it).

**To `/qa` (parts 17–18):**

5. A REPL turn-latency lane (F1 fixture, redefinition loop) holding §3.4's interactive budget —
   body-only edits stay at today's cost; ABI-changing edits bounded by the cone.
6. The §5.4 promotion counter: attribute surviving atomic RC ops to "all-fork-edges-are-joins"
   cells in the RC-stats lanes, so the `Transferred` decision is revisited on data.
7. Negative differential coverage for §4: a borrowed projection escaping via return/store must
   materialize (leak/double-free guards on exactly that edge), plus the §4.2-rule-4
   root-release-ordering shape (the Sprint-61 regression, one level up).
8. Inherited from the spine (§9): the vec-query-family NULL-GOT-slot value-use triage.

**Deferred by design:** `Transferred` promotion (§5.4 trigger); mode-in-key (§7.3 data
question); Hoogle-style anything — none block increments I/II.

---

## §13. Increment-I change-set staging (S102 Phase 3 — Sprint 102 Block B2)

Authored by `/design` (cranelisp-typecheck) at S102 Phase 3, against
`sprints/SPRINT.md` Block B2 and the Phase-2 rulings (Q1 capture-first, Q3 close-short
seam after B2, the public-API impact statement). Everything here elaborates §§1–10;
where §13.6 amends an earlier section it says so explicitly.

### 13.1 Dependency pin — CS-A, the `/arch` `cranelisp-types` change-set (v11→v12)

All typecheck change-sets sequence **after** one `/arch`-authored `cranelisp-types`
change-set (one `CACHE_SCHEMA_VERSION` bump v11→v12, riding the 0476
`PrimitiveBody` reshape per the Phase-2 public-API statement). What this crate needs
from it, exactly — the list `/arch` verifies at the Phase-3 exit gate:

1. **`Mode { Copy, Borrowed, Owned }`** — all three points from day one (the contract
   never migrates, spine §7), even though the increment-I classifier mints `Copy` for
   scalars only (§2.2).
2. **`ModeSummary { param_modes: Vec<Mode>, result: ResultMode, param_flow:
   Vec<ParamFlow>, spark_ops: Vec<bool>, result_unique: bool }`** (spine §3.3 enriched
   shape) with derives `Clone + Debug + PartialEq + Eq + Serialize + Deserialize`;
   `#[serde(default)]` on the advisory half. Full `Eq` is load-bearing for the
   fixpoint's change detection (an advisory-half change must re-enter callers too —
   `param_flow`/`spark_ops` feed caller classification, §2.2).
3. **`ResultMode { Fresh, ProjectionOf(usize), AliasOf(usize) }`** (default `Fresh`)
   and **`ParamFlow { Consumed, IntoResult, Retained }`**.
4. **Conservative-read accessors on `ModeSummary`** — the single home for ⊤-on-absence
   (Principle 7/18; both typecheck and backend read through them):
   `param_mode(i) -> Mode` (missing/short ⇒ `Owned`), `param_flow(i) -> ParamFlow`
   (⇒ `Retained`), `spark_op(i) -> bool` (⇒ `true`). A bare-serde-default empty `Vec`
   MUST read as conservative through these accessors — no consumer indexes the vectors
   directly.
5. **`abi_eq(&self, &Self) -> bool`** (or an `AbiModeSurface` projection view)
   comparing `(param_modes, result)` only — one definition serving the R3
   summary-diff gate (`/int`'s `AbiSurface` comparison) and any future consumer, so
   the ABI half is never hand-picked field-by-field at two sites (mirror hazard).
6. **`mode_summary: Option<ModeSummary>` on the callable `DefKind` variants** (spine
   §3.3; `UserFn`-Concrete and `Primitive` are the increment-I load-bearing two) +
   a uniform **`ModuleEntry::mode_summary() -> Option<&ModeSummary>`** read accessor
   (the `callable_got_slot()` precedent, `module.rs:1303`) + a
   **`set_mode_summary(...)`-style mutator** returning a did-write indicator for
   non-callable kinds, usable through `current_symbol_table_mut`.
7. **The `DefKind::Primitive` declared-fact payload IS the same `mode_summary` slot**
   — no separate `PrimitiveFacts` type. Principle 19 demands the pass cannot tell a
   declared leaf from an inferred summary except by `DefKind`; one carrier + one read
   accessor (item 6) delivers that structurally. The declaration site populates it at
   entry construction (§13.4). (`borrowed_sibling_slot: Option<...>` is the backend's
   §3.1(b) sibling carrier — same change-set, not consumed by this crate.)
8. **`MonoDefnVariant.mode_summary: Option<ModeSummary>`** — the compile-in-hand
   carrier the backend reads.
9. **`MonoExpr` advisory site-fact fields** (`#[serde(default)]` = `None` =
   conservative): `escapes: Option<bool>` + `confined: Option<bool>` on the
   allocation/capture-producing variants (`ConstrADT`, `VecLit`, `Lambda`,
   `StringLit`, `Apply`), `unique_static: Option<bool>` present-but-never-`Some` in
   increment I, and **`provenance: Option<Symbol>`** (the borrowed-projection root
   binding) on the projection-producing sites (`Apply` — accessor/`vec-get` calls —
   and match-arm pattern bindings). Symbol-keyed provenance carries the §13.6(d)
   shadowing rule. `/arch` pins the exact variant set; this is the minimum this
   crate's §2.3 emission needs.
10. **The per-entry value-use mark** (§8.3) — a per-entry bool the pass writes and the
    backend's wrapper emission reads.
11. **0476's `PrimitiveBody::{Extern, Inline}` + `is_callable_target()`** — consumed
    by the §2.1 classifier: the inline-lowered vs extern-shimmed distinction (§9.3)
    becomes representational instead of name-keyed (Principle 19 — the classifier
    reads `PrimitiveBody::Inline`, never matches `"vec-get"` by name).
12. **Toggle relocation — the one-master-switch need (spine §6.2).** The read-once
    `CRANELISP_NO_OWNERSHIP` gate currently lives in
    `cranelisp-backend/src/cache/manifest.rs:243–260`; typecheck cannot depend on
    backend. Ask: relocate the accessor to `cranelisp-types` (e.g.
    `ownership_analysis_off()`), backend delegates, manifest key untouched. Fallback
    if `/arch` rejects env-reading in the types crate: a typecheck-local read-once
    reader of the same env name with a cross-referencing comment; the L-B2(i)
    suite-polarity lane is the divergence guard. The relocation is preferred —
    two independent readers of one polarity is the Principle-7 mirror class.

### 13.2 The ordered change-sets

Each CS is one `/dev` change-set with its Principle-23 scenario matrix (§13.7) landing
in the same commit. Sequencing: CS-A → {CS-B, CS-1} → CS-2 → CS-3 → CS-4. CS-B and
CS-1 are order-independent (CS-1's leaf-read unit tests build `DefKind::Primitive`
entries via `TestFixture` — `builtins.rs:1005/1083` already mints them — so CS-1 does
not block on CS-B; only the e2e fact-table lanes L-D3e need CS-B).

**Proposed module composition (Principle 23 — strategy seams as named submodules):**
a new `crates/cranelisp-typecheck/src/ownership/` cluster — `mod.rs` (the
`pass5_ownership` driver), `classify.rs` (static-call classifier + `Copy` predicate),
`transfer.rs` (the body walk), `fixpoint.rs` (worklist/SCC/memo),
`confinement.rs` (strand classification + per-cell join), `publish.rs`
(summary/site-fact/value-use publication) — each with a sibling per-submodule test
module. Pass entry wires into `program.rs::finalize_check_result_inner` after the
callee write-back (current anchors: `pass4_monomorphise` call at `program.rs:1986`,
accumulator callee write-back at `:2082–2084`; the §3.1 `:1901`/`:1999` anchors have
drifted with S101's edits — same seam, same order).

- **CS-B — primitive fact-table declaration** (owner: `/dev` narrow on
  `cranelisp-primitives`, backend-paired per root `CLAUDE.md`; NOT a typecheck
  change-set — named here because pass5's leaf reads consume it). `PrimitiveDef`
  gains a declared-facts field (a `ModeSummary` value per item 7);
  `insert_primitive_entry` + `insert_vec_query_entries` populate the entry's
  `mode_summary` at construction. Content per §13.4; audit-table cross-check +
  FIXME 0504 (the missing `neq-string` row) resolve before or with it.
- **CS-1 — classifier + `Copy` predicate + declared-leaf reads** (`classify.rs`).
  The §2.1 static-call classifier as a pure function over an `Apply` shape + a
  chain-follow lookup (`resolve_terminal_entry_and_home`); `PrimitiveBody`
  consumption (item 11); the memoized scalars-only `Copy` classifier (§2.2); leaf
  fact reads through `ModuleEntry::mode_summary()`. No fixpoint, no writes —
  unit-tested standalone.
- **CS-2 — the transfer function** (`transfer.rs`). One pre-order `MonoExpr` body
  walk per §3.3: per-binding abstract state (mode + provenance root), mode/flow
  joins, escape edges (§2.2-spine rules 1–5 incl. R6 suspension), projection rules
  §4.2 1–5, `ResultMode` derivation (with the §13.6(c) multi-path join),
  `result_unique` hardwired `false`, value-use marks. Signature per the §11
  testability pin: `(body, lookup: impl Fn(&FQSymbol) -> Option<ModeSummary>) →
  (ModeSummary, SiteFacts, DepSet)` — pure, no table access, `TestFixture` +
  hand-built bodies. `DepSet` is the harvested dependency set (§13.3).
- **CS-3 — fixpoint driver + SCC + confinement + memo** (`fixpoint.rs` +
  `confinement.rs`). The §3.2 worklist: universe = cluster's codegen-bound callables
  (defined-symbols + `codegen_view.is_some()`, incl. mono instances registered by
  `register_mono_entry`); reverse-topo seeding from the S101-widened
  `call_graph_edges` (template grain — §13.3); re-entry driven by the harvested
  `DepSet`, not the persisted edges; stratification (modes/escape/flow converge, then
  the §5 confinement join over surviving ops with `spark_ops` propagation and the
  §5.4 `Transferred`→`Crossing` emission collapse); the §6 session memo
  (`DashMap` on the checker env, keyed `(template home, mangled name)`). The
  toggle gate lives at the driver entry: `pass5_ownership` returns immediately when
  analysis is off (§13.5).
- **CS-4 — publication + observability** (`publish.rs`). Post-convergence: summaries
  onto entries via `current_symbol_table_mut` (staging-aware, cluster-atomic —
  Decision 44, exactly the `program/finalize.rs::finalize_annotations_and_publish`
  write path); the
  §13.6(b) one-shot site-fact walk annotating the stored `codegen_view`
  (`MonoDefnVariant.mode_summary` + per-node facts + provenance); value-use marks;
  the **H5 `CRANELISP_OWNERSHIP_TRACE`** dump (per-cluster summaries + per-site
  verdicts — an in-increment deliverable, not a follow-up: I-G3 and L-D3f are
  unmeasurable without it, qa plan §6/G-3).

**Out of this crate, named for `/sprint`:** (i) the R3 summary-diff gate widening
(type-scheme-only → + `abi_eq`) is a small `src/` change-set (`/int` owns the
transaction; item 5 is its input) — Q3 pin 1 expects it live the moment summaries
exist; (ii) I-G5/I-G6 run at the B2 seam even under a short close (Q3 pin 2) —
`/qa` executes, CS-3/CS-4's memo + H5 are the support surface.

### 13.3 Graph-feed verification — what the S101 `callees` widening does and does not give pass5

Verified against the landed S101 work (0470 resolved: single-chokepoint recorder in
`infer_var`, call- **and** value-position user-fn references, retained in the active
`BodyFrame`; 0472 resolved: `program/callees.rs::harvest_callees` for ledger bodies
and `harvest_callees_in_module` for impl-provided/default/HKT method bodies; schema
v11):

- **What pass5 assumed (§3.2) and now verifiably has:** complete forward
  statically-resolved user-fn edges at **template/defn grain** — plain direct calls,
  SigDispatch/TraitMethod targets, value-position references, impl/default/HKT method
  bodies. Sufficient for **reverse-topo worklist seeding** (Kahn's over intra-cluster
  edges; the `dependency_sort` precedent) and for the R3 reverse index (one graph,
  two consumers — spine §5.3). The widening delivers what §3.2's *seeding* assumes.
- **Residual gap 1 — grain (the design consequence, not just a risk).** The recorder
  runs at infer time, pre-mono: edges are template-grain (`f → g`), never
  instance-grain (`f$Int → g$Int`); the 0472 cure deliberately excluded the
  mono-recheck seam (mono instances never appear as edge sources — documented
  template-chain rationale, S101 Wave 2b). pass5 computes **per-instance** summaries,
  so caller re-entry keyed on template edges would over-approximate (re-enter every
  instance of a caller template) — sound but wasteful, and worse, it makes fixpoint
  correctness depend on a persisted feed with a known deliberate exclusion.
  **Ruling: the fixpoint's re-entry edges are harvested by the transfer walk itself**
  (`DepSet`: every callee whose summary an `Apply` classification consulted, at the
  exact grain consulted — mangled instance or concrete FQSymbol). Correctness then
  depends only on what the walk actually read (self-describing, immune to any feed
  gap); `call_graph_edges` is demoted to a **seeding-order hint** (a bad order costs
  extra revisits, never a wrong result — the seed-order-independence scenario in
  §13.7 pins this). Mono instances, absent from the persisted graph, are appended to
  the seed in registration order after the template-sorted members.
- **Residual gap 2 — self-edges** are structurally skipped by the recorder (recursion
  binds locally). Irrelevant to pass5: the harvested `DepSet` sees a self-call's
  `resolved_call` like any other, and a self-recursive summary change re-enters its
  own frame via the ordinary fixpoint revisit.
- **Residual gap 3 — target population**: `call_graph_edges` records user-fn
  references only (no primitive/constructor/platform edges). Correct for pass5 —
  those are constant leaves/pinned boundaries (§9.2), never on the worklist.
- **Residual gap 4 — cross-module ordering** (risk, accepted): imported summaries are
  boundary conditions read by chain-follow; a mutual-import cycle compiled under the
  S93 signature/body pre-pass can read an importee whose pass5 has not yet run —
  absent summary ⇒ ⊤ ⇒ Decision-24 on those edges (monotone-sound, precision-only
  loss, confined to mutual-import cycles). Not cured in increment I; named for the
  F-series attribution if a fixture ever shows it.
- **Residual gap 5 — 0488 adjacency** (risk, coordination): the missing-mono defect
  class (FQ-call/imported-value-use instances never minted) means those shapes have
  no compiled body — a compile-level defect upstream of pass5, not a summary gap
  (nothing to summarize). Corpus-excluded per the Q1 ruling; when the fix lands,
  newly-minted instances enter the universe by the existing predicate with no pass5
  change. `/qa`'s isolation (Block A3, `tests/plan/s102-test-plan.md` §3) may land
  in `monomorphise.rs` mid-sprint — the 0497 rider (§13.7) coordinates on that file.

### 13.4 Fact-table staging and the coverage verdict

**Where declared (confirms §9.1 against as-built source):** `PrimitiveDef` rows
(`cranelisp-primitives/src/operator.rs` — `ring0/ring1/ring3_primitives()`) gain a
declared `ModeSummary`; `insert_primitive_entry` (`lib.rs:223`) and
`insert_vec_query_entries` (`lib.rs:267`) place it on the entry's `mode_summary`
slot at static construction. No typecheck-side table of any kind (Principle 19).

**Coverage cross-check against the `ring2-rc.md` §3.3 extern audit (the seed):**

- **Covered, transcribed mechanically:** the 15 string externs with heap args +
  `parse-int` (audit "Action" column ⇒ `param_flow: Consumed`, `result: Fresh`);
  `string-identity` (⇒ `AliasOf(0)` — the one alias row, why `AliasOf` exists);
  `quote-sexp` (`Consumed`/`Fresh`); `str-eq`-family (⇒ analysis-fact `Borrowed` +
  extern body keeps consuming — the §9.1 split ruling; declared `Borrowed` is per
  the only-read column, the ABI stays Decision-24).
- **Covered, hand-built (no audit row needed — no extern body):** the vec query
  family per §9.3 — `vec-get: [Borrowed], ProjectionOf(0)`;
  `vec-set`/`vec-push`: `[Owned/Consumed, …], Fresh`; `vec-len:
  [Borrowed(analysis)/Consumed], Fresh`.
- **Trivial, generated:** the ~30 ring0 scalar ops + `int/float/bool-to-string`
  (all-`Copy` params; `Fresh` results) — mechanical, zero audit dependency.
- **Gap found: `neq-string`** — shimmed + registered post-audit, two heap args,
  body verified consuming (`string.rs:109–116`), **no audit row**. FIXME 0504 filed
  (`target: /design`, backend deployment): the row must exist before CS-B
  transcribes and before L-D3e generates its per-row guards, or both silently skip
  the leaf.
- **Deliberate scope cut, named:** `DefKind::PrimitiveExtern` entries (`sconcat`,
  `bind`, `catch-runtime-error`, `discover-tests` — slot-less, by-name
  `Linkage::Import` dispatch) carry **no facts in increment I** and stay at the
  pinned Decision-24 boundary (spine §3.1 "named-extern intrinsic" pin); §2.2 rule 5
  fires on their args. `sconcat` has an audit row ready if macro-infrastructure
  volume ever makes this measurable — it is a watch item, not a gap.
- **Correctly excluded (not `DefKind::Primitive`):** trace-family accessors,
  `cranelisp_run_io`, IVar intrinsics (intrinsics crate), platform fns
  (`PlatformEffect`), `heap_alloc_string`/`string_read`/`vec-push-grow` (internal,
  never name-resolvable). All boundary-pinned per the spine.

**Verdict: the audit table is a sufficient seed — coverage is complete for every
heap-arg extern-shimmed `DefKind::Primitive` except the one filed gap (0504), plus
the named `PrimitiveExtern` scope cut.** Audit mechanism: CS-B lands a completeness
contract test (every `DefKind::Primitive` entry with a heap-typed param in its
scheme carries a declared summary — the S101 cat-1 "convention-populated field"
lesson applied at birth), and `/qa`'s L-D3e generates one wrong-direction e2e guard
per audit row.

### 13.5 Monotone-soundness obligations and the toggle pin

- **Absent facts ⇒ Decision-24, structurally.** Every read of a summary or site fact
  goes through the CS-A conservative-read accessors (§13.1 items 4–6); no pass5 code
  path indexes the raw vectors or interprets absence. An absent summary reads ⊤ on the
  parameter axes — all-`Owned`, all-`Retained`, all-`spark_ops` — and an absent site fact is
  `None` = escapes/crossing/shared/no-provenance. **The result axis is the exception, and
  always was:** the walk substitutes `ResultMode::Fresh` for an absent callee result, which is
  that axis's STRONGEST claim, not its ⊤. The axis's real ⊤ is `MayAliasAny` (§19.2); §19.7
  states the premise that keeps the `Fresh` read co-sound and names the observation that would
  refute it. Joins only widen; init is
  optimistic per fresh run; `Transferred` collapses to `Crossing` at emission (§5.4);
  `result_unique` and `unique_static` are never emitted true in increment I (§10).
- **The toggle pin (stated with explicit polarity): when `CRANELISP_NO_OWNERSHIP` is
  SET (analysis disabled), typecheck emits NO summaries** — `pass5_ownership`
  returns at entry before any walk: no `ModeSummary` computed or published,
  `mode_summary = None` on every entry and every `MonoDefnVariant`, all site facts
  `None`, no value-use marks, memo untouched. This is the spine's own wording
  (§5.7: "with analysis off, summaries are absent") — the
  emit-but-ignored alternative is REJECTED on three grounds: (i) **oracle honesty** —
  I-G5 measures toggle-on vs toggle-off compile cost; running pass5 under both
  polarities hides exactly the cost the gate exists to bound; (ii) **behavioral
  fidelity** — with summaries present, the R3 `AbiSurface` gate would classify
  mode-changing edits ABI-changing and take slow-path recompiles in a configuration
  whose whole purpose is to reproduce the pre-increment (stage-M, type-scheme-only)
  session byte-for-byte; (iii) **persistence coherence** — the manifest polarity key
  (landed S101) wholesale-invalidates on flip precisely so off-polarity caches never
  carry facts the polarity says do not exist; emitting them anyway re-opens the
  question the key closed. When the env var is UNSET (the default), the pass runs
  and emits; the backend consumes or ignores per its own gating (one master switch,
  read through the §13.1-item-12 shared accessor on both sides).
- **What typecheck guarantees under toggle-set, testably:** entries and
  `.meta.json` payloads are field-identical to a stage-M compile (serde: absent
  optional fields serialize away), so the differential oracle's byte-identity
  obligation (spine §6.2) holds on this crate's outputs by construction, not by
  filtering.

### 13.6 Refinements the implementation problem forces (amendments to §§2–4)

- **(a) The internal `OwnershipSummary` (§2.2) is superseded by the boundary
  `ModeSummary`.** FIXME 0467's folding put the identical field set on the §3.3
  carrier; a parallel crate-internal struct would be a Principle-7 mirror. pass5
  computes `ModeSummary` values directly; only per-walk working state (the
  binding→(mode, provenance) map, the strand-context stack, `DepSet`) stays
  internal. §2.2's field-by-field justification stands, read onto `ModeSummary`.
- **(b) Site-fact emission moves to a one-shot post-convergence walk** (amends
  §3.3's "producing (i) … and (ii) site facts" per visit). Facts written mid-fixpoint
  from a not-yet-converged summary environment could be stale on revisit; rather than
  re-writing per visit, the repeated transfer walk computes summaries + `DepSet`
  only, and one annotation walk per callable runs after both strata converge,
  writing facts + provenance onto the stored `codegen_view`. Budget: ≤ one extra
  linear walk per callable — inside §3.4's structural budget (still
  annotation-only, no `Type` traffic).
- **(c) Multi-path `ResultMode` join, pinned** (completes §3.3's return-position
  rule). **As-built (S102, FIXME 0520 — the ABI-half soundness cure; SUPERSEDES
  the original "any disagreement ⇒ `Fresh`" rule, which was UNSOUND).** The join
  is over the may-alias each path can carry to the result. `Fresh` is **NOT** the
  conservative point — it is the DANGEROUS point: `Fresh` means "no param reaches
  the result", which a borrow-elision consumer trusts to DROP a needed RC op and
  free the returned param → UAF. The conservative (safe, protect-preserving)
  direction is **not-`Fresh`**. Rule:
  - all return paths `AliasOf(i)`/`ProjectionOf(i)` for the SAME `i` and kind ⇒
    that precise mode (a full-`if`/same-param-`match` stays exact);
  - any path that MAY carry a param to the result (a param on one arm, a fresh or
    a DIFFERENT param on another, or mixed alias/projection kinds) ⇒ a
    **not-`Fresh`** may-alias: `AliasOf(i)` (or `ProjectionOf(i)` when EVERY
    reaching path is a projection), where `i` is the reaching param of LOWEST
    index (the deterministic conservative representative when several may reach);
  - `Fresh` is emitted **only** when NO path can carry a param (both/all paths
    provably fresh — an owned local returned by value is `Fresh` at the result).

  This is the cure for the partial control-flow collapse: `(defn build [v i n]
  (if c v (build (vec-push v i) …)))` returns param `v` in the base case, so its
  result is `AliasOf(0)`, never `Fresh` — despite the recursive arm being fresh.
  The implementation carries an internal `Origin::MayParam { rep, projection }`
  through `If`/`Match` joins and through `Apply` composition (a may-alias arg to
  an `AliasOf`/`ProjectionOf` callee stays a may-alias — never collapses to
  `Fresh`), mapping to the `ResultMode` at the boundary. **Monotone soundness:**
  widening toward not-`Fresh` is always sound (only less precise — an unneeded
  retain, i.e. a leak, never an elided one). **The lowest-index representative is
  RETIRED (S121, §19.3) — it was not sound, and it was not a join.** For a return that
  may alias MULTIPLE DISTINCT params (the `(if c v w)` shape) the rule kept one reaching
  index and discarded the rest, which this section justified as "sound for the live
  borrow-elision consumer, which needs only the BINARY `Fresh`-vs-not". That premise is
  false, because the producer is itself an index reader: `walk_apply` composes a callee's
  `MayAliasOf(k)` by taking argument `k` alone, so a caller that passes a fresh value at the
  representative position and a parameter at the discarded one composes to `Fresh` and
  publishes the elide-my-protect claim. Measured 2026-09-07 at the ownership trace on a
  three-line program: `pick2 [c a b] = (if c a b)` publishes `MayAliasOf(1)`, and its caller
  `q [c p] = (pick2 c "lit" p)` publishes `result=Fresh` while `q` may return its own
  parameter `p` (§19.1). The same discard is what makes the transfer non-monotone on the
  result axis, which is the non-convergence of §19.1. §19.3 replaces the representative
  with the reaching-parameter SET and publishes `MayAliasAny` when it holds two or more.
  §4.2-rule-5 materialization is still emitted on each non-`Fresh` path (the returned borrow
  escapes at that edge).
- **(d) Provenance is symbol-keyed, with a shadowing guard.** `MonoExpr` bindings
  are `Symbol`-named, so the provenance site fact carries the root binding's
  `Symbol` — the carrier the backend's last-use machinery was expected to key
  on. **As built no consumer binds that symbol**; §20.5(i) records the consumer
  position read at source, and nothing below rests on identity matching.
  Where a body rebinds a name that is (or roots) a live provenance root
  (`let x … let x …` shadowing), the walk emits `provenance: None` for projections
  whose root would be ambiguous under that name — conservative (the backend treats
  no-provenance as materialize-at-Decision-24), and pinned as a scenario row
  (§13.7 transfer matrix) so the cut is visible, not accidental. **As-built (S102,
  FIXME 0512 blocker 3 + Wave 8c-R F2):** ONE single-sourced helper
  `transfer.rs::drop_shadowed_provenance(name)` — `if bindings.contains_key(name)
  { facts.provenance.retain(|_, root| root != name) }` — is called at **every**
  binding-introducing seam: the `Let` arm, the `ParBind` arm, AND each `Match`
  pattern binding in `bind_pattern`. The first cut (FIXME 0512) guarded only the
  `Let` seam and left the match-arm MIRROR unfixed: `(defn f [g h] (let [x (gcells
  g)] (match h [(Box g) x])))` — the arm binds field `g` (scrutinee `h≠g`, so the
  arm's own scrutinee-root suppression does NOT fire) yet shadows the param `g`,
  leaving `x`'s stale `g`-rooted provenance live ⇒ a backend eliding the
  materialize on a value that borrows a freed `g` (UAF, same class as the `Let`
  narrowing). The `bind_pattern` scrutinee-root `shadow` check (arm-own provenance
  suppression) is a SEPARATE, complementary guard and stays. **Wave 8c-R2 note
  (§13.6(i)):** the scope-frame discipline now makes shadow *detection* precise
  (the walker resolves a name to its lexically-correct binding), but the
  `drop_shadowed_provenance` drop-to-`None` (⇒ Decision-24 materialize) STAYS as
  the boundary-safe action at a genuine cross-boundary `Symbol` collision: the
  fact leaves the walk as a bare `Symbol` that the walk's scope discipline does
  not travel with, and dropping it leaves no fact rooted at a rebound name.
  **What the backend reads is presence, not identity** (§20.5(i)), so the drop
  is not established by an observed re-resolving consumer; it is retained as the
  safe direction for one. The scope stack does not retire it.
- **(g) Binding-mediated escape re-propagation** (amends §2.2 rules 1–5 for the
  let-indirected shape; FIXME 0512 blocker 1). §3.3's "a later escaping *use of
  `n`* re-classifies the param root through `n`'s Root/Projection origin" fires
  only for `Root`/`Projection` origins — never for a **`Fresh`** binding (a
  freshly-constructed `VecLit`/`ConstrADT`/`Lambda`). So `(defn keep [x] (let
  [box (Some x)] box))` narrowed to `escapes=false` on the returned aggregate and
  `x.param_flow=Consumed` when the truth is `escapes=true` + `IntoResult` (the
  DIRECT `(Some x)` was already correct+tested; the binding-indirected shape was
  the bug). **As-built (S102 blocker 1 + Wave 8c-R F1):** the transfer walker
  records each `Fresh` binding used in an escaping context (`ctx.escapes()`) with
  that context; `transfer.rs::drain_escaped(bindings)` re-walks the binding's RHS
  in the escaping context, so the folded-in params widen
  (`Consumed`→`IntoResult`/`Retained` via the monotone `join_flow`) and the
  aggregate's `escapes` fact flips `false`→`true`. **The drain is a FIXPOINT over
  the scope's own bindings, not one level** (F1 correction — the first cut
  partitioned once): a re-walk can newly escape an EARLIER binding of the same
  flat `let` fold-chain (`[a (Some x) b (Some a)]`, `b` returned ⇒ `a` escapes ⇒
  `x` escapes), so the drain loops — re-partitioning `self.escaped` for this
  scope's names and re-walking until no this-scope entry remains. **Termination
  is guarded by deduping each `(name, ctx)` re-walk** (bounded by |bindings| ×
  |UseCtx|). **As-built (Wave 8c-R2, §13.6(i)):** the drain re-walks each RHS in
  its DEFINING scope — the binding-being-drained is temporarily restored to its
  shadowed prior, so `var("a")` in a self-aliasing binding `(let [a a] …)` (the
  stdlib `case`/`cond` macro shape, `` `(let [__case__ __case__] …) ``) resolves
  to the OUTER `a`, not itself. Because `self.escaped` is `Symbol`-keyed, a
  still-`Fresh`, still-`"a"`-named outer binding is re-pushed as `("a", ctx)`, so
  the `(name, ctx)` dedup remains the **defensive** termination cap — its ROLE
  downgraded from the F1 cure's termination mechanism to a belt-and-braces bound
  (the Principle-7 workaround did not fully retire because name-keying, not
  unscoped bindings, is the residual re-push driver). Deduping
  preserves the fold-chain fixpoint: re-walking one RHS in one context is
  idempotent (monotone joins), so once done it never needs repeating; distinct
  escaping contexts of one binding are still each re-walked (no flow
  under-widened). Monotone ⇒ purely-local aggregates keep `escapes=false` /
  `Consumed`. **A residual PRECISION gap (advisory-half only; NOT the F4
  soundness issue, which §13.6(i) cured):** flow propagation through a
  self-aliasing shadow chain (`(let [a (Some x)] (let [a a] a))`) still does NOT
  reach the outer binding — the inner drain consumes the re-pushed `Symbol`-keyed
  `"a"` escape and dedups it before it can bubble to the outer let — so `x` stays
  `Consumed` there (verified empirically, Wave 8c-R2). Scope discipline reaches
  the outer *`BindState`* on the re-walk, but the name-keyed `escaped`/dedup pair
  means the escape does not *propagate* across the name collision; closing it
  fully would require attributing escapes to binding identity rather than name
  (out of the §13.6(i) scope; the earlier "0518 strike this caveat" premise did
  not hold — the driver is name-keying, not the now-cured unscoped map).
  **Applies at BOTH the `Let` and `ParBind` seams** —
  a joined-spark binding that is returned/stored escapes exactly like a `let`
  binding; §4.3's non-escape property is a STRAND fact (confinement), not a
  frame-escape fact, so `ParBind` must drain too (F1 second gap). ABI mode is
  unaffected: a constructor field-store is `Owned` on both paths, so `param_modes`
  never moves — this refinement is advisory-half only (`param_flow` + escape).
- **(h) Cap exhaustion REFUSES the cluster — it publishes nothing** (hardens §3.2's
  worklist termination; FIXME 0512 blocker 4, **corrected S121, §19.5**). A
  partially-converged summary set is monotone-**below** its true fixpoint ⇒ too precise ⇒
  unsound to publish. The universe-wide scope of the recovery stands: a non-queued entry may
  have converged against a still-too-low queued callee, so no per-callable salvage is
  available.
  **What is corrected is WHAT the recovery publishes.** The pre-S121 as-built reset the whole
  universe to a hand-written ⊤ literal (`fixpoint::top` — all-`Owned` / `Retained` /
  spark-set / **`result: Fresh`**) and re-populated every `SiteFacts` from
  `fixpoint::conservative_site_facts`. That literal was ⊤ on four axes and the axis's
  STRONGEST claim on the fifth, and the claim it published — "the result reaches none of my
  parameters" — is the one fact the backend's callee-side return protect elides on. Measured
  S121: the f4 fixture's whole module (41/41 callables) carried that literal, and the
  builder that returns its accumulator lost its return retain (`sprints/SPRINT.md`, S121
  active checkpoint). The old claim in this bullet that "⊤-everywhere is the only sound
  recovery" is **falsified by measurement** and is deleted with the literal.
  **As-built after §19.5:** a cluster whose analysis does not converge publishes **no
  summary, no site fact and no value-use mark** for any member. `top`, `reset_to_top` and
  `conservative_site_facts` retire. The refused cluster is then exactly the
  `CRANELISP_NO_OWNERSHIP` shape (§13.5), whose safety is the differential oracle's
  (`design/arch/ownership-inference.md` §6.2) rather than a fresh argument about a literal.
  The refusal is shared by all three strata (§19.5), and the cap remains the shared test seam
  (`compute_cluster_with_cap(.., cap=0)` forces the refusal).
- **(i) The transfer walker models lexical scope — scope-save/restore**
  (Wave 8c-R2, F4 cure; FIXME 0518). **Root cause (the third instance of the
  scope-modeling class, with B1 and B3):** `Let`, `ParBind`, and `Match`-arm
  bindings were inserted into the flat `Walker.bindings` map and never removed
  when their lexical scope ended, so they leaked past scope. For a name shared
  between a param/outer binding and an inner **branch-sibling** binding — e.g.
  `(if c (let [a (gcells g)] …) (consume a))`, where the then-branch inner `let`
  binds `a` and the else-branch `(consume a)` means the PARAM `a` — the walker
  resolved the post-scope use to the STALE inner `BindState`. Because the inner
  state is a `Projection`/`Fresh` origin (not the param `Root`), `param_root`
  returned `None`, `classify_param_use` never fired, and the param that should
  widen to `Owned` stayed `Borrowed`: **a narrowing BELOW truth on the
  ABI-bearing `param_modes` half — a SOUNDNESS issue (ABI-half), not precision.**
  `MonoExpr` carries no alpha-rename guarantee (names copied verbatim by
  `from_expr`; the `case`/`cond` macros literally reuse `__case__`), so the walker
  may not rely on binding-name uniqueness (spine "The boundary" invariant).
  **As-built cure:** each binding scope pushes a `ScopeFrame`
  (`Vec<(Symbol, Option<BindState>)>`) that saves, per bound name, the value
  `bindings` held **before** insertion (the shadowed prior, or `None` if unbound);
  `restore_frame` replays it in reverse on scope EXIT (`Some(old)` reinserts,
  `None` removes). Params are the base frame, never restored away. `Let`/`ParBind`
  each push one frame; **each `Match` arm gets its OWN frame** (subsuming the
  arm-leak half of F4 — an arm binding is restored before the sibling arm and the
  post-match uses are walked). This makes `bindings` faithfully model lexical
  scope: a branch-sibling shadow no longer leaks, so the else/sibling use resolves
  to the param `Root` and `param_modes` widens to truth (`Owned`). Guarded by
  `transfer::tests::{branch_sibling_shadow_does_not_narrow_param_shadow_first,
  branch_sibling_shadow_does_not_narrow_param_use_first,
  match_arm_binding_does_not_leak_past_arm}`. **Confinement (`confinement.rs`) gets
  the same discipline for precision + anti-recurrence** (a `ConfineFrame` shadows
  the colliding `param_idx` entry on scope entry, restores on exit): its
  scope-unawareness over-approximated toward `spark_ops=true`/Crossing (the sound
  ⊤ direction, NOT a Wave-11 blocker), so this only tightens precision — a
  shadowed inner name no longer false-matches the param
  (`confinement::tests::shadowed_param_name_does_not_false_match_in_spark`).
  **Interaction with the F1 drain (§13.6(g)):** the drain now runs BEFORE the
  frame restore (enclosing + this-scope bindings still live) and re-walks each RHS
  with the binding-being-drained temporarily restored to its shadowed prior — the
  correct sequential-let reading (a binding is not in scope while its own RHS
  evaluates). The `(name, ctx)` dedup is **downgraded to a defensive termination
  cap** (see §13.6(g)).
- **(e) Fixpoint re-entry rides harvested `DepSet` edges, not `call_graph_edges`**
  (§13.3's ruling; amends §3.2's "caller lookup inverts the cluster's `callees`
  edges" — the inversion now inverts the walk-harvested instance-grain set;
  `call_graph_edges` seeds order only).
- **(f) Anchor drift recorded:** §3.1's `program.rs:1901/:1999` are now
  `:1986/:2082–2084` post-S101; the seam and ordering are unchanged.
- **(j) Closure/spark capture is an escape edge driven by the FREE-VAR set, not
  context propagation** (Wave 11 B3.4 cure; FIXME 0523 — the second pass5
  classifier gap after 0520, a hard UAF). **Root cause:** §3.3's `Lambda` case
  walked the closure body with the `EscapingCapture` context and relied on that
  context propagating to each captured use. But context does **not** propagate
  through an `Apply`: at a call the args are re-classified `Arg{mode, flow}` from
  the callee summary, so a captured value used as a **`Borrowed` argument** (or
  any non-escaping sub-position) inside an escaping closure lost its escape edge —
  `(defn f [x] (let [r (Box x)] (fn [] (readonly r))))` marked `r`'s aggregate
  `escapes=false`, and `(defn f [x] (fn [] (readonly x)))` inferred `x` as
  `Borrowed`. B3.4 (stack-alloc for `NoEscape` scalar-payload aggregates, the
  first hard consumer) dangled on it — a use-after-free the RC-balance guards
  cannot catch. The DIRECT capture shapes (`(fn [] r)` / `(fn [] x)`) were already
  correct — the drain (§13.6(g)) flips a directly-captured `Fresh` local, and a
  directly-captured param widens through `classify_param_use` — which is why the
  gap hid behind the minimal repro. **As-built cure:** capture is an escape edge
  **independent of use-position** (spine R6). When a `Lambda` escapes, the walker
  computes the closure's **capture set** = the free variables of its body
  (`transfer.rs::free_vars`, proper lexical scoping over inner `let`/`par`/`match`/
  nested-`Lambda` binders minus the lambda's own params; over-approx is sound,
  under-report is not, so binders save+restore) and runs
  `classify_capture_escape` on each: a param-rooted capture widens
  `Owned`/`Retained` (the escape rides the ABI — the inter-procedural half needs
  **no new summary carrier**: a caller passing a fresh value to that
  `Owned`/`Retained` position escapes at the call site through the existing
  `UseCtx::Arg` classification); a `Fresh` local pushes to the escaped worklist so
  the enclosing drain flips its allocation's escape fact; a borrowed
  view/alias-of-a-local materializes at its root (§4.2 rule 5, followed
  recursively). The `EscapingCapture` body walk is **retained** (nested escaping
  allocation site facts / value-uses / deps) — the free-var pass is additive and
  monotone with it. **`LaunchContinue.launched` gets the same free-var capture
  pass** (suspension capture, R6 — same through-arg gap). `ParBind` bindings stay
  non-escape (§4.3 — a joined spark's frame-escape is a STRAND fact, handled by
  confinement, not a capture escape). **Precision preserved:** a closure that does
  NOT escape (bound-and-discarded locally, walked `Neutral`) triggers no free-var
  pass ⇒ its captures stay `escapes=false`/`Consumed`, so B3.4's stack-alloc win
  survives (verified: `non_escaping_local_lambda_does_not_escape_capture`,
  `lambda_param_shadows_capture_no_spurious_escape`). Guarded by the
  `transfer::tests` capture-escape matrix (intra direct/through-borrow-arg/param,
  inter-procedural via callee summary, nested, suspension, + the two over-widen
  pins). **Cache:** value-only change to escape site facts + `param_modes`/
  `param_flow` within the same schema; **rides `CACHE_SCHEMA_VERSION` 14** (the
  0520 S102 summary-meaning bump) — serde shape unchanged, and no ACTIVE
  cross-module consumer is exposed (B3.2 reads `result`, which this cure does not
  move; the fields it does move — escape site facts, `param_modes`/`param_flow` —
  have no active consumer with B3.4's flag OFF and increment-I summaries
  emitted-but-unconsumed ⇒ codegen behaviour-neutral, golden-CLIF empty). B3.4
  activation (the flag flip) is a separate future change-set.
- **(k) A lambda body is its OWN frame — its tail/return allocations escape the
  lambda frame** (Wave 11 B3.4 cure; FIXME 0524 — the THIRD pass5 classifier gap
  after 0520 result-mode and 0523 capture, a hard UAF). **Root cause (the class):**
  the escape analysis was **cluster-centric** — it modeled named-`defn` frames
  (via the top-level body walk in `UseCtx::Return` + the result-mode composition)
  but walked an ANONYMOUS lambda body as a sub-expression of the *enclosing*
  frame, in the context tied to whether the closure VALUE escapes
  (`EscapingCapture` if the lambda value escapes, else `Neutral`). This conflates
  two DISTINCT frames: "the closure value escapes the enclosing frame" (the
  capture axis, §13.6(j)) vs "an allocation created in the lambda body escapes the
  lambda frame" (this rule). A lambda whose value does **not** escape — passed as
  a `Borrowed` arg to a HOF (`(apply-it (fn [y] (Some y)) 7)`), or
  bound-and-discarded — had its body-return `(Some y)` walked `Neutral` ⇒
  `escapes=Some(false)`; the anonymous lambda never appears in the cluster
  summaries, so its body-return never got the escape edge its named-`defn` sibling
  gets. B3.4 (stack-alloc for `NoEscape` scalar-payload aggregates) then
  stack-allocated `(Some y)` in the lambda frame; once the lambda/HOF frame pops
  the returned value dangles (UAF, `runtime panic: match failed`). **HOF-flow
  (edge 4) needs NO new carrier:** the escape is intrinsic to the lambda
  body-return (edge 2) — the allocation carries `escapes=true` at its own site, so
  a HOF returning `(f x)` merely propagates an already-escaping value; the
  interprocedural half rides the existing `ModeSummary`/site facts unchanged.
  **As-built cure:** the `Lambda` walk splits on whether the closure value
  escapes. When it does, the body is walked `EscapingCapture` (unchanged — its
  allocations already escape via `escapes()==true`) atop the §13.6(j) free-var
  capture pass. When it does **not**, the body is walked in `UseCtx::Return` (its
  own frame's return) with an **ISOLATED escaped worklist**
  (`std::mem::take(&mut self.escaped)` / restore): lambda-LOCAL fresh bindings
  still drain WITHIN the body (their own `Let`/`ParBind` scopes run during the
  walk), but a capture of an ENCLOSING fresh local must NOT bubble to the
  enclosing drain — capture-escape is gated on the lambda VALUE escaping
  (§13.6(j)), so a non-escaping lambda's captures stay in-frame. The only escaped
  entries left after the body walk are those enclosing captures; restoring `outer`
  discards them. **The complete outflow-edge model (edges 1–7, spine §2.2 + R6):**
  (1) named-fn return — top-level body walk in `Return` + result-mode
  (`return_direct_param_is_alias`, `return_embedded_in_constr_escapes`,
  `named_fn_return_edge_reconfirmed_after_0524`); (2) lambda body-return — THIS
  rule (`lambda_body_return_constructor_escapes_when_value_discarded`,
  `…_veclit_escapes`, `…_through_let_tail_escapes`); (3) closure capture —
  §13.6(j) free-var pass (`intra_*_capture_*`); (4) HOF-mediated flow — rides
  edge 2 (`lambda_body_return_via_hof_borrowed_arg_escapes`); (5) store into an
  escaping aggregate — `Field{flow}` + drain (`intra_direct_closure_capture_of_local_escapes`,
  `binding_mediated_escape_widens_flow_and_escape`); (6) spark/suspension capture —
  §13.6(j) `LaunchContinue` free-var pass (`suspension_capture_through_borrow_arg_escapes`);
  (7) nested compositions — `nested_lambda_body_return_alloc_escapes`,
  `lambda_body_return_in_match_arm_escapes`, `nested_closure_capture_escapes`.
  **Precision preserved (B3.4's win survives):** a non-escaping lambda that
  returns a bare param/scalar allocates nothing that escapes
  (`lambda_body_return_scalar_no_spurious_escape`); a captured enclosing local
  returned from a non-escaping lambda stays in-frame
  (`non_escaping_lambda_returning_captured_local_stays_in_frame`,
  `non_escaping_local_lambda_does_not_escape_capture`); a genuinely-frame-local
  aggregate stays `escapes=false` (`binding_local_fresh_aggregate_does_not_escape`).
  The cure is **monotone-sound** — it only flips lambda-body allocations
  `false`→`true` (never the reverse) and never moves `param_modes` at the closure
  boundary (a constructor field-store is `Owned` on both paths). **Cache:**
  value-only change to escape site facts (+ advisory `param_flow` widening);
  **rides `CACHE_SCHEMA_VERSION` 14** (the 0520/0523 summary-meaning bump) — serde
  shape unchanged, no ACTIVE cross-module consumer with B3.4's flag OFF
  (emitted-but-unconsumed ⇒ codegen behaviour-neutral, golden-CLIF empty). B3.4
  activation (the flag flip) is the separate next change-set that re-runs the
  killer/win/adversarial + full-corpus behavioral suite.

### 13.7 The Principle-23 scenario space (the 0497 rider) — submodule × scenario class

**0497 staging.** The de-pool rides B2 in three steps: (i) a **mechanical relocation
commit** (the pooled `traits/tests.rs` 41 tests + `primitive_dispatch_tests.rs` move
to sibling per-submodule test modules — `monomorphise`, `impl_check`, `dispatch`,
`type_resolve`, `registry` — content-unchanged) lands with CS-1's window, before new
strategy tests, so attribution exists when the gap-fill starts; (ii)
**`monomorphise.rs` gap-fill** (instantiation matrices: value-position, FQ-reference,
≥2 instantiations — the 0488-class crate-side pins) rides CS-3 (the memo/instance
work touches those seams; coordinate with `/qa`'s 0488 isolation, which may add the
attribution test first); (iii) **scheme/cluster/scope negatives**: `cluster.rs` SCC
negatives ride CS-3 (the fixpoint exercises SCC shapes); `scheme.rs`/`scope.rs`
negatives are the capacity-gated tail, re-deferred with rationale if untouched
(0497's own terms). The new `ownership/` cluster is born compliant — per-submodule
test modules from CS-1 onward, scenarios through the crate facade (`check_forms` +
`TestFixture`) wherever facade-reachable.

**The matrices `/dev` derives from (a design that does not name its matrix has not
laid the strategy bare):**

- **`classify.rs` (CS-1).** *Complexity matrix* — Apply-shape × `resolved_call`, all
  eight §2.1 rows: {`Var`+`SigDispatch`, `Var`+`TraitMethod`, `Var`+`BuiltinFn`,
  `Var`+`None`→chain-resolves-`UserFn`, `Var`+`None`→`Primitive`/`Constructor`/
  `PlatformEffect`, `Var`→let/param binding (closure value), non-`Var` callee,
  `AutoCurry`} → {static-moded, declared-leaf, pinned-boundary, Decision-24}.
  *Edge* — imported callee through `Import`/`Reexport` chain; `PrimitiveExtern`
  (`sconcat`) ⇒ Decision-24; `Primitive` with `PrimitiveBody::Inline` vs `Extern`
  (0476 consumption); `Primitive` with NO declared facts ⇒ leaf-with-⊤. *Negative* —
  never moded for closure-valued/`AutoCurry` sites; `Copy` classifier: exactly
  {`Int`,`Bool`,`Float`} in, `String`/`Vec _`/ADT/`Fn` out; memo determinism.
- **`transfer.rs` (CS-2).** *Mode/flow join matrix* — use-shape × callee fact:
  {borrowed handoff (non-widening — the load-bearing negative), owned handoff
  (widen + callee's `ParamFlow` applied), Decision-24 site (widen + `Retained`),
  constructor field-store (`Owned`), declared-`Borrowed` leaf (no widen, no escape —
  rule 5 stops), absent-fact leaf (widen + escape)} plus multi-site joins
  (`Borrowed ⊔ Owned = Owned`; `Consumed ⊔ IntoResult ⊔ Retained` full triangle).
  *Escape-edge matrix* — all §2.2-spine rules: return direct / return embedded in
  `ConstrADT` / store into escaping aggregate / escaping-closure capture /
  non-escaping closure capture (negative) / `ParBind` joined (non-escape) /
  `LaunchContinue.launched` (escape) / deferred continuation (escape) /
  owned-handoff opaque edge (escape) / borrowed handoff (non-escape, negative).
  **Lambda body-return escape (§13.6(k), FIXME 0524 — the complete outflow-edge
  audit):** lambda body-return constructor when the closure value is
  discarded (edge 2) / returned through a BORROWING HOF (edge 4, rides edge 2) /
  VecLit body-return / lambda-local `let`-tail body-return (drains within the
  isolated frame) / constructor in a match-arm returned from a lambda (edge 7) /
  lambda returning a lambda that constructs (nested edge 7) — each ⇒ the body
  allocation `escapes=true`. **Over-widen pins:** a non-escaping lambda returning
  a bare param/scalar allocates nothing that escapes / a captured ENCLOSING local
  returned from a non-escaping lambda stays in-frame (the isolated-worklist guard —
  the B3.4 win) / named-fn return edge unchanged (edge 1 re-confirm).
  **Binding-mediated escape (§13.6(g)):** let-bound `Fresh` aggregate returned
  (single level) / FLAT fold-chain `[a (Some x) b (Some a)]` returned (the
  fixpoint-drain row — F1) / never-escaping local aggregate (negative, precision)
  / `ParBind`-bound aggregate returned (the strand-vs-frame row — F1).
  **Lexical-scope discipline (§13.6(i), F4 — the ABI-half soundness rows):**
  branch-sibling shadow, shadow-walked-FIRST ⇒ param must widen `Owned` in the
  sibling branch (the load-bearing negative — narrows `Borrowed` pre-cure) /
  branch-sibling shadow, use-walked-FIRST (the both-orderings guard) / match-arm
  binding shadowing a param must not leak into the sibling arm / self-alias
  `(let [a a] …)` terminates (the `case`-macro shape — dedup defensive cap).
  *Projection-depth matrix* — proj-of-`Borrowed`-param (root = param), chained
  projection collapses to ONE root (depth ≥ 3), proj-of-`Owned`-local (root =
  local), match-arm binding, accessor call with `ProjectionOf` summary
  (interprocedural root composition), the §13.6(d) shadowed-root ⇒ `None` rows at
  BOTH the `Let` and `Match` seams (F2 mirror, single-sourced) + the unshadowed
  precision twins, `vec-get` declared row, escape-of-borrowed-proj
  ⇒ materialization fact at the edge (rule 5), return-proj-of-param ⇒
  `ProjectionOf(i)`, return-param ⇒ `AliasOf(i)`, return-proj-of-LOCAL ⇒ local
  escapes + `Fresh`, the §13.6(c) mixed-path joins, the §13.6(d) shadowed-root ⇒
  `None` row. *Negative* — `result_unique` never set (increment-I pin); no RC-op
  fact at any projection extraction (rule 3).
- **`fixpoint.rs` (CS-3).** *SCC-shape matrix* — {straight chain (1 visit each in
  reverse-topo), self-recursive (≤2 visits), mutual 2-cycle, 3-cycle, mono-instance
  recursion (`reduce$…`↔`reduce-loop$…`), imported callee (boundary condition —
  never enqueued, negative)}. *Ordering/determinism* — scrambled seed order converges
  to the identical summary set (the §13.3 demotion pin); instances appended after
  templates. *Re-entry* — callee widens ⇒ exactly the harvested `DepSet` callers
  re-enter (negative: an unrelated cluster member is not revisited). *Termination* —
  adversarial widening chain bounded by O(Σ per-param lattice heights); **cap
  exhaustion resets the universe to the conservative ⊤** (`compute_cluster_with_cap`
  `cap=0` seam ⇒ every callable Owned/Fresh/Retained/spark-set, never a too-precise
  partial — FIXME 0512 blocker 4, §13.6(h)). *Memo* —
  hit skips the walk; template-module recompile drops entries; cross-module
  duplicate instances produce equal summaries (determinism pin). *Toggle* —
  env-set ⇒ driver returns at entry: zero summaries, zero facts, zero marks, memo
  untouched (§13.5, all four as negatives).
- **`confinement.rs` (CS-3).** *Strand-context matrix* — {plain body op = parent;
  `ParBind` binding RHS = potential-fork; lenient-eligible let-RHS / apply-arg =
  potential-fork (the over-approximation rows); `LaunchContinue` / IO-capture =
  deferred}. *Join matrix* — {all ops parent ⇒ `Confined`; any spark-side surviving
  op ⇒ `Crossing`; borrowed spark read with zero surviving ops ⇒ `Confined` (the F2
  shape — the S99 target, positive AND its widening twin where the spark
  materializes); callee `spark_op(i)` set ⇒ `Crossing`; deferred edge ⇒ `Crossing`}.
  *Propagation* — `spark_ops` transitive through a two-deep callee chain. **The
  transitive propagation is a DRIVER-LEVEL row** (`fixpoint::compute_cluster`,
  `fixpoint/tests.rs::transitive_spark_ops_propagate_caller_before_callee`): two
  callables, caller listed FIRST (processed before its callee), the caller must
  still inherit the callee's `spark_ops` — the worklist-fixpoint guarantee
  (FIXME 0512 blocker 2). The `confinement/tests.rs` unit rows pre-set the callee
  summary and so cannot catch the ordering defect; the driver row is the guard.
  *Negative* — emission never carries `Transferred` (collapse pin, §5.4); confinement
  never feeds back into modes (stratification pin, §3.2); a parent-only caller→callee
  chain stays `Confined` (no fixpoint over-widening). **Lexical-scope precision
  (§13.6(i), F4 — non-gating, over-approximation-toward-`Crossing` is sound):** a
  `let`/`ParBind`/match-arm binding shadowing a param name must not false-match the
  param via `param_idx` — a spark-side consume of the SHADOWED name leaves the real
  param's `spark_ops` clear (`shadowed_param_name_does_not_false_match_in_spark`).
- **`publish.rs` (CS-4).** *Placement matrix* — summary lands on `UserFn`-Concrete;
  `Constructor`/`PlatformEffect` stay `None` (negative); declared `Primitive` facts
  never overwritten by the pass (negative); staging vs live table mode
  (`SymbolTableAccess` both arms — cluster-atomic commit). *Round-trip* — serde:
  absent summary/facts deserialize to the conservative point; toggle-set output
  field-identical to stage-M (§13.5). *Marks/facts* — value-use mark set exactly for
  value-position references; site facts + provenance present on the stored
  `codegen_view` post-pass; H5 dump smoke (present under the env var, silent
  without).

## §14. Increment-II write-path change-set staging (S103 Phase 3 — Sprint 103 Block B1)

Authored by `/design` (cranelisp-typecheck) at S103 Phase 3, against
`sprints/SPRINT.md` Block B1 and the Phase-2 arch review. Block B1 — the
**typecheck-drain foundation + the write-path queries** — is the real gate on the
write-path mechanisms (reuse tokens + R5), which consume the S102-landed carriers
and this foundation, not the Block-A surfaces. Everything here elaborates §7
(the S100 write-path ruling, unchanged) and §§2–3 (the fixpoint); where §14 amends
an earlier section it says so.

**The one-line frame.** Increment II adds **no new typecheck-authored
`cranelisp-types` carrier**. The two write-path carriers it emits — `result_unique`
(summary half) and `unique_static` (site fact) — **already landed at S102 CS-A**
(§3.3, schema v12, emitted `false`/`None` throughout increment I). Increment II
starts *emitting them true* on a narrow proven subset; that is a **value change,
not a shape change**. The only genuinely-new carrier in the sprint is /arch's R5
`value_layout` predicate (§14.5), which is not typecheck-authored. This is the
Principle-8 payoff of the S100 "every dimension from day one" contract (§7): the
write path is a precision growth on a frozen shape.

### 14.1 The typecheck-drain quartet — disposition and sizing (Block B1 foundation)

The four accumulated typecheck debts that gate opening the crate for the write-path
pass. Sized and dispositioned; the write-path emission (§14.2) rests on a clean
foundation.

- **FIXME 0509 — generalization-ordering resettle debt.** *Target `/design`
  (typecheck); RESOLVED this pass — documentation-sufficient.* Recorded in its
  proper home, `design/typecheck/monomorphisation.md §5.1` (it is a
  generalization/scheme-writeback concern, not an ownership concern): the S102
  `resettle_polymorphic_schemes` is sound but compensates (O(n²)) rather than
  curing the 0344 writeback-before-forward-helper-tie root cause, and carries a
  **reverse-definition-order under-tie gap** (no repro today). **Not a write-path
  blocker** — pass5 reads *converged* schemes at the finalisation seam (§3.1),
  after all bodies and all re-settles. The two O(n) cures (topo-order the per-form
  generalization over the harvested `call_graph_edges`; or defer the 0344
  writeback to finalize) are named for a future promotion; a `/qa` reverse-order
  boundary test is requested so the gap is *tested*, not latent. **Sizing:
  doc-only this sprint.**
- **FIXME 0511 — pass5 session-memo threaded field.** *Target `/design`; RESOLVED
  this pass — keep option 2 (in-pass memo), defer option 1 (session-threaded
  field).* The §6 memo is a `DashMap` on the checker env, but `TypeCheckEnv` is
  constructed fresh per `check_forms` and borrows all its state, so a
  cross-invocation memo would have to be a session-owned `&'a DashMap` threaded
  from `int` — a cross-crate signature change. **Ruling: not worth the plumbing
  for increment II.** §6's own property holds — determinism makes the memo's
  absence a *re-compute cost, never a wrong result* — and the R3 machinery is not
  yet consuming summaries (Wave 9+), so the cross-invocation fast path has **no
  live consumer to accelerate**. The in-pass memo (S102 CS-3 landing) converges
  each callable once per compile; repeated mints within one compile are map hits.
  **Increment-II caveat (new):** the uniqueness stratum (§14.2) adds a per-callable
  greatest-fixpoint pass, so per-turn re-inference cost grows — **routed to `/qa`**
  to fold the uniqueness-stratum cost into the L-D1 turn-latency lane (§3.5); if
  that measurement ever shows re-inference material across REPL turns, option 1
  (the session-owned memo) is the pre-designed upgrade, `int`-side, cite the
  `TypeCheckEnv::new`/`new_with_staging` constructor signature. **No
  `cranelisp-types` edit either way** — the memo is typecheck-internal state.
  **Sizing: doc-only this sprint** (the in-pass memo already ships).
- **FIXME 0513 — qualified-lookup phantom-child gap.** *Target `/typecheck`
  (the impl skill — actioned by `/dev` in Phase 5); design specified here.* Not
  an ownership concern per se; it is in the B1 drain because the crate is open and
  it is a live resolution-correctness debt that a future qualified-name path not
  flowing through `int`'s `finalize_cluster` gap seam would re-expose.
  **The seam:** `Checker::lookup`'s `name.find('/')` arm
  (`crates/cranelisp-typecheck/src/checker.rs` ~1188–1226) probes two candidates
  for `mod/sym` — child-of-current (`{current}.{module_part}`) then absolute
  (`{module_part}`) — and the gap-selection tail surfaces the **phantom child
  gap** (`user.primitives/nosuchfn`) even when the **absolute module is loaded but
  the member is absent** (a definitive member-not-found with no gap). **Fix design
  (option (b), the narrower cut): suppress the child-probe gap when the
  absolute-path candidate resolves the module but not the member.** When
  `resolve_qualified(module_part, sym)` returns `Ok((None, None))` — module
  loaded, member absent — that is a definitive member-not-found and MUST win over
  the child probe's `ResolutionGap::SymbolTypechecked`. Prefer (b) over (a)
  (synthesising a `TypeError` naming the real module+member at the var span
  directly from `lookup`) as the minimal change: (b) removes the *misleading gap*
  without moving diagnostic authorship out of the existing `infer_var`/int seam,
  so the int-side `phantom_member_diagnostic` mitigation (S102 Wave 10a) stays as
  a belt-and-suspenders guard until the resolution reorder proves out and can then
  be removed. **Unit seam:** a `checker.rs` `#[cfg(test)]` case building a loaded
  absolute module with a missing member and asserting `lookup` yields the honest
  member-not-found (no phantom `<current>.<qualifier>` gap). **Sizing: small code
  change (`/dev`, Phase 5) + one unit test;** spec adjacency `spec/08-modules.md
  §8.6.4` (order-independence of qualified member-miss diagnostics).
- **FIXME 0510 — `neq-string` has no primitive entry.** *Target `/design`
  (backend); COORDINATED, not owned here.* Named for completeness: the
  §13.4 fact-table coverage claim's one filed gap. `neq-string` is shim-only
  (no `DefKind::Primitive` entry), reached via the `Eq.!=` `String` dispatch
  path, so pass5's `Apply` classification of `(!= s1 s2)` chain-follows to a
  missing entry ⇒ the Decision-24 default (args widen `Owned`) — a **precision
  loss only, monotone-sound**, asymmetric with `str-eq` (which is a registered
  entry). The classifier already encodes the correct `Borrowed` facts
  (transcribed under CS-B), so `/design(backend)`'s choice is (a) register
  `neq-string` as a `ring1` `PrimitiveDef` (restoring `==`/`!=` symmetry, assessed
  against the golden corpus / `extern_shims` invariants) or (b) accept the
  conservative default and amend §13.4 to name it a trait-dispatch leaf outside
  the declared-fact table. **No typecheck action either way** — the classifier is
  correct on both branches. Watch item for the write path: `neq-string`'s args
  being `Owned` rather than `Borrowed` never affects *uniqueness/reuse* emission
  (uniqueness is about the *result*, not the string comparands), so 0510 does not
  gate any increment-II query.

### 14.2 The write-path query emission — what pass5 newly emits in increment II

Two facts, both on carriers that already exist (§3.3, S102 CS-A):

- **`ModeSummary.result_unique: bool`** — the summary-half chaining discriminator.
- **`MonoExpr.unique_static: Option<bool>`** — the per-use-site static-uniqueness
  fact (present-but-never-`Some` in increment I; now `Some(true)` on proven uses).

Neither is ABI-bearing — both are in the **advisory half** (a `false`/`None` is
always sound; it degrades to the dynamic rc==1 check or to no-reuse). So the
write-path emission adds **no summary-diff-gate surface** (§5.4 compares
`param_modes` + `result` only, via `abi_eq` — §13.1 item 5), and the R3 machinery
is unaffected by whether uniqueness is emitted.

**The subset that earns `unique_static = Some(true)` (§7.2, restated as the
emission rule).** At a consuming use site of `v`, emit `unique_static = Some(true)`
iff all three hold:

1. **Provenance is a fresh unique root.** `v` is (i) a fresh allocation or the
   **`Fresh`**-result of a static call (read `result == Fresh` — a *binary* test,
   never the `AliasOf` index; see §14.4), (ii) a freshly-COW'd copy, or (iii) a
   param carrying a caller-side static proof (`result_unique` chained in) — **and**
   every other reference taken from `v` between birth and this use is
   `Borrowed`/projection-covered (rc-invisible by §4).
2. **Single syntactic consuming use** (flow-insensitive: count consuming-use sites;
   a projection read is not a consuming use). Multi-use / conditional-consume /
   loop-carried values need use-*ordering* (last-use), which is backend-local — they
   take the dynamic check (§7.1(a)), the mechanism built for them.
3. **Layout-eligibility at mono** (the *eligibility* axis, static; permission stays
   dynamic-or-proven — spine §10 item 5 two-axis separation): the concrete
   instantiation is in-place-layout-compatible.

**`result_unique = true` (the chaining bit, §7.2 clause 3).** A callable's summary
carries `result_unique = true` iff its returned value is (1)-fresh **inside the
callee** or an in-place-reused unique param — computed **intraprocedurally** from
the callee's own converged transfer state (the `Origin` working state the walker
already tracks — §13.6(c)), so a caller's clause-1(iii) proof re-emerges from the
call as a **bool read**, never an index read. `result_unique` is emitted `false`
throughout increment I and `false` whenever the proof does not hold — the sound
default.

**The uniqueness stratum — a third fixpoint stratum, stratified after modes and
confinement.** `result_unique` chains across the cluster (a callee's bit feeds a
caller's clause-1(iii)), so it is a per-cluster fixpoint, run **after** the
modes/escape/flow stratum and the confinement stratum converge (§3.2
stratification; nothing in modes or confinement reads `result_unique`, so the
stratification is exact). Its shape and soundness:

- **A must-property, greatest-fixpoint (co-inductive) iteration.** Uniqueness is a
  *must* (v must be unique). Init **optimistic** (`result_unique = true` for every
  cluster member), narrow to `false` on any return path that is not fresh /
  not-unique-chained, iterate to the greatest fixpoint. This is the **same
  "init-optimistic, move monotonically toward the conservative point" shape** as
  the modes stratum (which inits `Borrowed`/`Fresh` and widens toward `Owned`) —
  only the conservative point differs: **conservative = `false`** for
  `result_unique` (degrades to the dynamic check). Re-entry rides the same
  harvested `DepSet` edges as the modes stratum (§13.6(e)).
- **Cap exhaustion REFUSES, it does not reset** (§19.5, superseding this section's
  earlier per-stratum reset). A partially-converged greatest-fixpoint sits *above*
  its true fixpoint (too many `true`s) ⇒ unsound to publish. S121 collapsed the three
  per-stratum recoveries into one refusal: a uniqueness exhaustion publishes nothing
  for the whole cluster instead of resetting `result_unique` to `false` and dropping
  every `unique_static` site fact, and `fixpoint::conservative_site_facts` is deleted.
- **Site facts written in the one-shot post-convergence walk** (§13.6(b)):
  `unique_static = Some(true)` is annotated onto the `codegen_view`'s consuming-use
  nodes in the same annotation walk that writes `escapes`/`confined`/`provenance`,
  after all three strata converge. Budget unchanged: still annotation-only, no
  `Type` traffic (§3.4).

**Monotone soundness — absent facts ⇒ today's lowering.** Every write-path fact's
absent/false reading is exactly the increment-I (and pre-increment) behaviour: an
absent `result_unique`/`unique_static` (old cache, unconverged edge, toggle-off,
cap-reset) reads `false`/`None` ⇒ the backend takes the **dynamic rc==1 check**
(§14.3) or emits no reuse — never an unsound elision. The direction is one-way:
the analysis only ever moves a value *toward* `false`/`None` when it cannot prove
uniqueness, and the backend's default when it reads `false`/`None` is the safe
copy-or-check path. This is the same monotone-soundness the increment-I contract
established (§3.3, §13.5), extended to the uniqueness bit.

**Toggle-off (spine §6.2, §13.5) extends unchanged.** With `CRANELISP_NO_OWNERSHIP`
set, `pass5_ownership` returns at entry: no `result_unique` computed (⇒ default
`false`), no `unique_static` site facts (⇒ `None`), the uniqueness stratum never
runs. The differential oracle's byte-identity obligation holds on this crate's
outputs by construction — a write-path-off compile is field-identical to a
stage-M compile (serde: absent optional/default fields serialize away).

### 14.3 The dynamic rc==1 discriminator — the typecheck/backend handoff

The **general** write-path discriminator is the **dynamic rc==1 entry check**
(spine §4.3, §7.1(a); Koka/Roc drop-guided reuse, what today's `vec-set-copy`
mutate-in-place already is): one branch per *call*, copy-once-then-in-place. It is
**not a typecheck output** — it carries no ResultMode index, no summary field, no
site fact. The split of responsibility:

- **Typecheck provides *eligibility* (static) + the *proof* (where it holds).**
  Eligibility = layout-compatibility per instantiation, decided at mono
  (`unique_static`'s clause 3; §7.3). The proof = `unique_static = Some(true)` /
  `result_unique = true` on the narrow subset (§14.2). Where the proof holds, the
  backend **elides** the rc==1 check (proof ⇒ permission — §7.1(c)-refined).
- **Backend owns *permission* (dynamic) — the reuse mechanism itself.** Where
  typecheck emits no proof (`false`/`None`), the backend runs the rc==1 check at
  the call/drop site; the reuse token (function-local SSA maybe-null, **off the
  ABI** — spine §3.5, §7 constraint) threads a drop site to a same-layout alloc
  site intra-function. This is backend part 16 (`design/backend/ownership-codegen.md`),
  consuming typecheck's site facts, never the reverse. **There is no third
  mechanism**: §7.1(c)-refined *is* (a) with the check hoisted/elided by the proof,
  and uniqueness never enters the ABI (R4).

So typecheck's increment-II contribution to the general discriminator is purely
*subtractive on the check* — it removes a dynamic branch where it can prove the
branch's outcome, and is silent (⇒ the check runs) everywhere else. The backend's
reuse machinery is complete without any typecheck emission; the emission is an
optimisation on top.

### 14.4 FIXME 0521 trigger verdict — S103: DEFERRED. **Discharged S121 (§19.2).**

**The Phase-2 conditional (restated):** /design(typecheck) lands the `ResultMode`
⊤ element (`AliasOfAny`, monotone-widening) in the B1 carrier change-set + a
`CACHE_SCHEMA_VERSION` bump **iff** the static-uniqueness subset design introduces
a consumer that reads the `AliasOf` **index** (the multi-distinct-param may-alias
case); else 0521 stays deferred until the reader arrives.

**S103 verdict: no index-reader was introduced by increment II, so 0521 stayed deferred.**
The five points below record why that was right for the write path and remain accurate about
it.

**S121 correction — the trigger fired from the other side, and the conditional was too
narrow.** The reader that arrived is not a new write-path consumer; it is the **producer**,
which has read the `MayAliasOf`/`AliasOf` index since increment I at `walk_apply`'s result
composition (point 4 below records the read and then dismisses it as "never acted on"). It is
acted on: the composition is what publishes the caller's own `result`, and taking one
representative argument makes that publication untruthful and the iteration non-monotone
(§13.6(c), §19.1). The ⊤ element lands as `ResultMode::MayAliasAny` under the user approval of
2026-09-07, with `CACHE_SCHEMA_VERSION` 26→27; §19 is the design and 0521 closes on it. The
name differs from this section's `AliasOfAny` because the `AliasOf` prefix is reserved for
unconditional claims (§3.7's reservation clause) and the new point is the join of conditional
ones.

The S103 reasoning, for the write path it was about:

1. **The subset's provenance clause admits only `Fresh` results — `AliasOf(i)` is
   excluded by construction.** §14.2 clause 1(i) / §7.2 clause 1(i) require the
   unique-candidate to be a *fresh allocation* or a **`Fresh`-result** of a static
   call. An `AliasOf(i)` result aliases param `i`, whose uniqueness is
   *call-site-dynamic* (R4) — not a statically-nameable unique root — so it is
   **not admitted** into the unique-value set. The subset therefore never chases an
   alias provenance for uniqueness, and never needs the aliased param's index.
2. **The chaining discriminator is a bool, read binary.** A caller proving
   clause-1(iii) reads the callee's `result_unique: bool`, and clause-1(i) reads
   `result == Fresh` (a *binary* `Fresh`-vs-not test — the same read the live
   increment-I borrow-elision consumer `return_is_fresh_by_summary` already makes).
   Neither reads `AliasOf(k)`.
3. **`result_unique` is computed intraprocedurally, not from a callee's index.**
   A callable sets `result_unique` from its **own** converged `Origin` state
   (fresh-inside / reused-unique-param — §14.2), not by reading another summary's
   `AliasOf` index. No cross-summary index read arises in its computation.
4. **The only `AliasOf`-index arithmetic that exists — `walk_apply`'s
   `AliasOf(k) → arg_origins[k]` result-mode composition — is unchanged
   increment-I machinery whose sole *acting* consumer remains the binary
   `result == Fresh` gate** (0521's own finding: a multi-param body is an
   `if`/`match`, never a direct `Apply`, so its codegen never trusts the specific
   index). The write path adds no consumer that *acts* on the index `k`.
5. **The write-path mechanisms read no index either.** Reuse tokens key on layout
   (intra-function, off-ABI); R5 keys on `value_layout(ty)` (§14.5); the dynamic
   rc==1 check reads nothing from `ResultMode`. None reads `AliasOf(k)`.

**The named future trigger is outside increment II's committed floor.** 0521's own
recommendation is to co-land the ⊤ element with "the first backend consumer that
reads the `AliasOf` INDEX (rather than the binary `Fresh` test) — part 12/16
borrow-elision keyed off the specific param." That per-index borrow-elision
refinement is a backend part-12/16 item, **not** in the B1/increment-II committed
floor (reuse tokens + R5 + the static-uniqueness subset). **0521 was the durable
record and did not action in S103; it actions in S121 and closes on §19.** The clause this
section closed with — "the 0520 lowest-index representative is sound for every live
consumer" — is **falsified** (§13.6(c)); the sentence is retained here only so the
falsification has its subject. Monotone-soundness of the add held as predicted: the new
point only ever widens a value *away from* `Fresh`, so it lands additively, with the schema
bump in its own change-set (26→27, §19.9).

### 14.5 Shared value layout and the checked declaration view

Typecheck's `Copy` classifier and backend value flattening consume the same
`cranelisp-types` layout algorithm. Their agreement is safety-critical: copying
an unflattened heap object without an RC increment can free it prematurely.
The shared algorithm owns scalar bases, Vec exclusion, the single-constructor,
exactly-one-concrete-field restriction, recursion and word limits; typecheck
does not reproduce these rules.

`ownership/fixpoint.rs::checked_value_layout` supplies
`TypeCheckEnv::probe_module_entry_owned` to
`cranelisp_types::value_layout_with_lookup`. Both consumers use this private
adapter: `compute_cluster_with_cap` classifies Copy when the layout is present;
`UniqClusterEnv::layout_eligible` permits reuse only for String/ADT values whose
layout is absent. Scalars and functions remain ineligible for heap reuse.

A present staged binding takes precedence even when its layout is ineligible.
Only an absent staged key falls through to published metadata; nested types in
other modules use their published declarations. The owned lookup releases each
storage borrow before recursive layout inspection. No temporary table or world
is materialized.

The two `ownership/fixpoint/tests.rs` tests
`copy_layout_uses_staged_declarations` and
`uniqueness_layout_uses_staged_declarations` observe these consumers separately,
including both precedence directions, missing-key fallback and a nested type
in another module. The declaration-access correction changes neither layout
rules nor the live ownership-ABI refusal or cache schema; the exact boundary
and composed evidence are governed by
[the approved API packet](../arch/s121-staged-value-layout-api.md).

### 14.6 CS staging + acceptance seams (Phase-5 handoff)

The increment-II typecheck change-sets, in dependency order, each landing with its
Principle-23 scenario matrix in the same commit and building on the S102
`ownership/` cluster (`classify.rs`/`transfer.rs`/`fixpoint.rs`/`confinement.rs`/
`publish.rs`):

- **CS-II-0 — the drain quartet** (Block B1 foundation, §14.1). 0509 + 0511
  doc-only (landed this pass); **0513** is the one code change — the
  `checker.rs::lookup` qualified-arm reorder + its unit test. Order-independent of
  the query CSes; lands first so the foundation is clean.
- **CS-II-1 — the uniqueness stratum + `result_unique`** (`fixpoint.rs` +
  `transfer.rs`). The third stratum (greatest-fixpoint, init-optimistic-true,
  conservative-`false`, `DepSet` re-entry, cap-reset-to-`false`); the
  intraprocedural `result_unique` computation from converged `Origin` state.
  *Unit seam:* `fixpoint.rs`/`transfer.rs` `#[cfg(test)]` — the pure transfer/
  fixpoint functions with `TestFixture` + hand-built `MonoExpr` bodies (the §11
  testability pin). *Scenario classes:* fresh-return ⇒ `result_unique = true`;
  aliased/projected-return ⇒ `false`; chaining across a two-call cluster;
  recursive cluster greatest-fixpoint; cap-exhaustion ⇒ all-`false` (the
  `compute_cluster_with_cap(cap=0)` seam extended to the uniqueness stratum);
  toggle-off ⇒ stratum never runs.
- **CS-II-2 — `unique_static` site-fact emission** (`transfer.rs` + `publish.rs`).
  The §14.2 three-clause subset rule, annotated in the one-shot post-convergence
  walk. *Unit seam:* `transfer.rs`/`publish.rs` `#[cfg(test)]`. *Scenario classes:*
  fresh single-use ⇒ `Some(true)`; multi-use ⇒ `None` (the load-bearing negative);
  conditional-consume ⇒ `None`; projection-read-is-not-a-consume; freshly-COW'd
  copy ⇒ `Some(true)`; layout-ineligible instantiation ⇒ `None`; cap-reset ⇒
  `None`.
- **CS-II-3 (rides B3) — the `Copy` classifier's R5 clause** (`classify.rs`).
  Delegates to /arch's `value_layout` when it lands (§14.5); until then the
  scalars-only classifier is unchanged. *Unit seam:* `classify.rs` `#[cfg(test)]`
  — the `Copy` predicate over `ConcreteType` (exactly `{Int,Bool,Float}` pre-R5;
  the delegation-to-`value_layout` rows post-R5).

**How Phase-5 /dev + /qa verify each change-set (unit seam × gate/guard):**

| Change-set | /dev unit seam | /qa gate / guard |
|---|---|---|
| CS-II-0 (0513) | `checker.rs::lookup` qualified-arm unit test (loaded-module member-miss ⇒ honest not-found, no phantom child gap) | e2e: qualified-ref-missing-member diagnostic names the real module (existing `display_exact.rs::qualified_ref_missing_member_diagnostic_names_real_module` stays green when the int mitigation becomes redundant) |
| CS-II-1 (`result_unique`) | `fixpoint`/`transfer` `#[cfg(test)]` stratum + chaining + cap-reset matrix | **II-G2** (reuse hit-rate ≥50% on F4; counter movement is the attribution prerequisite) — the chained-write shape `result_unique` feeds |
| CS-II-2 (`unique_static`) | `transfer`/`publish` `#[cfg(test)]` subset matrix (single-use positive + multi-use/conditional negatives) | **II-G2/II-G3** (F4 floor: median wall ≤ 2× serial); **L-C3** reuse-corruption fence (reuse fired on a non-unique value ⇒ corruption — the differential-off + behavioral + ASan legs) |
| CS-II-3 (R5 `Copy`) | `classify.rs` `#[cfg(test)]` `Copy`-over-`ConcreteType` (delegation to `value_layout`) | **II-G1** (R5 witness via the **F2v single-ctor fixture**: rc_inc collapses <1% of B2; F2v N-worker wall < serial — the first parallel-must-pay gate) |

The differential oracle (`CRANELISP_NO_OWNERSHIP`) is byte-identical off throughout
(spine §6.2; §14.2 toggle pin). II-G5/G6 re-run the I-G4/I-G5/I-G6 non-regression +
overhead bars including F2v serial.

### 14.7 Dependencies / coordination — the seam contracts

- **From /arch:** (1) the R5 `value_layout` predicate carrier + `VALUE_LAYOUT_MAX_WORDS`
  in `cranelisp-types/src/heap.rs`, landing **in the B3 change-set** with the schema
  bump reconciled to the live value (§14.5 — 14→15, not the plan's stale 12→13);
  single-sourced, consumed by this crate's `Copy` classifier and the backend's
  `HeapCategory::Value` arm. (2) The 0521 verdict is **NO** (§14.4) — /arch takes
  no action on the ⊤ element this sprint; the FIXME stays the durable record.
  **No other new typecheck-authored carrier** — `result_unique`/`unique_static`
  already landed at S102 CS-A.
- **From /design(backend):** (1) the **dynamic rc==1 discriminator** is
  backend-owned (§14.3) — the reuse-token mechanism (off-ABI, spine §3.5) consumes
  this crate's `unique_static`/`result_unique` site facts to *elide* its entry
  check where the proof holds, and runs the check everywhere else; the seam
  contract is "absent proof ⇒ run the check" (monotone). (2) **FIXME 0510**
  (`neq-string` entry) is /design(backend)'s call (§14.1); either branch leaves
  the classifier correct and gates no increment-II query.
- **To /qa:** (1) fold the **uniqueness-stratum re-inference cost** into the L-D1
  turn-latency lane (§14.1, 0511 caveat) — the trigger for the deferred
  session-memo. (2) The **L-C3 reuse-corruption fence** and **II-G1–G4** perf lanes
  are the acceptance gates (§14.6 table); F2v is the honest R5 witness. (3) A
  **reverse-order generalization under-tie boundary test** (§14.1, 0509) pinning
  the known gap as tested, not latent.
- **To /int:** the R3 summary-diff gate (`abi_eq`, §13.1 item 5) is **unaffected**
  by the write-path emission — `result_unique`/`unique_static` are advisory-half,
  outside the ABI surface `abi_eq` compares, so no gate widening is owed for
  increment II.

## Next skills

- `/arch` — take the **FIXME 0521 verdict: NO** (§14.4) — no ⊤ element, no schema
  bump for it in B1; author the R5 `value_layout` carrier in the B3 change-set with
  the schema bump reconciled to the live value (§14.5). Verify the §14.1/§14.6
  foundation at the Phase-3 exit gate.
- `/dev` (cranelisp-typecheck) — implement CS-II-0 (the 0513 `lookup` reorder +
  unit test) → CS-II-1 (uniqueness stratum + `result_unique`) → CS-II-2
  (`unique_static` emission) → CS-II-3 (R5 `Copy` clause, rides B3) per §14.6 with
  the scenario matrices.
- `/design` (cranelisp-backend) — the dynamic rc==1 reuse-token mechanism consumes
  §14.2's site facts (elide-on-proof, check-otherwise, §14.3); resolve FIXME 0510.
- `/qa` — L-C3 + II-G1–G4 (F2v witness); the L-D1 uniqueness-stratum cost lane
  (0511 trigger); the reverse-order under-tie boundary test (0509).
- `/sprint` — the write-path emission adds no ABI surface and no new
  typecheck-authored carrier; sequence CS-II-0 first (foundation), CS-II-1/2 on the
  S102 `ownership/` cluster, CS-II-3 riding B3's `value_layout`.

### Next skills (S102 — superseded by the §14 list above for S103)

- `/arch` — verify the §13.1 needs list at the Phase-3 exit gate and author CS-A
  (the v11→v12 `cranelisp-types` change-set, riding 0476); rule on item 12 (toggle
  relocation).
- `/dev` (cranelisp-typecheck) — implement CS-1→CS-4 per §13.2 with the §13.7
  matrices; carry the 0497 rider stages (i)–(iii).
- `/dev` (cranelisp-primitives, backend-paired) — CS-B fact-table declaration per
  §13.4, after 0504 resolves the audit row.
- `/design` (cranelisp-backend) — ownership-codegen consumption unchanged; note
  §13.6(b) (facts arrive post-convergence, one write) and §13.6(d) (symbol-keyed
  provenance + shadow rule) as consumption pins.
- `/qa` — L-D3e per-row generation depends on 0504; H5 (CS-4) unblocks L-D3f/I-G3;
  I-G5/I-G6 run at the B2 seam per Q3 pin 2.
- `/sprint` — sequence CS-A → {CS-B, CS-1} → CS-2 → CS-3 → CS-4; the `/int`
  summary-diff-gate widening rides after CS-4 (or with it, same wave).

---

### Next skills (S100 original — superseded by the §13 list above for S102)

- `/design` (cranelisp-backend) — author `design/backend/ownership-codegen.md` (parts 12–16)
  against the spine, consuming §8.4/§12 items 1–4 of this doc as its typecheck-side inputs.
- `/arch` — evaluate FIXME 0467 (summary-shape extension) alongside the §3.3 carrier design;
  no action needed before the implementing sprint.
- `/qa` — author the verification plan (parts 17–18) inheriting spine §9 + §12 items 5–8 here.
- `/sprint` — sequence at close per spine §5.7: R3 machinery → increment I → increment II.

---

## §15. The vec-assoc COW schema-20 landing — typecheck side (S111 Phase 3)

**Status:** DESIGN (S111 Phase 3), pre-implementation. Realizes the typecheck (a1/a3)
layers of the `/arch` §3.7 ruling (`design/arch/ownership-inference.md`; the spine governs).
The peer layers land in the SAME coordinated change-set (spine §3.7 / SPRINT.md §2):
`cranelisp-types` `ResultMode::MayAliasOf(usize)` + `CACHE_SCHEMA_VERSION` 19→20 (`/arch`);
`cranelisp-primitives` truthful COW declarations (`/dev` backend-paired). This section
answers the SPRINT.md §5 **carrier-completeness matrix axes 1 (reachability) + 3 (producer)**
for this crate; axis 2 (variant exhaustiveness) is structurally forced (§15.4). **The whole
landing is emission-affecting BY DESIGN** — see §15.6 for the disposition every `/dev` +
`/qa` step inherits.

### 15.1 The three coupled defects, restated at this crate's seams

Per the spine §3.7 root-cause: (1) `ResultMode` lacked the COW point ⇒ a legal state (the
dynamic either-fresh-or-alias result) was falsely declared `Fresh`; (2) the declared COW
facts on `vec-set`/`vec-push` said `Fresh`; (3) the declared facts were **unreachable** from
prelude-fallback modules, so even a corrected declaration would be dead code. Layers (1)+(2)
are §15.3 (producer) + the §9.3/§2.2 doc-currency fixes above + the `cranelisp-primitives`
peer; layer (3) is §15.2 (reachability) — **this crate's load-bearing new work**, because
without it a2 is dead code (spine §3.7(a3)).

### 15.2 Reachability — prelude-fallback-aware ownership environments (axis 1; the a3 leg)

**The defect precisely.** The ownership envs resolve callee facts through
`TypeCheckEnv::resolve_terminal_entry_and_home` (`checker.rs:1889`) — a raw
`probe_module_entry_owned` current-module probe + `chain_follow_to_home` `Import`-chain
follow, with **no prelude fallback and no I-1 public-head filter**. In any module that
reaches primitives via the implicit prelude (essentially all user code), the probe misses:
`summary_of → None`, `terminal_kind → None`. Params then degrade to ⊤-`Owned`
(conservative-safe, precision lost) and — the anti-conservative direction this defect is
about — results default to `Fresh` at the transfer walk (`transfer.rs:590`
`unwrap_or(ResultMode::Fresh)`). The entire §3.1(a)/§9 declared-fact precision is silently
inert in production.

**Confirmed fact-lookup site inventory (grep-verified 2026-07-17; the SPRINT.md §5 axis-1
completeness obligation — "confirm no sixth site").** The raw fallback-less resolve is
`resolve_terminal_entry_and_home`; there are **exactly five call sites, ALL in
`ownership/fixpoint.rs`, zero `probe_module_entry_owned` under `ownership/`:**

| # | Env method | Site | Returns |
|---|---|---|---|
| 1 | `ClusterEnv::terminal_kind` | `fixpoint.rs:77` | `TerminalKind` |
| 2 | `ClusterEnv::summary_of` | `fixpoint.rs:89` | `(FQSymbol, ModeSummary)` |
| 3 | `UniqClusterEnv::terminal_kind` | `fixpoint.rs:393` | `TerminalKind` |
| 4 | `UniqClusterEnv::summary_of` | `fixpoint.rs:402` | `ModeSummary` |
| 5 | `UniqClusterEnv::result_unique_of` | `fixpoint.rs:413` | `bool` |

All five are the byte-identical expression
`self.env.resolve_terminal_entry_and_home(&self.current_module, name.as_ref())`.
**`confinement.rs:162` is NOT a sixth site** — it calls `self.env.summary_of` where
`self.env: E: TransferEnv` is the `ClusterEnv`, so it is a *consumer* of site 2, fixed
transitively (verified: `Confiner<'e, E: TransferEnv>`). Likewise every `self.env.summary_of`
/ `self.env.terminal_kind` in `transfer.rs` routes through sites 1–2. The spine §3.7's "five
sites (ClusterEnv twins + UniqClusterEnv twins + confinement's read)" and this grep converge:
the confinement read is subsumed by fixing ClusterEnv::summary_of, and UniqClusterEnv carries
the third raw twin (`result_unique_of`) the spine folded into its `:388–415` range.

**The fix — ONE shared prelude-hop helper (Principle 7 — binding, spine §3.7(a3)).** Add a
single fallback-aware `(entry, home)` resolver on `TypeCheckEnv`, e.g.
`resolve_terminal_entry_and_home_scoped(current_module, name) -> Option<(ModuleEntry<C>,
ModuleFullPath)>`, that **delegates to the existing scope-resolve machinery**
(`scope_resolve_in(current_module, name, Span::SYNTHETIC)`, `checker.rs:1037`) and maps
`Ok(resolved) → Some((resolved.entry, resolved.storage_fq().module))`, `Err(_) → None`. All
five sites call this ONE helper. Rationale:

- `scope_resolve_in` is **staging-aware** (it selects `SymbolTableRead::Cluster` when
  `staging.module == current_module`, else `Live`) — parity with the ownership pass's current
  staging-visibility (the pass runs at finalize while staging is live).
- Prelude fallback + `Import`-chain follow + the I-1 public-head filter + the
  qualified-never-retries guard are ALL **intrinsic to `ResolutionScope::resolve`** (decided
  once at scope construction from the `PreludeFallback` bit) — so the helper hand-rolls
  nothing (the `crates/cranelisp-typecheck/CLAUDE.md` "never re-thread `prelude_fallback_target` at a
  new call site" rule). It is the terminal-entry sibling of the existing `resolve_entry_scoped`
  (`checker.rs:1769`), differing only in also returning the home the ownership FQSymbols need.
- Same-module and explicit-import reach are behaviour-preserved (scope resolve subsumes the
  raw probe + chain-follow); prelude reach is newly correct; a **private** prelude binding is
  now correctly filtered (I-1) rather than leaking — a strict correctness gain.

**Home/symbol identity (design pin, consistent with 0620/0621).** Site 2's returned FQSymbol
currently uses `FQSymbol { module: home, symbol: name.clone() }` — the WRITTEN name. Prefer
`resolved.storage_fq()` (home + terminal storage key) so the returned identity is the storage
key, not a member/renamed alias (the same discipline the 0620/0621 flip enforces on the
`resolved_targets`/`callees` carriers). This is **not load-bearing for fixpoint correctness**
— a prelude/imported callee is a boundary condition (never on the worklist), and its recorded
`deps` FQSymbol (`transfer.rs:571`) drives only intra-cluster caller re-entry, which a
non-cluster key never triggers — but using `storage_fq()` avoids re-seeding the alias class in
a new carrier and keeps the crate's identity discipline uniform.

**Unit pin (spine §3.7(a3)):** `summary_of` finds `vec-set`'s declared `MayAliasOf(0)` facts
from a prelude-fallback module (`tf.prelude_fallback.insert(module, true)` per the CLAUDE.md
test recipe). Negative pin: a *private* prelude entry is NOT resolved (I-1 filter honoured).

### 15.3 The producer arm — `origin_to_result_mode` (axis 3)

The body-final-origin → published `ResultMode` map (`transfer.rs:237`) currently publishes a
**hard `AliasOf`** for a may-alias origin. Per spine §3.7(a1) with the binding constraint
*"no may-origin may publish a mode whose consumer can elide an inc/protect; retain-side
imprecision is acceptable"*:

| origin | current | S111 | grounds |
|---|---|---|---|
| `Root(s)`, `param_root=Some(i)` | `AliasOf(i)` | `AliasOf(i)` (unchanged) | UNCONDITIONAL — the value IS param i on every path |
| `Projection(s)`, `param_root=Some(i)` | `ProjectionOf(i)` | `ProjectionOf(i)` (unchanged) | UNCONDITIONAL borrowed view (the clean accessor; only a single-path `Origin::Projection` reaches here, never a join — §15 note) |
| `MayParam{rep, projection:false}`, `param_root=Some(i)` | `AliasOf(i)` | **`MayAliasOf(i)`** | may-alias — a `Fresh`-path exists; `AliasOf` would let a future consumer assume it IS param i and transfer/skip a dec (unsound on the fresh arm) |
| `MayParam{rep, projection:true}`, `param_root=Some(i)` | `ProjectionOf(i)` | **`MayAliasOf(i)`** (recommended) | may-projection — also conditional; `AliasOf`/`ProjectionOf` are reserved for UNCONDITIONAL claims (spine §3.7(a1)). Collapsing to `MayAliasOf` is the conservative, no-unsound-elision choice. Precision cost is nil: the consumer already writes **no** provenance fact for a may-projection (`transfer.rs:601`), and the flagship accessor stays `Origin::Projection` (row 2), so no S99-target read-path shrinks |
| `Fresh` / `None` param_root | `Fresh` | `Fresh` (unchanged) | no param reaches the result |

**The projection-true row is a `/design` ruling the spine left to this pass** (§3.7(a1) named
only the `projection:false` flip explicitly). I rule **both may-arms publish `MayAliasOf`** —
it maximally satisfies the binding constraint (a may-origin can never mislead a consumer into
an unsound elision) at zero measured cost. Flagged for `/review`/`/arch` visibility since it
is stronger than the letter of the ruling; a reviewer preferring the minimal change (keep the
projection-true arm at `ProjectionOf`) is retain-side-safe **today** — the current backend
consumer reads only `== Fresh`, so `ProjectionOf` keeps protect — but is future-fragile
against any projection-provenance last-use consumer, which is why the collapse is the
recommended end-state.

### 15.4 The transfer-walk consumer arm (axis 2 — variant exhaustiveness)

`walk_apply`'s result-origin match on the CALLEE's `ResultMode` (`transfer.rs:591`) has **no
wildcard** and `ResultMode` carries no `#[non_exhaustive]` (the `/arch` §2 exhaustiveness-as-
safety exception) — so adding `MayAliasOf` **forces** this arm to be written at compile time
(Principle 18). The arm, per spine §3.7(a1) ("the join of `Fresh` with `arg_origins[k]`"):

```rust
ResultMode::MayAliasOf(k) => {
    // Result is EITHER fresh OR arg k's reference (COW, dynamic). Join Fresh with
    // the arg's origin: a param-reaching arg ⇒ Origin::MayParam (never collapses to
    // Fresh — the 0520 rule keeps protect); a fresh/non-param arg ⇒ Fresh.
    let arg = arg_origins.get(k).cloned().unwrap_or(Origin::Fresh);
    self.join_origin(Origin::Fresh, arg)
}
```

`join_origin` already produces `MayParam` when one side reaches a param and `Fresh` when
neither does (§transfer, FIXME 0520) — so this arm reuses the exact 0520 may-alias
composition, no new join logic. **This is the only exhaustive `match` on `ResultMode` in the
crate** (grep-confirmed: the sole consumer match is `transfer.rs:591`; `origin_to_result_mode`
at `:237` produces it; `uniqueness.rs` reads the separate `result_unique` bool, never the
variant; `trace.rs` Debug-formats it). Axis 2 is therefore closed by the compiler.

**Increment-II non-impact (checked).** The uniqueness stratum admits a call result as a
unique root only when the callee's `result_unique` bit proves it — **never** `result == Fresh`
(`uniqueness.rs:29`). A `MayAliasOf`-producing COW body has `result_unique = false` (it may
return a shared param), so the stratum already refuses to treat it as unique. No `MayAliasOf`
handling is owed in `uniqueness.rs`; the new variant is invisible to increment II by
construction.

### 15.5 The 0621 rider — `callees` records `storage_fq()` (SAME change-set)

Per FIXME 0621 + SPRINT.md §2 (binding: same CHANGE-SET, not merely same sprint — the schema
constant flips once). `record_reference_target` (`checker.rs:1417`) records **two** feeds from
one resolution: `resolved_targets` (already `storage_fq()` since the 0620 landing, `:1464`)
and `user_fn_refs`/`callees` (still `resolved.fq`, `:1468`). Flip `:1468`:
`state.user_fn_refs.insert(span, resolved.storage_fq())`, and correct the method rustdoc
(`:1388–1395`, which currently documents `callees` as recording `resolved.fq` NOT
`storage_fq()`). This is a persisted-`.meta.json` meaning change ⇒ it MUST ride the same
`CACHE_SCHEMA_VERSION` 19→20 bump (the `Def.callees` completeness contract in
`crates/cranelisp-typecheck/CLAUDE.md` — "changing what `callees` records is a meaning change: bump
in the same change-set"). Unit pins (`program::tests::callees_*` family): a **renamed import**
(`[(foo bar)]` → edge names `{m, foo}` the storage key, not the `{m, bar}` alias) and a **bare
accessor** reference (edge names `{m, Box.v}` canonical, not bare `{m, v}`). Landing check
(from 0621): confirm `extract_call_graph_edges`' `ResolvedCall` channel is already
storage-keyed (post-W0.1b it is). `/dev` implements; the schema constant + the types
`MayAliasOf` variant are `/arch`-authored in the same change-set.

### 15.6 Golden / byte-identity disposition (inherited by every `/dev` + `/qa` step)

**The landing is emission-affecting by design, in TWO ways** (spine §3.7 "Golden/byte-identity
disposition"): (i) protect re-emission on COW-return chains (the fix's point); (ii) the a3
reachability leg **activates the designed increment-I precision** (`Borrowed` param narrowing,
`ProjectionOf` accessor results) in production prelude-fallback modules where it was silently
inert — so CLIF changes **beyond** the COW class are EXPECTED AND INTENDED. Discipline: schema
19→20 invalidates caches wholesale; every drifted golden frame must be attributed to one of
the two named mechanisms and re-baselined **scoped + attributed** per MANIFEST.md (S102 §6.2 —
extension ≠ re-baseline), with the re-baseline as the wave's LAST act (SPRINT.md §1 ordering
constraint 1: byte-identical backend work lands BEFORE this wave). This is the standing risk
`/qa` must pin — see §15.7.

### 15.7 Risks routed to `/qa` (0623 fences)

1. **Declared-fact reachability fence (0623 item 3):** a prelude-fallback module exercising a
   `Borrowed`-declared primitive (`str-eq`/`vec-len` in a loop) must show the narrowed emission
   once §15.2 lands — the fence that would have caught "declared facts silently dead in
   production". Absent this, an accidental regression of the prelude hop is invisible.
2. **Return-position copy-arm leak fence (0623 item 2):** post-fix, a shared-source COW returned
   through a NON-direct shape conservatively over-incs the copy arm by exactly one (retain-side
   residual — the summary-driven protect vs the direct-body recognizer's exact accounting, spine
   §3.7). Pin the residual's magnitude (exactly one, never a UAF); flip when the walk-emitted
   per-site-fact generalization lands.
3. **Body-shape × branch × face matrix (0623 item 1):** the four RED siblings (let-wrapped +
   match-arm × REPL/`--link`) plus if-branch/chained-COW × {in-place, shared} — `/qa` authors,
   `/testing` builds. The typecheck-side guarantee: `MayAliasOf` keeps protect on EVERY body
   shape (the summary is body-shape-agnostic), so all shapes are safe-by-summary; the direct-body
   recognizer's re-scope to a leak-exactness optimization is backend-side (spine §3.7).

## §16. The monotone provenance frame — the 0641 sound-narrowing cure (S113 W5)

**Status:** DESIGN (S113 W5, `/design`(typecheck)). Realizes `design/arch/safety-invariants.md`
§3 (a)/(b)/(c) — the arch-binding frame FIXME 0641 is gated on — as the concrete typecheck
mechanism. **The false-`Fresh` class closes by making the transfer walk lattice-monotone with
an enumerated, classified rule table; B-1/I-1/I-2 land as rule-table corrections INSIDE this
frame, never as a `VecLit` spot-fix** (safety-invariants §3e; the CS-1.1 → 0640 lesson). This
section supersedes the ad-hoc origin reasoning scattered across §3.3/§15.3; §15 (the COW
schema-20 landing) is the first correction this frame generalizes.

### 16.1 §3a — the provenance lattice and its explicit ⊤

The walk's provenance state is the internal `Origin` enum (`transfer.rs:138`; NOT the persisted
`ResultMode`). Its four points, ordered by **claim strength** (how much elision each licenses):

```
        Fresh                        Root(i) / Projection(i)      ← STRONG claims (license elision:
       (no param reaches)            (UNCONDITIONALLY param i)       a dec-transfer / no-protect)
              \                          /
               \                        /
                MayParam{rep=i, projection}      ← the CONSERVATIVE point
             (MAY reach param i on some path)
                        |
                        ⊤ = MayParam over the JOIN of all reachable param-roots
```

The **conservative point is `MayParam` — "the result may reach anything the inputs reach."**
`Fresh` and unconditional `Root`/`Projection` are the *strong* claims: `Fresh` says "no param
reaches this, free it on scope exit"; `Root(i)`/`Projection(i)` say "this IS param i's
reference on **every** path, transfer/borrow it." Each licenses a safety-op elision. **⊤ is
`MayParam` joined over every param-root the inputs could reach** — the absence of a stated ⊤
on this axis (the mode lattice has `Owned`; the origin axis had none) is exactly where the
0641 bugs live.

**The normative monotone rule (safety-invariants §3a):** *information loss in the walk MUST
move toward `MayParam`, never toward `Fresh` or toward an unconditional `Root`/`Projection`.*
Losing per-element or per-path detail is fine (widen to `MayParam`); losing the **reach**
(collapsing to `Fresh`) or **strengthening** a conditional reach to an unconditional claim is
the unsound direction — and is precisely a *rule violation visible at design review*, not a
fact someone must adversarially discover.

### 16.2 §3c — the enumerated, classified transfer-rule table

One row per construct the walk visits. **Classification:** *widening* (joins toward ⊤/`MayParam`
— always admissible), *precision-preserving* (carries provenance exactly), or *narrowing*
(publishes a claim stronger than the join of its inputs — admissible ONLY with a named
justification: a provably-unconditional structural argument recorded on the row). `/review`
rejects a `transfer.rs` change that adds or alters a rule absent from this table — the same
discipline as an unjustified `pub`.

| # | Construct (walk arm) | Rule — the result Origin | Class | Justification / 0641 correction |
|---|---|---|---|---|
| 1 | **Var / reference** (`walk_var`, `:544`) | the binding's recorded Origin; a param ref → `Root(i)` | precision-preserving | `param_root` chain-follow; unconditional because a direct param ref IS the param on every path |
| 2 | **Let / ParBind binding** (`:362`) | binds the value's Origin unchanged into the new scope | precision-preserving | a `let r = e` alias carries `e`'s exact Origin (the `Root`/`MayParam` chain extends) |
| 3 | **Match-arm var-pattern binding** | the SCRUTINEE's Origin — **`MayParam` when the scrutinee is conditional, NEVER unconditional `Projection`/`Root`** | **narrowing-forbidden → widening** | **0641 B-2 CORRECTION.** As-built binds an unconditional `Origin::Projection`/`Root` for a COW `MayParam` scrutinee (`(match (vec-set v 1 99) [r r])` publishes hard `ProjectionOf(0)`) — a narrowing with no justification (the scrutinee is conditional). Rule: an arm var-pattern binds the scrutinee's Origin verbatim; a `MayParam` scrutinee yields a `MayParam` binding. A destructuring sub-pattern that PROJECTS binds `Projection` of the scrutinee root — unconditional only if the scrutinee root itself is unconditional, else `MayParam{projection:true}` |
| 4 | **If / Match branch join** (`join_origin`, `:298`) | join of the arms' Origins — `MayParam` if either reaches a param, `Fresh` iff neither does | widening | already correct (FIXME 0520): the join never collapses a param-reaching arm to `Fresh`. The completeness anchor for the ⊤ rule |
| 5 | **VecLit / ConstrADT element-store** (`:436`) | **the JOIN of the container's element Origins** (`MayParam{rep=i}` if any element reaches param i), not unconditional `Fresh` | **narrowing → widening** | **0641 B-1 + I-2 CORRECTION.** As-built returns `Origin::Fresh` UNCONDITIONALLY (`:442`), discarding that an element reaches a param — the clearest anti-monotone rule (`(vec-get [v] 0)` launders `v`→`Fresh`; `[(vec-set v 0 9)]` returns a fresh container whose escaping element is a COW alias). Rule: the container Origin is `join_origin` folded over its element Origins (losing per-element detail is fine — reach is not). A projection-OUT of the container (row 6) then yields the aliased element's origin, not `Fresh` |
| 6 | **Projection-out** (`vec-get` / accessor / field read, ProjectionOf consume, `walk_apply` `:591`) | roots at the container's Origin: `Projection(i)` if the container is unconditional `Root(i)`, else `MayParam{projection:true}` over the container's reach | precision-preserving | depends on row 5 being correct — with the container carrying its element-join, a projection-out inherits the alias reach. Never strengthens: a projection of a `MayParam` container stays `MayParam` |
| 7 | **Capture (closure free-var)** (`walk_lambda`, `:445`; `classify_capture_escape`) | a captured local that `param_root`-reaches param i is a **param escape** (retain param i's reference past the enclosing frame); the captured Origin roots THROUGH the let/alias chain | **narrowing → widening** | **0641 I-1 CORRECTION.** As-built capture-accounting laundries a let-bound param alias (`(let [r v] (fn [] (vec-get r 1)))`) — it treats the captured `r` as a fresh local rather than a `Root(v)` param alias, so param `v`'s reference isn't retained past `mk`'s return (freed heap read). Rule: `classify_capture_escape` roots each captured free var through `param_root`; a param-rooted capture escapes the param, exactly as a directly-captured param does |
| 8 | **Apply — static call** (`walk_apply`, `:568`) | per the callee's `ResultMode`: `AliasOf(k)`/`ProjectionOf(k)` → arg k's Origin; `MayAliasOf(k)` → `join(Fresh, arg_k)` (= `MayParam` if arg reaches a param); `Fresh` → `Fresh` | precision-preserving (widening on `MayAliasOf`) | the §15.4 consumer arm; `MayAliasOf` reuses the 0520 join, keeps protect. Unconditional `AliasOf`/`ProjectionOf` are trusted only because the callee summary earned them (row 9's publish gate) |
| 9 | **Return — origin → `ResultMode` publish** (`origin_to_result_mode`, `:237`) | unconditional `Root(i)`→`AliasOf(i)`, unconditional `Projection(i)`→`ProjectionOf(i)`, **`MayParam`→`MayAliasOf(i)` (both projection arms)**, `Fresh`→`Fresh` | precision-preserving | the §15.3 producer arm — the hard-claim arms match ONLY the unconditional variants (§16.3). A `MayParam` can never publish a hard claim (safety-invariants §3b) |
| 10 | **Suspension — ParBind / spark escape edge** (R6, §5.5.2) | a value crossing a suspension point escapes its frame — its root materializes (inc at the escape edge); result Origin widens to the crossing classification | widening | suspension is an escape edge, never a borrow-widening; already the confinement axis's job |

**Ten rows.** Rows 3, 5, 7 are the 0641 corrections; rows 4, 8, 9 are the already-correct
monotone anchors the corrections must compose with; the rest are precision-preserving.
Completeness argument = the *table*, not the example pins (safety-invariants §3c). The 0623
behavioral matrix extends with the container-store × projection-out × capture axes (each row
gets its example pins — §16.5), but the table is the soundness argument.

### 16.3 §3b — the conditional/unconditional producer split (P20 shape)

The safety-invariants §3b requirement: make "publish a hard claim from a conditional origin"
**unconstructable**, not a prose contract (B-2 violated the reservation one level above the
arm §15.3 fixed). The shape:

**The distinction already exists at the `Origin` level** — `Root`/`Projection` are the
unconditional variants, `MayParam` the conditional one. The P20 reshape makes the invariant
*structural*: regroup so an unconditional Origin is **only constructable from a
provably-unconditional source**, e.g.

```
enum Origin {
    Fresh,
    Unconditional { root: Symbol, projection: bool },   // Root(s)=projection:false, Projection(s)=projection:true
    Conditional  { rep:  Symbol, projection: bool },     // today's MayParam
}
```

with the constructors that handle a conditional input (row 3 arm-var binding, row 4 `join_origin`,
row 5 element-store fold, row 6 conditional-container projection) able to build **only**
`Conditional`, and `origin_to_result_mode`'s hard-claim arms (`AliasOf`/`ProjectionOf`)
pattern-matching **only** `Origin::Unconditional`. Publishing a hard claim from a conditional
origin then has no representation — B-2 becomes a compile error, not a review finding. The
exact enum is `/dev`'s to settle; the requirement is the structural reservation.

**§3b shape verdict — NOT types-touching (W5 = no schema bump).** This reshape lives entirely
in the **internal** `transfer.rs::Origin` enum. The persisted carrier `ResultMode`/`ModeSummary`
(`cranelisp-types`) **already carries the conditional point** — `MayAliasOf` (schema 20, S111
§15) — and needs no new variant for the 0641 class: a may-projection collapses to `MayAliasOf`
(§15.3), so soundness needs no persisted may-projection variant. Therefore the §3b split for
the 0641 cure is **internal-only, no `cranelisp-types` edit, no `CACHE_SCHEMA_VERSION` bump** —
consistent with the arch W5-status "§3a/§3c do not depend on the §3b producer split (+ its
schema bump)". The schema-bump §3b fallback arch named is a **future capacity** concern (S114):
it is needed only if a later consumer (a projection-provenance last-use elision) must
distinguish may-projection from may-alias *in the persisted summary*, forcing a `ResultMode`
split into persisted `Unconditional`/`Conditional`. That is NOT the 0641 fix. **If `/dev`
implementation finds the internal `Origin` reshape insufficient and needs a persisted
`ResultMode` split, STOP and file FIXME `target: /arch`** (schema bump — do not design around
it; arch W5-status names it the capacity fallback).

### 16.4 Joint acceptance with the paired `/dev`(backend) consume fix

B-1/I-1/I-2/B-2 did NOT all flip on the typecheck provenance fix alone:

- **B-1** (`(vec-get [v] 0)`) is a **pure false-`Fresh`** defect — cured toggle-OFF already
  (clean exit under `CRANELISP_NO_OWNERSHIP=1`); the row-5 element-store fix flips it (and the
  MS-P7 lane cell) GREEN.
- **B-2** (`(match (vec-set v 1 99) [r r])`) and **I-2** (`[(vec-set v 0 9)]`) **fail
  toggle-OFF too** — an **ownership-INDEPENDENT** backend crash is stacked under the
  scrutinee/COW-set-into-container shapes (`/qa`-attributed, the paired `/dev`(backend)
  vec-set-result consume-seam fix, safety-invariants §6 task 1). The row-3/row-5 provenance
  corrections remove the false-`Fresh` protect-elision; the backend consume fix removes the
  ownership-independent crash. **Neither alone flips B-2/I-2.**
- **I-1** (capture) — the row-7 capture-rooting fix flips the ownership arm; verify against
  toggle-off.

**Joint acceptance — DISCHARGED S113/S114.** The acceptance set was the 8 pins in
`tests/false_fresh_provenance_residual.rs` (B-1/B-2/I-1/I-2 × {REPL value, `--link`
no-heap-corruption}) plus MS-P7 (`tests/safety_oracle_lane.rs` — the COW-set→project
`--link` mode-divergent cell, the 0641 class's third reaching context), under the tier-4
differential lane + the three modes, and only when BOTH change-sets landed. Both landed —
the typecheck half in S113 W5b, the backend consume half in S114
(`sprints/archive/sprint-113.md`, `sprints/archive/sprint-114.md` §0669) — and FIXME 0641
was deleted at `3297adf8`. **Those 8 cells are GREEN regression guards, not open pins:**
`qa` measured them green in the whole-suite census of 2026-09-07 13:34, hours before the
§19 wave, so no S121 movement is attributable to them. The tier-4 oracle (analysis-on ≡
analysis-off byte + RC balance) remains the standing end-to-end discharge
(safety-invariants §3d): an elision is correct iff equivalent to the all-`Owned`
lowering.

### 16.5 Riders and cross-refs

- **0623 matrix axes** (`/qa` authors, `/testing` builds): extend with **container-store ×
  projection-out × capture** (rows 5/6/7), each cell × {in-place, shared} × {REPL, `--link`} ×
  {ownership-on, ownership-off} — the on/off discriminator is what separates the pure-provenance
  B-1 face from the backend-stacked B-2/I-2 faces (MS-P7's discriminator, generalized).
- **CS-5 rustdoc over-claim (`/dev`(backend) rider):** `fn_compiler.rs` §B3.2 claims the
  `==Fresh` return-protect elision is sound iff **leaf** facts are truthful+reachable — the
  review disproved it (the WALK launders provenance with truthful, reachable leaf facts). `/dev`
  scopes the claim honestly to the covered axes when landing the row-5/7 corrections
  (safety-invariants §6 task 1's named small item). Design-side flag; the edit is backend code.
- **Spec-diff (§2.3.8/§12):** EMPTY. The ownership analysis is a spec-invisible optimization —
  the memory model's observable behavior (`spec/10-io.md` §12.4.3 fork-join, §2.3.8) is defined
  by the all-`Owned` reference semantics, and every rule above is sound iff equivalent to it
  (the tier-4 oracle IS that equivalence check). No spec case changes; correctness is the
  oracle, not a new observable.

## §17. MS-P7 chained-face family — the may-alias LINK protect (S115)

**Status:** DESIGN (S115 Phase 3, `/design`(typecheck)). Realizes the /arch
Phase-2 §2 ruling (SPRINT.md S115): the chained `MayAliasOf` faces close as
**§16.2 rule-table corrections at the FAMILY grain**, NEVER a 5th
per-consumer/per-context arm. The W7 `ProjectionOf`/`MayAliasOf` escape-force
(`transfer.rs:703–735`, S114 `68cd7a96`) was the **4th** arm of an instance-patch
progression; this section replaces its syntactic reach with a provenance-carried
obligation so the SINGLE existing projection-out consumer discharges the whole
chain. Governed by the §16 monotone-provenance frame (the spine
`design/arch/ownership-inference.md`; where they disagree, the spine governs).

### 17.1 The two open faces, restated at the walk seam

Both RED cells (`tests/safety_oracle_lane.rs`, S114 0706) are a COW `vec-set`
result — an `Origin::Conditional` may-alias reference — flowing through **≥2
links in one frame** before a **projection-out** (`vec-get`) consumes it. `--run`
tolerates the double-dec in-process (returns the correct value); `--link`'s glibc
allocator aborts (134). The W7 fix protected the OUTER (immediate) container only:

- **Nested-projection** — `(vec-get (vec-set (vec-set v 0 1) 1 2) 0)`. In
  `walk_apply`'s `ProjectionOf` arm (`:690`), `args[0]` IS the outer
  `(vec-set … 1 2)` `Apply`, so the `if let MonoExpr::Apply { span, .. } = &args[k]`
  guard (`:729`) forces the OUTER container's escape fact `true`. The **INNER**
  `(vec-set v 0 1)` — an arg-temp the outer set's inline lowering releases — keeps
  `escapes = Some(false)` (its own `:754` insert, `Arg{Borrowed}` ctx). The inner
  link double-decs (arg-temp drop + `v`'s scope-dec on the in-place arm).
- **Let-chained** — `(let [w (vec-set v 0 1)] (vec-get (vec-set w 1 2) 0))`. The
  outer `(vec-set w 1 2)` gets the W7 force (`args[k]` is an `Apply`), but `w`'s
  RHS `(vec-set v 0 1)` — the INNER link — is a `MonoExpr::Var` when reached, so the
  W7 guard never sees its allocation span. The `w` RHS keeps `escapes = Some(false)`.

The shared root: **the W7 mechanism reaches the allocation to protect only via the
consumer's immediate syntactic `args[k]` when it happens to be a direct `Apply`.**
A chain of length ≥2 (nested `Apply`, or `let`-mediated `Var`) hides the inner
allocation(s) from that syntactic reach. Adding a `Var`-arg arm, then a
nested-`Apply` arm, then an `If`/`Match`-container arm (face 3) is exactly the 5th,
6th, 7th instance-patch the family-grain ruling forbids.

### 17.2 The family-grain rule — the may-alias value carries its protect obligation

**Invariant (binding, folds the W7-review Minor; SPRINT.md §2 / test plan §1.1.1):**
*every may-alias LINK whose accounting includes a consumer-emitted release needs
its protect.* A "link" is any COW `MayAliasOf` allocation on the provenance chain
feeding a release-emitting consumer. The obligation belongs to the **value**
(P25 "Narrowing carries its check"; the R1/R14 producer-truth obligation
applied per-link), not to the consumer's syntactic view — so the analysis moves
the protect FROM the syntactic reach INTO the `Origin` the may-alias value
already carries.

**Mechanism — the internal `Origin::Conditional` records its may-alias allocation
site(s).** The `Conditional` variant (`transfer.rs:138`, the ex-`MayParam` point)
gains a set of **cow-alloc spans** — the `Apply` spans where a `MayAliasOf`-result
minted this may-alias reference. This is an **internal `transfer.rs::Origin`
change only** — `Origin` is walk-internal, NOT the persisted `ResultMode`
(§16.3's "internal-only, no `cranelisp-types` edit, no `CACHE_SCHEMA_VERSION`
bump" verdict extends verbatim; the exact shape — a `Vec<Span>` field, a
`SmallVec`, or a side-map keyed by the binding — is `/dev`'s to settle, per §16.3
"the exact enum is `/dev`'s to settle; the requirement is the structural
reservation"). The rule-table rows change as follows (all §16.2 grain):

| §16.2 row | Correction | Class |
|---|---|---|
| **8 — Apply, `MayAliasOf(k)`** (`transfer.rs:747`) | the produced `Conditional` UNIONs the arg's carried cow-alloc spans with **this Apply's own span** (this call minted a fresh may-alias link). `join(Fresh, arg_k)` is unchanged for the `rep`/reach axis (§16 already correct); the span-set is the added carrier | precision-preserving (widening on reach; the span-set only grows) |
| **2 — Let / ParBind binding** (`:362`) | a `let w = e` alias carries `e`'s cow-alloc span-set unchanged into the new scope (the `w` binding for the let-chained face) | precision-preserving |
| **4 — If / Match join** (`:298`) | **CORRECTED (FIXME 0772/0777, landed).** A join whose operands carry may-alias links produces a value carrying their **union**, and the joined **variant** is the ⊤-ward of the two operands (`Unconditional ⊑ Conditional`) — both **independently of which operand contributed them and of operand order** (P24). The original wording, "UNION … when the join is `Conditional`", described one code path rather than the invariant, and left the join's own variant choice free to be `Unconditional`, at which point the as-built discarded the union it had just computed. Order-independence is the property; the union is its consequence | widening |
| **6 — Projection-out** (`:690`, the W7 arm) | when the projected container is `Conditional`, force `facts.escapes.insert(span, true)` for **EVERY carried cow-alloc span**, not the single `args[k]` syntactic span. The W7 `if let MonoExpr::Apply = &args[k]` reach is DELETED — replaced by iterating the container Origin's carried spans | narrowing→**widening** (the escape-force now covers the whole chain; monotone — it only ADDS incs, never removes a dec, per the test comment "the escape-force only ADDS incs; the failure is in the too-many-decs direction") |

**Why this is not over-widening (the negative control holds).** The force fires
ONLY at a **projection-out** consumer of a `Conditional` container (row 6). The
whole-value negative control `(defn f [v] (vec-set (vec-set v 0 1) 1 2))` returned
WHOLE and projected by the CALLER
(`safety_lane_whole_value_nested_transfer_clean_green`) has NO in-frame
projection-out — the chain flows to a **return** (row 9 publishes `MayAliasOf(0)`;
the return-protect already covers it). The cow-alloc spans accumulate on the
`Conditional` as it flows but are never force-triggered absent a projection-out
consumer, so the clean nested-transfer shape is unchanged. This is the family
boundary the control fences: **chained-may-alias × projection-IN-THE-SAME-FRAME**,
not nested COW per se.

**Why the terminal projection reaches every inner link.** The cow-alloc span-set
composes down the chain (row 8 union + row 2 carry + row 4 join), so by the time
the terminal `(vec-get …)` consumes the outermost `Conditional`, that Origin
carries EVERY may-alias allocation on the chain — inner set, outer set, and any
`let`-mediated intermediate. Row 6 then forces escape `true` at all of them in one
place. The backend's escape-gated COW retain (`cow_source_ownership` →
`retain_reused`) incs each in-place result, balancing each consumer-emitted release
— one net dec per link. Worked through both faces:

- **Nested:** inner `(vec-set v 0 1)` → `Conditional{rep=v, cow=[inner]}`; outer
  `(vec-set INNER 1 2)` → `Conditional{rep=v, cow=[inner, outer]}` (row 8 union);
  `(vec-get OUTER 0)` forces escape at BOTH `inner` and `outer` (row 6). ✓
- **Let-chained:** `w = (vec-set v 0 1)` → binding `Conditional{rep=v, cow=[rhs]}`
  (row 2); `(vec-set w 1 2)` → `Conditional{rep=v, cow=[rhs, outer]}` (row 8);
  `(vec-get … 0)` forces escape at BOTH `rhs` and `outer`. ✓

### 17.3 Why no 5th consumer arm (the explicit argument the ruling demands)

The W7 arm and any per-shape successor patch the **consumer** to recognise one
more syntactic shape of its argument (direct `Apply`; then `Var`; then nested
`Apply`; then `If`/`Match`). Each is a new arm keyed on the consumer's local view —
the instance-patch anti-pattern (SPRINT.md §2 constraint 1; test plan §0 risk-2).
The family-grain fix inverts the direction: the may-alias VALUE carries its own
allocation provenance on its `Origin`, so the **count of consumer arms does not
grow** — the single pre-existing projection-out arm (row 6) discharges every link
of every chain shape *for which the composition is closed*.

**The closure obligation, named (FIXME 0777).** The original wording claimed the
composition rules covered every new chain shape outright. That claim was too
strong, and the face-3 probe falsified it as written: the composition is closed
only while every composition rule is **order-independent**, and row 4 as
originally stated was not. What is provable, and what this section now claims, is
two things and no more:

1. **The arm count is fixed.** `review` verified by grep that the W7 fix added no
   consumer arm — the `if let MonoExpr::Apply` reach was deleted and replaced by a
   loop over the carried spans, and the `Origin::Conditional` arms are pre-existing
   arms that gained a `cow` field.
2. **Closure holds iff every composition rule is order-independent at its join.**
   That is the obligation each new composition rule is checked against, and it is
   the property the `join_lattice_*` property cells pin. A rule that reads its
   result off one operand — as the pre-0772 `join_origin` did (`match a {
   Conditional => …, other => other }`) — breaks closure without adding an arm,
   which is exactly why arm-counting alone was not a sufficient fence.

### 17.4 Face-3 (Conditional-container) — probed, and closed by the row-4 correction

**The prediction this section carried is retired and replaced by the probe result
(FIXME 0777).** `review` ran the probe §17.4 originally called for. Result: the
`If`-joined container was covered when the may-alias arm was written **first** and
aborted (`--link`, exit 134) when it was written **second** — two programs
executing the same runtime path, differing only in source order. A `let`-mediated
variant aborted in **both** orders. The behavioural defect was FIXME 0772; the
full probe table lived there.

The mechanism gap was row 4's, not a missing arm: the original condition ("union
when the join is `Conditional`") left the join's own variant choice free, and the
as-built then discarded the union it had computed whenever the `Unconditional`
operand happened to be first. `MonoExpr::If` joins its arms in source order, so
the memory-safety verdict depended on which arm the programmer wrote the COW
producer in — the P24 acid test, failed.

**Landed.** `transfer.rs::join_origin` (`:391-419`) now computes
`union_cow(a.cow_spans(), b.cow_spans())` unconditionally, takes the ⊤-ward
variant from either operand
(`matches!(a, Conditional) || matches!(b, Conditional)`), and applies both to
every constructed result. Order symmetry is pinned by the seam-level
`join_lattice_*` property cells in `transfer/tests.rs` — no program involved —
because the pre-existing `msp7_chained_*` cells are program-*shape* cells over one
hand-built tree and are structurally incapable of failing on an order asymmetry,
which is why 0772 passed review-by-suite. The rustdoc at `transfer.rs:374-390`
carries the corrected rule at the seam; the crate `CLAUDE.md` §"The two
order/settlement seams" carries it as as-built memory.

So face 3 is covered, and it is covered by the composition — no new consumer arm
was authored for it, which was the design's substantive claim. What was wrong was
the *sufficiency* of row 4 as stated, and this section no longer states it that
way.

### 17.5 The 0693 disagreement-fence placement — BEFORE/WITH this fix

FIXME 0693 (`target: /dev`, backend) is the R3-gate MIRROR: the backend
`scrutinee_cow_retains_reused` (`fn_compiler.rs:1427`) re-derives the COW escape
gate from the **syntactic callee name** (`matches!(callee_name, "vec-set" |
"vec-push")`) instead of sharing the producer's carrier discriminator — a P7/P24
mirror, one level up from the R14 escape-fact re-derivation /arch already REJECTED
(`design/backend/ownership-codegen.md` §13.7). It is **currently masked** because
typecheck records `escapes = Some(false)` on the relevant scrutinee, so the mirror
declines a balancing dec anyway.

**Placement (binding on S115 sequencing):** the 0693 consolidation + its unit
disagreement fence MUST land **before or with** the §17.2 escape-fact correction,
because that correction is precisely the event that **lifts the mask** — §17.2
flips `escapes` to `true` at more may-alias sites, so the mirror's name-based
re-derivation can now diverge from the producer's carrier-driven decision (emit a
balancing dec for a producer inc that never happened → spurious dec of a forwarded
alias, the UAF direction 0693 names). Landing §17.2 without the fence is a plan
violation to report (test plan §1.1 item 2). The fence is:

1. **The consolidation** (backend `/dev`, out of this crate's scope — flagged as a
   cross-wave sequencing constraint): make the pair structurally ONE gate —
   either ONE shared predicate both `scrutinee_cow_retains_reused` and
   `cow_source_ownership::retain_reused` call (parameterized by operand + escape
   fact), OR have the producer record its retain decision (keyed by the Apply
   span, beside `pending_cow_escapes`) and have the match seam read THAT
   (Principle 24 — name is a trigger, carrier is identity).
2. **The unit disagreement fence** (backend `/dev`): over the §13.5-style matrix
   (builtin/user-named × live/non-live source × escapes true/false/absent ×
   return-source × both toggles), assert `mirror == producer-emitted-inc?`. This is
   the durable guard that any future escape-fact family change (§17.2 is the
   trigger) cannot re-open a producer/consumer disagreement silently.

`/design`(typecheck) records the placement and the causal reason (the mask-lift);
the consolidation code and the unit fence are `/dev`(backend)'s (0693's own
`target: /dev`, `refers_to` the two backend seams). `/testing` supplies the e2e
twin verification that the committed family shapes hold through the consolidation
(test plan §5 rider). **0693 is NOT deleted by this design pass** — it is the
backend `/dev`'s to resolve and delete once the consolidation + fence land.

### 17.6 The carrier-enrichment contingency trigger (precise)

/arch pre-authorized (SPRINT.md §2 constraint 2 / §7) ONE contingency: if the
family rule requires a **new `ResultMode` shape or advisory fact in
`cranelisp-types/src/ownership.rs`**, that is a `cranelisp-types` edit → FIXME
`target: /arch` + approval + ONE `CACHE_SCHEMA_VERSION` window (22→23), surfaced
AT Phase 3, never mid-wave.

**This design does NOT trigger it.** The §17.2 mechanism lives entirely in the
internal `transfer.rs::Origin` enum (the cow-alloc span-set) and the per-span
`WalkFacts.escapes` map — both walk-internal, exactly as §16.3's `Origin` reshape
was. For the two open faces the may-alias allocations are `MayAliasOf`-declared
**primitive leaves** (`vec-set`/`vec-push`; the `MayAliasOf(0)` is a §9 declared
fact) whose `Apply` node lives in THIS cluster's walk — the per-span escape-force
is fully reachable. No persisted-summary field is needed; the S115 plan assumes NO
schema bump.

**The precise trigger — surface at Phase 3/4 if `/dev` hits it, never absorb
mid-wave:** the contingency fires **iff** the may-alias protect obligation must
cross a **summary boundary** the internal `Origin` span-set cannot span — i.e. a
may-alias link is allocated **inside an imported/summarised USER-fn COW helper**
whose internal allocation span is NOT in the consuming cluster's walk, AND the
caller's per-`Apply`-span escape-force at the helper-call site proves insufficient
to drive the backend's retain for that inner link (the retain must be gated on a
fact the persisted `ResultMode`/summary carries, not on a caller-frame span). Then
the may-alias-protect obligation must ride the summary as a new advisory fact (e.g.
a `may_alias_protect_sites` marker, or promoting the internal cow-provenance to a
persisted per-site fact) → STOP, FIXME `target: /arch`, schema 22→23. A second
invalidation event, or any schema bump outside this named contingency, is reported
to `/sprint` as a plan violation (test plan §7 item 3). The two S115 faces stay
below this line (primitive-leaf COW, same-cluster spans).

### 17.7 Acceptance and riders

- **Flip:** both RED cells
  (`safety_lane_chained_nested_cow_projection_returns_set_value_abort_free_red`,
  `safety_lane_chained_let_bound_cow_projection_returns_set_value_abort_free_red`)
  GREEN under the tier-4 differential lane BOTH toggles × 3 modes (test plan
  §1.1 items 4–5).
- **Must-hold GREEN fences:** the whole-value nested-transfer negative control
  (§17.2); the immediate-face W7 flip
  (`safety_lane_..._cow_set_read_returns_set_value...`); the lane clean/green cells
  both toggles.
- **/review structural check (part of flip acceptance):** the fix is §16.2
  rule-table rows/corrections (rows 8/2/4/6) with NO new consumer arm — grep the
  `walk_apply`/`join_origin`/`walk` arm count; a 5th `MayAliasOf`/`ProjectionOf`
  per-shape arm is a REJECT (test plan §0 risk-1).
- **Unit tier (`/dev`, METHOD §2.2):** each corrected §16.2 row exercised —
  the chained-link cow-alloc span carried through the emitted accounting; the
  projection-out force covers ≥2 spans (test plan §6.5 §1.1).
- **0623 behavioral matrix rider (`qa`/`test`):** the §16.5 container-store ×
  projection-out × capture axes extend with the chain-length axis (≥2 links ×
  {nested, let} × {in-place, shared} × {REPL, `--link`}) **and with an arm-order
  axis** (FIXME 0777). Order symmetry is the property that failed at the join, and
  no cell in the behavioural lane tests it — the seam-level `join_lattice_*`
  property cells do, which is the right home for an algebraic property, but the
  behavioural matrix should still carry one cell per face with the COW producer in
  each `If` arm, because that is the shape a user writes.

---

## §18. The ungraded `unwrap_or` narrowings in the ownership walk (S121 C3)

**Status:** DESIGN (S121 Phase 3, `design`(typecheck)). Discharges the typecheck
arm of FIXME **0929** (site 1) and the successor obligation of FIXME **0762**.

### 18.1 Why these two are one item

Both sites answer a question they may not be able to answer, and both answer it
with a literal in `unwrap_or` position rather than with a refusal or a proof:

| Site | Expression | The question it cannot answer | Owner |
|---|---|---|---|
| `ownership/fixpoint.rs:221` | `ConcreteType::from_type(t).unwrap_or(ConcreteType::String)` | what heap class is a residual-typed parameter? | C3 |
| `ownership/transfer.rs:830` | `arg_origins.get(k).cloned().unwrap_or(Origin::Fresh)` | what is the origin of argument `k` when `k` is out of range? | C3 |

Root `CLAUDE.md` §Assurance names the failure state exactly: a claim that is
neither structural nor measured, carrying no named falsifier, is **not a grade**.
Both sites carry a rationale; neither carries a check; and one of them carries a
rationale that is narrower than the claim it supports.

### 18.2 Site 1 — `fixpoint.rs:221`, the seed placeholder

The enclosing rustdoc (`fixpoint.rs:213-216`) reads: *"Any non-`Fn` scheme, arity
mismatch, or non-concrete param type falls back to a non-scalar placeholder
(`String`) — never mis-classified as `Copy` (sound: a non-`Copy` param seeds
`Borrowed`)."* The sibling catch-all at `:223` does the same for the whole
parameter vector.

**The rationale is true and it protects one axis only.** It establishes that the
placeholder cannot make a heap parameter look `Copy`, which is the Copy⊑Borrowed
edge. It says nothing about whether a residual-typed parameter may legally *stay*
at `Borrowed` — below ⊤ `Owned` — through the fixpoint, which is precisely the
elide-an-inc consequence class R1/R18 exist for. So the grade today is
**"reviewed and correct on one axis"**, which §Assurance says is not a grade.

**The disposition, and the reason it is a refusal rather than a better default.**
The concreteness programme (`non-concrete-producer-obligations.md`) removes the
population that reaches this arm: after P-1 consumption every codegen-bound frame
has a concrete scheme, so `from_type` succeeds on every parameter of every frame
the ownership pass runs over. The arm therefore has two admissible end states, and
a defaulted placeholder is neither:

> **O-1.** The seed reads through the **types-owned refusing projection** rather
> than a local `unwrap_or`. A parameter whose type is not concrete makes the
> **frame** ineligible for per-parameter seeding, and the frame seeds at ⊤ —
> `Owned`, uniformly — which is the monotone-sound direction and needs no
> per-axis argument. The two model sites `arch` named on register row R18 are the
> required spelling: `program/support.rs:321`'s explicit `NotConcrete` match, and
> `cranelisp-types/src/heap.rs:310-334`'s `ctor_field_concrete_types`, whose
> `Option` collect makes one residual field refuse the whole constructor.
>
> **O-2.** The refusal remains observable by exact frame identity in
> `ownership/fixpoint.rs::residual_param_frames`; the existing ownership trace
> emits that set when enabled (`ownership/trace.rs::emit`). This observation
> explains which frames took the conservative seed. It is not the codegen-view
> refusal aggregate in `program/support.rs`, and it is not a zero-count gate:
> a non-zero set remains safe because every listed frame already seeds at ⊤.

The safety property comes from O-1's conservative branch. O-2 preserves the
population needed to inspect or falsify that branch without making a separate
counter part of correctness.

`qa`'s S119 plan cell **NC-3(b)** is the fail-on-revert unit row for this site and
stays as planned; O-1 changes what it pins from "the placeholder is `String`" to
"a residual parameter refuses per-parameter seeding and the frame seeds ⊤".

### 18.3 Site 2 — `transfer.rs:830`, the successor to FIXME 0762

**0762's central claim is falsified at source and the filing retires on it.** The
filing cites *"the `ProjectionOf` arm's `&args[k]`"* — a raw index over an
externally-derived, persisted `ModeSummary` index, one boundary past its
validation. There is no `&args[k]` anywhere in `transfer.rs` at HEAD. The §17.2
row-6 correction deleted that syntactic reach: the arm now iterates the container
`Origin`'s carried cow-alloc spans instead, and the only index read left is
`arg_origins.get(k)` at `:830` — checked, exactly as the filing asked for.

**The obligation the filing actually carried survives the falsification, and this
is the part that must not be lost with the file.** Principle 25's statement in
0762 — *validation at one boundary is not a licence for an unchecked read at the
consumer* — is discharged for the index. It is **not** discharged for the value
substituted on a miss:

> `arg_origins.get(k).cloned().unwrap_or(Origin::Fresh)` silently answers
> `Origin::Fresh` when `k` is out of range. `Fresh` means *"not aliased to any
> param"*, which a borrow-elision consumer trusts to drop a needed RC op — it is
> the **anti-conservative** point of this lattice, not the conservative one, and
> `join_origin`'s own rustdoc (`transfer.rs:357-365`) says so: *"`Fresh` is
> reserved for provably-no-param-reaches-result."*

The filing predicted the miss would be monotone-sound because "declining the
projection-provenance refinement widens toward the conservative point". At the
`get(k)` site that prediction does not hold: declining here narrows.

> **O-3.** The out-of-range answer is the lattice's ⊤ (`Origin::Conditional` over
> the reaching parameter set, i.e. may-alias), not `Fresh` — or, if the arm is
> believed unreachable, it is a **located refusal**, never a default. Which of the
> two is chosen is `dev`'s, on the evidence of whether any corpus program reaches
> it; the prohibition is on a silent anti-conservative default.
>
> This is the same rule §3.7 applied to `transfer.rs:590`'s `Fresh` default, and
> the precedent is instructive rather than permissive: that default was ruled
> **co-sound under the consuming convention** and kept only because the premise
> was then made explicit in rustdoc. There is no such premise here, and no rustdoc
> stating one.

**Relationship to `ResultMode`'s validation.** The R6 cache-load census validates
`MayAliasOf`, `ProjectionOf` and `AliasOf` indices exhaustively via
`result_mode_param_index` (S115 W3b, backend side), so the cache path cannot
deliver an out-of-range `k`. That makes the arm unreachable *today*, by an
argument about a different crate's boundary — which is the shape 0762 filed
against in the first place. O-3 is what makes the consumer's own answer safe
regardless.

**S121 status of O-3.** The default is already gone from source: the arm reads
`arg_origins.get(k).cloned().unwrap_or_else(|| self.unknown_param_origin())`, and the
same helper backs the `AliasOf`/`ProjectionOf` arms. What O-3 asked for and did not yet
have is a **truthful** ⊤: `unknown_param_origin` answers with the frame's LOWEST-index
parameter, which is the same representative fiction §13.6(c) retires. §19.3 makes it
answer with the frame's whole parameter set, so an out-of-range index publishes
`MayAliasAny` — the axis's real ⊤ — and a parameterless frame still proves `Fresh`.
O-3 closes there; §18.4's byte-identity fence is unchanged, because the arm remains
unreachable for every in-range `k`.

**The sibling that O-3 does NOT close: the absent-callee result read.** `walk_apply`
substitutes `ResultMode::Fresh` when the callee has no summary at all. That is the same
anti-conservative direction O-3 prohibits, at a site O-3 did not name, and §19.5 enlarges
its population. §19.7 records why it is retained, the premise it rests on and the
observation that would refute it; it is not silently defaulted any more, and it is not
changed in this change-set.

**0776's generalisation applies and is `arch`'s.** 0762's instrumentation note
proposes that every §4 register row whose subject is a closed sum be enforced by
an exhaustive match somewhere, not only described. That is a register-row
question, filed and owned by `arch`; C3 records that it applies to this family and
decides nothing about it.

### 18.4 Acceptance

- **O-1/O-2:** the seed refuses on a residual parameter, and the frame **publishes
  nothing** (§19.6 supersedes "seeds ⊤ and publishes it" — the ⊤ literal it seeded carried
  the same present-`Fresh` claim §13.6(h) retires); `residual_param_frames` contains that
  exact frame, while an all-concrete frame is absent. The ownership trace reports the same
  keyed set when enabled.
- **O-3:** a unit row over a seeded `arg_origins` shorter than `k` asserts the
  result is ⊤ (or that the call is refused), and **not** `Fresh`. This is a
  seam-level property cell in the `join_lattice_*` style — no program shape.
- **Byte-identity fence:** neither grade may change the emitted accounting for any
  frame whose parameters are all concrete and whose `k` is in range, which is every
  frame in the current corpus. A golden-CLIF or `CRANELISP_RC_STATS` movement is a
  finding, not a re-baseline.
- Both changes are **walk-internal** — `Origin` is not the persisted `ResultMode`,
  and the seed is not a carrier — so §17.6's contingency does **not** fire: no
  `cranelisp-types` edit, no `CACHE_SCHEMA_VERSION` participation, no public-API
  movement.


---

## §19. The S121 ownership-result correction — a truthful result axis, and refusal publishes nothing

**Status:** DESIGN, S121 Phase 5, `design`(typecheck). Approved by the user on
2026-09-07 in the direction proposed by `arch`: safe absence fallback, the
`ResultMode::MayAliasAny` addition (+1 variant, +1 `cranelisp-types/public-api.txt`
line), `CACHE_SCHEMA_VERSION` 26→27, platform ABI unchanged. The generated baseline
diff remains a separate post-implementation user gate. Nothing here is a language-spec
change, a new language constraint, or an additional facade change; anything that would
be returns to the user (§19.10).

**Governing:** `design/arch/ownership-inference.md` §3.7 (the conditional/unconditional
split and its naming reservation), §6.1 (the conservative point is total), §6.2 (the
differential oracle). This section amends §3.2, §13.5, §13.6(c), §13.6(h), §14.2, §14.4
and §18.3 of this document, each corrected in place.

### 19.1 What is wrong — two failures of one carrier

The `ResultMode` axis carries the claim a consumer acts on most sharply: the backend's
callee-side return protect is elided exactly when a summary is present and says `Fresh`
(`crates/cranelisp-backend/src/compiler/fn_compiler.rs::return_is_fresh_by_summary`). The
axis had four points and no ⊤, so the analysis had nowhere truthful to put "the result
reaches some parameter, which one undetermined". It put that value in two untruthful
places instead, and both were measured this sprint:

| | Measured | Where |
|---|---|---|
| **F-1 — the transfer does not converge** | `(defn f [i b] (if (eq-i64 i 0) b (f b i)))` publishes `MayAliasOf(1)` and `MayAliasOf(0)` on alternating visits, exhausting the cap at the production bound (44) and at 10,000; the recovery then published the ⊤ literal for **every** callable in the module (41/41 on the f4 fixture), so a builder that returns its accumulator lost its return retain | producer seam, `dev`(typecheck) unit run `a19d1ccd`; module census in `sprints/SPRINT.md` §Active checkpoint |
| **F-2 — the published claim is false even when it converges** | `pick2 [c a b] = (if c a b)` publishes `MayAliasOf(1)`; its caller `q [c p] = (pick2 c "lit" p)` publishes **`result=Fresh`** although `q` returns its own parameter `p` whenever `c` is false | `CRANELISP_OWNERSHIP_TRACE` on a three-line program, 2026-09-07, current binary |

F-1 is the lowest-index representative composed with itself: `walk_apply` reads
`MayAliasOf(r)` as "argument `r`", the self-call permutes, and the join's representative
flips — the involution `r ↦ 1 − r`, which has no fixed point. F-2 is the same discard
seen from the caller: the representative kept one reaching parameter and the caller
happened to pass a fresh value there. **They are one defect** — a join that is not a
join, on an axis that is not a lattice — and F-2 is why fixing convergence alone would
not be enough.

**F-2's exploitability is not established.** Two probe programs built to turn `q`'s false
`Fresh` into an observable use-after-free returned correct results, because the backend's
return-protect path has further gates (`body_has_independent_result`, cleanup-target
presence). What is established is that the carrier publishes a false claim to a consumer
whose whole job is to trust it. That is the defect this section fixes; whether it is
today reachable end-to-end is `qa`'s to attribute (§19.10).

### 19.2 The result axis becomes a join-semilattice with a real ⊤

`ResultMode` gains one variant, `MayAliasAny`, carrying no index: *the result either is a
fresh value or reaches into some parameter, which one undetermined.* The exact carrier
delta, the affected producers and consumers, the `public-api.txt` effect and the schema
consequence are `arch`'s and are recorded in the user-approved proposal; this section
designs the interior that produces and composes it.

The axis's order, stated as the joins the interior must realise (`i ≠ j`):

| join | result | reading |
|---|---|---|
| `Fresh ⊔ Fresh` | `Fresh` | no path carries a parameter |
| `AliasOf(i) ⊔ AliasOf(i)`, `ProjectionOf(i) ⊔ ProjectionOf(i)` | unchanged | every path is the same unconditional claim |
| `AliasOf(i) ⊔ ProjectionOf(i)` | `MayAliasOf(i)` | one index, kinds disagree |
| `Fresh ⊔ AliasOf(i)`, `Fresh ⊔ ProjectionOf(i)`, `Fresh ⊔ MayAliasOf(i)` | `MayAliasOf(i)` | one index, conditional |
| anything reaching `i` `⊔` anything reaching `j` | **`MayAliasAny`** | two indices ⇒ the ⊤ |

So the atoms are `Fresh` and the per-index unconditional claims; `MayAliasOf(i)` sits above
`Fresh` and above both unconditional claims for that index; `MayAliasAny` is above
everything.

Three properties this pins, none of which held before:

- **`Fresh` is an atom, not the ⊥ of the axis.** `Fresh ⊔ AliasOf(i) = MayAliasOf(i)`:
  "no parameter reaches the result" and "the result IS parameter *i*" are contradictory
  claims whose join is weaker than either. The optimistic seed is `Fresh` because that is
  the right *guess*, not because it is the lattice bottom — §19.8 is the consequence.
- **`MayAliasAny` is a weakening, never a strengthening.** A join of two distinct
  UNCONDITIONAL roots ("definitely a parameter, unknown which") also publishes
  `MayAliasAny`, which is a strictly weaker claim than the truth. That is deliberate: the
  axis names conditionality and index, and there is no point that names "definitely a
  parameter, index unknown". No later refinement may tighten this arm without adding that
  point.
- **The conservative value of the result dimension is now nameable.** The spine's §6.1
  list of per-dimension conservative values omits the result axis, because before this
  variant it had none. That is `arch`'s document; §19.10 files the row.

### 19.3 The reach SET replaces the representative

The walk-internal `Origin` (`transfer.rs`) is where the untruth was minted, and it is
where the fix belongs: the conditional origin carries **the set of parameter-rooted
bindings the value may reach**, not one representative of them. Concretely:

- `Origin::Conditional` carries a non-empty, deduplicated collection of reaching roots in
  place of its single `rep`. Everything else about the variant is unchanged, including its
  `projection` flag and its `cow` may-alias link set (§17.2) — the link set must survive
  the collapse, or the MS-P7 projection-out consumer loses the protect obligations it
  discharges.
- **The join is set union**, and nothing else: `Fresh ⊔ Fresh = Fresh`; unconditional ⊔
  unconditional over the same root and kind stays unconditional (the definite `AliasOf` /
  `ProjectionOf` regression pins in `transfer/tests.rs` must stay green); every other
  combination is conditional over the union of the two reach sets, with `projection` true
  only when every reaching path is a projection and `cow` unioned as today. Union is
  commutative, associative and idempotent by construction, so the P24 order-symmetry
  property the `join_lattice_*` cells assert is structural rather than tested-into-place.
- **Publication derives from the set, at the boundary only.** `origin_to_result_mode`
  resolves the reach set to distinct parameter indices: none ⇒ `Fresh` (an owned local
  returned by value); exactly one ⇒ `MayAliasOf(i)` (or the unconditional `AliasOf(i)` /
  `ProjectionOf(i)` when the origin is unconditional); two or more ⇒ `MayAliasAny`.
- **The set is walk-internal and per-visit.** The fixpoint compares `ModeSummary`, not
  `Origin`, so carrying a set costs the iteration nothing: the published value collapses
  at "two or more" and cannot grow further, which is why the oscillator settles on the
  visit after its first disagreement regardless of the permutation's cycle length. The
  cost that is not nothing is allocation: `param_roots` builds a `Vec` and a `HashSet`
  per call on the hottest walk path (once per `walk_var`, once per root inside `reach`,
  and `reach` twice per `join_origin`), where the retired `param_root` allocated nothing.
  Unmeasured, and no gate would observe a compile-time regression; the
  resolve-at-construction repair of §19.10 removes it.
- **`unknown_param_origin` answers with the frame's whole parameter set** (§18.3 O-3), so
  an out-of-range persisted index publishes ⊤ rather than a fictitious lowest-index
  may-alias, and a parameterless frame still proves `Fresh`.

Every consumer that followed the old `rep` follows every member of the set instead —
notably the parameter-widening chase (`param_roots` from `walk_var` and
`classify_capture_escape`), which is ABI-bearing. Both chases are measured against a
planted single-root retirement, on shapes with no §13.6(g) drain to mask them:
`transfer/tests.rs::{match_bound_conditional_widens_every_reaching_param,
escaping_capture_widens_every_reaching_param}`.

**The narrowing is NOT closed by construction, and it is not confined to the result axis.**
`Origin`'s roots are SYMBOLS resolved late against the flat `bindings` map, so a binder
reusing a parameter's name makes the chain self-referential and `param_roots` terminates
by dropping that root. Measured 2026-09-07 on `(defn f [a b] (let [a (if a b)] (if a
(fresh))))`: the published result is `MayAliasOf(0)` where the truth is ⊤ — one reaching
parameter named, the other dropped, so a caller passing a fresh value at the named
position composes it back to `Fresh`. The probe is
`transfer/tests.rs::self_shadowed_reach_set_result_is_top` (**known-red, unignored**),
against the sibling control `renamed_binder_reach_set_result_is_top` — byte-identical
body with the binder renamed, green at ⊤, so name reuse is the only variable. This is
the open §13.6(i) / S102 F4 class and not a regression: pre-S121 the same shape published
outright `Fresh`. In **this** `let` shape the ABI half does not narrow — the §13.6(g)
escaped-binding drain re-walks the RHS in its defining scope, where both names still
resolve to their parameters (`self_shadowed_widening_is_covered_by_the_drain`, green, and
the falsifier for that masking); `qa` re-derived the same answer on 2026-09-07, this
shape's `modes`/`flow` equalling its rename control's.

**That measurement is shape-specific, and this section over-generalised it.** The sentence
carried here until 2026-09-07 — that the loss "reaches publication on the RESULT axis
only", the ABI half being covered by the drain — is true of the drain-carrying shape it was
measured on and false as a claim about the class. A shape with no drain narrows the ABI
half as well: §20.1 rows C, C′ and C″ measure `modes`, `flow` and an argument's `escapes@`
site fact all moving under a shadow, one of them to a runtime abort. §20.1 is the corrected
record for the class; the drain measurement above stands for its own shape. The repair and
its authorization are §19.10 and §20.

### 19.4 One conditional-result arm at the call site

`walk_apply` composes a callee's result into the caller's origin. The two conditional
result points are one rule with two inputs:

> The callee's result may reach a **set of argument positions** — `{k}` for
> `MayAliasOf(k)`, *all* positions for `MayAliasAny`. Join `Fresh` with those arguments'
> origins, and when the outcome is conditional, union this `Apply`'s span into its
> may-alias link set (§17.2 row 8, unchanged).

The unconditional arms are unchanged: `AliasOf(k)` carries argument `k`'s origin verbatim,
`ProjectionOf(k)` roots at argument `k`'s origin per §17.2 row 6, `Fresh` yields `Fresh`.
The exhaustive match forces the new arm to be written; no wildcard arm may be added
(`crates/cranelisp-types/src/ownership.rs` module docs, §Exhaustiveness discipline).

Under this composition F-2 resolves: `pick2` publishes `MayAliasAny`, so `q` joins `Fresh`
with all three arguments, reaches `p`, and publishes `MayAliasOf(1)` — the truth. F-1
resolves because the self-call's contribution and the base case disagree on index exactly
once, after which both sit at ⊤ and the summary stops changing.

**No index filter is applied to the reach set.** A `Copy` parameter cannot in fact be
aliased, so excluding `Copy` positions would be sound and slightly more precise; it is not
done, because `MayAliasOf(i)` over a `Copy` parameter is already publishable today and the
filter would be a second rule for no established gain. Trigger for adding it: a measured
precision loss attributable to `Copy` positions entering a reach set.

### 19.5 Refusal publishes nothing, and there is one refusal

**Rule.** A cluster whose analysis does not converge publishes **no summary, no site fact
and no value-use mark** for any of its members. Absence is the single spelling of the
conservative point.

**The publication map is separate from the seed.** The optimistic seed must keep existing
— it is the working environment the walk reads — so the obligation is that **only a
transfer walk's output is publishable**. `compute_cluster` holds two maps: `working`, the
seed the `ClusterEnv` reads through the modes loop, and `walked`, whose one write site is
a completed `transfer` walk's output. On normal exit `working` is dropped and `walked`
becomes the map the confinement and uniqueness strata refine and `ClusterOwnership`
publishes. A walkable member that is queued and never walked is therefore **absent** from
the published map rather than carrying its seed — and the seed is the sharper literal (a
*present* `Fresh` with `Borrowed` params; the deleted `top` was at least ⊤ on the other
four axes). Re-entry is unchanged, because `changed` still compares against the seeded
value; the cost is one `ModeSummary` clone per visit.

**Grade: asserted, with a named falsifier — narrowed by one structural fact, not
unconstructable.** The structural fact is that the published container has a single write
site fed by a walk output, where it previously had two (seed, then walk). It is not more
than that, and the limit is measured rather than argued: planting the swap
(`summaries = working`) reddens **no** cell in the ownership tier, because the two maps are
content-identical whenever every walkable member is walked, and that condition is not
constructible through `compute_cluster`. **Named falsifier:** a walkable member queued and
never walked — `fixpoint.rs`'s `let Some(c) = by_key.get(&key) else { continue }` sits
ahead of the walk and today cannot fire only because `by_key` and `queue` are built from
the same list. A member the walk never produced (the refused cluster; the residual frame of
§19.6) has nothing to publish.

**Why absence rather than a now-truthful ⊤ literal.** With `MayAliasAny` in hand a ⊤
`ModeSummary` becomes expressible for the first time, and publishing it would be safe. It
is still the wrong choice. The literal that just failed was ⊤ on four axes and the
strongest claim on the fifth, and nothing detected that for the whole life of the code;
re-minting a "this time correct" literal restores exactly the construction that decayed
(root `CLAUDE.md` §Assurance, R11 and I-CT). Deleting the constructor removes the last
literal that could reach a consumer: after this change the only construction feeding the
published map is the converged walk's output, graded above. Absence also lands the refused
cluster on the `CRANELISP_NO_OWNERSHIP` shape, whose end-to-end safety the differential
oracle already measures, instead of on a shape that needs its own argument.

**One refusal, all three strata.** The modes worklist, the confinement worklist and the
uniqueness stratum each carried their own cap-exhaustion recovery. They collapse into one:
any stratum exhausting the shared cap refuses the whole cluster. This is a net deletion
(three recovery blocks and their literals become one early return), it removes the
confinement recovery's asymmetry — it forced `spark_ops` to ⊤ while leaving each site's
already-written `confined` fact at whatever partial value the interrupted pass had reached
— and it needs no argument about which partial facts are salvageable. The precision cost
is a cluster that converges on modes but exhausts on confinement losing everything; that
has never been observed, and after §19.3 the known non-convergent class no longer reaches
the cap at all.

**The refusal is observable, and the observation is armed.** `ClusterOwnership` carries
the refusal (the exhausted stratum, the visits consumed, the cap, the universe size);
`ownership/trace.rs` renders one line for it beside the existing
`residual-parameter-refusals` line, under the same `CRANELISP_OWNERSHIP_TRACE` gate. That
is the whole instrument — no counter in `[RC_STATS]` (wrong crate, and the question is a
compile-time one), no new environment variable. The residual it observes is silent
precision collapse, not a correctness risk, so it earns a trace line and nothing more.
Detection is proved in the same change-set by both legs at the seam: the `cap = 0` seam
yields a refusal and an empty summary map, and a converging cluster yields no refusal and
a full one. Neither leg needs stderr capture, because the refusal is a value.

**The confinement arm is unexercised, and the shared cap is not why.** `cap = 0` refuses at
`Stratum::Modes` and a tuned cap reaches `Stratum::Uniqueness`; no cell executes the
`Stratum::Confinement` arm. The strata share the cap VALUE but keep separate counters
(`visits` / `cvisits`), so confinement can exhaust independently of what modes consumed —
the arm is **asserted, not measured**, and any argument resting on a shared budget is
wrong. Its falsifier is a spark-propagating chain plus a tuned cap, the construction that
already produced the uniqueness leg.

### 19.6 Residual-parameter frames publish nothing too

A frame whose scheme still carries a residual parameter type refuses per-parameter seeding
(§18.2 O-1) and is never walked. It published the same ⊤ literal, including the same
present-`Fresh` claim, and therefore had its own return protect elided — the §13.6(h)
hazard on a frame the fixpoint never touches. It now publishes nothing, by the same rule
and the same constructor deletion; `residual_param_frames` keeps the exact keyed set for
the trace, so O-2's observation is unchanged. This is behaviour-identical at the frame's
**callers** (absence and a present all-`Owned` summary read the same through the
conservative accessors) and strictly safer at the frame itself.

**The member fence — how absence is realised inside the pass.** A cluster member with no
walk output must read as ABSENT at the pass's own callee-fact environments, not fall
through to the summary a PREVIOUS compile persisted on its symbol-table entry: the
chain-follow that serves imports and declared leaves would otherwise deliver a stale fact
for exactly the frames this section refuses, and `collect_universe` does not filter on
`code: None`. `compute_cluster` therefore carries the universe's key set, and every
private-env read consults it before the chain-follow — `ClusterEnv::summary_of`,
`UniqClusterEnv::summary_of` and `UniqClusterEnv::result_unique_of`. Its live path is REPL
redefinition and incremental compilation, which the `CACHE_SCHEMA_VERSION` bump does not
fence within a session.

Measured by `fixpoint/tests.rs::a_cluster_members_persisted_summary_is_never_read`, which
installs a prior compile's summary on the residual member's entry and asserts all three
reads refuse it, with the negative twin `a_non_members_persisted_summary_is_read` putting
the same summary on a non-member and asserting all three DO read it — so the fence is keyed
on membership and nothing else. Each fence was deleted in turn and reddened its own leg
while the twin stayed green; the `UniqClusterEnv::summary_of` leg needed a caller whose
returned binding's uniqueness depends on whether the call consumes it, because no
pre-existing cell discriminated it.

### 19.7 What deliberately does not change

- **The absent-callee result read stays `Fresh`.** `walk_apply` substitutes `Fresh` when a
  summarised callee has no summary at all, and §19.5 enlarges that population to include
  every member of a refused cluster. The claim is retained on a stated premise, not by
  default: **a callee compiled with no summary is lowered Decision-24, which materialises
  an independently owned result**, so the caller's value is not a borrowed view of the
  caller's own parameters and `Fresh` is co-sound. For the population §19.5 adds, that
  premise is the `CRANELISP_NO_OWNERSHIP` lowering itself, which the differential oracle
  measures. For the pre-existing population — host-promised externs, and callables outside
  the strict-concrete universe such as generated accessors — the premise is asserted, and
  it is load-bearing: measured 2026-09-07, `(defn get-inner [b] (inner b))` over a product
  accessor publishes `result=Fresh`, resting entirely on the accessor materialising.
  **Falsifier:** any callable reachable at an absent summary that returns a parameter's
  reference without materialising it. Filed to `qa` (§19.10); not changed here, because
  the alternative — reading absence as ⊤ on the result axis — puts typecheck at odds with
  `ModeSummary::is_abi_conservative`'s published `None ≡ all-Owned/Fresh` equivalence,
  which is a `cranelisp-types` semantic change and therefore the user's.
- **`ModeSummary::abi_eq` / `is_abi_conservative` are untouched**, and so is the R3
  redefinition gate that reads them. Because nothing publishes a ⊤ literal any more, no
  new `None`-versus-⊤ comparison arises.
- **The uniqueness stratum is untouched.** It admits only `Fresh` results, and
  `MayAliasAny` is not `Fresh`, so the new point is excluded exactly as `MayAliasOf` is.
- **The S121 self-reentry correction stays.** Re-enqueueing a callable on its own summary
  change is what lets a self-recursive body reach its fixpoint at all; restoring the
  `other != &key` guard would hide non-convergence by never re-visiting, which is why QA
  ruled it out as a fix. With §19.3 the self-edge now terminates.
- **Replace-on-update stays in the worklist.** Joining each visit's output into the stored
  summary would force an ascending chain, but at the first visit it would turn every
  exact `AliasOf(i)` into `MayAliasOf(i)` — a precision loss across the whole corpus, in
  exchange for a termination guarantee the cap already provides safely (§19.8).
- **No SCC narrowing of the refusal.** Refusing only the non-converged strongly-connected
  component and its dependants would need an SCC pass over the harvested `DepSet` to buy
  precision on a path that should now be unreachable. §13.6(h)'s argument for
  universe-wide scope stands.

### 19.8 Termination, stated honestly

After §19.3 the result axis is a finite join-semilattice with a ⊤, and every transfer rule
is monotone in the callee summaries it reads. That is **not** a termination proof, and this
document no longer claims one (§3.2). The iteration is optimistic-init: the seed `Fresh` is
a claim, not the axis's ⊥, so the first computed value for a callable can be incomparable
to its seed and the Kleene induction does not start. What is available:

- **Measured, for the known class — as a falsifier, not as a prediction.** The two
  `dev`(typecheck) cells committed this sprint fail today on the permuting self-call, at
  the production cap and at 10,000 visits. That this design converges that shape in three
  visits is derived by hand, not run; those cells are the standing falsifier and the design
  is wrong if they do not flip.
- **Grade: structural, for the consequence.** Reaching the cap can no longer publish an
  untrue claim (§19.5), so non-termination costs precision and nothing else.
- **Named residual:** a body shape whose result oscillates under the set-union join is not
  proven impossible. Its refuter is the refusal trace line (§19.5) firing on a corpus
  compile. If one is found, the next step is the ascent discipline this section declined
  (join-on-update after the first visit), not another literal.

### 19.9 Change-sets, order, evidence

**One wave, three reservations, in the order the primary set: types → typecheck → backend
cache.** The tree does **not** compile between them, by design: `ResultMode` carries no
`#[non_exhaustive]`, so adding the variant is what forces both consumer matches to be
revisited (`crates/cranelisp-types/src/ownership.rs` module docs, §Exhaustiveness
discipline). A green build is owed at the end of the wave, not at each step, and the
`dev` release gate (`sprints/METHOD.md` §2.3) applies to the wave.

| # | Reservation | Content | Owner |
|---|---|---|---|
| 1 | `crates/cranelisp-types` | the `MayAliasAny` variant + its rustdoc; regenerate `public-api.txt` (forecast: exactly one added line, the post-implementation user gate) | `arch` |
| 2 | `crates/cranelisp-typecheck/src/ownership` | §19.3 reach set + union join; §19.4 conditional-result arm; §19.3 `unknown_param_origin`; §19.5 refusal (delete `top`, `reset_to_top`, `conservative_site_facts` and the three per-stratum recoveries) + the refusal value and its trace line; §19.6 residual frames | `dev`(typecheck) |
| 3 | `crates/cranelisp-backend/src/cache` | the forced `result_mode_param_index` arm (`MayAliasAny` carries no index ⇒ no arity check) and its R6 negative cell; `CACHE_SCHEMA_VERSION` 26→27 with its version-log entry — a soundness invalidation, because a sidecar written by the current tree may carry a present-`Fresh` ⊤ for a permuting body | `dev`(backend) |

No other crate moves: `cranelisp-primitives` only constructs `ResultMode` (no leaf declares
the new point), `src/redefine.rs`'s `{:?}` is a display, and the platform ABI, DLL manifest
and `ABI_VERSION` have no `ModeSummary` contact at all. The variant-adding change-set
re-runs the standing escape grep (`_ =>` / `== Fresh` over `ResultMode`) to confirm no third
binary read has appeared.

Module-test obligations for reservation 2, red-first, per submodule
(`sprints/METHOD.md` §2.2):

- `ownership/transfer` — the join as a lattice: union, commutativity, idempotence and the
  `MayAliasAny` collapse at two distinct reaching parameters, in the existing
  `join_lattice_*` style; the F-2 shape at the seam (a callee publishing `MayAliasAny`
  composed by a caller passing one fresh and one parameter argument must publish
  not-`Fresh`); the O-3 out-of-range row asserting ⊤; the existing definite-case regression
  pins unchanged.
- `ownership/transfer` re-expectations: `multi_distinct_param_return_is_not_fresh` now
  expects `MayAliasAny` rather than "the lowest reaching index"; its `assert_ne!(…, Fresh)`
  leg is the part that must not move.
- `ownership/fixpoint` — the two S121 convergence cells flip green with the annotated
  non-permuting control still green; a three-parameter rotation `(f b c i)` and QA's
  `find-min-helper` over `(Vec Int)` are added as convergence cells, because the general
  trigger set is not established (`unit-report.md` §8); `cap_exhaustion_publishes_conservative_top`
  and `cap_exhaustion_forces_conservative_site_facts` re-expect "publishes nothing";
  `cap_exhaustion_resets_uniqueness_to_false_and_no_sites` folds into the single refusal;
  the refusal's two detection legs (§19.5).
- `ownership/publish` — a refused cluster writes nothing through the publication funnel.

**Evidence that is not this crate's:** the three committed e2e witnesses in
`tests/s99_fixtures.rs` and the four pre-existing f4 REDs. That they flip is `qa`'s
single-mechanism reading, and it is a prediction until the run exists — the design does not
assume it.

**Golden posture.** The wave is emission-affecting: bodies that today publish a
representative `MayAliasOf` publish `MayAliasAny` (identical codegen, binary consumer), but
callers whose composition today collapses to `Fresh` through a discarded reaching parameter
will publish not-`Fresh` and keep a return protect they currently elide. That movement is
the F-2 correction and is expected; every moved golden is attributed to this seam before any
recapture, under the standing hold in `tests/plan/s121-test-plan.md` §14.2 and the spine's
scoped-re-baseline rule.

### 19.10 Residuals, filings and triggered extensions

- **To `arch`:** the spine's §6.1 per-dimension conservative-value list omits the result
  axis; `MayAliasAny` supplies the missing value and the row should say so. Also `arch`'s
  own §4.4 observation — whether `result` belongs in the caller-visible ABI half at all, and
  hence in `abi_eq` — remains open and is not touched here.
- **To `qa`:** the §19.7 falsifier. Is any callable reachable at an absent summary
  non-materialising? The two populations to attribute are host-promised externs and
  callables outside the strict-concrete universe (generated accessors are the measured
  instance). Related, and separate: whether F-2's false `Fresh` is reachable end-to-end —
  two probes said no, and `design`'s remit stops at the carrier's truthfulness. Also the
  §19.3 residual, which attributes to the open §13.6(i) / S102 F4 class: this wave does not
  close that class, and the conditional e2e trigger — a macro-generated `(let [a a] …)`
  shape (stdlib `case`/`cond`) reaching an ABI-bearing parameter — is `qa`'s to allocate,
  not this section's to assume.
- **Potential extension, with its trigger:** filter `Copy` parameters out of the reach set
  (§19.4). Trigger — a measured precision loss attributable to `Copy` positions.
- **Potential extension, with its trigger:** join-on-update after a callable's first visit
  (§19.8). Trigger — the refusal trace line firing on a corpus compile after the wave lands.
- **Open residual, direction since approved — the self-shadowed reach set (§19.3).** The
  published result names one reaching parameter and drops the other when a binder reuses a
  parameter's name; the probe
  `transfer/tests.rs::self_shadowed_reach_set_result_is_top` is committed known-red and is
  the record. The repair is to resolve `Origin` roots to parameter INDICES at construction
  instead of carrying symbols resolved later against a flat `bindings` map: it makes
  §19.3's closure genuinely structural, and it dissolves the `param_roots` allocation
  (§19.3) at the same time. It was not authorized in the §19 wave and is not designed here.
  **→ §20 carries the design and, since 2026-09-07, the as-built record. The user approved
  its direction together with the `CACHE_SCHEMA_VERSION` 27 → 28 that landing it requires, and
  both landed the same day; what is outstanding is the wave's acceptance, not its
  construction.**
  §20.1 also records the measured evidence that this residual is NOT confined to the result
  axis, correcting §19.3 above.

---

## §20. Parameter reach resolved at `Origin` construction (the shadowing correction wave)

**Status: APPROVED AND AS BUILT (2026-09-07) — NOT YET ACCEPTED OR RELEASED.**
`design`(typecheck); reconciled to source 2026-09-07. The user approved the
stable-parameter-origin direction below and the `CACHE_SCHEMA_VERSION` 27 → 28 epoch §20.5
shows it requires, both on 2026-09-07; both landed the same day, as two reservations of one
wave — `crates/cranelisp-typecheck/src/ownership/transfer.rs` with its module tests (in two
change-sets, the second closing the `bind_pattern` arm), and `crates/cranelisp-backend`'s
cache surface for the epoch. The sections below are written **as built and verified against
source**, and say so wherever an as-built rule is narrower or more precise than the approved
wording. What is *not* done is the wave's acceptance: independent review, the full-workspace
census, the CLIF-golden recapture hold and the generated `public-api.txt` diff returning to
the user. §19 is the approved, landed design and is unchanged here except where §19.3 and
§19.10 are corrected in place against §20.1's measurements. This closes §19.10's last bullet.
No language-spec change, no new language constraint, no facade change.

### 20.1 What is measured — and where it differs from the §19.3 record

§19.3 recorded the residual as **result-axis only**, with the ABI half masked by the
§13.6(g) drain — a generalisation of one drain-carrying `let` shape (§19.3, corrected in
place). Real-source observations on the **pre-fix** tree's binary
(`CRANELISP_OWNERSHIP_TRACE=1`, own scratch dir, each paired with a control differing
**only** in the binder's name) show a wider class. Every row of the table is a **pre-repair**
measurement, retained as the record of what the defect published. `qa` independently
reproduced every row on 2026-09-07 and added the last two; the binary and both comment-stripped source hashes were re-checked against the prior
verified checkpoint, closing `qa`'s open mtime caveat.

| Program (each under `(import [primitives …])`) | Published | Truth | Renamed-binder control |
|---|---|---|---|
| **A** `(defn f [flag a b] (let [a (if flag a b)] (if flag a (str-concat a "!"))))` | `result=MayAliasOf(1)` | `MayAliasAny` | `MayAliasAny` |
| **B** `(defn g [p] (f true "lit" p))` — A's caller | `g: result=Fresh` | `MayAliasOf(0)` (conservative composition) | — |
| **C** `(defn f [a n] (let [x a] (let [a n] x)))`, `a:String`, `n:Int` | `modes=[Borrowed, Copy] result=AliasOf(0) flow=[Consumed, Consumed]` | `modes=[Owned, Copy] result=AliasOf(0) flow=[IntoResult, Consumed]` | `modes=[Owned, Copy] … flow=[IntoResult, Consumed]` |
| **C′** as C with the shadow's RHS a fresh literal — `(let [x a] (let [a "q"] x))` | byte-identical to C's summary | as C's | `modes=[Owned, Copy] … flow=[IntoResult, Consumed]` |
| **C″** as C with both parameters `String` — `(defn f [a b] (let [x a] (let [a b] x)))` | `modes=[Borrowed, Owned] … flow=[Consumed, IntoResult]` | `modes=[Owned, Borrowed] … flow=[IntoResult, Consumed]` | `modes=[Owned, Borrowed] … flow=[IntoResult, Consumed]` |

**C is the face that is not on the result axis.** Its summary is self-contradictory — the
result IS parameter 0, which is simultaneously `Borrowed`/`Consumed` — and the argument
literal's `escapes@` site fact is absent where the control has it. **Observed: C aborts at
runtime** under `--run` (cached and `--no-cache`) and as a `--link` executable, with
`STALE RC DEC (consume_shallow): dec of non-live heap pointer … already freed + reclaimed`,
deterministically and with no `--run`/`--link` divergence; the renamed control exits clean,
and `CRANELISP_NO_OWNERSHIP=1` makes C exit clean too. So the ABI half of the summary is the
mechanism, not a bystander.

**C′ shows the same defect landing silently, and that matters more than the abort.** Its
shadow binder's RHS reaches no parameter at all, yet it publishes C's summary byte for byte
and *exits correctly* — while running one `rc_inc` short of its control (646 vs 647) with
one extra dealloc (57 vs 56), `CRANELISP_RC_TRACE` showing the argument string freed and its
chunk re-allocated under the still-live result. Abort versus silence is allocator timing, so
neither exit code nor the abort string is a sufficient oracle for this class. RC parity
against a rename control is the oracle **for C′** — and §20.6 records, as built, that it does
not extend to the class: C″'s subject and control are counter-identical under ownership ON,
where only the ON/OFF differential fires.
the modes *permute* onto whichever parameter the shadow binder's RHS happens to reach.

**B is a carrier-composition row, not a demonstrated runtime alias.** A's narrowed
`MayAliasOf(1)` composes at `g`'s call site — where argument 1 is the literal — to a
published `result=Fresh`, discarding the may-reach on `p` that A's truthful ⊤ carries at
argument 2. That is the F-2 discard crossing a procedure boundary on real source, and it is
what the row is for. It is **not** an observed alias: the measured program passes the
literal `true` for `flag`, so `g` returns the literal and never returns `p` at runtime. The
runtime faces are C and C′; do not cite B for one.

The §19.3/§19.10 record — result-axis only, ABI half masked, no demonstrated runtime failure
— is falsified by C and C′, and both sections are corrected in place. Re-attribution is
`qa`'s, not this section's (§20.6).

### 20.2 Mechanism — one late resolution, re-derived at every read

`Origin` carries binding **names**. `Walker::param_roots` re-derives *which parameters this
value reaches* from a name, against the flat `bindings` map, **at every read** — including
reads taken after `restore_frame` has changed what that name denotes:

```
              mint site (correct)         read site (wrong)
  A   (if flag a b) → roots {a, b}   in (let [a …]): "a" → the binder → chain self-refs,
                                                      drops p1            ⇒ reach {2}
                                     after restore:  "a" → parameter 1    ⇒ MayAliasOf(1)
  C   x = a     →  root "a"          in (let [a n]): "a" → the binder → "n"
                                                                          ⇒ widens p1, not p0
                                     at publication: "a" → parameter 0    ⇒ AliasOf(0)
```

The reach is right where the origin is minted; only the re-derivation is wrong — **Principle
24** (resolve once; the corollary's "bare name past the seam" marker) in spatial form, and
**Principle 26**'s acid test with *where in the scope stack* for *where in the pass*. The
language is unambiguous (`spec/04-expressions.md` §Shadowing — a chain of lexical scopes), so
no spec question is attached.

### 20.3 The repair — resolve at construction, delete the re-derivation

Carry the parameter reach **on** the `Origin`, resolved where the origin is minted:

- `Origin::Unconditional { root: Symbol, param: usize, projection: bool }` — `param` is the
  parameter this value IS, fixed at mint, and **total**: an unconditional origin that reaches
  no parameter is not representable. `root` survives for the one *purpose* that needs a live
  binding identity rather than a reach — the `facts.provenance` fact (§13.6(d)) — which has
  **two** emission sites, not one: the row-6 projection-out fact keyed by the `Apply` span
  and the arm fact keyed by the arm span (`transfer.rs::walk`'s `ResultMode::ProjectionOf`
  arm and `transfer.rs::bind_pattern`; `crates/cranelisp-typecheck/src/ownership/sites.rs::annotate`
  copies them onto `MonoExpr::Apply.provenance` and `MonoMatchArm.provenance`). `root` is
  never resolved to an index, and what it *denotes* is fixed by the mint chain below: it is
  always the **formal parameter's name** — the seed carries the formal's own name, every
  other mint inherits it verbatim, and `Let`/`ParBind` insert an RHS origin without
  re-rooting — so it is not a claim about which binding is live at the emitting span.
  §20.5(i) states what consumers do with the emitted fact and what that does not establish.
- `Origin::Conditional { params: <sorted index set>, projection, cow }` — §19.3's reach set as
  indices. `cow` (§17.2) unchanged.
- **Every mint inherits.** The parameter seed carries its own index; `walk_var` returns the
  binding's origin verbatim; `bind_pattern`, `walk_apply`'s four result arms and the aggregate
  rows carry the operand's set through; `join_origin` unions. **No site resolves a name to an
  index**, so `param_roots`' name graph, its visited set and its per-call `Vec`+`HashSet` (the
  §19.10 allocation residual) are deleted, and `BindState::param_idx` dies with them.
  `unknown_param_origin` is `0..arity` off the frame's parameter count; it no longer scans
  `bindings` for a `param_idx` a shadow corrupts. As built (`transfer.rs`, 2026-09-07):
  `Walker::param_roots`, `Walker::reach`, `Reach` and `BindState` are gone, and `bindings` is
  a plain `HashMap<Symbol, Origin>` over a `Vec<(Symbol, Option<Origin>)>` scope frame.
- **`classify_capture_escape`'s recursion is deleted, not guarded** (see below), so that
  function resolves no name past its own argument either.
- `origin_to_result_mode`, the §19.2 lattice and the §19.4 call-site arm are **unchanged** in
  meaning: they read the set instead of resolving it. As built, `origin_to_result_mode` and
  `join_origin` use nothing from the walker once the reach is carried and are free functions
  of their operands.
- **One reach, three readings — preserved deliberately; the approved wording did not name
  it.** The retired resolver did **not** follow an unconditional PROJECTION when widening at
  an ordinary use — a bare accessor's borrowed view must not make its parameter `Owned`, the
  §4.4 rc-free read path — while it *did* follow one for the result axis and, through the
  recursion, for a capture. Carrying one index collapses those three readings into one and
  silently over-widens; `match_arm_binding_is_projection_of_scrutinee` caught it (`Owned`
  where `Borrowed` is required). The distinction is carried by
  `Origin::params_widened_by_use()`: an ordinary use widens through an alias and through a
  CONDITIONAL projection — which may alias on some path, so over-approximating is sound —
  but not through an UNCONDITIONAL one; a capture and the result axis read the whole reach
  set. No new state: the existing `projection` flag decides it. A later reader collapsing the
  two accessors back into one re-opens this paragraph.
- **`bind_pattern` inherits under a shadow too.** Its `shadow` flag is one flag over two axes
  whose safe directions are **opposite**: suppressing the provenance fact is the conservative
  direction at the one eliding consumer and stays (§20.5(i), which states what that
  establishes and what it does not), while minting `Fresh` for the arm's bindings is the F-2
  narrowing, since `return_is_fresh_by_summary` elides the return protect on a `Fresh`
  result. As built, `shadow` gates the `facts.provenance` insert and nothing else, and the
  bindings take the ordinary inherit path (whole-`Var` verbatim, else a projection of the
  scrutinee). This arm was the one §20.3 site the first change-set left unrepaired; it was
  measured RED — `(defn f [p] (match p [(Box p) p]))` publishing `result=Fresh` against its
  one-identifier rename control's `ProjectionOf(0)` — and closed in a second change-set the
  same day.

**Why `param` is total, and why that retires the capture recursion.** `Origin::Unconditional`
has exactly four mint sites, and each either *is* the parameter seed or *inherits* an
unconditional operand: the per-parameter seed (`root` = the parameter's own name, index
known); `join_origin`'s definite arm (it keeps one already-index-paired member of the joined
reach set); the `ResultMode::ProjectionOf` arm (inherits the container's unconditional
origin); and `bind_pattern` (inherits the scrutinee's). The two sites that could introduce a
**non-parameter** root do not: a projection out of a `Fresh` container and a pattern bind of
a `Fresh` scrutinee both yield `Fresh`, never an unconditional origin rooted at a local. By
induction over those sites, every unconditional origin reaches exactly one parameter, so
`param: usize` loses nothing and a local-rooted unconditional origin stops compiling.

That is what removed the last name-based resolution from `classify_capture_escape`. Its
recursion existed to reach a parameter through an unconditional **projection**, which
`param_roots` did not follow; with the index carried, the function's own widening covers that
case at the top and the recursion had no remaining input. Deleting it is strictly safer
than guarding it: the recursion decides which binding reaches `self.escaped`, and under a
shadow a wrong recursion loses the *right* binding's escape edge — `escapes = Some(false)` ⇒
stack allocation ⇒ the FIXME-0524 dangle. That is a narrowing, not imprecision, and it is not
a residual worth carrying when the representation can make it unconstructable.

**Grade and falsifier — two claims, and they do not share a grade.** *Absence* is
**structural**: `param: usize` makes an unconditional origin reaching no parameter fail to
compile, so a future mint site that genuinely needs a non-parameter root re-opens this
paragraph rather than silently narrowing, and that compile error is the falsifier. *Correct
inheritance* is **measured**, not bought by the type — a present-but-wrong index type-checks
exactly as well. It is carried by the subject/control cells §20.6 lists: the pre-fix reading
of `shadowing_binder_must_not_permute_the_obligation` was `[Borrowed, Owned]` against its
control's `[Owned, Borrowed]`, an index that was present and wrong, so those cells
discriminate mis-inheritance and not merely absence. The mint-site enumeration that licenses
totality remains a source reading (`transfer.rs`, 2026-09-07).

Through the scope forms behaviour moves only where a name was mis-resolved: `Fresh`,
unconditional same-index joins, the `Fresh` collapse of a no-parameter join, `restore_frame`,
the §13.6(g) drain and the §17.2 link set with its row-6 discharge all keep today's semantics.
A, B, C, C′ and C″ then publish their truth column above.

### 20.4 Alternatives considered

| Alternative | Why not |
|---|---|
| Lexical binding **identities** (a scope stack keyed by binder identity, not name) | Correct and more general, but `facts.provenance` crosses the boundary as a bare `Symbol`, and changing that carrier is an `arch`/backend seam, out of this wave. §20.3's total parameter index closes the escape axis without it; what would still want it is the symbol-carrying provenance fact, whose actual consumer position §20.5(i) records |
| **Seal** origins at scope exit (substitute restored binders) | Incomplete: C is already wrong *inside* the scope, and it keeps the redundant re-derivation |
| **Alpha-rename** shadowing binders | The walk does not own the AST, and the backend needs source symbols |
| **Refuse** (publish nothing, §19.5) for any body shadowing a parameter name | Sound and small, but stdlib `case`/`cond` expand to `(let [a a] …)`, so it de-optimises broadly and silently. Offered as **containment** if the wave cannot be scheduled |

### 20.5 Impact

**No boundary moves.** `Origin` and the walker state it lives in are private to
`transfer.rs` — `Reach` and `BindState` are deleted outright (§20.3) — so there is no
`cranelisp-types` edit, no `public-api.txt` line and no platform ABI change. Published summary
**values** change for affected programs — more `Owned`/`IntoResult`, more `ProjectionOf`, more
`MayAliasAny`, always toward the conservative point — which moves CLIF goldens into the
recapture hold that already exists. As built, no golden was recaptured and none reddened in
the bands run.

**`CACHE_SCHEMA_VERSION` 27 → 28 IS required, was approved, and IS APPLIED.** The user
approved the bump on 2026-09-07 as part of this wave's landing change-set, and it landed the
same day at `cache/mod.rs::CACHE_SCHEMA_VERSION` with its version-log entry, the tripwire
moved to 28, and one added module witness,
`cache/serialize/tests.rs::cache_v27_meta_rejected_after_shadowed_param_reach_correction` —
authored before the bump and measured RED against the live 27 (a pre-fix sidecar was
*honoured* at HEAD), with the other 78 cache cells silent, which is also the measurement
establishing that no existing cell observes this value-only epoch. The sentence this section
carried before the approval — no bump, because no serde shape moves and `BUILD_ID` already
invalidates persisted summaries on rebuild — was wrong on both halves (`arch`,
source-verified 2026-09-07):

- **`BUILD_ID` does not cover it.** It is `<pkg_version>+git rev-parse HEAD`
  (`crates/cranelisp-backend/build.rs`), so an *uncommitted* landing build stamps the pre-fix
  sha and a pre-fix sidecar loads into a post-fix compile. Its own rustdoc
  (`cache/mod.rs::BUILD_ID`) states it is an **additional** trigger that does not replace the
  manual bump, and that cross-branch reuse without a compiler rebuild is caught only by the
  schema gate. This is the identical hole recorded as the reason for the S103 15 → 16 bump.
- **"No serde shape moves" is the wrong test.** What changes is persisted *meaning*.
  `ModeSummary` persists on `Life::Concrete.mode_summary` and on the `codegen_view`;
  `callee_summary_at` reads it for **cache-restored** entries; `param_mode` drives caller
  arg-protects and callee RC, and `return_is_fresh_by_summary` elides the return protect on
  `result == Fresh`. The current tree is already at schema 27 **with the defective producer**
  — §20.1's rows were measured on it — so schema-27 sidecars carrying C's false
  `Borrowed`/`Consumed` and B's false `Fresh` are producible today, and schema 27 cannot
  distinguish the two epochs. A warm hit on unchanged source resurrects exactly the elision C
  measures as a `STALE RC DEC` abort, which no source hash or shape check can catch; paired
  `.o` files bake the pre-fix RC contract on the generated-code axis too. Bumping on
  value-only soundness invalidation is the established discipline here — 13→14, 19→20, 21→22
  and this sprint's own 26→27 are all of that kind.
- **Smallest adequate handling, and nothing more — AS BUILT:** the literal at
  `cache/mod.rs::CACHE_SCHEMA_VERSION`, its version-log entry, and the bump tripwire at
  `cache/serialize/tests.rs::result_context_instances_round_trip_complete_links`, plus the one
  module witness above. Owner `dev`(backend), taken as a backend-cache reservation in this
  wave. No new mechanism, no serde change, no `CacheStale` variant, no new serialized field.
  Consumers: none — every schema-27 sidecar and paired object is rejected wholesale as
  `CacheStale::SchemaMismatch`, with no translation path and none built; the pre-fix objects
  bake the pre-fix RC contract, so wholesale rejection is the correct handling.
  `public-api.txt`: **zero delta** (the baseline records both consts without their values).
  `--link` is closed-world and needs nothing. Any other persisted-meaning change landing in
  the same wave rides this one window (S111 0621 / S119 precedent).

**What the epoch does and does not establish.** It establishes that the two epochs never
mix, and that refusal is now continuously measured by a check proven to detect its own
absence. It establishes **nothing** about whether the post-fix summary values are correct —
that is §20.6's evidence, not the cache's. And a warm-cache stale-summary observation taken
*after* the bump (alternating source at the already-applied epoch 28) is not a demonstration
of schema-27 reuse and is not cited as one here.

**Remaining limits, with triggers.**

(i) `facts.provenance` stays symbol-carrying and the `bind_pattern` `shadow` suppression is
retained exactly as built — but its established ground is narrower than "two live bindings
answer to one `Symbol`, so the backend cannot name the root", and this section does not claim
the stronger one. Read at source 2026-09-07:

- **Every production consumer tests PRESENCE, not identity.**
  `crates/cranelisp-backend/src/compiler/apply.rs::is_direct_vecget_projection` matches
  `MonoExpr::Apply { provenance: Some(_), … }` to elide one borrowed-arg inc on a direct
  `vec-get` read, and
  `crates/cranelisp-backend/src/compiler/control_flow/sparkability.rs::accumulate_density`
  matches the same shape as a spark-**density heuristic**. No production site binds the
  symbol. `crates/cranelisp-backend/src/compiler/fn_compiler.rs::operand_live_binding_root`
  is a different, structural classifier over the scope stack, explicitly
  analysis-independent — it is not this fact.
- **`MonoMatchArm.provenance` has no reader at all.** It is written by
  `crates/cranelisp-typecheck/src/ownership/sites.rs::annotate` and consumed nowhere, so the
  arm fact the `shadow` flag gates currently reaches no decision.
- **What the suppression therefore buys.** On the presence axis it is conservative at the
  eliding consumer (absent ⇒ inc emitted verbatim) and inert at the heuristic (absent ⇒ one
  extra density point). The `Symbol`-ambiguity it is named for is not observed by any
  consumer today. It is retained because it is the boundary-safe direction for a consumer
  that binds the symbol and costs one name comparison over the arm's bound names — **not**
  because a present-day reader would be misled by the fact, and not as a claim that the
  emitted symbol resolves correctly at its span (§20.3: `root` is the formal parameter's
  name, whatever the span's live bindings are).
- **Falsifier.** A production backend site that binds the provenance `Symbol` rather than
  testing `Some(_)`, or any reader of `MonoMatchArm.provenance`. Either makes the arm fact
  load-bearing and re-opens this paragraph — including the §20.4 binder-identity
  alternative, which is what such a consumer would want.

§13.6(d)'s `drop_shadowed_provenance` remains the mitigation for a fact left rooted at a
rebound name, single-sourced across the `Let`, `ParBind` and `Match` pattern-binding seams
(`transfer.rs:579`, `:781`, `:1243`).

(ii) **Retired rather than carried.** This section previously kept
`classify_capture_escape`'s name-based recursion behind a `param: None` guard and graded the
residual "imprecision, not narrowing". That grading was **not established, and was the unsafe
direction**: the recursion decides which binding reaches `self.escaped`, and under a shadow it
can escape the wrong local, leaving the right one's allocation at `escapes = Some(false)` ⇒
stack allocation ⇒ the FIXME-0524 dangle. §20.3 removes the case by making the carried
parameter index total, so the recursion is deleted and there is no residual here to grade. The
enumeration that licenses the totality, its grade and its falsifier are stated in §20.3.

(iii) The escaped worklist stays `Symbol`-keyed. `drain_escaped` partitions it against the
defining `Let`'s own binding list, so an entry is claimed by the innermost live binding of
that name — the one in scope when it was pushed — and this repair does not move that. Read at
source this pass, not measured; trigger — an escaped entry drained by a scope that did not
bind it, observable as a lost or duplicated allocation-site escape fact under a shadow.

(iv) The §19.2 `MayAliasAny` weakening is unchanged.

### 20.6 Evidence implications and handoffs (allocation is `qa`'s)

**As built, 2026-09-07.** The module tier carries the class; the independent tier carries the
runtime face. None of it is accepted evidence until the wave's review and census pass.

- **Module tier, `transfer/tests.rs`** — four subject/control pairs, each pair one identifier
  apart, every subject authored RED-first with its polarity measured against the tree
  immediately before the change-set that flips it:
  `shadowing_binder_must_not_narrow_the_returned_parameter` /
  `renamed_binder_keeps_the_returned_parameter_owned` and
  `shadowing_binder_must_not_permute_the_obligation` /
  `renamed_binder_charges_the_obligation_to_the_returned_parameter` (the ABI half this
  section previously recorded as **owed** — it is now carried, and C″'s permutation with it);
  `captured_projection_widens_its_parameter_under_a_shadowed_root` /
  `captured_projection_widens_its_parameter` (the deleted recursion — the control's staying
  green pins that deletion did not remove the reach the recursion used to find);
  `shadowing_pattern_binder_must_not_erase_the_scrutinee_reach` /
  `renamed_pattern_binder_projects_the_scrutinee_parameter` (the `bind_pattern` arm, on the
  result axis — the subject asserts the §20.5(i) provenance suppression inside the same cell,
  so a future "repair" that re-emits the symbol-keyed fact reddens there).
- `self_shadowed_reach_set_result_is_top` flipped GREEN and left the expected-RED set;
  `renamed_binder_reach_set_result_is_top` stays as its control.
- `self_shadowed_widening_is_covered_by_the_drain` stays green **for a different reason** —
  the chase now covers it directly — and the comment asserting the drain masking was corrected
  where it sits. Whether a separate §13.6(g) drain falsifier is still wanted is `qa`'s.
- `match_bound_conditional_widens_every_reaching_param`,
  `escaping_capture_widens_every_reaching_param`, the provenance cells and the
  `join_lattice_*` property cells are maintained, not weakened: every property is restated
  over index sets, and `lattice_norm` no longer normalises a representative away because
  there is none.
- **The ABI half is module-tier only.** `param_modes`/`param_flow` are not observable
  end-to-end, so those four cells are the whole of that evidence.
- **Independent tier** (`tests/shadowed_param_reach_stale_rc_dec.rs`, unmodified): three of
  the four established REDs flipped GREEN with no assertion weakened or re-baselined — C's
  `STALE RC DEC` abort, the `--run`/`--link` safety matrix, and C′'s RC balance against
  ownership-OFF. The fourth is below.
- **The oracle claim, held at its measured scope.** §20.1's "RC parity against a rename
  control is the oracle" is **over-general as a claim about the class**, and is not restated
  as one. Parity detects C′. It does **not** detect C″, whose subject and control were
  measured counter-identical under ownership ON — only the ON/OFF differential fires there.
  And on the `bind_pattern` shape the correction has **no measured runtime face at all**:
  subject and control counters were identical pre-fix and post-fix, on one program, which is
  an observation about that shape and not a grade on the class. Parity, the ON/OFF
  differential and the module summary each cover part of this class; none covers it.
  **The consequence is `qa`'s**: C″ has no allocated cell, none is created here, and the
  class's final evidence adequacy is `qa`'s judgment, not this section's.
- **The surviving independent RED is not §20's face, and is not an approved carry.**
  `binder_rename_must_not_change_rc_counters` has its memory-safety face closed
  (allocs/deallocs `3/2` on both legs, marginal residual 0, no `STALE RC DEC`, `--run`,
  `--link` and ownership-OFF agreeing) and publishes a byte-identical summary across the
  pair — yet one balanced inc/dec pair and one **missing** `Crossing` materialisation site at
  the function's return value (`crossing_cells` 2 vs 1, the F-2 direction) persist with the
  ownership carrier out of the pipeline under `CRANELISP_NO_OWNERSHIP=1`, and reproduce
  identically on the `bind_pattern` shape. `qa` re-attributed it to `dev`(backend); a
  symbol-keyed backend binding identity is a hypothesis and nobody has observed that seam,
  with `qa`'s refuter being a shadow of a **non-parameter** local losing the same cell.
  It is **unresolved**, not an accepted residual, and it is neither this section's to close
  nor its to carry.
- Faces A, B, C, C′ and C″ and their attribution remain `qa`'s. The ABI face is **not** the
  result-axis class §19.10 filed.
- The `param_roots` rustdoc that carried §19.3's falsified "RESULT axis only … the drain
  covers it" went with the function, as this section required.

### 20.7 What remains

The direction and the schema epoch are approved and built (2026-09-07); the choice §19.10
left open — repair, take the §20.4 refusal containment, or carry the residual — is closed in
favour of the repair, and the repair is in the tree. Nothing below is a design question.

- **Acceptance, which is not design.** Independent review of both change-sets in agents that
  did not author them, the full-workspace census, and the generated `public-api.txt` diff
  returning to the user as the wave's standing gate (expected delta zero — the two cache
  constants are recorded without their values and every changed typecheck item is private to
  `transfer.rs`). CLIF goldens stay in the existing recapture hold; none was recaptured. The
  one golden RED observed while running the ownership bands,
  `ownership_fences::clif_golden_single_module_smoke`, is a toggle-OFF declaration-layer
  difference already present in the S121 intake census taken before this wave.
- **`qa`** owns what §20.6 leaves open: C″'s allocation, the drain-falsifier question, and
  the class's final evidence adequacy.
- **`dev`(backend)** owns the ownership-independent rename-parity residual named in §20.6,
  which is outside this design and unresolved.
