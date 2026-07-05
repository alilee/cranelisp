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
- **The finalisation pass** (`program.rs::finalize_check_result_inner`) — the post-pass
  sequence the analysis joins: Pass-4 mono runs at `:1901`, callees are written to entries at
  `:1999` via `write_callees_to_module_entries` (Decision 21). The ownership fixpoint slots
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
    ProjectionOf(usize),  // borrowed view rooted in param i (accessors — §4.4)
    AliasOf(usize),       // param i returned as-is, ownership flows through
                          // (the `string-identity` / `vec-push-grow` shapes)
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
`write_callees_to_module_entries` does — staging-aware, cluster-atomic, no new mutation path
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
- **Termination:** finite lattice + monotone transfer ⇒ each callable re-visits at most
  O(Σ per-param heights) times; in practice ≤ 2–3 visits for recursive clusters, 1 otherwise.
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
  (`…-copy` semantics): `params [Owned/Consumed, …]`, `result Fresh` — the COW copy is a
  genuine materialization and is precisely the increment-II Q4 target, not a read-path fact.
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
  Decision 44, exactly the `write_callees_to_module_entries` write path); the
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
`infer_var`, call- **and** value-position user-fn references, span-keyed delta into
`call_graph_edges`; 0472 resolved: `harvest_callee_edges` at all body-check seam
families incl. impl-provided/default/HKT method bodies; schema v11):

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
  path indexes the raw vectors or interprets absence. An absent summary is ⊤
  (all-`Owned`, `Fresh`, all-`Retained`, all-`spark_ops`); an absent site fact is
  `None` = escapes/crossing/shared/no-provenance. Joins only widen; init is
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
  retain, i.e. a leak, never an elided one). **Lattice-sizing residual (existing
  lattice retained):** for a return that may alias MULTIPLE DISTINCT params (the
  `(if c v w)` shape), the existing 3-element `ResultMode` cannot name "may alias
  0 or 1"; the representative-lowest-index choice is sound for the live
  borrow-elision consumer (which needs only the BINARY `Fresh`-vs-not) and is
  strictly more sound than the pre-cure `Fresh`, but a future index-specific
  provenance consumer would need a distinct ⊤ element (`MayAliasParam`/
  `AliasOfAny`) — a `cranelisp-types` carrier change routed to `/arch` as
  FIXME 0521, not required by increment I. `§4.2-rule-5 materialization is still
  emitted on each non-`Fresh` path (the returned borrow escapes at that edge).
- **(d) Provenance is symbol-keyed, with a shadowing guard.** `MonoExpr` bindings
  are `Symbol`-named; the backend's `borrowed_vars`/last-use machinery is
  symbol-keyed already, so the provenance site fact carries the root binding's
  `Symbol`. Where a body rebinds a name that is (or roots) a live provenance root
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
  the sound action at a genuine cross-boundary `Symbol` collision — provenance
  leaves the walk as a bare `Symbol` the backend re-resolves against its own
  `borrowed_vars`, so the drop is the boundary-safe behaviour regardless of
  in-walk scope fidelity. The scope stack does not retire it.
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
- **(h) Cap-exhaustion resets to the conservative ⊤** (hardens §3.2's worklist
  termination; FIXME 0512 blocker 4). The visit cap is defensive (unreachable
  under monotone convergence), but a partially-converged summary set is
  monotone-**below** its true fixpoint ⇒ **too precise** ⇒ unsound to publish.
  **As-built:** on cap exhaustion the modes worklist resets the WHOLE universe to
  the conservative ⊤ (`fixpoint::top` — all-`Owned` / `Fresh` / `Retained` /
  spark-set) before publishing; the confinement worklist (see §5.3) resets every
  `spark_ops` to all-`true` (Crossing). The reset is universe-wide, not
  queued-only: a non-queued entry may have converged against a still-too-low
  queued callee, so ⊤-everywhere is the only sound recovery. **The SITE FACTS are
  reset too** (Wave 8c-R F3): `fixpoint::conservative_site_facts` re-populates each
  callable's `SiteFacts` with every escape-bearing node's span `escapes=true` and
  provenance dropped — an un(fully)visited callable otherwise has no / below-truth
  escape entries, which the backend would trust to elide a retain (UAF). Cap is a
  shared test seam (`compute_cluster_with_cap(.., cap=0)` forces the reset).
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
- **Cap-exhaustion resets to `false` everywhere** (extends §13.6(h)). A
  partially-converged greatest-fixpoint sits *above* its true fixpoint (too many
  `true`s) ⇒ unsound to publish. On cap exhaustion the uniqueness stratum publishes
  `result_unique = false` for the whole universe and drops every `unique_static`
  site fact to `None` — the write-path analog of the §13.6(h) modes ⊤-reset and
  site-fact reset. `fixpoint::conservative_site_facts` gains the `unique_static →
  None` leg. This makes "publish only on clean convergence" structural, not a hope.
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

### 14.4 FIXME 0521 trigger verdict — **NO. The ⊤ element stays DEFERRED.**

**The Phase-2 conditional (restated):** /design(typecheck) lands the `ResultMode`
⊤ element (`AliasOfAny`, monotone-widening) in the B1 carrier change-set + a
`CACHE_SCHEMA_VERSION` bump **iff** the static-uniqueness subset design introduces
a consumer that reads the `AliasOf` **index** (the multi-distinct-param may-alias
case); else 0521 stays deferred until the reader arrives.

**Verdict: NO index-reader is introduced. 0521 stays deferred; no ⊤ element, no
schema bump for it in B1.** The reasoning, definitively:

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
floor (reuse tokens + R5 + the static-uniqueness subset). Until that reader lands,
the 0520 lowest-index representative is sound for every live consumer. **0521 is
the durable record; it does not action in S103.** (Monotone-soundness of the
eventual add is preserved: `AliasOfAny` only ever widens a value *away from*
`Fresh`, so it lands additively whenever its reader arrives, with its own schema
bump in that change-set.)

### 14.5 The R5 `value_layout` predicate — coordination (not typecheck-authored)

R5 value-representation flattening (Block B3; spine §6.3) is the one genuinely-new
`cranelisp-types` carrier of the sprint, and it is **/arch-authored**
(`value_layout(ty) -> Option<ValueLayout>` + `VALUE_LAYOUT_MAX_WORDS = 1` in
`heap.rs`), single-sourced because it is **soundness-coupled**: typecheck's `Copy`
mode classifier (§2.2) and the backend's `HeapCategory::Value` arm both consume it,
and a `Copy`-moded param the backend did not flatten is a UAF (spine §6.3). This
crate's dependency on it:

- **When R5 lands, the §2.2 `Copy` classifier gains the representation clause.**
  Increment I's classifier is exactly `ConcreteType::{Int, Bool, Float}` (the
  representation clause fails for every heap type — §2.2). When `value_layout`
  lands, `Copy(T)` gains "…or an ADT/Vec all of whose field element types are
  transitively `Copy` **and** `value_layout(T).is_some()`" — the classifier
  *delegates* to the shared predicate, never recomputes it. This is a **value
  change to which `ConcreteType`s classify `Copy`**, deterministic (post-mono ⇒
  total), hence cache-key-safe.
- **Landing discipline (Principle 8):** the predicate lands **in the B3
  implementing change-set, never ahead of the R5 mechanism design** — the same
  not-speculatively discipline the S100 carriers followed. Until it lands the
  `Copy` point is scalars-only and no unsound configuration is reachable.
- **Schema-version coordination (flag to /arch).** The sprint plan names the R5
  bump as `CACHE_SCHEMA_VERSION 12→13`, but the **live schema is already 14**
  (S102 Waves 8c-R/11 folded the 0520/0523/0524 summary-meaning bumps to 14 —
  §13.6(c)(j)(k)). The R5 predicate's bump must therefore be from the
  then-current value (14→15, or whatever S103's earlier waves reach), **not** the
  stale 12→13 in the plan. **This crate does not author the bump** — it is named
  here so /arch reconciles the number when authoring the B3 carrier change-set.

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
