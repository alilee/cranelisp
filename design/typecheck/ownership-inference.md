# Ownership inference — the typecheck-crate proposal (parts 6–11)

**Status:** DESIGN (S100 Phase 3, stage 2) — the per-crate inference proposal for the
interprocedural ownership-inference analysis. Authored by `/design` narrow-deployed on
`cranelisp-typecheck`, against the S100 sprint scope (`sprints/SPRINT.md` parts 6–11).
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

## Next skills

- `/design` (cranelisp-backend) — author `design/backend/ownership-codegen.md` (parts 12–16)
  against the spine, consuming §8.4/§12 items 1–4 of this doc as its typecheck-side inputs.
- `/arch` — evaluate FIXME 0467 (summary-shape extension) alongside the §3.3 carrier design;
  no action needed before the implementing sprint.
- `/qa` — author the verification plan (parts 17–18) inheriting spine §9 + §12 items 5–8 here.
- `/sprint` — sequence at close per spine §5.7: R3 machinery → increment I → increment II.
