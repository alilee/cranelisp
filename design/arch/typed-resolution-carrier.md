# Typed resolution carrier — `VarRef` / `ApplyRef` (0653 prong 3)

**WORKING (S114 Phase 3, `/arch`) — the binding cross-crate design for the
Track-A carrier change-set.** Scribes the user's prong-3 directive (two
statements, 2026-07-19, quoted in FIXME 0653) into a concrete carrier shape and
pins the coordinated flip diff. The corollary itself is canonical at
`principles/24-resolve-once.md` §Corollary; this doc is the migration contract.

**Archive trigger**: the Phase-5 carrier wave lands (types flip + typecheck
producer + backend consumer + `CACHE_SCHEMA_VERSION` 21→22) and the contract
folds into `mono_expr.rs`/`check.rs` rustdoc + `interfaces.md` §"Method
Resolutions" + BC §2 producer obligation / §3 invariant 10.

## 1. Problem — the `Option<FQSymbol>` conflation

`MonoExpr::Var.resolved_target: Option<FQSymbol>` conflates two states under
one `None`: **local by design** (param / `let` name / match var — legal) and
**unresolved by producer bug** (the S113 check-gate-leak class, ×3 in one
sprint: D2's original leak, 0655 face 3 / MC-X3, F-D2-10). The backend
disambiguates by convention (`variables` consult, hard-error on double miss
since S113 W2b) — a dropped carrier surfaces as a codegen-time `undefined
function`, the **wrong phase**. `FQSymbol`/`FQTypeName` themselves audited
clean (no sentinel-module convention); the guilty encoding is the `Option`.

User directive (verbatim in substance): *"the backend is supposed to have all
names resolved to FQ canonical — otherwise unrepresentable"*; refined: *the
dichotomy must be enforced IN THE TYPE, not by a checking sweep*.

## 2. The two closed sums (landed dormant, S114 Phase 3)

Landed in `crates/cranelisp-types/src/mono_expr.rs` (produces-but-unused — the
established mono_expr precedent; re-exported at the crate root; additive
`public-api.txt` regen rides the 0685-resolution change-set — the dormant-enum
change-set omitted it, a two-update-discipline lapse healed there):

```rust
pub enum VarRef {
    Local { binder: Symbol, binding_span: Span },
    Global(FQSymbol),
}

pub enum ApplyRef {
    Dispatch(FQSymbol),
    ViaCallee,
}
```

Design decisions (resolving the three forks named in the S114 Phase-2
public-API assessment, SPRINT.md §Architecture review):

- **(a) `Local` carries BINDER IDENTITY, not a slot.** Frame/slot mapping
  stays backend-side (the backend's scope stack is the slot authority; a
  types-crate slot index would smuggle backend storage layout across the
  boundary). Identity = the bound name + the span of the binding **form** that
  introduced it (`let`/`fn`/`defn`/match-arm node — per-binder spans do not
  exist on the AST for params, so the form span is the honest grain). The
  span disambiguates §4.6 shadow frames for diagnostics and any future
  slot-keying; the producer fills it from the scope frame's provenance
  (`/design`(typecheck) plumbs frame → binding-form span).
- **(b) The Apply side is a SEPARATE sum.** An `Apply` has a third legal state
  a `Var` does not — "the identity rides the callee expression"
  (`ApplyRef::ViaCallee`: the callee `Var`'s own `VarRef` governs, or the
  callee is a computed closure value). Sharing one shape with `VarRef` would
  re-smuggle an ambiguous `None`/default. `ViaCallee` is a POSITIVE verdict —
  typecheck asserts it looked and there is no dispatch selection at this node.
- **Closed sums — deliberately NOT `#[non_exhaustive]`** (the ownership-mode
  vocabulary exception class, types `CLAUDE.md`): a variant addition must
  break every consumer match at compile time; "unresolved" has NO constructor
  in either sum.
- **Value source unchanged**: `Global`/`Dispatch` carry `Resolved.storage_fq()`
  — the walk-surfaced terminal storage key, never a written spelling (the
  0620 rule, `backend-keyed-consumer.md` §1.1.2).

## 3. Producer contract (the constructor IS the gate)

1. **The sidecar splits typed and TOTAL.** `MethodResolutions.resolved_targets:
   HashMap<Span, FQSymbol>` splits into `var_refs: HashMap<Span, VarRef>`
   (keyed by `Var` span) + `apply_refs: HashMap<Span, ApplyRef>` (keyed by
   `Apply` span). Typecheck's Var-resolution and Apply-dispatch chokepoints
   record a verdict for **every** node they check — locals get
   `VarRef::Local`, dispatch-less applies get `ApplyRef::ViaCallee`. The split
   also retires the latent Var-span/Apply-span collision hazard of the shared
   map (two key populations, one keyspace).
2. **View-build is the phase-boundary gate.** `MonoExpr::from_expr` reads the
   maps non-optionally: a missing entry for a real-span `Var`/`Apply` is a
   **located typecheck-phase error** (the gate the user directed — not a
   sweep, not a codegen miss). The error widens `from_expr`'s failure type
   (see §4 pinned diff). The former "pass empty maps for all-local bodies"
   license is RETIRED — all-local bodies now need `Local` entries, which the
   totality rule provides for free.
3. **Check-run pairing carries over unchanged** (§1.1.3 of
   `backend-keyed-consumer.md`): a view is built from the SAME
   `MethodResolutions` instance its body-check populated.
4. **Synthetic bodies** (`Span::SYNTHETIC` on every node) stay structurally
   outside span-keyed transport: synthesis holds the `VarRef`/`ApplyRef`
   identity in hand, never routed through the maps. **Sanctioned realization
   (0685 ruling, S114 Phase 3): the named all-local entry point
   `MonoExpr::synthetic_local_from_expr(expr, pattern_ctors)`** — landed
   dormant beside the sums — for the two adt.rs synthetic all-local
   populations (ctor `Expr::ConstrADT` body; accessor
   `(match self [(Ctor .. field ..) field])` body — the §4.5 typecheck
   census). Two structural tightenings make the positive all-local
   classification airtight rather than a convention: (i) the signature takes
   **no resolution-map parameters** — the all-local license IS the signature
   (retiring the "pass empty maps" convention; `pattern_ctors` is still
   taken, because a match-arm ctor identity is not a local — synthesis holds
   it and transports it under the synthetic pattern span); (ii) an
   **always-on tier-3 assert** that every node span is `Span::SYNTHETIC` — a
   real (check-run) body cannot borrow the all-local door to silently
   localize a table reference, so the license is machine-bounded, not
   call-site discipline. Direct hand-construction of the ctor/`Match` nodes
   (0685 option (a)) was REJECTED: it would mirror the node-construction
   walk `lenient_from_expr` already owns (the P7 duplication class — every
   future `MonoExpr` field addition needs a second edit site) while buying
   no additional structure; the span assert gives the named entry point a
   strictly stronger boundary than hand-construction discipline would.
5. **Lenient builder**: `lenient_from_expr`'s tolerance is for TYPES only —
   resolution verdicts come from the same paired check-run and are equally
   total. A resolution miss in a lenient walk is a tier-3 **always-on seam
   assertion** (in-process producer-bug breach, `safety-invariants.md` §2) —
   it must NOT silently manufacture `Local` for a table reference.
   `/design`(typecheck) validates this against the real lenient population
   (generic templates, REPL `__expr`, non-concretized macro-clause bodies); if
   a legitimate-miss population exists, it comes back to `/arch` as a FIXME
   naming the population, not as a silent default. **Census CLOSED (FIXME
   0685, resolved S114 Phase 3; `design/typecheck/typed-resolution-carrier.md`
   §4.5):** the only legitimate-miss population was the two adt.rs synthetic
   all-local bodies, now sanctioned via `synthetic_local_from_expr` (§3.4).
   With those rerouted, the lenient population is solely the
   `build_concrete_codegen_view` `NotConcrete` fallback over real check-run
   bodies — where resolution IS total — so this seam assert has NO
   legitimate-miss carve-out and fires unconditionally on a real-span miss.

## 4. The pinned Phase-5 flip diff (ONE coordinated wave — types + typecheck + backend + bump)

Types (`/arch`-approved; `/dev` lands within the wave):

- `MonoExpr::Var`: `resolved_target: Option<FQSymbol>` → `resolution: VarRef`
  (non-optional, no `#[serde(default)]` — absence is unrepresentable).
- `MonoExpr::Apply`: `resolved_target: Option<FQSymbol>` → `dispatch:
  ApplyRef` (non-optional).
- `MethodResolutions`: `resolved_targets` → `var_refs` + `apply_refs` (§3.1).
- `MonoExpr::from_expr` / `lenient_from_expr`: parameters become the two typed
  maps; `from_expr`'s error type widens from `NotConcrete` to a view-build
  error sum, e.g. `ViewBuildError { NotConcrete(NotConcrete), Unresolved {
  span: Span, name: Symbol } }` — the `Unresolved` arm IS the located
  typecheck-exit error. (`lenient_from_expr` stays infallible; its resolution
  miss is the §3.5 seam assert.)
- `MonoExpr::synthetic_local_from_expr` (dormant since Phase 3, §3.4): its
  interior flips from the empty-sidecar `lenient_from_expr` delegation to the
  **all-local MODE of the ONE shared lenient walk** — every `Var` →
  `VarRef::Local { binder: name, binding_span: Span::SYNTHETIC }`, every
  `Apply` → `ApplyRef::ViaCallee` — never a second hand-built
  node-construction walk. The signature does not change at the flip (that is
  the point of landing it dormant).
- `public-api.txt` regen + `interfaces.md` §"Method Resolutions" update ride
  the same change-set (two-update discipline).

Typecheck (producer; the wave's heaviest half — `/design`(typecheck) plans):

- Var/Apply chokepoints record total typed verdicts (§3.1), binder-identity
  provenance plumbed from scope frames.
- adt.rs's two synthetic-body callsites (`:210` ctor, `:612` accessor) swap
  `lenient_from_expr(body, pc, &empty)` → `synthetic_local_from_expr(body,
  pc)` (0685 ruling, §3.4). The swap is behaviour-identical pre-flip (the
  dormant interior delegates) and MAY land ahead of the wave; after it,
  `lenient_from_expr` has no all-local caller and its §3.5 seam assert is
  unconditional.
- **F-D2-10 gate-leak fixes RIDE this change-set** (F1: draining them
  pre-carrier authors exactly the interim gate patches the constructor
  obsoletes). MC-X4/X4b, MC-X5, PS-SH1, I-1 are orthogonal inference/harvest
  defects — drain before/interleaved, not behind the carrier (F2).
- The **B-2 match-var-pattern escape-recording fix is typecheck work** (F4)
  and shares the schema window (below).

Backend (consumer):

- `compiler/apply.rs` (12 refs incl. the S25 TCO keyed read,
  `backend-keyed-consumer.md` §3), `literals.rs`, `fn_as_value.rs`,
  `match_codegen.rs`: exhaustive matches on `VarRef`/`ApplyRef` replace the
  `Option` + `variables`-consult convention. `VarRef::Local` → scope-stack
  read (a miss is now a hard invariant failure with the binder identity in the
  message); `Global`/`Dispatch` → the existing `entry_at` keyed fetch.
  `is_self_call` keys on `VarRef::Global` == current fn's storage FQ.

Schema: **`CACHE_SCHEMA_VERSION` 21→22, ONE window** (F7) — the carrier
reshape (serde-visible on persisted `codegen_view`) and the B-2 escape-fact
correction (stale cached `Some(false)` would reproduce the UAF post-fix)
coordinate into one bump, not two invalidation events (the S111 0621
precedent). The bump lands in the flip change-set, NOT before it.

Blast radius (measured, Phase 2): `resolved_target` ×368 across 59 files but
structurally narrow — producer cranelisp-typecheck, consumer
cranelisp-backend, **zero refs in `src/`** (boundary confirmed right).

## 5. Sequencing (binding on Phase 4 — mirrors SPRINT.md §Required sequencing)

1. Carrier change-set = ONE coordinated multi-crate wave (serial handoffs,
   never split across a wave gate).
2. Carrier → F-D2-10 (rides) → **P26 full typecheck sweep + 0653
   helper-classification sweep AFTER** (the reshape changes the inventory they
   classify; the helper sweep IS the carrier's acceptance check — sweeps as
   migration aids, per the corollary).
3. Both bump-worthy changes (carrier + B-2) in the one schema window.

## 6. Residual audit items (assessment (c) — helper-sweep scope, not carrier scope)

- `mono_expr.rs` `node_ty`'s `NotConcrete::Var(0)` "no concrete type at this
  position" sentinel — a convention-in-value candidate; classify in the
  helper sweep.
- The `{home}/{bare}$sig` string-embedded mangle identities — already fenced
  in the 0632 register; R4 census (`safety-invariants.md`) is the mechanism
  home.
- The bare-name+state helper classification (0653 prong 1): two explicit camps
  — legitimate pre-resolution seams vs re-resolvers to delete
  (`has_impl_with_state` the dead-code template; `resolve_trait`,
  `resolve_type` to classify; diagnostics-only renderers pass).

## 7. Handoff

- **`/design`(typecheck)** reads §3 + §4 (producer contract; chokepoint
  totality; binder-identity provenance; lenient-population validation;
  F-D2-10 riding; B-2 in-window) and elaborates the pass-level plan in
  `design/typecheck/`.
- **`/design`(backend)** reads §4 (consumer flip; exhaustive-match discipline;
  S25/`is_self_call` keying) — sequenced behind the 0669 `/qa` disposition per
  SPRINT.md; the 0668 consume contract must NOT absorb B-2 (it is typecheck
  work, F4).
- **`/qa`**: the wave's acceptance = the helper-classification sweep (§5.2) +
  the F-D2-10 pins flipping green + schema-window verification.
