# Backend as a pure keyed-lookup consumer — the 0583 resolution-boundary migration

**Status: WORKING (S110 Phase 3, `/arch`).** The binding cross-crate design for
FIXME 0583 (S110 centrepiece, user directive S109 P5): typecheck emits
fully-qualified SYMBOLS and fully-qualified TYPES on every mono-view reference;
the backend performs ZERO name resolution and ZERO bare-type-name resolution —
one keyed fetch, kind-discrimination on the fetched entry, hard `CodegenError`
on miss. Deletes `resolve_driven` + the arbitrary-order `symbol_tables.iter()`
global scan + the ten `resolve_*` entry points in
`crates/cranelisp-backend/src/compiler/resolution.rs`. Realizes **Principle 24
"Resolve once"** (`principles/24-resolve-once.md`, authored this phase,
ratification at Phase-7 close) at the typecheck→backend seam; the S109 §10
pattern-position cure (`dotted-ctor-canonical-keys.md` §10) is the worked
per-kind template this doc generalises.

Evidence base: Phase-2 architecture review (`sprints/SPRINT.md` §"Architecture
review (Phase 2)") — `resolution.rs` read in full, all backend resolver call
sites enumerated (§3 below is the authoritative re-verified inventory), full
type-axis survey (finding T: the type axis is already FQ-keyed except ctor
construction/reference position, which folds into the symbol-axis waves).

**Archive trigger:** W3 lands (resolver seam deleted; grep gate green). The
carrier contract folds into `mono_expr.rs`/`check.rs` rustdoc + BC §2/§3 +
`interfaces.md`; this doc moves to `design/arch/archive/`.

---

## 1. The one-carrier contract

**One carrier serves every reference kind.** Three pieces, all landing in W0:

1. **Sidecar** — `MethodResolutions.resolved_targets: HashMap<Span, FQSymbol>`
   (`crates/cranelisp-types/src/check.rs`; mirror of `pattern_ctors`, S109
   §10.2). Span-keyed by the *referencing node's span* (`Expr::Var.span` for
   value/callee references; `Expr::Apply.span` for dispatch-leg resolutions
   that resolve at the Apply). `#[serde(default)]`.
2. **Mono-view fields** — `MonoExpr::Var.resolved_target: Option<FQSymbol>` and
   `MonoExpr::Apply.resolved_target: Option<FQSymbol>`
   (`crates/cranelisp-types/src/mono_expr.rs`), both `#[serde(default)]`,
   populated by `MonoExpr::from_expr` from the sidecar at view-build time.
3. **The unforgettable parameter** — `MonoExpr::from_expr` gains a REQUIRED
   third parameter (the §10 template, Principle 18: a new view-build site
   cannot forget the carrier because the signature demands it):

   ```rust
   pub fn from_expr(
       expr: &Expr,
       pattern_ctors: &HashMap<Span, FQSymbol>,
       resolved_targets: &HashMap<Span, FQSymbol>,
   ) -> Result<MonoExpr, NotConcrete>
   ```

### 1.1 Semantics — "whichever storage key HIT"

Per §10.1: the recorded `FQSymbol` is **the storage identity under which the
referenced `Def` actually resolved** — module + the exact symbol-table key the
typecheck resolution terminated at. It is NOT the written name and NOT a
display name. Per kind:

| Reference kind | `resolved_target` | Backend read off the fetched entry |
|---|---|---|
| Concrete user fn | `m/f` (bare storage key) or `m/f$Int+Int` (mangled variant / mono instance — whichever entry the resolution/dispatch selected) | `callable_got_slot()` → GOT-indirect; `param_names.len()` for arity; `mode_summary()` |
| Primitive (slot-carried) | `primitives/add-i64` | `callable_got_slot()` → GOT-indirect |
| Primitive (inline, vec-query trio) | `primitives/vec-get` | `DefKind::Primitive { body: PrimitiveBody::Inline }` → inline emission (the kind IS the discriminator) |
| Sum ctor (construction/reference position) | `m/Type.Ctor` (canonical `member_key`; S109 keying) | `DefKind::Constructor { tag, field_count, .. }` |
| Product ctor | `m/Type` (the dual-facet single key) | same `Constructor` arm (`type_def: Some`) |
| Platform effect | `m/effname` (defining entry) | `DefKind::PlatformEffect { got_slot, poll_shape, scheduling_class }` — poll vs blocking vs stamp all off the ONE fetched entry |
| Host-promised extern | `primitives/discover-tests` | `DefKind::PrimitiveExtern` → `fq.symbol` IS the ABI key (`Linkage::Import`) |
| Trait-method / sig-dispatch leg | the module-bearing FQ of the SELECTED mangled impl entry (`m/Trait.method$Type`, `m/f$Int+Int`) | same concrete-fn arm |
| Local variable / lambda param | `None` (not table-resolved) | backend's local-`variables` check precedes the keyed read, unchanged |
| Slot-less `Polymorphic` template referenced as a value | the template's storage key | W2's 0585 hard error (§7) — a template entry at a value read is the LOUD backstop, never a silent leak |

`ResolvedCall` is left **untouched** — it stays supplementary dispatch metadata
(inline-builtin intercepts, auto-curry counts, trait resolution for the
as-value wrapper). Preferred over widening `ResolvedCall` because one carrier
gives one backend read for every kind; `ResolvedCall` has no module leg and
carries mangled *names*, not storage identities. (Phase-2 §2 pin.)

**Producer chokepoints (typecheck).** One writer helper (working name
`CheckState::record_resolved_target(span, fq)`), called from the seams where
the storage identity is in hand:

- `infer_var` — the S101 `record_user_fn_ref` chokepoint (F1: the FQ is already
  computed there for the `callees` feed), widened to record EVERY
  statically-resolved table reference kind (user fn, primitive, ctor, effect,
  extern), keyed at the Var span. Records the terminal STORAGE key (chain-follow
  already yields it).
- `instantiate_ctor` — construction-position ctors (the mirror of the S109
  pattern-sidecar mint, same storage-key discipline).
- The dispatch-selection seams (`monomorphise_call` / sig-dispatch /
  auto-curry resolution writeback) — the selected mangled entry's FQ, keyed at
  the Apply span.

`/design` (typecheck) may refine the exact seam list; the binding property is
**recording happens where resolution happens** (Principle 24) — never a second
post-hoc resolution pass.

### 1.2 The no-soft-fallback REJECT criterion (Rev-2 — binding on every wave)

**NO soft fallback, ever, not even "temporarily."** For any reference kind, a
codegen site either (a) reads the carrier and hard-fails on miss
(`CodegenError`, precise message naming the reference and the missing carrier —
the §10.3 precedent), or (b) still runs the UNTOUCHED legacy resolver path
because its wave has not arrived. A keyed-read-else-`resolve_driven` hybrid is
the half-resolver Principle 8 forbids: it would silently mask producer gaps and
reintroduce the arbitrary-order scan as a shadow path. `resolve_driven` never
gains a sometimes-keyed mode; it only loses callers. **`/review` REJECTS any
wave change-set containing a carrier-miss fallback to a name resolver.** Kinds
flip atomically: when a wave flips a kind, every site of that kind flips in
that wave.

### 1.3 The backend end-state reader

ONE keyed fetch — working name `CompileContext::entry_at(&FQSymbol) ->
Option<(ModuleFullPath, ModuleEntry)>` — the `ctor_meta_at` generalisation
(`context.rs:176`): direct two-level map read (`symbol_tables.get(&fq.module)`,
`table.get(fq.symbol)`), NO import-chain walk, NO alias substitution, NO global
fallback, NO DashMap iteration order. Kind-discrimination on the ONE fetched
entry's `DefKind` replaces all ten resolvers:

- got-slot dispatch via `callable_got_slot()`
- platform/poll arms via `DefKind::PlatformEffect` (+ `poll_shape`)
- extern via `DefKind::PrimitiveExtern`
- vec-query via `PrimitiveBody::Inline`
- arity via `param_names.len()`
- ownership summary via `mode_summary()`
- ctor tag/meta via `DefKind::Constructor` (the existing `ctor_meta_at`
  becomes a projection of `entry_at`)

Carrier-miss (a table-reference kind whose mono node carries `None`) or
entry-miss (`Some(fq)` that fetches nothing) = hard `CodegenError`
(Principle 18). One deliberate non-keyed remainder: **extern-by-name
int-hosted intrinsics** (the trace field accessors — `cranelisp_trace_name`
etc.), which are NOT symbol-table entries at all; they keep the by-name
`Linkage::Import` lowering (`compile_extern_call`). That is not a resolver (no
scan, no precedence walk — a fixed catalog), and it is the documented
`resolved_target: None` + known-extern-name arm of the BuiltinFn funnel.

### 1.4 Backend-synthesized names (not mono-node references) — explicit treatment

Phase-2 §3 obligation. Two sites synthesize a callee name in codegen rather
than reading one off a mono node:

- **`literals.rs::compile_operator_as_value`** (`operator_primitive_name` maps
  `+` → `add-i64`, …, then `resolve_got_target` at literals.rs:282). The
  target is a FIXED compile-time mapping into the `primitives` module. W2
  replaces the resolver call with a direct keyed read of
  `FQSymbol { module: "primitives", symbol: <mapped> }` + hard-miss. No
  carrier needed (the name is synthesized, the home is static), no resolver.
- **GOT data-symbol names** (`got_data_symbol_name`) and **inner-fn
  discriminators** (`inner_fn_discriminator_for`) are naming primitives, not
  resolution — they remain in `resolution.rs` as its only survivors (§6).

---

## 2. Finding T restated — the type axis is closed except ctor position (Rev-1)

Full backend type-identity survey (Phase 2): `heap.rs` classify/mixed-adt,
drop glue (`rc_emission.rs`/`vec_codegen.rs`), `schema.rs` layout-hash closure,
`trace_codegen.rs` descriptor baking, and `context.rs::lookup_type_def` /
`ctor_meta_at` / `constructor_metas` ALL key on an `FQTypeName` read off the
node's `Type::ADT`/`ConcreteType::ADT` through the single-sourced
`cranelisp-types` readers (`type_ctor_names`, `value_layout`, `member_key`).
**Zero bare type-name resolution exists on the type axis.** The only bare
resolver reachable from a type-ish position is `context.rs:146
lookup_constructor(name: &str)` — constructor **construction/reference**
position — which folds into the symbol-axis waves as one more kind (W1 ctor
Apply, W2 ctor-as-value/nullary; pattern position was cured S109 §10). The
sprint plan's separate "type axis audit + FQ-ize" bucket is RE-SCOPED to this
fold-in; the end-state (backend keys types on `FQTypeName` only) is already
true and W1–W3 make it true for ctor references too.

---

## 3. Per-site inventory — the authoritative checklist

Re-verified exhaustively this phase (grep over
`crates/cranelisp-backend/src/`, comments and unit tests excluded). Every
resolver-reaching site, its kind, and the wave that flips it. **This table is
each wave brief's checklist and `/qa`'s per-wave acceptance basis.** (The
Phase-2 review quoted "26 sites" counting the ten resolver entry points'
internal driver calls; the binding artifact is this SET — S1–S24. At W3 the
grep gate, not the count, is the criterion.)

Direct resolver invocations:

| # | Site | Resolver | Role | Wave |
|---|---|---|---|---|
| S1 | `compiler/apply.rs:566` | `resolve_got_target` | BuiltinFn arm: extern-primitive GOT-vs-direct-extern discrimination | W1 |
| S2 | `compiler/apply.rs:612` | `resolve_got_target` | BuiltinFn arm: platform GOT-flip transitional discrimination | W1 |
| S3 | `compiler/apply.rs:757` | `data_constructor_info` → `lookup_constructor` | ctor `Apply` recognition (tag/field_count) | W1 |
| S4 | `compiler/apply.rs:781` | `lookup_constructor` | ctor `Apply` value-flatten (R5) classification | W1 |
| S5 | `compiler/apply.rs:960` | `resolve_callee_summary` | moded arg-list borrow elision | W1 |
| S6 | `compiler/apply.rs:1118` | `resolve_poll_effect_target` | `compile_direct_call` poll-construction arm | W1 |
| S7 | `compiler/apply.rs:1135` | `resolve_got_target` | `compile_direct_call` unified GOT dispatch | W1 |
| S8 | `compiler/apply.rs:1172` | `resolve_platform_effect_target` | platform fn-name stamp arm | W1 |
| S9 | `compiler/apply.rs:1194` | `resolve_extern_target` | `PrimitiveExtern` ABI-key arm | W1 |
| S10 | `compiler/apply.rs:1681` (`resolve_got_entry`; sole caller `fn_as_value.rs:586`) | `resolve_got_target` | fn-as-value wrapper GOT entry | W2 |
| S11 | `compiler/literals.rs:155` → `:202` (`nullary_constructor_tag`) | `lookup_constructor` | nullary-ctor `Var` fold | W2 |
| S12 | `compiler/literals.rs:187` → `control_flow/fn_as_value.rs:117` (`is_known_function`) | `resolve_is_callable_target` | fn-as-value gate | W2 |
| S13 | `compiler/literals.rs:282` | `resolve_got_target` | operator-as-value (backend-synthesized name — §1.4 direct keyed read) | W2 |
| S14 | `control_flow/fn_as_value.rs:149` | `resolve_func_arity` | closure-wrapper arity | W2 |
| S15 | `control_flow/fn_as_value.rs:500` | `resolve_callee_summary` | wrapper return-protection summary | W2 |
| S16 | `control_flow/fn_as_value.rs:532` | `lookup_constructor` | ctor-as-value | W2 |
| S17 | `control_flow/fn_as_value.rs:575` | `resolve_vec_query_primitive` | vec-query wrapper discrimination | W2 |
| S18 | `control_flow/fn_as_value.rs:665` | `resolve_vec_query_primitive` | vec-query wrapper discrimination (curry leg) | W2 |
| S19 | `compiler/match_codegen.rs:263` | `lookup_constructor` | `resolved_ctor: None` synthetic-body fallback | dead after W0.b; DELETE W3 (§5) |
| S20 | `compiler/match_codegen.rs:600` | `lookup_constructor` | `resolve_field_types` ctor re-resolution | W3 residue: fold onto `ctor_meta_at(arm.resolved_ctor)` — the arm already carries the identity |
| S21 | `compiler/context.rs:159` (inside `lookup_constructor`) | `resolve_driven` | the ctor resolver body | deleted W3 with `lookup_constructor` |

Resolver seam itself (all deleted W3):

| # | Item |
|---|---|
| S22 | `resolution.rs::resolve_driven` + `resolve_chain` + the step-3 `symbol_tables.iter()` global scan |
| S23 | The ten entry points: `resolve_got_target`, `resolve_is_callable_target`, `resolve_vec_query_primitive`, `resolve_callee_summary`, `resolve_platform_effect_target`, `resolve_poll_effect_target`, `resolve_extern_target`, `resolve_func_arity` (+ `lookup_constructor`, `resolve_got_entry`) |
| S24 | View-builders outside `from_expr`: `lib.rs:673 lenient_mono_from_expr` (live arm `lib.rs:909`), `jit.rs:622 compile_defn` (unit-test-harness-only — no live caller; verified this phase) — §5 ruling |

**W3 grep gate (the structural invariant, greppable):** zero occurrences of
`resolve_driven|resolve_chain|resolve_got_target|resolve_is_callable_target|resolve_vec_query_primitive|resolve_callee_summary|resolve_platform_effect_target|resolve_poll_effect_target|resolve_extern_target|resolve_func_arity|lookup_constructor|lenient_mono_from_expr`
in `crates/cranelisp-backend/src/` outside git history. `resolution.rs`
retains exactly `got_data_symbol_name` + `inner_fn_discriminator_for`.

---

## 4. The wave plan

Each wave independently correct-and-shippable (Principle 8). Serial backend
chain W1 → W2 → W3 (SPRINT §8); W0 is the one coordinated cross-crate
deployment.

### W0 — producer (ONE coordinated `/dev` deployment; types diff pre-approved §8)

Two commits inside one schema window (`CACHE_SCHEMA_VERSION` 18→19 rides
commit 1; the 0472 v10→11 precedent covers commit 2 landing inside the same
window):

**W0.a — carriers + population.**
- `cranelisp-types`: the §1 contract (sidecar field, 2 mono fields, `from_expr`
  third param). Baseline regen + `interfaces.md` + BC §2/§3 already carry the
  narrative (this phase).
- `cranelisp-typecheck`: `record_resolved_target` writer at the §1.1
  chokepoints, for ALL statically-resolved reference kinds; all `from_expr`
  callers updated (`program/support.rs:235`, `traits/monomorphise.rs:491`).
- `cranelisp-backend`: `from_expr` callers in `test_support.rs:327/692`
  updated; the **unit-test harness populates the sidecar for its fixtures**
  (it constructs both tables and exprs, so it computes the storage FQs
  directly). Without this, W1's hard-miss flips the whole backend unit suite
  red — pinned here so `/dev` does not discover it mid-wave.
- `CACHE_SCHEMA_VERSION` 18→19 (`cache/mod.rs:316`): the mono fields ride the
  persisted `codegen_view`; a stale cache would deserialize `None` carriers
  and (post-W1) hard-fail — the bump invalidates wholesale.
- Shippability: behaviour-invariant — carriers ride unread; suite stays green.

**W0.b — view totalization (the §5 ruling's mechanism).** typecheck becomes
the SOLE mono-view producer for every codegen-reached body:
- typecheck builds a **lenient view** (same placeholder semantics as backend's
  `lenient_mono_from_expr`: non-concrete/absent node type → placeholder
  `ConcreteType`, read only via `signature_heap_category`) for the entry
  classes that legitimately fail strict `from_expr`: ctor `Def`s, synthesised
  accessors, `f$Var` multi-sig variants, generic templates reached by
  direct compile, `__expr` §3.11.2-disposition-3 bodies, non-concretized
  macro-clause bodies. The lenient builder lives beside `from_expr` in
  `cranelisp-types` (ONE home for view construction; both take the same two
  REQUIRED sidecar params — Principle 18).
- **Synthetic bodies get their carriers DIRECTLY, not via the span maps**:
  synthesised bodies use `Span::SYNTHETIC` uniformly, so a span-keyed sidecar
  structurally cannot address them (all keys collide). At synthesis time the
  identities are in hand — the accessor's single pattern arm gets
  `resolved_ctor` = the just-registered ctor's canonical storage key; ctor
  bodies are `ConstrADT` (already FQ + tag, no reference at all). This CLOSES
  S19's fallback need entirely — no scoped helper, no re-resolution.
- backend: the `lib.rs:905` match flips to read a present view for ALL kinds
  (the `requires_codegen_view` bypass retires); `lib.rs:909`'s lenient arm
  becomes a hard error ("codegen-reached entry without a view") — Principle 18.
- Shippability: behaviour-invariant (the typecheck-built lenient view walks
  the same enriched ast with the same placeholder rules; CLIF byte-identity is
  the wave's verification gate). Same schema window as W0.a.

### W1 — call seam (`apply.rs` dispatch funnel; highest traffic)

Flips S1–S9: callee dispatch reads `resolved_target` → `entry_at` keyed read;
kind arms off the fetched entry (§1.3); ctor-`Apply` included (Rev-1). Deletes
the apply-site reach of `resolve_got_target`, `resolve_platform_effect_target`,
`resolve_poll_effect_target`, `resolve_extern_target`, `resolve_callee_summary`,
and `lookup_constructor@apply.rs`. Extern-by-name intrinsics keep the §1.3
non-keyed arm. Value seam stays on the intact legacy path (Rev-2: whole kinds,
no hybrids). Verification: per-site carrier coverage shown against §3; `/qa`
hard-miss negative pins (the §10.9 loud-miss precedent); e2e green.

### W2 — value seam (`literals.rs`, `fn_as_value.rs`) + the 0585 guard

Flips S10–S18: fn-as-value gate, closure-wrapper arity, vec-query
discrimination, wrapper summary, nullary-ctor tag, ctor-as-value, operator-as-
value (§1.4). Deletes the remaining reach of `resolve_is_callable_target`,
`resolve_func_arity`, `resolve_vec_query_primitive`, `resolve_callee_summary`,
`lookup_constructor`, `resolve_got_entry`. **The 0585 structural guard lands
here** (§7). Same verification obligations as W1 + the `/qa` value-position ×
{mint, die} matrix.

### W3 — deletion + residue

- Fold S20 onto `ctor_meta_at(arm.resolved_ctor)` (the arm carries the
  identity; re-resolving the name was always redundant under the carrier).
- Delete S19's `None`-arm fallback (dead since W0.b — a `None` on ANY ctor arm
  is now keying drift, hard error; the §10.3 fold-in note is superseded).
- Delete `lenient_mono_from_expr` + the `lib.rs:909` arm (dead since W0.b) and
  the unit-test-only `jit.rs::compile_defn` lenient build (migrate the harness
  onto typecheck-built/`from_expr`-built views, or demote `compile_defn` to
  `#[cfg(test)]` with a view parameter — `/dev`'s choice; the live-path
  invariant is what binds).
- Delete S21–S23: `resolve_driven`, `resolve_chain`, the global scan, the ten
  entry points, `lookup_constructor`. `resolution.rs` shrinks to the two
  naming primitives.
- Run the §3 grep gate; update backend rustdoc (`lib.rs` `//!` resolver
  mentions at lines 37/84/106/556/961/1582 area) + `compiler/mod.rs` re-export
  hub + `cranelisp-backend/CLAUDE.md` seam map in the same change-set.
- End-state: the audit rotation (backend, post-W3 per Phase-2 §7) verifies the
  boundary lens structurally — zero `resolve_*` in backend.

**Fallback posture** (Phase-2 §3): the shipped state after ANY completed wave
is coherent — fewer kinds keyed, legacy intact for the rest. Carrying a wave
across the sprint boundary requires evidence per the no-defer-for-size rule,
never habit.

---

## 5. The W3 residual ruling — view-builders outside the `from_expr` path

**The question (Phase-2 §3, named risk):** bodies built OUTSIDE the
sidecar-threaded `from_expr` path — `lib.rs::lenient_mono_from_expr` (live arm
`lib.rs:909`) and the synthetic fallbacks at `match_codegen.rs:263` — have no
carriers; under Rev-2 they cannot keep a resolver and must not get a hybrid.

**Phase-3 findings that decide it:**

1. The lenient arm's live reach is NOT same-module/self-contained. It serves
   (per `lib.rs:892–910` + the `lenient_mono_from_expr` rustdoc): ctor/accessor
   synthetic bodies (self-contained), but ALSO generic templates, `__expr`
   disposition-3 bodies, and non-concretized macro-clause bodies — full
   reference-kind spectrum. A "prove same-module + scoped helper" ruling is
   therefore UNAVAILABLE for the lenient class: the proof is false.
2. Synthetic bodies use `Span::SYNTHETIC` on every node, so the span-keyed
   sidecar STRUCTURALLY cannot carry their resolutions (all keys collide) —
   "thread the span map through the builder" is unavailable for the synthetic
   class.
3. `compile_to_module` runs only downstream of a live typecheck (no re-codegen
   on cache-hit — cache invariant 5), so typecheck ALWAYS has the resolutions
   in hand when any view is built; and `jit.rs::compile_defn` has **no live
   caller** (unit-test harness only — verified by call-site grep this phase;
   its "REPL calls directly" rustdoc is stale and is corrected in W3).

**RULING — thread carriers by making typecheck the sole view producer (W0.b),
with synthetic bodies carried directly:**

- The **lenient view moves to typecheck** (built beside the strict view at the
  same writeback seams, sidecar in hand). Both view builders live in
  `cranelisp-types` with the REQUIRED two-map signature; backend builds NO
  views on the live path. This is the "thread carriers through them" arm of
  the Phase-2 either/or, executed at the architecturally-correct site: the
  view is a typecheck PRODUCT (Principle 24 — derived at one stage, crosses
  the boundary as resolved data), and the transport problem (threading
  per-check-run maps into `compile_to_module`) dissolves because the carrier
  rides the persisted view.
- The **synthetic class** (accessor/ctor bodies) is carried by DIRECT
  population at synthesis time (§4 W0.b) — the scoped-keyed-helper alternative
  is superseded by something strictly better: no helper, no lookup, the
  identity is written where it is minted.
- **Proof-and-pin obligations** (W0.b unit tests, typecheck-side):
  1. every synthesised accessor view's ctor arm carries `resolved_ctor`
     = the owner type's canonical ctor key (structural pin);
  2. every codegen-reached `defined_symbols()` entry carries a view after
     check (the totalization pin — the backend's view-absent hard error is the
     runtime twin);
  3. backend-side W3 pin: no live caller of `compile_defn` /
     `lenient_mono_from_expr` (compile-time: both delete or demote to
     `#[cfg(test)]`).

**Rejected alternative (recorded):** a scoped, non-driven keyed helper for the
lenient arm (current-module-only probe + one same-module alias hop). Rejected
because finding 1 breaks its precondition for the lenient class — it would
have had to grow qualified/import handling to cover `__expr`/macro-clause
bodies, i.e. become a resolver again through the back door (exactly the hole
Phase 2 flagged this subsection to prevent).

**Phase-2 impact-table refinement (recorded honestly):** W0.b touches the
backend's `lib.rs:905` view-selection match (backend-internal, no public
surface movement) and adds the lenient builder beside `from_expr` in
`cranelisp-types` (public, rides the same W0 baseline regen). The Phase-2 "W1–
W3 = backend-internal, zero baseline movement" claim is preserved; W0's types
diff grows by the lenient builder (§8).

---

## 6. R-2 — the ADT-entry builder (folds under the centrepiece)

**LANDED this phase (additive, no consumers):**
`cranelisp_types::{AdtCtorSpec, build_adt_entries}`
(`crates/cranelisp-types/src/adt_build.rs`; narrative `interfaces.md` §"ADT-
entry builder"; BC §7 paragraph; baseline regenerated, +16 additive lines;
4 unit tests). The single derivation of the ADT registration entry set —
product/sum split, ctor schemes + `ConstrADT` synth bodies, canonical
`member_key` + bare-alias edges, product facet + docstring fallback,
`TypeDefInfo` computed once.

**Phase-5 caller wiring (ONE coordinated `/dev` change-set, src-chain slot per
SPRINT §8):**
- `crates/cranelisp-typecheck/src/adt.rs::register_type_def_with_ctor_infos` —
  builds `AdtCtorSpec`s from `CtorBuild`s (allocating slots from staging as
  today), calls the builder, inserts pairs sequentially: `Def`/`TypeDef` pairs
  verbatim; each `Import` alias pair routed through the existing §8.6.5
  contest classification (`register_constructors`' probe/poison/leave arms —
  which KEEP their current semantics, operating on the returned alias instead
  of a locally-constructed one). Pre-seed, accessor synthesis, and
  `build_constructor_scheme`'s local uses fold away where duplicated.
- `src/bootstrap.rs::register_synth_adt` — builds specs from `SynthCtor`s
  (allocating slots from the session table), inserts all pairs verbatim.
- Acceptance: behaviour-invariant (entry shapes unchanged — no schema bump);
  the existing adt/bootstrap unit + e2e suites green; `/review` verifies the
  mirror is actually DELETED (both writers thin), per the 0585-leg-1 precedent.

---

## 7. 0585 — the value-position structural guard (lands in W2)

Ruled Phase-2 §5; recorded here as the wave-2 work item. Three legs:
1. **One enumeration** — mint and die share the `for_each_child_expr`
   value-position walk (landed S109 0571.2). `/review` verifies the
   per-position whitelist (`collect_parametric_fn_value_args`'s historical
   shape) is DELETED in the wave that touches it.
2. **The loud backstop IS W2's keyed read** — under the carrier, a
   value-position `Var` whose fetched entry is a slot-less `Polymorphic`
   template hard-fails with a precise `CodegenError` ("generic value reference
   '<name>' reached codegen without a mono instance"), release builds
   included — strictly stronger than a debug-assert, and it replaces the
   misleading `undefined variable` leak at `literals.rs:191`. A 4th value
   position cannot silently leak: it either flows through the shared walk
   (minted) or dies loudly at the keyed read.
3. `/qa`'s value-position × {mint, die} matrix (unchanged, proceeds in
   parallel).

Permanent manifestation: Principle 24 + the BC §2 producer-obligation note
(landed this phase). FIXME 0585 closes when W2 + the matrix land.

---

## 8. The pinned W0 producer diff (specified change-set — Phase-5 `/dev`, NOT landed in Phase 3)

W0 does NOT land this phase: the `from_expr` signature change + schema bump
force cross-crate atomicity with the typecheck producer (a types-only landing
would strand the same-change-set bump rule). The carrier fields alone would be
safe additively (`#[serde(default)]`, unread), but the bump must ride the
change-set that also lands the producer — so the whole of W0 is PINNED, not
landed. The approved diff:

**`crates/cranelisp-types/src/check.rs`** — `MethodResolutions` gains:
```rust
/// Per-reference-span resolved STORAGE identity (S110 0583; mirror of
/// `pattern_ctors`): the FQSymbol under which the referenced Def actually
/// resolved — "whichever storage key HIT" at the typecheck resolution
/// chokepoint. Keyed by Var span (value/callee refs) or Apply span
/// (dispatch-leg selections). design/arch/backend-keyed-consumer.md §1.
#[serde(default)]
pub resolved_targets: HashMap<Span, FQSymbol>,
```

**`crates/cranelisp-types/src/mono_expr.rs`** —
- `MonoExpr::Var` + `MonoExpr::Apply` each gain
  `#[serde(default)] resolved_target: Option<FQSymbol>` (rustdoc per §1.1
  semantics; the §10.2 `resolved_ctor` precedent).
- `from_expr` gains the required `resolved_targets: &HashMap<Span, FQSymbol>`
  param (§1); `Var`/`Apply` arms populate by span lookup.
- W0.b: the lenient builder relocates here beside `from_expr` (same two
  required sidecar params; placeholder semantics per `lib.rs:673`'s current
  rustdoc), so view construction has ONE home.

**`crates/cranelisp-typecheck`** — `record_resolved_target` writer at the §1.1
chokepoints; `from_expr`/lenient-view call sites updated; W0.b totalization at
the `codegen_view` writeback seams + direct `resolved_ctor` population for
synthesised bodies; proof-and-pin tests (§5).

**`crates/cranelisp-backend`** —
- `cache/mod.rs`: `CACHE_SCHEMA_VERSION` **18 → 19** (same change-set, W0.a).
- `test_support.rs` harness populates fixture sidecars (W0.a).
- `lib.rs:905` view-selection flip + view-absent hard error (W0.b).
- Baseline: `cranelisp-types/public-api.txt` regen (sidecar field + 2 mono
  fields + `from_expr` signature −1/+1 + the lenient builder); backend
  baseline: ZERO movement (all touched items `pub(crate)`).

Cache-impact summary: ONE bump (18→19) for the whole initiative — W0.a's field
additions and W0.b's population-extent change land inside the same schema
window (the S101 0472 precedent). W1–W3: no types/public-API/cache impact
(backend-internal flips + deletions).

---

## 9. Interfaces completeness for `/qa`

The per-wave acceptance surface is fully specified: §3 is the per-site
checklist (each wave's flip set), §1.2 the per-wave REJECT criterion, §1.1 the
per-kind carrier semantics (the hard-miss negatives: carrier-None on a
table-reference kind; Some(fq) fetching nothing; slot-less template at a value
read — each a distinct pinned `CodegenError` message family), §4 the per-wave
verification obligations (W0 behaviour-invariance/byte-identity; W1/W2
kind-flip positives + loud-miss negatives; W2 the 0585 value-position ×
{mint, die} matrix; W3 the grep gate + no-live-lenient pin), §6 the R-2
behaviour-invariance acceptance.
