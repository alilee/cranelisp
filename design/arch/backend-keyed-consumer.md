# Backend as a pure keyed-lookup consumer — the 0583 resolution-boundary migration

**Status: LANDED (S110 Phase 5; centrepiece-close verified 2026-07-16, `/arch`).**
The binding cross-crate design for FIXME 0583 (S110 centrepiece, user directive
S109 P5), DELIVERED end-to-end: typecheck emits fully-qualified SYMBOLS and
fully-qualified TYPES on every mono-view reference; the backend performs ZERO
name resolution and ZERO bare-type-name resolution — one keyed fetch,
kind-discrimination on the fetched entry, hard `CodegenError` on miss. W0
producer (carriers + `from_expr`, `CACHE_SCHEMA_VERSION` 18→19, `41fab350`;
W0.1b `144828d1`) → W1 call seam (`86038e27`) → W2 value seam + 0585 backstop
(`369c226c`) → W3 deletion (`4c899dd9`+`be06f6cb`): `resolve_driven`,
`resolve_chain`, the arbitrary-order `symbol_tables.iter()` scan, the ten
`resolve_*` entry points, `lookup_constructor`, and `lenient_mono_from_expr`
are DELETED (−993 LOC). **§3 grep gate verified at the centrepiece close
(2026-07-16): zero resolver CODE in `crates/cranelisp-backend/src/`** (every
remaining textual mention is deletion-narrative comment/rustdoc);
`resolution.rs` retains exactly the two naming primitives
(`got_data_symbol_name`, `inner_fn_discriminator_for`). Producer precision
closed on all three sidecar axes (key values 0616; carrier values
§1.1/§1.1.2/0620; map instance §1.1.3/0622). Realizes **Principle 24 "Resolve
once"** (`principles/24-resolve-once.md`, authored S110 Phase 3, ratification
at Phase-7 close) at the typecheck→backend seam; the S109 §10 pattern-position
cure (`dotted-ctor-canonical-keys.md` §10) was the worked per-kind template
this doc generalised. FIXMEs 0583/0584/0585 closed at the Phase-5
centrepiece-close pass.

Evidence base: Phase-2 architecture review (`sprints/SPRINT.md` §"Architecture
review (Phase 2)") — `resolution.rs` read in full, all backend resolver call
sites enumerated (§3 below is the authoritative re-verified inventory), full
type-axis survey (finding T: the type axis is already FQ-keyed except ctor
construction/reference position, which folds into the symbol-axis waves).

**Archive trigger — MET for the contract (verified 2026-07-16):** W3 landed
(resolver seam deleted; grep gate green) and the carrier contract is folded
into all four permanent homes — `crates/cranelisp-types/src/{mono_expr,check}.rs`
rustdoc, BC §2 (the producer obligation) + §3 invariant 10 (the consumer
statement), and `interfaces.md` §"`resolved_targets` — the 0583 keyed-consumer
carrier" (0618, `0cb5fbf7`). The physical move to `design/arch/archive/` is
PARKED on the one §6 tail still sprint-tracked — the
`src/bootstrap.rs::register_synth_adt` R-2 caller wiring (S110 src-chain) — so
the active sprint's citations stay live; the next `/arch` archive triage
executes the move. Residuals tracked at their own homes: FIXME 0621 (`callees`
alias residual — S111 schema-bump window); stale present-tense resolver
mentions in backend comments (cosmetic `/dev` sweep, named in the S110 Phase-5
close report).

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
| Trait-method / sig-dispatch leg | the module-bearing FQ of the SELECTED mangled impl entry (`m/Trait.method$Type`, `m/f$Int+Int`) — storage module per §1.1.1: the impl-WRITER's module for trait legs (read off the `TraitImpl` shell), the CALLER's module for mono-minted SigDispatch | same concrete-fn arm |
| Local variable / lambda param | `None` (not table-resolved) | backend's local-`variables` check precedes the keyed read, unchanged |
| Slot-less `Polymorphic` template referenced as a value | the template's storage key | W2's 0585 hard error (§7) — a template entry at a value read is the LOUD backstop, never a silent leak |

`ResolvedCall` stays supplementary dispatch metadata (inline-builtin
intercepts, auto-curry counts, trait resolution for the as-value wrapper) —
the backend never reads it as the keyed-lookup carrier; `resolved_targets` is
the ONE carrier. (Phase-2 §2 pin.) **Amended by §1.1.1 (W0.1 ruling):** the
Phase-2 "left untouched" wording is narrowed — `ResolvedCall::TraitMethod`
gains an `impl_module` field so the resolution PRODUCT carries the storage
module the carrier writer needs (recording happens where resolution happens);
this does not make `ResolvedCall` a backend carrier — the backend still reads
only `resolved_target`.

**Producer chokepoints (typecheck).** One writer helper (working name
`CheckState::record_resolved_target(span, fq)`), called from the seams where
the storage identity is in hand:

- `infer_var` — the S101 `record_user_fn_ref` chokepoint (F1: the FQ is already
  computed there for the `callees` feed), widened to record EVERY
  statically-resolved table reference kind (user fn, primitive, ctor, effect,
  extern), keyed at the Var span. Records the terminal STORAGE key via
  `Resolved::storage_fq()` — **NOT `Resolved.fq`** (the W1.1/0620 correction,
  §1.1.2: `fq` composes the WRITTEN spelling, which is an alias for
  member-canonical-keyed symbols and renamed imports; the walk-surfaced
  `storage_key` is the terminal table key).
- `instantiate_ctor` — construction-position ctors reached through the typed
  ctor path + ALL pattern-position ctors (the S109 pattern-sidecar mint, same
  storage-key discipline: "whichever storage key HIT" is the probe key).
- The dispatch-selection seams (`monomorphise_call` / sig-dispatch /
  auto-curry resolution writeback) — the selected mangled entry's FQ, keyed at
  the Apply span.

`/design` (typecheck) may refine the exact seam list; the binding property is
**recording happens where resolution happens** (Principle 24) — never a second
post-hoc resolution pass.

**The carrier value-source rule (binding, W1.1/0620).** No `resolved_targets`
value is EVER composed from a written spelling. Every insert's `FQSymbol`
comes from exactly one of three sources:

1. **walk-resolved** — `Resolved::storage_fq()` (the terminal storage key the
   `cranelisp-types` resolution walk surfaced; the ONLY actor that knows it,
   since a `ModuleEntry` does not carry its own table key);
2. **mint-resolved** — the exact probe/registration key in hand at the seam
   (`instantiate_ctor`'s canonical-vs-bare probe hit, `dotted_member_identity`'s
   `member_key` probe, `register_mono_entry`'s mangled key, the fn-value
   rewrite's minted mangle, the W0.1b `TraitImpl.impl_module` + mangle);
3. **transport** — copying an existing carrier entry to a new span (the
   AutoCurry callee-span transport).

A new writer that builds `FQSymbol { module, symbol: <written name> }` is the
0620 defect class reintroduced — `/review` REJECTS it on sight.

### 1.1.1 Storage-module derivation for dispatch legs (S110 W0.1 `/arch` ruling)

**The question (W0.1 deviation, `sprints/SPRINT.md` §"/dev (W0.1)"):**
`dispatch_target_fq` derives the TraitMethod/SigDispatch carrier module as
`current_module` (the shipped `callees` model, whose rustdoc carries the
pending "Step 5: look up the impl's defining module" note). For a
cross-module dispatch the mangled entry may live elsewhere; the backend's W1
keyed read would entry-miss where today's global-order scan silently finds it.

**Ground truth — where each dispatch-selected entry actually lives (verified
against source, this ruling):**

- **Trait-impl method `Def`s** (`Trait.method$m/Type` — explicit, default, and
  HKT alike) are written by `finalize_impl_method_writeback`
  (`crates/cranelisp-typecheck/src/traits/impl_check.rs:652–677`) via
  `current_symbol_table_mut` with `state.current_module` deliberately RESTORED
  to the **impl-writer's module** (`impl_check.rs:514–518`) — the module whose
  source contains the `(impl …)` form. Only the `ModuleEntry::TraitImpl`
  **shell** goes to the trait's defining module (`impl_check.rs:153`,
  Decision 45 discovery). This placement is **forced, not accidental**: the
  method bodies compile in the writer module's codegen batch, and
  `compile_to_module` structurally requires every compiled defn's entry (and
  GOT slot) in the compiling module's OWN table — it hard-errors on absence
  (`crates/cranelisp-backend/src/lib.rs:939–947`) and writes the finalized
  code ptr into THAT module's GOT (`lib.rs:999–1006`). **Decision 0045's
  method-co-location clause ("the method `Defn` entries live in the same
  module that holds the `TraitImpl` entry") is therefore AMENDED**: the shell
  lives at the trait's home (the chain-follow discovery record); the method
  bodies live with the writer (the compilation record). Moving the bodies to
  the trait's home is structurally impossible under the definition-side
  invariant (and would push per-impl GOT-slot writes into shared tables —
  the 0604 write-race surface).
- **Mono instances** (every mono-minted SigDispatch: the pass-4 drive, mono
  self-recursion P5, inner-constrained, inner-parametric-hop) register in the
  **caller's module** (`register_mono_entry` →
  `current_symbol_table_mut`, after `recheck_body_for_mono` restores
  `current_module`). The mangled NAME embeds the defining home (0519) but the
  STORAGE is the caller's table. Every one of the four writers records
  `state.current_module` at the same moment the entry registers there —
  correct by construction.
- **Multi-sig overload variants** register in the defining module
  (`register_mangled_variants` during that module's own check). The pending
  gate (`state.overloads`) is run-local + same-module-rehydrated
  (`form.rs:211–235` reads only the current module's own `Overloaded` Defs,
  no chain-follow), so an overload `SigDispatch` is only ever recorded when
  caller module == defining module — recorded `current_module` == storage.
  (Cross-module multi-sig dispatch does not exist today — a latent,
  pre-existing language gap, NOT a 0583 producer gap and not a W1 blocker.)

**The derivation rules (binding on the producer):**

| Leg | Carrier FQ | Source at the seam |
|---|---|---|
| TraitMethod — call, deferred, value-position, and AutoCurry-inner | `{ impl_module, mangled_name }` | `impl_module` read off the `TraitImpl` shell at `try_resolve_trait_method` (the shell probe that proves impl existence), carried on `ResolvedCall::TraitMethod.impl_module` |
| SigDispatch — all mono-minted legs | `{ current_module, mangled }` | correct as shipped (storage is the caller's table) |
| SigDispatch — overload pending | `{ current_module, mangled }` | correct by reach (gate is same-module-only) |
| AutoCurry — plain fn target | the callee Var's already-recorded `resolved_targets` entry, transported by callee span through `pending_auto_curry`; `None` for a local-binding target | resolve-once + shadow-correct: `infer_var` already recorded the target's terminal storage FQ (or nothing, for locals); do NOT re-resolve the bare name at drain time |
| BuiltinFn | `builtin_storage_fq` (`def_resolved` chain-follow, `primitives` fallback) | correct as shipped |

**The `cranelisp-types` diff (PINNED for the W0.1b `/dev` change-set — not
landed by `/arch` alone because adding enum-variant fields breaks every
construction site, forcing cross-crate atomicity; the §8 W0 precedent):**

1. `ModuleEntry::TraitImpl` gains `impl_module: ModuleFullPath` — the module
   whose table holds this impl's mangled method `Def`s and their GOT slots
   (the impl-writer's module). Written at the shell construction
   (`impl_check.rs:149–161`) from `state.current_module` (the writer IS
   current there). Required field, NO `#[serde(default)]`: a defaulted `""`
   module is a representable-invalid state (Principle 20), and construction
   sites must be forced to supply it (Principle 18). Rustdoc states the
   amended D45 model (shell = discovery record at the trait's home;
   `impl_module` = where the bodies live).
2. `ResolvedCall::TraitMethod` gains `impl_module: ModuleFullPath` — the
   resolution product. Populated by `try_resolve_trait_method` from the shell
   that grounds the selected mangle (probe the trait home's table with the
   exact key `impl${fq_for_mangle}${fq_trait_name}` — a direct keyed get;
   bare-match fallback mirroring `has_impl_in_home` for the intrinsic-receiver
   case). Downstream consumers (`dispatch_target_fq`,
   `resolved_call_to_fqsymbol`) READ the field, never re-derive — this
   **resolves the callees.rs "Step 5" pending note** (the answer: the impl's
   module is the WRITER's, knowable only from the shell, carried on the
   resolution). Note the callees fix also repairs the S101 session-transaction
   reverse index for cross-module trait calls (its edges currently name the
   wrong module — a silent affected-set starvation).
3. Cascade in the same change-set: `into_concrete` arm (`module.rs:569`), the
   int display fixture (`src/repl.rs::impl_entry`), typecheck fixtures, types
   `public-api.txt` regen, `interfaces.md` narrative. **No new
   `CACHE_SCHEMA_VERSION` bump**: lands inside the schema-19 window (the 0472
   precedent); `BUILD_ID` staleness covers dev-cache skew across compiler
   rebuilds.

**Two further producer gaps the sweep surfaced (typecheck-only, same
change-set):**

- **AutoCurry plain leg** (`resolve_auto_curry`, mono_collect.rs:711–721):
  records `{current_module, target_name}` for a possibly-IMPORTED target whose
  `Def` lives in its home module. Fix per the table above (callee-span
  transport; widen the typecheck-private `pending_auto_curry` tuple with the
  callee span).
- **Fn-value mono rewrite** (mono_collect.rs:79–88): `rename_var_at_span`
  repoints the stored AST `Var` at the caller-local mangled mono but leaves
  `resolved_targets[arg_span]` at the slot-less template's FQ (or absent) —
  post-W2 the 0585 guard would hard-fail a VALID program. Fix: insert
  `{current_module, mangled_sym}` at `arg_span` alongside the rename (and the
  W0.b view-totalization must rebuild/patch the enclosing view from the
  renamed AST so the carrier reaches codegen).

**Completeness sweep — every kind W1/W2 will key-read, against the §1.1
producer inventory.** *(W0.1 module-axis sweep, retained for the findings it
grounded. Its ctor row MIS-ATTRIBUTED the recorder — a bare
construction/reference ctor or accessor Var is recorded by
`record_reference_target`, NOT `instantiate_ctor` — and the sweep verified
only the recorded MODULE, never the recorded SYMBOL against the terminal
storage key. Both defects of method are cured by the §1.1.2 recorder-grounded
re-sweep, which supersedes this table as the completeness statement.)*

| Reference kind (carrier leg) | Writer seam | Recorded module | Actual storage | Verdict |
|---|---|---|---|---|
| Concrete user fn / value ref (Var span) | `infer_var` → `resolve_ref_target` (`def_resolved` chain-follow) | terminal home | terminal home | correct |
| Self-recursive ref (Var span) | `record_reference_target` + `current_defn` | enclosing defn's module | same | correct |
| Primitive / operator (BuiltinFn, Apply span) | `builtin_storage_fq` | terminal home (`primitives` fallback) | `primitives` / `macros` | correct |
| Trait method — call / deferred / value-position / curry-inner | `dispatch_target_fq` TraitMethod arm | caller's module | **impl-writer's module** | **GAP — fix 1+2 above** |
| SigDispatch — overload pending | `resolve_pending_overloads` | current (= defining, by the run-local gate) | defining module | correct by reach |
| SigDispatch — pass-4 mono mint / dedup | `drive_call_site_monomorphisation` | caller | caller (`register_mono_entry`) | correct |
| SigDispatch — mono self-recursion / inner-constrained / inner-hop | monomorphise.rs 399/843/988 | caller (explicit) | caller | correct |
| AutoCurry — plain fn target | `resolve_auto_curry` | caller's module | target's home | **GAP — callee-span transport** |
| Fn-value mono rewrite (Var at arg position) | `rename_var_at_span` — no carrier update | stale template FQ / absent | caller (minted mono) | **GAP — sidecar update at rename** |
| Ctor construction/reference + dotted `Type.member` (Var span) | ~~`instantiate_ctor` / `dotted_member_identity`~~ **bare spellings: `record_reference_target`; dotted spelling only: `dotted_member_identity`** | storage key that HIT / `fqtn.module` | same (S109 canonical keying) | ~~correct~~ **MIS-ATTRIBUTED — the bare-spelling recorder emitted the ALIAS symbol (FIXME 0620); ruled + fixed §1.1.2** |
| Pattern ctors (sidecar) | S109 §10 | storage key that HIT | same | correct |
| Platform effect / extern (Var span; plain Apply keys off the callee Var) | Var leg | terminal home | platform / `primitives` module | correct |
| Synthetic bodies (accessors / ctor `ConstrADT`) | direct at synthesis (W0.b) | just-registered canonical key | same | correct by construction |

**Gating verdict.** W1 must NOT flip until the W0.1b top-up lands. The
trait-method gap is BROAD, not a corner case: every non-primitive impl of a
prelude-provided trait called from user code (`(show (Some 3))` — impl
written in the prelude, caller in `user`) records the caller's module while
the entry lives in the writer's; the FIXME-0185 primitive short-circuit
covers only the Int/Float/Bool/String operator table. The AutoCurry gap hits
every curry of an imported fn. Both would surface as hard `CodegenError`s on
valid programs at W1/W2 flip. **Fix shape: W0.1b, one coordinated `/dev`
change-set (types + typecheck + int fixture), in the W0-completion front
BEFORE W1** — not folded into W1 (cross-crate where W1 is backend-narrow, and
Rev-2 forbids discovering producer gaps via backend misses). One unit pin per
fixed leg (cross-module trait dispatch carrier; imported-target curry
carrier; fn-value rewrite carrier), mirroring the W0.1 pins.
*(W0.1b landed `144828d1`; the W1 flip subsequently re-blocked on the SYMBOL
axis — §1.1.2.)*

### 1.1.2 Terminal-storage-key derivation for alias-resolved references (S110 W1.1 `/arch` ruling — FIXME 0620)

**The defect (0620, third producer gap of the initiative).** For every
**member-canonical-keyed** symbol — every sum ctor and every field accessor
(S109 keying: the real `Def` lives under `member_key(Type, member)`; the bare
name is an `Import` alias) — the carrier recorded the bare-ALIAS FQ
(`{home, "Pure"}`, `{home, "v"}`), not the terminal storage key
(`{home, "IO.Pure"}`, `{home, "Box.v"}`). W1's `entry_at` (direct read, no
chain-follow — §1.3, by design) lands on the alias entry and hard-misses.
Root cause: `cranelisp_types::Resolved.fq` composes
`{home, canonical_symbol(WRITTEN_NAME)}` — the home is the chain-follow
terminus (right), the symbol is the written spelling (wrong for storage).
The recorder (`record_reference_target` → `def_resolved` → `scope_resolve`)
recorded `fq` verbatim.

**The class is broader than member keys.** The ruling sweep found the same
gap wherever a followed `Import`/`Reexport` edge RENAMES: **renamed imports
`[(foo bar)]` and renamed re-exports** (grammar §2 — symmetric rename forms),
including a qualified `m2/bar` landing on a renaming re-export. Written
spelling `bar`, storage key `foo` — identical hard-miss shape.

**Why neither filed candidate was adoptable as filed.**

- *Candidate 1 (repoint `Resolved.fq` at the terminal key)* — rejected.
  `fq` is the reference/display identity consumed by macro-head dispatch,
  error attribution, `callees`, the §8.6.4 remedy text, and the display
  surfaces under S20/S21 byte-identity pins. Repointing it makes `(v box)`'s
  `v` display as `Box.v` and a renamed `bar` display as `foo` — a
  user-visible regression riding a producer fix.
- *Candidate 2 as filed ("derive off `Resolved.entry`'s storage key")* — not
  implementable literally. A `ModuleEntry` does not carry its own table key:
  a field accessor is a plain `UserFn` `Def` with nothing identifying its
  `Type.field` key, and NOTHING on any terminal entry can recover a renamed
  import's original name. Per-kind reconstruction (mirroring
  `instantiate_ctor`'s `member_key` probe) would cover ctors only — a patch
  that leaves accessors needing a re-probe (a second resolution, violating
  Principle 24) and renamed imports broken forever.

**RULING — the uniform fix: the walk surfaces the terminal storage key; the
recorder records it.** The resolution walk is the ONE actor that knows the
terminal key (it looks the terminal up BY that key — the last followed edge's
`source.symbol`, or the written name when no edge renamed). Two halves:

1. **`cranelisp-types` (landed with this ruling, additive):** `Resolved`
   gains `storage_key: Symbol` + `storage_fq() -> FQSymbol` (`{home,
   storage_key}`), threaded through `chain_follow_committed` and
   `chain_follow_to_home` (new `pub(crate)
   resolve_terminal_entry_home_and_key`; the public
   `resolve_terminal_entry_and_home` is now its projection). `Resolved.fq`
   is UNTOUCHED — every display/attribution consumer is byte-identical by
   construction. `Resolved` is not serialized (no serde derives): zero cache
   surface. Baseline: +2 additive lines + `#[non_exhaustive]` (policy
   alignment; no external construction sites exist — verified). Unit pins:
   `resolve/tests.rs::storage_key_*` (member alias, renamed import,
   qualified renaming re-export, prelude-fallback alias, unaliased
   identity).
2. **`cranelisp-typecheck` (`/dev`, one small change-set):** in
   `record_reference_target`, the `resolved_targets` insert takes
   `resolved.storage_fq()` instead of `resolved.fq` (the ONE line at
   checker.rs:1429); `builtin_storage_fq`'s `def_resolved` arm likewise
   returns the resolution's `storage_fq()` (same value today — unrenamed
   prelude chains — flipped for structural uniformity). `user_fn_refs` (the
   `callees` feed) STAYS on `resolved.fq` in this change-set — `callees` is
   persisted `.meta.json` whose value stability is pinned this window; its
   own alias residual is FIXME 0621. Unit pins per leg: member-aliased ctor
   carrier == canonical `member_key`; member-aliased accessor carrier ==
   canonical `member_key`; renamed-import carrier == source storage key.

This is the structural close of the producer-gap class ("Resolve once,
record the entry's identity"): combined with the §1.1 value-source rule, a
carrier value composed from a written spelling is no longer something a
correct writer can produce by accident — walk-resolved kinds get the key from
the walk, mint-resolved kinds record the key they just probed/registered,
and transports copy existing carrier entries.

**Recorder-grounded re-sweep (supersedes the §1.1.1 table as the completeness
statement).** Every kind the backend will key-read (W1 + W2), by its ACTUAL
recorder, verifying the recorded SYMBOL against the terminal storage key.
Recorder census grep-verified this ruling: the only `resolved_targets`
writers are `record_reference_target` (checker.rs), the dotted leg
(infer.rs:347), `record_dispatch_target` (callees.rs), the mono legs
(monomorphise.rs:399/843/988), and the fn-value/AutoCurry sites
(mono_collect.rs:98/750); plus the `pattern_ctors` sidecar
(`instantiate_ctor`) and direct synthetic population (W0.b).

| # | Reference kind | ACTUAL recorder | Recorded symbol | Terminal storage key | Verdict |
|---|---|---|---|---|---|
| 1 | User fn, bare same-module (Var) | `record_reference_target` → `scope_resolve` | written name | same key | correct |
| 2 | User fn, plain/glob import or re-export chain, unrenamed (Var) | same | written name (edges preserve it) | same | correct |
| 3 | User fn, **renamed** import/export `[(foo bar)]` (Var) | same | **alias `bar`** | `foo` | **GAP → fixed by `storage_fq()`** |
| 4 | Qualified `m/sym` through a renaming re-export (Var) | same (`resolve_qualified` path) | **alias** | source key | **GAP → fixed (walk threads the key through `resolve_terminal_entry_home_and_key`)** |
| 5 | **Sum ctor, bare** (construction, callee, or value position; user `deftype` AND bootstrap-seeded alike) | `record_reference_target` — **NOT `instantiate_ctor`** (the §1.1.1 mis-attribution) | **bare alias `Pure`** | `member_key` (`IO.Pure`) | **GAP (0620) → fixed** |
| 6 | **Field accessor, bare** (call or fn-value position) | same | **bare alias `v`** | `Box.v` | **GAP (0620) → fixed** |
| 7 | Product ctor, bare (Var) | same | type-name key (dual facet — no alias edge) | same | correct |
| 8 | Hand-seeded internal ctor (`Bind` — bare storage key) | same (internal-reject gates precede) | bare name | bare name (no alias) | correct |
| 9 | Dotted `Type.member` (ctor or accessor, Var) | `dotted_member_identity` (infer.rs:347 leg) | `member_key` probe key | same — "exactly what the probe hits" | correct (verified checker.rs:1592) |
| 10 | Pattern ctors (sidecar; bare, dotted, qualified) | `instantiate_ctor` canonical-then-bare probe | whichever probe key HIT | same by construction | correct VALUE (S109 §10) — but the mono view-build seam read the WRONG MAP INSTANCE (0622); ruled §1.1.3 |
| 11 | Self-recursion carve-out (Var) | `record_reference_target` env-shadow arm | `{current_module, defn name}` | defn registers under its bare name | correct |
| 12 | Platform effect / extern / slot-carried primitive (Var; plain Apply keys off the callee Var) | `record_reference_target` | written name (unrenamed chains) / renamed → row 3 | same | correct (renames covered by fix) |
| 13 | Primitive/operator BuiltinFn (Apply) | `record_dispatch_target` → `builtin_storage_fq` | jit name via `def_resolved`, `primitives` fallback | same (prelude re-export chain preserves the jit name) | correct (flip to `storage_fq()` for uniformity — same value) |
| 14 | Trait method — call/deferred/value/curry-inner (Apply) | `record_dispatch_target` → TraitMethod arm | `{impl_module (shell), mangle}` | mangle IS the key in the writer's table | correct (W0.1b, `144828d1`) |
| 15 | SigDispatch — pass-4 mint / dedup / self-recursion / inner legs (Apply) | monomorphise.rs writers | `{caller, mangled}` at `register_mono_entry` | mint key | correct (mint-resolved) |
| 16 | SigDispatch — overload pending (Apply) | `resolve_pending_overloads` | `{current == defining, mangled}` | same (run-local same-module gate) | correct by reach |
| 17 | AutoCurry — plain fn target (Apply) | callee-span transport (mono_collect.rs:748) | copy of the callee Var's carrier | inherits rows 1–6 | correct AFTER the Var-leg fix (alias gap propagated here transitively; fixed transitively) |
| 18 | Fn-value mono rewrite (Var at arg) | sidecar insert at rename (mono_collect.rs:98) | `{current, minted mangle}` | mint key | correct (W0.1b) |
| 19 | Synthetic bodies (accessor arms / ctor `ConstrADT`) | direct population at synthesis | just-registered canonical key | same | correct by construction (W0.b) |

**No other alias/rename shapes exist**: the rename surface of the language is
exactly the `Import`/`Reexport` edge's `source.symbol` (member aliases,
renamed imports, renamed re-exports, glob-member bare aliases are all this
one edge shape), and the walk now threads the key across every edge — there
is no second mechanism by which a written spelling can diverge from a storage
key. Mangled names (`f$Int+Int`, `Trait.method$Type`) never pass through
alias edges (mint-resolved, rows 14–15).

**Behaviour-invariance + cache verdict.** The types half changes no consumer
(`fq` untouched; `storage_key` unread until the `/dev` flip; `Resolved`
unserialized). The typecheck half changes only `resolved_targets` VALUES —
unread by any live consumer until the W1 re-deploy (the stashed backend flip)
— and the field's documented MEANING ("the storage key that HIT") is
unchanged: this is conformance repair of wrong values, not a meaning change,
so **NO `CACHE_SCHEMA_VERSION` bump** (schema-19 window, the 0472 precedent);
`BUILD_ID` staleness invalidates any dev cache carrying alias-valued views
across the compiler rebuild.

**W1 gating verdict (supersedes §1.1.1's).** After the `/dev` recorder
change-set lands with its pins, the re-sweep shows **NO remaining producer
gap for any W1 kind (rows 1–17 all storage-key-correct)** — the W1 re-deploy
(pop `stash@{0}`, flip S3/S4 to the keyed `ctor_meta_at` read, populate the
KC-W0-6 fixtures) proceeds with no further producer prerequisites. The W2
value-seam legs (nullary ctor as value, accessor as fn-value) ride the same
Var-leg recorder and are fixed by the same change — no separate W2 producer
work remains either.

**Residual (out of this fix, filed):** `user_fn_refs`/`callees` still records
`Resolved.fq`, so a renamed-import or bare-accessor `UserFn` reference
persists an alias edge — dependency-sort edge misses (benign; Kahn fallback)
and, once the S101 session-transaction reverse index goes live, silent
affected-set starvation. Aligning `callees` onto `storage_fq()` is a
`.meta.json` MEANING change (schema bump) — **FIXME 0621** (`target:
/sprint`) schedules it at the next schema-bump window.

### 1.1.3 Map-provenance: the check-run pairing rule + the exhaustive carrier × construction-path matrix (S110 W3.1 `/arch` ruling — FIXME 0622)

**The defect (0622, fourth producer gap of the initiative).** A generic
ctor-pattern body defined in module A and monomorphised by a call from module B
yields a mono instance whose `MonoMatchArm.resolved_ctor` is `None`: the mono
view is built at `finalize_mono_codegen_view` (monomorphise.rs:519) with the
ENCLOSING run's `state.method_resolutions.pattern_ctors` — restored by
`recheck_body_for_mono` before the seam — while the template body's pattern
spans were recorded in A's separate check run. The `:516–518` comment's
assumption ("the original template check's entries serve every instance") is
true only when the template's check and the mono mint share ONE
`MethodResolutions` instance.

**The class is broader than filed: it is CHECK-RUN provenance, not
cross-module.** The same miss occurs SAME-module whenever the template's form
check and the mono mint are in different check runs — the REPL-incremental
case (template defined in input 1, first concrete call in input 2), where the
run-1 map was dropped at run end. The FIXME's candidate 1 (union the caller's
map with "the defining module's check-run sidecar") is therefore
unimplementable for the cross-run twin — that sidecar no longer exists at mint
time — and would additionally import the caller map's foreign-file spans
(`Span` is a bare byte range with no file id; a cross-file union invites
numeric span aliasing).

**Why the axis kept regenerating gaps — a span-keyed sidecar has exactly three
axes, and the prior sweeps closed two.** (1) *Key values* (which spans get
recorded) — closed by the 0616 recorder-coverage sweep; (2) *carrier values*
(which FQSymbol is recorded) — closed by §1.1's three-source rule + §1.1.2's
`storage_fq()` flip; (3) *map instance* (WHICH `MethodResolutions` the
view-build reads) — never swept until now. `MethodResolutions` has exactly
three provenances in the codebase: the **live run map** (accumulates across a
module check run), the **per-instance swap** (`recheck_body_for_mono`'s
take/restore), and the **accumulator** (per-form whole-map clones +
`sweep_post_pass_outputs`). 0622 is a provenance mismatch: a body annotated by
a per-instance recheck, viewed through the live run map.

**RULING — the check-run pairing rule (binding on every view-build site):**
*a codegen view is built from the SAME `MethodResolutions` instance that the
body-check run which annotated that body populated — never from a map
restored from, accumulated for, or belonging to a different check run.* The
mechanism already exists: `recheck_body_for_mono` re-checks the full body with
the fresh per-instance map live and `current_module` switched to `home`, so
`check_constructor_pattern` → `instantiate_ctor` re-records EVERY ctor-pattern
span into the per-instance map, resolved in the defining module's context
(and `resolve_auto_curry` drains inside the swap window, so curry transports
land there too). **The per-instance map is already complete for all three
carriers; the defect is only that P7 reads two different maps.** The fix is
strictly smaller than either filed candidate: no transport machinery, no
union — pass the per-instance map's `pattern_ctors` alongside its
`resolved_targets`.

**The pinned `/dev` (typecheck) change-set — one narrow deployment, no
`cranelisp-types` edit, no schema bump:**

1. `traits/monomorphise.rs::finalize_mono_codegen_view` — take the
   per-instance `resolutions: &MethodResolutions` (replacing the bare
   `resolved_targets` param); build the view as
   `MonoExpr::from_expr(body, &resolutions.pattern_ctors,
   &resolutions.resolved_targets)`. Delete the `:516–518` false-assumption
   comment; state the pairing rule in its place. Caller at P7 passes
   `&resolutions`.
2. `program/register.rs::register_test_fn_mono_roots` (`:931`) — the SIBLING
   cell this sweep surfaced: the test-root view is built from the enclosing
   live maps while its body is annotated from the per-root recheck's
   `resolutions`. Correct-by-reach today only because the mint is normally
   same-run as the template's form check; the retry edge (a root left
   `Polymorphic` by a failed recheck, re-attempted in a later run) reads a map
   without the body's spans. Same fix: build from the per-root `resolutions`
   maps (both).
3. `program/finalize.rs::sweep_post_pass_outputs` — hygiene: the sweep
   extends `resolved_calls` + `resolved_targets` but silently DROPS
   `taken.pattern_ctors`. Harmless today (no post-pass records pattern ctors
   into the enclosing map — the rechecks swap), but a partial sweep of a
   3-field struct is how the next starvation hides. Extend all three
   (behaviour-invariant).
4. Unit pins (failing-first): (i) a cross-module mono of a ctor-pattern
   template carries `resolved_ctor = Some(<canonical member_key>)` on its
   view's arm — the 0622 shape, RED on main; (ii) the cross-run same-module
   twin (template checked under one `CheckState`, mono minted under a fresh
   one over the same tables) — RED on main; (iii) same-run same-module mono
   view unchanged (regression pin). These unit pins ARE the
   failing-not-ignored defect record (an e2e cannot fail on main — the S19
   fallback masks it until W3 pops; the ~53 stdlib REDs on the stash are
   W3's wave-level acceptance).

**Cache verdict: NO `CACHE_SCHEMA_VERSION` bump** (schema-19 window, the
0472/0620 precedent). Only persisted `codegen_view` VALUES change
(`resolved_ctor` `None` → the correct storage key on mono-instance arms); the
field's documented meaning is unchanged; stale caches remain valid on main
(S19 fallback still present) and any pre-fix cache is invalidated by
`BUILD_ID` staleness across the compiler rebuild before W3 re-deploys.

**The exhaustive matrix — every carrier × every view-construction path.**
Carrier census (grep-closed over `mono_expr.rs`): exactly THREE —
`MonoExpr::Var.resolved_target` (C-V), `MonoExpr::Apply.resolved_target`
(C-A), `MonoMatchArm.resolved_ctor` (C-P). `resolved_call` is supplementary
dispatch metadata (Phase-2 pin), not a keyed carrier; `mode_summary` rides
the entry, not the view. Backend keyed-read census (context.rs): `entry_at` +
its projections (`ctor_meta_at`, `is_callable_target_at`, `arity_at`,
`callee_summary_at`, `is_inline_primitive_at`, `got_entry_at`,
`is_slotless_template_at`) — all key off the three carriers. Construction-path
census (grep-closed over `from_expr`/`lenient_from_expr` callers in
typecheck; backend `test_support.rs` is unit-fixture-only per KC-W0-6; the
ownership-fixpoint call at `fixpoint.rs:168` is a strictness probe, not a
view producer):

| # | View-construction path | Map instance read | C-V | C-A | C-P | Verdict |
|---|---|---|---|---|---|---|
| 1 | Per-form strict, single-sig (`body.rs:348`) | live run map | ✓ | ✓ | ✓ | correct — body checked and viewed in the same run; live map accumulates across the run |
| 2 | Per-form strict, multi-sig mangled variants (`register.rs:393`) | live run map | ✓ | ✓ | ✓ | correct — variant bodies checked per-form earlier in the SAME run |
| 3 | Shared strict-first/lenient-fallback builder (`support.rs:241/243`: `__expr` disp-3, macro-clause, generic/best-effort templates) | caller's live maps | ✓ | ✓ | ✓ | correct — same-run; lenient walk populates carriers identically to strict (`mono_expr.rs:552–608`) |
| 4 | Finalize view-rebuild (`finalize.rs:910`) | accumulator (per-form whole-map clones + post-pass sweep) | ✓ | ✓ (fn-value rewrite + curry legs swept in, W0.1b) | ✓ today; fix 3 makes it structural | correct — accumulator ⊇ live map at last form; no post-pass mints pattern ctors (rechecks swap) |
| 5 | Impl / default / HKT trait-method writeback (`impl_check.rs:645`) | live run map (no swap; D1 home switch active during the method check) | ✓ | ✓ (`impl_module` per §1.1.1) | ✓ | correct — the method body's records land in the live map in the same run |
| 6 | **Mono instance** (`monomorphise.rs:519`) — same-run, cross-module, AND cross-run | resolved_targets: per-instance ✓; pattern_ctors: **enclosing** ✗ | ✓ (recheck `infer_var` + P4/P5 dispatch legs + in-swap curry drain) | ✓ | **✗ THE 0622 CELL** | **fix 1** — read the per-instance map for both |
| 7 | **Test-fn mono roots** (`register.rs:931`) | **enclosing** for both, body annotated from per-root recheck | (✗) | (✗) | (✗) | **fix 2** — correct-by-reach same-run; the cross-run retry edge is the gap; uniformity flip closes it |
| 8 | Synthetic ctor bodies (`adt.rs:207` + bootstrap seeds) | empty sidecars | n/a | n/a | n/a | correct by construction — `ConstrADT` bodies carry no references, no arms |
| 9 | Synthetic accessors (`adt.rs:606`) | direct one-entry map at synthesis | n/a | n/a | ✓ | correct by construction (W0.b) — product-only (sum fields have no accessor, `adt.rs:236`), key = the product dual-facet type-name storage key |

Writers that ride the above paths' maps (not builders): the auto-curry drain
writes to whichever map is live at its drain site (per-form: path 1; in-swap:
path 6) ✓; the fn-value rewrite writes to the live map + sweep + path-4
rebuild ✓ (W0.1b); the mono inner-leg writers (monomorphise.rs:399/843/988)
write to the per-instance map explicitly ✓.

**Recorded latent hazard (NOT a W3 blocker):** `Span` is a bare byte range
with no file identity, so one run's shared maps can hold spans from more than
one file (default trait-method bodies carry the trait file's spans into the
impl-writer's run; macro-expanded bodies may carry macro-definition-file
spans). A numerically-equal span pair across files can cross-attribute a
carrier — always `Some(wrong)`, never `None`, so it cannot trip W3's
hard-miss on a valid program; it is a pre-existing (since S109 §10),
probabilistically narrow wrong-value class. Structural cure if evidence ever
surfaces: per-body map scoping (the path-6 discipline generalised) or a
source id in `Span`. Evidence-gated; not scheduled.

**W3 gating verdict (the initiative's producer close).** With fixes 1–3 + the
pins landed, every cell of the 3-carrier × 9-path matrix is
correct-by-same-run-map, correct-by-per-instance-map, or
correct-by-construction — **no construction path can produce a `None` carrier
for a valid program on any kind the W1/W2/W3 keyed reads consume. The
producer is COMPLETE across carriers × paths; the W3 re-deploy (pop
`stash@{0}`, delete S19/S20 + the resolver family, grep gate) proceeds with
NO further producer prerequisites.** This is the structural close of the
whole 0583 producer-gap sequence: 0616 closed the key axis, §1.1/§1.1.2
closed the value axis, this ruling closes the map-instance axis — and a
span-keyed sidecar has no fourth axis. Both mono-view builders now consume
the map handed back by their own recheck, and any NEW view-build site must
name its two maps explicitly (required `from_expr` params, Principle 18)
under the pairing rule, so a recurrence requires violating a stated rule at a
chokepoint `/review` checks, not overlooking an unenumerated cell.

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
- Delete S19's `None`-arm fallback (a `None` on ANY ctor arm is then keying
  drift, hard error; the §10.3 fold-in note is superseded). *(0622 correction:
  "dead since W0.b" over-claimed — W0.b covered the SYNTHETIC class only; the
  mono-view seam still produced `None` arms via the wrong map instance until
  the §1.1.3 pairing fix. S19's deletion is gated on that fix landing.)*
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

**W0.1b addendum (post-W0.1 `/arch` ruling, §1.1.1):** a second pinned types
diff rides the same schema-19 window — `ModuleEntry::TraitImpl.impl_module` +
`ResolvedCall::TraitMethod.impl_module` (both required fields, no serde
default) + the §1.1.1 typecheck derivation fixes (trait-leg module off the
shell; AutoCurry callee-span transport; fn-value rewrite sidecar update).
Baseline regen + `interfaces.md` + rustdoc ride that change-set. Still no
additional schema bump. *(Landed `144828d1`.)*

**W1.1 addendum (0620 ruling, §1.1.2):** the types half — `Resolved.
storage_key` + `storage_fq()` threaded through both chain-follow walks —
landed WITH the ruling (additive, `Resolved` unserialized, +2 baseline lines
+ `#[non_exhaustive]`, five `resolve/tests.rs::storage_key_*` pins). The
pinned `/dev` (typecheck) change-set: `record_reference_target`'s
`resolved_targets` insert flips `resolved.fq` → `resolved.storage_fq()`;
`builtin_storage_fq`'s `def_resolved` arm likewise; `user_fn_refs` stays on
`.fq` (FIXME 0621); unit pins per §1.1.2. No schema bump (value-only,
schema-19 window).

**W3.1 addendum (0622 ruling, §1.1.3):** typecheck-only, zero types diff —
`finalize_mono_codegen_view` reads the per-instance `resolutions` for BOTH
sidecars; `register_test_fn_mono_roots` likewise (its per-root recheck maps);
`sweep_post_pass_outputs` sweeps all three `MethodResolutions` fields; unit
pins per §1.1.3 item 4. No schema bump (value-only, schema-19 window;
`BUILD_ID` covers dev-cache skew). W3 re-deploys from `stash@{0}` after it
lands.

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
