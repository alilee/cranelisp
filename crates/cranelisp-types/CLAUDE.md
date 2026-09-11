# cranelisp-types — local conventions

The voice of the code: contract gotchas that bite consumers of the cross-crate
substrate. Owned by `/arch`; other skills file FIXME `target: /arch` for shape
changes. Design narrative: `design/arch/interfaces.md` + `bounded-contexts.md`
§7 — this file records only what rustdoc doesn't say.

## The serde shape IS the cache contract

`SymbolTable` and its `Binding`/`Decl`/`Callable`/`Life` tree serialize into the
backend's `.meta.json` sidecars.
**Any serde-visible change — field add/delete/retype, OR a meaning change to
what an existing field records — bumps `CACHE_SCHEMA_VERSION` in
`crates/cranelisp-backend/src/cache/mod.rs` in the SAME change-set.** (Read
the constant for the current value — a literal here goes stale, and did.) The constant lives in the backend, not here — an edit here is
incomplete without the cross-crate bump (precedents: `codegen_view` 7→8, S101
`callees` widening 10→11, S102 ownership carriers 11→12). Only exempt class: a
`#[serde(default)]` addition whose default equals the fresh-build value
(`SymbolTable.schema_version` rustdoc, `module.rs:218`).

- `#[serde(skip)]` runtime fields: `got`, `linker`, and
  `Realization::Body.code`. Caches deserialize as `SymbolTable<(), ()>`; int
  rehydrates via `SymbolTable::into_concrete` — every `code` becomes `None`.
- The `#[serde(bound = "")]` on `SymbolTable` and the generic lifecycle
  carriers is load-bearing: without it the derives demand `C: Serialize` even
  for skipped fields and the `()` default stops compiling.
- **`GotTable::clone()` returns a fresh, all-null table** (`got.rs`) —
  deliberate, matching `#[serde(default)]`. Sharing happens only through the
  `Arc` on `SymbolTable.got`. Cloning a `GotTable` never copies pointers.

## Callability is structural — read through the accessors

The GOT slot rides only `Life::Concrete` and `Life::Broken`, nested beneath a
`Decl::Callable`; slot-less templates, inline primitives, and host-promised
callables have no slot field (Principle 20). Use the read-throughs, never
re-pattern the lifecycle set:

- `Binding::callable_got_slot()` — the ONE callable-address read.
  `Life::Inline`, `Life::HostPromised`, `Life::Declared`, and `Life::Template`
  answer `None` by construction.
- `Binding::is_callable_target()` — the resolution STOP condition; covers
  slot-less inline/host-promised callables and the unslotted
  `Decl::TraitMethod` dispatch declaration. A
  `callable_got_slot().is_some()` probe at a resolution seam reopens the 0476
  shadowing hole.
- `SymbolTable::codegen_targets()` — the codegen-compilable projection
  (Decision 22): directly named callables, overload arms and macro clauses
  whose lifecycle is exactly `Life::Concrete` with `Realization::Body`.
  Templates and other non-body states are mono/dispatch sources, never codegen
  targets.
- `Binding::mode_summary()` / `SymbolTable::publish_body_ownership()` — a
  checked body summary is available only from `Life::Concrete`; publication
  replaces the annotated Body view and stamps its summary twin atomically.
- `Binding::type_def_info()` — the ONE "does this binding answer as a type"
  reader over the S79 dual facet (`Decl::Type(TypeRecord::Defined)` OR a
  product ctor `CallableOrigin::Ctor { type_def: Some(..) }`). Matching only
  `Decl::Type` at a type-consuming seam silently skips product types — the
  FIXME-0573 persistence data-loss class. `type_ctor_names` (`heap.rs`) is the
  ctor-name projection over the same switch.
- `CallableOrigin::PlatformEffect.poll_shape` polarity is INVERTED from the
  C-ABI `blocking` flag: `false` means blocking.

## Unified lifecycle and concreteness

- **The `SymbolTable` lifecycle funnels are the only fresh-slot authority.**
  `declare` + `settle_concrete` and the born-settled installers pair a
  concrete scheme with the opaque `CallableSlot` in one act; raw allocation
  and raw callable publication are private. `CallableSlot::rebind` is the
  checked reuse path. `validate_lifecycle` re-derives all live and retired
  claims after construction, clone, or deserialization.
- **Instance identity is authored once.** Ordinary `settle_concrete` and
  `install_concrete` do not accept `minted_from`. `install_instance(link, …)`
  derives the storage key from the actual settled function scheme plus the
  authored owner in the link via `concrete_callable_key`, stores the back-link,
  and returns `(key, slot)`. The common private validator rejects
  a key inconsistent with that settled-signature derivation before install mutation and from
  `validate_lifecycle` after clone/deserialization as
  `LifecycleError::InstanceKeyMismatch`; a restored mismatch is cache-stale.
- **Public non-exhaustive lifecycle records need explicit authoring paths.**
  Keep `Callable`, `CallableArm`, `OverloadedCallable`, `MacroDeclaration`,
  `MacroClause`, `TraitRecord`, `TraitMethodRecord`, `SpecialFormRecord`,
  `SynthSpec`, `ConstrainedMeta`, and `BrokenProvenance` non-exhaustive;
  construct them through their role-specific `new` functions or the
  `SymbolTable` declaration-family installers. Do not add raw field-literal or
  lifecycle-state escape hatches. `RetiredSlot` remains private and `ImplShell`
  remains types-authored through
  `enrol_written_trait_impl`. A `crates/cranelisp-types/tests/` external
  consumer compile-pass constructs every published record; in-crate unit
  tests cannot detect E0639. `NameCandidate` is the read-only exception:
  external consumers inspect its public fields, while only symbol-table
  exposure funnels construct it.
- **Trait method declarations are not executable lifecycle entries.** Store a
  `deftrait` member as `Decl::TraitMethod(TraitMethodRecord)` at canonical
  `member_key(Trait, method)` through `install_trait_method`; read that terminal
  through `Binding::trait_method`. Bare method reachability is a general
  `NameCandidate` exposure of that FQ, installed for imports/re-exports
  through `expose_candidate`; it coexists with an ordinary accessor candidate.
  The exposure is serialized with the table, canonical-source
  deduplicated, and validated locally plus at the cross-module load boundary;
  hot reload replaces it with its owning table. The record owns its constrained
  scheme, parameter names, documentation and canonical trait identity. Never leave it permanently
  `Life::Declared`, store it only at the bare key, create a parallel map, scan
  `TraitRecord`s by method name, fabricate an impl-method origin, or invent a
  body.
- **ADT construction is slotless until settlement.** `build_adt_entries`
  returns `AdtCallableSpec` recipes plus `Binding<C>` values typed for the
  target table; callers submit each callable recipe to the table funnel. The
  generic-constructor control is
  `adt_build/tests.rs::generic_constructor_recipe_has_no_slot_or_lifecycle_state`.
- **Cleanup is state-specific.** `remove_non_callable` is the ADT pre-seed
  rollback; `discard_declared` accepts only `Declared { prior: None }` and is
  the multi-sig internal-key cleanup. There is no generic callable remove,
  rename, mutable binding projection, or caller-side slot reclamation.
- **`heap::ctor_field_types_at(table, ctor_key, args)`** — the ONLY legal
  derivation of ctor field types at a concrete instantiation
  (concrete-or-refuse; one residual field refuses the whole ctor; caller bugs
  are `CtorFieldsAtError::NotACtor`/`ParamArity`/`InstantiationMismatch`,
  never conflated with the refusal). The backend's hand-rolled `scheme.ty`
  walk retires onto it in the S120 wash.
- **`ConcreteType::result_root()`** — the ONE IO-head-strip rule (FIXME 0898;
  one hop, `primitives/IO` only). Backend `result_roots` and int
  `release_key` re-express over it in the wash; hand-rolling the match again
  is the two-encodings defect it closed.
- **`got_data_symbol_name` is INJECTIVE** (FIXME 0748): `_`→`__`, `.`→`_d`,
  `-`→`_h`, `_u{cp:06x}` catch-all; alphanumeric paths are fixed points
  (`__cranelisp_got_primitives` is a link-time ABI literal); `_entry` is
  outside the escape image. Changing the scheme renames every cached `.o`'s
  relocations — a schema-window event.
- **`SymbolTable.written_trait_impls` + `WrittenTraitImpl` +
  `enrol_written_trait_impl` + `trait_impl_key`** — the 0869 writer-side
  trait-impl cache carrier (`trait-impl-cache-carrier.md`). The field has
  deliberately NO `#[serde(default)]` (absence = hard serde error;
  wholesale pre-24 invalidation). `trait_impl_key` is the ONE `impl$` key
  mint — never hand-roll `format!("impl${{}}${{}}", …)`; the two legacy
  typecheck sites re-point in the wash. Fresh registration uses
  `stage_trait_impl_shell` plus `RetainedCallables`; it upserts the writer
  record only after all methods settle, then commits both opaque tokens.
  Failure restores/removes methods and shell while leaving the prior writer
  record untouched. Restore continues to use strict
  `enrol_written_trait_impl`.
- **Deleted dead surface (FIXME 0918)**: `ImplSexp`, `CompileResult`,
  `CallEdge`/`CallInfo`/`CallGraph`, `StructuralDeclEntry` +
  `append_structural_decl`. The pub structural Vec fields ARE the append
  contract; live call edges are read through `Binding::callees()`.

## Lifecycle fields are populated through funnels

`callees`, `ast`, the concrete view/realization, and the slot enter together
through the settlement/install funnels. Checked AST-backed bodies use
`settle_checked_template` / `settle_checked_concrete`; later callee harvests
use `replace_callees`. Ownership submits its completely annotated view through
`publish_body_ownership`, which stamps the view and lifecycle summary twins
in one act; the one-sided public `set_mode_summary` is forbidden. Typecheck
writes `value_use` only through the state-checked `SymbolTable::set_value_use`.
The S101
transaction reverse index still starves silently if a body-check seam omits
the callee harvest (completeness contract in
`crates/cranelisp-typecheck/CLAUDE.md`).

Fields that LOOK optional but are contractually required downstream:

- `Binding::codegen_view()` projects only
  `Life::Concrete { realization: Realization::Body { view, .. }, .. }`.
  `codegen_targets()` uses that same structural shape for each directly named
  callable or family arm, so a codegen target cannot exist without its view.
- `Expr.inferred_type: Option<Box<Type>>` — `None` past typecheck is not a
  soft state: `MonoExpr::from_expr` fails it as
  `ViewBuildError::NotConcrete(NotConcrete::Var(0))` (`mono_expr.rs`), the
  unified ambiguity error. Its sibling arm `ViewBuildError::Unresolved` is
  the RESOLUTION gate (real-span `Var`/`Apply` with no typed verdict) —
  routed as a located error, NEVER into the lenient fallback.
- `ModeSummary` vectors — **never index directly**; `param_mode(i)` /
  `param_flow(i)`/`spark_op(i)` are the ONE home for ⊤-on-absence
  (missing/short ⇒ Owned/Retained/true; the `ModeSummary` accessors in `ownership.rs`). ABI comparison
  only via `abi_eq`/`abi_eq_opt` (`None` ≡ all-conservative).
  `ownership_analysis_off()` is read-once (OnceLock — one polarity per
  process) and flips a backend cache global key.

## Resolution primitive (`resolve.rs`) traps

- **`Resolved` carries one identity.** `canonical` is the terminal
  `FQSymbol` which direct-probes `symbol_tables[module][symbol]`; `entry` is
  that binding. Consumers never compose storage identity from the written
  spelling. `ResolutionScope::resolve_candidates` returns the complete set;
  `resolve` is the unique-candidate convenience.
- `split_qualified` requires BOTH `/`-parts non-empty:
  bare `/`, `//`, `foo/`, `/bar` are literal names (Principle 16, FIXME
  0328/0331). A `/`-named operator mis-resolving means a guard was lost —
  fix HERE, never with a checker-side literal-lookup shortcut.
- `ResolutionScope::resolve` (the SOLE public resolution entry point since
  S108 Wave G — the free `resolve`/`resolve_with_fallback` are private
  internals, and the fallback is decided ONCE at scope construction, never
  per call) retries prelude only on the not-found error class;
  `PrivateInaccessible`/`QualifiedModuleUnknown` return as-is. The prelude
  retry passes a PUBLIC-only I-1 filter on the **prelude HEAD binding** (the
  entry in prelude's own table — §8.8.1 provides prelude's public *names*;
  the terminal check stays as defence in depth); a private prelude hit —
  head OR terminal — reports as the ORIGINAL current-module not-found
  (`resolve_with_prelude`). The head-vs-terminal gotcha was FIXME 0567,
  fixed S109. The current direct types control
  `resolve/tests.rs::prelude_fallback_remains_public_head_only` is the public
  direct-binding leg;
  `resolve/tests.rs::prelude_alias_head_visibility_controls_public_terminal_fallback`
  discriminates a private alias head (original current-module not-found)
  from a public alias head reaching the same public terminal (success).
- `member_key(&str, &str) -> Symbol` (resolve.rs) is the ONE mint point
  for canonical dotted `Parent.member` keys: type members (§8.5.2 inverted
  member model: field accessors `Box.v`; ctor keys `Maybe.Some` from S109)
  and trait-method terminals (`Display.show`). Never
  hand-roll `format!("{}.{}", ..)` for a member key — per-site copies are
  how the key grammar drifts. Its projection INVERSE is
  `bare_member_name(&str) -> &str` (`Maybe.Some`→`Some`, `m/Type.Ctor`→`Ctor`;
  Principle-16 guards keep `/`, `.`, `foo.` literal) — the ONE terminal-segment
  grammar for comparing written forms / storage keys against bare display
  names (typecheck exhaustiveness normaliser, backend sparkability exclusion).
  Never hand-roll the `rsplit` pair either — the two sides of such a
  comparison drifting was the S109 I-1 finding.
- `chain_follow_committed`'s same-module alias arm carries a
  `CHAIN_FOLLOW_DEPTH_LIMIT` cap: a degenerate same-module alias cycle reads
  as a not-found miss, never a stack overflow. The same bound also governs the
  scoped module-alias walk, pinned by
  `resolve/tests.rs::alias_walk_refuses_more_than_the_shared_depth_limit`.
  `resolve/tests.rs::union_view_same_module_candidate_resolves_terminal`
  discriminates a staged same-module candidate that reaches its terminal.
- The bare primitive's generic miss is `TypeNotFound`-shaped regardless of
  kind (`resolve.rs::not_found`) — never infer entry kind from the
  error variant.

## Soundness-coupled single-source predicates

- `value_layout` / `value_layout_with_lookup` (`heap.rs`) — the shared Copy/value-flattening verdict BOTH
  typecheck's `Copy` classifier and backend's `HeapCategory::Value` arm must
  delegate to; divergence is a UAF. Single-field-only is soundness, not a
  size bound (Wave-3a blockers; the `adt_layout_words` rustdoc); bumping
  `VALUE_LAYOUT_MAX_WORDS` is a cache-schema-bump event. The table API wraps
  the lookup API; staging callers provide their existing exact-key lookup.
  Each lookup returns an owned binding after releasing its table/staging guard;
  the walk drops metadata before recursing — two Refs in one shard deadlock.
- `type_ctor_names` (`heap.rs`) — the ONE defined-type-vs-product-ctor-facet
  reader (FIXME 0528 mirror cure); backend heap classifiers delegate here.
- `is_strict_type_concrete` (`mono_expr.rs`) — the pure-TYPE half of the
  `from_expr` gate (Annotate erased; every other node's `inferred_type` must
  convert), single source for the ownership fixpoint's W0.b universe pin
  (FIXME 0689). A drifted local mirror silently perturbs every cluster
  summary; ask THIS predicate, never re-walk the gate (and never probe via
  `from_expr` with empty maps — since S114 that answers `Unresolved`, not the
  type question).
- `Type::is_concrete()` (`types.rs`) — the GOT-slot eligibility gate,
  strictly stronger than "no constraints" (constraint-emptiness gating was the
  S84 `(Box a)`-through-HOF SIGSEGV); `TyConApp` counts as non-concrete.
- `render_type` (`types.rs`) — the single `Type`→string walk (S87, FIXME
  0420); new variants edit one walk, not five renderers. `apply` carries a
  direct self-map cycle guard (FIXME 0279/0295) —
  debug-asserts, treats the var as unbound in release.

## Known asymmetries a reader would misread as bugs

- `Pattern::Constructor.name: SymbolRef` — the parser does NOT split
  qualified names: `(option/Some x)` lands verbatim as
  `{ module: None, name: "option/Some" }`; the split is a pending lift, the
  `SymbolRef` slot its destination (`ast.rs`). The resolved FQ lives in
  the `MethodResolutions.pattern_ctors` span-keyed sidecar, not on the AST.
- `PlatformSpec.name` is still bare `String` — the `ModuleName` narrow is a
  recorded standing target (S69 Sub 21, re-affirmed S119/FIXME 0919) with a
  real trigger: it rides the first change-set touching the construction sites
  (frontend `module_extract.rs::parse_platform` / the S120 int wash's
  `src/platform.rs` manifest-order mint). See the `PlatformSpec` rustdoc.
- `MethodResolutions` derives `Serialize` but is NOT serde_json-safe
  (`Span`-keyed maps; non-string keys). Fine for the binary cache; never
  JSON it (S106 latent note).
- The marshal tags' ctor-order truth is
  `cranelisp-typecheck::builtins::register_macros_module` — unassertable from
  this crate (dependency direction); `marshal/tests.rs` guards only the
  constants themselves.
- **`ResultMode::Fresh` is the `Default` but NOT the result axis's
  conservative point** — it is that axis's STRONGEST claim (backend elides the
  callee return protect on a *present* `Fresh`). The axis's ⊤ is
  `MayAliasAny` (S121); the conservative spelling of a WHOLE summary is
  `None`. So `ModeSummary::default()` and `is_abi_conservative()` are
  caller-side-ABI statements only and are **not** substitutable for absence,
  and no producer may mint a summary as a fallback. The one home for this
  rule is `ownership.rs`'s module rustdoc §Monotone defaults — read it before
  touching any `result` arm.

## Public-surface mechanics

Submodules are `pub(crate)`; the crate-root re-export list in `lib.rs` is the
sole surface. Any surface change regenerates `public-api.txt` (canonical
command: `design/arch/CLAUDE.md` §Baseline-diff) WITHOUT `--features
test-support` — that gate keeps `test_support` (Tier-2 builder, consumed by
typecheck's unit suite via the Cargo feature) off the frozen edge.
Every public lifecycle item, constructor, enum variant, and public field has
its own `///` contract. A type-level summary does not substitute for variant
and field documentation: downstream streams must be able to learn legal
authoring, state meaning, and ownership without reading a private funnel.
`#[non_exhaustive]` is policy on every pub struct/enum EXCEPT: string
newtypes, `View` (private fields), the `#[repr(C)]`/`#[repr(u32)]` ABI
types (`SchedulingClass`, `ConcurrencyDescriptor`, `Poll`, `HeapHeader`) —
layout contracts governed by `cranelisp_platform::ABI_VERSION` bumps
(Principle 14), offsets pinned by const asserts (`heap.rs:35`) and layout
tests (`scheduling.rs:445`) — and the ownership mode vocabulary (`Mode`,
`ResultMode`, `ParamFlow`, plus `ModeSummary`): ABI-bearing memory-model
enums where exhaustive consumer matches are the Principle-18 safety feature
(a variant addition MUST break every consumer match at compile time;
`#[non_exhaustive]` would compel the `_ =>` arms that hide a missed variant)
and a summary struct constructed literally by both producers. See the
`ownership.rs` module rustdoc §"Exhaustiveness discipline" (recorded S111
Phase 3); every variant-adding change-set re-runs the `_ =>`/`== Fresh`
escape grep over `ResultMode`. The unified lifecycle's closed sums
(`Decl`, `TypeRecord`, `Life`, `TemplateBody`,
`TemplateKind`, `CallableOrigin`, `Realization`, `RetireReason`), the ADT
recipe sum `AdtEntrySpec`, and the reader-quote sum `QuoteHead` deliberately
join this exception class: exhaustive consumer matches are the vocabulary
gate, so adding a variant must break every affected match instead of being
hidden by `_`. Their payload structs remain non-exhaustive and cross-crate
construction goes through the sanctioned constructors/funnels above. The
**typed resolution sums `VarRef`/`ApplyRef`**
(`mono_expr.rs`, S114 FIXME 0653 prong 3) join the same exception class:
closed sums whose exhaustive consumer matches ARE the contract ("unresolved"
has no constructor; a `_ =>` arm would re-smuggle the ambiguous default) —
LIVE since the S114 Phase-5 carrier flip: `MonoExpr::Var.resolution: VarRef`
/ `MonoExpr::Apply.dispatch: ApplyRef` are non-optional with NO
`#[serde(default)]` (absence is unrepresentable — a cache missing them is a
hard serde error by design; `CACHE_SCHEMA_VERSION` 22 window), and
`MethodResolutions` carries the TOTAL typed `var_refs`/`apply_refs` maps
(`design/arch/typed-resolution-carrier.md`). **`ViewBuildError`**
(`from_expr`'s failure sum) is in the exception class too: the
`NotConcrete`-vs-`Unresolved` routing at the strict-first/lenient-fallback
seam is the load-bearing match — `NotConcrete` may fall back to
`lenient_from_expr`; `Unresolved` is a located typecheck error that MUST NOT
be swallowed into the fallback (and is raised BEFORE the node's type, so a
miss cannot slip through as `NotConcrete`). `lenient_from_expr` tolerates
TYPES only — a real-span verdict miss PANICS (always-on tier-3 seam assert);
a `Span::SYNTHETIC` miss takes the all-local verdict in both walks (synthetic
nodes are structurally outside span-keyed transport). Their sibling
`MonoExpr::synthetic_local_from_expr` (FIXME 0685) is the ONE sanctioned
all-local builder for `Span::SYNTHETIC` synthesis bodies (typecheck adt.rs
ctor/accessor): no resolution-map params by design, plus an always-on
synthetic-span assert — routing a real (check-run) body through it panics
deliberately; never "fix" that by widening the license.

## Seam map + `#[cfg(test)]` locations

One module per concern, tests as `{module}/tests.rs` siblings: `module`
(`SymbolTable`, lifecycle funnels, chain-follow), `lifecycle`
(`Binding`/`Decl`/`Callable`/`Life`), `resolve`, `newtype`, `types`, `concrete`,
`mono_expr`, `check`, `got`, `heap` (at
`heap/value_layout_tests.rs`), `ownership`, `error`, `marshal`. Inline
`#[cfg(test)] mod tests`: `view.rs`, `scheduling.rs`, `macro_expander.rs`,
`test_support.rs`. NO test modules in `ast.rs`, `sexp.rs`, `span.rs`,
`parsed.rs`, `pipeline.rs` — pinned by consumer-crate suites, not locally.
