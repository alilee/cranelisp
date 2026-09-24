# Backend keyed consumption — resolved identities at the typecheck/backend boundary

**Status: canonical contract, maintained by `arch`.** Delivered S110 (FIXME
0583); the carrier shape was reshaped S114 into the closed sums `VarRef` and
`ApplyRef`. Typecheck emits the
fully-qualified storage identity of every statically resolved reference; the
backend performs no name resolution — one keyed fetch, kind discrimination on
the fetched binding, a hard `CodegenError` on a miss. This realizes
[Principle 24](principles/24-resolve-once.md) at the typecheck→backend seam and
is stated as [BC 2](bounded-contexts.md#2-typecheck-cratescranelisp-typecheck)
invariant 13 (producer) and
[BC 3](bounded-contexts.md#3-backend-cratescranelisp-backend) invariant 10
(consumer). Section numbers are stable: tests and source cite them.

The wave-by-wave delivery record (S110 W0–W3, the S1–S24 site inventory, the
pinned diffs and gating verdicts) is in Git history.

---

## 1. The one-carrier contract

- Every statically resolved reference crosses the boundary as a storage
  identity: an `FQSymbol` whose module is the resolution's terminal home and
  whose symbol is the exact table key at which resolution terminated. It is
  never the written spelling and never a display name.
- The carriers are `MonoExpr::Var.resolution: VarRef`,
  `MonoExpr::Apply.dispatch: ApplyRef` and `MonoMatchArm.resolved_ctor`,
  populated by `MonoExpr::from_expr` / `lenient_from_expr` from the three
  span-keyed sidecars of `MethodResolutions` (`var_refs`, `apply_refs`,
  `pattern_ctors`), which are required parameters: a view cannot be built
  without answering the question
  ([Principle 18](principles/18-enforce-invariants-structurally.md)).
  Shape, totality and the "unresolved has no constructor" rule:
  [interfaces — method resolutions](interfaces.md#method-resolutions) and the
  rustdoc in `crates/cranelisp-types/src/mono_expr.rs` and
  `crates/cranelisp-types/src/check.rs`.
- `ResolvedCall` is supplementary dispatch metadata (inline-builtin intercepts,
  auto-curry counts, trait resolution for the as-value wrapper). The backend
  never reads it as the keyed-lookup carrier. `ResolvedCall::TraitMethod.impl_module`
  carries the impl writer's module on the resolution product so the carrier
  writer never re-derives it (§1.1.1).

### 1.1 Semantics — "whichever storage key HIT"

The recorded `FQSymbol` is the identity under which the referenced binding
actually resolved. Per kind:

| Reference kind | Carrier value | Backend read off the fetched binding |
|---|---|---|
| Concrete user fn | `m/f` (bare storage key) or the mangled variant / mono-instance key the dispatch selected | `callable_got_slot()` → GOT-indirect call; `arity_at`; `callee_summary_at` |
| Primitive, slot-carried | `primitives/add-i64` | `got_entry_at` → GOT-indirect |
| Primitive, inline (the vec-query trio) | `primitives/vec-get` | `is_inline_primitive_at` → inline emission; the binding's kind is the discriminator |
| Sum constructor (construction, callee or value position) | `m/Type.Ctor` — the canonical `member_key` ([constructor keys](dotted-ctor-canonical-keys.md)) | `ctor_meta_at` / `ctor_value_shape_at` |
| Product constructor | `m/Type` — the dual-facet single key | the same constructor arm |
| Platform effect | `m/effname` — the defining entry | poll vs blocking vs stamp, all off the one fetched binding |
| Host-promised extern | `primitives/discover-tests` | the symbol is the ABI key (`Linkage::Import`) |
| Trait-method / sig-dispatch leg | the module-bearing FQ of the selected mangled entry (`m/Trait.method$Type`, `m/f$Int+Int`); storage module per §1.1.1 | the concrete-fn arm |
| Local variable / lambda parameter | `VarRef::Local { binder, binding_span }` — not table-resolved | the backend's scope stack; a binder absent from it is a producer breach and fails hard with the binder named |
| Slot-less polymorphic template referenced as a value | the template's storage key | `is_slotless_template_at` → the §7 loud backstop, never a silent leak |

**Producer chokepoints (typecheck).** Recording happens where resolution
happens (Principle 24) — never a second post-hoc pass:

- `record_reference_target` (`crates/cranelisp-typecheck/src/checker.rs`) for
  every `Var` reference — user fn, primitive, constructor, accessor, effect,
  extern, self-recursion and locals alike;
- `record_dispatch_target` (`crates/cranelisp-typecheck/src/program/callees.rs`)
  for dispatch selections at the `Apply` span;
- `instantiate_ctor` (`crates/cranelisp-typecheck/src/infer.rs`) for pattern
  constructors, and `dotted_member_identity` (`checker.rs`) for dotted
  `Type.member` spellings;
- the mono-instance writers (`crates/cranelisp-typecheck/src/traits/monomorphise.rs`)
  and the auto-curry / fn-value rewrite sites
  (`crates/cranelisp-typecheck/src/program/mono_collect.rs`).

**The carrier value-source rule (binding).** No carrier value is ever composed
from a written spelling. Every insert comes from exactly one of three sources:

1. **walk-resolved** — `Resolved.canonical`, the terminal storage identity the
   types-owned resolution walk surfaces (the only actor that knows it: a
   binding does not carry its own table key; see
   [interfaces — resolution](interfaces.md#resolution));
2. **mint-resolved** — the exact probe or registration key in hand at the seam
   (`instantiate_ctor`'s canonical-then-bare probe, `dotted_member_identity`'s
   `member_key` probe, a mono instance's registered mangle, the `ImplShell`'s
   `impl_module` plus mangle);
3. **transport** — copying an existing carrier entry to a new span (the
   auto-curry callee-span transport).

A new writer that builds `FQSymbol { module, symbol: <written name> }` is the
FIXME 0620 defect class reintroduced; `review` rejects it on sight.

### 1.1.1 Storage-module derivation for dispatch legs

Where each dispatch-selected entry lives (the placement facts; Decision 45 as
restated in [BC 7](bounded-contexts.md#7-cross-crate-types-cratescranelisp-types)
"Trait implementations split by placement"):

- **Trait-impl method bodies** live in the impl writer's module — the module
  whose source contains the `(impl …)` form. This is forced: the bodies compile
  in the writer's codegen batch, and `compile_to_module` requires every compiled
  definition's entry and GOT slot in the compiling module's own table. Only the
  discovery shell (`Decl::ImplShell`) lives in the trait's defining module, and
  the shell carries `impl_module`.
- **Mono instances** register in the caller's module. The mangled name embeds
  the defining home; the storage is the caller's table.
- **Multi-sig overload variants** register in the defining module.

The derivation rules, binding on the producer:

| Leg | Carrier module | Source at the seam |
|---|---|---|
| TraitMethod — call, deferred, value-position and auto-curry-inner | the impl writer's module | `impl_module` read off the `ImplShell` that proves impl existence, carried on `ResolvedCall::TraitMethod.impl_module`; downstream consumers read it, never re-derive |
| SigDispatch — every mono-minted and overload leg | the selected entry's storage module | the typed `CallableTarget` on `ResolvedCall::SigDispatch`, recorded at registration |
| AutoCurry — plain fn target | whatever the callee `Var` recorded | the callee's own `VarRef`, transported by callee span; a local target stays local. Never re-resolve the bare name at drain time |
| BuiltinFn | the chain-follow terminal (`primitives` fallback) | the resolution walk |

### 1.1.2 Terminal storage key for alias-resolved references

**Rule.** The resolution walk surfaces the terminal storage key and the
recorder records it (`Resolved.canonical`). The display identity (`Resolved.fq`,
the written spelling at the terminal home) is untouched: macro-head dispatch,
error attribution and every display surface keep it.

The rename surface of the language is exactly the `Import`/`Reexport` edge's
`source.symbol` — member aliases (a sum constructor or field accessor's bare
name is an alias of its `member_key` entry), renamed imports `[(foo bar)]`,
renamed re-exports and glob-member bare aliases. The walk threads the key
across every edge, so no second mechanism lets a written spelling diverge from
a storage key. Mangled names never pass through alias edges.

Rejected, and why: repointing the display identity at the terminal key (a
user-visible display regression riding a producer fix); reconstructing the key
per kind from the terminal binding (covers constructors only — nothing on a
terminal binding recovers a renamed import's original name — and is a second
resolution, which Principle 24 forbids).

Pins: `crates/cranelisp-types/src/resolve/tests.rs::unqualified_import_chain_returns_terminal_storage_key`
(types walk); the carrier cells in
`crates/cranelisp-typecheck/src/program/mono_collect/tests/carriers.rs`
(member-aliased constructor and accessor, renamed import).

### 1.1.3 Map provenance — the check-run pairing rule

A span-keyed sidecar has exactly three axes: **key values** (which spans are
recorded), **carrier values** (§1.1, §1.1.2) and **map instance** (which
`MethodResolutions` the view build reads). `MethodResolutions` has three
provenances: the live run map (accumulates across a module check run), the
per-instance swap (`recheck_body_for_mono`'s take/restore) and the finalize
accumulator.

**Rule (binding on every view-build site).** A codegen view is built from the
same `MethodResolutions` instance that the body-check run which annotated that
body populated — never from a map restored from, accumulated for, or belonging
to a different check run. The mechanism: `recheck_body_for_mono` re-checks the
full body with a fresh per-instance map live and `current_module` switched to
the defining home, so every carrier for that instance — variable references,
dispatch selections, the in-swap auto-curry drain and every constructor-pattern
span — is recorded in that map, resolved in the defining module's context.
`finalize_mono_codegen_view` (`crates/cranelisp-typecheck/src/traits/monomorphise.rs`)
and `register_test_fn_mono_roots` (`crates/cranelisp-typecheck/src/program/register.rs`)
build from the per-instance map they were handed back; `sweep_post_pass_outputs`
(`crates/cranelisp-typecheck/src/program/finalize.rs`) sweeps every sidecar
field, not a subset. Same-run paths (per-form strict and multi-sig views, the
shared strict-first/lenient-fallback builder, the finalize rebuild, trait-method
writeback) read the live or accumulated map their bodies were checked under;
synthetic bodies take no map (§4).

**Recorded latent hazard (evidence-gated, not scheduled).** `Span` is a bare
byte range with no file identity, so one run's shared maps can hold spans from
more than one file (default trait-method bodies carry the trait file's spans
into the impl writer's run; macro-expanded bodies may carry the macro
definition file's). A numerically equal span pair across files can
cross-attribute a carrier — always `Some(wrong)`, never `None`, so it cannot
trip the hard miss on a valid program. Structural cure if evidence surfaces:
per-body map scoping (the per-instance discipline generalised) or a source id
in `Span`.

### 1.2 No soft fallback — the reject criterion

A codegen site reads its carrier and hard-fails on a miss with a precise
`CodegenError` naming the reference and the missing carrier. There is no
keyed-read-else-resolve hybrid: it would mask producer gaps and reintroduce an
arbitrary-order scan as a shadow path
([Principle 08](principles/08-no-interim-implementations.md)). `review` rejects
any change-set containing a carrier-miss fallback to a name resolver. The
negative cells are `crates/cranelisp-backend/src/compiler/apply/keyed_miss_tests.rs`
(call seam) and
`crates/cranelisp-backend/src/compiler/control_flow/fn_as_value/keyed_miss_tests.rs`
(value seam); the pattern seam's two arms are unpinned — ACT-0968.

### 1.3 The backend reader

`CompileContext::entry_at(&FQSymbol) -> Option<(ModuleFullPath, Binding)>`
(`crates/cranelisp-backend/src/compiler/context.rs`) is the one keyed fetch: a
direct two-level map read (`symbol_tables.get(&fq.module)`, then the table by
`fq.symbol`) with no import-chain walk, no alias substitution, no global
fallback and no map iteration order. Every other read is a projection of it —
`ctor_meta_at`, `ctor_value_shape_at`, `is_callable_target_at`, `arity_at`,
`callee_summary_at`, `is_inline_primitive_at`, `got_entry_at`,
`is_slotless_template_at` — discriminating on the fetched binding's declaration
arm. A carrier miss or an entry miss is a hard `CodegenError`.

One deliberate non-keyed remainder: the int-hosted extern intrinsics (the trace
field accessors), which are not symbol-table entries. They keep the by-name
`Linkage::Import` lowering in `compile_extern_call` against a fixed catalog —
no scan and no precedence walk. The two remaining soft arms
(`constructor_metas`, `concrete_field_types`) and why neither is a resolver
are recorded in [backend design §2](../backend/backend.md#2-the-reading-discipline--a-pure-keyed-consumer).

### 1.4 Backend-synthesized names

- `compile_operator_as_value` (`crates/cranelisp-backend/src/compiler/literals.rs`)
  maps an operator to its `primitives` implementation
  (`operator_primitive_name`) — a fixed compile-time mapping into a static
  home — and performs a direct `got_entry_at` fetch with a hard miss. No
  carrier is needed and no resolver is involved.
- `crates/cranelisp-backend/src/compiler/resolution.rs` retains only name
  *composition*: `got_data_symbol_name` (a forward to the types-owned mint),
  `inner_fn_discriminator_for` and the closure/curry glue names. Composition
  is not resolution.

---

## 2. The type axis

The backend keys every type identity — heap classification, drop glue, schema
layout hash, trace descriptors, `lookup_type_def` — on an `FQTypeName` read off
the node's `ConcreteType::ADT` through the types-owned readers. No bare
type-name resolution exists. Constructor construction and reference position is
a symbol-axis kind (§1.1), and pattern position is
[constructor keys §10](dotted-ctor-canonical-keys.md#10-the-resolved-pattern-constructor-reaches-codegen).

---

## 3. The resolver-free backend — the gate and the reads outside it

**The grep gate.** Zero occurrences, as code, of
`resolve_driven`, `resolve_chain`, `resolve_got_target`,
`resolve_is_callable_target`, `resolve_vec_query_primitive`,
`resolve_callee_summary`, `resolve_platform_effect_target`,
`resolve_poll_effect_target`, `resolve_extern_target`, `resolve_func_arity`,
`lookup_constructor` and `lenient_mono_from_expr` under
`crates/cranelisp-backend/src/`; `resolution.rs` retains only the §1.4 naming
primitives. Remaining textual mentions are retirement comments. No test
executes this gate: it is re-run at review of backend changes, and its
falsifier is a resolver entry point or table scan reappearing. The retired
site labels S1–S24 still appear in source comments; the inventory they name is
in Git history.

**Keyed reads the grep cannot count.** A site that reads a carrier rather than
calling a resolver is invisible to the gate and is counted here deliberately:

| Site | Kind | Carrier / key |
|---|---|---|
| The TCO self-call gate — `is_self_call` (`crates/cranelisp-backend/src/compiler/fn_compiler.rs`), consumed by `compile_tail_self_call`, the stack-allocation gate and the spark classifier | self-call identity | the callee's `VarRef::Global` storage FQ compared, module and symbol, against `{ctx.current_module, current_fn_name}` |

Its predecessor decided self-call by bare written-name equality before
consulting the carrier and survived the S110 excision because it was neither a
`resolve_*` call nor a scan (FIXME 0652, S113). The bare-name match was
deleted, not demoted to a fallback (§1.2); a callee that is not a global falls
through to `compile_var_apply`, whose scope-stack check finds the shadow and
emits an indirect call. The second arm of `is_self_call` (the `SigDispatch`
mangled-name arm) is **truthfulness-conditional**: its soundness rests on the
producer never recording a self-`SigDispatch` for a shadowed call (Principle
24), not on the backend re-checking locals. Consumer discipline:
[backend design §2](../backend/backend.md#2-the-reading-discipline--a-pure-keyed-consumer).

---

## 4. View production — typecheck is the sole producer (W0.b)

- Typecheck builds the codegen view for every codegen-reached body and the
  backend compiles only present views: a codegen-reached entry without a view
  is a hard error. Both view builders live in `cranelisp-types` beside each
  other with the same required sidecar parameters
  (`MonoExpr::from_expr`, `MonoExpr::lenient_from_expr`).
- The lenient builder serves the entry classes that legitimately fail the
  strict builder on **types only**: constructor `Def` synthetic bodies,
  synthesised field accessors, `f$Var` multi-sig variants, generic templates
  reached by direct compile, REPL `__expr` bodies and non-concretized
  macro-clause bodies. Resolution verdicts are total in both builders; a
  real-span miss in the lenient walk is an always-on seam assertion, never a
  manufactured local. The CLIF byte-identity gate for these classes is
  `tests/golden_clif_w0b.rs` over `tests/fixtures/clif_w0b/`.
- **Synthetic bodies get their carriers directly.** Every synthesised node is
  `Span::SYNTHETIC`, so a span-keyed sidecar structurally cannot address them.
  Synthesis holds the identities: accessor bodies take
  `MonoExpr::synthetic_local_from_expr` and their single pattern arm's
  `resolved_ctor` is the just-registered canonical constructor key;
  constructor bodies are `ConstrADT` and reference nothing.
- **Standing invariant, asserted with a named falsifier.** No producer writes
  `var_refs` or `apply_refs` at `Span::SYNTHETIC`, and no real check-run body
  carries a synthetic-span table reference. Both builders classify a
  synthetic-span miss as local, so a synthetic-span table reference in a real
  body would be silently localised rather than refused — that observation is
  the falsifier. Synthetic nodes do occur inside real bodies
  (`crates/cranelisp-typecheck/src/builtins.rs`,
  `crates/cranelisp-typecheck/src/program/finalize.rs` and
  `crates/cranelisp-typecheck/src/program/mono_collect.rs`); every known
  population is a compiler-synthesised local or wrapper. The check is a read
  of those synthesis sites and of the two map writers
  (`record_reference_target` in `crates/cranelisp-typecheck/src/checker.rs`,
  `record_dispatch_target` in `crates/cranelisp-typecheck/src/program/callees.rs`)
  at review of a change to either; no test executes it.
- **Open: staged retirement of the lenient builder** (S119 ruling; FIXME 0931;
  [concrete boundary type](concrete-boundary-type.md)). Its
  `unwrap_or(ConcreteType::Int)` placeholder is a fabrication site the
  concreteness programme closes; the end state is `from_expr` as the sole
  builder, gated on the lenient-fallback census reading zero. Register row R18
  in [safety invariants](safety-invariants.md) carries the grade.
- Delivery shape, for the citations that name it: W0 landed the carriers
  (`CACHE_SCHEMA_VERSION` 18→19) and this totalization; W1 flipped the call
  seam (`apply.rs`); W2 the value seam (`literals.rs`, `fn_as_value.rs` — the
  former sites S10–S18) with the §7 guard; W3 deleted the resolver family. The
  S114 carrier reshape rode schema window 21→22.

---

## 5. Why the view is a typecheck product

The findings that decided it:

1. The lenient class is not self-contained. It spans generic templates, `__expr`
   and macro-clause bodies — the full reference-kind spectrum — so a
   "same-module scoped helper" for it would have to grow qualified and import
   handling and become a resolver through the back door. Rejected on that
   ground.
2. Synthetic bodies collide on one span, so threading a span map through a
   backend builder is unavailable for them.
3. `compile_to_module` runs only downstream of a live typecheck (no re-codegen
   on a cache hit), so typecheck always has the resolutions in hand when a view
   is built. `crates/cranelisp-backend/src/test_support.rs::compile_defns_in_module`
   has no live caller: it is a unit-fixture harness.

Ruling: the view is a typecheck product (Principle 24 — derived at one stage,
crossing the boundary as resolved data), and the transport problem dissolves
because the carriers ride the persisted view. Pins: the totalization and
accessor-arm cells in
`crates/cranelisp-typecheck/src/program/mono_collect/tests/carriers.rs`; the
lenient-class goldens in `tests/golden_clif_w0b.rs`.

---

## 6. The ADT-entry builder

`cranelisp_types::build_adt_entries` is the single derivation of the ADT
registration entry set, consumed by both writers —
`crates/cranelisp-typecheck/src/adt.rs` (user `deftype`) and
`src/bootstrap.rs::register_synth_adt` (synthetic seeds). Contract:
[interfaces — ADT recipes](interfaces.md#adt-recipes--adtctorspec--build_adt_entries).

---

## 7. The value-position guard

Three legs, all landed:

1. **One enumeration.** Minting a mono instance for a parametric fn value and
   the ambiguity check share `for_each_child_expr`
   (`crates/cranelisp-typecheck/src/program/support.rs`); there is no
   per-position whitelist (BC 2 invariant 13).
2. **The loud backstop is the keyed read.** A value-position `Var` whose
   fetched binding is a slot-less polymorphic template (`is_slotless_template_at`)
   hard-fails with a precise `CodegenError` ("generic value reference …
   reached codegen without a mono instance"), release builds included. A new
   value position cannot leak silently: it either flows through the shared
   walk and is minted, or dies loudly at the keyed read.
3. **Evidence.** The value-position keyed-miss cells in
   `crates/cranelisp-backend/src/compiler/control_flow/fn_as_value/keyed_miss_tests.rs`.

---

## 8. The landed carrier surface

Exact promises live in rustdoc; this is the inventory a schema reader needs.

- `cranelisp-types`: `MethodResolutions.{pattern_ctors, var_refs, apply_refs}`
  (`check.rs`); `MonoExpr::Var.resolution: VarRef`,
  `MonoExpr::Apply.dispatch: ApplyRef`, `MonoMatchArm.resolved_ctor`
  (`mono_expr.rs`); `MonoExpr::{from_expr, lenient_from_expr,
  synthetic_local_from_expr}`; `ResolvedCall::TraitMethod.impl_module` and
  `ImplShell.impl_module` (both required, no serde default);
  `Resolved.canonical` on the resolution walk.
- `cranelisp-backend`: the `CompileContext` reader of §1.3; the unit harness
  populates fixture sidecars itself.
- Cache: the S110 carriers rode `CACHE_SCHEMA_VERSION` 18→19; the S114 reshape
  rode 21→22; the current value is `pub const CACHE_SCHEMA_VERSION` in
  `crates/cranelisp-backend/src/cache/mod.rs`. The carriers are serde-visible
  on the persisted `codegen_view`, so a change to their population or shape is
  a schema change.
