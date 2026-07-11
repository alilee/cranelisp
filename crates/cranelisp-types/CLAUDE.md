# cranelisp-types — local conventions

The voice of the code: contract gotchas that bite consumers of the cross-crate
substrate. Owned by `/arch`; other skills file FIXME `target: /arch` for shape
changes. Design narrative: `design/arch/interfaces.md` + `bounded-contexts.md`
§7 — this file records only what rustdoc doesn't say.

## The serde shape IS the cache contract

`SymbolTable`/`ModuleEntry` serialize into the backend's `.meta.json` sidecars.
**Any serde-visible change — field add/delete/retype, OR a meaning change to
what an existing field records — bumps `CACHE_SCHEMA_VERSION` in
`crates/cranelisp-backend/src/cache/mod.rs` (currently 16) in the SAME
change-set.** The constant lives in the backend, not here — an edit here is
incomplete without the cross-crate bump (precedents: `codegen_view` 7→8, S101
`callees` widening 10→11, S102 ownership carriers 11→12). Only exempt class: a
`#[serde(default)]` addition whose default equals the fresh-build value
(`SymbolTable.schema_version` rustdoc, `module.rs:218`).

- `#[serde(skip)]` runtime fields: `got`, `linker`, `Def.code`. Caches
  deserialize as `SymbolTable<(), ()>`; int rehydrates via `into_concrete`
  (`module.rs:503`) — every `code` becomes `None`.
- The `#[serde(bound = "")]` on `SymbolTable` and `ModuleEntry` derives is
  load-bearing: without it the derive demands `C: Serialize` even for skipped
  fields and the `()` default stops compiling (`module.rs:88–99`).
- **`GotTable::clone()` returns a fresh, all-null table** (`got.rs:167`) —
  deliberate, matching `#[serde(default)]`. Sharing happens only through the
  `Arc` on `SymbolTable.got`. Cloning a `GotTable` never copies pointers.

## Callability is structural — read through the accessors

The GOT slot rides the callable `DefKind` variants, not a flat `Def` field
(S83, FIXME 0356/0357, Principle 20). Use the read-throughs, never re-pattern
the kind set:

- `ModuleEntry::callable_got_slot()` (`module.rs:1318`) — the ONE callable-address
  read. `PrimitiveBody::Inline` answers `None` by construction (S102, FIXME 0476).
- `ModuleEntry::is_callable_target()` (`module.rs:1354`) — the resolution
  STOP condition; covers slot-less inline primitives. A
  `callable_got_slot().is_some()` probe at a resolution seam reopens the 0476
  shadowing hole.
- `SymbolTable::defined_symbols()` (`module.rs:676`) — the codegen-compilable
  filter (Decision 22): `ast.is_some()` AND kind not `Overloaded` /
  `Constrained`/`Polymorphic` (templates are mono SOURCES; emitting a
  `Polymorphic` body was the FIXME-0381 317× backstop fire).
- `mode_summary()` / `set_mode_summary()` (`module.rs:1377/1399`) — the summary
  rides where the slot rides; `set_` returns `false` for non-carrying kinds.
- `DefKind::PlatformEffect.poll_shape` polarity is INVERTED from the C-ABI
  `blocking` so the serde default (`false`) = blocking — a cached pre-S94
  entry deserializes as blocking (`module.rs:1691`).

## Fields populated by convention, not construction

`DefBuilder` has NO setter for `callees`, `value_use`, or `code` (table at
`module.rs:1465`): typecheck writes `callees` (the S101 transaction reverse
index starves silently if a body-check seam skips the harvest — completeness
contract in `crates/cranelisp-typecheck/CLAUDE.md`), typecheck's ownership
pass writes `value_use`, backend writes `code`.

Fields that LOOK optional but are contractually required downstream:

- `Def.codegen_view: Option<MonoDefnVariant>` — `None` at a codegen-reached
  concrete entry trips the backend's single located `expect`. Population is
  best-effort for ordinary concrete defns, hard-error for mono instances;
  ctor/accessor entries and `f$Var` multi-sig variants are legitimately
  `None` (typecheck CLAUDE.md §codegen_view — do not "fix" the asymmetry).
- `Expr.inferred_type: Option<Box<Type>>` — `None` past typecheck is not a
  soft state: `MonoExpr::from_expr` fails it as `NotConcrete::Var(0)`
  (`mono_expr.rs:451`), the unified ambiguity error.
- `ModeSummary` vectors — **never index directly**; `param_mode(i)` /
  `param_flow(i)`/`spark_op(i)` are the ONE home for ⊤-on-absence
  (missing/short ⇒ Owned/Retained/true, `ownership.rs:167`). ABI comparison
  only via `abi_eq`/`abi_eq_opt` (`None` ≡ all-conservative).
  `ownership_analysis_off()` is read-once (OnceLock — one polarity per
  process) and flips a backend cache global key.

## Resolution primitive (`resolve.rs`) traps

- `split_qualified`/`canonical_symbol` require BOTH `/`-parts non-empty:
  bare `/`, `//`, `foo/`, `/bar` are literal names (Principle 16, FIXME
  0328/0331). A `/`-named operator mis-resolving means a guard was lost —
  fix HERE, never with a checker-side literal-lookup shortcut.
- `resolve_with_fallback` retries prelude only on the not-found error class;
  `PrivateInaccessible`/`QualifiedModuleUnknown` return as-is. The prelude
  terminal passes a PUBLIC-only filter; a private prelude hit reports as the
  ORIGINAL current-module not-found (`resolve.rs:356–392`).
- The bare primitive's generic miss is `TypeNotFound`-shaped regardless of
  kind (`not_found`, `resolve.rs:709`) — never infer entry kind from the
  error variant.

## Soundness-coupled single-source predicates

- `value_layout` (`heap.rs:131`) — the Copy/value-flattening verdict BOTH
  typecheck's `Copy` classifier and backend's `HeapCategory::Value` arm must
  delegate to; divergence is a UAF. Single-field-only is soundness, not a
  size bound (Wave-3a blockers, `heap.rs:221–244`); bumping
  `VALUE_LAYOUT_MAX_WORDS` is a cache-schema-bump event. The walk drops its
  DashMap guard before recursing — two Refs in one shard deadlock (`heap.rs:207`).
- `type_ctor_names` (`heap.rs:269`) — the ONE `TypeDef`-vs-product-ctor-facet
  reader (FIXME 0528 mirror cure); backend heap classifiers delegate here.
- `Type::is_concrete()` (`types.rs:92`) — the GOT-slot eligibility gate,
  strictly stronger than "no constraints" (constraint-emptiness gating was the
  S84 `(Box a)`-through-HOF SIGSEGV); `TyConApp` counts as non-concrete.
- `render_type` (`types.rs:149`) — the single `Type`→string walk (S87, FIXME
  0420); new variants edit one walk, not five renderers. `apply` carries a
  direct self-map cycle guard (`types.rs:295`, FIXME 0279/0295) —
  debug-asserts, treats the var as unbound in release.

## Known asymmetries a reader would misread as bugs

- `Pattern::Constructor.name: SymbolRef` — the parser does NOT split
  qualified names: `(option/Some x)` lands verbatim as
  `{ module: None, name: "option/Some" }`; the split is a pending lift, the
  `SymbolRef` slot its destination (`ast.rs:87–98`). The resolved FQ lives in
  the `MethodResolutions.pattern_ctors` span-keyed sidecar, not on the AST.
- `PlatformSpec.name` is still bare `String` (`module.rs:2348`) — the
  `ModuleName` narrow is a recorded target (S69 Submission 21), not landed.
- `MethodResolutions` derives `Serialize` but is NOT serde_json-safe
  (`Span`-keyed maps; non-string keys). Fine for the binary cache; never
  JSON it (S106 latent note).
- The marshal tags' ctor-order truth is
  `cranelisp-typecheck::builtins::register_macros_module` — unassertable from
  this crate (dependency direction); `marshal/tests.rs` guards only the
  constants themselves.
- `unsafe impl Send/Sync for ModuleEntry` (`module.rs:1151`) is informational
  — safety delegates to `C: CodeStore`'s own bounds.

## Public-surface mechanics

Submodules are `pub(crate)`; the crate-root re-export list in `lib.rs` is the
sole surface. Any surface change regenerates `public-api.txt` (canonical
command: `design/arch/CLAUDE.md` §Baseline-diff) WITHOUT `--features
test-support` — that gate keeps `test_support` (Tier-2 builder, consumed by
typecheck's unit suite via the Cargo feature) off the frozen edge.
`#[non_exhaustive]` is policy on every pub struct/enum EXCEPT: string
newtypes, `View` (private fields), and the `#[repr(C)]`/`#[repr(u32)]` ABI
types (`SchedulingClass`, `ConcurrencyDescriptor`, `Poll`, `HeapHeader`) —
layout contracts governed by `cranelisp_platform::ABI_VERSION` bumps
(Principle 14), offsets pinned by const asserts (`heap.rs:35`) and layout
tests (`scheduling.rs:445`).

## Seam map + `#[cfg(test)]` locations

One module per concern, tests as `{module}/tests.rs` siblings: `module`
(SymbolTable/ModuleEntry/DefKind/chain-follow), `resolve`, `newtype`, `types`,
`concrete`, `mono_expr`, `check`, `got`, `heap` (at
`heap/value_layout_tests.rs`), `ownership`, `error`, `marshal`. Inline
`#[cfg(test)] mod tests`: `view.rs`, `scheduling.rs`, `macro_expander.rs`,
`test_support.rs`. NO test modules in `ast.rs`, `sexp.rs`, `span.rs`,
`parsed.rs`, `pipeline.rs` — pinned by consumer-crate suites, not locally.
