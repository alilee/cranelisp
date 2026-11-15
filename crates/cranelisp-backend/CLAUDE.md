# cranelisp-backend — local conventions

The voice of the code: API gotchas, codegen/heap/RC invariants, cache discipline,
and debug hooks for Cranelift emission, JIT lifecycle, and object caching. Owned
by `/dev` when narrow-deployed to this crate.

## Cranelift version + the byte-identical-CLIF invariant

Pinned to **Cranelift 0.116** across `cranelift`, `-module`, `-jit`, `-native`,
`-codegen` (with `disas`), `-object` (`Cargo.toml`); `target-lexicon 0.12`,
`object 0.36` are `/arch`-blessed direct deps already transitive via cranelift's
`disas`. This is the ONLY crate that names Cranelift types — everything upstream
flows in through `cranelisp-types` (`crates/cranelisp-backend/src/lib.rs` rustdoc).

**Mode is the `Module` instance, never a parameter.** `compile_to_module` is
generic over `M: Module + CodeFinalizer` and emits **byte-identical CLIF**
whether `M` is `JITModule` or `ObjectModule` (crate-root rustdoc, "The codegen
boundary"). Any
env-gated codegen change (RC gates below) is written to be *byte-identical when
the gate is off* — that phrase in a gate's rustdoc is a load-bearing contract,
not a comment. There is no object-compile entry point; the object path is
`compile_to_module::<ObjectModule>` + caller-side `finish().emit()`.

## Forbidden pattern — no trait knowledge, one dispatch path

Every primitive — including `not`, `+`, `=`, arithmetic/comparison — goes
through the SAME GOT-indirect dispatch as any user fn (`compiler/mod.rs`
rustdoc). `primitives_inline::try_emit_inline_primitive` is a **name-keyed
opportunistic optimisation consulted before that fallback**, NOT a parallel
dispatch: it keys on `Symbol` only, never `(trait, method, type)` triples
(Decision 43). The GOT slot for every primitive is always populated, so
call-by-symbol (`(let [f not] (f true))`) works whether or not the site is in
the 30-name inline table. Removing an inline entry is a code-size/dispatch-cost
regression, never a correctness one. Backend has NO trait knowledge at all.

## Heap layout — `heap.rs` is the sole layout importer

`heap.rs` is the ONLY file that imports the cross-crate layout constants
(`HeapHeader`/`HeapAdt`/`HeapClosure` from `cranelisp-types`); all other codegen
calls its `heap_load`/`heap_store`/`emit_rc_*` helpers (confinement per
`src/CLAUDE.md` §"Heap Access"). Offsets are pinned by `const _: () = assert!(…)`
static checks: `HeapAdt::TAG_OFFSET==16`, `FIELDS_START==24`;
`HeapClosure::{CODE_PTR==16, DROP_GLUE_PTR==24}`; `HeapVec::{LEN==16, CAP==24,
DATA_PTR==32}`. **Nullary ADT constructors are NOT heap-allocated** — they are
bare i64 tags (`HeapAdt` rustdoc, `NULLARY_TAG_THRESHOLD`); a reader expecting a
header on every ctor value will misread this as a missing allocation. RC lives at
`HeapHeader::RC_OFFSET`; `emit_rc_inc/dec` emit `atomic_rmw(Add/Sub, ptr+RC_OFFSET)`.

## GOT slab — fixed 1024 slots, fallible allocation (S101 item d, got_slab_tests.rs)

`GotTable` is a FIXED `GOT_TABLE_SIZE`(=1024)-slot `Box<[AtomicPtr<u8>; 1024]>`
allocated once and NEVER reallocated; `base_ptr()` is structurally stable for the
session (finalized machine code bakes the base via `__cranelisp_got_{M}`
resolution, so movement would dangle it — verified by `got_slab_tests.rs`, the
backend-side slab-invariant home rehomed from the deleted `got.rs` re-export
shim, S111 R4 §1.2). `GotTable`/`GOT_TABLE_SIZE`/`NULLARY_TAG_THRESHOLD` are
imported from `cranelisp-types` directly (the `got.rs`/`codegen_types.rs`
convenience-re-export shims were deleted S111 R4 §1.2).
"Growth" is only the monotone `SymbolTable::next_got_slot` index. The hard bound
is EXHAUSTION, not movement; long dev sessions with many ABI-changing
redefinitions (fresh-slot churn) approach it faster. **S111 R7 closed the
release-UB hole:** `allocate_got_slot` is now the fallible seam
(`Result<usize, GotExhausted>`, refuses at the bound, no bump on failure — a
diagnosed compile error at every allocation path, mapped into `CheckError`
typecheck-side / `CranelispError::CodegenError` int-side); `store_slot`/`load_slot`
promoted `debug_assert!` → always-on `assert!` (an in-process OOB index is a
compiler-invariant breach → located hard-fail, never release UB). The ONE
untrusted GOT-index source — a cache-deserialised `got_slot` — is validated at
the cache-load seam (`serialize.rs::deserialise_meta_with_build_id`, per-entry
`callable_got_slot() < GOT_TABLE_SIZE`) and turned into `CacheStale::GotSlotOutOfRange`
→ recompile, never a panic on disk content.

## Cache — schema-bump discipline (cache/mod.rs)

Five invariants (cache/mod.rs rustdoc): `Linker` is the only mmap-holder (per-symbol
retention via `Arc<Linker>`); `CacheManifest` is the single index (sidecar⇔object
pair-invariant); validity checked at every hit (stale ⇒ recompile, never
use-stale); **no re-codegen on cache-hit** (the `.o` bytes are authoritative);
`CACHE_FORMAT_VERSION` (manifest shape) and `CACHE_SCHEMA_VERSION` (sidecar
`SymbolTable` shape) are independent. **Any serde-shape change to the persisted
`SymbolTable` MUST bump `CACHE_SCHEMA_VERSION`** (read the constant in
`cache/mod.rs` for the current value — a literal here goes stale, and did) in
the same change-set — this includes upstream `cranelisp-types` changes to what
`Def` records (e.g. the S101 `callees` edge set). `BUILD_ID = env!("CRANELISP_BUILD_ID")`
is stamped by `build.rs`; a mismatch on disk ⇒ `CacheStale::BuildIdMismatch` ⇒
fresh build (so uncommitted codegen edits never read a stale cache).

## Codegen env gates — byte-identical-off, read ONCE into a `OnceLock`

All are codegen-time (zero runtime cost) and default OFF ⇒ byte-identical codegen.
Each memoizes into a process-global `OnceLock`/`LazyLock` so a whole run is
consistent. Provenance in each gate's rustdoc.

| Env var | Effect | Location |
|---|---|---|
| `CRANELISP_NONATOMIC_RC` | plain load/store RC instead of `atomic_rmw`. **UNSOUND above one worker**, isolation-only, excluded from `nextest`, MUST NEVER ship | `heap.rs` (S99) |
| `CRANELISP_RC_STATS` | emit `runtime/rc_stat_{inc,dec}` tally calls; printed at exit | `heap.rs`/`rc_site_stats.rs` (S99) |
| `CRANELISP_RC_DEC_CHECK` | emit `runtime/rc_dec_check(ptr)` before each inline dec | `heap.rs` (FIXME 0494) |
| `CRANELISP_NO_STACK_ALLOC` | force heap (disable escape∧unique stack-slot placement) | `compiler/fn_compiler.rs` (S105 N4) |
| `CRANELISP_NO_OWNERSHIP` | moves off: the ownership plan duplicates every use (U1's uniform reference), and stack placement reads no facts; **flips a cache global key** | via `cranelisp_types::ownership_analysis_off()`, `compiler/ownership_plan.rs`, `cache/manifest.rs` |
| `CRANELISP_NO_LENIENT` / `CRANELISP_SPARK_ADMIT` / `CRANELISP_SPARK_DENSITY_MAX` / `CRANELISP_SPARK_STATS` | lenient-eval spark admission tuning + tally | `compiler/control_flow/sparkability.rs`, `utilization.rs` |

**`CRANELISP_CODEGEN_DUMP`** dumps CLIF to stderr per symbol. Filter grammar
(`crates/cranelisp-backend/src/lib.rs::clif_dump_matches`, pure + unit-tested): `*` = all; `module::symbol`
= exact pair; bare string = exact module match. This is the codegen-layer
inspection hook (the S66/CLAUDE-cited `CRANELISP_CODEGEN_TRACE` role); pairs with
REPL `/clif <name>` and `/disasm` (`produce_disasm`, on-demand — disassembly is
NOT in the always-created `CompilationArtifacts`).

## Binder identity — ONE SLOT PER BINDER, never per name (S121)

`compiler/scope_chain.rs` owns lexical name resolution and binder storage; see
`design/backend/binding-scope.md` for the model. Its frames are ordered
`BinderSlot`s, so scope exit is `frames.pop()` and releases nothing. Ownership
is keyed by the plan's `BinderId`, never by a name (next section).

The seams that matter on a future edit:

- `bind_local` publishes the value and optional type only after its initializer;
  `fresh_variable` is private, with `bind_local` and `bind_capture` its only
  callers.
- Captures belong to function-lifetime `CaptureEnv`, resolved after the chain;
  a local shadow cannot release a capture.
- `Option<Type>` preserves an intentional unrecorded type. Do not invent a
  scalar type merely to make a slot uniform.
- Lenient binding state is positional (`sparkability::binder_before`), not
  name-keyed.

`closure_drop_glue` and `pending_closure_drop_glue` are retired: canonical
type-directed release does not consume per-binding glue IDs.

## Uniform counting — the ownership plan is the only decider (S123)

`compiler/ownership_plan.rs` implements `design/backend/uniform-counting.md`.
Every expression compiles to an OWNED value its receiver consumes.

- `OwnershipPlan::build` is the only producer of move, duplicate and drop
  decisions: per variable occurrence (`Occurrence`), per binder dead at its
  introduction, per `if`/`match` branch entry, per closure creation
  (`CaptureEntry`), and, moves off, per consumer (`post_drops`).
- Emission must not decide a count. `FnCompiler::{compile_occurrence,
  bind_binder, bind_field_binder, emit_entry_drops, emit_post_drops,
  capture_value}` read the plan; nothing is released at scope exit or before a
  tail jump.
- Operand order has one definition, `ownership_plan::operand_sequence`, read by
  the plan, `check_linearity`, `consumed_within` and the emitter's one operand
  evaluator, `FnCompiler::compile_operands`. A lowering of an application, Vec
  literal, constructor, `par-bind` or launch receives its operands as values
  from `compile_operands` and never evaluates an operand expression itself.
  `callee_is_evaluated` is the one shared predicate for callee evaluation, and
  the TCO path declines a callee the plan evaluates. The U-15 e2e cells
  (`tests/uniform_counting.rs`) are the measure; their detection proof is
  reversing only the evaluator's iteration.
- A planned variable occurrence is counted at its binder's recorded type
  (`FnCompiler::counted_type`), so a scrutinee release and a drop of its binder
  classify alike: synthetic bodies carry `Int` placeholder node types.
- Generated wrappers (function-as-value, trait-method-as-value, auto-curry)
  have no plan: each builds its one call's arguments with
  `fn_as_value::forwarding_template_args`, the only RC emission in a wrapper
  body (`uniform-counting.md` §3.3).
- `FnCompiler::plan_body` runs `check_linearity` in debug builds before any
  emission; its detection proof is `ownership_plan/tests.rs`.
- A lenient spark thunk is a clone the plan never saw: its captures all
  duplicate (`duplicating_captures`), and the frame drops
  `OwnershipPlan::consumed_within` at the forcing point, so both create-gate
  arms consume the same references.
- Copy-on-write builtins always own their source (rule U2): the runtime
  `rc == 1` probe picks the in-place or copy arm (`vec_codegen::OwnedSource`).
  `OwnedSource::elem_release` is the one element-release source: the copy
  arm's teardown callback and the in-place `vec-set` arm's release of the
  overwritten element.
- `rc_ownership_fence_tests.rs` fences bare `MonoExpr` kind tests in the
  counting files.

## Submodule seam map + test-module locations

Codegen lives in `impl FnCompiler` blocks across `compiler/` submodules, re-exported
through hub files (`compiler/mod.rs`, `compiler/control_flow.rs`) so in-crate
`crate::compiler::*` / `super::*` paths keep resolving — the hub is the single
resolution point (S87 W5b decomposition). `CompileContext` is the ONLY
pub-to-boundary item under `compiler::`; everything else is `pub(crate)`.

- `compiler/apply.rs` — call-site dispatch (direct/GOT/extern/platform/poll).
- `compiler/{fn_compiler,context,resolution,extern_call,rc_emission,literals,match_codegen,trace_codegen,vec_codegen}.rs`
  — per-concern codegen. **S110 W3 (`backend-keyed-consumer.md`): the backend is a
  pure keyed-lookup consumer** — it reads typecheck's per-reference
  `resolved_target` storage key and does ONE direct keyed fetch
  (`CompileContext::entry_at` / `ctor_meta_at` / `got_entry_at` in `context.rs`),
  kind-discriminating on the fetched entry and hard-erroring on a carrier/entry
  miss (Principle 24 "Resolve once"; Rev-2 no-soft-fallback). The `resolve_*`
  resolver family (`resolve_driven` + the arbitrary-order `symbol_tables.iter()`
  global scan + the ten `resolve_*` entry points + `lookup_constructor`) is
  DELETED; `resolution.rs` now holds ONLY fixed name-composition schemes (no
  scan/precedence walk): the two symbol-naming primitives (`got_data_symbol_name`
  / `inner_fn_discriminator_for`) plus the two capture-glue naming fns
  (`closure_drop_glue_name` / `curry_drop_glue_name` — the S111 R6 §4.1 ONE
  naming-identity home, never re-composed inline). These name capture
  ENVELOPES, not type glue: **type-glue identity is `cranelisp_types::
  drop_glue_symbol_name` and nothing else** (S118 W3 §8 deleted
  `adt_drop_glue_name` / `adt_instantiation_mangle` / `escape_symbol`, the
  backend-local second identity scheme).
  Grep gate: zero `resolve_driven`/`resolve_*_target` in `compiler/`.
- `compiler/scope_chain.rs` — the binding environment above (`ScopeChain`,
  `BinderSlot`, `CaptureEnv`, `resolve_binding`); tests in
  `compiler/scope_chain/tests.rs`.
- `compiler/control_flow/` — `let_if`, `par_bind`, `lambda`, `fn_as_value`,
  `free_vars`, `sparkability`, `capture_rc`, `select`, `launch`, `utilization`.
  Publication-order evidence: `control_flow/let_if/binder_publication_tests.rs`;
  the positional-spark matrix lives in `control_flow/sparkability_tests.rs`.
- `heap.rs`, `jit.rs`, `got_observer.rs`, `schema.rs`, `exe.rs`,
  `code.rs`, `primitives_inline.rs`, `cache/{manifest,serialize,object,linker,mod}.rs`.

**`#[cfg(test)]` modules are per-submodule siblings** (S101 coverage-audit reorg:
the flat 5,861-line crate-root `tests.rs` was split into 14 siblings; the split
serves the METHOD §2.2 submodule×scenario-class accounting). Convention:
`{module}/tests.rs` next to `{module}.rs` (e.g. `cache/linker/tests.rs`,
`compiler/resolution/tests.rs`, `heap/tests.rs`, `jit/tests.rs`), plus topical
`_tests.rs` siblings for a specific behaviour (e.g.
`compiler/apply/dispatch_tests.rs`, `compiler/vec_codegen/index_guard_tests.rs`,
`compiler/context/ctor_value_shape_tests.rs`,
`compiler/control_flow/{par,poll,select}_codegen_tests.rs`). Crate-root exceptions:
`module_assembly_tests.rs`, `clif_dump_tests.rs`, `got_slab_tests.rs`. When
adding a codegen behaviour, add its test sibling next to the submodule — don't
grow a crate-root file. `test_support.rs` provides the shared AST-fragment
compile harness.

**The CLIF-probe / execution test seam is the PRODUCTION per-body function**
(`test_support::probe_defn_clif` for a single defn's CLIF text;
`compile_defns_in_module` for the multi-defn / execution-tier no-finalize
variant; `try_compile_defns_in_module` — the fallible core both delegate to —
when the probe must READ a codegen refusal rather than panic on it). All ride
`compile_defn_in_module` — the EXACT Step-3 call
`compile_to_module_impl` makes. Note that a probe whose behaviour depends on a
heap-typed parameter must spell that type in the symbol-table entry's
`Scheme.ty` (`insert_user_fn_stub_typed`, not the all-`Int`
`insert_user_fn_stub`) — `defn_param_types` reads it from there, and an
`Int`-stamped `String` param is never heap-classified, so every RC gate silently
sits out. **The `Jit::compile_defn`/`compile_defn_with_targets`/
`build_compile_context`/`CompileArtifacts` test front door was DELETED (S111 R4
§1.3)** — do NOT re-introduce a parallel context-assembly; a new probe seeds its
aux entries into the `symbol_tables` it also builds and calls the helper. The
`compile_to_module_impl` body is 5 phase helpers (S111 R5 §3.1:
`collect_compile_targets` / `declare_module_functions` / `compile_module_bodies` /
`emit_module_got_data` / `write_finalized_got_slots`); `compile_resolved_call`
(`apply.rs`) is one method per `ResolvedCall` variant (S111 R5 §2). Drop-glue for
the two span-keyed mirrors (closure + auto-curry) shares ONE envelope
(`emit_capture_dec_glue`, `lambda.rs`) owning idempotency + declare/build/define;
type glue, including ADT glue, is built by `DropGlueRegistry` (below).

## Canonical drop glue — ONE named body per concrete owning type (S118 W3)

`drop_glue.rs::DropGlueRegistry` is the sole construction authority for release
code. It is **module-borrow-free state** (`module_path`, `dealloc_id`,
`vec_drop_id`, `entries`): `module` and `symbol_tables` are call arguments, and
that is not a style choice — `FnCompiler` already holds `module: &'a mut M`, so
a registry that held one could never be reached from body compilation. It is
that borrow conflict, not scope, that left the S116 foundation with zero
consumers. The access pattern is a **disjoint three-field borrow**:

```rust
self.glue.request_if_owning(self.module, self.ctx.symbol_tables, concrete)?
```

`FnCompiler::glue` is threaded into every inner compiler (lambda, par-bind and
launch continuations, dependent spark) so a nested body mints the SAME body as
the outer one. Construction is declaration-first — the entry goes in
`Defining` before the fields are walked — so recursive and mutually recursive
type graphs close through already-declared `FuncId`s and the compiler walks a
finite graph of type nodes while the generated code recurses over the runtime
value graph. **There is no depth bound anywhere in the release path**, and
`finish()` fences that every entry reached `Defined` (it runs after
`compile_module_bodies` and before `finalize_for_code_read`, so
`project_drop_glues` still sees finalized addresses).

Gotchas the next reader will hit:

- `compile_to_module` proactively requests glue for each body result through
  `ConcreteType::result_root()`. That is the one-hop `IO a -> a` projection;
  backend code must not restate the `primitives/IO` shape or normalize again.
- **A glue body is built mid-body**, in a fresh `make_context()` while the
  enclosing `FunctionBuilder` is live. That is safe and long-precedented
  (`lambda.rs::emit_capture_dec_glue`), but it means request order — and so
  emission order — varies with compilation input. Identity is the type and
  nothing else; anything order-dependent is a defect.
- **Two shapes never reach `emit_outer_drop`.** `Vec` goes through
  `vec_codegen::emit_vec_rc_dec_with_drop` (the rc gate; `runtime/vec_drop` is
  an unconditional teardown and calling it directly frees a shared Vec), and
  `Closure` delegates to `rc_emission::emit_closure_dec_into`. Both are
  `unreachable!()` in that match arm on purpose.
- **Field discharge happens ONLY in the `old_rc == 1` branch.** Every shape.
- Capture-env bodies build in their own context and cannot reach the registry,
  so the enclosing compiler requests their glue FIRST
  (`request_capture_glue`) and the body emits the resolved call.
- **Non-concrete release is governed by
  `design/backend/non-concrete-release-contract.md`** (the five faces, §7.4,
  §8 reject list); `transitive-drop-glue.md` §4.1 is only the superseded S118 record. A
  residual-parameter constructor is a slotless `Life::Template`, so its frame
  never reaches codegen in production (I-CT′).
- **The non-concrete arm in `FnCompiler::emit_release` is keyed on the TYPE, not
  the frame — knowingly** (FIXME 0903). A codegen target is a `Life::Concrete`
  body whose slot exists only for a concrete scheme, so no frame's parameter is
  residual-typed. A residual type reaches the arm from inside a body instead:
  `CtorMeta` field types come from the constructor declaration's scheme, so a
  generic product's field reads as a `Type::Var` (non-concrete release contract
  §7.4). The S119 families — synthetic field accessors of a generic product and
  generic trait-method instances — are producer obligations; on the S123 U′
  build `qa` found no program that reaches the arm. A frame key was measured at
  **+16 hard codegen refusals over the `spec_*` corpus** — do not re-run the
  narrowing on its own; the contract §2.6 and §8 record it.

## RC-emission gates that are ONE predicate, not per-site syntax (S115 W3/W4c)

Each row is a single pure predicate its sites call instead of re-deriving the
answer from local node syntax; the pure form is what the unit tier pins.
Counting decisions are not here: they are the ownership plan's (above).

| Predicate | Home | Consumers | Why it is shared |
|---|---|---|---|
| `context::CtorMeta::value_shape` | `context.rs` | `literals::nullary_constructor_tag` (the bare-`iconst` lowering) | **S120 (0917)**: a two-state classification of a constructor — `BareTag` (zero fields; the value IS the tag) or `Payload` (mints or moves a box) — from the ONE keyed `ctor_meta_at` read and the ONE `fields.is_empty()` test. A second field-list read is the channel on which a lowering could disagree with what a constructor carries, so none exists. |
| `apply::classify_auto_curry_target` | `apply.rs` | `compile_auto_curry_call` | the auto-curry seam's totality over the CLOSED carrier sums. The enum IS the totality claim — a new carrier state is a non-exhaustive-match compile error, never a `_ =>` fallthrough. |
| `apply::IoCombinator` | `apply.rs` | the lenient apply-argument spark exclusion and `compile_builtin_fn_call`'s interceptors | **S122 (IOR-5)**: the four inline IO combinators (`bind`/`select`/`race`/`sleep`) — the CLOSED set of `BuiltinFn` carriers lowered in place to a new IO node that consumes its operands. The enum IS the totality claim: a fifth combinator must decide its lowering, or it does not compile. |
| `FnCompiler::emit_typed_rc_dec` | `rc_emission.rs` | **every** concrete release (plan drops via `FnCompiler::emit_release`, the match arm's scrutinee release, Vec element adapters, capture slots) | **releasing a heap value is a function of its TYPE, not of the site** (0753, completed S118 W3). It converts to a `ConcreteType`, asks the registry for that type's glue, and emits ONE `call`. It has no `needs_guard` parameter — the nullary guard is `GlueShape::guard_nullary`, derived from the type's own ctor set, inside the body — and **no fallback arm**: a non-concrete type is a located `CodegenError`. The per-site classification it replaced (`typed_release_kind`/`TypedRelease`) is deleted; the load-bearing half of that rule, Vec-before-ADT, lives in `drop_glue::shape()`. |
| `control_flow::capture_rc::CaptureReleaseKind` → `CaptureRelease` | `capture_rc.rs` | both capture drop-glue mirrors via `emit_capture_dec_glue` | the same "release by what it owns" rule for closure-env capture slots, which build in a SEPARATE Cranelift context and so cannot call the `&mut self` helpers above — the enclosing compiler requests the glue (`request_capture_glue`) BEFORE that builder exists and the body emits the call. Two arms, **both glue**: the slot type's canonical body, or the closure box's embedded `DROP_GLUE_PTR`. There is no bare-dec disposition left, which is what made 0760's stranding shape unrepresentable rather than merely fixed. |
| `heap::emit_nullary_skip_guard` | `heap.rs` | every guarded increment through `emit_rc_inc_guarded_atomicity` (including Vec literal/set/push/get and element-adapter copies), plus `emit_rc_dec_guarded_atomicity` | **S118/S122 (0905/0906)**: the nullary-tag skip guard — `icmp ult ptr, NULLARY_TAG_THRESHOLD` then `brif` to the continuation, so the RC op runs iff `ptr >= NULLARY_TAG_THRESHOLD`. The RC halves and former Vec-local copies used to spell the prologue separately, which made a **polarity GAP** between "what each site treats as a pointer" spellable — the leak/UAF direction of invariant I-CT (`transitive-drop-glue.md` §4.1). Now one body owns every guarded increment and decrement. What sharing CANNOT close is the ABSOLUTE polarity (inverting here inverts every consumer consistently), so that is pinned structurally, as control flow — each `atomic_rmw` traced back to its guarding comparison and branch ARM — by the shared test walker used for constructor and Vec emissions. **Counting `iconst.i64 1024` occurrences is NOT that pin**: an inverted comparison keeps the count exact. Callers create the continuation block first; moving the Vec sites onto this helper can renumber CLIF blocks without changing behavior, so only attributed fixtures are re-baselined. |

## `got_data_symbol_name` is a FORWARD — never a second body

The GOT data-symbol scheme's canonical home is
`cranelisp_types::got_data_symbol_name` (relocated down at S76). The backend
**references** the symbol (`Linkage::Import` at every cross-module GOT-indirect
call site); **int defines** it (`jit.rs::symbol_lookup_fn`, `worker.rs`,
`exe.rs` — all on the types-owned fn). `compiler/resolution.rs`'s function is a
one-line forward and must stay one: changing it alone makes the consumer emit
relocations against names the definer never registers, and EVERY cross-module
call dies with `can't resolve symbol __cranelisp_got_…` (observed S115 W3 — the
whole stdlib stopped loading). Fenced by
`resolution::tests::got_data_symbol_name_agrees_with_the_types_owned_home`.
The scheme is non-injective (`a.b` collides with `a_b`); the fix is a types edit,
FIXME 0748 → `/arch`.

## Cache-load validation is ONE loop (R6)

Every persisted index deserialised from `.meta.json` is validated in the single
per-entry loop in `cache/serialize.rs::deserialise_meta_with_build_id`, one arm +
one distinct `CacheStale` class per family, and the census table lives in that
module's `//!` rustdoc. **A census in prose is not an instrument** (W3b / FIXME
0750: the summary-index row validated `MayAliasOf` — the one variant whose
consumers all read through checked `.get(k)` — and missed `ProjectionOf`, whose
consumer does a raw `args[k]`, i.e. the family's only genuine
panic-on-disk-content path). Where a family is a closed sum, its arm goes
through an EXHAUSTIVE match (`result_mode_param_index`) so a new variant is a
compile error, not a silent escape. Cache bytes are EXTERNAL data: every arm
**diagnoses and recompiles**, never `assert!`s (contrast the in-process
`store_slot`/`load_slot`
asserts). A new persisted index adds its row AND its arm in the change-set that
introduces it — never a parallel walk.
