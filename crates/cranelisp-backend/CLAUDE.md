# cranelisp-backend — local conventions

The voice of the code: API gotchas, codegen/heap/RC invariants, cache discipline,
and debug hooks for Cranelift emission, JIT lifecycle, and object caching. Owned
by `/dev` when narrow-deployed to this crate.

## Cranelift version + the byte-identical-CLIF invariant

Pinned to **Cranelift 0.116** across `cranelift`, `-module`, `-jit`, `-native`,
`-codegen` (with `disas`), `-object` (`Cargo.toml`); `target-lexicon 0.12`,
`object 0.36` are `/arch`-blessed direct deps already transitive via cranelift's
`disas`. This is the ONLY crate that names Cranelift types — everything upstream
flows in through `cranelisp-types` (`lib.rs` rustdoc).

**Mode is the `Module` instance, never a parameter.** `compile_to_module` is
generic over `M: Module + CodeFinalizer` and emits **byte-identical CLIF**
whether `M` is `JITModule` or `ObjectModule` (`lib.rs` §"codegen boundary"). Any
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
| `CRANELISP_NO_OWNERSHIP` | force conservative ownership point; **flips a cache global key** (mixed-ABI caches unrepresentable) | via `cranelisp_types::ownership_analysis_off()`, `cache/manifest.rs` |
| `CRANELISP_NO_LENIENT` / `CRANELISP_SPARK_ADMIT` / `CRANELISP_SPARK_DENSITY_MAX` / `CRANELISP_CAPTURE_BORROW` / `CRANELISP_SPARK_STATS` | lenient-eval spark admission tuning + tally | `compiler/control_flow/sparkability.rs`, `utilization.rs` |

**`CRANELISP_CODEGEN_DUMP`** dumps CLIF to stderr per symbol. Filter grammar
(`lib.rs::clif_dump_matches`, pure + unit-tested): `*` = all; `module::symbol`
= exact pair; bare string = exact module match. This is the codegen-layer
inspection hook (the S66/CLAUDE-cited `CRANELISP_CODEGEN_TRACE` role); pairs with
REPL `/clif <name>` and `/disasm` (`produce_disasm`, on-demand — disassembly is
NOT in the always-created `CompilationArtifacts`).

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
  / `inner_fn_discriminator_for`) plus the three drop-glue naming fns
  (`closure_drop_glue_name` / `curry_drop_glue_name` — the S111 R6 §4.1 ONE
  naming-identity home, never re-composed inline). These name capture
  ENVELOPES, not type glue: **type-glue identity is `cranelisp_types::
  drop_glue_symbol_name` and nothing else** (S118 W3 §8 deleted
  `adt_drop_glue_name` / `adt_instantiation_mangle` / `escape_symbol`, the
  backend-local second identity scheme).
  Grep gate: zero `resolve_driven`/`resolve_*_target` in `compiler/`.
- `compiler/control_flow/` — `let_if`, `par_bind`, `lambda`, `fn_as_value`,
  `free_vars`, `sparkability`, `capture_rc`, `select`, `launch`, `utilization`.
- `heap.rs`, `jit.rs`, `got_observer.rs`, `schema.rs`, `exe.rs`,
  `code.rs`, `primitives_inline.rs`, `cache/{manifest,serialize,object,linker,mod}.rs`.

**`#[cfg(test)]` modules are per-submodule siblings** (S101 coverage-audit reorg:
the flat 5,861-line crate-root `tests.rs` was split into 14 siblings; the split
serves the METHOD §2.2 submodule×scenario-class accounting). Convention:
`{module}/tests.rs` next to `{module}.rs` (e.g. `cache/linker/tests.rs`,
`compiler/resolution/tests.rs`, `heap/tests.rs`, `jit/tests.rs`), plus topical
`_tests.rs` siblings for a specific behaviour (e.g.
`compiler/apply/moded_arg_rc_tests.rs`, `compiler/vec_codegen/reuse_proof_tests.rs`,
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
when the probe must READ a codegen refusal rather than panic on it, or must
thread a per-defn `ModeSummary`, which is the only way to put a parameter in
`Borrowed` mode since `bind_defn_params` marks params borrowed from the summary
and from nothing else). All ride `compile_defn_in_module` — the EXACT Step-3 call
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
the ADT builder keeps its own multi-ctor-body envelope but shares the naming fn
(S111 R6 §4.3 fallback).

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
- The only *sanctioned* non-concrete release site is the **ctor template's own
  parameter** (`design/backend/transitive-drop-glue.md` §4.1 — the authority; it
  covers BOTH a declared type parameter and an undeclared field, because a ctor
  `Def` is compiled once per declaration, not per instantiation). Its licence is
  invariant **I-CT** — the dec balances the guarded consuming inc on a word
  `emit_adt_construct` published into the box the frame returns, so it can never
  be the last reference. Balance pinned by
  `compiler/fn_compiler/ctor_template_admission_tests.rs`. Standing obligation:
  a `ModeSummary` with a `Borrowed` parameter reaching a ctor template drops the
  dec while the inc still fires — that breaks I-CT in the leak direction and
  must revisit §4.1.
- **But the live gate in `emit_heap_binding_decs` is keyed on the TYPE, not the
  frame — knowingly, and it is NOT the whole story** (FIXME 0903; 0891 deferred
  on it). §4.1 rules the gate must be the frame and §11 makes a type-keyed gate
  a `/review` REJECT; implementing exactly that (an `is_ctor_template` boolean
  from `compile_body`, a two-state verdict threaded to the shared body, both
  tail-jump flushes rejecting) was measured at **+16 hard codegen refusals over
  the `spec_*` corpus**. Two further families reach the arm in ordinary
  `defn`-shaped frames I-CT does not cover: synthetic **field accessors** of a
  generic/undeclared-field product (`Box.v`'s `self: ADT(user/Box, [Var(0)])` —
  `concrete-boundary-type.md` §3.1.1 pairs the ctor *and accessor* signature
  paths; §4.1 named only the ctor half) and **generic trait-method instances**
  (`Functor.fmap$primitives/Option`'s `Fn([Var(9)], Var(8))` parameter). Those
  leak today. Do not re-run the narrowing on its own — the experiment is done and
  the census is in the function's rustdoc; the class needs one ruling.

## RC-emission gates that are ONE predicate, not per-site syntax (S115 W3/W4c)

Three RC decisions used to be re-derived at each consuming site from local node
syntax. Each is now a single pure predicate; the sites call it, and the pure form
is what the unit tier pins (constructing a live `FnCompiler` is not needed).

| Predicate | Home | Consumers | Why it is shared |
|---|---|---|---|
| `vec_codegen::cow_site_source` (+ `cow_source_has_separate_owner` / `cow_source_is_borrowed` / `cow_retains_reused_gate` / `cow_site_retain_verdict`) | `vec_codegen.rs` | **all four** consumers of "is this a COW site": the producer `cow_source_ownership`, the R3 dec-side seam `fn_compiler::scrutinee_cow_retains_reused`, the MS-P8 flush exemption `fn_compiler::arg_is_inplace_cow_on`, and the return-source producer `fn_compiler::return_cow_source_in_scope` | ONE identity question. Every one of them used to re-derive it from the **syntactic callee spelling** (`matches!(callee_name, "vec-set"\|"vec-push")`) — the resolver-mirror class, with a latent UAF: a user fn literally named `vec-set` made the name test true though the COW gate never ran. S115 W3 converted the R3 seam (0693); **W3b converted the last two (0752)** — `return_cow_source_in_scope` was the sharp one, because its product FEEDS `cow_source_is_borrowed`, so the spelling channel persisted one level upstream of the "consolidated" gate. Identity comes from the RESOLUTION CARRIER (`ResolvedCall::BuiltinFn`), P24. `cow_source_needs_toggle_off_count` is the toggle-inverted face of `cow_source_is_borrowed` and shares its body. |
| `fn_compiler::is_fresh_construction` | `fn_compiler.rs` | `protect_return_value` (fn-return AND match-arm protect sites) | the return-protect's only license is that the returned box cannot alias a scope binding. Keying it on the fn NAME (`== "main"`) was the 0632/P19 class; freshness is the real license, and it forwards through `let` and through control-flow joins (fresh iff EVERY arm is fresh). **W3b (0749)**: the predicate now covers EVERY box-minting kind (`ConstrADT`, ctor-`Apply`, **`Lambda`, `StringLit`, `VecLit`, auto-curry `Apply`**) and `protect_return_value` no longer carries its own `matches!` list — two lists of "what is fresh", of which the local one did not forward through `let`. The match is **exhaustive (no `_ =>`)**: that is the standing instrument, since a minting kind swept into a catch-all emits a protect inc nothing can balance. |
| `fn_compiler::value_provenance` → `yields_owned_temporary` | `fn_compiler.rs` | **four** probeless ownership gates plus the one probe-reading consumer: `vec_codegen::{emit_vec_drop_if_temporary, is_vec_last_use, cow_source_has_separate_owner}`, `match_codegen::compile_match`'s once-recorded arm lifetime plan, and `rc_emission::protect_return_value` via `body_is_fresh_construction` | **W4c (0781)**: each probeless gate asked "is this container/scrutinee mine to release?" with `matches!(e, MonoExpr::Var { .. })` — the NODE KIND standing in for the value's provenance. An `If`/`Match`/`Let` that merely YIELDS a borrowed param is not a `Var`, so every one of them claimed a box the enclosing scope still owns: `(defn f [v b] (vec-get (if b v v) 0))` → `--link` exit 134, no `let`, no COW, both arms identical. (`compile_var_pattern_arm`'s alias registration was a fifth reader until S118 W3's single-owner ruling deleted it; "five gates" is the stale count.) The derived answer is a **four-point** lattice `NoReference ⊑ Fresh ⊑ OwnedTemporary ⊑ NotOwnedHere` (join = weakest arm, forwards through `Let`/`If`/`Match`, capped at `OwnedTemporary` through `Trace`/`ParBind`/`LaunchContinue`, and the `Match` fold seeds at the identity `NoReference` — the explicit ARM-LESS guard is what keeps "no value on any path" distinct from "every path carries no reference"), read at TWO thresholds: `is_fresh_construction` = `<= Fresh` (protect elision needs the strong unaliased claim, which a value carrying no reference satisfies trivially), `yields_owned_temporary` = `Fresh \| OwnedTemporary` (release needs "nothing else will release it", and a bare tag is nothing to release — spelling it `!= NotOwnedHere` is now the bug). The match is **exhaustive (no `_ =>`)**: the standing instrument, and triply load-bearing — a minting kind swept into a catch-all leaks (0749), a borrowing kind swept in is a UAF (0781), and a bottom kind swept in poisons its join (0917). |
| `context::CtorMeta::value_shape` | `context.rs` | `literals::nullary_constructor_tag` (the bare-`iconst` lowering) and `CompileContext::ctor_value_shape_at` → `value_provenance`'s ctor probe | **S120 (0917)**: the probe is a THREE-STATE closed classification of a global reference — `None` (not a constructor, the probe declining), `BareTag` (zero fields; the value IS the tag), `Payload` (mints or moves a box) — produced by the ONE keyed `ctor_meta_at` read and the ONE `fields.is_empty()` test. A boolean `is_ctor` could not separate a zero-field constructor from one with fields, so `value_provenance`'s `Var` arm classified user-written `None` as ⊤ and one nullary arm poisoned the whole match's join, licensing a protect inc on the fresh boxed arm beside it that nothing balanced (4 objects stranded per iteration, deallocs CONSTANT). A **second** predicate or a second field-list read is the channel on which a provenance verdict can disagree with what was emitted — 0917's own shape one level down — so neither exists. |
| `apply::classify_auto_curry_target` | `apply.rs` | `compile_auto_curry_call` | the auto-curry seam's totality over the CLOSED carrier sums. The enum IS the totality claim — a new carrier state is a non-exhaustive-match compile error, never a `_ =>` fallthrough. |
| `FnCompiler::emit_typed_rc_dec` | `rc_emission.rs` | **every** release seam (scope exit, both tail-jump flushes, the match wrapper release, the moded-arg post-call dec, Vec element adapters, capture slots) | **releasing a heap value is a function of its TYPE, not of the site** (0753, completed S118 W3). It converts to a `ConcreteType`, asks the registry for that type's glue, and emits ONE `call`. It has no `needs_guard` parameter — the nullary guard is `GlueShape::guard_nullary`, derived from the type's own ctor set, inside the body — and **no fallback arm**: a non-concrete type is a located `CodegenError`. The per-site classification it replaced (`typed_release_kind`/`TypedRelease`) is deleted; the load-bearing half of that rule, Vec-before-ADT, lives in `drop_glue::shape()`. |
| `control_flow::capture_rc::CaptureReleaseKind` → `CaptureRelease` | `capture_rc.rs` | both capture drop-glue mirrors via `emit_capture_dec_glue` | the same "release by what it owns" rule for closure-env capture slots, which build in a SEPARATE Cranelift context and so cannot call the `&mut self` helpers above — the enclosing compiler requests the glue (`request_capture_glue`) BEFORE that builder exists and the body emits the call. Two arms, **both glue**: the slot type's canonical body, or the closure box's embedded `DROP_GLUE_PTR`. There is no bare-dec disposition left, which is what made 0760's stranding shape unrepresentable rather than merely fixed. |
| `heap::emit_nullary_skip_guard` | `heap.rs` | both guarded RC halves: `emit_rc_inc_guarded_atomicity` + `emit_rc_dec_guarded_atomicity` | **S118 (0905)**: the nullary-tag skip guard — `icmp ult ptr, NULLARY_TAG_THRESHOLD` then `brif` to the continuation, so the RC op runs iff `ptr >= NULLARY_TAG_THRESHOLD`. Each half used to spell the three-instruction prologue itself, which made a **polarity GAP** between "what the inc treats as a pointer" and "what the dec does" spellable — the leak/UAF direction of invariant I-CT (`transitive-drop-glue.md` §4.1). Now one body moves both halves together. What sharing CANNOT close is the ABSOLUTE polarity (inverting here inverts both consistently), so that is pinned structurally, as control flow — each `atomic_rmw` traced back to its guarding comparison and branch ARM — by `compiler/fn_compiler/ctor_template_admission_tests.rs::assert_threshold_guarded_rmws`. **Counting `iconst.i64 1024` occurrences is NOT that pin** and was the 0905 defect: an inverted dec-side comparison keeps the count exact. Callers create the continuation block FIRST — block creation order is CLIF block numbering, and the refactor is byte-identical (verified against `tests/fixtures/clif_baseline/golden/`). |
| `fn_compiler::tco_slot_disposition` | `fn_compiler.rs` | `flush_let_scopes_before_tail_jump` + `flush_superseded_heap_params_before_tail_jump` | the ONE TCO owner-continuity verdict (`TransferOldOwner \| Replace \| BorrowedInvalid`), folding four fragments that used to be combined ad hoc inside two filter closures. Two traps: **row 2 (a control-flow tail argument) must stay `Replace`** — the per-branch protective inc plus uniform flush is the emission strategy, and a blanket skip re-introduces the F1 UAF; and **`BorrowedInvalid` means a SHADOWING borrow**, not "the slot is borrowed" (a `Borrowed` param carried forward as its own tail argument is ordinary and owes nothing). |

**The R3 gate additionally DERIVES rather than re-derives**: `cow_source_ownership`
records its emitted retain decision span-keyed into `FnCompiler::cow_retain_decisions`,
and the match seam READS it via `fn_compiler::reconcile_cow_retain_verdict`. The
shared predicate is a `debug_assert!` disagreement fence (a producer/consumer
mismatch is the spurious-dec/UAF channel). **Every uncertain case takes the
leak-safe verdict `false`**: an ambiguous span collision, AND — since W3b /
FIXME 0751 — a release-build disagreement. The old rustdoc claimed a
disagreement "degrades to the producer's truth"; it degrades to a DIFFERENT
SITE's truth, which is the UAF direction, so it now gets the polarity the
ambiguity arm always had. An absent record (the producer ran in another
compiler frame) falls back to the shared predicate.

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
