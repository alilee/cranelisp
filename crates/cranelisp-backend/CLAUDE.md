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
  (`closure_drop_glue_name` / `curry_drop_glue_name` / `adt_drop_glue_name` — the
  S111 R6 §4.1 ONE naming-identity home, called by the production glue builders +
  the consolidated `resolution::tests` identity battery, never re-composed inline).
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
`compiler/control_flow/{par,poll,select}_codegen_tests.rs`). Crate-root exceptions:
`module_assembly_tests.rs`, `clif_dump_tests.rs`, `got_slab_tests.rs`. When
adding a codegen behaviour, add its test sibling next to the submodule — don't
grow a crate-root file. `test_support.rs` provides the shared AST-fragment
compile harness.

**The CLIF-probe / execution test seam is the PRODUCTION per-body function**
(`test_support::probe_defn_clif` for a single defn's CLIF text;
`compile_defns_in_module` for the multi-defn / execution-tier no-finalize
variant). Both ride `compile_defn_in_module` — the EXACT Step-3 call
`compile_to_module_impl` makes. **The `Jit::compile_defn`/`compile_defn_with_targets`/
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

## RC-emission gates that are ONE predicate, not per-site syntax (S115 W3/W4c)

Three RC decisions used to be re-derived at each consuming site from local node
syntax. Each is now a single pure predicate; the sites call it, and the pure form
is what the unit tier pins (constructing a live `FnCompiler` is not needed).

| Predicate | Home | Consumers | Why it is shared |
|---|---|---|---|
| `vec_codegen::cow_site_source` (+ `cow_source_has_separate_owner` / `cow_source_is_borrowed` / `cow_retains_reused_gate` / `cow_site_retain_verdict`) | `vec_codegen.rs` | **all four** consumers of "is this a COW site": the producer `cow_source_ownership`, the R3 dec-side seam `fn_compiler::scrutinee_cow_retains_reused`, the MS-P8 flush exemption `fn_compiler::arg_is_inplace_cow_on`, and the return-source producer `fn_compiler::return_cow_source_in_scope` | ONE identity question. Every one of them used to re-derive it from the **syntactic callee spelling** (`matches!(callee_name, "vec-set"\|"vec-push")`) — the resolver-mirror class, with a latent UAF: a user fn literally named `vec-set` made the name test true though the COW gate never ran. S115 W3 converted the R3 seam (0693); **W3b converted the last two (0752)** — `return_cow_source_in_scope` was the sharp one, because its product FEEDS `cow_source_is_borrowed`, so the spelling channel persisted one level upstream of the "consolidated" gate. Identity comes from the RESOLUTION CARRIER (`ResolvedCall::BuiltinFn`), P24. `cow_source_needs_toggle_off_count` is the toggle-inverted face of `cow_source_is_borrowed` and shares its body. |
| `fn_compiler::is_fresh_construction` | `fn_compiler.rs` | `protect_return_value` (fn-return AND match-arm protect sites) | the return-protect's only license is that the returned box cannot alias a scope binding. Keying it on the fn NAME (`== "main"`) was the 0632/P19 class; freshness is the real license, and it forwards through `let` and through control-flow joins (fresh iff EVERY arm is fresh). **W3b (0749)**: the predicate now covers EVERY box-minting kind (`ConstrADT`, ctor-`Apply`, **`Lambda`, `StringLit`, `VecLit`, auto-curry `Apply`**) and `protect_return_value` no longer carries its own `matches!` list — two lists of "what is fresh", of which the local one did not forward through `let`. The match is **exhaustive (no `_ =>`)**: that is the standing instrument, since a minting kind swept into a catch-all emits a protect inc nothing can balance. |
| `fn_compiler::value_provenance` → `yields_owned_temporary` | `fn_compiler.rs` | **five** ownership gates across two seams: `vec_codegen::{emit_vec_drop_if_temporary, is_vec_last_use, cow_source_has_separate_owner}` and `match_codegen::{compile_var_pattern_arm::is_alias, dec_temporary_scrutinee::is_temp}` | **W4c (0781)**: all five asked "is this container/scrutinee mine to release?" with `matches!(e, MonoExpr::Var { .. })` — the NODE KIND standing in for the value's provenance. An `If`/`Match`/`Let` that merely YIELDS a borrowed param is not a `Var`, so every one of them claimed a box the enclosing scope still owns: `(defn f [v b] (vec-get (if b v v) 0))` → `--link` exit 134, no `let`, no COW, both arms identical. The derived answer is a three-point lattice `Fresh ⊑ OwnedTemporary ⊑ NotOwnedHere` (join = weakest arm, forwards through `Let`/`If`/`Match`, capped at `OwnedTemporary` through `Trace`/`ParBind`/`LaunchContinue`), read at TWO thresholds by TWO consumers: `is_fresh_construction` = `== Fresh` (protect elision needs the strong unaliased claim), `yields_owned_temporary` = `!= NotOwnedHere` (release needs only "nothing else will release it"). `is_fresh_construction` is now literally the `== Fresh` face — one classification, two heights. The threshold is ctor-probe-INDEPENDENT, which is why the five gates need no symbol-table access. The match is **exhaustive (no `_ =>`)**: the standing instrument, and now doubly load-bearing — a minting kind swept into a catch-all leaks (0749), a borrowing kind swept in is a UAF (0781). |
| `apply::classify_auto_curry_target` | `apply.rs` | `compile_auto_curry_call` | the auto-curry seam's totality over the CLOSED carrier sums. The enum IS the totality claim — a new carrier state is a non-exhaustive-match compile error, never a `_ =>` fallthrough. |
| `rc_emission::typed_release_kind` → `FnCompiler::emit_typed_rc_dec` | `rc_emission.rs` | the ADT drop-glue field walk (`emit_field_decs`) + the moded-arg post-call dec (`apply::emit_post_call_decs`) | **releasing a heap value is a function of its TYPE, not of the site** (W3b, 0753). Vec → `vec_drop` + per-element dec; ADT → recursive inline glue; `Fn` → the box's EMBEDDED `DROP_GLUE_PTR`; anything else → plain dec. A bare `heap::emit_rc_dec(.., None)` frees the box and STRANDS what it owns — that is the recurring leak shape, and `emit_post_call_decs` was doing exactly that for `Borrowed`-param temporaries. Vec is classified BEFORE ADT (a Vec is spelled `Type::ADT(Vec, [t])` but its elements live behind `DATA_PTR`). |
| `control_flow::capture_rc::CaptureRelease` | `capture_rc.rs` | both capture drop-glue mirrors via `emit_capture_dec_glue` | the same "release by what it owns" rule for closure-env capture slots, which build in a SEPARATE Cranelift context and so cannot call the `&mut self` helpers above. Covers the closure-box case (0749 mechanism (b)); the nested-heap cases (a Vec-of-heap / ADT-with-heap-field capture) are still stranded — **FIXME 0760**. |

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
