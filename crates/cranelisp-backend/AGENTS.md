# cranelisp-backend — working in the code

Entry guidance for Cranelift emission, RC, JIT lifecycle and the object
cache. Owned by `dev` when narrow-deployed to this crate. How the crate solves
its problems is in [design/backend/backend.md](../../design/backend/backend.md)
and the designs it indexes; this memory links to them and does not restate them.

## Toolchain

- Cranelift is pinned to **0.116** across every `cranelift*` dependency
  (`Cargo.toml`). This is the only crate that names Cranelift types.
- Mode is the `Module` instance, never a parameter. `compile_to_module` is
  generic over `M: Module + CodeFinalizer` and emits the same CLIF for
  `JITModule` and `ObjectModule`. There is no object-compile entry: the object
  path is `compile_to_module::<ObjectModule>` plus the caller's
  `finish().emit()`.

## Rules an edit must not break

Each rule is owned elsewhere; the link is the authority.

- **One dispatch path.** Every primitive goes through the same GOT-indirect
  call as a user fn. `primitives_inline::try_emit_inline_primitive` is a
  name-keyed shortcut consulted first, never a second dispatch, and the backend
  has no trait knowledge ([backend.md](../../design/backend/backend.md) §2).
- **Pure keyed consumer.** Codegen fetches by typecheck's resolved key
  (`CompileContext::entry_at`, `ctor_meta_at`, `got_entry_at`) and hard-errors
  on a miss; it never searches symbol tables by name (backend.md §2).
- **The ownership plan is the only counting decider.** Emission reads
  `OwnershipPlan` and decides no count; operand order has one definition,
  `ownership_plan::operand_sequence`
  ([uniform counting](../../design/backend/uniform-counting.md)).
- **Release is by type.** Every concrete release goes through
  `FnCompiler::emit_typed_rc_dec`, which asks `DropGlueRegistry` for the
  type's one glue body
  ([transitive drop glue](../../design/backend/transitive-drop-glue.md);
  non-concrete types: [non-concrete release](../../design/backend/non-concrete-release-contract.md)).
- **A binder is its slot, never its name**
  ([binding scope](../../design/backend/binding-scope.md)).
- **Every codegen gate is byte-identical when off**, and a non-empty golden
  diff from a refactor means the refactor is wrong (backend.md §5).
- **A raise goes through `raise::emit_raise`**, the only emitter of a
  `runtime/panic` call (backend.md §7).

## Gotchas

- **Nullary ADT constructors are bare `i64` tags, not heap objects.** Values
  below `NULLARY_TAG_THRESHOLD` carry no RC header; guarded RC helpers skip
  them through `heap::emit_nullary_skip_guard`.
- **Layout offsets have two sources.** `heap.rs` owns `HeapAdt`, `HeapClosure`
  and `HeapVec` (static offset asserts beside each); `HeapHeader` is
  `cranelisp-types`'; `cranelisp-intrinsics` cannot depend on this crate and
  keeps its own offset constants. Change a layout on both sides.
- **`got_data_symbol_name` in `compiler/resolution.rs` is a one-line forward**
  to `cranelisp_types::got_data_symbol_name`. Int defines the symbol through the
  types function, so a backend-local change breaks every cross-module call.
- **Do not call `runtime/vec_drop` directly to release a Vec.** It tears down
  unconditionally; release goes through `vec_codegen::emit_vec_rc_dec_with_drop`.
- **A glue body can be built while another function's builder is live**, so
  emission order varies with input. Anything that depends on that order is a
  defect.

## Cache discipline

- **Any change to what a persisted `SymbolTable` means bumps
  `CACHE_SCHEMA_VERSION`** (`cache/mod.rs`; read the constant for the current
  value), in the same change-set. This includes upstream `cranelisp-types`
  changes and value-only changes; the constant's rustdoc states the rule.
  `CACHE_FORMAT_VERSION` is an alias of it.
- **Persisted indices are validated in one loop**,
  `cache/serialize.rs::deserialise_meta_with_build_id`, whose `//!` rustdoc
  holds the census. A new persisted index adds its row and its arm together;
  a closed sum goes through an exhaustive match.
- Validation diagnoses and recompiles rather than asserting. That covers the
  sidecar, not every byte: `cache/linker.rs` can panic on a truncated
  relocation in a malformed `.o`, a residual the user accepted on 2026-09-24.
- `BUILD_ID` (stamped by `build.rs`) invalidates on a compiler rebuild, but an
  uncommitted build carries its base commit's sha.

## Codegen environment gates

Each is read once into a process-global `OnceLock`/`LazyLock`, so a unit test
cannot flip one in-process; exercise it in a child (`test_child`). All default
off and are byte-identical off.

| Variable | Effect | Read in |
|---|---|---|
| `CRANELISP_NONATOMIC_RC` | Plain load/store RC instead of `atomic_rmw`. Unsound above one strand; measurement only, never shipped | `heap::use_nonatomic_arm` |
| `CRANELISP_RC_STATS` | Emit `runtime/rc_stat_*` tally calls, printed at exit | `heap.rs` |
| `CRANELISP_RC_DEC_CHECK` | Emit `runtime/rc_dec_check(ptr)` before each inline dec | `heap::emit_rc_dec_check_gated` |
| `CRANELISP_NO_OWNERSHIP` | Moves off: every use duplicates. Also a cache key | `cranelisp_types::ownership_analysis_off()` |
| `CRANELISP_NO_LENIENT`, `CRANELISP_SPARK_ADMIT`, `CRANELISP_SPARK_STATS` | Lenient spark admission and its tally | `compiler/control_flow/sparkability.rs`, `utilization.rs` |

## Debug hooks

- `CRANELISP_CODEGEN_DUMP` dumps CLIF to stderr per symbol: `*` for all,
  `module::symbol` for one, a bare string for one module
  (`crates/cranelisp-backend/src/lib.rs::clif_dump_matches`). The REPL's `/clif <name>` and `/disasm`
  (`produce_disasm`, on demand) are the interactive equivalents.
- The golden-CLIF lane is `tests/scripts/clif_golden.sh diff`, gated in
  nextest by `tests/clif_golden_lane.rs`. To check that a refactor is
  byte-identical when the committed goldens already drift, capture the current
  tree to a scratch directory before the change and compare after.

## Seam map

Codegen is `impl FnCompiler` blocks across `compiler/` submodules, re-exported
through the hubs `compiler/mod.rs` and `compiler/control_flow.rs`.
The `compiler` module is crate-private.

| Area | Files |
|---|---|
| Body compiler and context | `compiler/{fn_compiler,context}.rs` |
| Call sites (direct, GOT, extern, platform, poll, IO combinators) | `compiler/{apply,extern_call,io_nodes}.rs` |
| Ownership plan | `compiler/ownership_plan.rs` |
| Lexical scope | `compiler/scope_chain.rs` |
| RC and release | `compiler/rc_emission.rs`, `drop_glue.rs`, `heap.rs` |
| Literals, match, trace, Vec | `compiler/{literals,match_codegen,trace_codegen,vec_codegen}.rs` |
| Fixed name-composition schemes | `compiler/resolution.rs` |
| Control flow | `compiler/control_flow/`: `let_if`, `lambda`, `fn_as_value`, `free_vars`, `capture_rc`, `par_bind`, `launch`, `select`, `sparkability`, `dependent_spark`, `utilization` |
| Panics | `raise.rs` |
| JIT, code handles, GOT observer | `jit.rs`, `code.rs`, `got_observer.rs` |
| Cache and objects | `cache/{mod,manifest,serialize,object,linker}.rs` |
| Executables, platform schema, artefacts, errors | `exe.rs`, `schema.rs`, `artefact.rs`, `error.rs` |

## Tests

- **Tests sit beside the submodule they cover**: `{module}/tests.rs` or a
  topical `{module}/{behaviour}_tests.rs`. Do not grow a crate-root test file.
  The crate-root exceptions are `module_assembly_tests.rs`,
  `clif_dump_tests.rs`, `got_slab_tests.rs`, `macro_clause_ownership_tests.rs`
  and `rc_ownership_fence_tests.rs`.
- **CLIF probes go through the production per-body function.**
  `test_support::probe_defn_clif` returns one defn's CLIF;
  `compile_defns_in_module` compiles several without finalizing;
  `try_compile_defns_in_module` returns a codegen refusal instead of panicking.
  All call `compile_defn_in_module`, as `compile_to_module` does. Do not add a
  parallel context assembly.
- **A heap-typed parameter must be spelled in the stub's scheme**
  (`insert_user_fn_stub_typed`). The all-`Int` `insert_user_fn_stub` leaves a
  `String` parameter unclassified, so every RC gate silently sits out.
- **Code that raises, or reads a once-read gate, runs in a child process**
  through `test_child.rs`; `test_support::assert_raise_terminates` covers the
  raise case.
