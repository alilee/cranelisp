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

## GOT slab — fixed 1024 slots, UNCHECKED allocation (S101 item d, got.rs)

`GotTable` is a FIXED `GOT_TABLE_SIZE`(=1024)-slot `Box<[AtomicPtr<u8>; 1024]>`
allocated once and NEVER reallocated; `base_ptr()` is structurally stable for the
session (finalized machine code bakes the base via `__cranelisp_got_{M}`
resolution, so movement would dangle it — verified by `got.rs::slab_growth_tests`).
"Growth" is only the monotone `SymbolTable::next_got_slot` index. **GOTCHA:
`allocate_got_slot` is UNCHECKED** (`+= 1`, no bound test); `store_slot`/`load_slot`
only `debug_assert!(slot < 1024)` — in release, slot 1024 is OOB (UB). The hard
bound is EXHAUSTION, not movement; long dev sessions with many ABI-changing
redefinitions (fresh-slot churn) approach it faster. Slot exhaustion is an
unresolved surfaced-error question, not a bug to "fix" locally.

## Cache — schema-bump discipline (cache/mod.rs)

Five invariants (cache/mod.rs rustdoc): `Linker` is the only mmap-holder (per-symbol
retention via `Arc<Linker>`); `CacheManifest` is the single index (sidecar⇔object
pair-invariant); validity checked at every hit (stale ⇒ recompile, never
use-stale); **no re-codegen on cache-hit** (the `.o` bytes are authoritative);
`CACHE_FORMAT_VERSION` (manifest shape) and `CACHE_SCHEMA_VERSION` (sidecar
`SymbolTable` shape) are independent. **Any serde-shape change to the persisted
`SymbolTable` MUST bump `CACHE_SCHEMA_VERSION`** (currently `19`, cache/mod.rs) in
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
  — per-concern codegen; `resolution.rs` holds the `resolve_*_target`/`resolve_func_arity` probes.
- `compiler/control_flow/` — `let_if`, `par_bind`, `lambda`, `fn_as_value`,
  `free_vars`, `sparkability`, `capture_rc`, `select`, `launch`, `utilization`.
- `heap.rs`, `jit.rs`, `got.rs`/`got_observer.rs`, `schema.rs`, `exe.rs`,
  `code.rs`, `primitives_inline.rs`, `cache/{manifest,serialize,object,linker,mod}.rs`.

**`#[cfg(test)]` modules are per-submodule siblings** (S101 coverage-audit reorg:
the flat 5,861-line crate-root `tests.rs` was split into 14 siblings; the split
serves the METHOD §2.2 submodule×scenario-class accounting). Convention:
`{module}/tests.rs` next to `{module}.rs` (e.g. `cache/linker/tests.rs`,
`compiler/resolution/tests.rs`, `heap/tests.rs`, `jit/tests.rs`), plus topical
`_tests.rs` siblings for a specific behaviour (e.g.
`compiler/apply/moded_arg_rc_tests.rs`, `compiler/vec_codegen/reuse_proof_tests.rs`,
`compiler/control_flow/{par,poll,select}_codegen_tests.rs`). Crate-root exceptions:
`module_assembly_tests.rs`, `clif_dump_tests.rs`. When adding a codegen behaviour,
add its test sibling next to the submodule — don't grow a crate-root file.
`test_support.rs` provides the shared AST-fragment compile harness.
