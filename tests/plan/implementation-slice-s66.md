# Sprint 66 implementation slice — `/qa` test plan

**Status.** draft
**Author.** `/qa`, 2026-05-06
**Reads.** all eight final-state facades (`design/arch/facades/{types,frontend,typecheck,backend,platform,intrinsics,primitives,int}.md` after S65 close), `design/arch/sprint-65-reshape-phase-2-review.md` §3 (slice template — adapted for `/qa`), `design/arch/sprint-65-legacy-triage.md` (carryforward FIXMEs into S66 scope), `design/arch/legacy/substance-action-plan.md` Step-4 row for `/qa` ("First-wave slice of integration + e2e infrastructure uplift; coverage tests for the substance commitments landing in Sprint 66"), `tests/CLAUDE.md`, `tests/plan/PLAN.md`, `tests/plan/ledger.md`, `sprints/SPRINT.md` § Hard constraints, `sprints/archive/sprint-64.md` Phase-6 reconciliation, `memory/feedback_failing_not_ignored.md`, `memory/project_test_strategy.md`.

This slice scopes the **test-side** of S66 facade adoption. S66 lands per-crate facade conformance against the binding S65 facade set; this plan scopes the test-suite work that gates that adoption. Authoring follows the slice template adapted from `design/arch/sprint-65-reshape-phase-2-review.md §3.2` for `/qa`'s deliverable.

---

## 1. `cargo public-api` integration plan

S66 is the first sprint where every facade is binding. `cargo public-api` becomes the mechanical drift detector between as-designed (the facade `.md` file) and as-built (the crate's actual public surface). The integration plan:

### 1.1 Per-crate baselines

One `public-api.txt` baseline per crate, checked into the crate's directory:

| Crate | Baseline path | Author | Notes |
|---|---|---|---|
| `cranelisp-types` | `crates/cranelisp-types/public-api.txt` | W4a /design (types) — runs `cargo public-api` once facade is final | Largest baseline; FQTypeName threading + `PlatformError` + `ResolutionGap` + `CheckError` all surface here |
| `cranelisp-frontend` | `crates/cranelisp-frontend/public-api.txt` | /design (frontend) | Per facade §"Free functions" — `parse`, `extract_module_declarations`, `build_ast`, `build_expr`, `expand`, `parse_preserving_comments`, `next_synthetic_span`, `parse_defmacro`, `synthesize_macro_clause_defn`, `is_defmacro`, `is_begin`, `flatten_begin`, `expand_quasiquotes`. Plus DTOs: `StructuralDecls`, `DefmacroInfo`, `ExpansionError`. |
| `cranelisp-typecheck` | `crates/cranelisp-typecheck/public-api.txt` | /design (typecheck) | Per facade §"Free function" — `check_form`, `register_builtins`, `CheckResult`, `CheckError`, `ReplSnapshot`, `CheckState`, `TypeCheckEnv`, `CheckPass`, trace install hook |
| `cranelisp-backend` | `crates/cranelisp-backend/public-api.txt` | /design (backend) | Per facade — `compile_to_module`, `load_object`, `compile_to_object`, `Code`, `Jit`, `Linker`, `LinkerArtefact`, `ObjectArtefact`, `CompilationError`, `GotEvent{Tag,}`, `GotProvenance`, `GotObserver`, `register_got_observer` |
| `cranelisp-platform` | `crates/cranelisp-platform/public-api.txt` | /design (platform) | DLL ABI types (`#[repr(C)]` exempt from `#[non_exhaustive]` per Principle 14) + `OwnedPlatformFnDescriptor` + `load_manifest` + `parse_type_sig` + `derive_jit_name` + `HostContext`/`HostCallbacks` + `IO_TAG_*` consts + `declare_platform!` macro |
| `cranelisp-intrinsics` | `crates/cranelisp-intrinsics/public-api.txt` | /design (intrinsics) | New baseline — every `#[no_mangle] extern "C" fn` plus `IoEvent`, `IoEventTag`, `IoObserver`, `register_io_observer`, `trace_anchor`, `HeapString`, stats accessors |
| `cranelisp-primitives` | `crates/cranelisp-primitives/public-api.txt` | /design (primitives) | New baseline — every `#[no_mangle] extern "C" fn` (integer, float, bool, conversions). No structs / enums |
| `cranelisp` (binary / int) | `crates/cranelisp-exe-bundle/public-api.txt` (or `src/public-api.txt`) | /design (int) | Largest surface; `CompilerSession` methods, `SharedState`, `CompileScheduler`, `ObjectCache`, `EvalResult`, `CommandResult`, `SlashCommand`, `SymbolInfo`, `SymbolDescription`, `Introspection`, line-editor types, watcher events, CLI parsing, `IoTraceFlushGuard`, `SchedulerTraceFlushGuard`, `CacheWritePacket`, `TracedFnInfo` |

### 1.2 CI gate

A new top-level `cargo xtask api-check` (or `just api-check`) script runs `cargo public-api --diff-git-checkout HEAD~1` per crate. Drift produces a non-zero exit. Wired into the same CI lane as `cargo nextest run`.

### 1.3 Drift workflow

When `api-check` reports drift:

- **Intentional facade-shape change** — author updates the facade `.md` first, then regenerates the baseline (`cargo public-api > crates/{crate}/public-api.txt`), commits both in one change. PR review checks the facade rationale.
- **Unintentional drift** — fix the source to match the facade. The baseline does not regenerate.
- **The two cases are distinguished by which side of the diff changed**: facade or source. Reviewers always look at the facade first.

### 1.4 Sizing

Per-crate baseline generation: 30 min × 8 crates ≈ 4 hr. CI wiring: 1 hr. xtask + docs: 2 hr. Drift-process documentation in `tests/CLAUDE.md` and `design/arch/CLAUDE.md`: 1 hr. **Total ~ 1 day.**

### 1.5 Out-of-scope for the gate

`cargo public-api` does NOT enforce semantic correctness — only signature shape. A function whose signature matches the facade but whose body returns wrong values is a test problem, not an `api-check` problem. The 95% pass-rate gate (§2 below) catches that side; the two gates are complementary.

---

## 2. 95% pass-rate gate calibration

### 2.1 S64-close baseline

Per `tests/plan/ledger.md` § "Sprint 64 Phase 6 reconciliation (2026-05-05, SHA `9340534`)":

- **932 pass / 21 fail / 6 skipped** out of **953 tests** total.
- Pass rate: 932 / 953 = **97.8%**.
- The 21 failures are tracked in the ledger; cluster mapping (per Phase-6 reconciliation):
  - 1 cache (FIXME 0121)
  - 9 spec_08_modules `(mod ...)` cluster (FIXME 0121 cluster)
  - 1 spec_08_modules import-below-use (FIXME 0140)
  - 4 build_confidence `--link` divergence (FIXME 0122)
  - 1 repl_negative unclosed-paren (FIXME 0142)
  - 4 d6_exemplar_* SEGVs (FIXME 0145 / Defect 6, /port + /backend)
  - 1 regression::wave6_exemplar_solver_full_run (FIXME 0148 / Defect 6, /port + /backend)

### 2.2 Hard-constraint phrasing

**The 95% gate is calibrated as: at S66 close, pass-rate MUST be ≥ 95% of the active-suite test count, AND the cluster of failures MUST be a subset of (the S64 ledger ∪ pre-classified expected reshapes from S66 facade adoption — see §2.3 below) ∪ explicit S66 ledger entries with target sprints.** No silent net-new failures.

The gate has two parts:

- **Pass-rate floor**: 95% of the active-suite count (e.g., 953 → 906 minimum passing). The S64 baseline of 932 already exceeds this comfortably; a 26-test margin against unforeseen reshapes.
- **Failure-set discipline**: every failure carries a ledger row (per `tests/plan/ledger.md` discipline). New failures need a new row + a target sprint + an owning skill — not "flaky" or "pre-existing".

### 2.3 Pre-classified expected reshapes per facade migration

Each in-scope facade migration may temporarily flip tests red during S66 adoption. The pre-classification:

| Facade migration | Expected reshape pattern | Failure window | Net-new failures? |
|---|---|---|---|
| **D43 split** (FIXME 0150) | Source-imports-of-`cranelisp-runtime` rewrites; tests that depend on `runtime` types via `tests/helpers/` indirectly may fail to compile during transit. /qa's e2e harness (per `tests/CLAUDE.md`) does NOT depend on `cranelisp-runtime` at all — only spawns the `cranelisp` binary — so this pattern should NOT touch e2e tests. Crate-internal unit tests (owned by /dev) move with their crate. | One sprint (S66) | None expected at the e2e tier; unit-tier transitively |
| **FIXME 0098** (ResolutionGap/CheckError/ExpansionError migration) | Compile error if any test imported `cranelisp_types::CheckError` (none should — e2e tests don't import internal types). REPL gap-orchestration retry behaviour observable via subprocess; if int's retry loop regresses, `repl_*.rs` and import-resolution tests will surface. | Possible 1-2 days | None expected at e2e; spec_08_modules tests catch regression |
| **FIXME 0099** (GotObserver) | Backend extension point + int-side ring buffer. Test surface: new e2e tests that activate `CRANELISP_GOT_TRACE=1` and assert observer-fired events appear in stderr (parallel to existing `CRANELISP_IO_TRACE`). NEW tests, not reshapes. | 0 reshapes; new coverage | None |
| **FIXME 0100** (single-consumer relocations) | `CheckError`, `CheckResult`, `ResolutionGap`, `ReplSnapshot`, `CompilationError`, `Got*` types move from `cranelisp-types` to their originating crates. Pure Rust-source path-rewrite; e2e tests (subprocess-only) are insulated. | 0 reshapes at e2e | None |
| **FIXME 0103** (trace.rs/io_trace.rs runtime → int) | The IO observer relocates to `cranelisp-intrinsics` (post-D43); int-side ring buffer + flush guard machinery moves into `src/io_trace/`. Behavioural test: `CRANELISP_IO_TRACE=1` continues to produce the same stderr trace shape pre/post relocation. Tests that assert specific trace dump *line ordering* may need re-baselining; tests that assert *event presence* are stable. | One sprint | Possibly 1-3 line-ordering tests if any exist (search yields none today; new coverage gets `event-presence` assertions, not order-sensitive) |
| **FIXME 0104** (PlatformError adoption) | Error message shape changes from free-floating string to `lib/main.cl:42:7: error: platform "stdio" not found in search path` form. Tests that match on the OLD shape (substring match per `tests/CLAUDE.md` "Error tests use substring matching") need re-baselining to the new shape. **Pre-classified count**: ~3-5 tests in `repl_negative.rs` and `examples.rs` plausibly match on platform-load error strings. | One sprint | ~3-5 reshapes; allowlist in S66 ledger |
| **FIXME 0107** (`OwnedPlatformFnDescriptor` `#[non_exhaustive]`) | Test-side: e2e tests don't construct `OwnedPlatformFnDescriptor`. Unit tests (/dev-owned) inside `cranelisp-platform` may need `..Default::default()` patterns. | 0 reshapes at e2e | None |
| **FIXME 0108** (display.rs backend → int) | Pure Rust-source relocation; output bytes identical. | 0 reshapes | None |
| **FIXME 0150** (D43 implementation) | Phase 4's stdlib trait-impl audit may surface impls that "just worked" because backend's collusion intercepted before the impl body ran. Tests that exercise operators on Int/Float (`(+ 1 2)`, `(let [f +] (f 1 2))`) may regress if a stdlib impl body is wrong. **This is the single highest reshape risk.** | One sprint, possibly more | Up to ~10-15 conformance tests in `spec_04_expressions.rs`, `spec_07_traits.rs`, `spec_06_types.rs`. Pre-classified as "expected reshape from D43 Phase 4 stdlib audit". |
| **FQTypeName threading** (FIXME 0151 — out of S66 scope per SPRINT.md, deferred to S67+) | NOT in S66; gate calibration unchanged. | n/a | n/a |

**Tolerance commitment**: The S66 gate accepts up to **~47 net-new test failures** (the 932 → 906 margin = 26 failures, plus a 21-test allowance against the existing failure set if any S64 failures resolve along the way) before hard-stopping the sprint. Anything past 47 is a Phase 5 close-short trigger. The pre-classification above predicts ~13-23 expected reshapes; well under the 47 envelope.

### 2.4 Verdict

**Gate is calibrated; baseline holds; pre-classified reshapes well within tolerance.** S66 opens with 932/21/6 as the freeze line; close-time accepts ≥ 906 passing, with every failure ledgered or pre-classified.

---

## 3. Facade-conformance test strategy (per facade)

For each of the 8 final-state facades, name how the public surface gets test coverage post-adoption. Coverage discipline is two-tier per `tests/CLAUDE.md`: e2e (owned by `/qa`, in `tests/`) for behaviour-through-the-binary; unit (owned by `/dev`, in `crates/{crate}/src/`) for crate-internal correctness.

### 3.1 `cranelisp-types`

**Public surface coverage strategy.** This is the bottom of the dep DAG; types are data, not behaviour. **Conformance is mostly compile-time** (any consumer crate's `cargo build` exercises the public surface) plus targeted unit tests for the small amount of logic (`apply`, `free_vars`, `format_type_display`, `from_u32` on `SchedulingClass`).

**S66 test-side work**:
- `/dev` (types-narrow) authors unit tests in `crates/cranelisp-types/src/` for the `Type` helper functions (`apply`, `free_vars`, `format_type_display`, `format_type_with_vars`, `type_var_names`, `Type::adt`, `Type::from_name`, `Type::type_name`, `Type::is_io`, `Type::unwrap_io`).
- `/dev` authors `SchedulingClass::from_u32` tests covering known discriminants + ABI-version-drift fallback to `Sequential`.
- `/dev` authors `ErrorLocation` constructor tests (the per-producer-policy table in the facade § "Errors and warnings" producer-side policy).
- **e2e coverage is indirect**: every behaviour test that hits the binary exercises types through type-display in error messages, REPL output (`/sig`, `/info`), and slash-command output. No new e2e tests required.

**Negative coverage**: `Type::from_name(&TypeName::new("Option"))` must return `None` (not the user-defined ADT lookup); `Type::type_name(&Type::ADT(…))` must return `None`. Unit tests assert the returns.

### 3.2 `cranelisp-frontend`

**Strategy.** Free-function surface (`parse`, `extract_module_declarations`, `build_ast`, `build_expr`, `expand`, `parse_preserving_comments`). Per `tests/CLAUDE.md` two-tier rule, test through the binary at e2e tier; unit tests inside the crate cover edge cases.

**S66 test-side work**:
- Existing `repl_*.rs`, `spec_03_syntax.rs`, `spec_04_expressions.rs`, `spec_08_modules.rs`, `spec_09_macros.rs` already cover the e2e behaviour; FIXME-0098-driven migration of `expand` from `src/expander.rs` into `cranelisp-frontend` is a pure-source move, no new e2e coverage required.
- **Per-form-build verification**: §2.1 `parse`-reshape was confirmed landed in S64 (frontend.md lines 16-46). e2e tests already exercise it through `--run` and REPL paths. Verify no regression at S66 close.
- **Macro round-trip via `parse_preserving_comments`**: REPL `/source name` slash command exercises this. e2e coverage in `repl_introspection.rs`.
- **Gap retry contract**: when `expand` returns `Err(ExpansionError::Gap(MacroInMem(fq)))`, int's `process_form` must dispatch + retry. e2e visibility: REPL `(import [m])` followed by `(macro-from-m ...)` exercises the retry path. Coverage in `spec_08_modules.rs` + `spec_09_macros.rs`. **New regression test**: import-then-immediately-use a macro from a freshly registered module — assert it works in one REPL eval (the retry loop completes inside that eval).

### 3.3 `cranelisp-typecheck`

**Strategy.** Free function `check_form` + builtin registration + per-form-pass scaffolding. Behavioural coverage is e2e; per-pass introspection (`CheckPass::Pass1Signatures` vs `Pass2Bodies`) is `/dev`-unit-tier.

**S66 test-side work**:
- e2e: type-error test set in `spec_06_types.rs`, `spec_07_traits.rs`, polymorphism / monomorphisation in `spec_06_types.rs`. Existing coverage carries.
- **Decision 38 + per-symbol mutability**: REPL form-by-form append (`Sess::eval`) must succeed without whole-module re-typecheck after Phase 0 lands (per int.md invariant 16). e2e regression test: `(defn f [] 1)\n(defn g [] (f))\n` REPL transcript completes; both `/list` rows present; `g`'s scheme references `f`'s.
- **Gap-return discipline**: `check_form` MUST NOT block, MUST NOT call scheduler. Test surface impossible at e2e (it's an internal contract); covered at `/dev`-unit tier with an injected fake `SymbolTables` that simulates the not-yet-typechecked state.
- **Negative coverage**: `check_form` against a malformed AST returns `CheckError::TypeError`, not `CheckError::Gap`. e2e exercises through bad-program REPL transcripts.
- **`ReplSnapshot` rollback**: a failed REPL form must not leave residual type-var bindings visible to the next eval. e2e regression: REPL `(defn f [] (+ 1 "x"))` (type error) followed by `(defn g [] 1)` — the second succeeds with no leakage. New test in `repl_lifecycle.rs`.

### 3.4 `cranelisp-backend`

**Strategy.** Three free-function compile entries (`compile_to_module`, `load_object`, `compile_to_object`) + `Code` + `CompilationError` + GOT observer. Coverage is e2e for the compile pipeline (every `--run` and `--link` and REPL eval routes through these); unit tests inside backend cover internal CLIF emission edge cases.

**S66 test-side work**:
- **Decision 41 verification**: per-symbol JIT cardinality is observable via `/clif name` per-symbol output (each name gets distinct CLIF). e2e: `repl_introspection.rs` already exercises `/clif`; verify no regression.
- **`compile_to_module` direct-write pattern**: backend writes `Code::Jit` and `Introspection` directly into shared stores via `&self`-interior-mutable `write_code(&self, sym, code)`. **Cannot be observed e2e directly** (it's an internal contract). Covered at `/dev`-unit tier with a unit test in `cranelisp-backend/src/` that calls `compile_to_module` against a stub `SymbolTable<Code, ()>` and asserts the entry's `code: Some(Code::Jit { … })` post-call.
- **`SymbolNotCompilable` error variant** (per §2.7 / FIXME 0098 typed error): /dev-unit test in backend asserts the variant fires when caller passes a name with `kind == Overloaded` or `ast: None`.
- **GotObserver** (FIXME 0099): NEW e2e test set:
  - `CRANELISP_GOT_TRACE=1 cranelisp --run …` produces stderr trace with `JitWrite`/`LinkerWrite` events. New test in a fresh `tests/got_trace.rs` (parallel to `io_trace`-shaped tests).
  - REPL redefinition fires `Redefinition` event. e2e coverage in same file.
  - Production batch (no env var, no REPL) does NOT register the observer (zero-overhead claim). Verify by absence of trace output.
- **`load_object` cache-hit path**: e2e in `cache.rs` already exercises (cache hit produces same output as cache miss).
- **Object file contract** (`compile_to_object` output): e2e in `link.rs` and `build_confidence.rs` mode-equivalence tests already exercise via `--link` mode.
- **Bare-name + Local linkage** (Decision 36): `link.rs` linker-command tests verify; existing.

### 3.5 `cranelisp-platform`

**Strategy.** DLL ABI + host callbacks + `OwnedPlatformFnDescriptor` + manifest loader. Two-faced surface: DLL-author API (tested by stdlib's platforms `cranelisp-stdio`, `cranelisp-test-capture`) and host-side API (consumed by int). e2e tests exercise platforms end-to-end via `(platform "stdio")` declarations in `--run` programs.

**S66 test-side work**:
- e2e: existing `spec_10_io.rs` and `examples.rs` exercise `(platform "stdio")` and `(platform "test-capture")`. Carries.
- **`PlatformError` adoption** (FIXME 0104): error-message reshape from `String` to structured `LineCol`-bearing form. **e2e reshape**: `repl_negative.rs` and any test that asserts on platform-load error substrings. **Action**: at S66 facade-adoption time, /qa re-runs the e2e suite, identifies each `PlatformError`-carrying test, updates substring matches to the new shape (e.g., `error: platform "stdio" not found in search path` rather than the older `Failed to load platform: …`). **Pre-classified count**: ~3-5 tests; ledgered as expected reshape per §2.3.
- **`OwnedPlatformFnDescriptor` `#[non_exhaustive]`** (FIXME 0107): /dev-unit test inside `cranelisp-platform` confirming external construction by struct-literal fails to compile (use a doc-test with `compile_fail`).
- **`HostContext::dispatch` removal verification** (§2.13): the function never existed in source; facade truth-telling. No test work.
- **`load_manifest` ABI version mismatch**: e2e via a synthetic mismatched DLL fixture. NEW test in `tests/platform_abi.rs` (or extend `examples.rs`) that builds a fake DLL with stale `ABI_VERSION` and asserts `PlatformError::AbiVersionMismatch` surface in `--run` mode.
- **`declare_platform!` macro** (DLL-author API): exercised transitively by every platform DLL the stdlib + tests use. No new test work.

### 3.6 `cranelisp-intrinsics`

**Strategy.** Backend-emitted-call targets — every `#[no_mangle] extern "C" fn` is invoked by JIT-emitted code. Coverage is **always indirect via behaviour**: any test that allocates heap, ref-counts, runs IO, panics, etc. exercises intrinsics. Plus the IO observer extension point.

**S66 test-side work**:
- e2e: `spec_12_runtime.rs` exercises RC + heap; `spec_10_io.rs` exercises trampoline; existing.
- **`register_io_observer` concurrency contract** (per intrinsics.md §"IO observation"): "Replaces the current observer atomically. Thread-safe from any thread; last write wins under happens-before ordering." **Cannot be tested e2e** directly. Covered at `/dev`-unit tier:
  - **Stress test inside `cranelisp-intrinsics`**: spawn N threads, each calling `register_io_observer(Some(…))` repeatedly; concurrently spawn another N threads each producing `IoEvent` dispatches; assert no UB (loom or shuttle-style if practical; otherwise repeated stress under TSAN). **NEW test infrastructure**: add `[dev-dependencies] loom = "0.7"` (or equivalent) to `cranelisp-intrinsics`; new test file `crates/cranelisp-intrinsics/src/io_observer/concurrency_test.rs` under `#[cfg(loom)]`.
  - **Last-writer-wins assertion**: after N concurrent `register_io_observer` calls, exactly one observer is current; subsequent events route to it.
- **`HeapString` layout invariant**: /dev-unit test verifying `HeapString.len` matches `read_string_as_str` byte count; tests live in intrinsics crate.
- **`runtime_panic` thread-local sentinel** (per spec §12.7.2): e2e in `spec_12_runtime.rs` (match-exhaustiveness panic). Existing.
- **`alloc_count`, `dealloc_count` accessors**: `/mem` slash command reads them; e2e via REPL `/mem` in `repl_introspection.rs`. Existing.
- **D43 split in intrinsics**: coverage is implicit in the e2e reshape — every `--run` and `--link` test must continue to work post-relocation. `--link` linker-archive update (linking against `cranelisp-intrinsics.a` instead of `cranelisp-runtime.a`) is part of FIXME 0150 Phase 5. /qa runs full e2e suite at each FIXME-0150 phase boundary; failures map to "crate-relocation in transit" in the ledger.

### 3.7 `cranelisp-primitives`

**Strategy.** User-callable extern fns — `(add-i64 1 2)` direct calls, plus operator-as-value `(let [f +] (f 1 2))` via GOT slots, plus backend's optional inline-CLIF substitution. Coverage is e2e through every arithmetic / conversion test.

**S66 test-side work**:
- e2e: `spec_04_expressions.rs` arithmetic suite, `spec_06_types.rs` conversion suite. Existing.
- **D43 trait-knowledge deletion in stdlib audit** (FIXME 0150 Phase 4): the highest reshape risk per §2.3. /qa runs full e2e suite at the FIXME-0150-Phase-4 boundary; surfaces any stdlib impls that "just worked" because backend's collusion intercepted before the impl body ran. **Test infrastructure**: a new `tests/stdlib_trait_impls.rs` that exercises every operator on every primitive type via the explicit `(impl Num Int)` path — the test serves as the regression guard for the audit. Pre-classified ~10-15 tests if the audit surfaces empty/circular impls; ledgered as expected reshapes.
- **Operator-as-value path**: REPL transcript `(let [f +] (f 1 2))` returns 3. e2e in `spec_04_expressions.rs` (verify existing coverage; add explicit row in `tests/plan/PLAN.md` if not).
- **GOT-slot indirection**: covered transitively by operator-as-value tests above.
- **No trait knowledge in backend**: structural — verifiable via `cargo public-api` on backend (no `(TraitName, Symbol, TypeName) → PrimitiveOp` map types in the public surface). The `api-check` gate is the discriminator.

### 3.8 `cranelisp` (binary / int)

**Strategy.** Largest facade; integration layer. e2e tier IS the conformance check for the binary's public CLI + REPL surface. Internal `CompilerSession` methods (`process_form`, `insert_symbol`, `eval`, `trampoline`, `link_by_name`) are exercised via subprocess invocation.

**S66 test-side work**:
- e2e: 25 active e2e files (per `tests/CLAUDE.md`) cover the bulk. Carries.
- **Decision 41 receive-side** (per int.md §"`Code` — the per-entry retention root"): per-symbol JIT loop replaces the old worker post-loop. e2e: REPL redefinition + `/clif` of redefined symbol returns the NEW CLIF, not stale. New row in `repl_introspection.rs` if not already covered.
- **`process_form` gap-orchestration retry loop**: covered transitively by import + macro tests in `spec_08_modules.rs`, `spec_09_macros.rs`. **NEW regression coverage** for the orchestrator-side macro-vs-fn discrimination after `wait_for_typecheck_symbol` (per int.md gap design rationale): a test where a typechecked-but-not-yet-jitted **function** is referenced — orchestrator must NOT speculatively JIT it (verify by inspecting `/clif name` is empty until the function's first actual call, OR via `CRANELISP_GOT_TRACE=1` showing no `JitWrite` event fires from the speculative path). Covered in new `tests/process_form_dispatch.rs` or extension of `repl_lifecycle.rs`.
- **`SharedState` vs `CompilerSession` split** (Decision 38): structural; verified at compile-time + by `cargo public-api`.
- **Cache-hit decision** (Decision 37): cache.rs e2e tests already exercise; carries.
- **`--link` mode `_main` alias** (Decision 36): `link.rs` already covers; carries.
- **Mutual-import deadlock** (Decision 30): documented as known constraint; e2e regression test exists in `spec_08_modules.rs` asserting `SchedulerError::Cycle` surfaces (not deadlock).
- **`Code::Jit` and `Code::Linker` retention dissolves on session shutdown** (Decision 31 + Custom Drop): e2e via memory-leak detection or via repeated REPL session start/stop in a stress harness. **NEW infrastructure**: `tests/lifecycle.rs` exercises N session create / destroy cycles + asserts via `/mem` accessor that `bytes_current` returns to baseline. Defers to S67+ if stress-test framework not yet ready.
- **Display surface arrival** (FIXME 0108): pure source relocation. e2e coverage via existing `/sig`, `/type`, `/info`, `format_eval_result` paths in `repl_introspection.rs`. Carries.
- **Trace + io_trace arrival** (FIXME 0103): per FIXME 0099 + 0103, the consumer-side ring buffers move from `cranelisp-runtime` to `src/io_trace/` + `src/scheduler_trace/` + `src/got_trace/`. e2e coverage: `CRANELISP_IO_TRACE=1`, `CRANELISP_GOT_TRACE=1` (new), and the existing scheduler-trace activation paths produce stderr output. Existing tests in `spec_10_io.rs` and similar carry; new `tests/got_trace.rs` adds.
- **`regenerate_backing_file` + `defn_order` discipline** (per Decision 39): e2e via REPL `/reload` transcripts. Existing.

---

## 4. Cross-crate migration test impact (per in-scope FIXME)

For each in-scope FIXME (0098, 0099, 0100, 0103, 0104, 0107, 0108, 0150), name which existing tests are at risk and which need new tests.

### 4.1 FIXME 0098 — ResolutionGap / CheckError / ExpansionError migration

**Risk to existing tests**: low. The migration is internal — `expand` moves from `src/expander.rs` to `cranelisp-frontend/src/expand.rs`; types relocate. e2e tests don't import internal types.

**New tests needed**:
- Macro-immediately-after-import regression test (per §3.2 above).
- `process_form` retry-loop concurrency: two concurrent REPL workers waiting on the same FQ-symbol gap shouldn't double-register the module. /dev-unit test in int crate (or new e2e stress).

### 4.2 FIXME 0099 — GotObserver implementation

**Risk to existing tests**: zero (new extension point).

**New tests needed**:
- `tests/got_trace.rs` — new e2e file mirroring `io_trace`-shape tests:
  - `got_trace_emits_jit_write_event`
  - `got_trace_emits_linker_write_event_on_cache_hit`
  - `got_trace_emits_redefinition_event_on_repl_redefn`
  - `got_trace_off_path_zero_overhead` (asserts no env-var = no observer registered = no stderr trace)
- /dev-unit tests inside `cranelisp-backend`: observer concurrency contract (parallel to intrinsics' `register_io_observer` stress per §3.6).

### 4.3 FIXME 0100 — single-consumer relocations

**Risk to existing tests**: zero at e2e (subprocess-only); transitive at unit tier (path rewrites for any `/dev`-unit test that imported the relocated types from `cranelisp-types`).

**New tests needed**:
- Verification at `cargo public-api` gate: relocated types appear in their NEW homes (`cranelisp-typecheck`, `cranelisp-backend`) and are GONE from `cranelisp-types`. The `api-check` IS the test for this FIXME.

### 4.4 FIXME 0103 — trace.rs / io_trace.rs runtime → int

**Risk to existing tests**: medium. `CRANELISP_IO_TRACE=1` stderr output may shift in line ordering or frame discipline as ring buffers move. Tests asserting **event presence** are stable; tests asserting **specific line ordering** may need re-baselining. Search of `tests/` for `IO_TRACE` substring matches: ~5-10 tests in `spec_10_io.rs` and `regression.rs`.

**New tests needed**:
- Trace-output-shape regression: a "snapshot test" that pins the canonical trace dump shape for a representative IO program. Snapshot file `tests/fixtures/io_trace_snapshot.txt` (or inline string assert). Updates in lockstep with FIXME 0103 close — pre/post commit must show byte-equivalent snapshot.
- D43-split observer location verification: post-FIXME 0150, the observer registration moves from `cranelisp-runtime` to `cranelisp-intrinsics`. Verification is `cargo public-api`-mediated.

### 4.5 FIXME 0104 — PlatformError adoption

**Risk to existing tests**: medium. Error-substring tests against the OLD platform-load error shape need re-baselining. **Pre-classified count: ~3-5 tests** per §2.3.

**New tests needed**:
- `tests/platform_errors.rs` — new e2e file:
  - `platform_load_failed_carries_form_span` — assert error contains `lib/main.cl:42:7:` style location prefix
  - `platform_manifest_not_found_carries_dll_path`
  - `platform_abi_version_mismatch_emits_expected_vs_found` (uses synthetic stale-ABI fixture per §3.5)
  - `platform_dispatch_error_during_run_carries_fn_name`

### 4.6 FIXME 0107 — `OwnedPlatformFnDescriptor` `#[non_exhaustive]`

**Risk to existing tests**: zero at e2e.

**New tests needed**:
- /dev-unit `compile_fail` doc-test inside `cranelisp-platform` (per §3.5).

### 4.7 FIXME 0108 — display.rs backend → int

**Risk to existing tests**: zero. Pure source relocation; output bytes identical.

**New tests needed**: none.

### 4.8 FIXME 0150 — runtime split (D43)

**Risk to existing tests**: high (see §2.3). The Phase 4 stdlib trait-impl audit is the load-bearing risk: ~10-15 conformance tests in `spec_04`, `spec_06`, `spec_07` may regress if a stdlib impl's body was relying on backend's `(TraitName, Symbol, TypeName) → primitive` collusion.

**New tests needed**:
- `tests/stdlib_trait_impls.rs` — an explicit-coverage suite that exercises every operator on every primitive type via the binding `(impl Num Int)` / `(impl Eq Int)` / `(impl Ord Int)` / `(impl Display Int)` paths and on Float counterparts. Acts as the regression guard for the Phase 4 audit.
- `--link` linker-archive update verification: post-Phase 5 (runtime crate retired), `--link` mode must link against `cranelisp-intrinsics.a` + `cranelisp-primitives.a` instead of `cranelisp-runtime.a`. Existing `link.rs` tests verify by passing.
- /dev-unit at the new crate-skeleton boundaries: assertions that `cranelisp-primitives` does NOT depend on `cranelisp-intrinsics` (per facades — siblings, not coupled). Verifiable via `cargo tree` in CI.

---

## 5. Sizing

Rough sizing per work-item, suitable for `/sprint` to fit into S66 wave envelopes.

| Work-item | Sizing | Notes |
|---|---|---|
| `cargo public-api` baselines + CI gate (§1) | ~1 day | 8 baselines + xtask + docs |
| 95% gate calibration commitment in SPRINT.md (§2) | 1 hour | Doc work; freezes baseline |
| New `tests/got_trace.rs` (FIXME 0099 §4.2) | ~1 day | 4 e2e tests + harness wiring |
| New `tests/platform_errors.rs` (FIXME 0104 §4.5) | ~1 day | 4 e2e tests + synthetic stale-ABI fixture |
| Re-baselining ~3-5 platform-error substring tests (FIXME 0104) | ~half day | Edits in `repl_negative.rs`, `examples.rs` |
| New `tests/stdlib_trait_impls.rs` (FIXME 0150 §4.8) | ~2 days | Comprehensive operator × type matrix; serves as Phase 4 audit guard |
| Trace-output-shape snapshot regression (FIXME 0103 §4.4) | ~half day | Snapshot fixture + assertion |
| New `tests/process_form_dispatch.rs` (orchestrator gap retry, §3.8) | ~1 day | 2-3 e2e tests with `CRANELISP_GOT_TRACE` introspection |
| New `tests/lifecycle.rs` (Decision 31 retention dissolves) | ~1 day | OR defer to S67+ if stress framework not ready |
| New `tests/platform_abi.rs` (ABI mismatch) | ~half day | Synthetic stale-DLL fixture |
| ReplSnapshot rollback regression (§3.3) | ~half day | New row in `repl_lifecycle.rs` |
| `tests/CLAUDE.md` updates (drift workflow + new test files) | ~half day | Doc work |
| `tests/plan/PLAN.md` row additions for every new test (per `tests/CLAUDE.md` "No test is silently dropped") | ~1 day | Lockstep with test landing |
| `tests/plan/ledger.md` updates per pre-classified reshape | ~1 day | Per FIXME 0150 Phase 4 audit + FIXME 0104 reshape |
| /dev-unit work (intrinsics observer concurrency, types helpers, backend SymbolNotCompilable, platform compile_fail) | ~2-3 days, /dev-owned | NOT /qa work; tracked here for cross-skill visibility |

**Total /qa-owned work**: ~10-12 days of test + plan + doc work, fits comfortably within an S66 wave envelope alongside the /dev adoption work.

---

## 6. Cross-crate dependencies (bilateral)

This /qa slice's test-surface-impact rows align with the per-crate `/design` slices' "Test surface impact" sections per the Phase-2-review template §3.2 row 5. Bilateral cross-references:

| This slice's item | Depends on / aligns with | In the other crate's slice |
|---|---|---|
| `cargo public-api` baselines (§1.1) | Each /design (crate) authors and freezes their facade in S65; their slice generates the baseline at adoption time | `design/{crate}/implementation-slice-s66.md` §5 "Test surface impact" — each names the baseline-generation step |
| 95% gate pre-classified reshapes (§2.3) | Each /design (crate) slice scopes which existing tests its adoption may shift | `design/{crate}/implementation-slice-s66.md` §5 — names the test-side reshape per delta row |
| `tests/got_trace.rs` new file (§4.2) | /design (backend) implements observer; /design (int) implements ring buffer | `design/backend/implementation-slice-s66.md` §5 (FIXME 0099 backend phase); `design/int/implementation-slice-s66.md` §5 (FIXME 0099 int phase) |
| `tests/platform_errors.rs` (§4.5) | /design (platform) lands `PlatformError`; /design (int) consumes via `format_error` | `design/platform/implementation-slice-s66.md` §5; `design/int/implementation-slice-s66.md` §5 |
| `tests/stdlib_trait_impls.rs` (§4.8) | /design (primitives) + /design (intrinsics) Phase 4 stdlib audit | `design/primitives/implementation-slice-s66.md` §5; `design/intrinsics/implementation-slice-s66.md` §5; runtime-retiring slice §5 |
| `tests/process_form_dispatch.rs` (§3.8) | /design (frontend) FIXME 0098 Phase 2; /design (int) FIXME 0098 Phase 4 | `design/frontend/implementation-slice-s66.md` §5; `design/int/implementation-slice-s66.md` §5 |
| Trace-snapshot regression (§4.4) | /design (intrinsics) IO observer relocation; /design (int) ring-buffer relocation | `design/intrinsics/implementation-slice-s66.md` §5; `design/int/implementation-slice-s66.md` §5 |
| `tests/platform_abi.rs` (§4.5) | /design (platform) ABI handling | `design/platform/implementation-slice-s66.md` §5 |
| /dev-unit observer concurrency (§3.6, §4.2) | /dev-owned (per `memory/feedback_unit_tests_with_dev.md`) | `design/intrinsics/implementation-slice-s66.md` §5; `design/backend/implementation-slice-s66.md` §5 |

**Count: 9 cross-crate dependency rows.** Each /design (crate) slice has at least one corresponding row in this /qa plan; /qa has one row corresponding to every /design (crate) slice that touches the user-visible surface.

If any bilateral row above does not appear in the corresponding /design (crate)'s §5, /qa files an `/arch` FIXME at W4b cross-cutting check time. The bilateral table is the gate for "everyone agrees what tests cover what".

---

## 7. Test infrastructure uplift

Per `legacy/substance-action-plan.md` Step-4 row for `/qa`: *"First-wave slice of integration + e2e infrastructure uplift; coverage tests for the substance commitments landing in Sprint 66."*

### 7.1 Infrastructure changes

- **`tests/helpers/e2e.rs` Cranelisp builder** — extensions for S66:
  - `.with_env(key, value)` — explicit env-var injection for trace gates (`CRANELISP_GOT_TRACE`, `CRANELISP_IO_TRACE`, etc.). May already exist; verify.
  - `.expect_stderr_substring(s)` — convenience over the existing `cap.stderr.contains(s)` pattern; reduces boilerplate in error-shape tests.
  - `.with_synthetic_dll(spec)` — for `tests/platform_abi.rs`; constructs a fake DLL fixture under the per-test tmpdir with caller-controllable `ABI_VERSION` + manifest contents. NEW helper requiring buildscript discipline; defers to /qa-design at infrastructure-uplift time if non-trivial.

- **`tests/helpers/snapshot.rs` (new module)** — for FIXME 0103's trace-output-shape snapshot regression. Pattern:
  ```rust
  pub fn assert_snapshot(actual: &str, fixture_path: &str);
  // Reads tests/fixtures/{fixture_path}, compares; on UPDATE_SNAPSHOTS=1, rewrites.
  ```
  Lightweight — does NOT pull `insta` (per `tests/CLAUDE.md` minimalism); plain `std::fs` + diff. Single-snapshot file pattern.

- **`tests/helpers/regex.rs`** — already exists; named regex library. Add patterns for new error shapes:
  - `PLATFORM_ERROR_LOAD_FAILED` — `r"error: platform .* not found in search path"` family
  - `PLATFORM_ERROR_ABI_MISMATCH` — `r"error: platform .* ABI version mismatch \(expected .*, found .*\)"`
  - `GOT_TRACE_JIT_WRITE` — for the new got_trace stderr format
  - `GOT_TRACE_REDEFINITION`

- **`tests/got_trace.rs`** — new e2e file. Mirrors existing IO-trace-shape tests.

- **`tests/platform_errors.rs`** — new e2e file.

- **`tests/stdlib_trait_impls.rs`** — new e2e file.

- **`tests/platform_abi.rs`** — new e2e file (or extension of `examples.rs` if synthetic-DLL fixture is too heavy for a separate suite).

- **`tests/process_form_dispatch.rs`** — new e2e file (or new section in `repl_lifecycle.rs`).

- **`tests/lifecycle.rs`** — new e2e file for Decision-31 retention regression. May defer to S67+ if stress framework needs work.

### 7.2 New helpers

Listed in §7.1. Total ~3-4 new helper additions to `tests/helpers/e2e.rs` + 1 new helper module (`snapshot.rs`).

### 7.3 Deprecations

None at this level. The S64 migration to two-tier (e2e or unit, no middle) completed in S64 Phase 3; `tests/helpers/mod.rs::ReplSession` was deleted. No further deprecation work in S66.

### 7.4 Spec-link-check linter (existing, runs in lockstep)

`tests/plan/spec_link_check.py` (per `tests/CLAUDE.md`): every new `// spec:` annotation in S66's new test files MUST pass the linter. Run before commit:
```bash
python3 tests/plan/spec_link_check.py
```

S66 introduces ~6-8 new test files (per §7.1) carrying ~30-50 new `// spec:` annotations. The linter run is a S66 close-gate item.

### 7.5 Pre-commit / CI integration (carry-forward)

`tests/CLAUDE.md` notes: *"Pre-commit / CI integration is a future commitment, not a Sprint 64 deliverable."* S66 does NOT make it a deliverable either; tracked as an out-of-scope item per `sprints/SPRINT.md` § Out-of-scope.

---

## 8. Open questions

Where the facade or the FIXME body left ambiguity that affects test scope, /qa surfaces here for `/arch` to resolve at W4b cross-cutting check time. Each open question would file a `target: /arch` FIXME if not resolved.

### Q1 — `cargo public-api` tooling: monorepo or per-crate?

The plan §1 assumes per-crate `public-api.txt` baselines. Some workspaces use a single workspace-level baseline. /qa needs to know which shape to plan against. Recommend per-crate per Principle 13 (`interfaces.md` per-crate auditability).

**Resolution path**: /arch confirms in W4b cross-cutting check, OR `/sprint` decides at S66 wave-plan time.

### Q2 — Is `tests/lifecycle.rs` (Decision 31 retention) S66 work or S67+?

The `bytes_current` returns to baseline assertion requires either reliable tooling OR a memory-leak detector. /qa can land a coarse-grained version in S66 (REPL session create/destroy ×100 + assertion that `/mem` `bytes_current` doesn't grow monotonically) but a tight assertion may need /platform's allocator instrumentation infrastructure.

**Resolution path**: /qa lands the coarse version in S66 unless /sprint defers; tight version filed as a future FIXME if coarse insufficient.

### Q3 — Concurrency stress for `register_io_observer` / `register_got_observer`: loom or shuttle?

`tests/CLAUDE.md` does not currently sanction either crate. /qa/dev-tier introduces a loom or shuttle dep on `cranelisp-intrinsics` and `cranelisp-backend` for the observer concurrency contracts (§3.6, §4.2). Choice between the two is a /dev-decisions question; /qa flags here so /sprint sees it.

**Resolution path**: /dev (intrinsics) chooses at FIXME 0099 / IoObserver implementation time; /qa accepts the choice.

### Q4 — Does the 95% gate include `/dev`-tier unit tests, or only /qa-owned e2e?

§2 above calibrates against the e2e suite (953 tests). Crate-internal unit tests are owned by /dev (per `memory/feedback_unit_tests_with_dev.md`). Whether the 95% gate aggregates both tiers OR runs separately matters for sprint close. /qa recommends: **track separately, gate separately**. e2e gate is the user-facing release gate; unit gate is per-crate /dev's responsibility.

**Resolution path**: /sprint clarifies at SPRINT.md drafting; /qa takes default of "separate" unless told otherwise.

### Q5 — Pre-classified reshape allowances: reserved budget vs. discovered?

§2.3 pre-classifies expected reshape counts per FIXME (~3-5 platform-error, ~10-15 stdlib-trait-impl). If actual count exceeds the pre-classified budget at adoption time, what's the trigger? /qa proposes: **adoption-phase mid-sprint check** at end of Wave 1 of S66 — count actual vs. pre-classified, escalate to /sprint Phase-5 close-short if outside the 47-test envelope.

**Resolution path**: /sprint S66 Phase-3 plan reflects the mid-sprint check; /qa includes the check as a wave acceptance criterion.

### Q6 — FIXME 0150 (D43) sequencing: Wave 0 of S66 OR S67+?

Per `legacy/substance-action-plan.md` §F4 finding, /arch recommended deferring D43 implementation to S66 or a dedicated sprint. SPRINT.md's `Out-of-scope` line ("FIXME 0150 — *implementation* — S66 facade adoption" implicit) suggests S66. If D43 lands as Wave 0 of S66, the test-side reshape (§4.8) anchors that wave; if D43 defers to S67+, this slice's §4.8 work likewise defers.

**Resolution path**: /sprint S66 Phase-3 plan resolves at wave-planning boundary. /qa scopes for both contingencies (the §4.8 work is self-contained whichever way it sequences).

---

## Cross-references

- `design/arch/sprint-65-reshape-phase-2-review.md` §3 — slice template (adapted here for /qa)
- `design/arch/sprint-65-legacy-triage.md` — F1 (Step 4 retro), F4 (D43 sequencing) findings
- `design/arch/legacy/substance-action-plan.md` Step-4 row for /qa
- `tests/CLAUDE.md` — two-tier strategy, helper API, fresh-tmpdir discipline, isolation protocol
- `tests/plan/PLAN.md` — normative spec → tests bridge
- `tests/plan/ledger.md` — failure ledger, S64-close baseline 932/21/6
- `sprints/SPRINT.md` § Hard constraints — facade-final commitment, 1-3 narrow editorial revisions tolerance
- `sprints/archive/sprint-64.md` — Phase-6 reconciliation that produced the freeze line
- `memory/feedback_failing_not_ignored.md` — failing-not-ignored discipline
- `memory/project_test_strategy.md` — two-tier discipline
- `memory/feedback_repros_join_suite.md` — every reduction joins as a committed failing test
- `memory/feedback_unit_tests_with_dev.md` — /qa owns e2e in `tests/`; /dev owns unit in `crates/{crate}/src/`
- `design/arch/fixmes/0098`, `0099`, `0100`, `0103`, `0104`, `0107`, `0108`, `0150` — the eight in-scope FIXMEs scoped per §4
- `design/arch/facades/{types,frontend,typecheck,backend,platform,intrinsics,primitives,int}.md` — the eight final-state facades scoped per §3
