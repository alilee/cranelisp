# Sprint 66 implementation slice — `/qa` test plan

**Status.** revised post-Phase-2 (D43 bound; FIXME 0152 closed)
**Author.** `/qa`, 2026-05-06; revised 2026-05-07
**Reads.** all eight final-state facades (`design/arch/facades/{types,frontend,typecheck,backend,platform,intrinsics,primitives,int}.md` after S65 close), `design/arch/sprint-65-reshape-phase-2-review.md` §3 (slice template — adapted for `/qa`), `design/arch/sprint-65-legacy-triage.md` (carryforward FIXMEs into S66 scope), `design/arch/legacy/substance-action-plan.md` Step-4 row for `/qa` ("First-wave slice of integration + e2e infrastructure uplift; coverage tests for the substance commitments landing in Sprint 66"), `tests/CLAUDE.md`, `tests/plan/PLAN.md`, `tests/plan/ledger.md`, `sprints/SPRINT.md` § Hard constraints + § Architecture review (Phase 2), `sprints/archive/sprint-64.md` Phase-6 reconciliation, `memory/feedback_failing_not_ignored.md`, `memory/project_test_strategy.md`.

**Phase-2 revisions binding into this slice (2026-05-07).**
- /sprint resolved D43 (FIXME 0150) into S66 scope per /arch Option A. The "if D43 defers" fork in §2.3 + §4.8 is removed; primitives + intrinsics crate baselines (§1.1) are LIVE, not conditional.
- FIXME 0103's "Phase 1 home" question is resolved: the IoObserver registration site lands in `cranelisp-intrinsics` per /arch Phase-2 selection (bundled with D43 Phase 2). §3.6 + §4.4 below align.
- /arch Phase 2 verdict §3 calls out the `process_form` shape-pivot triad (frontend row 7 + typecheck row 1 + int row 3) as the load-bearing critical path; same-wave landing required.
- Phase 6 (user-facing assessment) waived for this sprint by user direction (per SPRINT.md "Out of scope"). /qa Phase 7 reporting closes the loop directly.
- FIXME 0152 (this slice's §1 baseline-ownership editorial) closed in the same change set as this revision.

This slice scopes the **test-side** of S66 facade adoption. S66 lands per-crate facade conformance against the binding S65 facade set + D43 runtime split; this plan scopes the test-suite work that gates that adoption. Authoring follows the slice template adapted from `design/arch/sprint-65-reshape-phase-2-review.md §3.2` for `/qa`'s deliverable.

---

## 1. `cargo public-api` integration plan

S66 is the first sprint where every facade is binding. `cargo public-api` becomes the mechanical drift detector between as-designed (the facade `.md` file) and as-built (the crate's actual public surface). The integration plan:

### 1.0 Prerequisites

**Toolchain.** `cargo public-api` requires the **nightly Rust toolchain**. Each developer environment + CI runner must have nightly installed:

```bash
rustup toolchain install nightly
cargo +nightly install cargo-public-api
```

The `cargo xtask api-check` (or `just api-check`) wrapper must invoke `cargo +nightly public-api` explicitly to avoid silent failure if the host's default channel is stable. Documented in `tests/CLAUDE.md` § "Public-API enforcement" + the slice's §1.4 sizing.

### 1.1 Per-crate baselines

One `public-api.txt` baseline per crate, checked into the crate's directory. **Triad ownership** (FIXME 0152 closure, per /arch Phase 2 verdict revision #4):

- **`/dev`** runs `cargo +nightly public-api > crates/{crate}/public-api.txt` once the facade-conformant change is implemented; commits the per-crate `public-api.txt` in the same change set as the source change.
- **`/design` (per crate)** verifies the regenerated baseline matches the facade target — no scope creep, no accidental surface widening — and stamps verification in the design slice's "implementation status" row.
- **`/review`** approves the baseline diff against `/arch`'s facade approval in the same change set as the facade-conformant landing.

This is the standard triad pattern (`/design` → `/dev` → `/review`); baseline regeneration is a tooling action that belongs to `/dev`, not to `/design` (which authors but does not edit source artefacts).

| Crate | Baseline path | `/dev` workstream that lands the baseline | Notes |
|---|---|---|---|
| `cranelisp-types` | `crates/cranelisp-types/public-api.txt` | Wave 0 (`/arch` types-crate authoring) → `/dev` (types-narrow) regenerates after the new enums (`ResolutionGap`, `PlatformError`) land | Largest baseline; FQTypeName threading deferred to S67+, but `PlatformError` + `ResolutionGap` surface here this sprint. `CheckResult`/`CheckError`/`ReplSnapshot`/`CompilationError`/`Got*` types REMOVE from this baseline (FIXME 0100 Phase 1+2). |
| `cranelisp-frontend` | `crates/cranelisp-frontend/public-api.txt` | `/dev` (frontend) at FIXME 0098 Phase 2 close | Per facade §"Free functions" — `parse`, `extract_module_declarations`, `build_ast`, `build_expr`, `expand`, `parse_preserving_comments`, `next_synthetic_span`, `parse_defmacro`, `synthesize_macro_clause_defn`, `is_defmacro`, `is_begin`, `flatten_begin`, `expand_quasiquotes`. Plus DTOs: `StructuralDecls`, `DefmacroInfo`, `ExpansionError`. |
| `cranelisp-typecheck` | `crates/cranelisp-typecheck/public-api.txt` | `/dev` (typecheck) at FIXME 0098 Phase 3 + 0100 Phase 1 close | Per facade §"Free function" — `check_form`, `register_builtins`, `CheckResult`, `CheckError`, `ReplSnapshot`, `CheckState`, `TypeCheckEnv`, `CheckPass`, trace install hook. Receives types relocated from `cranelisp-types` (FIXME 0100 Phase 1). |
| `cranelisp-backend` | `crates/cranelisp-backend/public-api.txt` | `/dev` (backend) at FIXME 0099 + 0100 Phase 2 + 0150 Phase 3 close | Per facade — `compile_to_module`, `load_object`, `compile_to_object`, `Code`, `Jit`, `Linker`, `LinkerArtefact`, `ObjectArtefact`, `CompilationError`, `GotEvent{Tag,}`, `GotProvenance`, `GotObserver`, `register_got_observer`. Receives `CompilationError` + `Got*` from types (FIXME 0100 Phase 2). Trait-knowledge maps DELETE per FIXME 0150 Phase 3 — backend's surface SHRINKS net of new GOT observer entries. |
| `cranelisp-platform` | `crates/cranelisp-platform/public-api.txt` | `/dev` (platform) at FIXME 0104 + 0107 close | DLL ABI types (`#[repr(C)]` exempt from `#[non_exhaustive]` per Principle 14) + `OwnedPlatformFnDescriptor` (now `#[non_exhaustive]` per FIXME 0107) + `load_manifest` + `parse_type_sig` + `derive_jit_name` + `HostContext`/`HostCallbacks` + `IO_TAG_*` consts + `declare_platform!` macro |
| `cranelisp-intrinsics` | `crates/cranelisp-intrinsics/public-api.txt` | `/dev` (intrinsics) at FIXME 0150 Phase 1 (skeleton) + Phase 2 (sources move in) close | **NEW baseline — LIVE in S66 (D43 bound per Option A; no longer conditional).** Every `#[no_mangle] extern "C" fn` (RC, drop-glue, allocator, IO trampoline, panic) plus `IoEvent`, `IoEventTag`, `IoObserver`, `register_io_observer`, `trace_anchor`, `HeapString`, stats accessors. The IoObserver registration site lives here (per /arch revision #3 — bundled with D43 Phase 2; FIXME 0103 Phase 1 home is intrinsics, not runtime). |
| `cranelisp-primitives` | `crates/cranelisp-primitives/public-api.txt` | `/dev` (primitives) at FIXME 0150 Phase 1 (skeleton) + Phase 2 (sources move in) close | **NEW baseline — LIVE in S66 (D43 bound per Option A; no longer conditional).** Every `#[no_mangle] extern "C" fn` (integer, float, bool, conversions). No structs / enums. The `cranelisp_op_*` duplicates DELETE per FIXME 0150 Phase 4. |
| `cranelisp` (binary / int) | `crates/cranelisp-exe-bundle/public-api.txt` (or `src/public-api.txt`) | `/dev` (int) at FIXME 0098 Phase 4 + 0099 Phase 2 + 0103 Phase 2 + 0108 + 0150 Phase 5 close | Largest surface; `CompilerSession` methods, `SharedState`, `CompileScheduler`, `ObjectCache`, `EvalResult`, `CommandResult`, `SlashCommand`, `SymbolInfo`, `SymbolDescription`, `Introspection`, line-editor types, watcher events, CLI parsing, `IoTraceFlushGuard`, `SchedulerTraceFlushGuard`, `CacheWritePacket`, `TracedFnInfo`. Receives `display.rs` from backend (FIXME 0108) + `trace.rs`/`io_trace.rs`/`got_trace.rs` ring-buffer machinery. |

**Confirmed 8-crate baseline list** (D43-bound, per Option A): `cranelisp-types`, `cranelisp-frontend`, `cranelisp-typecheck`, `cranelisp-backend`, `cranelisp-primitives`, `cranelisp-intrinsics`, `cranelisp-platform`, `cranelisp` (binary / int).

**Note on `cranelisp-runtime`**: per FIXME 0150 Phase 5, the runtime crate retires by S66 close. /qa baselines `cranelisp-runtime`'s public surface ONE LAST TIME at S66 open (the freeze line) — the baseline file deletes when the crate retires. The 8-crate list above is the **post-S66-close** target; transit-state (mid-sprint) carries 9 baselines, settling to 8 at Phase 7.

### 1.2 CI gate

A new top-level `cargo xtask api-check` (or `just api-check`) script runs `cargo public-api --diff-git-checkout HEAD~1` per crate. Drift produces a non-zero exit. Wired into the same CI lane as `cargo nextest run`.

### 1.3 Drift workflow

When `api-check` reports drift:

- **Intentional facade-shape change** — author updates the facade `.md` first, then regenerates the baseline (`cargo public-api > crates/{crate}/public-api.txt`), commits both in one change. PR review checks the facade rationale.
- **Unintentional drift** — fix the source to match the facade. The baseline does not regenerate.
- **The two cases are distinguished by which side of the diff changed**: facade or source. Reviewers always look at the facade first.

### 1.4 Sizing

Per-crate baseline generation (incl. transit-state runtime baseline): 30 min × 9 crates ≈ 4.5 hr. CI wiring: 1 hr. xtask + docs (incl. nightly-toolchain prerequisite per §1.0): 2 hr. Drift-process documentation in `tests/CLAUDE.md` (new "Public-API enforcement" subsection) and `design/arch/CLAUDE.md`: 1 hr. Triad-ownership editorial revisions per FIXME 0152 closure: 0.5 hr. **Total ~ 1 day** (sized as `/dev` workstream wrappable around any crate's facade-conformant landing).

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

Each in-scope facade migration may temporarily flip tests red during S66 adoption. The pre-classification (D43 bound; per /arch Phase 2 verdict):

| Facade migration | Expected reshape pattern | Failure window | Net-new failures (lower / upper) |
|---|---|---|---|
| **FIXME 0098** (ResolutionGap/CheckError/ExpansionError migration) | Compile error if any test imported `cranelisp_types::CheckError` (none should — e2e tests don't import internal types). REPL gap-orchestration retry behaviour observable via subprocess; if int's retry loop regresses, `repl_*.rs` and import-resolution tests will surface. | Possible 1-2 days | 0 / 2 (regression-only) |
| **FIXME 0099** (GotObserver) | Backend extension point + int-side ring buffer. Test surface: new e2e tests that activate `CRANELISP_GOT_TRACE=1` and assert observer-fired events appear in stderr (parallel to existing `CRANELISP_IO_TRACE`). NEW tests, not reshapes. | 0 reshapes; new coverage | 0 / 0 |
| **FIXME 0100** (single-consumer relocations) | `CheckError`, `CheckResult`, `ResolutionGap`, `ReplSnapshot`, `CompilationError`, `Got*` types move from `cranelisp-types` to their originating crates. Pure Rust-source path-rewrite; e2e tests (subprocess-only) are insulated. | 0 reshapes at e2e | 0 / 0 |
| **FIXME 0103** (trace.rs/io_trace.rs intrinsics → int; IoObserver in intrinsics per /arch revision #3) | int-side ring buffer + flush guard machinery moves into `src/io_trace/`. Behavioural test: `CRANELISP_IO_TRACE=1` continues to produce the same stderr trace shape pre/post relocation. Tests that assert specific trace dump *line ordering* may need re-baselining; tests that assert *event presence* are stable. | One sprint | 1 / 3 (line-ordering tests, if any) |
| **FIXME 0104** (PlatformError adoption) | Error message shape changes from free-floating string to `lib/main.cl:42:7: error: platform "stdio" not found in search path` form. Tests that match on the OLD shape (substring match per `tests/CLAUDE.md` "Error tests use substring matching") need re-baselining to the new shape. | One sprint | 3 / 5 (`repl_negative.rs`, `examples.rs` substring matches) |
| **FIXME 0107** (`OwnedPlatformFnDescriptor` `#[non_exhaustive]`) | Test-side: e2e tests don't construct `OwnedPlatformFnDescriptor`. Unit tests (/dev-owned) inside `cranelisp-platform` may need `..Default::default()` patterns. | 0 reshapes at e2e | 0 / 0 |
| **FIXME 0108** (display.rs backend → int) | Pure Rust-source relocation; output bytes identical. | 0 reshapes | 0 / 0 |
| **FIXME 0150 — D43** (LIVE in S66 per /arch Option A; no longer conditional) | **Composite, four risk vectors**:<br/>**(a)** Phase 1+2 source migration (`cranelisp-runtime` → `cranelisp-primitives` + `cranelisp-intrinsics`) — pure-source path rewrite. Compile error in transit if any unit test imported `cranelisp_runtime::*` directly; e2e tests are insulated.<br/>**(b)** Phase 3 backend deletions (trait-knowledge maps + `cranelisp_op_*` GOT slots). The `(let [f +] (f 1 2))` operator-as-value path now goes through trait-impl entry → primitive — net behaviour unchanged, intermediate code path different.<br/>**(c)** Phase 4 stdlib trait-impl audit — **the highest single reshape risk in S66.** Empty-body or circular-recursion `(impl Num Int)` / `(impl Eq Int)` / `(impl Ord Int)` / `(impl Display Int)` / Float counterparts that "just worked" because backend's `(Trait, method, Type) → primitive` map intercepted upstream of the impl body now break at runtime when the map deletes. /arch Phase-2 recommendation #4 calls this out as observability-bandwidth-priority.<br/>**(d)** Phase 5 `--link` linker-archive update — `link.rs` mode-equivalence tests must continue to pass against `cranelisp-intrinsics.a` + `cranelisp-primitives.a` instead of `cranelisp-runtime.a`. | One sprint, may bridge into Phase 5 close-short if Phase 4 audit surfaces > 15 broken impls | **10 / 15** (Phase 4 stdlib audit dominant) — pre-classified as "expected reshape from D43 Phase 4 stdlib audit" per /arch Phase-2 budget call-out |
| **FQTypeName threading** (FIXME 0151 — out of S66 scope per SPRINT.md, deferred to S67+) | NOT in S66; gate calibration unchanged. | n/a | 0 / 0 |

**Aggregate pre-classified envelope**: lower bound **~13** reshapes (favourable Phase-4-audit outcome — most stdlib impls already correct), upper bound **~23** reshapes (worst-case Phase-4-audit outcome — many empty-body impls discovered) + a small allowance for tracing-line-ordering. /arch Phase 2 verdict §"Notes" confirms the **13–23 range** as the working budget.

**Tolerance commitment**: The S66 gate accepts up to **~47 net-new test failures** before hard-stopping the sprint. Headroom calculation against the **post-S64 baseline of 932 / 953**:

- 95% pass-rate floor: 953 × 0.95 = 906 passing minimum → 47-test margin from 953 active tests.
- S64 baseline of 932 passing absorbs the first 26 reshapes within the floor; the remaining 21-test allowance comes from the budgeted ledgered failures (which may resolve along the way as side-effects of D43 cleanup — e.g., FIXME 0122's `--link` divergence may close as a Phase-5 byproduct).
- Pre-classified envelope (13–23) sits well below the 47-test budget. Headroom on the order of 24–34 reshapes for un-pre-classified surprises.

**Mid-sprint check (per /qa Q5 below)**: end of Wave 3, /qa counts actual failure delta against pre-classified; if outside the 13–23 envelope but within the 47-test budget, escalate to /sprint Phase-5 review (continue or close-short). If outside the 47-test budget, hard stop and Phase-5 close-short.

### 2.4 Verdict

**Gate is calibrated against post-S64 baseline (932 / 953, 95% floor = 906 passing); D43 bound; pre-classified reshapes (13–23) well within the 47-test tolerance envelope.** S66 opens with 932/21/6 as the freeze line; close-time accepts ≥ 906 passing, with every failure ledgered or pre-classified per the table above.

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

## 5. Phase 5 Stage 1 — failing-test inventory (QA-first authoring)

Per METHOD §2.2 and `/qa` Phase-5 obligation, **/qa first across the entire solution** authors failing integration / e2e tests covering every in-scope FIXME BEFORE per-crate D/D/R cycles begin in Phase 5. The tests scope what each per-crate triad must make pass.

**Failing-not-ignored discipline.** Per `memory/feedback_failing_not_ignored.md` and `qa.md` § "Failing-not-ignored discipline": every test below is committed at Phase-5 Stage-1 open as failing-not-ignored. Compilation failures are valid failure modes (louder than `#[ignore]`); if a test references a public-surface item not yet relocated (e.g., `register_got_observer`), the test won't compile and the e2e binary won't link — that is the signal. Each test carries a `// spec:` annotation and a `// FIXME(<owner>)` reference to the owning compiler-skill workstream that must make it pass.

The inventory below is **per-FIXME**, naming each new test file, the new test functions, the rationale for failing at Phase-5 Stage 1, and which compiler-skill workstream resolves.

### 5.1 FIXME 0098 — ResolutionGap / CheckError / ExpansionError migration

**Test file**: `tests/process_form_dispatch.rs` (new).

| Test fn | Fails because… | Resolves when |
|---|---|---|
| `process_form_dispatch_macro_after_import_succeeds_in_one_eval` | At Phase-5 Stage 1, frontend's `expand` still lives in `src/expander.rs` and returns the legacy stringly-typed `MacroResolver`-mediated error; `process_form` retries via ad-hoc string parsing. The test asserts that REPL `(import [m])\n(macro-from-m ...)` completes in a single REPL `eval` (the orchestrator-side retry loop completes inside that eval). Fails because the typed pattern-match path on `ExpansionError::Gap(ResolutionGap::MacroInMem(fq))` is the new contract and doesn't exist yet. | frontend Phase 2 + int Phase 4 of FIXME 0098 land. |
| `process_form_dispatch_typecheck_gap_completes_in_one_eval` | Asserts REPL `(defn f [] (g 1))\n(defn g [x] x)\n` completes — the forward-reference to `g` from `f` triggers a `CheckError::Gap(ResolutionGap::SymbolTypechecked(fq))`, the orchestrator retries after `wait_for_typecheck_symbol`. Fails because the new typed-error contract is not yet wired through `int::process_form`. | typecheck Phase 3 + int Phase 4 of FIXME 0098 land. |
| `process_form_dispatch_function_gap_does_not_speculatively_jit` | Per /arch recommendation #1 + facade-level invariant: when `wait_for_typecheck_symbol` returns a function (not a macro), the orchestrator must NOT speculatively JIT it. Test enables `CRANELISP_GOT_TRACE=1`, asserts no `JitWrite` event fires from the speculative path. Fails because backend's GotObserver doesn't exist yet (FIXME 0099 dependency). | int Phase 4 of FIXME 0098 + backend Phase 1 of FIXME 0099 land. |

`// spec:` 08-modules.md §"REPL form sequencing" + 09-macros.md §"Macro resolution".

### 5.2 FIXME 0099 — GotObserver (backend trait + int consumer)

**Test file**: `tests/got_trace.rs` (new; mirror of existing `io_trace`-shape tests).

| Test fn | Fails because… | Resolves when |
|---|---|---|
| `got_trace_emits_jit_write_event` | Asserts `CRANELISP_GOT_TRACE=1 cranelisp --run …` produces stderr lines containing `JitWrite` events with the correct symbol name. Fails: `cranelisp_backend::register_got_observer` doesn't exist; binary doesn't compile. | backend FIXME 0099 Phase 1 + int FIXME 0099 Phase 2 land. |
| `got_trace_emits_linker_write_event_on_cache_hit` | Asserts cached load path emits `LinkerWrite` events. Fails identically. | Same as above. |
| `got_trace_emits_redefinition_event_on_repl_redefn` | Asserts REPL `(defn foo [] 1)` followed by `(defn foo [] 2)` emits a `Redefinition` event. Fails identically. | Same as above. |
| `got_trace_off_path_zero_overhead_neg` | **Negative test.** Asserts that with NO `CRANELISP_GOT_TRACE` env var, stderr contains NO got-trace lines. Verifies the zero-overhead claim from the facade (one relaxed-load null check, no observer registered). Fails identically until the binary compiles. | Same as above. |

`// spec:` 12-runtime.md §"Diagnostic logging" (reservation for `CRANELISP_GOT_TRACE`).

### 5.3 FIXME 0100 — relocations (assert types resolve from new homes)

**Test file**: `tests/public_api_relocations.rs` (new — small file; bulk of verification is via `cargo public-api` baseline diff).

| Test fn | Fails because… | Resolves when |
|---|---|---|
| `public_api_check_runs_against_all_eight_crates` | Calls `cargo +nightly public-api` per crate via subprocess; asserts no drift against committed `public-api.txt`. Fails at Phase-5 Stage 1 because: (a) baselines for `cranelisp-primitives` + `cranelisp-intrinsics` don't exist (crates don't exist), (b) `cranelisp-types` baseline includes `CheckError`/`CheckResult`/`ReplSnapshot`/`CompilationError`/`Got*` which must move out, (c) `cranelisp-typecheck` + `cranelisp-backend` baselines don't yet show the relocated types. | All eight `/dev` crate workstreams complete + commit baselines per §1.1. |

`// spec:` (no direct spec — this is a structural conformance test backed by /arch facade approval).

### 5.4 FIXME 0103 — IoObserver in intrinsics; trace.rs + io_trace.rs in int

**Test files**: extension to `tests/spec_10_io.rs` + new fixture `tests/fixtures/io_trace_snapshot.txt` + new test in `tests/got_trace.rs` (or own file).

| Test fn | Fails because… | Resolves when |
|---|---|---|
| `io_trace_snapshot_pre_post_relocation_byte_equivalent` | Pins the canonical `CRANELISP_IO_TRACE=1` stderr trace shape for a representative IO program. Loaded against `tests/fixtures/io_trace_snapshot.txt`. Fails at Phase-5 Stage 1 if the fixture expectation differs from the freshly-relocated-machinery output. The intent is to catch silent reshape during migration. | intrinsics Phase 2 (IoObserver moves in) + int Phase 2 (trace.rs/io_trace.rs ring-buffer adoption) land — both in FIXME 0103 scope, bundled with FIXME 0150 Phase 2 per /arch revision #3. |
| `io_observer_registration_lives_in_intrinsics` | Asserts (via `cargo public-api`-mediated check) that `register_io_observer` appears in `cranelisp-intrinsics`'s baseline and is ABSENT from `cranelisp-runtime`'s baseline. Fails at Phase-5 Stage 1 because the function has not yet relocated. | Same as above. |

`// spec:` 12-runtime.md §"Diagnostic logging" + 10-io.md §"IO observation contract".

### 5.5 FIXME 0104 — PlatformError adoption (error type round-trip across crate boundaries)

**Test file**: `tests/platform_errors.rs` (new).

| Test fn | Fails because… | Resolves when |
|---|---|---|
| `platform_load_failed_carries_form_span` | Asserts `--run` of a program with a `(platform "stdio")` declaration that fails to find the DLL produces stderr containing the form span (`lib/main.cl:42:7:` or similar) plus `error: platform "stdio" not found in search path`. Fails because `PlatformError` enum doesn't yet exist in `cranelisp-types`; the legacy `String`-backed error has different shape. | types Wave 0 + platform Phase 2 + int Phase 3 of FIXME 0104 land. |
| `platform_manifest_not_found_carries_dll_path` | Similar: error carries the DLL search path inspected. Fails identically. | Same as above. |
| `platform_abi_version_mismatch_emits_expected_vs_found` | Uses synthetic stale-ABI-version DLL fixture; asserts error contains both expected + found ABI versions. Fails because the `PlatformError::AbiVersionMismatch { expected, found, .. }` variant doesn't yet exist. | types Wave 0 + platform Phase 2 land; intrinsics manifest-loader audit. |
| `platform_dispatch_error_during_run_carries_fn_name` | Asserts dispatch error (e.g. type sig mismatch) carries the offending fn name. Fails identically. | types Wave 0 + platform Phase 2 + int Phase 3 land. |

`// spec:` 11-platform.md §"Platform error reporting" + 12-runtime.md §"Error diagnostics".

### 5.6 FIXME 0107 — `#[non_exhaustive]` build-time enforcement test

**Test file**: /dev-unit `compile_fail` doc-test inside `crates/cranelisp-platform/src/lib.rs` (Sprint-66 /qa scopes, /dev-unit-tier authors per `memory/feedback_unit_tests_with_dev.md`). /qa's responsibility at Phase-5 Stage 1 is to **track this in the plan and confirm the doc-test exists** at FIXME 0107 close — not to author it. The /qa-owned e2e surface is unaffected.

**No new e2e test**; FIXME 0107 has zero e2e reshape per §2.3.

### 5.7 FIXME 0108 — `backend::display::*` no longer reachable; int's display surface intact

**Test file**: extends existing `tests/repl_introspection.rs` (regression-only).

| Test fn | Fails because… | Resolves when |
|---|---|---|
| `display_format_eval_result_after_relocation_unchanged` | Asserts `/sig`, `/info`, REPL eval output bytes are byte-equivalent pre/post relocation. Fails at Phase-5 Stage 1 only if relocation is in-progress and output differs (which it shouldn't — pure source move). Stays green if landing is clean. | int FIXME 0108 land. |
| `public_api_check_backend_display_absent_neg` | **Negative test.** Asserts `cargo public-api` on `cranelisp-backend` shows NO `display::*` symbols. Fails because backend baseline still carries them. | int FIXME 0108 land + backend baseline regenerated. |

`// spec:` (structural — no spec change; verified via baseline diff).

### 5.8 FIXME 0150 (D43) — primitives + intrinsics crates exist; backend trait-knowledge maps deleted; stdlib trait impls compile against new homes

**Test file**: `tests/stdlib_trait_impls.rs` (new — comprehensive operator × primitive-type matrix; serves as Phase-4 audit guard).

This is the **highest-risk reshape** per /arch recommendation #4 + §2.3. The test file is the regression guard; it MUST be authored at Phase-5 Stage 1, failing-not-ignored, before any D43 source migration begins. It catches Phase-4 stdlib-audit regressions early — including the empty-impl + circular-recursion patterns the audit must surface and fix.

Test fns enumerated by (Trait, primitive type, path):

| Test fn | Fails because… | Resolves when |
|---|---|---|
| `stdlib_num_int_inline_path` | `(+ 1 2)` returns `3`. Fails until D43 Phase 3 deletes backend's `(Num, +, Int) → add-i64` map AND Phase 4 stdlib audit confirms `(impl Num Int)`'s `+` body calls `add-i64` directly. | FIXME 0150 Phase 3 + 4 land. |
| `stdlib_num_int_mappable_path` | `(let [f +] (f 1 2))` returns `3`. Fails until the operator-as-value path goes through trait-impl entry → `(add-i64 a b)` (post-Phase-4) and not through deleted `cranelisp_op_add` GOT slot (Phase 3 deletion). | FIXME 0150 Phase 3 + 4 land. |
| `stdlib_num_float_inline_path` | `(+ 1.0 2.0)` returns `3.0`. | Same. |
| `stdlib_num_float_mappable_path` | `(let [f +] (f 1.0 2.0))` returns `3.0`. | Same. |
| `stdlib_eq_int_inline_path` / `stdlib_eq_int_mappable_path` | `(= 1 1)` returns `true`; `(let [f =] (f 1 1))` returns `true`. | Same. |
| `stdlib_eq_float_inline_path` / `_mappable_path` | Same on Float. | Same. |
| `stdlib_eq_bool_inline_path` / `_mappable_path` | `(= true true)` returns `true`; mappable variant. | Same. |
| `stdlib_eq_string_inline_path` / `_mappable_path` | String equality positive + mappable. | Same. |
| `stdlib_ord_int_inline_path` / `_mappable_path` | `(<` `(>` `(<=` `(>=` family on Int. Compressed into one fn each path with multiple asserts. | Same. |
| `stdlib_ord_float_inline_path` / `_mappable_path` | Float Ord. | Same. |
| `stdlib_display_int_inline_path` | `(show 42)` returns `"42"`. Must NOT regress to backend's pre-D43 substitution path. | Same. |
| `stdlib_display_float_inline_path` | `(show 3.14)` returns `"3.14"`. | Same. |
| `stdlib_not_inline_path` / `_mappable_path` | **Specifically named in FIXME 0150**: `not` currently has only the inline path via backend's `operators.rs:64`; no symbol-table entry; mappable-path almost certainly fails today. The test surfaces this gap as failing at Phase-5 Stage 1; closure requires symbol-table seeding for `not`. | FIXME 0150 Phase 4 + a primitives-side seeding entry land. |
| `stdlib_link_mode_against_intrinsics_archive` | `cranelisp --link` produces a runnable binary that links against `cranelisp-intrinsics.a` + `cranelisp-primitives.a`. Fails until Phase 5 retirement of `cranelisp-runtime` is complete. | FIXME 0150 Phase 5 land. |
| `cranelisp_runtime_crate_absent_post_phase_5_neg` | **Negative test.** Asserts `cranelisp-runtime` directory does NOT exist post-FIXME-0150 close + workspace `Cargo.toml` does not list it as a member. Fails until Phase 5 retirement lands. | FIXME 0150 Phase 5 land. |

**Inventory total for FIXME 0150**: 19 test fns across 16 rows above.

`// spec:` appendix-a-builtins.md (every primitive named) + 07-traits.md §"Trait dispatch resolution".

### 5.9 Inventory summary

| FIXME | Test file (new) | # failing tests at Stage 1 |
|---|---|---|
| 0098 | `tests/process_form_dispatch.rs` | 3 |
| 0099 | `tests/got_trace.rs` | 4 (incl. 1 negative) |
| 0100 | `tests/public_api_relocations.rs` | 1 (composite — runs across 8 crates) |
| 0103 | extension to `tests/spec_10_io.rs` + `tests/fixtures/io_trace_snapshot.txt` | 2 |
| 0104 | `tests/platform_errors.rs` | 4 |
| 0107 | n/a — /dev-unit `compile_fail` doc-test inside `cranelisp-platform`; tracked here for cross-skill visibility | 0 (e2e); 1 (/dev-unit) |
| 0108 | extension to `tests/repl_introspection.rs` | 2 (incl. 1 negative) |
| 0150 (D43) | `tests/stdlib_trait_impls.rs` | 19 (incl. 1 negative) |
| **Total /qa-owned failing-not-ignored at Phase-5 Stage 1** | | **35 tests** |

**ReplSnapshot rollback regression** + **session-lifecycle Decision 31 retention** + **platform ABI version mismatch** + **process_form orchestrator dispatch tests** that were noted in earlier §3 / §4 sections as "new tests" are subsumed into the inventory above — primarily under FIXME 0098 (process_form_dispatch.rs) and FIXME 0104 (platform_errors.rs). The §5 inventory is the authoritative count for Phase-5 Stage 1 authoring.

All 35 tests are committed failing-not-ignored at Phase-5 Stage 1 open. Each has a `// spec:` comment, a `// FIXME(<owner>)` reference, and a row in `tests/plan/PLAN.md`. As `/dev` workstreams complete, /qa updates the row annotation from `[S66]` to `[Tested tests/{file}::{fn}]` (or `[Tested+Neg ...]` for the 4 negative tests above).

### 5.10 Wave-allocation considerations (critical path + observability)

**Critical-path triad — same-wave landing required.** Per /arch Phase-2 recommendation #1, the `process_form` shape-pivot triad must land in a **single wave sub-batch**:

- **frontend slice row 7** — `expand` migration to `cranelisp-frontend`; emits `ExpansionError::Gap(ResolutionGap::MacroInMem(fq))`.
- **typecheck slice row 1** — `check_form` shape-pivot to `Result<CheckResult, CheckError>`; emits `CheckError::Gap(ResolutionGap::SymbolTypechecked(fq))`.
- **int slice row 3** — `process_form` typed pattern-match on the new error contracts; orchestrates the gap-retry loop.

If any one slips, the other two cannot validate end-to-end (the test in §5.1 — `process_form_dispatch.rs` — needs all three present to pass). **/qa wave acceptance criterion**: a wave that lands fewer than all three rows of the triad does NOT clear the §5.1 tests, even if the wave succeeds in isolation. Plan for a same-wave triad burst at /sprint Phase-4 wave-allocation time. The /qa-side test infrastructure (`tests/process_form_dispatch.rs`) is authored at Phase-5 Stage 1 (failing-not-ignored) so /sprint sees the gating signal at every wave checkpoint.

**Observability bandwidth — D43 Phase 4 stdlib audit.** Per /arch Phase-2 recommendation #4 + SPRINT.md §"Notes": `CRANELISP_RC_TRACE` + `CRANELISP_CODEGEN_TRACE` are **reserved for the D43 Phase-4 stdlib trait-impl audit** — the highest-risk reshape per §2.3. /qa's role:

- The §5.8 `tests/stdlib_trait_impls.rs` test fns are designed for trace-friendly minimisation: each test exercises a single `(operator, primitive-type, path)` triple in a tiny REPL transcript. When any test fails during Phase 4 audit, /qa runs the failing test under `CRANELISP_RC_TRACE=1` (catches RC mis-count from circular-impl recursion) and `CRANELISP_CODEGEN_TRACE=1` (inspects CLIF for the failing primitive call). Per `memory/feedback_repros_join_suite.md`, small repros aid debugging.
- /qa flags reservation in `tests/CLAUDE.md` § "Public-API enforcement" subsection so concurrent agents do not contend on the same env-var output during Phase 4.
- Stress-test contention with concurrent observer registration (`register_io_observer`, `register_got_observer`) is documented as Q3 below; resolution is /dev-tier choice (loom vs. shuttle).

**Heaviest-load wave** (per /arch Phase-2 recommendation #2): int slice's full S66 load is ~10–13 working days = ~2.5–3 S66 waves. /qa's expectation is that int receives a 2-wave allocation; /qa's plan-side artefacts (`tests/process_form_dispatch.rs`, `tests/got_trace.rs`, extension to `tests/repl_introspection.rs`) survive the 2-wave allocation unchanged because they're authored against the final-state contract — not against an intermediate state.

---

## 6. Sizing

Rough sizing per work-item, suitable for `/sprint` to fit into S66 wave envelopes.

| Work-item | Sizing | Notes |
|---|---|---|
| `cargo public-api` baselines + CI gate (§1) | ~1 day | 8 final baselines + transit-state runtime baseline + xtask + nightly-toolchain docs |
| 95% gate calibration commitment in SPRINT.md (§2) | 1 hour | Doc work; freezes baseline (already reflected in SPRINT.md §"Notes" by /sprint) |
| **Phase-5 Stage 1 failing-test authoring (§5)** | ~3.5 days | 35 failing-not-ignored tests across 6 new files + 2 extensions; sequenced sprint-wide BEFORE any /dev D/D/R cycle |
| — `tests/process_form_dispatch.rs` (FIXME 0098 §5.1) | ~1 day (in §5 budget) | 3 tests; gap-retry contract + speculative-JIT negative |
| — `tests/got_trace.rs` (FIXME 0099 §5.2) | ~1 day (in §5 budget) | 4 tests incl. negative; mirror of `io_trace`-shape |
| — `tests/public_api_relocations.rs` (FIXME 0100 §5.3) | ~half day (in §5 budget) | 1 composite test; subprocess-runs `cargo +nightly public-api` per crate |
| — `tests/spec_10_io.rs` extension + `io_trace_snapshot.txt` (FIXME 0103 §5.4) | ~half day (in §5 budget) | 2 tests + snapshot fixture |
| — `tests/platform_errors.rs` (FIXME 0104 §5.5) | ~1 day (in §5 budget) | 4 tests incl. synthetic stale-ABI DLL fixture |
| — `tests/repl_introspection.rs` extension (FIXME 0108 §5.7) | ~half day (in §5 budget) | 2 tests incl. negative; baseline-diff verification |
| — `tests/stdlib_trait_impls.rs` (FIXME 0150 D43 §5.8) | ~2 days (in §5 budget) | 19 tests; comprehensive operator × primitive-type matrix incl. negative; serves as Phase-4 audit guard |
| Re-baselining ~3-5 platform-error substring tests (FIXME 0104) | ~half day | Edits in `repl_negative.rs`, `examples.rs` (when /dev lands the error reshape, /qa updates) |
| `tests/CLAUDE.md` updates (Public-API enforcement subsection + nightly toolchain) | ~half day | Doc work; FIXME 0152 closure |
| `tests/plan/PLAN.md` row additions for all 35 new tests + status updates as /dev workstreams complete | ~1.5 days | Per `tests/CLAUDE.md` "No test is silently dropped" + per `qa.md` test-plan obligation |
| `tests/plan/ledger.md` updates per pre-classified reshape (D43 Phase-4 audit + FIXME 0104) | ~1 day | Mid-sprint check (Wave 3 close per Q5) + Phase-7 outcome reporting |
| Mid-sprint Wave-3 reshape audit (per Q5) — actual vs. pre-classified | ~half day | Counts failure delta; escalates to /sprint if outside 13–23 envelope |
| /dev-unit work (intrinsics observer concurrency, types helpers, backend SymbolNotCompilable, platform compile_fail, FIXME 0107) | ~2-3 days, /dev-owned | NOT /qa work; tracked here for cross-skill visibility |
| Carry-forward (deferred): `tests/lifecycle.rs` (Decision 31 retention) + `tests/platform_abi.rs` (ABI mismatch) + ReplSnapshot rollback regression | absorbed into §5.5 + §5.4 + §5.1 above | Earlier (pre-revision) sizing rows are subsumed into the §5 inventory; flagged in §9 Q2 if S66 cannot land all of them. |

**Total /qa-owned work**: ~7-8 days of test + plan + doc work — concentrated in the Phase-5 Stage 1 authoring burst (~3.5 days of test authoring) + ongoing plan/ledger maintenance through Waves 2–4. Fits within an S66 wave envelope; sequenced before any /dev D/D/R cycle per METHOD §2.2 QA-first commitment.

---

## 7. Cross-crate dependencies (bilateral)

This /qa slice's test-surface-impact rows align with the per-crate `/design` slices' "Test surface impact" sections per the Phase-2-review template §3.2 row 5. Bilateral cross-references:

| This slice's item | Depends on / aligns with | In the other crate's slice |
|---|---|---|
| `cargo public-api` baselines (§1.1) — triad-ownership editorial closed per FIXME 0152 | /dev (per crate) regenerates after facade-conformant landing; /design verifies; /review approves the diff | `design/{crate}/implementation-slice-s66.md` §5 "Test surface impact" — each names baseline-regeneration step under /dev's milestones |
| 95% gate pre-classified reshapes (§2.3) | Each /design (crate) slice scopes which existing tests its adoption may shift | `design/{crate}/implementation-slice-s66.md` §5 — names the test-side reshape per delta row |
| `tests/got_trace.rs` (FIXME 0099 §5.2) | backend implements observer (Phase 1); int implements ring buffer + register (Phase 2) | `design/backend/implementation-slice-s66.md` §5 (FIXME 0099 backend phase); `design/int/implementation-slice-s66.md` §5 (FIXME 0099 int phase) |
| `tests/platform_errors.rs` (FIXME 0104 §5.5) | types Wave 0 (`PlatformError` enum); platform Phase 2 (carrier adoption); int Phase 3 (`format_error` consumer) | `design/platform/implementation-slice-s66.md` §5; `design/int/implementation-slice-s66.md` §5 |
| `tests/stdlib_trait_impls.rs` (FIXME 0150 D43 §5.8) | primitives Phase 1+2 (skeleton + sources); intrinsics Phase 1+2; backend Phase 3 (trait-knowledge deletion); stdlib Phase 4 (impl audit); runtime Phase 5 (retirement) | `design/primitives/implementation-slice-s66.md` §5; `design/intrinsics/implementation-slice-s66.md` §5; `design/backend/implementation-slice-s66.md` §5; runtime-retiring slice §5 |
| `tests/process_form_dispatch.rs` (FIXME 0098 §5.1) — **critical-path triad** | frontend Phase 2 (`expand` migration); typecheck Phase 3 (`check_form` shape-pivot); int Phase 4 (typed pattern-match). **Same-wave landing required** per /arch recommendation #1 | `design/frontend/implementation-slice-s66.md` §5; `design/typecheck/implementation-slice-s66.md` §5; `design/int/implementation-slice-s66.md` §5 |
| `tests/spec_10_io.rs` extension + `io_trace_snapshot.txt` (FIXME 0103 §5.4) | intrinsics Phase 2 (IoObserver moves in); int Phase 2 (trace.rs/io_trace.rs ring-buffer adoption). Bundled with FIXME 0150 Phase 2 per /arch revision #3 | `design/intrinsics/implementation-slice-s66.md` §5; `design/int/implementation-slice-s66.md` §5 |
| `tests/public_api_relocations.rs` (FIXME 0100 §5.3) | All eight crate baselines committed by /dev; types-crate baseline shrinks (FIXME 0100 Phase 1+2 removals) | every `design/{crate}/implementation-slice-s66.md` §5 baseline-regeneration step |
| `tests/repl_introspection.rs` extension (FIXME 0108 §5.7) | int Phase (display.rs adoption); backend baseline regenerated absent display | `design/int/implementation-slice-s66.md` §5; `design/backend/implementation-slice-s66.md` §5 |
| /dev-unit observer concurrency (§3.6) + FIXME 0107 `compile_fail` doc-test (§5.6) | /dev-owned (per `memory/feedback_unit_tests_with_dev.md`) | `design/intrinsics/implementation-slice-s66.md` §5; `design/backend/implementation-slice-s66.md` §5; `design/platform/implementation-slice-s66.md` §5 |

**Count: 10 cross-crate dependency rows** (post-revision; up from 9 — added the public-api relocations row to the explicit table). Each /design (crate) slice has at least one corresponding row in this /qa plan; /qa has one row corresponding to every /design (crate) slice that touches the user-visible surface.

If any bilateral row above does not appear in the corresponding /design (crate)'s §5, /qa files an `/arch` FIXME at W4b cross-cutting check time. The bilateral table is the gate for "everyone agrees what tests cover what".

---

## 8. Test infrastructure uplift

Per `legacy/substance-action-plan.md` Step-4 row for `/qa`: *"First-wave slice of integration + e2e infrastructure uplift; coverage tests for the substance commitments landing in Sprint 66."*

### 8.1 Infrastructure changes

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

- **`tests/got_trace.rs`** — new e2e file (FIXME 0099). Mirrors existing IO-trace-shape tests. 4 test fns per §5.2.

- **`tests/platform_errors.rs`** — new e2e file (FIXME 0104). 4 test fns per §5.5; subsumes the synthetic-DLL ABI fixture (folded in from earlier `tests/platform_abi.rs` plan).

- **`tests/stdlib_trait_impls.rs`** — new e2e file (FIXME 0150 D43). 19 test fns per §5.8; comprehensive operator × primitive-type matrix; serves as Phase-4 audit guard.

- **`tests/process_form_dispatch.rs`** — new e2e file (FIXME 0098 critical-path triad). 3 test fns per §5.1.

- **`tests/public_api_relocations.rs`** — new e2e file (FIXME 0100). 1 composite test fn that subprocess-runs `cargo +nightly public-api` per crate.

- **`tests/lifecycle.rs`** — Decision-31 retention regression. **Deferred to S67+** if stress framework not ready (per Q2 below). Coarse-grained version may land in S66 if /sprint allocates the wave time; otherwise filed forward.

### 8.2 New helpers

Listed in §8.1. Total ~3-4 new helper additions to `tests/helpers/e2e.rs` + 1 new helper module (`snapshot.rs`).

### 8.3 Deprecations

None at this level. The S64 migration to two-tier (e2e or unit, no middle) completed in S64 Phase 3; `tests/helpers/mod.rs::ReplSession` was deleted. No further deprecation work in S66.

### 8.4 Spec-link-check linter (existing, runs in lockstep)

`tests/plan/spec_link_check.py` (per `tests/CLAUDE.md`): every new `// spec:` annotation in S66's new test files MUST pass the linter. Run before commit:
```bash
python3 tests/plan/spec_link_check.py
```

S66 introduces ~6-8 new test files (per §8.1) carrying ~30-50 new `// spec:` annotations. The linter run is a S66 close-gate item.

### 8.5 Pre-commit / CI integration (carry-forward)

`tests/CLAUDE.md` notes: *"Pre-commit / CI integration is a future commitment, not a Sprint 64 deliverable."* S66 does NOT make it a deliverable either; tracked as an out-of-scope item per `sprints/SPRINT.md` § Out-of-scope.

---

## 9. Open questions

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

§2.3 pre-classifies expected reshape counts per FIXME (3-5 platform-error, 10-15 stdlib-trait-impl, 1-3 trace-line-ordering). Aggregate envelope: 13–23 reshapes within the 47-test budget. /qa's mid-sprint check happens at **end of Wave 3** (D43 source migration + observer/error adoption substantially complete; Phase-4 stdlib audit underway): count actual vs. pre-classified, escalate to /sprint Phase-5 close-short if outside the 47-test envelope. Inside the envelope but outside the 13–23 pre-classified range = /sprint review (continue or close-short).

**Resolution path**: /sprint S66 Phase-3 plan reflects the mid-sprint check; /qa includes the check as a wave acceptance criterion.

### Q6 — FIXME 0150 (D43) sequencing: ~~Wave 0 of S66 OR S67+?~~ — RESOLVED (2026-05-07)

**Resolution.** /sprint Phase-2 review resolved with /arch Option A: D43 binds into S66. The wave plan integrates D43 across Wave 2 (skeleton crates + type relocations) → Wave 3 (source migration in primitives + intrinsics; backend trait-knowledge deletions; FIXME 0103 IoObserver in intrinsics) → Wave 4 (stdlib trait-impl audit + `cranelisp-runtime` retirement). Per §2.3 + §5.8 above, /qa authors `tests/stdlib_trait_impls.rs` failing-not-ignored at Phase-5 Stage 1 to guard the Phase-4 stdlib audit (highest-risk reshape). No fork remains — the §4.8 work is unconditional.

---

## Cross-references

- `design/arch/sprint-65-reshape-phase-2-review.md` §3 — slice template (adapted here for /qa)
- `design/arch/sprint-65-legacy-triage.md` — F1 (Step 4 retro), F4 (D43 sequencing) findings
- `design/arch/legacy/substance-action-plan.md` Step-4 row for /qa
- `tests/CLAUDE.md` — two-tier strategy, helper API, fresh-tmpdir discipline, isolation protocol; new "Public-API enforcement" subsection authored alongside this slice (FIXME 0152 closure)
- `tests/plan/PLAN.md` — normative spec → tests bridge
- `tests/plan/ledger.md` — failure ledger, S64-close baseline 932/21/6
- `sprints/SPRINT.md` § Hard constraints + § Architecture review (Phase 2) — D43 bound per Option A; critical-path triad call-out; observability bandwidth reservation
- `sprints/archive/sprint-64.md` — Phase-6 reconciliation that produced the freeze line
- `memory/feedback_failing_not_ignored.md` — failing-not-ignored discipline
- `memory/project_test_strategy.md` — two-tier discipline
- `memory/feedback_repros_join_suite.md` — every reduction joins as a committed failing test
- `memory/feedback_unit_tests_with_dev.md` — /qa owns e2e in `tests/`; /dev owns unit in `crates/{crate}/src/`
- `design/arch/fixmes/0098`, `0099`, `0100`, `0103`, `0104`, `0107`, `0108`, `0150` — the eight in-scope FIXMEs scoped per §4
- `design/arch/facades/{types,frontend,typecheck,backend,platform,intrinsics,primitives,int}.md` — the eight final-state facades scoped per §3
