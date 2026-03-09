# Sprint 16: Prior-Ring Debt + Ring 4A — IO Foundation

**Status**: COMPLETE
**Ring**: 4 (Effects) — first increment
**Goal**: Close all prior-ring coverage gaps, then deliver `(print "hello")` — the IO model foundation.

## Scope

Two workstreams running in sequence: prior-ring debt first (blocking — these are defects in completed rings), then Ring 4A IO foundation.

### Prior-Ring Debt (priority)

Gaps found by the Phase 1 prior-ring coverage audit. These represent requirements the project claims to have delivered but hasn't verified.

| # | Type | Requirement | Owner | Description |
|---|------|------------|-------|-------------|
| D1a | Coverage gap (R1) | Builtin docstrings — storage | /typecheck | spec/appendix-a-builtins.md §A.5: Primitives have `DefKind::Primitive` with no docstring field. Add docstring to primitive registrations in `builtins.rs` using the Description column text from §A.3. Special forms already have `description` fields. |
| D1b | Coverage gap (R1) | Builtin docstrings — display | /int | Surface special form `description` and new primitive docstrings via `/doc` command and universal output format `:Type name ; classification - docstring`. |
| D2 | Coverage gap (R3) | `/expand` tests | /qa | 3 test scenarios in repl/spec.md §11.1/§11.5 reference nonexistent tests. Write: single macro expand, nested macro expand, no-macro-calls expand. |
| D3 | Coverage gap (R3) | Macro expansion errors | /qa | spec/12-runtime.md:188 — verify non-Sexp return type and expansion limit exceeded produce correct errors. |
| D4 | Stale annotations | IGNORED cleanup | /repl | 6 stale IGNORED annotations in repl/spec.md: 3 reference missing tests, 2 reference tests that pass (upgrade to [Tested]), 1 has name mismatch. |
| D5 | Negative coverage | Risk-based negative test review | /qa | Review ALL spec sections (spec/*.md, repl/spec.md) for negative coverage gaps — not just MUST NOT requirements but any requirement where bracketing matters (feature does not extend beyond its scope). Prioritise by risk: module boundaries, type system invariants, visibility rules, output format boundaries, category containment. Write tests for highest-risk gaps. Update annotations from `[Tested]` to `[Tested+Neg]` where negative tests exist. |
| D6 | Traceability | R3 annotation audit | /qa | ~30 `[R3 S*]` tags across spec files need verification: upgrade to `[Tested]` where tests exist, flag genuine gaps. |

### Ring 4A: IO Foundation

The most user-visible Ring 4 capability: side effects via `(print "hello")`.

| # | Feature | Owner | Description |
|---|---------|-------|-------------|
| I1 | IO ADT typing | /typecheck | IO type in typechecker: `IO a` as a builtin type. Type rules for `pure`, `bind`, `do`. `main :: () -> IO ()` signature for batch entry. |
| I2 | IO trampoline | /backend | Codegen for IO effect chain: build IO tree, trampoline evaluates it. Effect nodes dispatched to platform. |
| I3 | Platform DLL loading | /int | Load platform `.dylib`/`.so` at startup. `(platform stdio)` declaration in entry module. Platform manifest, effect dispatch table. |
| I4 | `print` / `read-line` | /platform | `cranelisp-stdio` platform DLL: `print` and `read-line` effects via C-ABI contract. `cranelisp-test-capture` platform for test harness. |
| I5 | `pure` / `do` / `bind!` | /stdlib | IO combinators in stdlib. `pure` lifts a value, `do` sequences effects, `bind!` sugar for bind chains. |
| I6 | Batch IO entry | /int | `main :: () -> IO ()` — batch programs with IO effects. `cargo run -- --run` executes the trampoline. |
| I7 | REPL IO | /int | IO expressions at the REPL evaluate effects immediately (trampoline runs inline). |

## FIXME Debt

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `repl/spec.md:837` | /repl | Terminal styling — Ring 4 scope | Carry — evaluate for inclusion in a later Ring 4 sprint |

## Architecture Review

**Reviewer**: /arch
**Status**: APPROVED with notes

### Technical Coherence

The sprint forms a complete, testable increment. The two workstreams (prior-ring debt then IO foundation) are correctly sequenced: debt items are prerequisite defects in completed rings and must be fixed before building new features on that base. The IO foundation scope (I1-I7) is the minimal vertical slice to get `(print "hello")` working end-to-end: type system, codegen, runtime trampoline, platform DLL, stdlib combinators, and both batch/REPL integration. This is the right decomposition.

The wave structure correctly captures the dependency chain: I1 (types) before I2 (codegen) and I5 (stdlib); I4 (platform DLLs) before I3 (loading); I2+I3 before I6/I7 (integration). No circularity.

**One concern with Wave 4 parallelism**: /stdlib (I5) is listed as depending only on I1, but `pure` is an ordinary Cranelisp function that constructs `Pure` nodes, meaning it needs the `Pure` constructor to be available (which it will be once I1 seeds the IO ADT). However, `do` and `bind!` are macros that expand to `bind` calls, and `bind` is an inline primitive (I1/I2). The stdlib macros can be written before the backend handles `bind` codegen, but they cannot be *tested* until I2 is also complete. This is acceptable as long as /stdlib understands that testing is blocked on I2, not just I1.

### No Interim Architecture (Principle 8)

No violations found. The IO model is the final mechanism per the spec (10-io.md). There are no temporary IO primitives being built that a later ring would replace. The trampoline, platform ABI, and IO ADT are all the production design.

One note: the `Par` constructor (tag=3) and automatic IO scheduling (spec 10.12) are scoped to Ring 4 Sprint 11 (later sprint), not this sprint. The sprint correctly omits them. The trampoline should handle only Pure/Effect/Bind for now; the `Par` path can be added when auto-scheduling lands. The IO ADT seed should include Bind as internal (tag=2) but should NOT include Par (tag=3) yet, to avoid dead code and untested paths. When Par arrives, it will be an additive change (new constructor + new trampoline branch).

### Design Questions — Answers

**I1: IO type representation — `Type::ADT("IO", vec![a])` vs `Type::IO(Box<Type>)`**

**Decision: Use `Type::ADT(TypeName::from("IO"), vec![a])`.**

Rationale:
- The spec (10.1.1) explicitly states IO participates in the type system as an ordinary ADT with no special type-checking rules. Adding a dedicated `Type::IO` variant would contradict this.
- IO propagation works through standard HM unification. `Type::ADT` supports this without special-casing.
- The sketch uses `Type::ADT("IO", ...)` and it works correctly. ADT machinery (constructor typing, exhaustiveness checking for user-accessible constructors, heap classification) already handles IO.
- A dedicated variant would add a branch to every `match` on `Type` across all crates, violating principle 2 (narrow interfaces) and principle 1 (decoupling).
- IO-specific behavior (trampoline forcing, REPL display) is detected by checking `Type::ADT(name, _) if name == "IO"` at the integration boundary, not inside the type system. This is the correct location.

**I2: IO trampoline design — recursive interpreter vs iterative trampoline**

**Decision: Iterative trampoline with explicit continuation stack (as in the sketch).**

The sketch's `IoTask::run()` in `intrinsics.rs` is already iterative, not recursive. It uses a `Vec<Continuation>` as an explicit stack and processes nodes in a `loop` with `match` on the tag. This is the correct design per spec 10.8.2: "This loop is iterative -- no recursion, O(1) call stack depth regardless of chain length."

Architecture placement: The trampoline lives in `cranelisp-runtime` (not `cranelisp-backend`). It is a runtime function (`cranelisp_run_io`) called from JIT-compiled code. The backend's responsibility is codegen for `bind` (allocating Bind nodes) and `Pure`/`Effect` constructors; the runtime's responsibility is interpreting the tree.

RC considerations for IO nodes:
- Pure/Effect/Bind nodes are heap-allocated ADTs and participate in the RC system.
- `bind` inline primitive must inc both the inner IO value and the continuation closure when storing them in the Bind node (sketch does this correctly at codegen/primitives.rs:177-178).
- The trampoline consumes IO nodes: once a node is processed (tag read, fields extracted), the node itself is no longer needed. However, the trampoline does NOT dec IO nodes — it reads their fields by raw pointer offset. The IO tree is a temporary structure that is freed when its RC reaches zero through normal scope exit. This is acceptable because IO trees are typically short-lived (built, forced, done).
- **CAUTION**: Effect thunks are double-boxed Rust closures (`Box<Box<dyn FnOnce() -> i64>>`). The trampoline calls `call_effect_thunk` which does `Box::from_raw` to reclaim ownership and invoke the closure. This consumes the thunk — it is valid to call exactly once. The backend must not emit code that could force the same Effect node twice.

**I3: Platform DLL ABI — review and version pin**

**Decision: Adopt the sketch's `cranelisp-platform` C-ABI contract. Pin ABI version at 1 for the reimplementation.**

Review findings on the sketch's ABI (currently version 3):

1. **`PlatformManifest` / `PlatformFn` / `HostCallbacks` structs**: Sound. All `#[repr(C)]` with explicit layout. Raw pointer + length pairs for strings are the standard C-ABI pattern. The `HostCallbacks` struct contains only `alloc: extern "C" fn(i64) -> i64`, which is minimal and correct.

2. **`CLIO<CL>` wrapper**: Sound. The `effect()` / `effect_on_resource()` methods correctly double-box the closure to produce a thin pointer. `call_effect_thunk` correctly reclaims ownership. The `pure()` method allocates a 2-field node (tag + value) using the host allocator, which is correct for RC integration.

3. **`CLOwned` / `CLHeap` RAII wrappers**: Sound. These give platform authors safe RC management for heap values (strings) they capture across effect thunk boundaries. The `inc_rc`/`dec_rc` use atomic operations consistent with the reimplementation's atomic-RC-from-Ring-1 decision (arch decision 13).

4. **`declare_platform!` macro**: Sound. Generates the `cranelisp_platform_manifest` entry point, initializes host callbacks, builds the function descriptor array with leaked allocations (static lifetime). The leaked allocations are acceptable — manifests live for the process lifetime.

5. **`SchedulingClass` enum**: Correct for forward compatibility. Ring 4A only needs `Sequential`. `Commutative` and `ResourceSerial` are future-proofing for Ring 4's auto-scheduling (10.12), but including them in the ABI from the start avoids a version bump later.

6. **Potential issue — `GLOBAL_ALLOC` is per-DLL**: Each DLL gets its own copy of the `AtomicPtr` static. This is correct (each DLL's `CLString::from()` uses the host allocator, not its own). But it means `HostContext::init()` must be called per DLL. The `declare_platform!` macro handles this correctly.

**Version pinning**: The reimplementation starts at ABI version 1 (not 3). The sketch's version 3 reflects its own iteration history. The reimplementation's ABI is a fresh contract. Future breaking changes bump the version; the runtime checks `manifest.abi_version == ABI_VERSION` at load time.

**I3: Platform search path convention**

**Decision: Three-tier search with `CRANELISP_PLATFORM_PATH` env var override.**

Search order (first match wins):
1. `CRANELISP_PLATFORM_PATH` env var, if set — colon-separated list of directories
2. `./platforms/` relative to the project root (the project_root used by the REPL session)
3. Cargo build output: `target/debug/` then `target/release/` (development convenience only)
4. `~/.cranelisp/platforms/` (user-global install location)

The sketch's `resolve_platform_path` already implements items 2-4. Adding `CRANELISP_PLATFORM_PATH` as item 1 provides the missing explicit override mechanism. This is consistent with standard Unix conventions (`LD_LIBRARY_PATH`, `PATH`).

**Drop**: Explicit filesystem path (containing `/` or extension) is treated as a direct path, bypassing search. The sketch handles this correctly.

**I6: Batch entry convention**

**Decision: Confirm `main :: (Fn [] (IO _))` per spec 10.6.**

The spec (10.6) is clear: "Batch programs MUST define a function named `main` with no parameters. The return type of `main` MUST be `IO _`."

The sketch implements this correctly: `check_program()` validates `main` exists with type `() -> IO _` (primitives.rs:235-263). The JIT entry point calls `main()`, checks if the return type is `IO`, and if so, forces the IO tree via `cranelisp_run_io()` (jit.rs:1227-1236).

**Adjustment for the reimplementation**: The spec says `main` returns `IO _` (IO of any type). The exit code is determined by the inner value when it is `IO Int` (10.6.1). The reimplementation should:
- Require `main :: (Fn [] (IO _))` at the type level (reject `main :: (Fn [] Int)`)
- Always force the IO tree via the trampoline
- Use the inner result as the process exit code when it is `Int`; default to exit code 0 for other inner types

This matches the sketch's behavior and the spec. No changes needed.

### Interface Types — Required Extensions

The existing `cranelisp-types` interface definitions already accommodate IO:

1. **`Type::ADT` is sufficient** — no new `Type` variant needed (see I1 answer above).

2. **`PrimitiveKind::PlatformEffect` already exists** in `design/arch/interfaces.md` — this is the classification for platform functions like `print`. No change needed.

3. **`DefKind::Primitive` needs a `docstring` field** (D1a). The current definition has `primitive_kind` and `jit_name` but no docstring. This is a minor additive change:

```rust
/// A built-in primitive (inline IR, extern FFI, or platform effect).
Primitive {
    primitive_kind: PrimitiveKind,
    jit_name: Option<JitSymbol>,
    docstring: Option<String>,      // NEW — Sprint 16 D1a
},
```

4. **`ModuleEntry::PlatformDecl`** already exists in the interfaces — no change needed.

5. **`ModuleInfo.platforms` and `ModuleDecls.platforms`** already exist — no change needed.

6. **`ConstructorInfo.internal: bool`** — this field is needed to mark Bind (and later Par) as non-user-constructable/matchable. If not already present in the reimplementation's `ConstructorInfo`, it must be added. The sketch has this field on its `ConstructorInfo` struct.

### Concerns

1. **D1a scope creep**: Adding docstrings to all primitives is the right thing to do, but the text source (spec/appendix-a-builtins.md A.3 Description column) must be treated as authoritative. /typecheck should pull strings verbatim from the spec, not invent new ones.

2. **D5 is open-ended**: "Review ALL spec sections for negative coverage gaps" is unbounded work. /qa should timebox this and prioritize by risk as described (module boundaries > type system invariants > visibility > output format > syntax). The sprint proposal already says "highest-risk gaps" which is appropriate. /arch recommends D5 produce a written risk assessment document (even if brief) so the project has visibility into which areas remain uncovered.

3. **IO node RC and the trampoline**: The trampoline reads IO node fields by raw pointer. It does not participate in RC. This means the IO tree must remain live (RC > 0) for the duration of the trampoline run. In batch mode, `main()` returns the IO tree, and the trampoline runs immediately — the tree is live because the return value holds a reference. In REPL mode, the same applies: the eval result holds a reference while the trampoline runs. This is safe as long as no code path drops the IO tree reference before the trampoline completes. /backend and /int should be aware of this invariant.

4. **Effect thunk lifetime**: Effect thunks capture Rust closures that may reference Cranelisp heap values (e.g., the string argument to `print`). The platform DLL must ensure these captures are properly RC'd. The sketch handles this via `CLOwned<CLString>` — platform functions that capture heap values create an owned handle that inc's RC on creation and dec's on drop. The reimplementation must preserve this pattern. /platform's design doc should document the capture-RC protocol explicitly.

5. **`bind` codegen incs both arguments**: When `bind` allocates a Bind node `[tag=2, inner_io, cont]`, it must inc both `inner_io` and `cont` because the Bind node holds references to them. The sketch does this (codegen/primitives.rs:177-178). The reimplementation's /backend must replicate this. Drop glue for IO ADT nodes must dec the fields — Pure decs the inner value (if heap), Effect does not dec the thunk pointer (it is consumed by the trampoline), Bind decs both inner_io and cont.

6. **No `cranelisp-test-capture` in this sprint?**: I4 lists `cranelisp-test-capture` as part of the platform task. This is valuable for IO integration tests (capturing output instead of printing to stdout). However, it is technically optional for the first IO milestone. If /platform finds the test-capture DLL adds significant complexity, it can be deferred to a follow-up sprint without blocking `(print "hello")`. The /qa tests can use process-level stdout capture (spawn subprocess, capture output) as a simpler alternative for Sprint 16.

### Debt Review

Per the arch role's debt-first principle:

- **D1a/D1b** (builtin docstrings): Correctly prioritized. This is a Ring 1 gap that should have been caught earlier. Small, well-scoped.
- **D2/D3** (expand tests, macro errors): Ring 3 gaps. Small, well-scoped.
- **D4** (stale IGNORED): Bookkeeping. Trivial.
- **D5** (negative coverage): Important but open-ended. See concern #2 above.
- **D6** (R3 annotation audit): Bookkeeping with potential to surface real gaps.
- **FIXME debt** (terminal styling): Correctly carried. Not blocking and not related to IO.

No items have been deferred twice. The debt-first sequencing (Wave 1 before Wave 4) is correct.

### Summary

**The sprint is architecturally sound.** The scope forms a complete vertical slice. No interim architecture. Interface types need only one minor extension (docstring on `DefKind::Primitive`) plus verification that `ConstructorInfo.internal` exists. All design questions answered above. No blocking issues identified.

Design doc authors (/typecheck, /backend, /platform, /int) should reference the answers above as architectural constraints for their design docs in Wave 2.

## Skill Plans

### /int
**Task**: D1b (builtin docstrings display), I3 (platform DLL loading), I6 (batch IO entry), I7 (REPL IO)
**Design doc**: `design/int/io-integration.md` (new)
**Approach**: TBD — filled by /int. I3: three-tier platform search path: `CRANELISP_PLATFORM_PATH` env var → `./platforms/` → Cargo output → `~/.cranelisp/platforms/` (/arch decision I3). I6: batch entry requires `main :: (Fn [] (IO _))`, trampoline forces the IO tree, exit code from inner value when Int, default 0 (/arch decision I6). I7: REPL IO trampoline runs inline on eval result. **Critical invariant**: IO tree must stay live (RC > 0) for the duration of the trampoline run — no code path may drop the IO tree reference before trampoline completes (/arch concern #3).
**Design refs**: `spec/10-io.md`, `spec/12-runtime.md`, `repl/spec.md §1.1`, `spec/appendix-a-builtins.md §A.5`, sketch `src/platform.rs`, sketch `src/pipeline.rs`
**Acceptance**: `(print "hello")` works in REPL and batch. `/doc if` shows docstring. `/doc add-i64` shows docstring. Platform search path follows 3-tier convention.

### /typecheck
**Task**: D1a (builtin docstrings storage), I1 (IO ADT typing)
**Design doc**: `design/typecheck/io-types.md` (new)
**Approach**: TBD — filled by /typecheck. D1a: add `docstring: Option<String>` to `DefKind::Primitive` in `cranelisp-types`. Pull strings verbatim from spec/appendix-a-builtins.md §A.3 Description column — do not invent new ones (/arch concern #1). I1: IO as `Type::ADT("IO", vec![a])` — no dedicated variant (/arch decision I1). Seed IO ADT with Pure (tag=0), Effect (tag=1), Bind (tag=2, internal=true). Do NOT include Par (tag=3) yet (/arch note on Principle 8). Verify `ConstructorInfo.internal: bool` exists or add it.
**Design refs**: `spec/10-io.md §10.1-10.5`, `spec/03-types.md`, `spec/appendix-a-builtins.md §A.3-A.5`, sketch `src/typechecker.rs` IO handling
**Acceptance**: `(pure 42) :: IO Int` type-checks. `(do (print "hello") (pure 0)) :: IO Int` type-checks. Type errors for non-IO in do-chain. All primitives have docstrings accessible via `DefKind`. Bind marked internal, Par not present.

### /backend
**Task**: I2 (IO trampoline)
**Design doc**: `design/backend/io-trampoline.md` (new)
**Approach**: TBD — filled by /backend. Trampoline is iterative with explicit continuation stack, lives in `cranelisp-runtime` (/arch decision I2). `bind` codegen MUST inc both `inner_io` and `cont` when building Bind node (/arch concern #5). Drop glue: Pure decs inner value if heap; Effect does NOT dec thunk pointer (consumed by trampoline); Bind decs both inner_io and cont. IO tree must stay live (RC > 0) during trampoline run — no code path may drop the IO tree reference before trampoline completes (/arch concern #3). Effect thunks are consumed exactly once — backend must not emit code that forces same Effect node twice (/arch concern from I2 CAUTION).
**Design refs**: `spec/10-io.md §10.6-10.9`, `spec/12-runtime.md`, sketch `src/codegen.rs` IO codegen, sketch `src/intrinsics.rs` trampoline
**Acceptance**: IO tree built at codegen time. Trampoline executes effects via platform dispatch. RC correct for IO values. `bind` incs both args. Effect thunks consumed exactly once.

### /platform
**Task**: I4 (stdio platform DLL; test-capture optional)
**Design doc**: `design/platform/platform-dlls.md` (new or update existing)
**Approach**: TBD — filled by /platform. Adopt sketch's `cranelisp-platform` C-ABI contract at ABI version 1 (/arch decision I3). Design doc MUST document the capture-RC protocol explicitly: platform functions that capture heap values across effect thunk boundaries must use `CLOwned<CLString>` (inc on create, dec on drop) (/arch concern #4). `cranelisp-test-capture` is optional for this sprint — /qa can use subprocess stdout capture as simpler alternative (/arch concern #6). If test-capture adds significant complexity, defer to follow-up sprint.
**Design refs**: `spec/10-io.md`, sketch `cranelisp-platform/`, sketch `platforms/`
**Acceptance**: `cranelisp-stdio` provides `print` and `read-line`. Platform loads via `(platform stdio)` declaration. Capture-RC protocol documented.

### /stdlib
**Task**: I5 (`pure`, `do`, `bind!` IO combinators)
**Design doc**: n/a — implementing spec, not new design
**Approach**: Port IO helpers from sketch `lib/core/io.cl`. `pure` wraps value in IO (uses Pure constructor, available once I1 seeds IO ADT). `do` and `bind!` are macros that expand to `bind` calls — can be written after I1 but cannot be tested until I2 (backend `bind` codegen) is also complete (/arch Wave 4 parallelism note).
**Design refs**: `spec/10-io.md §10.3-10.5`, sketch `lib/core/io.cl`, sketch `lib/prelude.cl`
**Acceptance**: `(pure 42)` returns `IO Int`. `(do (print "a") (print "b"))` sequences. `(bind! [x (read-line)] (print x))` works.

### /qa
**Task**: D2 (/expand tests), D3 (macro error tests), D5 (risk-based negative coverage review), D6 (R3 annotation audit)
**Design doc**: n/a
**Approach**: (1) Write 3 /expand E2E tests. (2) Verify macro error handling, write tests if missing. (3) Risk-based negative coverage review: walk ALL spec sections (spec/*.md, repl/spec.md), assess each for negative test needs — not just MUST NOT but any requirement where bracketing matters (feature doesn't extend beyond its scope). Prioritise by risk: module boundaries > type system invariants > visibility rules > output format > syntax. Write tests for highest-risk gaps. Update `[Tested]` → `[Tested+Neg]` where negative tests exist. **Timebox D5 and produce a brief written risk assessment** documenting which areas were reviewed, what gaps were found, and which remain uncovered (/arch concern #2). (4) Audit ~30 R3 tags, upgrade annotations. (5) Write IO integration tests from ring4.md plan. IO tests may use subprocess stdout capture instead of test-capture DLL (/arch concern #6).
**Design refs**: `repl/spec.md`, `spec/*.md`, `tests/plan/ring4.md`
**Acceptance**: All prior-ring coverage gaps closed. Risk-based negative coverage assessment document produced. Highest-risk negative tests written, annotations updated. R3 tags either upgraded to `[Tested]` or flagged as genuine gaps. IO tests pass.

### /repl
**Task**: D4 (stale IGNORED cleanup), IO REPL experience validation
**Design doc**: n/a
**Approach**: (1) Fix 6 stale IGNORED annotations: upgrade 2 to [Tested], update/remove 4 referencing missing tests. (2) After IO lands, validate REPL IO experience.
**Design refs**: `repl/spec.md §11`
**Acceptance**: Zero stale IGNORED annotations. IO expressions produce visible output at REPL.

### /arch
**Task**: Architecture review of I1-I7, answer design questions
**Approach**: Review IO model design against sketch, confirm type representation, trampoline design, platform ABI, batch entry convention.
**Acceptance**: All design questions answered. No architectural blockers.

### /review
**Task**: Code review after implementation waves
**Approach**: Review IO pipeline additions for quality: function length, no unwrap, RC correctness in IO paths, no duplicate trampoline logic between batch/REPL.
**Acceptance**: No Blockers or Important findings.

### /frontend
**Task**: No changes expected for IO — IO forms are macros/special forms handled by existing infrastructure.

### /examples
**Task**: Write IO example programs after IO lands (e.g., `examples/21-hello-io.cl`, `examples/22-echo.cl`).
**Acceptance**: IO examples compile and run correctly.

### /port
**Task**: Evaluate IO impact on exemplar. Plan how Sudoku solver will use IO for output.
**Acceptance**: Plan documented in exemplar notes.

### /docs
**Task**: No action until IO is stable. Plan IO section for language guide.

## Waves

_To be filled during Phase 4 after /arch review and skill plans are finalized._

Anticipated wave structure:

### Wave 1: Architecture review + prior-ring debt (parallel)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Review I1-I7, answer design questions | done | APPROVED with notes. 6 concerns documented. See Architecture Review section. |
| /qa | D2: /expand tests, D3: macro error tests | deferred | Worktree agent wrote tests against sketch codebase (wrong base). Tests need rewriting for reimplementation. Moved to Wave 3. |
| /qa | D5: risk-based negative coverage review (all spec sections) | done | Assessment document saved to `tests/plan/negative-coverage.md`. 17 test specifications identified across P1-P5 priorities. Tests themselves need writing for reimplementation (worktree wrote against sketch). |
| /qa | D6: R3 annotation audit | done | 6 stale IGNORED annotations fixed in repl/spec.md: 3→[R3 S16], 2→[Tested], 1 name mismatch fixed. 7+ R3 annotations upgraded to [Tested]. defmacro in appendix-a-builtins.md upgraded. |
| /repl | D4: stale IGNORED cleanup | done | Annotations updated in repl/spec.md — /expand retargeted to S16, /imports and /exports upgraded to [Tested], macro annotations upgraded. |
| /typecheck | D1a: add docstrings to primitive registrations | deferred | Worktree agent modified sketch's builtins.rs (wrong codebase). Reimplementation's `crates/cranelisp-typecheck/src/builtins.rs` needs same treatment. Moved to Wave 4 alongside I1. |

### Wave 2: Design docs (parallel)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /int | D1b: surface builtin docstrings via /doc + universal format | blocked | Blocked on D1a (deferred to Wave 4) |
| /typecheck | Write design doc: IO types | done | `design/typecheck/io-types.md` |
| /backend | Write design doc: IO trampoline | done | `design/backend/io-trampoline.md` |
| /platform | Write design doc: platform DLLs | done | `design/platform/platform-dlls.md` |
| /int | Write design doc: IO integration | done | `design/int/io-integration.md` |

### Wave 3: Design review + deferred debt tests
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Review design docs for I1-I7 | done | All 4 docs APPROVED WITH NOTES. 1 blocking: RC ordering in platform (Relaxed→SeqCst for dec). 4 non-blocking: Effect resource_token needs spec update, batch main leniency vs spec, REPL IO format pending /repl, PlatformDecl duplication check. |
| /qa | Derive test cases from design docs, update ring4.md | pending | |
| /qa | D2: Write /expand E2E tests (reimpl) | done | Already existed: 4 tests in tests/e2e.rs (e2e_s11_1_expand_*). No new tests needed. |
| /qa | D3: Write macro error tests (reimpl) | done | 6 new tests in tests/macros.rs: non-Sexp return (batch+REPL+Bool), depth limit, arity mismatch, session corruption. All pass. |
| /qa | D5 tests: Write highest-priority negative tests (reimpl) | done | 16 new tests: 6 P1-HIGH module boundaries (ring2.rs), 6 P2-HIGH/MED type system (ring2.rs), 3 P5-MED pattern matching (ring1.rs), 1 companion positive. 15 pass, 1 ignored (constrained fn as value — spec 3.6.6 gap). |

### Wave 4: IO implementation (parallel where possible)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /typecheck | I1: IO ADT typing + D1a: docstrings | done | IO ADT (Pure/Effect/Bind) seeded in `primitives`. ConstructorInfo.internal added. bind inline primitive registered. 12 unit tests. Builtin docstrings for all §A.3 primitives. IO types imported as Import entries (not direct) to avoid /list leakage. |
| /platform | I4: stdio DLL (test-capture optional) | done | Full C-ABI contract in cranelisp-platform. ABI v1. platforms/stdio/ + platforms/test-capture/ created and compile. CLOwned capture-RC protocol. SeqCst ordering. |
| /stdlib | I5: pure/do/bind! combinators | done | `stdlib/core/io.cl`: pure, >>, map-io, when-io, unless-io, sequence-io. Exported via core.cl + prelude.cl. FIXME(/stdlib) filed re `do` semantics transition. |
| /backend | I2: IO trampoline | done | `crates/cranelisp-runtime/src/io.rs`: iterative trampoline with continuation stack. `bind` inline codegen in apply.rs. `runtime/run_io` JIT symbol. 9 unit tests (incl 1000-deep chain). |
| /int | D1b: surface builtin docstrings | done | `/doc` already worked (D1a stored docstrings in ModuleEntry). `; primitive` classification added for primitives in /sig output. |
| /int | I3: platform DLL loading | done | `src/platform.rs`: DLL loading, manifest validation, type registration. 3-tier search path. Platform forms intercepted in pipeline.rs (batch) and repl.rs (REPL). 14 unit tests. `libloading` added. |
| /typecheck | Constrained fn fix | done | Spec §3.6.6 enforced: `in_call_position` flag in infer.rs rejects bare constrained fn references. 0 ignored tests. |
| /int | I6: batch IO entry | done | IO detection in pipeline.rs, trampoline invocation after main, exit code from (IO Int). 5 unit tests. Non-IO programs unaffected. |
| /int | I7: REPL IO | done | IO detection in eval_and_display(), force_io_and_format() with catch_unwind safety, :(IO T) display format. 6 unit tests. |

### Wave 5: Verification + showcase
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /review | Code review of IO additions | done | 2B + 6I + 7S findings. All B+I fixed. See `design/review/sprint16-wave4.md`. |
| /qa | IO integration tests | done | 25 tests in `tests/io.rs`: Pure pipeline, bind pipeline, internal ctor rejection, IO type checking, REPL IO eval, match/let. Found nested-bind SIGSEGV — fixed (consuming calling convention for bind). |
| /examples | Verify existing examples | done | All 19 examples compile and run. No breakage from IO work. |
| /port | Evaluate IO impact on exemplar | done | Exemplar is pure computation — IO only needed for future `main.cl`. No changes needed this sprint. |
| /repl | Validate REPL IO experience | done | IO display format `:(IO T) value` is correct. Minor spec elaboration needed (repl/spec.md line 126). `eval_platform()` code review clean. |

## Notes

**2026-03-09**: Wave 1+2 execution. Spawned 8 parallel agents for debt tasks and design docs. All 4 design docs completed successfully. However, the 4 worktree agents (D1a, D2+D3, D4+D6, D5) were created from the wrong git base commit (`97bf7d3` orphan initial commit instead of `747e6e8` main HEAD). Consequence: test code and source changes written against the sketch codebase cannot be directly merged to the reimplementation. Resolution:
- D4+D6 annotation changes: Applied manually to main (spec/doc files are shared)
- D5 negative coverage assessment: Saved to `tests/plan/negative-coverage.md` (pure documentation)
- D1a primitive docstrings: Deferred to Wave 4 (needs to target reimplementation's `crates/cranelisp-typecheck/src/builtins.rs`)
- D2+D3 /expand and macro error tests: Deferred to Wave 3 (needs reimplementation test helpers)
- D5 negative tests (17 specified): Test implementations deferred (need reimplementation test infrastructure)
- All worktrees removed and branches cleaned up

**Next**: Wave 3 — design review (/arch reviews 4 design docs, /qa derives test cases and writes deferred tests D2+D3+D5)

**2026-03-09**: Wave 3 arch design review complete. All 4 docs APPROVED WITH NOTES.
- **Blocking fix applied**: RC ordering in platform-dlls.md changed from `Relaxed` to `SeqCst` for dec operations (unsound per arch decision 13).
- **Spec fix applied**: Effect node layout in spec/10-io.md updated to include `resource_token` field for forward compatibility with auto-scheduling (§10.12). FIXME(/spec) filed for verification when Par lands.
- **Non-blocking notes**: (1) Batch `main` validation: recommend warning for non-IO main (transitional), not error. (2) REPL IO display format: pending /repl decision. (3) `PlatformDecl` already exists in interfaces.md — verify before implementation. (4) Effect thunk leak on dropped branches is acceptable (bounded, with clean upgrade path). (5) `bind` is unique among inline primitives in having RC responsibilities — document this for maintainers.
- QA agent complete: 22 new tests (6 macro + 13 ring2 + 3 ring1). 21 pass, 1 ignored.
- **Implementation gap found**: `neg_constrained_fn_in_closure` (spec 3.6.6) — reimplementation does not reject constrained polymorphic functions used as bare values. Test ignored with proper annotation. Not a Sprint 16 blocker (Ring 2 issue, defer to separate fix).
- `tests/plan/negative-coverage.md` updated with actual test locations and status.
- **Test count**: 1097 total (1096 passing, 1 ignored). Up from 1075.

**Wave 3 COMPLETE**. Ready for Wave 4 (IO implementation).

**2026-03-09 (cont'd)**: Wave 4 Phase 1 — I1+D1a and I4 completed.
- I1+D1a agent: IO ADT seeded (Pure tag=0, Effect tag=1, Bind tag=2 internal), `bind` inline primitive registered, builtin docstrings added for all §A.3 primitives (12 new unit tests). Agent hit rate limit mid-session but all changes were complete.
- I4 agent: Full C-ABI contract in `cranelisp-platform/src/lib.rs`, `platforms/stdio/` and `platforms/test-capture/` DLLs created and compile.
- **Test regression fixed**: IO types (Pure, Effect, IO) were leaking into `/list` output because `import_primitives_into_user` copied TypeDef/Constructor entries directly. Fixed by converting them to Import entries — IO types are accessible but don't appear as user definitions. All 1096 tests pass (1 ignored).
- **Test count**: 1097 total (1096 passing, 1 ignored). Same as Wave 3 close — new IO tests were already counted from incomplete agent run.

**Wave 4 Phase 2** — I2, I5, I3+D1b completed in parallel.
- I2 agent: Iterative IO trampoline (`cranelisp-runtime/src/io.rs`), `bind` inline codegen in apply.rs, `runtime/run_io` JIT symbol registered. 9 unit tests including 1000-deep bind chain.
- I5 agent: `stdlib/core/io.cl` with 6 combinators (pure, >>, map-io, when-io, unless-io, sequence-io). Exported via core.cl + prelude.cl. Found `do` semantics conflict (pure let-based vs IO bind-based) — FIXME(/stdlib) filed.
- I3+D1b agent: `src/platform.rs` with full DLL loading pipeline (3-tier search, manifest validation, type registration). D1b verified: `/doc` already works, added `; primitive` classification. 14 unit tests.
- **Constrained fn fix**: Spec §3.6.6 now enforced via `in_call_position` flag in infer.rs. Ignored test un-ignored. **0 ignored tests.**
- **Test count**: 1111 total (1111 passing, 0 ignored). Up from 1097.

**Wave 4 Phase 2 COMPLETE.** Remaining: I6 (batch IO entry) + I7 (REPL IO) — both deps satisfied.

**Wave 4 Phase 3** — I6 and I7 completed.
- I6 agent: IO detection in `pipeline.rs`, trampoline invocation via `run_io_trampoline()`, exit code propagation from `(IO Int)`. 5 unit tests. Non-IO programs unaffected.
- I7 agent: IO detection in `repl.rs` eval loop, `force_io_and_format()` with `catch_unwind` safety, `:(IO T)` display format. 6 unit tests.
- Both agents defined `is_io_type`/`extract_io_inner_type` independently (pipeline.rs and repl.rs) — acceptable duplication for now, can be factored to shared module later.
- **Test count**: 1122 total (1122 passing, 0 ignored). Up from 1111.

**Wave 4 COMPLETE.** All I1-I7 + D1a+D1b + constrained fn fix delivered. Ready for Wave 5 (verification + showcase).

**Wave 5 Phase 1** — Code review complete, all findings fixed.
- `/review` delivered `design/review/sprint16-wave4.md`: 2 Blockers, 6 Important, 7 Suggestions.
- **B1 fixed** (/int): `determine_exit_code` doc contract clarified, param renamed to `inner_ty`.
- **B2 fixed** (/typecheck): `in_call_position` reset before arg inference, 2 new tests.
- **I1 fixed** (/int): IO helpers deduplicated to `Type::is_io()`/`Type::io_inner_type()` on types crate.
- **I2 fixed** (/typecheck): 3 `.expect()` → `unreachable!` in builtins.rs.
- **I3 fixed** (/platform): CLIO Clone/Copy removed.
- **I4 fixed** (/int): Send safety comment improved.
- **I5 fixed** (/platform): transmute through `*const ()`.
- **I6 fixed** (/typecheck): Internal constructor rejection enforced + exhaustiveness excludes internals + 2 tests.
- **Test count**: 1115 total (1115 passing, 0 ignored). Up from 1122 (some tests moved/consolidated during dedup).

Review findings resolved. Ready for remaining Wave 5: /qa, /examples, /port, /repl.

**Wave 5 Phase 2** — QA, examples, port, REPL validation complete.
- QA: 25 IO integration tests in `tests/io.rs`. **Found nested-bind SIGSEGV** — `(bind (bind ...) f)` crashed because `dec_temporary_args` applied drop glue to live ADT nodes. Fixed: bind now uses consuming calling convention (`compile_consuming_arg_list`), transferring ownership of temps instead of borrowing+dec. All 25 tests pass.
- Examples: All 19 existing examples verified — no breakage from IO.
- Port: Exemplar is pure computation, no IO needed yet. Future `main.cl` planned.
- REPL: IO display format verified correct. Minor spec elaboration needed for repl/spec.md line 126.
- **Test count**: 1140 total (1140 passing, 0 ignored). Up from 1115.

**Wave 5 COMPLETE.** Sprint close review found critical gaps — see Wave 6.

**Sprint close review findings (2026-03-09)**:
- **Blocker**: Effect codegen missing — `PlatformEffect` primitives can't compile. `(print "hello")` fails with "unknown builtin primitive: print". The backend has no dispatch for `PlatformEffect` calls. Platform DLLs already construct Effect nodes (`CLIO::effect()`), so the backend just needs to emit an extern call to the platform function's JIT symbol — but this path was never implemented.
- **Blocker**: `/qa` wrote 25 tests covering only Pure/bind — no tests for platform effects, `do`, `bind!`, or platform error handling. Tests shaped by implementation, not spec. QA skill definition updated with "Spec-Scope Test Coverage" rule. Sprint skill definition updated: `/qa` now runs in parallel with implementation, not after.
- **Gap**: R3 annotation audit upgraded 22 tags to `[Tested]`, found 5 genuine gaps retargeted to S17 (auto-currying, HKT traits, lazy sequences, appendix B examples).
- **Gap**: No IO demo showing actual effects. No IO examples using `print`.
- **Governance**: Platform-specific content (stdio functions, test-capture) doesn't belong in `spec/10-io.md`. Each platform should have its own spec under `platforms/`, with requirements filed by consumer skills (/repl, /port, /qa). Language spec keeps only the mechanism (§10.9–10.10).
- **Spec**: `par-let` is redundant given lenient evaluation — should be removed from spec.

### Wave 6a: Effect codegen + spec-surface tests + governance (parallel)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /backend | PlatformEffect codegen — compile platform function calls as extern calls to JIT symbols; the DLL returns the Effect node | done | `resolve_primitive_jit_name()` fixed to return JIT symbol names for platform effects. `is_known_builtin()` gate routes unrecognized builtins to extern calls. |
| /qa | Write spec-surface IO tests: `print` via test-capture, `do` macro, `bind!` sugar, platform error handling, `read-line`. Tests that fail start as `#[ignore]`. Also: R3 gap tests (auto-currying, HKT, lazy seq). | done | 38 new tests (52 pass, 11 ignored). Covers full spec surface including platform effects, batch entry, trampoline, ADTs, bind/do, negative tests. |
| /spec | Remove `par-let` from spec — lenient evaluation subsumes it. Remove specific platform references (stdio function signatures, etc) from `spec/10-io.md` — keep only mechanism (§10.9 declarations, §10.10 ABI contract). | done | 5 edits to spec/10-io.md. par-let was already removed previously. |
| /platform | Create per-platform specs: `platforms/stdio/spec.md`, `platforms/test-capture/spec.md`. Populate with requirements from /repl, /port, /qa, /examples. Update `/platform` skill definition to reflect governance model. | done | Platform specs created. Governance model added to platform.md. |
| /repl | File requirements on `platforms/stdio/spec.md` — what REPL needs from stdio (print for user output, read-line for future REPL input). | done | Requirements filed in platforms/stdio/spec.md. |
| /port | File requirements on `platforms/stdio/spec.md` — what exemplar needs from stdio (print for Sudoku output). Assess need for future `platforms/web/`. | done | Requirements filed. |

**Wave 6a COMPLETE.** Critical fix applied after agents: CLIO heap offset bug — `CLString`, `CLHeap`, and `CLIO` all stored/returned payload pointers but the compiler uses base pointers throughout. Fixed all three to use base pointer convention. `(print "hello")` now works end-to-end. 1526 tests pass (11 ignored in io.rs for future features; 8 flaky runtime counter tests pass when run serially).

### Wave 6b: Build/test/review cycle + showcase (after 6a)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /platform | CLIO base pointer fix — all CL* types (CLString, CLHeap, CLIO) now use base pointers matching compiler convention | done | Root cause: compiler uses base pointers, platform used payload pointers. Fixed CLString::as_str(), CLString::from(&str), CLHeap::inc_rc/dec_rc, CLIO::pure/effect. |
| /qa | Un-ignore Effect tests, fix IO test helper, run full suite | done | Fixed `repl_eval_display` to force IO values. Un-ignored 3 tests (REPL forcing, platform non-entry error, purity enforcement). 4 platform DLL tests retargeted to S17 (need platform-aware helper). 4 auto-curry tests kept ignored (R3). |
| /examples | Update `examples/21-hello-io.cl` to use `print` | done | Added Part 7 with 4 platform IO examples (print, bind+print, print+Pure, wrapper fn). Found `then` combinator double-free bug (tracked, not blocking). |
| /review | Review Effect codegen + CLIO base pointer fix + governance changes | done | `design/review/sprint16-wave6.md`: 2 Blockers, 4 Important, 4 Suggestions. B1+B2 fixed (heap_alloc_payload for platform DLLs). I1-I4 fixed via subagent delegation. |
| /platform | B1+B2: Add heap_alloc_payload, fix pointer convention | done | `heap_alloc_payload` returns payload ptr for DLLs. `HostCallbacks.alloc` wired to it. CLIO/CLString use payload ptr from alloc, store base ptr. |
| /platform | I2: Add SAFETY comments to all unsafe blocks | done | All unsafe blocks in CLIO, CLString, CLHeap, get_global_alloc annotated. |
| /platform | I3: Deduplicate HEAP_HEADER_SIZE constant | done | Added cranelisp-types dependency. `HEAP_HEADER_SIZE = cranelisp_types::HeapHeader::SIZE as i64`. |
| /platform | I1: ABI heap parameter ownership contract | done | Added "Heap Parameter Ownership" section to `platforms/stdio/spec.md` and `platforms/test-capture/spec.md`. |
| /qa | I4: Fix fragile IO test helper formatting | done | Replaced string splitting with balanced-paren parser (`extract_type_from_display`, `extract_value_from_display`). |
| /platform | Fix flaky runtime tests (delta-based assertions) | done | int.rs, string.rs, vec.rs — all use before/after deltas instead of absolute counter values. |
| /repl | Update `repl/demos/ring4a.demo` to show actual `(print "hello")` | deferred | Defer to sprint close — demo infrastructure not critical for gate |

**Wave 6b COMPLETE.** Review done: 2B+4I resolved, 4S accepted. Flaky tests fixed. **1833 passed, 0 failed, 9 ignored** (8 io.rs: 4 platform DLL → S17, 4 auto-curry → R3; 1 doctest).

## Outcome

**Status**: COMPLETE
**Test count**: 1833 passed, 0 failed, 9 ignored
**Test delta**: +123 from Sprint 15 (1710 → 1833)

### Delivered

**Prior-Ring Debt (D1-D6)**:
- D1a: Builtin docstrings for all §A.3 primitives (12 unit tests)
- D1b: `/doc` surfaces docstrings, `; primitive` classification in `/sig`
- D2: `/expand` E2E tests verified (4 existing tests cover spec)
- D3: 6 macro error tests (non-Sexp return, depth limit, arity, session corruption)
- D4: 6 stale IGNORED annotations fixed in repl/spec.md
- D5: 16 negative tests (module boundaries, type system, pattern matching)
- D6: R3 annotation audit — 22 tags upgraded to `[Tested]`, 5 genuine gaps retargeted to S17

**Ring 4A: IO Foundation (I1-I7)**:
- I1: IO ADT seeded (Pure/Effect/Bind) with internal constructors, `bind` inline primitive, IO type inference
- I2: Iterative IO trampoline with continuation stack, `bind` codegen, `runtime/run_io` JIT symbol
- I3: Platform DLL loading — 3-tier search path, manifest validation, type registration, `libloading`
- I4: `cranelisp-platform` ABI crate, `cranelisp-stdio` + `cranelisp-test-capture` DLLs
- I5: `stdlib/core/io.cl` — pure, >>, map-io, when-io, unless-io, sequence-io combinators
- I6: Batch IO entry — `main :: () -> IO ()`, trampoline invocation, exit code propagation
- I7: REPL IO — force_io_and_format, `:(IO T) value` display, catch_unwind safety

**Platform Governance**:
- Platform-specific specs under `platforms/stdio/spec.md` and `platforms/test-capture/spec.md`
- ABI heap parameter ownership contract documented
- `/platform` skill definition updated with governance model

**Code Quality**:
- Constrained fn bare-value rejection (spec §3.6.6) — `in_call_position` flag
- CLIO base pointer convention fix — `heap_alloc_payload` for DLL allocations
- SAFETY comments on all unsafe blocks in cranelisp-platform
- HEAP_HEADER_SIZE deduplication (derives from cranelisp-types)
- Flaky runtime tests fixed (delta-based assertions)
- IO test helper robustified (balanced-paren parsing)

**Review Cycles**:
- Wave 4 review: 2B + 6I + 7S — all B+I resolved (`design/review/sprint16-wave4.md`)
- Wave 6 review: 2B + 4I + 4S — all B+I resolved (`design/review/sprint16-wave6.md`)

### Deferred

- **REPL demo** (`repl/demos/ring4a.demo`): Demo infrastructure not critical for gate. Sprint 17.
- **4 platform DLL integration tests**: Need platform-aware test helper for Effect codegen path. Sprint 17.
- **4 auto-curry tests**: Ring 3 scope, need overload resolution pipeline. Ring 3 followup.
- **`then` combinator double-free**: RC bug with Effect nodes in discard patterns. Tracked, not blocking current IO usage.
- **5 R3 annotation gaps**: Auto-currying, HKT traits, lazy sequences, Appendix B examples. Sprint 17.
- **`do` macro semantics transition**: Current `do` is pure let-based; IO `do` needs bind-based version. Future stdlib sprint.

### Findings

- **Base pointer vs payload pointer convention** was the sprint's hardest bug. The compiler uses base pointers everywhere; platform DLL code expected payload pointers. Initial fix appeared to work but was memory corruption — only caught by `/review`. The proper fix (`heap_alloc_payload`) preserves both conventions cleanly. Lesson: review before close, not after.
- **Spec-first test coverage matters**: QA wrote 25 tests post-implementation that covered only Pure/bind, missing that `print` (the sprint's headline goal) had no Effect codegen. Skill definitions updated: `/qa` now runs in parallel with implementation, writing tests from the spec. Sprint close review caught the gap.
- **Flaky tests are bugs**: Runtime unit tests using absolute global counter values raced in parallel test runs. Fixed with delta-based before/after assertions. The user correctly rejected treating flakey tests as acceptable.
- **Platform governance model**: Platform-specific content (stdio functions, test-capture) removed from language spec. Each platform has its own spec under `platforms/`, with consumer requirements from /repl, /port, /qa, /examples.
- **Sprint skill definition updates**: (1) `/qa` parallel test coverage rule, (2) `/sprint` subagent delegation for minor FIXMEs, (3) `/platform` governance model.
