# Substance Scoping — Architecture Misalignment Register

**Status.** Authored Sprint 63 close, in-session, by `/arch`. No artefacts other than this document have been changed; no FIXMEs filed; no Decisions drafted. Recommendations are *proposals* — actioning waits for user acceptance.

**Pairs with.** `design/arch/substance-scoping-brief.md` (the spec this executes); `design/arch/reconciliation-plan.md` (the procedural plan this informs).

**Method.** Cross-doc synthesis across the six master design docs (Sprint 63), the seven facade specs, Decisions 1–39 inline in `design/arch/CLAUDE.md`, `principles.md`, `bounded-contexts.md`, `overview.md`, four 2026-04-23 audits, and the nine already-filed FIXMEs (0001–0009). Per-item depth is options + recommendation; brief §5 discipline applied throughout.

**Read order for the user.** *Synthesis* first (closes the question of "is the as-designed architecture viable as-is"). Then walk items in the order presented — within each section, items are sequenced so that gates appear before unlocks.

---

## Synthesis

The as-designed architecture is **viable as-is in its load-bearing shape** — the bounded contexts hold, the principles serve, Decisions 38 + 39 stand as the coherent target. The Sprint-63 master design pass surfaced no item that requires bounded-context redrawing or principle evolution. The architecture's *bones* are sound.

The architecture is **not viable as-stated in its facade contracts** — at least four facades have load-bearing silences (runtime: operator primitives + `runtime_panic` truth; backend: `compile_to_module` return shape; platform: `PlatformError` carrying `ErrorLocation`; frontend: `SymbolTables` alias generic constraint). These are not editorial fixes — they bind cross-skill coupling that integration-layer code cannot satisfy without a definitive contract. They become **Decision elevations**.

The architecture has **one bounded-context drift to arbitrate** — the runtime crate hosts ~25% of LOC in `io_trace.rs` + `trace.rs` that the BC explicitly excludes as "diagnostics, observability". This is the single substantive BC question in the queue. Two options resolve it; both are tractable.

The architecture has **two audit-coverage gaps** — runtime and platform have never been audited; two existing audits (typecheck, int) have target-direction sections superseded by Decisions 38/39. The annotate-and-defer recommendation in `reconciliation-plan.md` §3 is right for the existing four; the missing two need authored-from-scratch passes scheduled.

**Substance wave verdict.** A small substance wave is required before the procedural reconciliation Wave 1 lands. The wave's content is ~5 Decision elevations (items §1.2, §1.3, §1.4, §1.7, §2.7), one BC arbitration (§1.1), one Decision retraction + reframe + new Decision + crate split (§1.7 — the largest single item), and one audit-pass scheduling (§1.6). §1.7 is too big to bundle into the substance wave alongside the others — suggest scheduling as a separate Sprint-65+ wave gated by Decision 43 acceptance. Estimated effort: 8–12 hours of `/arch` work for the substance wave (excluding §1.7); §1.7 is a multi-crate refactor sized for a dedicated sprint.

**No principle evolution proposed.** All 13 principles in `principles.md` survived this pass intact. Several items strengthen specific principles (Principle 7 single-source-of-truth for the runtime drift; Principle 11 single-pipeline for the backend facade pin) but no principle text needs change.

**No Decision retraction proposed beyond 38/39.** The retracted Decisions (7, 8, 9 partially, 20, 28) remain correctly retracted; no operative Decision needs to be moved to retracted in this pass. Several Decisions get *clarification* (22, 23, 26, 35) — these are body-text refinements, not status changes.

---

## §1. Load-bearing items

These items bind cross-skill coupling that current code cannot satisfy without a definitive Decision. They MUST land before procedural reconciliation, because procedural reconciliation cannot file Decisions on their behalf.

### §1.1 — Runtime bounded-context drift: `io_trace.rs` + `trace.rs`

**Description.** Picture two scenes. First: a programmer types `(trace (helper x))` at the REPL. To make the trace fire, *somebody* has to enumerate `helper`'s call sites, generate or pick a wrapper, and rewrite the project's GOT slot for `helper` so that future calls dispatch through the wrapper. That orchestration is REPL-time work — it happens once, before execution; after the rewrite, runtime is just runtime, dispatching through whatever GOT it has. Today, ~740 LOC of orchestration + wrapper machinery for `(trace ...)` lives in `crates/cranelisp-runtime/src/trace.rs`. Second scene: a developer sets `CRANELISP_IO_TRACE=1` and runs a program. The IO trampoline emits a trace event for every state transition — `Pure` → `Bind` → `PlatformEffect` → continuation pop, etc. — via ~17 inline calls to `record_event` in `io.rs`. Today the recorder (ring buffers, panic hook, formatter, merge-sort dump) is `crates/cranelisp-runtime/src/io_trace.rs` (952 LOC). Read the runtime bounded context: `bounded-contexts.md` §4 says "diagnostics, tracing, observability" are int's concern. ~25% of runtime LOC is dev tooling the BC excludes. Source reading during this scoping pass confirms the BC is right and the implementation is wrong: both modules are dev-only consumer state with a thin trampoline-side surface, both can move to int. `trace.rs` because the orchestration was never runtime semantics in the first place. `io_trace.rs` because it's a clean callback-observer pattern — the trampoline emits events; runtime defines the event taxonomy and a registration API; int implements all observer state. Resolution below: relocate both to `src/`; runtime keeps a tiny extension-point API for IO observation; BC §4 stays as-is.

**Symptom.** `design/runtime/runtime.md` §10 "Proposed FIXME: bounded-context drift" cites the mismatch directly (and originally proposed the BC-revision direction this scoping pass overturns). `int.md` §14 "FIXME — propose: relocate runtime diagnostics modules to int" surfaces it from the consumer side and proposes the relocation. `bounded-contexts.md` §4 "Out of scope: Diagnostics, tracing, observability (int — development concerns)" is the explicit exclusion. Source reading verified during this pass: `io_trace.rs:1-36` module doc says events are "in-process only" — "MUST NOT appear in any cranelisp-shared / cranelisp-types boundary type, .meta.json, CacheEntry, or other on-disk artefact"; the `TRACE_ANCHOR` at `io_trace.rs:58-65` is shared with int's observability module by explicit design ("`/int`'s `observability` module imports this to align its scheduler-trace timestamps with the IO trace"). `io.rs` couples to the recorder via ~17 inline `record_event(Tag, Payload {…})` calls — clean candidates for callback indirection.

**Tension.** Two contradictions that fold together. (1) `bounded-contexts.md` §4 says int owns diagnostics; runtime hosts ~1700 LOC of diagnostics. (2) `runtime.md` §10's framing was "BC wrong vs implementation wrong" with the original recommendation leaning BC-revision. The corrected framing distinguishes **orchestration** (one-time setup performed by int — e.g., the GOT swap that installs trace wrappers) from **runtime semantics** (what the program does once running, dispatching through the post-swap GOT). The runtime crate is for things programs need at runtime: builtins, RC primitives, the IO trampoline, the heap. Diagnostic *orchestration* and diagnostic *consumer state* are int concerns; the runtime side reduces to a small extension-point API (callback registration + event taxonomy) that lets the trampoline emit events to whatever observer int has registered. The BC is not just defensible — it is correct as written.

**Stake.** Load-bearing. Leaving the drift unresolved means: (a) `/dev` next-narrowing to runtime cannot tell from the BC whether `io_trace`/`trace` are extension points or doomed migrants; (b) `/dev` next-narrowing to int cannot tell whether to expect these modules to arrive; (c) `/qa` cannot anchor cross-crate test plans; (d) the runtime crate carries 1700 LOC of code its own BC excludes — every reader resolving the contradiction privately produces a different answer. The original `runtime.md` §10 lean toward BC-revision is itself a sign of the cost: when implementations drift, BCs come under pressure to absorb the drift, and absorbing it would have made the BC less load-bearing.

**Resolution.** Relocate both modules to int; keep a small IO observation extension-point API in runtime; do not revise BC §4.

**Plan, by piece.**

1. **`trace.rs` → `src/trace/` (int).** The orchestration to install trace wrappers (enumerate target functions, generate wrapper code, atomically swap GOT slots, manage the frame stack, marshal trace records) is integration-layer work. It walks the symbol table, calls backend codegen, mutates GOT data structures via existing runtime APIs — all things int already does for normal compile. No new dependency edge: int → runtime is the existing direction; the trace wrapper code, once installed in a GOT slot, is just code addresses in process memory (whether it lives in runtime memory or int memory is irrelevant to the dispatcher). `src/trace/` becomes the home for `(trace ...)` special-form compilation, slash-command handlers, frame stack, ADT marshaling, and the wrapper machinery. No public-API change to the runtime crate.

2. **`io_trace.rs` → `src/io_trace/` (int) via callback contract.** Runtime exposes:

   ```rust
   // crates/cranelisp-runtime/src/io_observer.rs (new, ~50 lines)
   pub enum IoTraceTag { TrampolineEnter, PureStep, PlatformEffect, ContPop, /* … */ }
   pub enum IoTracePayload { /* same variants as today, moved here */ }
   pub type IoObserver = fn(IoTraceTag, &IoTracePayload);
   pub fn register_io_observer(observer: Option<IoObserver>);
   pub fn trace_anchor() -> &'static Instant;  // shared monotonic anchor (kept here)
   ```

   The ~17 inline calls in `io.rs` change from `io_trace::record_event(tag, payload)` to invoking the registered observer (with a relaxed-load null check; no-op if unregistered). All ring-buffer state, thread-local buffers, the env-var filter parser, the panic hook, `flush_to_stderr`, formatter, dump, merge-sort move to `src/io_trace/`. Int's startup (REPL mode or `--run` with `CRANELISP_IO_TRACE=1` set) calls `runtime::register_io_observer(Some(int::io_trace::record))`. `--link` binaries do not register and pay zero cost (one relaxed null-check load per `record_event` call site, optimised to a single conditional branch).

3. **`TRACE_ANCHOR` placement.** Stays in runtime — exposed via `trace_anchor() -> &'static Instant`. Keeping the anchor accessor in runtime preserves the merge-sort coordination story (int's scheduler trace and the IO trace use the same monotonic origin) without forcing a callback round-trip per anchor lookup. `&'static Instant` is a trivial public surface.

4. **BC §4 stays as-is.** "Diagnostics, tracing, observability" remain out of scope for runtime. The new IO observation API is *not* diagnostics — it's an extension point in the same shape as `register_alloc_callback` (host-callback pattern; runtime defines the contract, host implements). The BC's "in scope: heap, RC, drop glue, IO trampoline, fork-join cells" already covers a thin extension-point API by implication; no BC revision needed.

5. **Net runtime LOC reduction: ~1700.** Runtime focus tightens to running-program needs plus host-callback extension points.

6. **New Decision (40).** *"`trace.rs` and `io_trace.rs` relocate to int; runtime keeps an `IoObserver` callback contract and the `(trace ...)` GOT-swap discipline as a normal int orchestration. The runtime crate's BC §4 exclusion of 'diagnostics, tracing, observability' is correct as written; the implementation drift is corrected by relocation, not BC revision. Shape: runtime defines the observation taxonomy and registration API (extension point); int implements all observer state and trace orchestration."* Cites Principles 1 (decoupling — int's diagnostic concerns no longer drag runtime), 2 (narrow — runtime's observation surface is ~50 lines), 3 (dependency direction unchanged — int → runtime stays the only edge), 7 (single source of truth for diagnostic state, in int). Aligned with the existing `register_alloc_callback` host-callback pattern. Sprint 63.

**Consequences.**
- `crates/cranelisp-runtime/src/trace.rs` deleted; `src/trace/` in int absorbs the orchestration + wrapper machinery.
- `crates/cranelisp-runtime/src/io_trace.rs` deleted; `src/io_trace/` in int absorbs ring buffers, panic hook, formatter, dump, merge-sort.
- `crates/cranelisp-runtime/src/io_observer.rs` new (~50 lines): `IoTraceTag`, `IoTracePayload`, `IoObserver` type, `register_io_observer`, `trace_anchor`.
- `crates/cranelisp-runtime/src/io.rs` ~17 inline calls swap from `io_trace::record_event` to invoking the registered observer.
- `crates/cranelisp-runtime/src/lib.rs` (facade) public surface gains the observer API; `facades/runtime.md` documents it as extension-point surface (NOT diagnostics).
- `bounded-contexts.md` §4 unchanged.
- Runtime FIXME 2 closes (BC drift resolved by relocation, not revision).
- Int FIXME 4 closes (relocation actioned).
- `crates/cranelisp-runtime/CLAUDE.md` (when authored — see procedural P1) reflects the slimmer scope.
- `--link` binaries: zero IO-trace overhead (no observer registered).
- REPL/dev `--run`: int's startup registers the observer; user-visible behaviour unchanged.
- `IoTraceTag` and `IoTracePayload` enums move with the API to runtime — they ARE the callback's type contract; they belong where the trampoline lives.
- §2.12 (runtime facade silences on operator + RC primitives) stays applicable: `dec_shallow_io` and operator primitives remain in scope; the scope tightening is just losing the diagnostic modules.

**Owner.** `/arch` files Decision 40 and authors the observer-API public surface (callback type + registration API + tag/payload enums in runtime). `/dev` (runtime) builds the new observer module, updates the trampoline call sites, deletes `trace.rs` and `io_trace.rs`. `/dev` (int) absorbs the relocated code into `src/trace/` and `src/io_trace/`, registers the observer at session start. `/design` (runtime) updates `design/runtime/runtime.md` to reflect the slimmer crate. `/design` (int) authors `design/int/trace.md` and `design/int/io-trace.md` subordinate docs.

**Sequencing.** Independent of §1.6 (the audit pass) — source reading during this scoping pass established the coupling story (~17 clean inline call sites; callback split is feasible without invasive trampoline restructure). Affects §2.12 only in scope-tightening (the diagnostic modules leave; the RC primitives + operator primitives stay). Implementation is a multi-crate move: schedule as a Sprint 64 wave gated by Decision 40 acceptance. Cleaner if landed alongside §2.11 (runtime facade truth-telling on `runtime_panic`) and §2.12 (runtime facade RC + operator primitive surfaces) — single runtime facade revision sweep.

---

### §1.2 — Backend `compile_to_module`: per-symbol JIT, direct shared-state writes, `Result<(), Err>`

**Description.** Backend's `compile_to_module` is currently a half-pulled-back contract. The function compiles, finalises a JIT, returns `(Arc<Jit>, code_ptrs)` — and then int does ~150 lines of post-processing (worker.rs:2860-3018): clone the Arc per defined symbol, look up GOT slots, store function pointers, construct `Code::Jit` wrappers, write into entry — with three "if X disappeared between read and write, error" guards along the way. The split exists because Decision 35 Layer 2 Option B wanted backend "generic-blind" on the symbol table's `C` parameter, so backend couldn't construct `Code::Jit` itself. The cost is real: backend has the data and the symbol-table reference; int duplicates the iteration and bears Decision 37's "no swallowed failures" cascade as bespoke per-step error guards. Two adjacent shape questions also surface: (1) JIT cardinality — Decision 31 says "one `JITModule` per compile batch, `Arc<Jit>` shared across many entries", but per-redefinition reclaim under that model is "all-or-nothing-per-batch" (the Arc only drops when every entry from the batch has been replaced); per-symbol JIT gives true per-redefinition reclaim at the cost of per-symbol JITModule setup; (2) where introspection writes happen — backend already produces `clif_ir`/`disasm`/`compile_duration` per Decision 38 but currently can't write them directly into `shared.introspection` because backend doesn't take a SharedState reference. Resolution below: per-symbol JIT cardinality (one Jit per defn = one batch of one); `Code` enum moves from `src/` to `cranelisp-backend` so backend can construct it directly; backend takes interior-mutable references to symbol tables and an `Option<&introspection>` and writes both directly; signature returns `Result<(), CompilationError>`; int's post-loop disappears.

**Symptom.** `int.md` §14 "FIXME — propose: backend facade should spell out compile_to_module return shape" surfaces the contract gap from the consumer side. `backend.md` §9 "Proposed FIXME 1 — Jit::compile_defn deprecation" is the adjacent question of which entry points are public. Source-reading verification (`worker.rs:2860-3018`) confirms the current shape: `Jit::new_with_symbols` per call (one Jit per `inline_jit_codegen_for_names` invocation, currently shared across many names per Decision 31); backend returns `(Arc<Jit>, code_ptrs)`; int loops over `names` doing GOT writes + `Code::Jit` construction, with three "if disappeared, return ModuleError" cascades carrying explicit Decision-37 references in the comments. The current implementation works but bears the cost of the artificial split — every line in the post-loop is something backend could have done at the call site where it had the data in hand.

**Tension.** Three Decisions intersect:

- **Decision 35 (Layer 2 Option B)** — backend stays C-blind; integration constructs `Code` from raw `(Arc<Jit>, *const u8)`. Selected to keep backend's signatures simple. The cost shows up at the call site as the post-loop and the duplicate per-step error guards.
- **Decision 31 (per-batch JIT)** — one JITModule per `compile_to_module` call, Arc shared across all entries from that batch. Per-redefinition reclaim under this model only fires when every entry from the batch has been replaced.
- **Decision 38 (per-symbol mutability via `&SymbolTable` + `write_code(&self, sym, code)`)** — already authorises the write-direct shape; no new mutability work needed.

The tension is internal to the architecture: Decision 38 grants the write-direct authority that Decision 35 Layer 2 Option B declines to use. Combined with the per-batch JIT cardinality, the result is a contract that's documented in code comments but not in the facade, with reclaim semantics that are correct-but-coarse and a write split that's non-load-bearing.

**Stake.** Load-bearing. Without the pin: (a) any backend refactor that changes the return shape breaks int silently — the facade gives no warning the contract moved; (b) `/qa` cannot write a focused boundary test against the backend↔int handoff; (c) `/review` cannot enforce facade conformance against an unspecified contract; (d) per-redefinition reclaim is coarser than necessary — REPL users redefining one defn at a time keep that batch's JIT alive until every batch-mate is replaced, which can be a long time in a session that compiles modules of 30+ defns; (e) the post-loop in worker.rs is exactly the kind of "consumer-side error cascade duplicating producer-side knowledge" Principle 7 exists to prevent.

**Resolution.** Three coordinated changes, packaged as one Decision (41):

**1. Per-symbol JIT cardinality.** Each `compile_to_module` call for JIT mode receives `&[symbol]` — one symbol per call. Backend creates one `JITModule`, defines one function, finalises, hands back. Object mode is unchanged: `compile_to_module` receives `&[full module's defined symbols]` and produces a `.o` containing all of them. Cardinality is determined by the `names` arity at the caller, NOT by mode at the function signature — Decision 23's "mode is a Module property" remains intact. JIT call sites now look like:

```rust
for sym in defined_symbols(&shared.symbol_tables[scope]) {
    let jit = Jit::new_with_symbols(&extra)?;
    compile_to_module(scope, &[sym], &shared.symbol_tables, shared.introspection.as_ref(), jit.jit_module())?;
}
```

Per-redefinition reclaim becomes truly per-symbol: redefine one defn → its `Code::Jit` clone in the table drops → the Arc<Jit> hits 0 → custom `Drop` calls `unsafe free_memory()` for that one defn's pages, immediately. Cost: per-symbol `JITModule::new` invocations (~50 intrinsic registrations each per `register_intrinsics` in `jit.rs:166`). Cache-hit `Linker` cardinality is unchanged: one Linker holds many symbols (the `.o` is per-module, not per-symbol).

**2. `Code` enum moves from `src/code.rs` to `cranelisp-backend/src/code.rs`.** Backend already owns `Jit` and `Linker`; it's the natural home for the type that wraps both. Decision 35's "Code lives in `src/`" rationale was Principle 3 — `cranelisp-types` cannot import Code because Code references backend types. That rationale stands intact — Code does NOT move to `cranelisp-types`; it moves to `cranelisp-backend`. `SymbolTable<C, L>` stays generic in `cranelisp-types`; backend instantiates `SymbolTable<Code, ()>` for its own signatures; frontend/typecheck stay on `SymbolTable<(), ()>` (no Code import for them either — the C generic continues to serve its purpose). Decision 35 Layer 2 Option B retracts: backend is no longer generic-blind; it knows about and constructs `Code`. The "integration layer is the sole crate that names Code" claim from Decision 35 relaxes — int still names `Code` at the session boundary instantiation, but backend now also names it (in its own crate).

**3. Backend writes directly to symbol tables and introspection; returns `Result<(), CompilationError>`.** Final signature:

```rust
pub fn compile_to_module<M: Module>(
    scope: &ModuleFullPath,
    names: &[Symbol],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<Code, ()>>,
    introspection: Option<&DashMap<FQSymbol, Introspection>>,
    module: M,
) -> Result<(), CompilationError>;
```

Backend writes each compiled symbol's `Code::Jit { jit, ptr }` into its entry via `symbol_tables.get(scope).unwrap().write_code(sym, Code::Jit { jit, ptr })` (Decision 38's `write_code(&self, …)` — interior mutable, no `&mut` flow needed). Backend also stores the GOT slot pointer via `entry's already-existing GOT path. Backend writes `Introspection { clif_ir, disasm, code_size, compile_duration, … }` into the introspection map if and only if `introspection.is_some()` — the `Option`'s `is_some()` IS Decision 38's mode discriminator, reaching backend directly via the parameter. Decision 37's "no swallowed failures" rule lands as a single `?` inside `compile_to_module` (the per-step cascade collapses; backend errors out at the first invariant breach with a typed `CompilationError` variant).

**Decision 41 (new), packaging all three.** *"`compile_to_module` is per-symbol-arity for JIT mode and per-module-arity for object mode (caller controls via `names` length). `Code` enum moves from `src/` to `cranelisp-backend` (Decision 35 Layer 2 Option B retracts; backend gains direct construction of `Code`; Principle 3 protected — `Code` does not enter `cranelisp-types`). Backend writes `Code::Jit` into symbol-table entries directly via Decision-38's `write_code(&self, …)`; writes `Introspection` into `Option<&introspection>` if `Some`; returns `Result<(), CompilationError>`. Per-symbol JIT cardinality enables true per-redefinition reclaim; Decision 31 amends from per-batch to per-symbol cardinality."* Cites Principles 1 (decoupling — int no longer duplicates backend's iteration), 2 (narrow — five parameters, no return tuple to unpack), 7 (single source of truth — backend writes the entry it produced), 11 (single pipeline — same function for JIT and object, mode driven by Module). Sprint 63.

**Consequences.**
- `crates/cranelisp-backend/src/code.rs` new (moved from `src/code.rs`); backend exports `pub enum Code { Jit { jit: Arc<Jit>, ptr: *const u8 }, Linker { linker: Arc<Linker>, ptr: *const u8 } }`.
- `src/code.rs` deleted; int imports `cranelisp_backend::Code` for session-boundary instantiation of `SymbolTable<Code, ()>`.
- `crates/cranelisp-backend/src/lib.rs` `compile_to_module` signature updated per §3 above; old `(Arc<Jit>, code_ptrs)` return removed.
- `src/worker.rs:2860-3018` post-loop deleted (the iterate-over-names + GOT-store + Code::Jit-construct + three error cascades collapse into the per-symbol call-site loop above).
- `Jit::compile_defn` (audit HIGH-1) confirmed deprecated — Decision-41 body adds the paired pin: "`Jit` exposes only `new`/`module`/finalize accessors; per-function compilation is via `compile_to_module` only — there is no public `compile_defn`."
- `facades/backend.md` §"Public surface": `compile_to_module` signature spelled per §3; the `CompilationResult` / return-tuple gone; `Code` enum surface added.
- `facades/int.md` §"SharedState — code carrier construction": post-loop description deleted; `Code` import path updates from `src/code.rs` to `cranelisp_backend::Code`.
- Decision 31 amends: "per-batch JIT" → "per-symbol JIT for `compile_to_module` JIT calls; per-batch retains for object mode (one ObjectModule per `.o`)". Per-redefinition reclaim becomes immediate-per-symbol rather than coalesced-per-batch.
- Decision 35 amends: Layer 2 Option B retracts; `Code` location moves from `src/` to `cranelisp-backend`; "the integration layer is the sole crate that names `Code`" relaxes (int names it at the session boundary; backend names it in its own crate). The Principle 3 protection (no `cranelisp-types → cranelisp-backend` dep) survives intact.
- Decision 32's empty-marker `CodeStore` trait still serves: `()` for non-codegen crates, `Code` for backend + int. The Clone super-bound stays — `Code` derives `Clone` (Arc clones are cheap).
- `tests/v4_jit_reclaim.rs::decision31_scenario2_per_redefinition_jit_pages_reclaimed` re-verified against per-symbol cardinality (the test's "redefine X, observe pages reclaimed" assertion strengthens — the reclaim is now per-symbol-immediate rather than batch-coalesced).
- Backend FIXME 1 closes (Jit::compile_defn deprecation pinned). Int FIXME 5 closes (return shape pinned). Backend FIXME 5 (defined_symbols error variant pin — §2.7) is adjacent: the typed error variant for "name in `names` not in defined_symbols" lands in the same `CompilationError` enum.

**Owner.** `/arch` files Decision 41 and authors the amended Decisions 31 and 35 bodies. `/arch` updates `facades/backend.md` and `facades/int.md`. `/dev` (backend) moves `Code` from `src/` to `cranelisp-backend`, refactors `compile_to_module` to the new signature with per-symbol JIT cardinality, updates the `Jit` public surface (drop `compile_defn`). `/dev` (int) deletes the post-loop in `src/worker.rs`, refactors the JIT call site to the per-symbol loop, updates `src/session_v4.rs` `Code` imports. `/design` (backend) refreshes `design/backend/compile-to-module.md` to reflect the new shape. `/design` (int) refreshes `design/int/symbol-table-generics.md` for the Layer 2 Option B retraction.

**Sequencing.** Independent of §1.1 (different crate). Bundles cleanly with §2.6 (`Linker::get_symbol` defensive contract — same facade revision sweep) and §2.7 (`defined_symbols` error variant pin — same `CompilationError` enum gets both variants in one pass). The per-symbol JIT cardinality change is the most invasive piece — it touches every JIT call site in int (worker.rs and session_v4.rs) — and should land as a single coherent wave. Suggest scheduling as Sprint 64 backend wave gated by Decision 41 acceptance; the `/qa` boundary test (which §2.7 enables) lands alongside as the regression net.

---

### §1.3 — `PlatformError` adopts `ErrorLocation` per Decision 39

**Description.** Today, when a user writes `(platform "stdio")` and the DLL fails to load, the user sees something like:

```
error: load failed: stdio not found in search path
```

No file, no source line, no column — just a free-floating string. Why? Because `manifest_to_descriptors` returns `Result<…, String>` and throws away every coordinate the parser had. Decision 39 (filed two days ago) says all errors crossing into integration carry `ErrorLocation { span, file, fq, line_col, context }`, so the user *should* see:

```
lib/main.cl:42:7: error: platform "stdio" not found in search path [./platforms, /usr/local/lib/cranelisp/platforms]
```

The platform facade already specifies a structured `PlatformError` enum that would carry this — it just hasn't been built. Two days later, the gap is visible. Resolution below: pin `PlatformError` in `cranelisp-types` with `ErrorLocation` carriers per variant; platform refactors `manifest_to_descriptors` and load-paths to construct it; int's existing `Sess::format_error` (also from Decision 39) consumes it.

**Symptom.** `platform.md` §12 "FIXME — adopt structured `PlatformError` and `ErrorLocation` per Decision 39" surfaces the gap. `facades/platform.md` specifies `PlatformError` enum; current `crates/cranelisp-platform/src/lib.rs` does not implement it (returns `String` from `manifest_to_descriptors`). Decision 39 §"Errors carry `ErrorLocation`" is the cross-crate rule that platform does not yet honour.

**Tension.** `facades/platform.md` says the public surface is `PlatformError`. `principles.md` Principle 2 says the facade is target-stating. Decision 39 says errors carry `ErrorLocation`. Three normative claims, one absent implementation. The tension is at the *cross-crate-error contract* — integration's error formatter (per Decision 39) cannot resolve introspection for platform errors because the platform-side doesn't carry the data.

**Stake.** Load-bearing. Without the structured error: (a) malformed DLL load produces a string; the user sees no source location for the offending `(platform "name")` form; (b) Decision 39's mode-conditional source-resolution path (introspection-enabled vs production batch) is unreachable for platform-origin errors; (c) the platform facade is target-stating but cannot be reached from current implementation — the gap is misalignment, not accumulating drift.

**Resolution.** Pin `PlatformError` as a `cranelisp-types`-hosted enum with `ErrorLocation` carriers per variant; platform constructs it; int's `Sess::format_error` consumes it.

```rust
// cranelisp-types/src/error.rs
pub enum PlatformError {
    LoadFailed { dll: PathBuf, cause: String, location: ErrorLocation },
    ManifestNotFound { dll: PathBuf, location: ErrorLocation },
    AbiVersionMismatch { dll: PathBuf, expected: u32, found: u32, location: ErrorLocation },
    DispatchError { fn_name: Symbol, cause: String, location: ErrorLocation },
}

pub enum CranelispError {
    // …existing variants…
    Platform(PlatformError),
}
```

The location field on each variant points back at the offending source (the `(platform "name")` form's span; the file path when known; FQ context per Decision 39). `cranelisp-platform`'s `manifest_to_descriptors` and DLL load paths refactor to construct `PlatformError` rather than `String`. Int's `Sess::format_error` (from Decision 39) gains a `PlatformError` arm that follows the same mode-conditional source-resolution path the other Decision-39 errors already use.

The `cranelisp-types`-as-home choice is non-negotiable per Principle 3 (boundary types live in `cranelisp-types`; cannot live downstream and be wrapped from upstream). The variant set is minimal per Principle 2 — four variants covering the load/manifest/ABI/dispatch failure modes the platform crate actually surfaces today; future failure modes extend the enum (it's `#[non_exhaustive]`). Single source of truth per Principle 7 — one enum, one home, every platform-origin failure flows through it.

**Decision 42 (new).** *"`PlatformError` is a `cranelisp-types`-hosted enum with `ErrorLocation` carriers per variant. Platform-origin failures (DLL load, manifest parse, ABI mismatch, dispatch error) construct it and surface via `CranelispError::Platform(PlatformError)`. Int's `Sess::format_error` consumes it through Decision 39's mode-conditional resolution path."* Cites Principles 2, 3, 7; Decision 39 as binding. Sprint 63.

**Consequences.**
- `cranelisp-types` gains `PlatformError` enum with `ErrorLocation` carriers per variant; marked `#[non_exhaustive]`.
- `CranelispError::Platform(PlatformError)` variant added.
- `crates/cranelisp-platform/` refactors `manifest_to_descriptors` and DLL load paths to construct `PlatformError` rather than `String`.
- `facades/platform.md` `PlatformError` reference moves from "specified, unimplemented" to "spec + implementation aligned".
- `facades/types.md` gains the `PlatformError` enum in §"Errors and warnings".
- `Sess::format_error` (per Decision 39) gains the `PlatformError` arm.
- Platform FIXME 4 closes.

**Owner.** `/arch` files Decision 42, authors `PlatformError` in `cranelisp-types`, updates `facades/platform.md` and `facades/types.md`. `/dev` (platform) refactors the load and dispatch paths to construct the enum. `/dev` (int) extends `Sess::format_error` with the `PlatformError` arm.

**Sequencing.** Independent of §1.1, §1.2. §2.10 was originally bundled here under Decision 42 as a parallel Decision-39 application; per §2.10's revised disposition (runtime panics being driven to zero, no enrichment work), Decision 42 narrows to platform-only. §1.3 stands alone as Decision 42's substance.

---

### §1.4 — Frontend `SymbolTables` alias type tension

**Description.** The frontend facade has a line that looks like this:

```rust
pub type SymbolTables = DashMap<ModuleFullPath, Arc<SymbolTable<Code, ()>>>;
```

The `Code` in there is the integration-layer enum (today at `src/code.rs` per Decision 35; moves to `cranelisp-backend` per §1.2's Decision 41) — it carries either `Arc<cranelisp_backend::jit::Jit>` or `Arc<cranelisp_backend::cache::Linker>`. Trouble: frontend depends only on `cranelisp-types`. Frontend does NOT depend on `src/` — and even after §1.2 lands and `Code` moves to `cranelisp-backend`, frontend still cannot reference it (frontend → backend is not an edge in the DAG, and Principle 3 says it shouldn't be — backend's churn shouldn't force frontend rebuilds). So the facade is referencing a type frontend cannot import — the as-stated form does not compile. The actual code in `cranelisp-frontend/src/lib.rs` works around this by being generic — `expand` takes `&DashMap<ModuleFullPath, Arc<SymbolTable<C, L>>>` for any `C`, `L` — and the integration layer instantiates with `Code` at the call site. The facade text and the implementation disagree, and Principle 3 sides firmly with the implementation. Resolution below: editorial — rewrite the facade with the generic form. The `SymbolTables` alias either drops or moves to `cranelisp-types` as `pub type SymbolTables<C, L> = …`.

**Symptom.** `frontend.md` §10 "Proposed FIXME (target: /arch) — `SymbolTables` alias type constraint" cites the gap. `int.md` §14 "FIXME — propose: `SymbolTables` alias type clarification" cross-references. `facades/frontend.md` lines 18, 42–46 carry the as-stated concrete form; the consumed-surface footnote at line 147 admits the generic form is what's needed.

**Tension.** `facades/frontend.md` pins `SymbolTable<Code, ()>`; `Code` lives where frontend cannot reach (today `src/`, post-§1.2 `cranelisp-backend`); frontend depends only on `cranelisp-types`; the as-stated form is uncompilable. Two normative claims (Principle 3 dep direction; facade target-stating accuracy) collide on one line of facade text. Decision 32's empty-marker `CodeStore` / `LinkerStore` traits are the existing mechanism for exactly this case — they let pre-codegen crates (frontend, typecheck) operate on `SymbolTable<C, L>` generically without naming the concrete `C`. The facade just hasn't been written to reflect that mechanism.

**Stake.** Load-bearing — but mechanically small. The fix is "use the generic form in the facade". Without it: facade text is misleading; `/dev` cannot build against the as-stated shape; `/review` cannot enforce facade conformance because the facade doesn't compile.

**Resolution.** Editorial — rewrite the three affected facades to use the generic form Decision 32 already authorises.

```rust
// facades/frontend.md (§"Public surface")
pub fn expand<C: CodeStore, L: LinkerStore>(
    forms: Vec<Sexp>,
    scope: &ModuleFullPath,
    symbol_tables: &DashMap<ModuleFullPath, Arc<SymbolTable<C, L>>>,
) -> Result<Ast, CranelispError>;

// facades/typecheck.md mirror — same generic form for check_form
pub fn check_form<C: CodeStore, L: LinkerStore>(
    form: &TopLevel,
    scope_table: &SymbolTable<C, L>,
    symbol_tables: &DashMap<ModuleFullPath, Arc<SymbolTable<C, L>>>,
) -> Result<CheckResult, CheckError>;
```

The `SymbolTables` alias either drops (every call site spells the full `&DashMap<…, Arc<SymbolTable<C, L>>>` form), or is moved to `cranelisp-types` in generic form:

```rust
// cranelisp-types/src/module.rs
pub type SymbolTables<C, L> = DashMap<ModuleFullPath, Arc<SymbolTable<C, L>>>;
```

Either choice works; the alias-in-types form is slightly easier on the eye in the facade. `facades/int.md` cites the alias instantiation site: int constructs `SymbolTables<Code, ()>` at the session boundary in `src/session_v4.rs` (where `Code` is now imported from `cranelisp-backend` per §1.2).

No new Decision needed. This is facade alignment within Decision 32's existing frame — the empty-marker traits exist precisely so frontend and typecheck can be generic over `C`/`L` without importing concrete carriers. The "alias from int" text in the current facade is a documentation error from the Sprint-63 lift; correcting it is editorial. Cites Principle 3 (frontend stays stable; cannot reach into backend or int); Principle 6 (generic form has zero runtime cost vs trait-object alternative's per-call vtable dispatch); Principle 7 (one definition per concept — the `SymbolTables<C, L>` alias-in-types is the single home).

**Consequences.**
- `facades/frontend.md` §"Public surface": `expand` signature updated to generic form (`<C: CodeStore, L: LinkerStore>`); the `SymbolTables` alias either drops or references the new types-crate alias.
- `facades/typecheck.md`: `check_form` signature mirror revision (typecheck FIXME 6 — same issue surfaced from typecheck side; facade names `SymbolTable<Code, ()>` literally; should be `<C, L>`).
- `facades/int.md`: alias instantiation site documented — int constructs `SymbolTables<Code, ()>` at `src/session_v4.rs`; the `Code` import is now from `cranelisp-backend` (per §1.2).
- `cranelisp-types/src/module.rs` (optional, recommended): adds `pub type SymbolTables<C, L> = DashMap<ModuleFullPath, Arc<SymbolTable<C, L>>>;` so the facade and call sites can name it cheaply.
- Frontend FIXME 3, int FIXME 6, and typecheck FIXME 6 close together — same fix.
- No new Decision (this is facade alignment within Decision 32 + Decision 41's frame).

**Owner.** `/arch` revises `facades/frontend.md`, `facades/typecheck.md`, `facades/int.md` (and adds the `SymbolTables<C, L>` alias to `cranelisp-types` if that variant is chosen).

**Sequencing.** Independent of §1.1, §1.2 mechanically (the facade revision is editorial regardless of where `Code` lives) — but cleaner to land *after* §1.2 so the int-side instantiation note in `facades/int.md` references the post-Decision-41 `Code` location (`cranelisp-backend`, not `src/`). Small and editorial; can land in the substance wave's first hour, after §1.2's Decision 41 acceptance.

---

### §1.5 — Methodology clarification: audits are point-in-time opinions, not ongoing ground truth

**Description.** This item began life framed as "audit supersession" — the typecheck and int audits dated 2026-04-23 contain target-direction commentary that Decisions 38/39 (2026-04-26+) reframe, and `triad-shared.md` step 7 says "the most recent audit is ground truth for current state". The original framing proposed structured supersession banners on the affected audits to prevent `/dev` agents from following stale guidance. That framing overweighted what audits *are*. An audit is **a single reader's reading of the code at a single moment in time** — its current-state observations are honest snapshots, its target-direction commentary is informed opinion. Neither is "ground truth" in the sense the methodology should treat it. The code is the truth about the code. The master design doc is the truth about design intent. Decisions 38/39 are the truth about the architectural choices that bind. The audit is none of those — it's a useful working document that ages exactly as quickly as the code it describes. `triad-shared.md` step 7's "ground truth" language overstates the audit's authority; this item's original "supersession needs formal banners" recommendation extended that overstatement. The corrected framing: audits are point-in-time opinion documents, useful as one input among several; `/review` is the continuous-audit mechanism that supplies ongoing oversight as changes land. Resolution below: revise step 7 to position audits accurately; do not add formal supersession banners (that work was overweight); position `/review` as the ongoing-audit role.

**Symptom.** `typecheck.md` §11 cites Decisions 38/39 as the "NEW MODEL" superseding the audit's per-form `&mut SymbolTable` direction; `int.md` §11 cites the same. The original §1.5 reading concluded these citations established a need for formal audit annotation. The actual signal: master design docs already do the right thing — they read the audit, take what's useful, and supersede the rest by writing the post-Decision-38/39 model into the master. That IS how audits should work — as input to the master design's authoring, not as ongoing-binding documents in their own right. `triad-shared.md` step 7 phrasing ("the audit takes precedence as ground truth for current state") encourages a reading that overweights audits — `/dev` agents are nudged to treat the audit as authoritative when they should treat the *code* as authoritative.

**Tension.** Three claims sit unevenly: (a) `triad-shared.md` step 7 says the audit is ground truth; (b) the actual role of an audit is "one snapshot's opinion at a date"; (c) `/review` is the methodology's continuous-audit role and is supposed to supplant standalone audit documents over time. (a) and (b) disagree about audit authority. (c) is barely visible in the methodology surface — `/review` exists as a skill but its relationship to standalone audits isn't named.

**Stake.** Smaller than the original framing claimed. The risk isn't that `/dev` will follow stale audit target-direction and ship the wrong code — `/review` (and the master design doc, which `/dev` is also told to read) will catch that. The risk is methodology drift: as long as step 7 says "ground truth", the methodology is internally inconsistent with what audits actually are, and future readers will keep needing to re-resolve the question of what audit weight is appropriate. The fix is small and editorial.

**Resolution.** Revise `triad-shared.md` step 7 to position audits accurately; name `/review` as the continuous-audit mechanism; do not add formal supersession banners to existing audit files.

**Step 7 reword (sketch).**

```
7. **When a recent crate audit `audits/{crate}-*.md` exists**, read it as
   one input among several — the audit captures one reader's view of the
   code at a specific date. Useful for spotting concerns the master
   design doc didn't surface; not authoritative. The **code** is the
   ground truth for current state; the **master design doc**
   (`design/{crate}/{crate}.md`) is the ground truth for design intent.
   Audit conclusions are opinions, useful for triage; cross-check
   against the master design doc and `/review`'s recent findings before
   acting on them. Audit target-direction commentary that pre-dates
   subsequent Decisions or master design doc revisions is superseded
   by those — the audit is not re-authored on supersession; it stays
   as a dated snapshot.
```

**`/review` as continuous-audit role.** `.claude/commands/review.md` (and the methodology that wraps it) names `/review` as the per-PR / per-change-set continuous-audit mechanism. As `/review` matures and runs against every change set, the standalone-audit document's role shrinks further — audits become useful as one-off retrospectives at architectural pivots (e.g., at sprint boundaries when a major Decision lands), not as ongoing-binding documents.

**No formal banners on existing audits.** The original §1.5 recommendation (structured supersession banners) was overweight — it treated audits as authoritative documents needing formal annotation. They aren't. The four 2026-04-23 audits stay as dated snapshots; readers who consult them under the revised step 7 understand them as opinion-from-2026-04-23, not ground truth. The master design docs already cite which audit findings they took or rejected; that's the right disposition.

No new Decision needed. This is methodology wording; cites Principle 7 indirectly (single source of truth — the code is the truth, not the audit).

**Consequences.**
- `sprints/triad-shared.md` step 7 reworded per the sketch above. (`/sprint` owns the file per its header.)
- `.claude/commands/review.md` reviewed for whether the continuous-audit role is clearly named; minor revision if not.
- Existing audit files unchanged — no banners.
- `reconciliation-plan.md` §3 ("Audit reconciliation") softens correspondingly: the "annotate-and-defer" recommendation drops; the "schedule a new full audit pass" recommendation re-evaluates against the lighter audit role.
- §1.6 in this doc is significantly affected — see "Sequencing" below.

**Owner.** `/sprint` for the `triad-shared.md` step 7 revision (file ownership). `/arch` confirms the framing aligns with how Decisions and master design docs are positioned. No `/dev` work.

**Sequencing.** Independent of §1.1–§1.4 (different concern). **Affects §1.6 substantially**: the "missing audits for runtime + platform" item was framed as a substantive gap requiring scheduled audit-authoring work. Under the revised framing, that gap dissipates significantly — the runtime master design doc filled the role by source-reading, which is *actually correct* under the lighter audit framing; platform is small and well-understood and similarly fine. §1.6 should be re-authored or possibly demoted to a procedural-only item. Suggest re-authoring §1.6 in the next iteration of this scoping pass alongside this §1.5 commitment.

---

### §1.6 — Runtime + platform have no standalone audit (resolves under §1.5's reframing)

**Description.** This item began life framed as "missing audits — runtime + platform have never been audited; schedule a Sprint 64 Wave 0 to fill the gap before substance commitments land." That framing depended on §1.5's overweight reading of audits as authoritative ground truth — if audits are *needed* for `/dev` to know what the code does, then absent audits are a load-bearing gap. §1.5 corrects the premise: the code is the ground truth; the master design doc is the design intent; the audit is one reader's opinion at a date, useful but not authoritative; `/review` is the continuous-audit role going forward. Under that reframing, this item dissolves substantially. The runtime and platform master design docs (Sprint 63) already filled the audit-gap-shaped hole by source-reading — exactly what's appropriate when the master design is the authoritative intent statement and there's no need for a parallel "audit's opinion" snapshot. Scheduling a one-off audit pass before substance commitments would be retrofitting an artefact whose role is now smaller. Resolution below: design suffices; `/review`'s first invocation against each crate (when the §1.1 / §1.3 substance work lands) supplies the audit-finding role naturally as part of the change-set review.

**Symptom.** `runtime.md` §10 "Proposed FIXME: runtime audit pass needed" cites LOC distribution (`io.rs` 966, `io_trace.rs` 952, `drop.rs` 864) and frames it as monolith-review territory needing an audit. `platform.md` §12 "FIXME — propose a platform crate audit pass" cites parallel concern. Both FIXMEs were authored under the pre-§1.5 framing where audits felt necessary. Under the corrected framing, the master design docs they accompany are themselves the appropriate response — they read the code, named the structural concerns directly (the runtime master flagged the BC drift; the platform master flagged the `HostContext::dispatch` define-or-retire question and the `PlatformError` ↔ `ErrorLocation` gap), and committed to direction. That IS the audit work, done as part of writing the master.

**Tension.** Original framing said "absent audits force master design to do double duty as both intent and current-state, which the methodology elsewhere keeps separate". §1.5's reframing dissolves the conflict — audits aren't a separate authoritative voice; they're one reader's opinion. The master design doc IS allowed to do its own source-reading; that's how it should work. `/review` provides the continuous oversight that catches drift between intent and reality as it accumulates.

**Stake.** Small. The substance commitments below (§1.1 runtime BC drift, §1.3 PlatformError) were originally claimed to "depend on" runtime/platform audits. They don't. §1.1's resolution flowed from source-reading the trampoline call sites in `io.rs` and the recorder structure in `io_trace.rs` — that source-reading is in this scoping pass and stands on its own. §1.3's resolution flowed from reading the platform crate's load paths and the facade's `PlatformError` spec. Neither needed a standalone audit document. Future substance work in these crates will benefit from `/review`'s continuous-audit role; standalone audit documents are optional retrospectives, not gates.

**Resolution.** Master design docs suffice as the authoritative current-state + intent statement for runtime and platform. `/review`'s first invocation against each crate (which lands as part of the §1.1 and §1.3 substance commitments' implementation waves) supplies the structural-finding role that a standalone audit would have. No standalone audits scheduled.

Concretely:
- **Runtime.** When §1.1's relocation work lands (move `trace.rs` and `io_trace.rs` to int; install the IO observer callback contract), `/review` (narrow runtime) reviews the change set. That review naturally surfaces any structural concerns about the remaining runtime modules (`io.rs`, `drop.rs`, `rc.rs`, allocator, etc.) — including the original "monolith candidates" flagged by the master. If a finding warrants standalone documentation, `/review` files it as a sprint-scope item or a `target: /design` FIXME.
- **Platform.** When §1.3's `PlatformError` work lands, `/review` (narrow platform) reviews the change set. Same shape — structural concerns surface naturally, including the `HostContext::dispatch` retire-or-implement question (§2.13) and the `non_exhaustive` adoption blocked on FIXME 0001.

If a future architectural pivot warrants a fresh full-crate audit (analogous to how the four 2026-04-23 audits were authored in advance of the post-pivot design work), `/sprint` schedules one then. The methodology supports on-demand audits as retrospective opinions; it doesn't mandate them.

No new Decision needed. This is the natural disposition under §1.5's reframing.

**Consequences.**
- Runtime FIXME (runtime.md §10 "audit pass needed") closes — the master design doc is the canonical current-state + intent statement; `/review` is the continuous-oversight role.
- Platform FIXME (platform.md §12 "audit pass") closes — same disposition.
- `reconciliation-plan.md` §3 ("Audit reconciliation") and reconciliation plan Wave 5 ("New audit pass") both soften: the wave goes from "scheduled work to fill gaps" to "optional retrospective when a future pivot warrants it".
- Sprint 64 wave plan simplifies: Wave 0 ("fill audit gaps") deletes; Wave 1 (substance commitments) becomes the actual first wave.
- §1.1 sequencing simplifies: the dependency on §1.6 (originally "Wave 0 audits gate §1.1's BC arbitration") drops entirely. §1.1's resolution stands on its source-reading; no audit needed first.

**Owner.** `/sprint` updates the Sprint 64 wave plan to drop the audit-fill Wave 0. `/arch` confirms via the §1.5 + §1.6 update to `reconciliation-plan.md`. `/design` (runtime) and `/design` (platform) close their respective master-doc FIXMEs when those changes land.

**Sequencing.** Independent. Resolves alongside §1.5's `triad-shared.md` step 7 revision — same methodology beat. Both are editorial methodology updates, not implementation work.

---

### §1.7 — Decision 14 retracts; `cranelisp-runtime` splits into `cranelisp-primitives` + `cranelisp-intrinsics`; trait dispatch lives in typecheck + stdlib only

**Description.** This item began life inside §2.12 ("operator primitives + RC primitives facade silence") as a question about how to enumerate runtime's public surface. Re-examination (worked through interactively across several turns) surfaced that the underlying problem is much deeper: **Decision 14 is broken**, and the broken model has propagated into source. Per Decision 14, "Backend recognizes known primitive impls (e.g., `Num.+$Int` → `iadd`) via a static `(TraitName, Symbol, TypeName) → PrimitiveOp` mapping" — backend special-cases trait knowledge. Source confirms: `cranelisp-backend/src/operators.rs:323-394` literally has `("Num", "+", "Int") => Some("add-i64")`, `("Display", "show", "Int") => Some("int-to-string")`, etc., and `literals.rs:327-332` has a parallel `"+" => Some("cranelisp_op_add")` mapping for operator-as-value. The runtime crate carries duplicate forms — `add-i64` (a primitive substituted to inline CLIF) AND `cranelisp_op_add` (a separately-named extern fn registered for the operator-as-value case). Two names for the same arithmetic operation; backend special-casing trait names; the trait-knowledge collusion table that should never have existed. Resolution below: retract Decision 14; split runtime into two crates honestly reflecting the two categories; backend's substitution table keys on primitive name only (no trait knowledge); trait dispatch lives entirely in typecheck + stdlib.

**Symptom.** Multiple converging signals:

- `runtime.md` §10 "Proposed FIXME: facade silent on the operator primitives" — the framing was wrong (these aren't "operators", they're either primitives or duplicates of primitives).
- `cranelisp-backend/src/operators.rs:323-394` — the `(TraitName, Symbol, TypeName) → PrimitiveOp` collusion table; ~70 lines of trait knowledge baked into backend.
- `cranelisp-backend/src/compiler/literals.rs:327-332` — parallel `"+" => "cranelisp_op_add"` mapping for operator-as-value; another path treating operators as a separate category.
- `cranelisp-runtime/src/primitives/int.rs:60+` — 10 `cranelisp_op_*` extern fns that are duplicate addressable forms of the named primitives (`add-i64`, etc.).
- `cranelisp-runtime` BC §4 — bundles two conceptually distinct categories (language-level callable primitives + backend-emitted-call targets) under one bounded context, accreted from convenience.

**Tension.** Three Decisions plus the BC are out of alignment with the corrected model:

- **Decision 14** asserts backend has trait knowledge. Wrong. Trait dispatch resolves at typecheck/stdlib level; backend sees a call to whatever the impl resolved to.
- **Decision 15** asserts "Ring 0-1 `BuiltinFn` coexists with Ring 2 `TraitMethod`" — true at the typecheck level, but the implication that backend has two paths (one for trait-method, one for BuiltinFn) is wrong. Backend has one path: resolve the call's target name to either an inline-primitive substitution or an emit-call site.
- **BC §4 (Runtime)** bundles language-level primitives + compiler-emitted intrinsics under one crate. Conceptually distinct categories with different evolution drivers (spec-driven vs backend-driven) get one bounded context. Ownership unclear.
- **Source state** has Decision-14-implementation artefacts (`cranelisp_op_*` duplicates, trait-knowledge maps) that under the corrected model shouldn't exist.

**Stake.** Load-bearing. Without resolution: backend continues to bake trait knowledge into codegen (every new trait the language defines requires backend changes — Principle 1 violation; backend's bounded context creeps); duplicate forms (`add-i64` vs `cranelisp_op_add`) age independently and accumulate (Principle 7 violation); runtime crate's BC continues to muddle two categories making `/dev` ownership unclear.

**Resolution.** Five coordinated changes, packaged as **Decision 43** (retracts Decision 14; reframes Decision 15; splits Runtime BC).

**1. Retract Decision 14.** Move to `decisions/retracted/0014-typecheck-emits-traitmethod-backend-maps-to-primitives.md` per `reconciliation-plan.md` §4 once the file-based register lands. Body retains the original text; frontmatter records `status: retracted; superseded_by: 43; rationale: backend trait-knowledge collusion violates Principle 1 (decoupling — adding a new trait's primitive impls required backend changes) and was an interim implementation that survived past its useful life`.

**2. Reframe Decision 15.** Body amends to clarify scope: "two resolution paths in TYPECHECK is correct (Ring 0-1 `BuiltinFn` coexists with Ring 2 `TraitMethod`); but the implication that backend has two paths is wrong. Backend has ONE path: resolve a call's target name; if the name matches an inline primitive (per backend's name-keyed substitution table), substitute CLIF; otherwise emit a call. Trait dispatch is invisible to backend by the time the resolved target is in hand."

**3. Define Decision 43 (the corrected model).**

> *"Two builtin categories. **Primitives** (e.g., `add-i64`, `int-to-string`, `parse-int`): callable from user code via the `primitives/` module path; live in `cranelisp-primitives` crate as `extern "C"` Rust fns; symbol-table entries at `primitives/<name>` with GOT slots; backend MAY substitute CLIF inline at direct call sites via a name-keyed substitution table. **Intrinsics** (e.g., `rc_inc`, `rc_dec`, `dec_shallow_io`, drop glue, allocator, `runtime_panic`, IO trampoline): NOT callable from user code; not in symbol table; not in GOT; live in `cranelisp-intrinsics` crate as `extern "C"` Rust fns; backend emits direct extern calls; resolved via JIT intrinsic registration (REPL/`--run`) or system linker (`--link`). Backend's inline-primitive substitution table is keyed on Symbol (e.g., `add-i64`) only — NO trait-knowledge keys (no `(Trait, method, Type)` triples). Trait dispatch resolves at typecheck/stdlib level; the resolved target (a stdlib defn for the impl) is what backend compiles; the impl body calls primitives by name; backend substitutes from there."*

**4. Split `cranelisp-runtime` into `cranelisp-primitives` + `cranelisp-intrinsics`.** Today's runtime crate retires entirely:

| Today (`cranelisp-runtime/src/`) | Goes to |
|---|---|
| `primitives/{int,float,bool,mod}.rs` (Cat 1: language-level callable) | **`cranelisp-primitives`** |
| `rc.rs` (Cat 2: RC inc/dec) | **`cranelisp-intrinsics`** |
| `drop.rs` (Cat 2: consume_*, drop glue) | **`cranelisp-intrinsics`** |
| Allocator (Cat 2: `cranelisp_alloc` etc.) | **`cranelisp-intrinsics`** |
| `io.rs` (Cat 2: trampoline) | **`cranelisp-intrinsics`** |
| `panic.rs` (Cat 2: `runtime_panic`) | **`cranelisp-intrinsics`** |
| IO observer registration API (per §1.1) | **`cranelisp-intrinsics`** (it's an intrinsic-extension hook) |
| `io_trace.rs` (per §1.1) | `src/io_trace/` (int) |
| `trace.rs` (per §1.1) | `src/trace/` (int) |

**5. BC §4 retires; replaced by §4a (Primitives) + §4b (Intrinsics).**

```
§4a Primitives — `cranelisp-primitives`
  Bounded context: language-level callable surface; spec-defined operations
  user code references via `primitives/<name>`. Symbol-table entries; GOT
  slots; addressable as values. Backend MAY substitute inline at direct
  call sites; otherwise emits normal calls (GOT-indirect). Owned by /dev
  narrow per crate. Spec-driven evolution.

§4b Intrinsics — `cranelisp-intrinsics`
  Bounded context: backend-emitted-call targets; runtime support code.
  NOT callable from user code; not in symbol table; not in GOT. Backend
  emits direct extern calls; ABI tightly coupled to backend's codegen
  choices. Owned by /dev narrow paired with /dev (backend). Backend-
  driven evolution.
```

**Concrete code deletions and refactors:**

- Delete `cranelisp_op_add` … `cranelisp_op_ge` (10 extern fns) from `cranelisp-primitives` (the relocated runtime). `add-i64`, `sub-i64`, etc. ARE the addressable form via their `primitives/<name>` symbol-table entries; the duplicates were Decision-14-implementation artefacts.
- Delete `cranelisp-backend/src/operators.rs:323-394` (`(Trait, method, Type) → primitive-name` map) — backend doesn't know traits.
- Delete `cranelisp-backend/src/compiler/literals.rs:327-332` (`"+" → "cranelisp_op_add"` map) — operator-as-value goes through the symbol-table entry's GOT slot like any other function value.
- Rename `cranelisp-backend/src/operators.rs` → `cranelisp-backend/src/primitives_inline.rs` (or similar) — the surviving substitution table at line 38 (`"add-i64" => iadd`) is name-keyed only; the file's role is "inline primitive substitutions", not "operators".
- Audit stdlib's `(impl Num Int)`, `(impl Display Int)`, `(impl Eq Int)`, `(impl Ord Int)` impls: each impl body should call the primitive directly (`(defn + [a b] (add-i64 a b))`); refactor where the impl was relying on backend's collusion.
- Update `crates/cranelisp-backend/src/jit.rs:130-159` `IntrinsicSymbol` array: remove `cranelisp_op_*` entries; keep `int-to-string` etc. as legitimately-registered intrinsics (they ARE the addressable backing for those primitives' GOT slots, until/unless those primitives also gain inline substitution).

**Deployment story.** A `--link` deployed binary links `cranelisp-primitives` (always — user code might call any primitive) + `cranelisp-intrinsics` (always — backend's emitted code calls into RC/drops/etc.). The compiler host links those two plus `cranelisp-backend` (the compile-time codegen logic with the inline-primitive substitution table) plus `cranelisp-typecheck`, `cranelisp-frontend`, `src/`. Clean physical separation between "what runs" and "what compiles".

**Vocabulary cleanup.** "Operator" is retired as an architectural category — `+` is a Symbol like any other; what mattered was always whether the underlying call site resolves to an inline primitive (substitute) or a normal call (emit). The `IntrinsicSymbol` term in jit.rs already used the right vocabulary; that terminology is now formalised crate-wide.

**Consequences.**
- Decisions 14 retracts; 15 reframes; 43 lands.
- `cranelisp-runtime` crate retires; `cranelisp-primitives` + `cranelisp-intrinsics` crates land.
- BC §4 retires; replaced by §4a + §4b.
- `cranelisp_op_*` duplicates delete from primitives (post-relocation).
- Backend's trait-knowledge maps in `operators.rs` and `literals.rs` delete.
- `operators.rs` renames to `primitives_inline.rs` (or similar); name-keyed substitution table survives.
- Stdlib trait impls audit; refactor where they relied on backend collusion.
- `facades/` gains `primitives.md` + `intrinsics.md`; `runtime.md` retires.
- §1.1's IO observer registration API now resides in `cranelisp-intrinsics`; §1.1 cross-reference updates.
- §2.12 narrows further: under the new structure, intrinsics aren't facade-enumerated in detail (they're internal-to-deployment infrastructure documented in `design/intrinsics/rc-discipline.md` per §P2). §2.12 becomes "intrinsics facade is minimal; the substantive surface lives in `cranelisp-primitives`'s facade".
- Backend's BC §3 unchanged in scope (still "Typed AST → executable code") but its substitution-table responsibility becomes explicit: backend hosts the inline-primitive substitution table, name-keyed only.
- `src/CLAUDE.md` "JIT Symbol Names" section updates: "Runtime infrastructure" row renames to "Intrinsic" (`runtime/alloc` → `intrinsic/alloc` or just `cranelisp_alloc`); user-visible primitives row says "registered into the symbol table at `primitives/<name>`".
- Cargo workspace gets two new crate paths; root `Cargo.toml` updates; `cranelisp-runtime` crate folder deletes.
- All inter-crate dependency edges revise: backend depends on `cranelisp-intrinsics` (declares its emitted symbols against intrinsics) NOT on `cranelisp-runtime`; backend ALSO depends on `cranelisp-primitives` (symbol-table seeding for `primitives/` module entries). Per `src/CLAUDE.md` "Dependencies Between Crates", this is the new shape.

**Owner.** `/arch` files Decision 43; retracts 14; reframes 15. `/arch` authors `facades/primitives.md` + `facades/intrinsics.md`; retires `facades/runtime.md`. `/arch` revises `bounded-contexts.md` §4 → §4a + §4b. `/dev` (the new triad surfaces — primitives + intrinsics) refactor via cargo workspace splits. `/dev` (backend) deletes the trait-knowledge maps; renames `operators.rs`. `/dev` (stdlib) audits trait impls. `/sprint` schedules the multi-crate refactor as a coherent wave.

**Sequencing.** Largest single item in this scoping pass — touches workspace structure, two BCs, three Decisions, multiple crates. Suggest scheduling as a Sprint-65 (or later) wave gated by Decision 43 acceptance — too big to fit alongside the other §1 substance commitments. §1.1 (the IO observer API placement) cross-references the new intrinsics crate but doesn't gate on it (the API can land in `cranelisp-runtime` first under §1.1 and migrate to `cranelisp-intrinsics` when this wave lands). §2.12 narrows immediately on §1.7's acceptance (waits on Decision 43 to land); the §2.12 implementation work bundles into §1.7's wave.

---

## §2. Substantive facade silences and contracts

These items are smaller than §1 — facade clarifications, error-variant pins, contract specifications. Each binds a specific cross-skill coupling but resolution is mechanical once the direction is chosen.

### §2.1 — Frontend public surface: parse + partition + per-form build, no AST union

**Description.** What does `parse(source)` return? The facade today says:

```rust
pub fn parse(source: &str) -> Result<ParseProduct, CranelispError>;
pub struct ParseProduct { pub forms: Vec<Sexp>, pub structural: StructuralDecls }
```

The implementation says `Result<Vec<Sexp>, CranelispError>` plus a separate `extract_module_declarations(&forms) -> StructuralDecls`. The original framing of this item proposed bundling. A deeper reframe (worked through interactively) reaches a different conclusion: **parsing is syntactic** (source → Sexp tree, knows nothing about which forms are special); **structural extraction is semantic recognition** (pattern-matches `(import …)` / `(export …)` / `(mod …)` / `(platform …)` heads, packages them as `StructuralDecls`); **defn AST construction** (`build_ast`) and **expression AST construction** (`build_expr`) are also semantic — different functions for different shapes. The frontend's public surface should reflect this conceptual layering directly, not collapse it into a `ParseProduct` struct or a `TopLevelForm` enum that wraps every shape uniformly. Critically, since `extract_module_declarations` produces `StructuralDecls` containing the parsed structural decl values directly (`ImportSpec`, `ExportSpec`, `ModDecl`, `PlatformSpec`), having a `TopLevelForm::Import(ImportSpec)` variant alongside it would duplicate the parsed information across two homes (Principle 7 violation). Resolution below: parse → partition → per-form build, with extract producing both the structural bundle and the remaining sexps, and `build_ast` / `build_expr` operating on individual partitioned forms.

**Symptom.** `frontend.md` §10 "Proposed FIXME — `ParseProduct` shape vs current `parse` return" surfaces the parse-return question; `frontend.md` §10 "Proposed FIXME — `Ast = TopLevel` alias clarity" surfaces the entry-point-type question (originally §2.2 in this scoping pass; folded in here under (ii) — see §2.2). `facades/frontend.md` carries both the `ParseProduct` struct and the `Ast = TopLevel` alias; the implementation has neither. The substantive question turned out to be neither of those individually but the broader shape of the frontend's public surface.

**Tension.** Facade target-stating accuracy vs the conceptual layering of parsing-vs-recognition-vs-construction; AND the duplication that emerges if a `TopLevelForm` enum wraps the same parsed information `StructuralDecls` already carries. Decision 33's Phase-0 RefMut window doesn't require bundling — it requires *ordering* (extract-before-check). Macro expansion (`expand`) is the existing precedent for "frontend exposes one concept per function".

**Stake.** Small individually; cumulative load-bearing in the sense that the frontend's whole public surface gets pinned in one consistent shape. Without the pin: `/dev` next-narrowing to frontend can't tell whether to fold/split/wrap; `facades/frontend.md` reads as inconsistent with implementation; consumers (int, REPL session) duplicate dispatch logic that should live behind frontend's surface.

**Resolution.** Frontend exposes four functions, no entry-point union type. `extract_module_declarations` *partitions* — returns the structural bundle plus the remaining (defn + bare-expr) sexps. `build_ast` constructs a `Defn`; `build_expr` constructs an `Expr`. No `Ast` alias, no `TopLevel` enum, no `TopLevelForm` enum, no `ParseProduct` struct.

```rust
// facades/frontend.md (§"Public surface")
pub fn parse(source: &str)
    -> Result<Vec<Sexp>, CranelispError>;

pub fn extract_module_declarations(forms: Vec<Sexp>)
    -> Result<(StructuralDecls, Vec<Sexp>), CranelispError>;
    //          ^^^^^^^^^^^^^^^^  ^^^^^^^^^
    //          import/export/    remaining sexps
    //          mod/platform      (defns + REPL bare exprs)

pub fn build_ast(defn_sexp: &Sexp)
    -> Result<Defn, CranelispError>;

pub fn build_expr(sexp: &Sexp)
    -> Result<Expr, CranelispError>;
```

`StructuralDecls` is the single home for parsed structural data:

```rust
pub struct StructuralDecls {
    pub imports: Vec<ImportSpec>,
    pub exports: Vec<ExportSpec>,
    pub mods: Vec<ModDecl>,
    pub platforms: Vec<PlatformSpec>,
}
```

The `Defn` struct is the single home for parsed defn data (carries `Expr` body, params, name, etc.). The `Expr` enum is the recursive expression tree. Neither needs an enum-wrapper at the public surface — callers know whether they're handling a defn or an expression based on which builder they called.

**Caller flows.**

File parse (int's Phase 0):

```rust
let forms = frontend::parse(source)?;
let (structural, defn_sexps) = frontend::extract_module_declarations(forms)?;
{
    let scope_table = symbol_tables.entry(scope).or_default();  // brief RefMut
    write_structural_decls(scope_table, structural);
    seed_defn_order(scope_table, &defn_sexps);
}  // RefMut drops
for sexp in defn_sexps {
    let defn = frontend::build_ast(&sexp)?;
    // attach: entry.ast = Some(defn)
}
```

REPL eval (one input form):

```rust
let forms = frontend::parse(input)?;            // typically one form
let sexp = forms.into_iter().next().ok_or(...)?;
match sexp_head(&sexp) {
    Some("import") | Some("export") | Some("mod") | Some("platform") => {
        let (structural, _) = frontend::extract_module_declarations(vec![sexp])?;
        // apply structural decls to current REPL module
    }
    Some("defn") | Some("defmacro") | Some("deftype") | Some("deftrait") | Some("impl") => {
        let defn = frontend::build_ast(&sexp)?;
        // register defn into REPL module
    }
    _ => {
        let expr = frontend::build_expr(&sexp)?;
        // synth __expr defn, compile, eval, display
    }
}
```

The REPL dispatch is one head-symbol check — exactly the same check `extract_module_declarations` does internally to identify structural forms. The check exists at the caller because REPL is the only context where all three flows are valid; in file context, only structural + defn shapes are legal (bare `(+ 1 2)` at file top level is a parse-context error caught when `build_expr` is reached for a sexp the file shouldn't have produced).

**Single-source-of-truth check.** `StructuralDecls` is the only home for parsed structural info. `Defn` is the only home for parsed defn info. `Expr` is the only home for parsed expression info. There is no enum wrapping these that would duplicate the data through a variant. Principle 7 honoured.

**Conceptual layering this encodes.**

- **Parsing** (`parse`): syntactic. Source → Sexp tree. Knows no special forms.
- **Structural recognition** (`extract_module_declarations`): partitions structural Sexps out, parses them into `StructuralDecls`, returns the rest unchanged.
- **Defn construction** (`build_ast`): per-defn-form Sexp → `Defn` (with body `Expr`).
- **Expression construction** (`build_expr`): Sexp → `Expr`.
- **Macro expansion** (`expand`): semantic transformation, already its own function — the convention is set; this resolution applies the same convention to parsing/extraction/building.

No new Decision needed. This is facade alignment within the existing BC, Decision 25's per-symbol AST placement (`ModuleEntry::Def.ast: Option<Defn>` — where `Defn` is now the literal type, not wrapped in an enum), and Decision 33's structural-decls-via-Phase-0. Cites Principle 1 (decoupling — each function owns one concept), Principle 2 (narrow — no entry-point wrapper struct or enum), Principle 7 (single source of truth — structural data has one home, defn data has another, no enum duplicates).

**Consequences.**
- `facades/frontend.md` §"Public surface": four functions spelled per the signatures above; `ParseProduct`, `Ast`, `TopLevel` removed from the public surface; `StructuralDecls` is the only multi-decl bundle type exposed.
- `crates/cranelisp-frontend/src/lib.rs`: `extract_module_declarations` refactors from `&[Sexp] -> StructuralDecls` to `Vec<Sexp> -> Result<(StructuralDecls, Vec<Sexp>), CranelispError>` (partitioning shape; `Result` because ImportSpec / ExportSpec parsing can fail on malformed input). `build_ast` signature confirms returning `Defn` directly. `build_expr` exposed if not already.
- `cranelisp-types`: `TopLevel` enum (currently with Defn/Expr/Mod/Import/Export variants, aliased as `Ast`) deletes; the variants' payload types (`Defn`, `Expr`, `ModDecl`, `ImportSpec`, `ExportSpec`, `PlatformSpec`) stay as their own types. `Ast = TopLevel` alias deletes.
- `ModuleEntry::Def.ast` field type changes from `Option<Ast>` (effectively `Option<TopLevel>`) to `Option<Defn>` — the only AST that ever lives on a defn entry IS a Defn. Decision 25 cite refreshes accordingly.
- Frontend FIXME 1 (ParseProduct) closes. Frontend FIXME 2 (Ast = TopLevel alias) closes — folded here per §2.2.
- `facades/int.md` Phase-0 description updates to reflect the partition shape: `extract_module_declarations` consumes `Vec<Sexp>`, returns `(StructuralDecls, Vec<Sexp>)`, and the remaining-sexp list feeds the per-form `build_ast` loop.
- REPL session in int gains the head-symbol dispatch (one match expression, ~10 lines).

**Owner.** `/arch` revises `facades/frontend.md` and `facades/int.md`. `/dev` (frontend) refactors `extract_module_declarations` to partition; deletes `TopLevel` enum and `Ast` alias from `cranelisp-types`. `/dev` (int) updates Phase-0 callers to consume the partition tuple; updates REPL session to use head-symbol dispatch; updates `ModuleEntry::Def.ast` consumers to expect `Defn` directly. `/dev` (typecheck) updates anywhere it pattern-matches on `TopLevel` to use `Defn` directly (the typecheck side only ever cares about Defn — the structural variants were never typecheck's concern).

**Sequencing.** Independent of §1.x. Bundles with §2.2 (which collapses to "alias problem dissolves" — see §2.2). Larger than originally framed because of the type deletions and ModuleEntry::Def.ast field-type change, but still mechanical. Suggest landing as a focused frontend wave alongside §1.4's facade-generic-form revision (same triad invocation; same review beat).

---

### §2.2 — `Ast = TopLevel` alias dissolves under §2.1's resolution

**Description.** This item began life framed as "the facade has `pub type Ast = TopLevel` plus discussion of `Expr` separately; readers see three names (Ast, TopLevel, Expr) and don't know which is which; recommendation: drop the alias, use `TopLevel`." A deeper reframe (worked through interactively) reaches a different conclusion: there shouldn't be a `TopLevel` enum either. Under §2.1's resolution, the frontend public surface exposes concrete types directly (`Defn`, `Expr`, `StructuralDecls`) without an enum-wrapper at the entry point. The `Ast` alias problem dissolves because there's no `Ast` to alias and no `TopLevel` to alias TO — both go away. Resolution below: this item is subsumed by §2.1; no separate work.

**Symptom.** `frontend.md` §10 "Proposed FIXME — `Ast = TopLevel` alias clarity" surfaces the gap. Under §2.1's resolution, the gap closes by deleting both names from the public surface, not by picking one. The original framing ("which name wins?") was answering the wrong question.

**Tension.** None remaining post-§2.1. The whole tension was rooted in there *being* an entry-point union type that needed a single name; deleting the union type deletes the tension.

**Stake.** Small (was small under the original framing too). The work is mechanical.

**Resolution.** Subsumed by §2.1. No separate Resolution. The `TopLevel` enum and `Ast` alias both delete from `cranelisp-types`; consumers (typecheck, int) update to use `Defn` directly where they previously matched on `TopLevel::Defn(_)`; `ModuleEntry::Def.ast` field type changes from `Option<Ast>` to `Option<Defn>`. All of this is enumerated in §2.1's Consequences.

**Consequences.**
- See §2.1 — all consequences of the `TopLevel`/`Ast` deletion are listed there.
- Frontend FIXME 2 closes alongside Frontend FIXME 1 in §2.1.

**Owner.** Same as §2.1 — `/arch` (facade), `/dev` (frontend, typecheck, int).

**Sequencing.** Bundled with §2.1.

---

### §2.3 — `MacroEnv` / `compile_single_clause` dead-code cleanup (demoted to procedural §3 P19)

**Description.** This item began life as a substantive item about where macro expansion lives, with a recommendation to add a facade clarification one-liner. On re-examination, the BC + facade are already clear: BC §1 (Frontend) lists "Macro expansion" as in-scope; `facades/frontend.md` exposes `expand(forms, scope, &symbol_tables) -> Result<AST, CranelispError>`; the orchestration boundary is encoded in the function signature itself (`&symbol_tables` injected by int; `Gap::MacroInMem(fq)` returned when JIT work is needed). No facade clarification needed. What remains is purely procedural: confirm whether `MacroEnv` and `compile_single_clause` in `src/expander.rs` are dead post-Decision-8, and delete them if so. That's `/dev` (int) cleanup, no architecture decision needed. **Demoted to §3 P19**; no separate substantive resolution.

---

### §2.4 — `ResolutionGap` stays unified; producer documented in rustdoc

**Description.** `ResolutionGap` is a single enum that two different producers raise — `frontend::expand` AND `typecheck::check_form`. But the `MacroInMem(FQSymbol)` variant is only ever produced by `expand` — typecheck never raises it. So a typecheck consumer pattern-matching on results has to handle a variant that can't happen:

```rust
match check_form(form, &table, &tables) {
    Err(CheckError::Gap(ResolutionGap::SymbolTypechecked(fq))) => wait_then_retry(fq),
    Err(CheckError::Gap(ResolutionGap::MacroInMem(_))) => unreachable!(),  // can't happen
    Err(CheckError::Gap(ResolutionGap::ImportPending(...))) => ...,
    ...
}
```

That `unreachable!()` looks like a refactor hazard at first glance — the day someone *does* extend typecheck to produce `MacroInMem` (or rearranges variants), every consumer with this pattern silently breaks. The natural defensive impulse is to split: `FrontendGap` for what `expand` raises; `TypecheckGap` for what `check_form` raises. But that splits the worker orchestration too — int's worker has to pattern-match on which producer raised the gap before deciding what to do, and the gap-handling loop fragments by source. The unified-shape lever is exactly what lets the worker's gap loop stay one piece of code that handles all gaps the same way structurally, dispatching on the gap *variant* rather than on the gap *producer*. Resolution below: keep unified; document producer per variant in rustdoc.

**Symptom.** `typecheck.md` §11 first FIXME — "`MacroInMem` gap appears in `ResolutionGap` enum but `check_form` cannot raise it."

**Tension.** Type-discipline impulse (split, prevent the `unreachable!()` hazard) vs orchestration uniformity (keep unified, let the worker loop be one piece of code regardless of gap source). Principle 2 (narrow interfaces — adding a boundary type costs every consumer at every change) reinforces the keep-unified side.

**Stake.** Small. The defensive `unreachable!()` is a code-review concern, not a correctness concern; producer-rustdoc closes it as a documentation matter.

**Resolution.** Keep `ResolutionGap` as a unified enum. Add rustdoc per variant naming the producer:

```rust
// cranelisp-types/src/gap.rs
pub enum ResolutionGap {
    /// Raised by `frontend::expand` when a macro call's compiled function
    /// is not yet available in memory. Caller (int's worker) ensures the
    /// macro is JIT-compiled and re-invokes `expand`.
    /// Typecheck NEVER raises this.
    MacroInMem(FQSymbol),

    /// Raised by `typecheck::check_form` when an FQ value reference points
    /// at a symbol whose type is not yet known. Caller waits on the
    /// symbol-table entry's typecheck publication and re-invokes `check_form`.
    /// Frontend NEVER raises this.
    SymbolTypechecked(FQSymbol),

    /// Raised by either `frontend::expand` or `typecheck::check_form` when
    /// an `(import …)` form references a module that isn't yet registered.
    /// Caller registers the import target and re-invokes.
    ImportPending(ModuleFullPath),

    // (other variants…)
}
```

The unified shape lets int's worker orchestration handle all gaps through one loop:

```rust
loop {
    match step() {
        Ok(progress) => break Ok(progress),
        Err(CheckError::Gap(gap)) => match gap {
            ResolutionGap::MacroInMem(fq) => ensure_macro_compiled(fq)?,
            ResolutionGap::SymbolTypechecked(fq) => wait_for_typecheck(fq)?,
            ResolutionGap::ImportPending(m) => register_module(m)?,
            // …
        },
        Err(other) => break Err(other),
    }
}
```

`step()` is whichever frontend or typecheck call the worker is currently driving. The worker doesn't care which producer raised the gap — it dispatches on variant only. Splitting `ResolutionGap` into `FrontendGap` + `TypecheckGap` would force the worker to know which kind of step it's currently driving and pattern-match the right enum, fragmenting the loop without payoff.

The `unreachable!()` defensive hazard is real but small — it's at the boundary where a typecheck consumer chooses to pattern-match exhaustively on every variant. Producer-rustdoc tells the reader "you can match `..` here" rather than `unreachable!()`; if a future variant migrates from frontend-only to also-typecheck, the rustdoc gets updated alongside the producer change.

No new Decision needed. This is a `cranelisp-types` rustdoc revision within the existing facade frame.

**Consequences.**
- `cranelisp-types::ResolutionGap` rustdoc updated per the sketch above; each variant gains a producer line.
- `facades/types.md` §"Errors and warnings" reflects the producer-per-variant convention.
- No facade-signature change in either `frontend.md` or `typecheck.md`.
- Typecheck FIXME 1 closes.
- Int FIXME 7 ("macro-vs-fn discrimination on `MacroInMem` gap") — separate refinement question about whether `MacroInMem` should split into more specific gap variants — stays open as deferred (not part of this resolution; the variant set is fine as-is for now).

**Owner.** `/arch` updates rustdoc on `cranelisp-types::ResolutionGap`.

**Sequencing.** Independent. Editorial.

---

### §2.5 — `CheckError::Gap` partial-state contract dissolves (no problem to solve)

**Description.** This item began life framed as "what's left in the symbol table when `check_form` raises Gap?", with the recommendation to pin a "no observable side effects on Gap" contract. On re-examination (worked through interactively), the threat model was wrong. **Status-gating handles concurrent visibility**: each entry carries a typecheck-progress status; entries mid-Pass-2 are `Pending`; consumers needing the entry's data check status first and wait via `wait_for_inmem` (or its typecheck-side equivalent) until status flips to `Typechecked`. Partial AST resolutions or partial type info on a `Pending` entry are never read. **Retry-from-form handles re-derivation**: each `check_form` invocation takes the form as input and re-walks Pass-2 from scratch; nothing in the retry consumes the first attempt's intermediate state because Pass-2 doesn't have a "where did I leave off" cursor on the entry. The partial state is at most a benign leftover that the successful retry overwrites. Neither facade pin nor implementation refactor is needed; the existing mechanisms already cover the case the original framing thought was uncovered. Typecheck FIXME 2 closes as not-an-issue.

**Symptom.** `typecheck.md` §11 second FIXME — "`CheckError::Gap` swallowing risk" — surfaced the question. The original §2.5 read this as a contract gap requiring a facade pin. Re-read (this iteration): the question was answered by the existing status-gating + retry-from-form discipline before it was asked; the FIXME is asking about a problem that doesn't exist.

**Tension.** None remaining. The original "facade silence on Gap-side-effect contract" framed silence as a gap; on re-examination, silence is appropriate because the contract isn't load-bearing — the runtime mechanisms (status-gating; retry-from-form) handle the cases the contract was meant to cover.

**Stake.** None. The originally-claimed "future refactor would silently corrupt the symbol table" risk depended on the wrong threat model — partial state is gated by status and overwritten by retry; it can't be silently consumed.

**Resolution.** None. §2.5 dissolves as not-an-issue. Typecheck FIXME 2 closes with the resolution note "covered by status-gating + retry-from-form discipline; no contract pin needed". No facade change. No `/dev` work. No procedural §3 entry.

---

### §2.6 — `Linker::get_symbol` returns `Result<*const u8, LinkerError>` over a `LinkerSymbol` newtype

**Description.** Decision 37 ships a safety invariant: when the cache loader can't resolve a symbol, it MUST raise an error, NOT push NULL into the GOT and report success. The reason is concrete — pre-S58, `worker.rs:2810-2823` did exactly the wrong thing. `linker.get_symbol(name)` returned `None`; the worker pushed NULL into the GOT slot; the worker pushed the symbol onto `loaded_symbols` as if it had succeeded; the next caller into that GOT slot SIGSEGV'd on a NULL function pointer. The original §2.6 framing took this as a documentation gap — add a one-line invariant to the facade telling callers "treat `None` as `CacheLoadError`". On re-examination (worked through interactively), that's the wrong fix. The right fix is to encode the contract in the type signature itself. `linker.get_symbol(name)` returning `None` is *always* an error in our usage (we only ever ask for symbols we expect the linker to have, just loaded from a `.o` we just wrote ourselves) — there's no probing case where absence is normal. The `Option` return invites the `unwrap_or(NULL)` regression. The right shape is `Result<*const u8, LinkerError>` — `?` is the natural propagation and the misuse pattern doesn't compile. Additionally, the lookup name should be a typed `LinkerSymbol` newtype rather than `&str` (Principle 7 — boundary identifiers are typed; codifies that linker symbols share one naming discipline whether emitted by JIT or `.o` linker). Resolution below: rename `JitSymbol` → `LinkerSymbol`; signature flips to `Result<…>`.

**Symptom.** `backend.md` §9 Proposed FIXME 2 surfaces the gap. Source-reading verification: pre-S58 `worker.rs:2810-2823` was the silent-NULL regression that motivated Decision 37; current code does check the Option but bears the invariant in caller-side comments rather than in the type. The original §2.6 read this as "facade should document the rule"; the corrected reading is "the rule should be a type-level invariant".

**Tension.** Type-discipline impulse (encode the contract in the signature) vs the pre-S58 lean toward caller-side documentation. Principle 5 (testability is structural — failure modes belong in types where the compiler enforces them, not in prose where future readers might miss them) wins decisively. Adjacent: Principle 7 (single source of truth — boundary identifiers are typed; today's `&str` for linker symbol lookup violates it, and `JitSymbol` (the existing newtype for "JIT linker name (mangled)") is too narrow because per Decision 36 the cache `.o` linker resolves bare-Local user fn names too — the same naming discipline covers both contexts).

**Stake.** Load-bearing for the regression-prevention story. Without the type change: future readers see `Option<*const u8>` and learn the rule by reading Decision 37 (or by re-introducing the regression). With the type change: misuse is a compile error.

**Resolution.** Two coordinated changes:

**1. Rename `JitSymbol` → `LinkerSymbol`.** The existing `JitSymbol` newtype is described as "JIT linker name (mangled)" — too narrow. Per Decision 36, the cache `.o` linker resolves bare-Local user fn names; the JIT resolves both bare and mangled names. Both contexts are the same conceptual thing: "the form a linker resolves against". Rename collapses two overlapping identifier concepts into one, and **codifies the bare-Local-only discipline at the type level** — `LinkerSymbol` carries no provision for cross-`.o`-visible names because Decision 36 says there are none. If a future architecture pivot ever needs cross-`.o`-visible linker symbols (cross-module direct calls, debugger-reachable symbol tables, etc.), that's a major shift that would touch Decisions 23, 31, 36 anyway — collapsing the names now doesn't make that shift harder.

```rust
// cranelisp-types/src/identifiers.rs
string_newtype!(LinkerSymbol);  // replaces JitSymbol everywhere

impl From<&Symbol> for LinkerSymbol { /* bare-Local user fn per Decision 36 */ }
// Mangled forms (`Trait.method$Type`, `name$T1+T2`) construct via dedicated builder fns;
// no From<&str> — every LinkerSymbol value comes from a typed source.
```

`JitSymbol` deletes; every `JitSymbol` use site updates to `LinkerSymbol`. The codebase memory entry under "JIT Symbol Names" in `src/CLAUDE.md` updates to reflect the rename.

**2. `Linker::get_symbol` returns `Result<*const u8, LinkerError>`.**

```rust
// cranelisp-backend/src/cache/linker.rs (and re-export)
impl Linker {
    pub fn get_symbol(&self, name: &LinkerSymbol) -> Result<*const u8, LinkerError>;
}

pub enum LinkerError {
    SymbolNotFound { name: LinkerSymbol, object: PathBuf },
    LoadObjectFailed { path: PathBuf, cause: String },
    // (other variants as needed — folded into CompilationError per §1.2 if that pattern lands)
}
```

Or — folded into the `CompilationError` enum from §1.2's resolution: `CompilationError::LinkerError(LinkerError)`. Either home works; the unified `CompilationError` is tidier given §1.2's direction.

`try_get_symbol(name) -> Option<*const u8>` is NOT introduced today — there's no legitimate probing use case in the codebase. If a debugger or introspection use lands later, add it then with the explicit `try_` prefix that signals "absence is OK here".

**Decision-37 invariant becomes type-enforced.** A caller writing `linker.get_symbol(&sym)?` is correct by construction. A caller writing `linker.get_symbol(&sym).unwrap_or(NULL)` doesn't compile (no `unwrap_or` on `Result<*const u8, _>` with `*const u8` default). The pre-S58 silent-NULL pattern becomes physically impossible.

No new Decision needed. This is facade alignment within Decision 36 (bare-Local discipline) + Decision 37 (no swallowed failures) + §1.2's `CompilationError` direction. The naming consolidation `JitSymbol` → `LinkerSymbol` is itself a small Decision-37-adjacent clarification: codifies that linker symbols are one concept regardless of which linker holds them, and that the bare-Local naming discipline applies uniformly.

**Consequences.**
- `cranelisp-types::JitSymbol` renamed to `LinkerSymbol`; `string_newtype!` macro use updated; `From<&Symbol>` impl added.
- Every `JitSymbol` use site (across `cranelisp-types`, `cranelisp-typecheck`, `cranelisp-backend`, `src/`) updates to `LinkerSymbol`.
- `Linker::get_symbol` signature flips: `(&self, name: &LinkerSymbol) -> Result<*const u8, LinkerError>`.
- `LinkerError` defined in `cranelisp-backend` (or folded into `CompilationError` per §1.2's direction).
- `facades/backend.md` reflects the new signature; the Decision-37 invariant line that the original §2.6 proposed adding is now redundant — the signature IS the invariant.
- `src/worker.rs` cache-hit code path simplifies: every `linker.get_symbol(&sym).expect(...)` or `... { Some(p) => …, None => return Err(...) }` collapses to `linker.get_symbol(&sym)?`.
- `src/CLAUDE.md` "JIT Symbol Names" §: rename `JitSymbol` → `LinkerSymbol` in the table; update the description from "JIT linker name (mangled)" to "form the linker (JIT or cache `.o`) resolves against per Decision 36".
- Backend FIXME 2 closes (the type IS the contract; no facade documentation needed).
- Adjacent §2.7 (`defined_symbols` error variant pin) is the same shape applied to `compile_to_module` — both items are "encode the failure mode in the type signature, not in caller-side documentation". Bundle into one wave.

**Owner.** `/arch` revises `facades/backend.md` and renames `JitSymbol` → `LinkerSymbol` in `cranelisp-types`. `/dev` (typecheck, backend, int) update use sites — mechanical rename, plus signature flip on the `get_symbol` call sites.

**Sequencing.** Bundle with §1.2 (same backend wave; `LinkerError` lives in backend per §1.2's `CompilationError` direction or as its own enum) and §2.7 (same shape applied to `compile_to_module`). Single backend facade revision sweep. The `JitSymbol` → `LinkerSymbol` rename is the largest piece (touches every use site across crates) but is mechanical.

---

### §2.7 — `compile_to_module` errors with typed `SymbolNotCompilable` variant

**Description.** Decision 22 commits backend to a contract: if you ask `compile_to_module` to compile a name, and that name resolves to a symbol-table entry that `defined_symbols()` does NOT include — the entry has no AST, OR it's an `Overloaded` base (parent of mono variants), OR it's a constrained polymorphic fn without specialisation — the call MUST return an error rather than silently fabricating compiled code. Good rule. But the original §2.7 left the *error variant unpinned*. `/qa` wants to write a test:

```rust
#[test]
fn rejects_overloaded_base() {
    let err = compile_to_module(scope, &[overloaded_base], ...).unwrap_err();
    assert!(matches!(err, CompilationError::????));  // what goes here?
}
```

Without a typed variant, the test matches on string substring, which breaks every time the message wording changes. Resolution below: pin `CompilationError::SymbolNotCompilable { module, symbol }` as the variant. Per §2.6's lens, this is the same encode-failure-in-types pattern: don't bear the contract in caller-side documentation; bear it in the type signature. The variant naming is sharper than the original "UndefinedSymbolInBatch" — the symbol is usually *defined* in the table (it's just not in the `defined_symbols()` predicate); "not compilable" describes the actual failure.

**Symptom.** `backend.md` §9 Proposed FIXME 5 surfaces the gap. `/qa` cannot author a stable test for the Decision-22 contract because there's no typed error variant to match on. The original §2.7 named the variant `UndefinedSymbolInBatch`, which misframes the failure ("undefined" suggests the symbol is missing from the table — usually it isn't; the entry exists but doesn't satisfy the predicate).

**Tension.** Facade invariant without a typed contract; Decision 22 has the rule but no error specification. Same shape as §2.6: a runtime contract that should be type-enforced rather than caller-documented.

**Stake.** Medium. Without the pin: `/qa` cannot author the contract test; future refactors of `compile_to_module`'s error reporting silently break consumer expectations; the Decision-22 invariant has no compiler-checked manifestation.

**Resolution.** Pin the typed variant on `CompilationError` (the unified backend error type per §1.2's resolution):

```rust
// cranelisp-backend/src/lib.rs (or wherever CompilationError lives per §1.2)
pub enum CompilationError {
    SymbolNotCompilable {
        module: ModuleFullPath,
        symbol: Symbol,
    },
    LinkerError(LinkerError),    // per §2.6
    // …other variants (codegen failures, ABI mismatches, etc.)…
}
```

Backend's `compile_to_module` (per §1.2's signature `Result<(), CompilationError>`) returns `Err(CompilationError::SymbolNotCompilable { module, symbol })` when the caller passes a symbol in `names` that isn't in `defined_symbols()`. The check happens at the top of `compile_to_module` — fail fast before any codegen work begins.

`/qa` writes the boundary test:

```rust
#[test]
fn rejects_overloaded_base() {
    // Set up a symbol table with an Overloaded base entry (no specialisation).
    let err = compile_to_module(scope, &[overloaded_name], &symbol_tables, None, jit_module)
        .unwrap_err();
    assert!(matches!(err, CompilationError::SymbolNotCompilable { .. }));
}
```

Stable across refactors. The contract is now compiler-checked (the `match` arm exists; if a future refactor renames or restructures the variant, every test using it breaks loudly).

**The three underlying reasons (no AST; Overloaded base; constrained polymorphic without specialization) are intentionally collapsed into one variant.** Carrying a `reason: NotCompilableReason` enum field would be richer but is overkill for a contract-violation error that should never fire in practice (it indicates a caller bug — the caller didn't respect `defined_symbols()`). If a CLI tool or richer diagnostic surface ever needs the breakdown, add the reason field then.

No new Decision needed. This is facade-pinning within Decision 22's frame, applied via §1.2's `CompilationError` enum and §2.6's encode-failure-in-types pattern.

**Consequences.**
- `cranelisp-backend::CompilationError` gains the `SymbolNotCompilable { module: ModuleFullPath, symbol: Symbol }` variant.
- `compile_to_module` (per §1.2's signature) checks `names` against `defined_symbols()` at entry; returns `Err(SymbolNotCompilable { … })` on the first violator.
- `facades/backend.md` documents the variant in the `CompilationError` shape (alongside `LinkerError` from §2.6 and other variants).
- `/qa` files a `target: /qa` FIXME (separate from this Decision) to author the boundary test.
- Backend FIXME 5 closes.

**Owner.** `/arch` adds the variant to `CompilationError` (in `cranelisp-backend` per §1.2's location decision). `/dev` (backend) adds the entry-check in `compile_to_module`. `/qa` writes the boundary test (filed as separate `target: /qa` FIXME).

**Sequencing.** Bundle with §1.2 (single `CompilationError` enum gets the `SymbolNotCompilable` variant alongside the per-symbol JIT cardinality changes) and §2.6 (single `LinkerError` variant; same encode-failure-in-types lens; same backend wave). Single Decision draft can cover all three (§1.2 + §2.6 + §2.7) since they're the same shape applied to three contracts.

---

### §2.8 — Backend GOT-slot population log (deferred — file future-sprint FIXME)

**Description.** After each `compile_to_module` returns, int populates the GOT slot for the compiled symbol with the function pointer that compilation produced. Imagine a future bug: a user redefines a function at the REPL, calls into it, gets back the *old* function's behaviour. Why? Maybe slot 7 of module `foo` ended up pointing at the wrong code. Maybe a Decision-31 reclaim regression freed JIT pages while a slot still pointed at them. Maybe a bad cache-hit wrote a Linker-resolved pointer over a fresh JIT slot. Diagnosing it would benefit from a structured log:

```
[got] module foo slot 7 := 0x7fff_2a3b_4c00 (jit=Arc<Jit>@0x7fff_aa00, batch=42)
```

Today there's nothing of the kind — `Introspection.code_size` records per-defn code size but doesn't link the defn to its slot, its pointer, or its retention root. This is future-proofing, not a current bug. Resolution below: defer to a future sprint; file the FIXME explicitly so it doesn't get lost.

**Symptom.** `backend.md` §9 Proposed FIXME 3.

**Tension.** Observability gap; no Decision binding either way; no current incident motivating prioritisation.

**Stake.** Low-medium. Diagnostic-only; no current bug. But a recurrence of a slot-regression pattern (the kind §2.6's type change closes the rule for, but doesn't add visibility for) would be much faster to triage with this log in place.

**Resolution.** Defer to a future sprint. File a `sprints/fixmes/NNNN-backend-got-slot-population-log.md` FIXME (`target: /arch`) so the item enters the queue with a stable home rather than living in this scoping document. The FIXME body captures the expected shape (extend `Introspection` with optional `got_population: Vec<GotEvent>` per module, gated on `shared.introspection.is_some()` per Decision 38's mode discriminator) so a future sprint can scope from it directly without re-deriving the rationale.

**Filing template** (for the FIXME body):

```markdown
---
number: NNNN
target: /arch
filed_by: /arch (Sprint 63 substance-scoping pass)
filed_at: 2026-05-01
sprint_filed: 63
refers_to: design/arch/substance-scoping.md §2.8, design/backend/backend.md §9 Proposed FIXME 3, design/arch/CLAUDE.md Decision 31, Decision 38
status: open
---

# GOT-slot population log

## Issue
After each `compile_to_module` populates a GOT slot, no structured log
records (module, slot, pointer, retention-root) tuple. Future incident
response on a slot-targeting regression (Decision-31 reclaim error,
cache-hit pointer mis-write) would benefit from this log.

## Proposed resolution
Extend `Introspection` (per Decision 38) with optional `got_population:
Vec<GotEvent>` per module. Populated by backend when
`shared.introspection.is_some()`. Zero overhead in production batch.
…
```

No Decision draft now; Decision lands when the future sprint scopes the work.

**Consequences.**
- New `sprints/fixmes/NNNN-backend-got-slot-population-log.md` filed.
- Backend FIXME 3 stays open, with the canonical home now `sprints/fixmes/` (not the master design doc inline).
- §3 procedural item P17 (which currently points at §2.8) updates to reference the filed FIXME by number once filed.
- No code or facade work in this scoping pass.

**Owner.** `/arch` files the FIXME during the substance-scoping commit. Future sprint: `/arch` files Decision; `/design` (int) elaborates; `/dev` (int + backend) implements.

**Sequencing.** File the FIXME alongside this scoping pass's commit. Implementation deferred to a future sprint when the work fits a wave (likely after the substance commitments §1.1–§1.4, §2.1, §2.4, §2.6, §2.7, §2.11, §2.13 land; §1.6 dropped per §1.5; §2.10 dissolved; §2.14 deferred).

---

### §2.9 — Runtime Effect-node scheduling class: side-channel correlation, deferred

**Description.** When the IO trampoline records an event for a `PlatformEffect` node — say, "this Effect is the network call `http-get`" — it would like to record the call's scheduling class (BlockingIO vs CPUBound vs etc.) so observability can show "this section spent 80% of its time in BlockingIO calls". The class is statically known per platform-fn — Decision 26 places it on `PrimitiveKind::PlatformEffect.scheduling_class` in the symbol table. But the Effect *node at runtime* is `[tag, thunk_ptr, resource_token]` with no back-reference to the platform-fn symbol it came from. So at trampoline runtime we know the *call* (thunk_ptr), but we don't know the *class* — and the recorded event ends up with a placeholder:

```rust
record_effect_event(EffectEvent { scheduling_class: 0, ... });  // at io.rs:178-184
```

Resolution below: side-channel correlation at analysis time (no Effect-node ABI change), deferred to a future sprint with the FIXME filed explicitly.

**Symptom.** `runtime.md` §10 "Proposed FIXME: Effect-node scheduling class plumbing"; backend inline FIXME at `io.rs:174`.

**Tension.** Decision 26 places scheduling class on `PrimitiveKind::PlatformEffect` (symbol-table side); Effect nodes (runtime values) don't carry it. The trampoline knows the call but not the class.

**Stake.** Medium. Observability + future scheduler refinement both benefit from accurate per-class data; today the placeholder zero makes per-class breakdowns impossible.

**Resolution.** Pick **side-channel correlation at analysis time** (option b). Defer implementation to a future sprint; file the FIXME explicitly so it has a stable queue home.

**Why side-channel over in-band.** The in-band alternative (extend Effect node payload by 8 bytes for `SchedulingClass`) would touch every Effect construction site in backend codegen + the runtime trampoline ABI, AND grow the Effect payload from 24 to 32 bytes per node. That cost is borne by every IO program at runtime, regardless of whether tracing is enabled. The side-channel alternative correlates IO trace events against int's scheduler trace at merge-sort time — int's scheduler dispatches platform calls with full FQSymbol context, so its trace knows the platform-fn symbol and (via Decision-26 lookup) the scheduling_class. Merging the two traces produces the joined view without any Effect-node ABI change. Cost lives in int's observability code, paid only when tracing runs (REPL/dev mode); production batch and `--link` binaries pay zero overhead.

The trade-off is real: side-channel correlation is best-effort; if traces drift (one buffer wraps, events lost), the correlation can fail. But the correlation key (timestamp + thread_id + thunk_ptr) is strong, and the failure mode is "missing class data on a few events" — graceful degradation, not silent corruption.

**Filing template** (for the FIXME body):

```markdown
---
number: NNNN
target: /int (correlation logic) + /design (int — observability subordinate)
filed_by: /arch (Sprint 63 substance-scoping pass)
filed_at: 2026-05-01
sprint_filed: 63
refers_to: design/arch/substance-scoping.md §2.9, design/runtime/runtime.md §10, design/arch/CLAUDE.md Decision 26, crates/cranelisp-runtime/src/io.rs:174
status: open
---

# Effect-node scheduling class via side-channel correlation

## Issue
IO trace records `scheduling_class: 0` placeholder because the Effect
node at runtime carries no back-reference to its platform-fn symbol.
Decision 26 places the class on the symbol table; the trampoline
can't see it.

## Proposed resolution
Side-channel correlation at int's scheduler-trace merge-sort time:
int's scheduler trace knows the dispatched platform-fn symbol (with FQ
context); merging the two traces by (timestamp, thread_id, thunk_ptr)
joins each IoTraceEvent::PlatformEffect with its scheduling_class.
Cost lives in int observability; runtime ABI unchanged; production
pays zero.

Update `runtime.md` §10 + `io.rs:174` inline FIXME to reflect that
the in-band option (extend Effect payload) is rejected; side-channel
is the chosen direction. The remaining work is implementation in
int's observability subordinate.
```

The in-band option is explicitly *rejected* by this scoping pass — future-sprint scoping should not re-litigate it. The FIXME records the rejection so the future sprint scopes against the chosen direction.

**Consequences.**
- New `sprints/fixmes/NNNN-effect-scheduling-class-correlation.md` filed.
- Runtime master design doc §10 "Proposed FIXME" eventually updates to reflect the chosen direction (side-channel; in-band rejected). That update lands when the future sprint actions the FIXME.
- Backend inline FIXME at `io.rs:174` similarly updates when actioned.
- No code or facade work in this scoping pass.
- Effect node ABI stays as-is.

**Owner.** `/arch` files the FIXME during the substance-scoping commit. Future sprint: `/design` (int) elaborates the correlation logic in `design/int/observability.md` (as part of the int rebuild wave that picks up subordinate-doc currency per §2.14); `/dev` (int) implements.

**Sequencing.** File the FIXME alongside this scoping pass's commit. Implementation is deferred and naturally bundles with the int rebuild wave that refreshes `design/int/observability.md` (the umbrella under which §2.14's observability formalisation lands); both touch int's observability surface; both gate on `shared.introspection.is_some()` per Decision 38.

---

### §2.10 — `runtime_panic` stays flat-String (panics are degenerate; investment is in eliminating call sites, not enriching them)

**Description.** Today, when a `match` expression doesn't cover all cases and a runtime value falls through, compiled code calls `runtime_panic`. The user sees:

```
runtime panic: match exhaustiveness failure
```

The original framing of this item proposed enriching the panic — pass `Span` as extern arg, update `take_runtime_error` to return structured `ErrorLocation`, bundle under Decision 42 with `PlatformError`. A deeper question (worked through interactively) reframes this: **the architectural direction is to drive UB and runtime panics out of the language, not invest observability into them.** Match exhaustiveness becomes a typechecker-enforced property; the panic site becomes unreachable in well-typed code. Other runtime panic call sites (RC underflow, allocation failure, bounds checks) similarly become preventable-by-construction or migrate to typed errors. Investment in panic-display infrastructure is investment in the wrong direction — work that gets thrown away when the call sites disappear. Resolution below: do nothing. `runtime_panic` keeps its current flat-String sentinel signature; spec §12.7.2 "produce some message" is met as-is. Decision 42 narrows to cover §1.3 (`PlatformError`) only.

**Symptom.** `runtime.md` §10 "Proposed FIXME: runtime_panic carries flat String, not ErrorLocation". The FIXME was authored under the assumption that runtime-panic display would be a permanent surface deserving Decision-39 alignment. Re-read under the "drive out panics" lens: the FIXME points at a feature whose payoff disappears when the call sites disappear.

**Tension.** Decision 39 binds error display to `ErrorLocation` for *errors that are part of normal development* (parse/typecheck/codegen failures; platform-load failures). Runtime panics are a different class — they exist as a degenerate fallback for cases the typechecker doesn't yet rule out, and the trajectory is to shrink that set toward empty. Aligning runtime panics with Decision 39 would treat them as first-class display surfaces; the corrected framing treats them as artefacts being eliminated.

**Stake.** None going forward. The user-visible cost (opaque "match exhaustiveness failure" messages today) is the cost of the typechecker's incomplete coverage, not of `runtime_panic`'s display story. Investing in the display story doesn't reduce the user-visible cost; closing the typechecker gap does.

**Resolution.** Do nothing. Keep `runtime_panic`'s current flat-String sentinel signature. Don't add `Span` propagation. Don't extend `take_runtime_error`'s return shape. Don't extend `Sess::format_error` with a structured runtime-panic arm.

The architectural direction is **driving out UB and panics**:

- **Match exhaustiveness** becomes a compile-time guarantee. The typechecker rejects non-exhaustive `match` expressions; the runtime panic at the fall-through site becomes unreachable in well-typed code. The work is in the typechecker, not the panic site.
- **RC underflow**, **bounds checks**, **allocation failure**, and similar runtime contract violations follow the same trajectory: each becomes either preventable by construction (the type system or the algorithm guarantees no violation) or surfaces as a typed error before any panic can fire.
- The remaining `runtime_panic` call sites — if any survive — are last-resort fallbacks for things genuinely impossible to recover from. Spec §12.7.2 "produce some message" is the right contract for them: bare message, no enrichment, no investment.

Decision 42 narrows to **§1.3 only** — covers `PlatformError` adopting `ErrorLocation`. Platform errors are a real ongoing concern (DLL loading is a normal-development concern; users will hit `(platform "name")` failures regularly) and deserve the structured-error treatment. Runtime panics are not in the same class.

If a future architectural direction reverses (e.g., the language evolves to embrace panics as a first-class user-facing surface), Decision 42 can extend then. Today, the design choice is to invest in elimination, not display.

**Consequences.**
- `cranelisp-runtime/src/panic.rs` unchanged.
- `cranelisp-backend` match-exhaustiveness codegen unchanged.
- `Sess::format_error` runtime-panic arm unchanged (continues showing the bare message).
- `facades/runtime.md` `runtime_panic` signature gets the §2.11 truth-telling fix only (matches actual implementation: `*const u8, usize` args, `()` return, sentinel pattern note) — without §2.10's `Span` extension.
- Runtime FIXME 4 closes with the resolution note "runtime panics are being driven to zero by typechecker enhancements; bare message is sufficient per spec §12.7.2; no Decision-39 alignment for this surface".
- Decision 42 narrows: covers `PlatformError` only (§1.3).
- §2.11's facade revision is no longer co-changing with backend codegen — pure facade truth-telling; smaller wave.
- Adjacent: future typechecker work to enforce match exhaustiveness lands as its own item (not in this scoping pass).

**Owner.** No owner. No work in this pass.

**Sequencing.** No bundling. §1.3's Decision 42 stands as a platform-only Decision. §2.11 stays bundled with §2.12 in the runtime facade revision sweep but no longer needs co-change with backend.

---

### §2.11 — `runtime_panic` facade signature corrected; sentinel pattern named explicitly

**Description.** Two signatures, one function, they don't match. The facade says:

```rust
pub extern "C" fn runtime_panic(msg_ptr: i64) -> !;   // returns never
```

The implementation says:

```rust
pub extern "C" fn runtime_panic(msg_ptr: *const u8, msg_len: usize);   // returns ()
```

The facade promises three things that aren't true: one argument (there are two); an `i64` argument (it's a pointer + length); never returns (it does — stores a sentinel and returns normally). Why does the implementation lie about returning? Because Cranelift cannot unwind through JIT frames — there's no machinery to actually never-return from JIT code. So the runtime stores `Some(msg)` in a thread-local sentinel, returns to the JIT, the JIT returns normally to the host, and the host calls `take_runtime_error()` after every JIT entry to check whether a panic happened. A reader of the facade alone might write code expecting `runtime_panic` to never return — and would be wrong. Resolution below: facade truth-telling — update to match the (current) implementation, add a one-line note about the sentinel pattern. Pure editorial; per §2.10's "drive out panics" disposition, no signature extension for spans or structured location.

**Symptom.** `runtime.md` §10 "Proposed FIXME: facade silent on `runtime_panic` signature".

**Tension.** Facade-vs-implementation lie. The facade is target-stating per `arch.md` §"Facade specs", but the implementation cannot return `!` because Cranelift can't unwind through JIT frames. The `!` was aspirational; reality requires the sentinel pattern.

**Stake.** Small but rule-violating. Misleads any reader who consults the facade alone.

**Resolution.** Update `facades/runtime.md` to match implementation truth; add a one-line note about the sentinel pattern. No signature extension (per §2.10's disposition — runtime panics are degenerate; the work is in eliminating call sites, not enriching them):

```rust
// facades/runtime.md
//
// Sentinel-pattern panic: Cranelift cannot unwind through JIT frames, so
// `runtime_panic` does not actually `!`-return. It stores a message
// sentinel in a thread-local; the host MUST call `take_runtime_error()`
// after every JIT entry to check for a pending panic and surface it as
// the program's exit signal. Per spec §12.7.2 — bare message is the
// contract.
pub extern "C" fn runtime_panic(msg_ptr: *const u8, msg_len: usize);

pub fn take_runtime_error() -> Option<String>;
```

The single-line sentinel-pattern note is the load-bearing addition — it tells a reader who consults the facade alone "this is the protocol; you MUST call `take_runtime_error()` after every JIT entry". Without it, the absence of `!` is silent; with it, the protocol is explicit.

No new Decision needed — pure editorial within the existing facade frame.

**Consequences.**
- `facades/runtime.md` `runtime_panic` block updated per the snippet above (signature matches current implementation; sentinel-pattern doc-comment added).
- Runtime FIXME 5 closes.
- `take_runtime_error()` sentinel pattern becomes facade-visible (was buried in implementation comments).
- No code change — the implementation is already what the corrected facade describes.

**Owner.** `/arch` revises the facade.

**Sequencing.** Bundle with §2.12 — single runtime facade revision sweep. §1.3's `PlatformError` is the parallel platform-side facade revision (different facade file). No co-change with backend codegen (per §2.10's disposition).

---

### §2.12 — Runtime facade silence dissolves under §1.7's crate split

**Description.** This item began life framed as "facade silent on operator primitives + RC primitives", with a recommendation to enumerate operators in the facade and demote `consume_*` helpers to `pub(crate)`. Re-examination (worked through interactively) surfaced that the underlying problem was deeper — Decision 14 was broken; the runtime BC bundled two conceptually distinct categories; "operator primitives" was a misframing. **The substance is now in §1.7** (Decision 14 retraction + `cranelisp-runtime` splits into `cranelisp-primitives` + `cranelisp-intrinsics`). Under §1.7's resolution, the facade-silence question dissolves: there's no monolithic runtime facade to enumerate operators on; instead, `cranelisp-primitives` has a clean facade documenting the language-level callable surface (no `cranelisp_op_*` duplicates — they delete), and `cranelisp-intrinsics` has a minimal facade because intrinsics aren't user-facing surface. Resolution below: subsumed by §1.7; §2.12 becomes a pointer.

**Symptom.** `runtime.md` §10 two FIXMEs — "facade silent on the operator primitives" and "facade silent on `consume_shallow` / `consume_*` exposure" — both surface the runtime facade's enumeration gap. Both close under §1.7's resolution: operators aren't a category (the term retires); `cranelisp-primitives`' facade enumerates the genuine primitive surface; `consume_*` helpers move to `cranelisp-intrinsics` and are documented in `design/intrinsics/rc-discipline.md` (per §P2; intrinsics aren't facade-enumerated in detail because they're internal-to-deployment infrastructure).

**Tension.** None remaining post-§1.7. The original tension ("facade silence on what's public-by-Decision") was rooted in the runtime BC bundling two categories under one facade; §1.7's BC split (§4a Primitives + §4b Intrinsics) gives each category its own clean facade with appropriate scope.

**Stake.** None. The substance moved to §1.7.

**Resolution.** Subsumed by §1.7. No separate Resolution. The facade-silence questions resolve naturally:

- **`cranelisp_op_*` extern fns**: delete entirely (per §1.7) — they were Decision-14-implementation artefacts duplicating `add-i64` etc. The "operator primitives" enumeration question dissolves because the duplicates don't exist.
- **`int_to_string`, `parse_int`, `float_to_string`, `bool_to_string`, `add-i64`, `sub-i64`, …**: enumerated in `cranelisp-primitives`' facade. Clean language-level surface.
- **`dec_shallow_io`**: lives in `cranelisp-intrinsics`. Documented in `design/intrinsics/rc-discipline.md` (per §P2). Not facade-enumerated in detail — intrinsics aren't user-facing.
- **`consume_shallow`, `drop::consume_*` helpers**: live in `cranelisp-intrinsics`. Internal to backend's emitted-call discipline. `pub` within `cranelisp-intrinsics` so backend can declare extern symbols against them; not a user-facing surface.

**Consequences.**
- See §1.7 — all consequences of the runtime crate split + Decision 14 retraction + facade restructure are listed there.
- Runtime FIXMEs 6 + 7 close alongside §1.7's other runtime FIXMEs.

**Owner.** Same as §1.7 — `/arch` (facades + Decision); `/dev` (the new triad surfaces — primitives + intrinsics).

**Sequencing.** Bundled with §1.7. No standalone wave.

---

### §2.13 — Platform `HostContext::dispatch` define-or-retire

**Description.** The platform facade specifies a method:

```rust
impl HostContext {
    pub fn dispatch(&self, platform_fn_id: PlatformFnId, args: &[CLValue])
        -> Result<CLValue, PlatformError>;
}
```

The implementation has never built it. Today's IO trampoline reaches platform fns by following the GOT directly — `ModuleEntry::Def` carries a `platform_fn_ptr` field per Decision 26, and the trampoline reads that. So either (a) `dispatch` is a centralised wrapper that someone is supposed to build (and has been on the to-do list since the facade was authored), or (b) `dispatch` was an early sketch and the trampoline's direct lookup is now canonical. Decision 26's whole point was to put the platform-fn pointer ON the symbol-table entry, not in a parallel registry — adding a `dispatch` wrapper would re-introduce a parallel call path (Principle 7 violation: two ways to invoke a platform fn). Recommendation: retire `dispatch` from the facade; add a note that platform-fn invocation is via direct GOT lookup per Decision 26.

**Symptom.** `platform.md` §12 "FIXME — define `HostContext::dispatch`".

**Tension.** Facade specifies what implementation doesn't provide. Decision 26 made direct lookup the canonical path; `dispatch` was an early sketch.

**Stake.** Small but rule-violating. Facade target-stating implies `dispatch` should land; current model says it shouldn't.

**Resolution.** Retire `HostContext::dispatch` from `facades/platform.md`. Replace with a one-paragraph note in the same section:

> Platform-fn invocation is via direct GOT lookup. The IO trampoline reads `platform_fn_ptr` off the `ModuleEntry::Def` for the resolved `PrimitiveKind::PlatformEffect` entry per Decision 26 and calls through it. There is no centralised wrapper; adding one would re-introduce a parallel call path (Principle 7 violation) without buying anything the per-entry pointer doesn't already provide.

`HostContext` retains its other responsibilities (DLL handle ownership, manifest loading, `HostCallbacks` registration); only the `dispatch` method is removed from the public surface. No new Decision — Decision 26 already binds; this resolution updates the facade to reflect Decision 26's consequences.

**Consequences.** `facades/platform.md` §12 redrafts to remove the `HostContext::dispatch` signature and the FIXME, replacing both with the note above. Platform FIXME 5 closes (subsumed by the redraft). No code change — the implementation never built `dispatch`; the facade catches up to the implementation.

**Owner.** `/arch` (facade revision).

**Sequencing.** Bundle with §1.3 (same platform facade revision).

---

### §2.14 — Int observability strategy formalisation under Decision 38 — DEFERRED (subordinate-doc staleness is systemic)

**Description.** Originally framed as: refresh `design/int/observability.md` to pick up Decision 38's `shared.introspection.is_some()` mode discriminator. On reflection, this is an instance of a systemic issue — every subordinate design doc is stale to some degree against the post-Sprint-63 canonical set (overview, principles, BCs, facades, Decisions 1–43), and each per-crate design rebuild wave will need to refresh its own subordinates as part of that wave's work. Singling int's observability doc out for one-off treatment in this scoping pass would set the wrong precedent (each scoping pass cherry-picks one stale subordinate) and would not address the root: subordinate-doc currency is owned by each `/design` (crate) and lands as part of each crate's design build-out, not as a separate `/arch` workstream.

**Resolution.** Defer. No action this scoping pass. Subordinate-doc currency — including `design/int/observability.md` — is addressed by each per-crate design rebuild wave, not by a one-off refresh. Int FIXME 3 stays open as a marker for the int rebuild wave to pick up; no new FIXME is filed, and no facade or Decision change follows from this item.

**Consequences.** `substance-scoping.md` carries this item as DEFERRED (preserved for traceability — the scoping pass surfaced it; the rebuild waves resolve it). No facade redraft, no Decision, no doc change in this pass. Each per-crate `/design` (crate) rebuild wave is implicitly scoped to refresh its own subordinate docs against the current canonical set as part of the wave's deliverables — this is a methodology expectation, not a per-item commitment recorded here.

**Owner.** `/design` (int) — picks up at the int rebuild wave, alongside other int subordinate docs.

**Sequencing.** Out of this scoping pass. Lands when `/design` (int) runs the int rebuild wave; not gated on §1.1 or any other item here.

---

## §3. Procedural-only items (handled by reconciliation-plan.md)

These items surfaced as FIXMEs in the master design pass but resolve through procedural reconciliation (`reconciliation-plan.md`'s subordinate-doc lifecycle, per-crate archive, FIXME triage). They are listed here so the substance scoping is complete; no per-item analysis required.

| # | Item | Mechanism in `reconciliation-plan.md` |
|---|---|---|
| P1 | Runtime `crates/cranelisp-runtime/CLAUDE.md` missing | §6 — `/dev` (runtime) authors on next narrow-deployment |
| P2 | Runtime RC discipline subordinate doc missing | §6 — `/design` (runtime) authors when next sprint introduces non-trivial RC change |
| P3 | Platform `runtime.md` ↔ `runtime/runtime.md` naming collision | §6 — `/design` (platform) renames to `platform-runtime-interface.md` |
| P4 | Platform `platform-registry-removal.md` archive candidate | §6 — `/design` (platform) moves to `design/platform/archive/` |
| P5 | Platform `non_exhaustive` adoption blocked on FIXME 0001 | §5 — track FIXME 0001 close; merge into 0001's resolution |
| P6 | Int extract `process_form` into its own module | §5 — lift to `sprints/fixmes/`, `target: /dev` (int) |
| P7 | Int narrow `src/lib.rs` to facade-shape exports | §5 — lift to `sprints/fixmes/`, `target: /dev` (int) |
| P8 | Int dependency-registration consolidation | §5 — lift to `sprints/fixmes/`, `target: /dev` (int) |
| P9 | Int subordinate-doc currency sweep + concurrency-family archive | §6 — `/design` (int) executes; concurrency-family collapses to one doc |
| P10 | Backend stale subordinate-doc archival pass (6 docs) | §6 — `/design` (backend) executes |
| P11 | Frontend refresh stale subordinates (4 of 6) | §6 — `/design` (frontend) executes; sequenced after audit recommended split lands |
| P12 | Frontend gap-return testability stub | §5 — lift to `sprints/fixmes/`, `target: /qa` |
| P13 | Typecheck fold `check-form-api` / `dashmap-migration` / `stateless-tc-impl` | §6 — `/design` (typecheck) executes after audit cleanup #1 lands |
| P14 | Typecheck `TypeCheckEnv` generic parameters in facade | Editorial; bundle with §1.4 |
| P15 | Typecheck `Code` as default `C` clarification | Same as §1.4 — facade revision sweep |
| P16 | Typecheck test coverage for gap-return contract | §5 — lift to `sprints/fixmes/`, `target: /qa` |
| P17 | Backend GOT-slot population log (deferred per §2.8) | §5 — file as future-sprint FIXME |
| P18 | Runtime Effect-node scheduling class (deferred per §2.9) | Track via existing `io.rs:174` inline FIXME |
| P19 | Verify and delete sketch-era `MacroEnv` + `compile_single_clause` in `src/expander.rs` (if confirmed dead post-Decision-8) | §5 — lift to `sprints/fixmes/`, `target: /dev` (int); demoted from §2.3 |

---

## §4. Sequencing summary — chains and gates

The substance scoping items form three chains plus a set of independents.

**Chain A — Audit-then-BC.** §1.6 (audit pass scheduling) → audit lands → §1.1 (BC arbitration informed by audit). Audit-first because the BC arbitration's "revise vs relocate" choice depends on the runtime audit's structural-coupling finding for `io_trace`/`trace`.

**Chain B — Decision-39 application sweep.** §1.3 (PlatformError) only; Decision 42 covers it. §2.10 was originally bundled here but dissolved (runtime panics being driven to zero; no enrichment work).

**Chain C — Backend facade pin sweep.** §1.2 (compile_to_module return shape) + §2.6 (Linker.get_symbol defensive contract) + §2.7 (defined_symbols error variant). Single facade revision, single Decision draft if elevated together, single backend wave.

**Chain D — Runtime facade revision sweep.** Post-§1.1, the runtime facade gets one revision for §2.11 (sentinel-pattern truth — `runtime_panic` signature alignment). §2.12 dissolved into §1.7 (the runtime crate splits into `cranelisp-primitives` + `cranelisp-intrinsics`; §2.12's facade-silence questions resolve under the new structure, not via a runtime-facade-as-it-stands revision). §1.7 is a separate, larger wave with its own facade/BC/Decision work — see §1.7's Sequencing.

**Chain E — Platform facade revision sweep.** §1.3 (PlatformError) + §2.13 (HostContext::dispatch retire). Single editorial pass.

**Independents.** §1.4 (SymbolTables alias), §1.5 (methodology clarification — audit role), §2.1 (frontend public surface; absorbs §2.2), §2.4 (MacroInMem rustdoc). §2.14 deferred — subordinate-doc staleness is systemic and addressed by each per-crate `/design` (crate) rebuild wave, not by this scoping pass.

**Wave proposal for substance.**

```
Sprint 64 Wave 1 — Substance commitments (parallel where independent;
                                          §1.6 dropped per §1.5 reframing)
  - /arch — §1.1 BC revision + Decision 40 (relocate trace.rs + io_trace.rs to int)
  - /arch — §1.2/§2.6/§2.7 backend facade pin sweep + Decision 41 (CompilationResult)
  - /arch — §1.3 Decision 42 (PlatformError adopts ErrorLocation; runtime_panic intentionally left flat per §2.10)
  - /arch — §1.4/§2.1 frontend facade alignment sweep (absorbs §2.2)
  - /arch — §1.5 triad-shared.md step 7 reword (audit role)
  - /arch — §2.4 typecheck rustdoc (ResolutionGap producer-per-variant)
  - /arch — §2.11 runtime_panic facade truth-telling
  - /arch — §2.13 platform facade retire dispatch
  Output: substance-wave commitments land; reconciliation plan can proceed
          (excluding §1.7 — see Sprint 65+)
  Note: §2.14 (observability formalisation) deferred — subordinate-doc
        staleness is systemic; addressed by each per-crate /design rebuild wave

Sprint 64 Wave 2+ — Implementation cascade (per-crate /dev waves)
  - /dev (frontend, typecheck, backend, runtime, platform, int) per Decision impacts
  - Dependent on Wave 1 Decisions

Sprint 65+ — §1.7 wave (Decision-14 retraction + crate split)
  - /arch — Decision 43 (corrected primitive/intrinsic model)
  - /arch — retract Decision 14; reframe Decision 15
  - /arch — facades/primitives.md + facades/intrinsics.md authored; facades/runtime.md retires
  - /arch — bounded-contexts.md §4 → §4a + §4b
  - /dev — cargo workspace splits cranelisp-runtime → cranelisp-primitives + cranelisp-intrinsics
  - /dev (backend) — delete trait-knowledge maps; rename operators.rs → primitives_inline.rs
  - /dev (stdlib) — audit Num/Eq/Ord/Display impl bodies
  - §2.12 implementation work bundles here
  Output: corrected primitive/intrinsic architecture lands

(then) reconciliation-plan.md Wave 1 — Decision log migration
```

The substance wave inserts before reconciliation Wave 1. §1.7 is too large for the substance wave and is scheduled separately. Per the brief §1, this is the verdict: substance-first, procedural-second.

**Estimated effort.**
- Wave 1 (substance commitments excluding §1.7): ~10–14 hr `/arch` + ~2 hr `/design` (int) + per-crate `/dev` cascade in Wave 2+.
- Sprint 65+ §1.7 wave: significantly larger — multi-crate refactor, two new crates, BC split, three Decision actions (43 file + 14 retract + 15 reframe), trait-knowledge map deletion, stdlib audit. Sized for a dedicated sprint.

**Decisions filed by this scoping pass (when accepted).**
- **New Decision 40** — `trace.rs` and `io_trace.rs` relocate to int; runtime keeps `IoObserver` callback contract (per §1.1)
- **New Decision 41** — `compile_to_module` per-symbol JIT cardinality + direct shared-state writes + `Result<(), Err>` return (per §1.2; amends Decisions 31 + 35)
- **New Decision 42** — `PlatformError` adopts `ErrorLocation` per Decision 39 (per §1.3). Runtime panics intentionally not aligned (per §2.10 — being driven to zero, not enriched).
- **New Decision 43** — Two builtin categories (primitives + intrinsics); `cranelisp-runtime` splits into `cranelisp-primitives` + `cranelisp-intrinsics`; backend's substitution table is name-keyed (no trait knowledge); trait dispatch lives in typecheck + stdlib (per §1.7; retracts Decision 14; reframes Decision 15).

Four new Decisions plus one retraction (14) plus one reframe (15). The §1.7 work is the largest single architectural shift in this scoping pass.

---

## Cross-references

- `design/arch/substance-scoping-brief.md` — the spec this executes
- `design/arch/reconciliation-plan.md` — the procedural plan this informs (substance wave inserts before its Wave 1)
- `design/arch/CLAUDE.md` — Decisions 1–39 (referenced throughout)
- `design/arch/principles.md` — principles (cited by number throughout)
- `design/arch/bounded-contexts.md` — §4 affected by §1.1
- `design/arch/facades/{frontend,typecheck,backend,runtime,platform,int}.md` — affected by §1.2, §1.3, §1.4, §2.6, §2.7, §2.11, §2.12, §2.13
- `design/{frontend,typecheck,backend,runtime,platform,int}/{crate}.md` — six master design docs (primary FIXME source for this scoping)
- `audits/{frontend,typecheck,backend,src}-20260423.md` — four existing audits (§1.5 affects)
- `sprints/fixmes/0001..0009-*.md` — already-filed (some §3 procedural items merge into 0001)

— end of substance scoping —
