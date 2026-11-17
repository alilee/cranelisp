# S123 public-API approval packet

**Owner:** `arch`. **Reader:** the user, at the inter-crate public-API gate
(root `AGENTS.md` §Roles). **Status:** rows P1–P10 are approved
([user rulings on the Phase 3 decisions, 2026-11-15](archive/sprint-123.md#user-rulings-on-the-phase-3-decisions-2026-11-15)),
and rows P11–P13 are approved
([user rulings at the Phase 3 → 4 checkpoint, 2026-11-15](archive/sprint-123.md#user-rulings-at-the-phase-3--4-checkpoint-2026-11-15)).
Row P14 is approved (user, 2026-11-16). Rows P15 and P16 are approved (user, 2026-11-16)
(§A6). R10-9 is not yet a listed delta (Part C).
A mismatch between an approved row
and the generated diff returns here. **Checkpoint:** planning commit
`b35bfb87`, 2026-11-15. Line counts are read from the committed
`public-api.txt` files at that commit.

Part A is what S123 implements. Part B is scheduled outside the Phase 5
functional change-sets. The withdrawn option-A row (`runtime/panic_pending`) of
the [architecture review](s123-architecture-review.md) §5 is not proposed.

Each row gives the exact items, their producer and consumers, compatibility,
cache-schema and ABI impact, and the expected `public-api.txt` effect. "Lines"
counts every baseline line naming the item, including the generated
auto-trait rows the current format prints.

## Gate status

| Rows | Status |
|---|---|
| P1–P9 | Approved 2026-11-15. P6 as proposed: `runtime/panic` stays and never returns. P3, P4 and P9 because platform dispatch faults end the process |
| P10 | Approved 2026-11-15 with U′; it lands only in U′'s change-set |
| P11–P13 | Approved 2026-11-15 (§A5). P13 lands at S123 close if the superseded redefinition residue is deleted in Phase 5, otherwise in S124 |
| P14 | Approved 2026-11-16 as proposed (§A6): `AgentState` and `build_agent_state_with` crate-private, `build_agent_state` off the public surface |
| P15, P16 | Approved 2026-11-16 as proposed (§A6) |
| B1 | Scheduled for S124 |
| B2, B3 | Scheduled for S123 close, with the baseline regeneration |

## Part A — deltas S123 needs

### A1. `cranelisp-intrinsics`: panics end the process

Governing contract: [process-ending panics](../design/arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics) (§4b invariant 13)
§1. Interior: `design/intrinsics/process-lifecycle.md` §1 and §3.

| Row | Exact delta | Consumers | Compatibility, schema, ABI | `public-api.txt` |
|---|---|---|---|---|
| P1 | Remove `#[export_name = "catch-runtime-error"] pub extern "C" fn panic::catch_runtime_error(i64) -> i64`, its catalog row and its `primitives` bootstrap registration | Root: `src/bootstrap.rs` registration and roster pin, `src/exe.rs`, `src/worker.rs`, `src/repl/format.rs`. Language: `stdlib/fn/result.cl`, `stdlib/testing/runner.cl`, `exemplar/main.cl`, `examples/32-concurrency-combinators.cl`, `user/guide/testing.md`, test fixtures | Removes a language primitive (user ruling). No serde shape change; `BUILD_ID` invalidates cached objects that import it. Emitted-call ABI: one import fewer | intrinsics −1 |
| P2 | Remove `pub fn panic::take_runtime_error() -> Option<String>` and `pub fn panic::set_runtime_error(String)` | Root production: `src/expander.rs`, `src/pipeline.rs`, `src/session_v4/lifecycle.rs`, `src/session_v4/test_runner/run.rs`. Tests only: backend `lib.rs`, `test_support.rs`; root `pipeline.rs` and runner tests. Removes the consumer edge root → these two items | Breaking for those callers, which lose their purpose. No schema or ABI effect | intrinsics −2 |
| P3 | Remove `pub struct panic::DispatchFault` (fields `fn_name`, `cause`), `pub fn panic::set_dispatch_fault(DispatchFault)` and `pub fn panic::take_dispatch_fault() -> Option<DispatchFault>` | Root: `src/pipeline.rs`, `src/session_v4/lifecycle.rs` | Breaking for those callers. No schema or ABI effect | intrinsics −12 |
| P4 | Remove `#[repr(C)] pub struct panic::ProgramOutcome` (fields `exit_code`, `error_kind`) and `#[export_name = "cranelisp_check_runtime_error"] pub extern "C" fn panic::cranelisp_check_runtime_error()`. Depends on P3 | Root: `src/pipeline.rs`, `src/session_v4/lifecycle.rs`; the generated startup stub (`src/exe.rs`), which stops calling the drain | Runtime/stub ABI only: both ship in one build, so no platform `ABI_VERSION` change | intrinsics −11 (10 for the struct, 1 for the export) |
| P5 | Change `pub extern "C" fn panic::cranelisp_run_program(*const u8, bool) -> ProgramOutcome` to `-> i64`, the program's reduced result word. Depends on P4 | Root: `src/pipeline.rs`, `src/session_v4/lifecycle.rs`, the startup stub (one return register instead of a two-word struct) | Same as P4 | intrinsics: 1 line changed |
| P6 | Change `#[export_name = "runtime/panic"] pub extern "C" fn panic::runtime_panic(*const u8, usize)` to `-> !` (never returns) | `cranelisp-primitives` Rust raisers (`ring0.rs`, `marshal.rs`): behaviour unchanged, their sentinel returns become unreachable. Backend: imports by name through the catalog. `platforms/poll-pool` resolves the symbol at load: its survival fixture becomes a process-exit fixture | C ABI unchanged (same parameters, no result). Semantic change: no caller resumes. `runtime/panic` is not part of the declared platform host vtable, so no `ABI_VERSION` change | intrinsics: 1 line changed |
| P7 | Catalog data: the `runtime/panic` row declares `has_return: false`, derived from the function type by ACT-1033's crate-private derivation | Backend import declaration (`jit.rs` via `intrinsics_table()`) | Corrects a wrong row; `IntrinsicEntry`'s public fields are unchanged | intrinsics +0 |

The binary deletes its consumers of P1–P5 and P9 in the same change-sets: the
REPL's trap arm and `runtime error:` display, `trampoline`'s slot read, the
expander's slot read, the runner's per-test bracket, `compose_dispatch_error`,
and the stub's error block and drain call (`design/int/int.md` §16.0, S123
bullet, delta 3). That is consumer removal under approved rows, not a new
delta.

### A2. `cranelisp-intrinsics`: baked runtime switches

Governing contract: [environment supply](../design/arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics) (§4b invariant 18)
§2.2. Interior: `design/intrinsics/process-lifecycle.md` §2.

| Row | Exact delta | Consumers | Compatibility, schema, ABI | `public-api.txt` |
|---|---|---|---|---|
| P8 | Add `pub mod runtime_switches` with `pub fn runtime_switches::capture_runtime_switches() -> Vec<u8>` (an opaque, versioned capture of the current switch values) and `#[export_name = "cranelisp_install_runtime_switches"] pub extern "C" fn runtime_switches::cranelisp_install_runtime_switches(*const u8, usize)` (installs a capture as the runtime's only switch source; ends the process with a located fault if a switch was already read or the capture is malformed) | Root: `src/exe.rs` calls the capture at `--link` and embeds the bytes in the startup object; the stub imports the install entry as its first call. New consumer edge: root → `runtime_switches`. `cranelisp-exe-bundle` adds `pub use cranelisp_intrinsics::runtime_switches;` to force-link the export (source change in a crate with no baseline). `design`(int) consumes it as stated and names no switch (`design/int/int.md` §16.0, delta 1) | Additive. No crate edge is new: root and exe-bundle already depend on intrinsics. The capture format is private to intrinsics, carries a format byte, and never reaches a cache: the startup object is per link. No `CACHE_SCHEMA_VERSION` change | intrinsics +3 (module, function, export) |

### A3. `cranelisp-types`

| Row | Exact delta | Consumers | Compatibility, schema, ABI | `public-api.txt` |
|---|---|---|---|---|
| P9 | Remove the variant `PlatformError::DispatchError { fn_name, cause, location }`. With P3 it has no producer | Root: `src/pipeline.rs` (producer and tests) | `PlatformError` is `#[non_exhaustive]` and not serialized; no schema effect | types −4 |
| P10 | No signature change. Semantic contract of `cranelisp_types::ownership_analysis_off` widens from "analysis off" to "moves off", the uniform reference of U′'s rule U1 (`design/backend/uniform-counting.md` §7). Rustdoc changes only | Backend emission; the cache manifest's ownership key is unchanged | The baseline cannot show it, so it is listed for approval here | types +0 |

Under U′ the backend stops reading borrow modes from `ModeSummary`, and those
typecheck outputs lose their emission consumer. Retiring or narrowing them is
a later packet; nothing is proposed for S123.

### A4. Confirmed without a delta

| Surface | Expected effect | Evidence owed |
|---|---|---|
| Backend: uniform counting (U′), the terminating `runtime/panic` call | +0 (`design/backend/uniform-counting.md` §7) | Unchanged baseline, recorded at the Phase 5 checkpoint |
| Frontend, typecheck, platform | +0 | Unchanged baselines |
| Primitives: the `checked-quot` primitive (`spec/12-runtime.md` §12.7.3) | +0. A primitive is a declaration row in `PRIMITIVES_TABLE` and a `pub(crate)` body, as `parse-int` is; no public item changes. A design that needs a public item returns here | Unchanged baseline |
| Macro-expansion panics end the process (user ruling) | +0: no containment entry is added | — |
| The REPL panic report: `error: runtime panic:`, plain on stderr (user ruling) | +0: no host formatter registration | — |
| Agent in the default build | The feature change itself changes no item, signature or edge; it only selects the configuration that compiles `cranelisp::agent` (review §1.1). The `AgentState` change W3 made inside that module is row P14 | — |
| Environment-file supply | A binary-private module (`design/int/environment.md` §1) | — |
| ACT-1033's catalog derivation | Crate-private | `IntrinsicEntry` unchanged |
| Any other root-crate item | No change beyond P12, P14 and P16 (`design/int/int.md` §16.0, delta 6). The activation module is `pub(crate)` | Root `src/` diff against `3bdf398e`: no other `pub` item added, removed or re-signed |

### A5. New deltas from `design`(int) — approved 2026-11-15

Source: `design/int/int.md` §16.0, S123 bullet, deltas 2, 4 and 5. The user
approved the rows with `arch`'s names, which follow `design`(int)'s stated
shape; a different name or parameter list returns to this gate.

| Row | Exact delta | Consumers | Compatibility, schema, ABI | `public-api.txt` |
|---|---|---|---|---|
| P11 | In `cranelisp-intrinsics`, add `pub const panic::PANIC_REPORT_PREFIX: &str = "error: runtime panic: "` and `pub const panic::PANIC_EXIT_STATUS: i32 = 1`. The terminator uses both, so they are the only copies. Rustdoc states the promise: every language-panic report is one stderr line that begins with the prefix, and the process then exits with the status; the status is shared with other failures, so a consumer must not classify by status alone | Root: the test supervisor in `src/session_v4/test_runner/` ([test runner §6.5](../design/int/test-runner.md#65-the-test-child)). New consumer edge root → these two items | Additive. No crate edge is new. No schema or ABI effect: the values are the spec's (`spec/12-runtime.md` §12.7.5) and today's batch status. It single-sources a spec-fixed value between its producer and its one consumer (Principle 07) with a two-item facade (Principle 02). Declining it leaves a private copy in int, guarded only by the end-to-end panic cell | intrinsics +2 |
| P12 | Root crate (no baseline). Change `pub fn CompilerSession::run_tests(&self) -> Result<TestRunReport, CranelispError>` to `pub fn CompilerSession::run_tests(&self, records: &std::path::Path, modules: Option<&[cranelisp_types::ModuleFullPath]>, resume_after: Option<&cranelisp_types::FQSymbol>) -> Result<(), CranelispError>`: the child's engine, which runs the selected tests in this process, appends one record per test to `records`, and runs only tests after `resume_after`. `modules` is the REPL's selection; `None` walks the entry chain as `--test` does today. `Err` keeps its meaning: the run could not start. Add `pub fn session_v4::supervise_tests(child_args: &[std::ffi::OsString], modules: Option<&[cranelisp_types::ModuleFullPath]>) -> Result<TestRunReport, CranelispError>`, re-exported beside `TestRunReport`: it needs no session, starts and restarts the child with the compile-affecting `child_args`, and returns the unchanged `TestRunReport` | `src/main.rs` (the binary target): `--test` calls `supervise_tests`, and the child mode calls `run_tests`. The REPL's `handle_run_tests` calls `supervise_tests`. No integration test calls either; `tests/` drive the binary | Breaking for `run_tests`' one caller, `main.rs`. No schema or ABI effect. The child's arguments are a CLI surface that `spec` states (`design/int/test-runner.md` §6.5); the record format is private to the runner | Root has no baseline. The gate applies to the item change and the bin → lib consumer edges |
| P13 | Remove the broken-symbol state. In `cranelisp-types`: the variant `Life::Broken { slot: CallableSlot, error: BrokenProvenance }`, `#[non_exhaustive] pub struct BrokenProvenance` (fields `broken_by`, `message`; `BrokenProvenance::new`), `#[non_exhaustive] pub struct BrokenTransition<C: CodeStore>` (fields `displaced_owner`, `slot`) and `pub fn SymbolTable::mark_broken(&mut self, &Symbol, BrokenProvenance) -> Result<BrokenTransition<C>, LifecycleError>`. In `cranelisp-backend`: `pub fn compile_trap_stub(*const u8, usize) -> Result<(*const u8, Code), CompilationError>`. Depends on the deletion of the superseded redefinition residue ([session transaction §5.2](../design/int/session-transaction.md#52-no-symbol-is-left-broken)), which removes every production caller | After that deletion: crate-private match arms only, in types (`lifecycle.rs`, `module.rs`), typecheck (`adt.rs`), backend (`lib.rs`, the `compiler/entry_convention.rs` `Broken` arm) and root (`src/worker.rs`), plus tests (types `module/tests.rs` and `crates/cranelisp-types/tests/lifecycle_facade.rs`, backend `entry_convention/tests.rs` and `lib.rs`, root `info_source_tests.rs`). The backend's `compile_trap_stub` tests also read P2's slot, so they are reworked or deleted in S123 regardless | Breaking only for exhaustive matches on `Life`, which are inside the workspace. **No `CACHE_SCHEMA_VERSION` bump.** `Life` is persisted as `serde_json`, which tags variants by name, so the remaining variants encode identically. No sidecar holds `Broken`: a module with a broken entry is never written ([session transaction §8.3](../design/int/session-transaction.md#83-broken-modules-are-not-persisted)). A sidecar that did would fail to decode, and the cache loader maps a decode failure to `CacheStale::Deserialise`, a fresh build, not an error. Falsifier: a cache hit that panics or errors on decode rather than missing. No ABI effect. With P13 the state is unrepresentable in the types crate (Principle 20) | types −26 (`Life::Broken` 3; `BrokenProvenance` 12; `BrokenTransition` 10; `mark_broken` 1). Backend −1. Typecheck +0 |

**Scheduling P13 (approved).** P13 lands with the B3 batch at S123 close,
under the same baseline regeneration, if the residue deletion lands in Phase 5;
otherwise it lands with B1 in S124. Until P13 lands, the one remaining hole is a new
call to the public `SymbolTable::mark_broken`.

### A6. Phase 5 deltas from W3 and W4

#### P14. Root crate: `AgentState` leaves the public surface — approved 2026-11-16

Source: W3's `design`(int) ruling that activation and the model handle are one
fact (`design/int/agent.md` §3.4), realised by `dev`(src) as
`AgentState.link: AgentLink`; `src/` review finding R3.

**The gate applies.** The root library's consumers are separate crates: the
binary target `src/main.rs`, each `tests/*.rs` integration test and each
`benches/*.rs` bench. No workspace member depends on `cranelisp`. Its `pub`
surface is therefore an inter-crate API without a baseline
([bounded contexts](../design/arch/bounded-contexts.md) §6, "What crosses the boundary").
The gate covers removed fields and changed visibility whether or not a consumer
exists, as it does for P12 and B3. W3 has already removed two public fields,
and narrowing further cannot restore them, so some row needs the user.

**Census, `src/` against `3bdf398e`.** In `src/` outside `main.rs`, the only
`pub` items added, removed or re-signed are the two `AgentState` fields.
`AgentLink`, `link`, `AgentState::new`, `activation()`, `model_mut()` and the
`agent_activation` module are `pub(crate)`. `env_files` is a module of the
binary target. Outside the library:

- `main.rs` uses `agent::Classify`, `agent::types::FnConsent` and
  `agent::types::ReplTurnOutcome`, and calls `CompilerSession::enable_agent`,
  `agent_is_active`, `classify_for_agent`, `agent_turn` and
  `record_repl_turn`. None of those signatures names `AgentState`.
- `tests/` and `benches/` have no Rust-level use of `cranelisp::agent` at the
  checkpoint or now. `tests/` drive the binary; `benches/` use
  `cranelisp::io_trace` only.
- Outside a public type, only the two builders produce an `AgentState`. Its
  only sink is the crate-private field `CompilerSession.agent`. An external
  holder of one could do nothing with it.

| Row | Exact delta | Consumers | Compatibility, schema, ABI | `public-api.txt` |
|---|---|---|---|---|
| P14 | With the `agent` feature, which is now default. Make `pub struct agent::types::AgentState` `pub(crate)`. At the checkpoint it exposed ten public fields: `transcript`, `model`, `provider_label`, `auto_accept`, `auto_accept_notice_shown`, `submit_gave_up`, `submit_committed`, `current_turn`, `error_class_runup` and `turn_ring`. Its public methods were `is_dormant`, `dominant_error_class`, `record_turn`, `record_user`, `record_assistant`, `record_assistant_tool_calls`, `record_tool_result` and `record_pull_result`. Make `pub fn agent::provider::build_agent_state_with(bool, bool) -> AgentState` `pub(crate)`. Remove `pub fn agent::provider::build_agent_state(bool) -> AgentState` from the public surface; it has no production caller. This subsumes W3's removal of `model` and `provider_label` | None outside the library (census above). Inside: `CompilerSession::enable_agent` and the agent module's own tests | Breaks only a crate that names `AgentState` or calls a builder, and none exists. `AgentState` is never serialised (§3.4), so there is no schema effect and no ABI effect. The agent-free build has no `agent` module, so it does not change | Root has no baseline. The seven library baselines +0 |

- **Recommended form.** `AgentState` is `design`(int)'s interior state. A
  public `AgentState` would send every later change to it, including W3's own,
  through this gate for no consumer
  ([Principle 02](../design/arch/principles/02-narrow-interfaces.md)).
- **Smaller alternative.** Remove only the fields `model` and
  `provider_label`. `AgentState` stays public, but code outside the crate can no
  longer construct it by struct literal. The user would then approve a public
  shape that has no consumer and that changes whenever the interior changes. It
  needs no further `dev` change.
- **Declining both** returns the representation to `design`(int). To keep both
  fields public, `AgentState` would have to give up activation and the handle
  agreeing by construction
  ([Principle 20](../design/arch/principles/20-model-invariants-by-representation.md)).
- **Not proposed.** Narrowing the rest of the unconsumed `cranelisp::agent`
  surface to the items `main.rs` uses. W3 did not change those items, and that
  census belongs in a later packet.

**`dev`(src) change under P14, after approval.**

- In `src/agent/types.rs`, change `pub struct AgentState` to `pub(crate)`.
- In `src/agent/provider.rs`, change `build_agent_state_with` to `pub(crate)`.
- Retire the test-only `build_agent_state`, so that no crate-private item is
  unused in the non-test build and no lint allowance is added. Its four test
  callers, in `harvest.rs`, `types.rs` and `mod.rs`, call
  `build_agent_state_with(false, false)`, or the function becomes
  `#[cfg(test)]`.
- Leave the remaining `pub` members alone: the type's visibility bounds them.
- **Evidence:** the default and `--no-default-features` builds compile without a
  new warning, and the three agent lanes pass. Review confirms that `tests/`,
  `benches/` and `main.rs` name neither `AgentState` nor a builder.

#### P15. `cranelisp-types`: the entry preload releases restaged slots — approved 2026-11-16, built in W4

Source: W4 `src/` review finding R1 and `qa`'s attribution
([evidence plan](../tests/plan/s123-evidence-delta.md) §3.6, row R-5). The entry
preload retires `__expr` and every minted instance with `retire_abi_changing`
before the recompile mints them again
([session transaction §8.2](../design/int/session-transaction.md#82-faithful-writes)).
Each retirement is a tombstone, and tombstones persist, so every cached launch
of an entry with `k` instances loses `k + 1` of its 1,024 slots for good. With
128 generics the seventh cached `--run` or `--link` fails.

| Row | Exact delta | Consumers | Compatibility, schema, ABI | `public-api.txt` |
|---|---|---|---|---|
| P15 | In `cranelisp-types`, add `pub fn SymbolTable<(), ()>::release_callable(&mut self, name: &Symbol) -> Result<(), LifecycleError>` to the `impl` block that holds `into_concrete`. It removes the single callable `name` from a decoded, code-free table and drops its slot claim without recording a tombstone, so a later mint may reissue the index. Existing tombstones are kept. Errors: `MissingBinding` when `name` is absent; `NotCallable` when it is not a `Decl::Callable`; a lifecycle-validation failure leaves the table unchanged and returns that error. Rustdoc states the caller's obligation: release only an index that no code this process may load embeds | Root: `src/session_v4/lifecycle.rs::release_bodies_the_recompile_restages`, called by `preload_entry_slot_assignments`. It releases `__expr` and each `minted_from: Some(_)` instance on the decoded table before `into_concrete`, instead of retiring them on the live-typed table. New consumer edge: root → `release_callable`. `retire_abi_changing` keeps its contract and its in-session consumers, the demand replay's table clone in `src/worker.rs` and typecheck's `adt.rs` | Additive; no existing item changes. **No `CACHE_SCHEMA_VERSION` bump**: no serde shape changes, and `retired_slots` still serializes but stops growing per launch. Caches written by the uncommitted W4 tree keep their surplus tombstones until the entry's source changes or the cache is removed; no committed build wrote them, because `bc57cbf1` has no preload retirement. No ABI effect: emitted code and the GOT layout are unchanged | types +1 |

- **No correct fix exists inside the current API.**
  - *Not retiring* leaves a preloaded instance live with a slot and no code.
    The batch compiles only staged bodies (session transaction §2.5), and
    R-4's cells crash.
  - *Restaging under the same key* would extend the worker's demand replay,
    which today restages only instances of templates the same turn restages,
    to every persisted instance. Each launch would then replay a set that never
    shrinks: an instance demanded once by a REPL expression would compile on
    every later launch. The instances a module needs follow from its source,
    which the recompile checks anyway; the whole-file rebuild already rests on
    that (§8.5). A persisted demand set is a second source of that fact
    ([Principle 07](../design/arch/principles/07-single-source-of-truth.md))
    recorded before the source it depends on settles
    ([Principle 26](../design/arch/principles/26-record-from-settled-state.md)).
    Restaging also cannot cover `__expr`, which no definition demands.
  - *Not persisting the retirement* needs either a filter in the
    serialization, which is another API change, or removing the claim from
    the table, which is this release.
  - *`retain_callables` then `rollback_callables`* would drop the new
    tombstones, but only by restoring a transaction snapshot outside its
    contract. A facade that its consumer must misuse is an architecture
    defect. `discard_declared` and `remove_non_callable` refuse slot-carrying
    callables by design.
- **The safety argument, checked against
  [Principle 22](../design/arch/principles/22-published-pointers-have-retention-owners.md).**
  A tombstone protects code that embeds an index
  ([session transaction §7.2](../design/int/session-transaction.md#72-freezing-is-structural)).
  There are three possible holders:
  - *This process.* A decoded table holds no compiled owner (`C = ()`). Its
    GOT is the fresh slab that deserialization creates, because `got` is
    `#[serde(skip)]`. Nothing has compiled against it, so a release displaces
    no code and creates no retention obligation. The preload runs once, from
    the binary's one `register_module` call, before any live entry table
    exists. Grade: **structural**: the type admits no compiled owner.
  - *Other modules' cached objects.* These can embed the entry's indices.
    §8.2's ground, that a cache-restored module cannot depend on the entry
    without a module cycle, does not hold for a module that `/mod` loads and
    that imports the entry. The argument rests on the mint rule instead.
    Instances are minted in the demanding module with their own slot
    ([monomorphisation §3.7](../design/typecheck/monomorphisation.md#37-cross-module-body-recheck-scoping)),
    and `__expr` is never referenced across modules. Such code therefore
    embeds only authored slots, which the preload keeps. Grade: **asserted
    with a named falsifier**: another module's cached object that relocates
    against the entry's GOT at an index the entry's table holds for a minted
    instance or for `__expr`.
  - *The entry's own earlier object.* The entry is compiled from source, and
    one compile writes its new object and `.meta.json` together.
- **Why only on the decoded table.** On a live table, the same removal would
  reopen the hazard that tombstones close. Placing it on `SymbolTable<(), ()>`
  makes that misuse fail to compile
  ([Principle 18](../design/arch/principles/18-enforce-invariants-structurally.md),
  [Principle 20](../design/arch/principles/20-model-invariants-by-representation.md)).
  Residual: `got` is a `pub` field, so a caller could assign a live GOT to a
  decoded table. This row does not widen that field.
- **Mechanism here, policy in int.** Types supplies the release. Which bodies
  the recompile restages stays int's policy, recorded by `design`(int) in
  §8.2. A predicate form, `release_minted_instances(&mut self)`, would need no
  caller obligation for instances. It cannot name `__expr`, which is an int
  constant, and retiring that alone would still exhaust the table after about
  a thousand REPL restarts.
- **Not in this row.** Persisted tombstones from ABI-changing redefinitions
  remain backlog item 0466, which the user deferred indefinitely
  ([performance backlog](../design/arch/backlog/performance.md) §4).

**`dev` changes after approval.**

- `dev`(types) adds `release_callable` with module tests. A released index is
  reissued by the next mint. Existing tombstones are unchanged. The `Missing`
  and `NotCallable` refusals and a validation failure leave the table
  unchanged.
- `dev`(src), in `preload_entry_slot_assignments`, releases on the decoded
  table and then calls `into_concrete`. It adds `qa`'s R-5 unit row and
  observes it failing on the count before the change. The row runs three
  sessions over one cache with unchanged source: `retired_slots` and the slot
  high-water mark after the second and third equal the first's, each
  authored definition keeps its slot, and each instance has code. The R-5
  cell turns green and R-4's fence cells stay green.

#### P16. Root crate: one module-to-file mapping for the binary (ACT-1020) — approved 2026-11-16, built in W4

Source: W4 `dev`(src). Two `src/main.rs` sites still build `{module}.cl`
without the resolver's mapping, which turns dots into directories
(spec §8.1). One is the error path's fallback entry file (line 235). The other
is the Rule 3 probe in `resolve_target_from` (line 1224). The mapping,
`pipeline::module_relative_path`, is private to the library, and the binary is
a separate crate, so converging the two sites needs a `pub` item. The gate
applies as it does for P12 and P14.

| Row | Exact delta | Consumers | Compatibility, schema, ABI | `public-api.txt` |
|---|---|---|---|---|
| P16 | Root crate (no baseline). Widen `pub(crate) fn pipeline::project_root_candidate(module: &ModuleFullPath, project_root: &Path) -> PathBuf` to `pub` and re-export it from the crate root: `pub use pipeline::project_root_candidate;`, giving `cranelisp::project_root_candidate`. Rustdoc states the promise: this is the file that `module`'s name maps to under `project_root`, and the first file the resolver probes; `core.str` maps to `{project_root}/core/str.cl` | `src/main.rs` (the binary target): the fallback entry file and the Rule 3 file probe. New consumer edge bin → `project_root_candidate`. The library's own callers (the resolver, the entry-registration refusal and the test runner's selection) are unchanged | Additive: a visibility widening with an unchanged signature. No schema or ABI effect | Root has no baseline. The seven library baselines +0 |

- **Rejected alternatives.**
  - *A second copy of the mapping in `main.rs`* would derive the same file
    from the same module name in two places
    ([Principle 07](../design/arch/principles/07-single-source-of-truth.md)).
    That divergence is what ACT-1020 is.
  - *Moving target resolution into the library* would add a larger public
    surface for the same edge.
  - *Putting the mapping in `cranelisp-types`* would add an item to a
    baselined crate for a fact that only the root uses.
- **Not decided here.** Whether Rule 3's directory probe applies to a dotted
  target is a CLI question for `spec` (§0.5.5). P16 supplies only the file
  half.
- **`dev`(src) change after approval.** Widen and re-export the function. In
  `main.rs`, derive both paths from it with `ModuleFullPath::from`. Keep the
  R-3 cells for ACT-1020 and their undotted control green.

## Part B — scheduled outside the Phase 5 functional change-sets

### B1. K5 N1: renamed import and export entries (ACT-0997) — S124

| Row | Exact delta | Consumers | Compatibility, schema, ABI | `public-api.txt` |
|---|---|---|---|---|
| N1 | In `cranelisp-types`: add `#[non_exhaustive] pub struct ImportName { pub source: Symbol, pub local: Symbol }` with `pub fn ImportName::new(source: Symbol, local: Symbol) -> ImportName`; change `ImportNames::Specific(Vec<Symbol>)` to `ImportNames::Specific(Vec<ImportName>)`. An unrenamed entry has `source == local`. `ExportSpec` shares `ImportNames`, so §8.4 export renames use the same shape | Producer: frontend `module_extract.rs` parses `(source local)` entries. Root: `src/imports.rs` binds `local` to `source`; `src/save.rs` regenerates the written form and merges lists; `src/session_v4/test_runner/selection.rs`, `src/process_form/{cache_restore,dependency}.rs`, `src/cluster.rs`, `src/session_v4/{index_worker,lifecycle}.rs` pass through or match | Breaking for every match on `Specific`'s payload. **`CACHE_SCHEMA_VERSION` bump**: `SymbolTable.imports` and `exports` are persisted. No ABI effect. The correction must carry ACT-0997's impl-identity evidence (an impl written through a renamed type import and a renamed trait import, each persisted with a later definition, plus a cold restart) | types: +12 (struct, 2 fields, `impl` header, constructor, 7 auto-trait rows), 1 changed (`Specific`). Frontend +0 |

`ImportNames` itself lacks the `#[non_exhaustive]` the types policy requires.
That is a separate one-line hygiene change, not included.

### B2. K11: the baseline batch — S123 close

| Row | Exact delta | Consumers | Compatibility, schema, ABI | `public-api.txt` |
|---|---|---|---|---|
| K11-a (ACT-0955) | Add `--omit auto-trait-impls` to the canonical command (`design/arch/AGENTS.md` §Baseline-diff discipline, `tests/AGENTS.md`) and to `tests/public_api_relocations.rs`; regenerate all seven baselines in one mechanical change-set. Before it, add a direct compile fence for any auto-trait property that is a cross-crate promise with no in-workspace consumer to enforce it. Candidates are the `cranelisp-platform` types out-of-tree platform authors hold; in-workspace cross-thread uses already fail to compile if a property is lost. Coupled: remove `unsafe impl Send for CacheWritePacket`, which R10-3 makes moot | The guard and the two documents | No product, schema or ABI change. Explicit `unsafe impl Send`/`Sync` rows remain (13 in source) | Approximate contraction by pattern at the checkpoint: types −978, frontend −14, typecheck −68, backend −210, intrinsics −91, platform −194, primitives 0. Part A and P13 change these figures; the regenerated diff is the exact figure and needs one user confirmation, separate from functional rows |
| K11-b (ACT-0963) | Remove the field `pub is_runtime: bool` from `catalog::IntrinsicEntry` (also printed at the root re-export path), with its derivation test | None outside the crate; mentioned in prose in intrinsics `lib.rs` and backend `jit.rs` | Breaking only for struct-literal construction, which happens only in the crate. No schema or ABI effect | intrinsics −2 |
| K11-c (ACT-0971, T1) | Narrow `SymbolTable::settle_template` and `SymbolTable::settle_concrete` to `pub(crate)` | None outside `cranelisp-types`; production uses the `settle_checked_*` pair. The callers are the crate's own module tests | No schema or ABI effect | types −2 |
| K11-d (ACT-0971, T2) | Narrow `MonoExpr::lenient_from_expr` to `pub(crate)`; re-export it from `cranelisp_types::test_support` under the existing `test-support` feature | Production: none outside types (`synthetic_local_from_expr` delegates internally). Tests: 14 call sites in root test modules and backend `test_support.rs` move to the test-support path; root and backend dev-dependencies enable `test-support`. Its planned end state is deletion ([concrete boundary](../design/arch/concrete-boundary-type.md) §3.1.1) | No schema or ABI effect. The default baseline is generated without `test-support` | types −1 |

### B3. Audit R10: public items with no consumer (backend audit F11) — S123 close

Census at the checkpoint: each item's external references were searched in
`src/`, `crates/`, `tests/` and `platforms/`; comment-only mentions are not
consumers.

| Row | Exact delta | External consumers found | Compatibility, schema, ABI | `cranelisp-backend` `public-api.txt` |
|---|---|---|---|---|
| R10-1 | Remove `pub fn load_object` (crate root) | None. `Linker::load_object` calls are a different method | — | −1 |
| R10-2 | Make `mod artefact`, `LinkerArtefact`, `ObjectArtefact` and their root re-exports `pub(crate)` | None | — | −42 |
| R10-3 | Delete the dormant root module `src/cache_writer.rs` and make `CacheWritePacket`, `ObjectCompileInput`, `ProcessedPacket`, `build_cache_packet` and `process_cache_packet` `pub(crate)` or delete them; `build_isa` and the `cache::object` module path stay | Only `src/cache_writer.rs`, which nothing in the root calls. Removes the edge root → `cache::object` packet family | — | −41 |
| R10-4 | Make `pub mod compiler` and `compiler::CompileContext` (struct, 10 fields, `lookup_type_def`, `Clone`) `pub(crate)` | None; no other public signature names it. The typecheck and types hits are `cranelisp_types::CompileContext`, a different type | — | −23 (including the module line) |
| R10-5 | Make `pub mod primitives_inline` `pub(crate)` | None; it exports nothing | — | −1 |
| R10-6 | Make `heap::HeapClosure` and its five associated items `pub(crate)` | None; intrinsics' mentions are comments | — | −17 |
| R10-7 | Make `heap::NULLARY_THRESHOLD_I64`, `jit::jit_free_memory_call_count`, `got_observer::emit`, `cache::serialize::{serialise_meta, deserialise_meta}` and `cache::CACHE_FORMAT_VERSION` `pub(crate)` (`jit_free_memory_call_count` under `#[cfg(test)]`) | None (`tests/cache.rs` and `src/got_trace.rs` mention them in comments only) | — | −6 |
| R10-8 | In `cranelisp-types`: remove the field `borrowed_sibling: Option<CallableSlot>` from `Realization::ExternShim`, which no producer populates since ACT-0974 | Backend cache validation arm (`cache/serialize.rs`) and tests; types `lifecycle.rs`, `module.rs`; typecheck tests; `tests/ownership_fences.rs` | **`CACHE_SCHEMA_VERSION` bump**: `Realization` is persisted | types −1, 1 changed (the variant) |
| R10-9 | Layout dual source: closure, ADT and Vec offsets are defined in both backend `heap.rs` and intrinsics. Position: intrinsics owns them, as bounded contexts §4b invariant 2 states, and the backend reads its blessed constants as primitives already does for strings and vectors | Backend emission | No layout change | **Pending**: the exact constants are for `design`(intrinsics) and `design`(backend) to list; expect additions to intrinsics and removals from backend. A listed row returns here before implementation |

## Part C — decisions outstanding

| | Decision | Recommendation |
|---|---|---|
| G7 | R10-9, once its constants are listed | Decide when listed |
| G8 | P15: the entry preload releases restaged slots (§A6) | Approve. No correct fix exists inside the current API, and the decoded-table placement keeps the release off live tables |
| G9 | P16: `cranelisp::project_root_candidate` for the binary (§A6) | Approve. It is the narrowest item that gives `main.rs` the resolver's mapping |
