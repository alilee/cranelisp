# Int — Master Design (Binary surface — `src/` + `crates/cranelisp-exe-bundle/`)

Owner: `/design`. Single source of design intent for the integration layer (`src/` + `crates/cranelisp-exe-bundle/`). Authored Sprint 63; refreshed Sprint 64 against the pinned Decision 40 / 41 / 42 + Principle 14 / 15 configuration.

**Sprint 122 — selected Binary/int closure.** `design/int/s122-closure.md` is the current
entry point for the approved reload/session, macro/quote, result-root, `/mem`,
diagnostic-recovery and eval-client review. It records the source-reconciled
mechanics, one continuous Phase-5 reservation and the explicit stop on an
ungrounded public codegen-failure trigger.

**Int holds no private copy of a neighbour's fact.** The symbol lifecycle,
alias-key mint, result-root rule, RC release and instantiation trigger are
owned upstream (`design/arch/symbol-table-lifecycle.md`,
`design/arch/module-alias-scoped-lookup.md`, `ConcreteType::result_root`, the
intrinsics consume funnels, `instantiate_demands`); int consumes them and
decides nothing they own. `design/int/int.md` §12.1 states the standing review rejects that keep it
so, and `design/int/int.md` §16.0 the obligations still open against it.

**S121 correction, approved 2026-09-04.** Its publication-receipt rule retires
unbuilt with the redefinition outcomes it carried
([S117 recovery §1.1.3](s117-conformance-recovery.md#113-post-publication-outcomes-retired)).
Public exposure is guarded only at `NameCandidate` routes—the obsolete
binding-shaped no-op closure gate deletes. Synthetic tables are constructed
off-map through fallible lifecycle operations, so the public constructor is
`pub fn CompilerSession::new(settings: SessionSettings, project_root: PathBuf,
entry_module_name: &str) -> Result<CompilerSession, CranelispError>`; bootstrap
failure is diagnosed rather than asserted.

**Sprint 117 conformance and recovery.**
`s117-conformance-recovery.md` is the active subordinate design for the
Binary/int portion of Tracks A and B. One entered cluster now remains a
prepared turn through ordinary Passes-2/3 staging, exact codegen batch
derivation, and JIT completion; only successful codegen reaches the live commit
and dependent-redefinition gates. Source-ordered macros are the S121 exception:
each complete macro publishes as its own checkpoint before expansion continues.
The same design pins
uniform macro-expanded declaration ordering, exact failing-unit attribution,
the shared inverse impl relation for `/info <Type>`, fully-qualified
constraint rendering, and ordered multi-definition presentation for `def`
faces DF-1/DF-2. Its macro-clause refinement uses an exact one-module staging
and lets dependency modules publish independently; no cross-module shadow
world or rollback remains. Pre-codegen clause descriptors are distinct from executable clauses, whose
non-null entry pointer is inseparable from a required `Code` owner and ABI
witness. `def` remains a stdlib macro and DF-3 is not included.

**Program-result ownership.** `result-owner.md` is the contract (R15). A clean
result stays owned as `(i64, Type)` through its last observation and is then
released exactly once through backend's module-qualified per-concrete drop
glue, keyed on the producer's codegen type and classified by backend's own
`HeapCategory::classify`. Fresh JIT reads the `{artifact, owner}` pair the
ordinary prepared publication writes to `SharedState.fresh_jit_drop_glues`;
cache-hit resolves the same canonical symbol through the entry's `Linker`;
linked startup relocates and calls it after exit-code conversion. The owner
attaches at the execution seams, never inside the prepared transaction, and
holds the code owner through the call. No JIT-only, IO-only, display-owned,
shallow or type-erased releaser is part of int.

This document elaborates *within* the bounded context fixed by
`design/arch/bounded-contexts.md` §6. The current public crate source and its
generated API checks are the concrete facade evidence. Where this document
drifts from the bounded-context statement or an approved public contract, route
the boundary conflict to `/arch` and update this doc accordingly.

> **Why int is the largest surface.** int integrates everything. It owns three internal cadences (compilation, REPL, watcher), four observability sinks (scheduler trace, IO trace, GOT trace, introspection store), the only `Code` carrier instantiation site, the gap-orchestration crossing point, the slash-command surface, the cache writer, the file watcher, the line editor, the CLI, the `--link` driver, the prelude loader, and the error formatter. By design, int has the most subordinate docs and the largest LOC count.

> **Audit reconciliation.** Open integration audit points are carried by [ACT-0965](../../sprints/actions/ACT-0965-src-audit-residuals.md). References below to older assessments are historical rationale recoverable from Git; they do not establish current implementation status.

---

## 1. Bounded-context recap

Per `design/arch/bounded-contexts.md` §6 — `int` is the *integration layer* spanning two crate paths (`src/` and `crates/cranelisp-exe-bundle/`), treated as ONE surface for triad purposes. It hosts three internal cadences (compilation, REPL, watcher) with distinct execution shapes, coordinates the typed handoffs between them, owns all dev tooling (slash commands, tracing, observability, introspection), and is the only crate that knows the concrete carrier of compiled code.

**Owns**:
- `SharedState` construction and lifecycle (per Decision 38)
- `CompilerSession` — high-level facade `::main` constructs and drives
- Pipeline orchestration: `register_module` (with Phase 0), `process_form` (gap-retry loop), `eval`, `trampoline`
- `CompileScheduler` — single coordination authority (work dispatch + per-symbol/module wait/release)
- Worker pool — priority + nice loops, persistent (Decision 27)
- Object cache orchestration — sidecar `.meta.json` + `.o`, version-checked, cache-hit-via-`register_module`-recursive (Decision 37)
- File watcher — `notify`-based, polled at REPL prompt boundary
- REPL session: line editor, slash-command dispatch, prompt formatting, banner, eval cursor, `current_repl_module`, `regenerate_backing_file`
- Per-symbol introspection store on `SharedState.introspection` (mode-conditional Decision 38) — populated by parse + codegen, consumed by `/source`/`/sexp`/`/clif`/`/disasm`/`/time`
- Error formatter (`Sess::format_error`) — resolves `ErrorLocation` against introspection at display time (Decisions 39 + 42)
- REPL display / pretty-printing (Sess::format_eval_result, Sess::pretty_print) — including the relocated `display.rs` (post-FIXME 0108)
- Platform DLL session retention (`SharedState.kept_dlls`) and the `(platform "name")` load orchestration
- Diagnostic ring buffers — scheduler trace, IO trace (post-Decision 40), GOT trace (post-FIXME 0099). All env-var activated, all parallel `src/*_trace/` modules
- `--link` orchestration: validates `main`, emits `_main` alias `.o` (Decision 36), invokes system linker
- Exe-bundle: the alias-`.o` template + the static archive consumed by `--link`
- CLI parsing (`Action`, `ProjectTarget`, `SessionSettings`, `CliError`)

**Does not own**:
- Source parsing (frontend)
- Macro-head recognition (`cranelisp_types::resolve_macro_head`) and reader-quote folding (frontend). int owns the Pass-1 expand walk and macro execution ([§6.8](#68-pass-1-macro-recognition-and-execution))
- Type inference (typecheck)
- Code emission (backend) — backend fills GOT slots and returns artefacts; int attaches the `Code` owner (§7.2)
- Runtime helpers — RC, allocator, string ops, IO trampoline (runtime)
- Platform ABI contract (platform)
- Boundary types (`cranelisp-types`, owned by `/arch`)

**Crosses the boundary**:
- **Inward**: the approved public surfaces of the compiler and runtime crates,
  as consumed by the current Binary/int source and checked APIs.
- **Outward**: nothing for other workspace crates — `int` is the application root. Exe-bundle exposes a startup stub used only by the system linker.
- **Window types**: cadence-scoped; not exposed to other crates.

**Architectural constraints (load-bearing)**:
- Mutual-import deadlock (Decision 30) — two modules that import each other deadlock the form-by-form scheduler. Workaround: `discover-tests`. **S93: structurally resolved by the signature/body pre-pass (`design/int/signature-body-prepass.md`) — the same fix that closes the H6/H7 import race (FIXME 0425 item 1). Mutual imports are a compile-time cycle-error (ratified user ruling, S93 Phase-3 review): the module-atomic src/-only barrier converts the deadlock into a deterministic `CycleError` at the import site. The "compile mutual imports" reading is REJECTED, not deferred — no cross-crate typecheck change is admitted; FIXME 0448 is closed. Authoritative record: BC §6 + `concurrency-dependency-service.mmd` Note.**
- **Compiler-internal H6/H7 import/typecheck race** (`'X' not found in module 'Y'`, ~5–10% under contention) — the convention-spread publish/readiness/block/resume protocol ([historical concurrency analysis](https://github.com/alilee/cranelisp/blob/48d6e713a396e0e6ba3f4c0b19174144ad3676a6/design/int/concurrency-architecture.md), sections 3.5–3.6, FIXME 0425 item 1). **S93 gate: closed structurally by the signature/body pre-pass (`design/int/signature-body-prepass.md`), replacing the tactical `eval_in_flight`/`eval_owned` flag family (heisenbug lineage) with a two-phase barrier — Principle 8/18.**
- One `CompilerSession` per process (pipeline-v4 §1).
- Per-batch JIT lifetime (Decision 31; §5.2) — never a long-lived per-worker JIT.

---

## 2. Public surface

The current root-library source and generated public-API checks are the concrete
public-surface evidence. `design/arch/bounded-contexts.md` §6 owns the boundary;
this document elaborates its internal architecture.

Three structural notes about the surface worth naming:

1. **`CompilerSession` is the high-level facade.** A single object that `::main` constructs and drives. Construction is fallible and returns `Result<CompilerSession, CranelispError>` because bootstrap uses the same fallible lifecycle machine as every other birth route. It wraps an `Arc<SharedState>` (the worker-shareable subset) plus initiator-thread-only state (watcher channel, REPL eval cursor, worker pool handles, accumulated warnings). Every CLI mode (`--run`, `--link`, REPL) constructs the same `CompilerSession`; the only difference is which methods are invoked after `register_module`. Per Principle 11 (single pipeline; mode parameters) — there is exactly one `process_form`, parameterised by mode. The mode discriminator is `SharedState.run_mode` (`session_v4/types.rs`), which replaced the former `shared.introspection.is_some()` proxy.
2. **No re-exports of `cranelisp-types` items beyond the checked Binary/int
   public surface.** Per Principle 15 (facade types live with their behavior),
   int imports from each implementation crate directly. Any convenience
   re-export is retained only when it remains present in the current checked
   public surface; the root library has a small consumer audience.
3. **`Code` is re-exported, not defined, here.** `Code` lives in `cranelisp-backend`; `src/code.rs` re-exports it and instantiates the session table (§5.1). Backend fills GOT slots inside `compile_to_module`; int attaches the `Code` owner afterwards (§7.2). `cranelisp-types` never depends on backend (Principle 3).
4. **The test harness has one public entry.** `CompilerSession::run_tests` returns a `TestRunReport` whose accessors are its text, its warnings and its exit code; the user approved this delta on 2026-09-28. It is the only public item the `--test` harness adds. S123 target, packet row P12: `run_tests` becomes the test child's engine and `session_v4::supervise_tests` returns the report ([test runner §6.5](test-runner.md#65-the-test-child)). Selection, the eligibility scan and the run-and-report core that it shares with `/run-tests` and `/run-all-tests` stay crate-private ([test runner](test-runner.md)).

---

## 3. Current-state summary (structural map)

The map is by subsystem and module home. Per-file line counts are deliberately
not pinned; `wc -l` over `src/` is the current measure.

The two structural facts that dominate the tree today:

1. **The former `session_v4.rs` god-file is decomposed.** `session_v4.rs` is now a small
   facade; its substance lives under `src/session_v4/` (`lifecycle.rs` — the largest,
   `CompilerSession` construction/register/link/trampoline/watcher; `shared_state.rs`;
   `index_worker.rs` — the `/search` background indexer, `index-worker-isolation.md`;
   `nice_worker.rs`; `test_runner.rs`; `types.rs`; plus per-concern `*_tests.rs` submodules).
   REPL eval split to `src/eval.rs`; the REPL command/display surface split to `src/repl/`.
2. **The REPL command/display surface is the five-file `src/repl/` directory**
   (`mod`/`search`/`format`/`format_type`/`commands`); §3.3 states its structure.

### 3.1 Subsystem map (module homes)

| Subsystem | Module home(s) |
|---|---|
| CLI + mode dispatch | `main.rs` (the single Run/Link/REPL dispatcher, Principle 11) |
| Module registry / visibility | `lib.rs` (5 binary-facing `pub mod` for `main.rs` imports + `cluster`/`worker_pool`/`cache`; everything else `pub(crate)`) |
| Session lifecycle + shared state | `session_v4.rs` (facade) + `session_v4/{lifecycle,shared_state,nice_worker,types}.rs`; `session_setup.rs` (construction helpers independent of `CompilerSession`) |
| Test discovery and running | `session_v4/test_runner.rs` (the `discover-tests` extern and its runner state) + `test_runner/{discovery,selection,run}.rs` (the one eligibility scan, test-module selection and the run-and-report core shared by `--test`, `/run-tests` and `/run-all-tests`) ([test runner](test-runner.md)) |
| Scheduling + workers | `scheduler.rs` (+ `scheduler/tests.rs`) — the single coordination authority; `worker.rs` (+ `worker/tests.rs`) priority/nice loops + codegen/cache subsystem; `worker_pool.rs`; `thread_util.rs` |
| Gap-orchestration form chain | `process_form.rs` + `process_form/{form_dispatch,dependency,macro_clause,macro_resolution,platform,cache_restore,tests}.rs` — the sole crate-crossing where a `ResolutionGap` becomes a scheduler call (Principle 1/7) |
| Cluster processing | `cluster.rs` (`process_cluster` → `ClusterOutcome::{Done, Gap}`; `ProcessedCluster` carries warnings, resolved imports, introspection records and the boxed `PreparedCommit`, which lives in `worker.rs`. No redefinition outcome rides it ([session transaction §5.1](session-transaction.md#51-why-no-redefinition-can-break-a-caller)). |
| REPL eval | `eval.rs` (form-chain eval, bare-symbol introspection, dep registration); `repl_input.rs` (the `ReplInput` TTY/non-TTY abstraction) |
| REPL command/display surface | `src/repl/` — five files; §3.3 states the structure and `src/AGENTS.md` §"Session/REPL module map" lists the members |
| Live redefinition | `redefine.rs` — the guarded-redefinition gate, blocking-dependent scan, instance-rematerialization policy, `RedefKind` slot classification and the retention pool (`session-transaction.md`); it still carries the superseded dependent-recompilation machinery recorded in `design/int/int.md` §16.0 |
| Import/export + prelude fallback | `imports.rs` (+ `imports/tests.rs`) — the int-side installer; the `prelude_fallback` mechanism (`src/AGENTS.md` §"Prelude as a resolution FALLBACK") |
| Bootstrap seeds | `bootstrap.rs` — `mount_synthetic_modules` (special forms, intrinsic types, `macros`/`Option`/`IO`/`Trace` seeds) |
| Macro execution | `expander.rs` (the `JitMacroExpander` invocation core + expand loop); `marshal.rs` (sexp marshaling) |
| Display / pretty-print | `display.rs` (`display::envelope` + value render); `pretty.rs` (`pretty_print`/`pretty_print_plain`); `styled.rs` (the `Role`/`StyledDoc` vocabulary + `styled::render`, the sole style-table site); `style.rs` (raw style helpers); `syntax.rs` |
| Save / regenerate | `save.rs` — `regenerate_backing_file` (Decision 39; source-text-first regen, `src/AGENTS.md` §"Regeneration source") |
| Cache orchestration | `cache.rs` (the `ObjectCache` facade over session cache state: the validity query, loaded-source records, deferred entries); `cache/dependency_record.rs` (the dependency record, its one edge set, the one builder, deferral and the current-hash source, §7.6); `callee_edges.rs` (the one callee enumeration, shared with `redefine.rs`, §7.6.1); `session_v4/nice_worker.rs` (the `.meta`/`.o` and manifest writer); `session_v4/index_worker.rs` (index `.meta` writes); `process_form/cache_restore.rs` (restore). `cache_writer.rs` has no caller and deletes in S124 (§16.0) |
| `--link` + exe-bundle | `exe.rs` (`validate_main`, alias-`.o`, linker invoke); `link/{mod,gnu,apple}.rs`; `crates/cranelisp-exe-bundle/` |
| Platform DLL orchestration | `platform.rs` (+ `platform/tests.rs`) — `load_platform_dll`, `/platform-schema`, `ABI_VERSION` gate; `marshal.rs` (host↔DLL) |
| Auto-IO scheduling (compile-time) | `bind_chain_analysis.rs` (+ `bind_chain_analysis/{tests,identity_tests}.rs`) — §10.12 `bind!`-chain → `ParBind` / `LaunchContinue` transform (`bind-chain-analysis.md`) |
| Observability sinks | `observability.rs` (+ `observability/tests.rs`) scheduler/worker event log; `io_trace.rs`; `got_trace.rs`; `sched_dump.rs` — all env-var-gated ring buffers. |
| Embedded agent | `src/agent/` (fully `#[cfg(feature = "agent")]`; `agent.md`) |
| `Code` carrier + aliases | `code.rs` — `SessionSymbolTable`/`SessionModuleEntry` aliases; `Code` is re-exported from `cranelisp-backend` (Decision 41) |
| Pipeline helpers | `pipeline.rs` (`resolve_module_file`, shared worker/eval helpers) |
| File watcher | `watch.rs` |

Sprint 117 refines the REPL-eval row through
`s117-conformance-recovery.md`: `eval.rs` owns the prepared-turn terminal
decision; `worker.rs` retains the single staging/commit and codegen-enrollment
authorities; `repl/{commands,format,format_type}.rs` render canonical binding
identities. W3c uses one eval-owned `TurnDefinitions` receipt to retain every
emitted definition in order across macro checkpoints and dependency retries.
Ordinary definitions become displayable only after HM/codegen publication;
macros become displayable at their own successful checkpoints.
`EvalResult::Definitions` carries the complete published list, and the
formatter reads each binding's ordinary `ModuleEntry` classification. There is
no selected subject, macro-result type projection, parallel presentation map,
post-publication table scan, runtime execution, or cache field.

S121 replaces the candidate-table plan with source-ordered macro checkpoints.
Each direct or expansion-produced `defmacro` becomes visible only after its
parent, all active clauses and complete expansion-time dependency/generated-
realization closure have typechecked and codegen has succeeded. It then
publishes immediately through the ordinary one-module prepared transaction and
remains live if a later form fails. Ordinary forms on both sides accumulate
into one HM binding cluster and retain all-or-nothing publication.

A `ResolutionGap` retains only the uncommitted source/emitted continuation and
already-expanded ordinary prefix. It retries an uncommitted macro or resumes
after a committed one, so a generated macro is neither re-expanded nor treated
as a duplicate. `PreparedMacroTurn`, `TurnCheckWorld`, `TurnDelta`, candidate
invocation, reserved unpublished slots and cross-module rollback do not survive.
Macro readers snapshot parent metadata plus the selected clause pointer and
owner under one module guard; invocation holds the cloned owner after the guard
is released. A clause-set shrink derives exact surplus keys from the prior
parent metadata and retires only validated private same-parent `MacroClause`
rows through absent-key `ChangeAbi` decisions in that same checkpoint. Old
owners are retained before guard release and old slots remain frozen and
tombstoned; later growth mints fresh slots. Cache restore enforces a bijection
between parent metadata and active clause rows. See
`s117-conformance-recovery.md` §1.1.2/§2.1.

### 3.2 Gap-orchestration module cohesion

`process_form.rs` is the cluster spine (§6.2); its submodules divide by concern. Keep
`process_form/dependency.rs` whole even though it is the largest: the structural handlers
(`import`/`export`/`mod`), the single dependency seam (`drive_module_dep`, `block_dep`) and
the per-dependency prologue (`register_dep`) are one protocol. Splitting register, block
and drive across files makes the gap protocol harder to verify.

### 3.3 REPL command/display surface (`src/repl/`)

`src/AGENTS.md` §"Session/REPL module map" lists each file's members. The design rules:

- **`src/repl/mod.rs` is the bottom layer.** It holds slash dispatch, prompt/banner/editor,
  input classification and the shared toolbox: the resolution glue
  (`lookup_with_prelude_fallback*`, `resolve_symbol_arg`,
  `get_introspection`) and the referer-scan family (`body_references`, `sexp_references`,
  `source_tokens_reference`). Each family has exactly one home; a sibling copy is a
  divergent mirror (Principle 7).
- **Values and definitions render separately.** `src/repl/format.rs` renders values, eval
  echoes, symbol descriptions, source/s-expressions, name layout and the shared span
  primitives. `src/repl/format_type.rs` renders a named definition (type, trait, builtin type,
  special form, macro, overloaded function) and its related sections.
  `format_def_entry_doc` dispatches from the first to the second.
- **`src/repl/commands.rs` is the whole `handle_*` battery.** It stays one file: argument
  resolution and the eval helpers straddle any query-versus-action split, and readers find a
  command by its handler name.
- **`src/repl/search.rs` is the `/search` UI**, the interactive half of
  `src/session_v4/index_worker.rs` (`index-worker-isolation.md`).
- **Cohesion, not a line count, decides a split.** `mod repl` is private to the binary, so
  it has no public-API baseline; cross-file free functions are at most `pub(crate)`.

**Introspection lists every in-scope candidate, through one query.** A spelling in the
current scope may name several distinct canonical declarations (`spec/08-modules.md`
§8.6.4). `repl/spec/04-self-documentation.md` §4.1.11 requires bare lookup to print every
one — each by its own per-class rule (§4.1), under its canonical fully-qualified name, with
no ambiguity error or warning and no comparison of candidate types — and
`repl/spec/03-slash-commands.md` §3.8 requires `/sig` to print the same lines. Selection,
and the ambiguity rejection that goes with it, belongs to an input that *uses* the
spelling and stays on `spec/08-modules.md` §8.6.5 unchanged. The listing is a complete-set
enumeration, Principle 24's named carve-out, not a scan.

- **One candidate query, in the `src/repl/mod.rs` toolbox.** It builds the committed
  `ResolutionScope` the way `src/expander.rs::recognize_macro_head` does — shared
  construction, never a copy (Principle 7) — and returns
  `cranelisp_types::ResolutionScope::resolve_candidates` for bare and qualified names
  alike. It displaces the tier-first walk in `lookup_with_prelude_fallback_resolved_opt`,
  the qualified leg of `resolve_entry_arg`, and the raw table probe in
  `src/eval.rs::check_bare_symbol_introspection`. The root `""` special-form tier survives
  only as a **miss-only tail** — special forms are not module-scope candidates.
  `QualifiedModuleUnknown` and `PrivateInaccessible` keep today's behaviour, leaving the
  FQ-autoload retry and the mode-uniform §8.7.3 error untouched.
- **Silence at introspection is structural.** `resolve_candidates` is the whole-set
  primitive; only `resolve`/`resolve_macro_head` mint `ResolveError::Ambiguous`, so a
  surface that asks for the set cannot raise it. Terminal deduplication — one declaration
  reached by two paths prints one line — is the primitive's too, not int's.
- **Render from the canonical key; never re-resolve.** Each candidate displays from its
  `Resolved::canonical` by direct probe (`crates/cranelisp-types/AGENTS.md` §"Resolution
  primitive traps"). `src/repl/format.rs::format_definition_symbol_doc` re-deriving a
  displayed name from its bare spelling is the divergent mirror that made display show a
  tier winner (Principles 7, *Single source of truth*, and 24, *Resolve once*); removing
  that second resolver is also what lets a qualified re-exported spelling
  (`prelude/add-i64`) reach its defining terminal at the prompt as `/sig` already does —
  same path, no separate mechanism.
- **A lookup is not a defining turn.** The multi-candidate result carries several
  canonical `FQSymbol`s and answers `ty() = None` / `is_defining() = false` by
  construction. `EvalResult::Definitions` is a defining turn and is not reusable here.
- **Order is a function of the set, not of return order.** §3.8 binds `/sig` to bare lookup
  byte-for-byte, and the resolver returns current-module candidates before prelude ones,
  which is arrival-like. Sort by canonical `FQSymbol`.
- **`/info` and `/doc` report per candidate**, each keyed by its own canonical FQ —
  including `/info`'s definition-source and code-size reads, which are keyed by spelling
  today. `/doc`'s module-preamble fallback runs only on an empty set.
- **Set size decides a value-path member.** When a spelling has several candidates, a
  result-only-polymorphic nullary constructor among them is listed by its canonical
  §4.1.2 constructor line exactly as its concrete sibling is — the §1.5.1 value display
  is the sole-candidate disposition only — while a zero-argument macro among them still
  hands the turn to expansion (`repl/spec/04-self-documentation.md` §4.1.6).

Every crossing item is already published (`crates/cranelisp-types/public-api.txt`
`ResolutionScope::new`, `resolve_candidates`, `Resolved`); the change is binary-local and
carries no public-API delta.

**The dormant second describe path goes with it.** `CompilerSession::describe_symbol`
builds a symbol-description record off the tier-first helper and has no production caller.
It is a second description provenance, dormant only because nothing reaches it — and a
function whose name states the responsibility is what the next reader picks up, so it is
deleted together with the cross-reference collector chain and the description record that
exist only to feed it. What it reads over is retained and keeps its live callers: the
`; defn:`/`; impl:`/`; match:` sections are built independently in
`src/repl/format_type.rs`, and the symbol-category classifier and the brief listing record
serve `/list`, `/exports` and `list_user_definitions`.

**Residual: five readers keep the tier-first helper, and two of them display.**
`lookup_with_prelude_fallback` returns the current module's unique candidate *before* the
prelude hop and refuses only on a collision **within one table**, so for a spelling whose
candidates span tiers it answers the tier winner, and it answers `None` only for a
same-tier collision. Three readers ask membership and carry no identity: `/search`'s
`is_already_in_scope`, `symbol_is_bound` behind `/refs` and `/tests-for`, and the agent's
`symbol_is_mentionable`. Two render from its answer: `/search`'s `exact_in_scope_hit`
synthesizes the exact-in-scope row, naming one home, and `format_display_only_value_doc`
— the §1.5.1 nullary-constructor value display — reads the two-tier variant to choose the
type home it prints. The single-provenance rule above therefore holds of the §4.1.11
listing, `/sig`, `/info` and `/doc`, which render only from canonical keys; it does not
hold of those two. The residual's observable consequence is confined to a spelling whose
candidates span tiers: `/search` marks it already in scope and names the tier winner's
home rather than offering an import, and `/refs`, `/tests-for` and harvest read it as
bound rather than a typo. The triggered extension retires the three membership readers
onto a non-empty candidate set and the two display readers onto that set's canonical keys.
Discovery is unaffected either way; the importable index, its scan and the row set never
consult this query. The trigger is a wave that owns `/search` behaviour.

---

## 4. SharedState architecture (Decision 38)

The central structural decision. `SharedState` is the formal worker-shareable subset of the session — defined in `facades/int.md` §"SharedState" and reproduced here for design-intent visibility:

```text
SharedState (interior-mutable; workers hold Arc<SharedState>):
  symbol_tables : DashMap<ModuleFullPath, SymbolTable<Code, ()>>
  scheduler     : Arc<CompileScheduler>
  cache         : Arc<ObjectCache>
  kept_dlls     : DashMap<PathBuf, Arc<DllHandle>>
  introspection : Option<DashMap<FQSymbol, Introspection>>          // mode-conditional
  settings, project_root, lib_dirs, platform_dirs                   // read-only after construction

CompilerSession (initiator-thread-only):
  shared              : Arc<SharedState>
  watcher             : Option<WatcherChannel>
  current_repl_module : ModuleFullPath
  repl_input_active   : Arc<AtomicBool>           // shared with watcher event handler via Arc clone
  worker_pool         : WorkerPool                // joins on Drop
  warnings            : Vec<Warning>              // initiator-collected
```

### 4.1 Per-symbol mutability discipline

After Phase 0 (`register_module`), no code path holds a whole-module `&mut SymbolTable`. Per-symbol writes go through `SymbolTable::insert_or_update(&self, sym, entry)` and `SymbolTable::write_code(&self, sym, code)`, which acquire the inner DashMap's per-entry write lock briefly.

**The two `&mut SymbolTable` operations**:
1. **Structural records**: not written at registration (§6.1). Pass 0 writes them under the module's guard; a whole-file rebuild starts them empty ([§6.10](#610-the-import-generation)).
2. **REPL append**: `append_defn_order(&mut self, sym)` per eval that introduces a new defn. Brief initiator-thread `&mut` hold (microseconds).

Everything else — `insert_or_update`, `write_code`, `install_import_bindings`, `get`, `get_type`, `defined_symbols`, `public_symbols`, `all_symbols`, `allocate_got_slot`, `defn_order` (read) — is `&self`, no RefMut needed.

**Operational consequence**:
- Cross-module read contention disappears. Worker reading m1 via `shared.symbol_tables.get(&m1)` no longer blocks behind another worker's per-form RefMut on m1.
- Per-symbol gap mechanism becomes mechanically sound — `Gap(SymbolTypechecked)` / `wait_for_typecheck_symbol` / `notify_symbol_typechecked` round-trip works without livelock.
- Decision 30's "single worker per module during typecheck" reframes from a *lock-safety requirement* into a *scheduler ordering choice* — the lock layer no longer requires it; the scheduler keeps it as form-sequencing discipline.

### 4.2 No merge step

Workers do not "merge back" into the session. They mutate `shared.*` through interior mutability under per-cell locks, and other workers see the mutation as soon as the lock releases. Warnings are the one exception: `Warning` values route back to the initiator via the work-completion notification, where they are appended to `Sess.warnings`. Initiator-collected, never cross-thread for storage.

Per Decision 41, even the `Code` write happens worker-side: backend's `compile_to_module` calls `SymbolTable::write_code(&self, sym, Code::Jit { jit, ptr })` directly on the worker's `&shared.symbol_tables[scope]`. There is no longer a session-side post-loop that ferries a backend-returned tuple back into the symbol table — the int-side machinery at `worker.rs:2860–3018` collapses into the per-symbol call-site loop:

```rust
for sym in defined_symbols(&shared.symbol_tables[scope]) {
    let jit = Jit::new_with_symbols(&extra)?;
    compile_to_module(scope, &[sym], &shared.symbol_tables, shared.introspection.as_ref(), jit.jit_module())?;
}
```

### 4.3 Introspection placement (Decision 38, mode-conditional)

`shared.introspection: Option<DashMap<FQSymbol, Introspection>>`. The outer `Option`:
- `Some(map)` iff `RunMode::Repl`.
- `None` in production batch (`--run`, `--link`).

**The mode discriminator is the explicit `RunMode` carrier on `SharedState`, not the store's presence.** `RunMode::populates_introspection()` decides the `Option` once at session construction and gates every population site; `CRANELISP_CODEGEN_TRACE` does not enable the store. The earlier `introspection.is_some()` proxy was retired by `design/arch/d1-introspection-repl-only.md` §4 — a store's presence is not a readable statement of session intent, and two facts keyed on one field drift. Production batch pays zero per-symbol metadata cost.

**`Introspection` shape** (`src/session_v4/types.rs`):
- `source: Option<String>` — per-defn source snippet (Decision 39); replaces module-global source store.
- `sexp: Option<Sexp>` — post-expansion s-expression.
- `clif_ir: Option<String>` — CLIF IR text (when trace mode); **eagerly captured** post-codegen.
- `code_size: Option<usize>` — native code size in bytes; **eagerly captured** post-codegen.
- `compile_duration: Option<Duration>` — codegen wall-clock.

> **No `disasm` field.** Native disassembly is NOT a stored introspection
> field — it is **re-derived on demand** (Decision 41 on-demand model). Disasm
> is the most expensive metadata (a full capstone pass over the finalised
> machine code) and is needed only when a human types `/disasm`; persisting it
> for every compiled symbol would tax every REPL eval to serve a rare query.
> The GOT slot already holds the live code address and `code_size` is already
> captured, so `cranelisp_backend::produce_disasm(fq, code_size, symbol_tables)`
> reconstructs the disassembly from the same allocation the backend finalised,
> on the `/disasm` keystroke. This mirrors the eager/lazy split: cheap, often-read
> metadata (`source`/`sexp`/`clif_ir`/`code_size`) is captured at codegen;
> expensive, rarely-read metadata (disasm) is derived at read time.
>
> *Historical note:* an earlier `Introspection.disasm: Option<String>` field +
> a `CompilerSession::symbol_disasm()` accessor were introduced under the
> assumption the backend would write disasm eagerly. The backend never
> populated it (`worker.rs` step 7 sets only `clif_ir` + `code_size`), so the
> field is permanently `None` and the `/disasm` handler reading it always hits
> the dead "no disassembly available" path (S86 defect, ledger guard
> `disasm_command_shows_native_code_for_compiled_fn`). The field + dead accessor
> are vestigial and SHOULD be removed when `/disasm` is rewired (S87 Stage A);
> if removed they cease to be a read site below.

**Population sites** (all conditional on `shared.introspection.is_some()`):
- Publication installs the authored-form records that form processing staged for the generation's ordinary definitions, only after that generation publishes; the macro checkpoint writer records macros ([session persistence §2.4.1](session-persistence.md#241-who-writes-a-record)).
- Backing-file rehydration fills absent authored-form records for entries installed from the object cache, on first read ([session persistence §2.4.2](session-persistence.md#242-backing-file-rehydration)).
- `compile_to_module` per-symbol call (Decision 41): backend writes `clif_ir`, `code_size`, `compile_duration` directly into the introspection map via the `Option<&DashMap<FQSymbol, Introspection>>` parameter — no int-side post-processing. Disasm is NOT among them (re-derived on demand, above).

**Read sites**: slash-command accessors on `CompilerSession` (`symbol_source`, `symbol_sexp`, `symbol_clif`, `symbol_code_size`, `symbol_compile_duration`) read the stored fields; `Sess::format_error` for rich inline display; `Sess::regenerate_backing_file` for source emission. `/disasm` is NOT a stored-field read — `handle_disasm` calls `cranelisp_backend::produce_disasm` on demand (see §8.2.1).

Cited principles: P1 (Decoupling), P6 (Complexity has a budget — production carries no overhead), P7 (Single source of truth — one place per-symbol metadata lives), P11 (Single pipeline — one mode discriminator at the integration layer).

---

## 5. Code enum + lifecycle (Decisions 31, 35, 41)

### 5.1 Placement and instantiation

- `cranelisp-types` keeps `SymbolTable<C: CodeStore, L: LinkerStore>` generic
  over empty marker traits, so the shared crate never names Cranelift
  (Principle 3).
- `Code` lives in `cranelisp-backend` beside `Jit` and `cache::Linker`, the
  types its variants own. `src/code.rs` re-exports it and pins the session
  instantiation `SessionSymbolTable = SymbolTable<Code, ()>`; int is the only
  context that names a concrete `C`.
- `L = ()`: every cache-hit entry already retains its `Linker` through
  `Code::Linker`, so no per-table linker store exists.

### 5.2 Variants

- **`Code::Jit(Arc<Jit>)`** — fresh-build code. One `Jit` serves one compile
  batch ([persistent-workers §4.5](persistent-workers.md#45-per-batch-jit-not-per-worker-decision-31));
  int wraps it in an `Arc` after `compile_to_module` returns and attaches one
  clone to every entry the batch compiled.
- **`Code::Linker(Arc<Linker>)`** — cache-hit code mapped from one `.o`; every
  entry restored from that object shares the clone.

`Code` carries lifetime only. Callable addresses live in the module's GOT,
which is their single source of truth.

One enum keeps mixed lineage ordinary: a module restored from cache and then
extended at the REPL holds both variants, and no table-level "cache mode"
exists. Do not split the carrier into a second per-entry field, a `dyn`
store or a per-backing session; each reintroduces two retention disciplines
for one fact.

### 5.3 Lifetime and reclaim

- `Jit`'s `Drop` calls `JITModule::free_memory()` once, so pages unmap only
  when the last `Arc<Jit>` clone drops. `Code::Linker` behaves the same for a
  mapped object.
- The table entries are the retention roots. There is no session-side JIT or
  linker pool; `kept_dlls` remains because platform DLLs are session-scoped
  and hold their own GOT slab.
- A displaced body is not freed at replacement. Every retaining publication
  path moves the displaced owner into the session retention pool, because a
  detached strand or heap closure may still execute it
  (`session-transaction.md` §6). The two non-pooling paths that section names
  are its falsifier.
- The eval wrapper `__expr` is an ordinary entry of its turn's batch. Its owner
  keeps the pages mapped through execution and through the result's release
  (`result-owner.md`); its replacement follows the same displacement rule.
- A persistent per-worker JIT (withdrawn Decision 28) must not return: it
  coalesces every batch a worker ran and defeats reclaim.
- No current test observes per-JIT reclaim.

### 5.4 Access discipline

- Read a callable address from the GOT slot, never from `Code`.
- Consult `Code` only for compiled-code presence (introspection and codegen
  target selection) or to pair a retention root with an address that must
  outlive a call, as the result owner does (§7.4).
- `Code: Send + Sync` is `unsafe`-implemented in backend: after finalisation
  the carrier is only cloned and dropped.

---

## 6. Pipeline orchestration

### 6.1 `register_module` Phase 0 (Decision 38)

Registration parses the source and queues the module with its forms on the work packet
(`scheduler.register_module`). It writes no structural record. The cluster's Pass 0 records
`import`, `export`, `mod` and `platform` forms and discovers dependencies through
`drive_module_dep` (§6.2); [§6.10](#610-the-import-generation) governs the import record.

**Queue-priority rule (`delays_other`)** — `scheduler.register_module(module, delays_other)` routes the module into the prioritised `TypecheckFirst` queue when `true` and `TypecheckNext` when `false`. The flag answers one question: *is some other module's progress waiting on this one?*

- **Every dep-registration site passes `true`** — the `process_form/dependency.rs` handlers and drive seam (both cluster wrappers, §6.2) and the cache-restore transitive-import registration. A dep is registered precisely because something is blocked on it, and even where the immediate registrant has already finished (cache-restore's fire-and-forget recursion), any other module importing that dep will block on it.
- **`false` is for entry-module registration by the thread that is itself the whole-world waiter** — `register_module_with_source`, `reload_module`'s watcher-seed fallback, and `recover_startup_failure`'s re-drive. Nothing else is queued behind them.

A `false` at a dep site is a silent divergence: the dep lands in the unprioritised queue behind unrelated work while a blocked caller waits. (S59/S60 lineage; the rule is the one durable residue of the dual-path persistence collapse.)

#### 6.1.1 A missing entry source file

Status: **implemented 2026-09-30** (K1,
[ACT-1004](../../sprints/actions/ACT-1004-batch-missing-entry-diagnostic-intake.md))
in `register_entry_module`; review found no blocking or required finding, and
QA judged the evidence adequate
([K1 adequacy](../../tests/plan/s122-evidence-delta.md#k1--bounded-adequacy-2026-09-30)).
Private to `src/`: no public item, signature, carrier, schema or ABI change.

**Rule** ([CLI §0.5.5](../../repl/spec/00-cli-invocation.md#055-error-handling-r4-s52)
rule 2). Entry registration resolves the entry's source file (project root,
then lib directories), so it is the one place that knows the file is absent.
When the resolver finds no file:

- **REPL:** register an empty module, as today. This is the empty-start
  workflow, and startup recovery, the watcher and regeneration are unchanged.
- **Every other run mode** (`--run`, `--link`, `--test`): refuse before
  anything is registered, with a located module error naming the resolver's
  own project-root candidate, `{project_root}/{entry}.cl` for an undotted
  entry. This is the refusal `--test` reported before K1, moved rather than
  copied, so `--test`'s text and outcome do not change.
  - For a dotted entry the candidate maps dots to directories (`core.str`
    names `{project_root}/core/str.cl`), the module-to-file mapping that
    [CLI §0.5.6](../../repl/spec/00-cli-invocation.md#056-dotted-module-paths-tested)
    rules for every invocation mode. The candidate is
    `pipeline::project_root_candidate`, so the refusal names the file the
    resolver probed. The binary reaches the same helper through the
    `cranelisp::project_root_candidate` re-export (S123 W4, packet P16) for
    the error formatter's fallback file and the CLI's third-case file check
    ([REPL lifecycle §6](repl-lifecycle.md#6-project-root-resolution)).

**Why this reaches every batch outcome.** The batch arms of `main.rs`'s `run`
already propagate the registration result (`startup?`) before any wait,
`trampoline`, `run_tests` or `link_by_name`. The existing error path prints it
to stderr and exits 1. So no module compiles, `main` is never validated, no
report is written and no executable is produced. `main.rs` does not change.

**Why at registration and not at each batch caller.**

- One decision point serves all three batch modes, with the mode as a
  parameter where the fact is decided (Principle 11). The session's run mode
  is the existing REPL-versus-batch signal, and REPL-versus-batch is the
  distinction §0.5.5 draws.
- It reads the resolver's own answer (Principle 07). A caller-side check must
  re-derive absence, either from the recorded file path (as `run_tests` does
  now) or by probing the file again. A project-root probe would also refuse an
  entry that the resolver finds in a lib directory.
- A batch session has no use for an empty entry registered without a source
  file. Removing that state removes the `no 'main' function` misdiagnosis at
  its origin, rather than intercepting it in each mode. `run_tests` carries no
  check of its own (Principle 06), and batch callers must not add one
  ([test runner §11](test-runner.md#11-rejected-alternatives-and-potential-extensions)).

**Unchanged.**

- An entry file that exists but is empty compiles as an empty module in every
  mode. §0.5.5 is about absence, not emptiness.
- `/run-tests` and `/run-all-tests` never passed through the check.
- `register_module` stays public with the same signature. In a batch session
  it now returns an error for a missing entry, as §0.5.5 requires. The
  `run_tests` rustdoc drops the missing-entry case from its error list. Both
  are inside the root crate, which has no generated API baseline, so there is
  no baseline effect and no inter-crate gate.

An entry file that exists but cannot be read is governed by §0.5.5 rule 4,
designed below
([ACT-1019](../../tests/plan/s122-evidence-delta.md#act-1019--unreadable-entry-file-closed),
closed).

**Unreadable entry (ACT-1019).** Implemented 2026-10-01 under
[CLI §0.5.5](../../repl/spec/00-cli-invocation.md#055-error-handling-r4-s52)
rule 4.

- **Rule.** Entry registration reads a resolved entry file once. A read
  failure, including invalid UTF-8 and a permission error, is a located
  module error naming the file, in every mode. It is never an empty source.
  - **Batch** (`--run`, `--link`, `--test`): the error propagates from
    `startup?`, is printed to stderr and exits 1, as a missing entry does.
  - **REPL:** the entry fails before registration, so startup recovery makes
    it stand failed with that error
    ([REPL lifecycle §1.3.1](repl-lifecycle.md#131-session-lock), Startup,
    step 1). The session is locked, the startup report names the file, and
    the chokepoint keeps it as saved. A save that the watcher can read and
    compile releases it.
- **Why at registration.** It is the same seam and the same reason as the
  missing-entry rule above: one decision point, reading the resolver's own
  file. A whole-file rebuild and a dependency load fail on a read error.
  The watcher's change test also swallowed one, treating any read error as
  a deleted file, so a save that made a loaded file unreadable went
  unreported and the next definition overwrote it (review R3). Its rule is
  [REPL lifecycle §1.2](repl-lifecycle.md#12-poll-and-reload), Content
  hash.
- **Module evidence** (`lifecycle::entry_registration_tests`): a non-UTF-8
  entry under `RunMode::Run` and under `RunMode::Repl` returns a located
  error naming the file, and the scheduler has no registration for it;
  control: a readable entry registers. In `persistence_tests`, startup
  recovery over a non-UTF-8 entry leaves it standing failed, and its bytes
  are unchanged after a refused definition. The first readable compiling
  save releases it (review R1; the watcher row of
  [REPL lifecycle §1.3.2](repl-lifecycle.md#132-module-evidence-dev)).

**Module evidence** (`lifecycle::entry_registration_tests`):

- `run_mode_refuses_a_missing_entry_before_registration`: the error names
  `{root}/user.cl` and carries that file in its location, and the scheduler
  has no registration for the entry, so the refusal came before registration.
- `link_mode_refuses_a_missing_entry_before_registration`: the same under
  `RunMode::Link`. This twin catches a mode test written as "is `Run`" instead
  of "is not REPL".
- `repl_mode_registers_a_missing_entry_as_empty`: the empty-start control.
- `run_mode_registers_an_existing_empty_entry`: absence, not emptiness,
  decides.
- `run_mode_registers_an_entry_found_only_in_a_lib_directory`: catches a
  project-root probe standing in for the resolver.
- The test-runner session test
  `run_tests_reports_an_existing_entry_without_tests_as_an_empty_run` keeps
  the existing-entry leg: `No tests found`, exit 0. Its former missing leg is
  the first row above.

**End to end** (`tests/cli_missing_entry.rs`).
`run_missing_entry_file_is_named_on_stderr` and
`link_missing_entry_file_is_named_on_stderr` assert exit 1 with the missing
file named on stderr; both were RED before K1. The controls are
`test_mode_missing_entry_file_is_named_on_stderr`,
`repl_missing_entry_starts_an_empty_module` and
`tests/test_runner.rs::test_mode_neg_missing_entry_file_errors_without_report`.

No cell asserts the absence of `no 'main'` text, or of an executable under
`--link`. QA judged both held by construction and allocated no cell
([K1 adequacy](../../tests/plan/s122-evidence-delta.md#k1--bounded-adequacy-2026-09-30)):

- the refusal precedes registration (the first two module rows);
- `startup?` precedes `trampoline` and `link_by_name`;
- an ignored error would print nothing, which fails the positive cells.

**Grade:** measured, by the module rows and the two end-to-end cells.

#### 6.1.2 The entry is settled before the eval thread owns it

Status: **designed 2026-11-15 (S123 W1); revised the same day to a
structural form after `qa`'s grade ruling (M-2,
[S123 evidence delta](../../tests/plan/s123-evidence-delta.md)); built by
`dev`(src) in S123 W1 and checked against source by `design` (int) on
2026-11-15, with independent review and the suite run still to come.** The residual that `dev` found beside the
refused-requeue intake was routed here by `qa`. Private to `src/`: no public item, carrier, schema
or ABI change.

**Rule.** Every path that hands the entry to the eval thread waits until the
entry stands in a terminal pool. These paths are a successful registration, startup
recovery's wait on a registered entry, and the empty restart. A terminal
pool is `TypecheckDone`, `Complete` or `Failed`. This is what
Invariant SW (`src/AGENTS.md`; [§6.5](#65-entry-module-and-the-implicit-prelude))
assumes: no pool worker is mid-pass on the entry, and nothing can claim it.

**Why it does not hold today.** A worker publishes in-memory completion and
`TypecheckDone` as two scheduler calls, each under its own acquisition of the
scheduler lock (`src/worker.rs`, `notify_processed_ready`). Between them the
module has in-memory completion and is still `TypecheckWorking`. So
`register_module_with_source`'s whole-world in-memory wait
(`src/session_v4/lifecycle.rs`) can return while a non-empty entry is
mid-pass, and so can startup recovery's wait for the entry's in-memory
outcome. Only `restart_entry_empty` also waits for the pass to settle. In
that window a requeue of the entry is refused and silently lost,
which is the refused-requeue symptom and the S82 reload race. `qa` pinned the
scheduler cause in
`scheduler::tests::inmem_wait_returns_before_the_terminal_pool_so_a_requeue_waits_for_settling`.
The fix makes that state impossible to build, so the fix removed the test
(see the evidence condition below). Its replacement is
`source_pass_ready_leaves_a_terminal_pool_so_a_requeue_is_accepted`. No
product harm has been observed.

**Shape: one scheduler transition publishes both facts.** The gap is removed
in the scheduler, where it is made, rather than fenced at each session site
that might observe it (Principle 18, enforce invariants structurally).

1. A new scheduler method, `notify_source_pass_ready(module, names)`,
   replaces the pair in `worker::notify_processed_ready`. Under one
   acquisition of the lock it releases the pass's JIT reservations, sets
   in-memory completion, moves the pool to `TypecheckDone` and sweeps the
   typecheck waiters, in the order the pair runs them today. After releasing
   the lock it wakes `completion` and both worker condition variables once.
2. `notify_inmem_codegen_complete` loses its `no_remaining` argument. It
   releases one reservation and never sets in-memory completion. Two
   production paths remain:
   - the macro checkpoint (`src/process_form/macro_clause.rs`), which
     passed `false` before the change;
   - `worker::notify_processed_codegen`, which the eval thread reaches
     through `compile_and_publish_processed`. It does so from the REPL turn
     in `src/eval.rs` and the redefinition turn in `src/redefine.rs`.
     Before the change it set in-memory completion on the turn's last name,
     or on a `__empty_module` sentinel for an empty turn. Neither happens
     now, and the sentinel is gone.

   The eval-thread turns lose nothing. The rule above hands the eval thread
   only a settled module, so the flag is already set. The eval thread's own
   waits are on dependencies, which a worker pass completes
   (`register_dep_for_eval`). Nothing waits for an eval turn to set it.
   These turns were also a second way to break the invariant: a turn that
   overlapped a requeue could set the requeued module's flag while the
   module was mid-pass.
3. `ModuleState::inmem_done` loses `pub`. Only the scheduler and its child
   test module read it.

The result is an invariant: **in-memory completion implies a terminal
pool.** After the change, three places set the field, and each leaves the
module in `TypecheckDone`:

- the fused transition, which sets `TypecheckDone` in the same critical
  section;
- a completed cached-object load (`notify_inmem_codegen_batch_complete`),
  whose module was registered in `TypecheckDone`;
- the `new_cached_no_object` constructor, which builds the module in
  `TypecheckDone`.

A requeue rebuilds the module's state with in-memory completion false. From
`TypecheckDone` a module moves only to `Complete` or `Failed`. Every wait
that returns on in-memory completion therefore returns on a terminal pool:
the whole-world waits, the per-module wait and the non-blocking check.

**The hand-off sites do not change.** Registration's whole-world wait still
decides the outcome and stays the batch modes' failure report. Recovery's
wait for the entry's outcome now returns on a settled pool, so
`entry_compiled` is decided on one
([REPL lifecycle §1.3.1](repl-lifecycle.md#131-session-lock), Startup). The
empty restart keeps its two waits; the second is now satisfied on arrival.
The reload paths keep `wait_module_typecheck_settled`, which also waits out
`TypecheckBlocked`. Every run mode reaches the same scheduler transition, so
`--run`, `--link`, `--test` and the REPL do not diverge (Principle 11, single
pipeline).

**Why this is safe.** The fused transition runs the pair's existing steps
with no point between them at which another thread can take the lock.
Today's code already runs that way whenever no thread takes the lock between
the two calls, so the change adds no behaviour. It removes only the
interleavings in which the gap is visible. Dependents still see in-memory
completion before `TypecheckDone`, the order `notify_processed_ready` exists
to keep.

**Cost.** In the scheduler: one method, mostly moved from the two it fuses,
plus the argument removal and the field's visibility. In the worker: the
helper makes one call instead of N+1. Test fixtures in the scheduler, worker
and session test modules that call `notify_inmem_codegen_complete(…, true)`
to simulate a finished pass move to the fused call. `qa`'s pinning test stops
compiling, because the state it builds can no longer be constructed; the
scheduler row below replaces it. At run time a pass takes one lock
acquisition and one wake instead of N+1.

**Rejected.**

- *A settle step at each hand-off site.* The first form of this section
  defined one scheduler wait, the module's own outcome followed by
  `wait_module_typecheck_settled`, and called it at the three sites. It is
  correct at those sites, but the bare in-memory wait stays reachable from
  every other session caller: the batch drivers in `main.rs`, the test
  fixtures and any future hand-off. That form is measured at three sites
  and only asserted elsewhere (`qa`, M-2).
- *Settling inside registration on both outcomes.* On a batch failure it
  waits for an entry the exit no longer needs. A wait for a queued entry
  behind a failed dependency also risks a stall on a path that today exits
  at once.

**Evidence condition for `dev`.** Write the tests first. The fix and its tests
land in one change-set.

- **Scheduler unit row (replaces `qa`'s pinning test).** Without workers,
  register a module, claim it into `TypecheckWorking`, and call the fused
  transition. The whole-world wait returns `Ok`, the pool is
  `TypecheckDone`, and a requeue is accepted. Negative legs: a claimed module
  without the transition fails the non-blocking in-memory check and refuses
  a requeue (`wait_inmem_complete_does_not_pass_on_claimed_but_unfinished_module`
  covers the first half); `notify_inmem_codegen_complete` on a
  `TypecheckWorking` module leaves it incomplete.
- **Unconstructability observation.** With the change in place, the old
  pinning test does not compile: no scheduler call sets in-memory completion
  on a `TypecheckWorking` module. `dev` records that compile failure as the
  detection evidence, then deletes the test in the same change-set.
- **Session seam row (`lifecycle::entry_registration_tests`).** After
  `register_module` returns `Ok` for a non-empty entry, the entry's pool is
  terminal and an immediate `requeue_for_typecheck` of the entry is
  accepted. This is a reachability check that registration passes through
  the transition; it is not the guarantee.
- **Recovery row (`persistence_tests`).** Start with a failing dependency and an entry
  that compiles. After `recover_startup_failure`, the entry is terminal and
  standing as compiled.
- No e2e cell. The window is not observable end to end, and the existing
  reload and REPL suites are the regression net.

**Grade:** **structural** at every session hand-off, present and future.
Session code cannot observe in-memory completion on a non-terminal pool: no
scheduler call publishes one without the other, and module state is
reachable only under the scheduler's private lock. This meets `qa`'s
condition, because no session code can reach a bare in-memory wait: every
in-memory wait is now a settled wait. **Residual, inside the scheduler:** a
future scheduler edit that sets in-memory completion outside the three
writers above. It is asserted with a falsifier: an `inmem_done = true` or
`inmem_done: true` in `src/scheduler.rs` other than those three, or a
requeue of the entry refused after a wait on in-memory completion returned
`Ok`. `review` checks the writer census on any change-set that touches the
field.

### 6.2 Cluster orchestration

A **cluster** is the unit of typecheck atomicity: one non-`(begin)` REPL input, one
`(begin …)`, or one module file. `process_form::process_cluster_once` is the single core for
every cluster: Pass-0 structural peel, Pass-1 expansion, build, and staged `check_forms`.
`s117-conformance-recovery.md` governs its prepared-turn publication and source-ordered macro
checkpoints. The core returns done, a dependency gap, or an error. Two thin wrappers own the
wait; neither duplicates the core (Principle 11):

- **Pool worker** (`cluster::process_cluster`). On a gap the module moves to
  `TypecheckBlocked` and the worker returns to the pool. When the dependency completes, the
  scheduler requeues the module's work packet. No worker thread waits on a dependency.
- **REPL eval thread** (`eval.rs`). On a gap it records only a cycle-check edge, waits for
  that dependency (`register_dep_for_eval`), then retries. The entry module never enters
  `TypecheckBlocked`, so no pool worker can claim it (Invariant SW,
  `signature-body-prepass.md`).

`process_form/dependency.rs::drive_module_dep` is the one dependency seam for both wrappers.
It resolves the module file with the `import` rules, registers the dependency with
`delays_other = true` (§6.1) and records the edge; it never blocks. `block_for_typecheck`
and the eval cycle edge check acyclicity before recording a wait, so a mutual import is a
cycle error at the import site, not a deadlock. A cycle between modules that are already
loaded involves no wait; the publication check refuses it ([§6.11](#611-module-cycles-at-publication)).

**Concurrency invariant — share only monotonic terminal facts.** In-progress cluster state
never leaves the frame that orchestrates it:

- staging is stack-local; a gap or failure drops it and live is unchanged;
- the cluster's continuation rides the work packet (`PriorityWork::Typecheck`), kept on
  the scheduler's own `ModuleState` for requeue. It holds the forms still to process and
  the macro-head lookup dependencies recognised while expanding its already-expanded
  prefix ([lookup dependencies](#762-lookup-dependencies)); no shared map parks forms or
  suspended state;
- a retry re-derives from the packet's uncommitted continuation against committed live
  state; nothing half-checked is saved.

The only cross-thread signal is a module reaching a terminal readiness state: publish-once,
carrying no in-progress data. Keeping in-progress state off shared maps removed the cause
of the S60–S62 import/resume races (`heisenbug-race-closure.md`). Do not reintroduce a
cross-thread map of in-progress state, or a role flag that suppresses a second
orchestrator; make the second orchestrator unconstructable instead. The cost is
re-expanding the uncommitted continuation on retry, which is deterministic over committed
tables.

**Codegen batch.** `worker::derive_codegen_batch` enrols the authored definitions of the
turn and every body-bearing concrete target still lacking code — synthesised constructors,
accessors and monomorphic instances — so a constructor used as a value has a populated GOT
slot.

**Macro-turn heap ownership** — the marshal/invoke boundary inside Pass-1 expansion (`src/expander.rs::invoke_clause` + `src/marshal.rs`) follows `design/int/macro-turn-ownership.md`. The clause ABI is pinned all-Owned at clause preparation; the marshaller produces **single-owner** argument trees and **transfers** them by crossing the C ABI (nothing is protected, retained or released by int); the expansion result is an **owned** word int observes via `runtime_to_sexp` and then discharges exactly once through `cranelisp_intrinsics::consume_sexp`. A trapped or panicking invocation forfeits its one transferred argument tree. On a clause-reported runtime error, int discards the returned word without release; no bound is claimed for that residue (Rules 3–4). No marshal handle outlives its invocation frame, which keeps the protocol orthogonal to both the immediate macro publication checkpoint and its source-continuation retry.

### 6.3 Gap production

Frontend and typecheck stay pure (Principle 3): they return `ResolutionGap` values and never
call the scheduler. `process_cluster_once` is the sole place a gap becomes a scheduler
action (Principle 7). An FQ reference to an unloaded module — function, type or macro head —
auto-loads through the same `drive_module_dep` seam (`src/AGENTS.md` §"FQ auto-loading").
The gap does not distinguish a macro from a function: the retry forces only the
dependency's typecheck and codegen, and nothing is speculatively JIT-compiled.

- **Grade: asserted, with a named falsifier.** The claim rests on source order.
  In `worker::prepare_cluster_commit_with_demands`, both gap returns come before
  publication planning. Codegen runs only for a cluster that reaches `Done`,
  and a failure publishes nothing. A macro checkpoint's clause codegen is a
  publication, not a speculative compile.
- **Falsifier.** A GOT trace (`JitWrite`, [observability](observability.md))
  shows a JIT write for a gapped cluster's definition before its successful
  retry.
- **Residual.** A violation would duplicate work, not publish state. No
  end-to-end cell is allocated.

**Termination** — each gap advances dependency state monotonically, so each retry sees
strictly more committed state. The loop ends on success, a non-gap error, or a cycle error.

#### 6.3.1 Locating a gap at its reference site

Status: **implemented 2026-09-25**, with the review R1 match-rule correction.
This is int's half of S122 fresh
FQ type-only loading. Typecheck's half produces the `Type` gap
([typecheck §7.3.1](../typecheck/typecheck.md)).

- **Obligation.** When a gap cannot be satisfied by loading, int reports the
  error at the reference that raised it (spec §8.5.4 edge 3). Two cases apply:
  the module's file is missing, or a terminal module lacks the member.
- **Why int searches.** `ResolutionGap` is public and span-free, so int
  recovers the site from the cluster's built program.
- **One lookup.** Both gap-arm decisions take their location from one
  reference-site lookup (Principle 7): the missing-member error and the
  dependency drive.
  - The typed gap supplies the dependency identity. The lookup only places the
    diagnostic and never chooses what to load (Principle 24).
- **Match rule.** A reference matches when both hold:
  - its name is the gap's member;
  - its qualifier is the gap's module, either as written or after
    `cranelisp_types::substitute_module_alias` from the cluster's module.
- **Why both forms.** The gap's module has two provenances, and the gap does
  not say which one applies:
  - an absent module (every `Type` gap and the absent-module value gap) names
    the alias-substituted module (spec §8.6.6);
  - a member missing from a present module (value gaps only) names the
    qualifier as written.
  - Matching one form alone loses a reference that is located today. Before
    the `Type` producer, an alias-spelled type reference to a missing module
    was a located type error, and a spelling match leaves it unlocated. The
    spelling search that preceded this lookup located `z/f` when `z` is an
    alias of a loaded module that lacks `f`, and a substituted-only match
    loses that.
  - A qualifier whose written form names one module and whose substituted
    form names another needs an alias named like a module. Where that happens
    and the cluster writes both spellings, the location may fall on the other
    reference to the same member. Only the location is affected.
- **Positions.** The lookup searches every reference position for every gap
  kind, in program order. It has no per-kind branch; any match is a reference
  to the same qualified name.
  - Variable references in expressions, including defn and impl method bodies.
  - Type positions that typecheck resolves:
    - defn and lambda parameter annotations;
    - inline annotations;
    - `deftype` fields;
    - trait method signatures, including their still-unclassified tail;
    - an impl's target type.
  - Trait references are excluded: bounds, an impl's trait and constraints.
    They raise no gap.
- **Span.** A type expression carries no span, so a type match reports the
  innermost spanned node containing it. That node is the field, defn variant,
  lambda, annotation, method signature or impl. A symbol in a signature tail
  reports its own span.
  - That node is at or inside the form that typecheck located before the gap
    existed.
  - The rejection keeps a real location. It takes the load-failure text that
    value references already produce.
- **Fallback.** `Span::SYNTHETIC` remains the fallback when nothing matches,
  for example when only a macro synthesised the reference.
- **Unchanged:**
  - public API, carriers, schema and the `ResolutionGap` variants;
  - the expand-time module-prefix lookup for an FQ macro head.

**Rejected:**

- *Carry the span in the gap.* This would locate every gap exactly, but it
  changes the public `ResolutionGap` surface. That change is user-gated and
  outside this correction.
- *A separate type-only lookup.* It would duplicate the match rule.

**Grade: asserted, with a named falsifier.** FT-4
([evidence delta](../../tests/plan/s122-evidence-delta.md#fresh-fq-type-only-loading--evidence-delta-2026-09-25))
renders `at 0..0` for `(defn h [:zz/T t] :Int 7)` when there is no `zz.cl`.
Row 5 below falsifies the match rule's written-qualifier leg.
The lookup re-derives what the producer recorded (Principle 24), so a new
producer arm whose module takes a third form is caught only by a failing row.
Nothing structurally forces a newly added type position into the lookup; the
unit rows pin each carrier.

**Residual (unexecuted; `qa`).** A `Type` gap reaches the member-absent arm
only when its module becomes terminal between typecheck's miss and int's
check, which needs a concurrent load. Int would then report "no member" for a
type that may exist. Value gaps raised for an absent module share this window.
Falsifier: two modules that load concurrently, where one names the other's
type and loads it.

**Unit rows,** in
`src/process_form/tests.rs` beside
`find_named_var_span_in_toplevel_recurses_defn_body`:

1. A defn parameter annotation `:zz/T` locates at its defn variant for a
   `Type(zz/T)` gap. This is FT-4's seam.
2. A `deftype` field `:zz/T` locates at the field.
3. With the alias `z → zz` registered for the referring module, `:z/T`
   locates for `Type(zz/T)`, and a value reference `z/f` locates for a value
   gap on `zz/f`.
4. Negative:
   - without that alias, `:z/T` does not match `Type(zz/T)`;
   - `:zz/U` does not match `Type(zz/T)`.
5. With the alias `z → zz` registered for the referring module, a value
   reference `z/f` in `(z/f 1)` locates at its var span for the value gap on
   `z/f`. This is the member-absent gap, whose module is the written qualifier.

Every row and the existing variable-search rows are GREEN; FT-4 is GREEN on every leg.

### 6.4 `notify_*` cadence

Per Decision 30 reframed by Decision 38 — scheduler notifications are *ordering* primitives (parallel macro-dep compilation, phased completion), not lock-safety primitives. Workers call:

- `notify_typecheck_done(module)` after the last form in a module finishes.
- `register_module_cached(module)` for a cache hit (Decision 37): the module is typecheck-done at once, and its `LoadObject` becomes claimable only when the restore releases it (§7.1).
- `notify_inmem_codegen_complete(fq)` after JIT finalize writes the GOT slot.
- `notify_inmem_codegen_batch_complete(module)` after `LoadObject` populates all GOT slots from cache.
- `notify_object_codegen_complete(module)` after nice-worker `.o` write completes.

The scheduler maps these to readiness states; waiters unblock when the corresponding state is reached. Dependency registration has one home, `drive_module_dep`, reached from the one cluster core by both wrappers (§6.2).

### 6.5 Entry module and the implicit prelude

- **The entry module is ordinary** (Principle 19). `"user"` is only the default CLI name; no
  orchestration path keys on a module name.
- **Its role is session data.** `CompilerSession.entry_module` names it. The REPL cursor
  starts there and a bare `/mod` returns there (`repl/spec/03-slash-commands.md` §3.9).
- **One orchestrator per module**: the REPL eval thread for the entry module, the pool for
  every other module ([cluster orchestration](#62-cluster-orchestration); Invariant SW).
- **The implicit prelude is resolved, never copied.**
  [The prelude convergence ruling](../arch/prelude-import-convergence.md) owns the
  [model](../arch/prelude-import-convergence.md#1-the-settled-model-spec-grounded-not-open)
  and the
  [per-module bit](../arch/prelude-import-convergence.md#34-fate-of-the-prelude_fallback-bit).
  int's obligations:
  - `SharedState.prelude_fallback` holds the bit session-side and never caches it. Absence
    means OFF; the prelude module and any module that names the prelude in an import stay OFF.
  - The prelude is loaded like any dependency. Its names are never installed into a module's
    table, and they carry the same §8.6.4 conflict and §8.6.5 ambiguity rules as an explicit
    import (spec §8.8.1).
  - A module whose bit is ON depends on the prelude in every graph int checks or orders by,
    and a null import of the prelude is no edge ([§6.12](#612-the-implicit-prelude-dependency)).
  - A prelude restored from cache establishes the same fallback as a fresh load
    ([restoration parity](#75-restoration-parity)).
    `tests/cache.rs::cache_repl_minimal_plain_fn_prelude_restored_on_session_2`
    guards the REPL second-session shape.
  - Only public prelude bindings are reachable as bare names.
  - `/imports` lists prelude-provided names in a separate `Prelude (implicit)` group when
    the bit is ON.
  - `SymbolTable.imports` records only user-authored `(import …)` forms. The implicit
    prelude import is never recorded there, because source regeneration writes what the
    user wrote. Its resolved effect is the fallback bit, not name candidates.
    `writer_does_not_record_implicit_prelude_in_imports` pins this. A whole-file rebuild
    starts the record empty and resets the bit ([§6.10](#610-the-import-generation)).

### 6.6 Pass-1 quote shield

Pass-1 expansion runs before the frontend fold desugars quotation, so without a
shield a macro-call-shaped list inside quoted data — `(defn f [] '(m x))` — would be
expanded and silently change a runtime value. `expand_scoped` therefore handles the
reader-quote family before binding-form or macro-head recognition:

- **Quote:** `(quote X)` is returned verbatim, with no descent.
- **Quasiquote:** the template is walked at depth 0 and held verbatim except the body
  of a live `unquote`/`unquote-splicing`, which is an ordinary expression position and
  re-enters `expand_scoped`. A nested `quasiquote` raises the depth; an
  `unquote`/`unquote-splicing` under it lowers the depth and stays shielded.
- **Quote under a quasiquote is not a boundary.** Inside a quasiquote template a
  `(quote …)` is an ordinary list, so `` `(quote ~x) `` still expands `~x`. This
  matches the fold.
- **Recognition is structural and shared.** Every walk classifies the family through
  `cranelisp_types::quote_head`, the fold's own test, and consults neither lexical
  shadows nor the macro resolver. The qualify walk carries the same shield
  (`expansion-qualification-scope.md` §2.4). A second classifier or a different depth
  rule would let shield and fold disagree, double-desugaring or expanding a subtree.
- The shield raises no quotation diagnostic; the fold owns them, including
  unquote-splicing at the top level of a template. The macro expansion-depth limit
  still applies inside a live unquote.

The interaction rows, including nested-depth agreement, are in
`tests/spec_09_macros.rs`.

### 6.7 Public candidate exposure — the export-closure gate

A module never accepts a public cross-module name candidate outside its declared export
closure `D(M)` (safety register R7).

- **One gate.** `imports::check_exposed_candidate_closure` admits a candidate that is
  private, whose canonical source is the destination module, whose local name is in
  `D(M)`, or whose `D(M)` is not yet recorded. It rejects any other public
  cross-module candidate. The rejection is a diagnosed internal-invariant error in every
  build, naming the module, name and source edge; it never aborts the session.
- **Why the destination's declared exports.** A provider-existence test cannot see the
  historical phantom: `primitives/bit-and` is a genuine public primitive, so a phantom
  `bit-and → primitives/bit-and` in `prelude` names a real provider. What makes it
  invalid is that `prelude` never declared `bit-and` (Principle 26).
- **`D(M)`** is recorded from `M`'s own `(export …)` specs into
  `SharedState.declared_exports`. It is session-side, unserialized and separate from
  `symbol_tables`, so reading it never re-enters a shard held by a write guard. Every
  route reads `D(M)` before taking the destination's write guard.
- **Routes.** Import installation, export installation, prepared publication and staged
  publication validate the complete candidate batch before mutating the table or
  publishing a GOT change. One rejected candidate rejects the batch.
- **Bindings are not closure-checked.** A module's own definitions are exported by
  `spec/08-modules.md` §8.4; cross-module exposure exists only as a name candidate.
- **Session-initialization seams are named legal skips**: synthetic-module bootstrap, the
  `PRIMITIVES_TABLE` mount and platform-DLL registration. They run before any worker
  exists or install only canonical own definitions. Bootstrap's skip is proven:
  `bootstrap_public_candidate_exposures_are_self_aliases_or_private` sweeps every seeded
  candidate through the gate under an empty `D(M)` and plants a forbidden candidate that
  must reject. Bootstrap's four `macros` edges to `primitives` are private, not public
  re-exports.
- **Candidate coexistence is not this gate's concern.** Importing distinct canonical
  sources is permitted; typecheck selects among candidates at the use site.

Evidence limit: the writer that produced the S109–S114 phantom was never identified,
and the phantom has not been re-induced since the gate landed. The gate converts any
recurrence into a located diagnostic; `tests/index_race_foreground_0604.rs` is a
no-regression sweep, not attribution. A firing is a `dev`(src) defect routed through
`qa` for attribution. The unit cells are listed on the R7 row of
`design/arch/safety-invariants.md`.

### 6.8 Pass-1 macro recognition and execution

[Macro expansion ownership](../arch/macro-expansion-ownership.md) splits
recognition from execution; the
[availability model](../arch/macro-availability-model.md) decides when a macro
exists. Within those, int's expand walk (`expander::expand_sexp_recursive`,
driven by `process_form/macro_resolution.rs::try_expand_sexp`) keeps these rules:

- **Two recognisers, one query.** The cluster walk uses
  `SymbolTableMacroResolver`; `/expand` uses `ReadOnlyMacroResolver`. Both
  recognise only through `ResolutionScope::resolve_macro_head` over committed
  tables and the session's prelude-fallback bit. Neither walks import chains,
  aliases or visibility itself.
- **One executor, keyed by the canonical home.** `JitMacroExpander` reads a
  clause's code from the GOT slot of the macro's home module. No per-caller macro
  map exists. Such a map would duplicate that fact and could key it by the
  calling module, not the home.
- **Recognition never compiles from source.** A macro's clauses compile when its
  checkpoint publishes (`s117-conformance-recovery.md` §2.1). The cluster
  recogniser has one side effect: when the home module was restored from cache
  and its object is not yet loaded, it asks the scheduler for that load's
  claim ([one load entry](#71-cache-hit-flow-inside-register_module)). It runs
  the load when it holds the claim. While the load is held or claimed
  elsewhere it waits and asks again, and it proceeds once the object is
  loaded or the module has failed. `/expand` has no side effect. If a recognised clause is still not in memory,
  execution fails with an aborted-expansion diagnostic. It is never skipped
  silently.
- **Borrow scope.** The recogniser borrows only the committed tables and the
  resolution scope. It drops before the expanded form is built and checked, and
  never holds check state or staging.
- **Unloaded qualified head.** A `mod/macro` head whose module is not loaded
  aborts the walk as blocked. The cluster core turns that into a dependency gap
  through `drive_module_dep` (§6.3) and commits no partial expansion. A
  `:`-prefixed symbol is a type annotation, never a macro head or load candidate.
- **Hygiene.** Recognition records each foreign defining module. Post-expansion
  qualification then uses them (`expansion-qualification-scope.md`).
- **Lookup-dependency producer.** When the cluster recogniser recognises a
  qualified head as a macro, it adds the head's module after alias substitution
  to the attempt's lookup dependencies. That is the module whose table answered,
  and the recogniser already computes it for the unloaded-head check. A bare head,
  an unrecognised head, a blocked head and `/expand` record nothing
  ([lookup dependencies](#762-lookup-dependencies)).

### 6.9 Bare module names in `import` and `export`

Status: **implemented, independently reviewed and QA-adequate 2026-09-27.**
All six end-to-end legs pass in the final workspace run; the adjacent cache
crash replay passed 800 sessions. Private to `src/`.

**Rule.** Inside module `M`, a bare (undotted) module name in an `import` or
`export` spec names `M.name` exactly when `M` declares `(mod name)` or
`(mod- name)`. Otherwise it names the absolute module `name`, found by the
root-then-lib search. Every int stage that reads the spec reaches the same
module (spec §8.11.2 item 1, §8.11.2.1; §8.5.4 edge 2 forbids inventing a
child). A dotted spelling is always absolute.

**Corrected defect (IR-1).** Neither former stage applied the rule:

- *Discovery* (`handle_import`, `handle_export`) took `M.name` when any module
  had registered it or a file backed it.
- *Installation* (`install_imports`, `install_exports`) took `name` when that
  table existed, else `M.name`.
- The other readers read the spelling as absolute:
  - the static import closure;
  - the restore walk;
  - the import-alias writer's target;
  - the dependency record;
  - the watcher.
- **Observed:** in
  `tests/spec_08_modules.rs::import_and_export_of_undeclared_file_backed_child_resolve_to_root_module`,
  both undeclared subjects bound `a.q`; all four legs now pass.
- **Module evidence:** pre-fix rows observed a raw-spelling alias target and
  a false cycle through root `q`. The installer rows detected a planted
  as-is-first fallback. The final test visit adds the root-first and alias
  end-to-end legs; their pre-fix end-to-end outcomes remain unobserved.

**One resolver.** A crate-private pure function in `src/imports.rs` takes
three inputs:

- the referring module;
- that module's declared child names;
- the written spelling.

It returns `M.name` for a declared bare name inside a non-root module, and the
spelling unchanged otherwise. The child path is the one `<parent>.<name>` that
declared-child enrollment derives. The resolver has no symbol-table,
filesystem or load-state input. A registered or file-backed undeclared child
therefore cannot capture a name (Principle 24).

The as-built private type is `imports::DeclaredChildren`; its `resolve`
method performs that pure resolution. `ResolvedSpec` pairs the written spec
with its resolved module, and only the resolver constructs that pair.
Installers accept the pair rather than a raw spec.

**Declared children come from settled state (Principle 26).**

- **A cluster:** the `mod` forms among the cluster's own forms, together with
  the declarations already recorded on the module's table from earlier REPL
  turns. The set is computed once per pass, before the static closure and Pass
  0. `(import [q …])` written before `(mod q)` therefore resolves as it does
  after it.
- **A module walked from its file** (the static closure's transitive walk):
  the `mod` forms of its parsed file.
- **A settled table:** its recorded `submodules`.

**Resolve once per pass.** Pass 0 resolves each spec once. That module then
feeds the private-submodule check, the fast path, the load, and installation.
The installer takes each spec paired with its resolved module and does no
module-path resolution. A missing table for that module is a hard error that
names it. The import-alias writer records the resolved module as its target.

| Stage | Consumer | Declared children from |
|---|---|---|
| Dependency discovery | `handle_import` (including the alias-only path) and `handle_export` | The cluster |
| Signature barrier and cycle check | `static_import_closure` and its transitive walk | The cluster for the root; each walked module's parsed file |
| Installation | `install_imports`, `install_exports` and the import-alias writer | Pass 0's resolved module |
| Restore ([restoration parity](#75-restoration-parity)) | The import and re-export walk; the alias rebuild in `install_module_session_env` | The restored table |
| Settled-table readers | Dependency-record edges ([§7.6](#76-dependency-record-and-validity)); the watcher's dependent closure and reload ordering in `session_v4/lifecycle.rs` | The table |
| Background index | The installer in `session_v4/index_worker.rs` | The parsed declarations |

The restore walk's `register_transitive_cached_imports` is private to its
module; no external caller requires its former parent-module visibility.

**Unchanged:**

- `ImportSpec`, `ExportSpec` and the persisted spelling, so source
  regeneration still writes what the user wrote;
- the cache schema;
- `super` rewriting;
- qualified-name resolution through `(mod q)`'s alias (R1-V, typecheck);
- the private-submodule rule.

**Behaviour changes:**

- A declared child whose file is missing now fails at the import, naming
  `M.name`. Before, the import could silently bind root `name` until
  enrollment failed. Both outcomes are §8.2.5 compile errors.
- An import of a declared child loads it before `drive_submodules` does, as
  today. Enrollment then finds it loaded.
- Suppose a parent imports its declared child, and the child imports `super`.
  The static closure now reports the cycle before any load. Today
  `block_for_typecheck` reports the same cycle when the child waits on the
  parent. The error class is unchanged, but its location may differ; spec
  §8.3.8 permits the rejection.
- **Census, 2026-09-27.** No `.cl` source under `stdlib/`, `exemplar/`,
  `examples/`, `repl/`, `user/` or `platforms/` imports or exports an
  undeclared file-backed child. The four bare child references, in
  `stdlib/core.cl` and `stdlib/seq.cl`, are all declared. A heuristic scan of
  the fixtures in `tests/*.rs` found only lib-directory modules and the
  declared-child cells. The full suite remains the census of record.

**Rejected:**

- *Read the declarations from the module-alias map.* The alias is written
  only when Pass 0 reaches the `mod` form, so the answer would depend on form
  order. The map also holds import aliases.
- *Keep file probing and add a declaration test.* The resolver would keep two
  inputs, and a stage could consult the wrong one.
- *Persist the resolved module on the spec.* This is the complete form of
  Principle 24. It changes the types-owned public spec and the cache schema,
  which is user-gated, and IR-1 does not need it. Potential extension. Trigger:
  a reader that needs the identity but lacks the module's declarations.

**Assurance.**

- *Structural:*
  - the resolver cannot consult load state or files;
  - the installer receives the resolved module and cannot re-resolve it.
- *Measured:* the IR-1 cell's four legs and the unit rows below.
- *Asserted, with named falsifiers:*
  - Every reader of a spec's module identity uses the resolver. Falsifier: an
    int reader in `src/` that uses a spec's `module_path` as a module key
    without going through the resolver (a review check).
  - The watcher readers have no row. Falsifier: `a` declares `(mod q)` and
    imports `[q …]`, and an edit to `a/q.cl` fails to reload `a`, or an edit to
    root `q.cl` reloads it.

**Residuals (for `qa` intake; not designed here):**

- *`super` capture.* The frontend rewrites `super` to the parent's path, which
  is bare for a top-level parent. A child that declares a submodule named like
  its parent would capture it. Today any file-backed child captures it; this
  correction narrows the case. Falsifier: `a.q` declares `(mod a)` and imports
  `[super [x]]`.
- *Prelude test by spelling.* The fallback-bit test treats `(import [prelude
  …])` as naming the prelude even where `M` declares `(mod prelude)`.
- *REPL turn order.* A turn that imports root `q` keeps that binding after a
  later turn declares `(mod q)`. Whether §8.11.2.1's uniformity spans REPL
  turns and how persistence preserves the outcome are deferred by the user
  to the next increment under [ACT-0995](../../sprints/actions/ACT-0995-repl-later-submodule-declaration-resolution.md).
  No behavior was selected. Within one cluster, form order does not change
  the chosen module. Loading an inline child body remains a separate lead:
  an import before its inline `mod` can reach the child before its backing
  file is written. This is unobserved; its falsifier is that ordering in a
  fresh project. QA routes it to design(int), without selecting a remedy.
- *Stale declarations.* The resolver inherits the lifetime of the recorded
  declarations, like enrollment. A reload that keeps a removed `(mod q)`
  affects both the same way.
- *Pre-fix caches.* A cache written before the fix may hold a wrong binding.
  Its shape is unchanged, and a committed build's `BUILD_ID` separates the
  two, so no schema bump is needed (§7.3). An uncommitted build shares the
  prior `BUILD_ID`. E2e cells use fresh projects.

**Unit rows (`dev`).** Arm each row RED against the pre-fix source where its
seam exists. Arm the resolver rows by planting file-backed capture.

1. `src/imports/tests.rs`, the resolver:
   - a declared `(mod q)` gives `M.q`;
   - a declared `(mod- q)` gives `M.q`;
   - an undeclared name gives `q`;
   - `q.r`, whose first segment is declared, is unchanged;
   - a root-level referring module leaves the name unchanged.
2. `src/imports/tests.rs`, the installers. Tables for both `q` and `a.q` exist:
   - a spec resolved to `a.q` installs from `a.q`;
   - a spec resolved to `q` installs from `q`;
   - an import alias records the resolved target;
   - a resolved module with no table errors, naming it.

   These rows replace
   `install_imports_resolves_bare_submodule_current_module_relative` and
   `install_imports_bare_name_without_submodule_errors`.
3. `src/process_form/dependency.rs`. Retire `current_module_relative_tests`:
   its registered-child and file-backed rows assert the defect. Add cluster
   rows:
   - `(import [q …])` before `(mod q)` in one cluster resolves to the child;
   - a declaration recorded by an earlier turn does the same;
   - with neither, the name resolves to root `q` even when `a/q.cl` exists.
4. The static closure, over a temporary project:
   - with `(mod q)`, the closure names `a.q`, and a root `q.cl` importing `a`
     is no cycle;
   - without it, the same files report the cycle.
5. `install_module_session_env`: a restored table with `(mod q)` and
   `(import [(q qq) []])` maps `qq` to `a.q`; without the declaration, `qq`
   maps to `q`.
6. The dependency-record edges: a declared child adds no root `q` edge; an
   undeclared `q` adds one.

### 6.10 The import generation

REPL §14.2 steps 2–3 require a successful reload to clear the module's
previous state and recompile it from the saved source; §15.1 requires the
regenerated file to reproduce that state. An `import` the saved source omits
therefore leaves scope, `/imports` and the regenerated file
([ACT-1012](../../tests/plan/s122-evidence-delta.md#act-1012--omitted-import-kept-closed)).

One `(import …)` form has three int-written carriers in the importing module:

| Carrier | Readers |
|---|---|
| `SymbolTable.imports`, the authored-form record | regeneration (`save.rs`), the cache dependency record, reload selection and order, restore-time session env, test-module selection |
| Private name candidates whose source is another module | bare resolution in typecheck and introspection, `/imports` (`explicit_import_sources`) |
| Import-alias keys `<module>.<alias>` in `SharedState.module_aliases` | qualified resolution through an alias |

**Rule.** A whole-file rebuild replaces all three with the saved source's
generation
([session transaction §7.3.1](session-transaction.md#731-the-whole-file-rebuild)):

- the fresh table starts with an empty record and no candidates, and Pass 0
  installs and records each import form as on a first registration;
- the rebuild prologue removes the displaced generation's import-alias and
  submodule-alias keys through `module_alias_key`, the key mint the installer
  uses, so the two cannot disagree;
- the prologue also resets the prelude-fallback bit, so the `Replace`
  prologue's fresh recompute is exact: a newly added explicit prelude import
  leaves the bit off.

An increment keeps today's rule: Pass 0 appends a form after it resolves
(FIXME 0548). A REPL-typed import therefore persists, and a later rebuild
keeps it exactly when the saved file still declares it. The `export`, `mod`
and `platform` records are rebuilt the same way.

**Consequences.**

- A body that still names an omitted import fails as an unresolved name, and
  the module stands failed, which locks the session.
- A failed rebuild's record holds only the forms Pass 0 resolved. Its cascade
  edges come from its established reference instead
  ([session transaction §7.3.2](session-transaction.md#732-the-established-reference)),
  so a save of the module whose import made it fail still reaches it. FL-3
  (`watch_cascade_failed_importer_locked_until_import_is_fixed`) is the
  end-to-end guard.
- Nothing that persists or evaluates reads a failed module's partial
  generation: regeneration returns early and code turns are refused while
  the session is locked, and a failed module never reaches `TypecheckDone`,
  so no cache entry is written for it.

**Evidence.** The Prologue, Prelude bit, Increments and Unresolved omission
rows of [session transaction §7.3.4](session-transaction.md#734-module-tests-dev);
end to end, C2 and its C3 control, RM-5's regeneration leg and FL-3.

**Outside this section.** A failed REPL-turn import can leave its alias key
installed without a record. This is an unverified lead.

### 6.11 Module cycles at publication

Status:

- the publication check (ACT-1013), its macro-checkpoint site and the prelude
  edge are built;
- the Pass-0 fail-fast (ACT-1014's helper end) is built; QA closed ACT-1014
  ([helper-end adequacy](../../tests/plan/s122-evidence-delta.md#act-1014-helper-end--final-adequacy-2026-09-30));
- the failed-dependency refusal (ACT-1016 Face 1) is built at `f95f0a3a` for
  a whole-file rebuild; a fresh load is not covered (*Failed dependency*
  below);
- the declaration readiness gate (ACT-1016 Face 2) is built at `870aacd8`;
- route independence through a declared child (ACT-1081) is designed and
  not built; its error clause waits on the user's ruling.

Private to `src/`; no public API, carrier, schema or ABI change.

**Rule.** A module dependency cycle is a compile-time error naming its path
(spec §8.10.2; §8.5.4 edge 6 for a qualified reference). The published
module graph stays acyclic: a cluster whose new generation would close a
cycle is refused before it publishes.

**Why a check at publication.** The two existing checks see only loading:

- the scheduler's wait graph sees a module wait for a dependency that is not
  yet terminal (§6.2);
- the static import-closure gate reads the `import` declarations of files
  (§6.9).

A qualified reference to a module already loaded resolves without a wait. A
save or a REPL turn that closes a cycle between loaded modules was therefore
accepted. Probed on 2026-09-29 at `e4062202`: the reload face of ACT-1013,
and an increment face, `/mod a` then `(defn h [] (b/g))` while `b` calls
`a/f`, which is accepted and written to `a.cl`. An `import` that closes a
cycle on reload is already rejected by the gate.

**Where.** The commit-planning step of the ordinary prepared publication
(`worker::plan_staging_commit_inner`), which a prepared cluster
(`prepare_cluster_commit_with_demands`) and a macro checkpoint
(`macro_clause::compile_macro_checkpoint`) both reach before codegen and
publication. Eval turns, pool clusters, whole-file rebuilds and macro
checkpoints therefore share one site in every mode (Principle 11; review
reject 11 already forbids a macro-specific publication writer). A refusal is
an ordinary prepare error: a REPL turn is rejected with the session unchanged,
a pool cluster fails its module, and a rebuild fails and locks it.

- **Why the checkpoint.** A macro clause publishes at its checkpoint, before
  any cluster of its attempt prepares. A check only at cluster prepare let a
  REPL `defmacro` turn, which has no later cluster, publish a clause that
  closes a cycle and write it to the file (ACT-1013, macro face).
- **Inputs at both callers.** The staged table, whose macro clauses carry
  their callee edges; the owed lookup dependencies (a cluster's owed facts; a
  checkpoint's clause-body and macro-head dependencies), seen by the check
  whether they are passed or recorded on the staging first; the later members
  of the attempt's whole-source provenance, threaded to the checkpoint from
  the expansion pass that holds it; and the checked program, for the refusal's
  location.

**The check** for module `M`:

- **New edges.** The edges of the staged table and the cluster's owed lookup
  dependencies, together with `M`'s live-table edges. The live table holds
  the Pass-0 imports and exports of this attempt, macro clauses published at
  its checkpoints, and, for an increment, the earlier generations still live.
- **Settled graph.** Every other module's live-table edges. Selection,
  ordering and this check read one edge predicate, from one crate-private
  home: imports that load and exports, through declared children; the
  prelude when the module's fallback bit is on
  ([§6.12](#612-the-implicit-prelude-dependency)); and recorded edges
  ([REPL lifecycle §1.2](repl-lifecycle.md#12-poll-and-reload)). Established
  references and failure dependencies are not read: they describe past or
  failed generations and serve selection only.
- **Unsettled members.** A whole-file rebuild's provenance carries, beside
  its established reference, the modules its plan pass rebuilds after `M`.
  The walk skips them, because their live tables still hold the pre-plan
  generation. An increment and a fresh load carry none.
- **Failed dependency** (ACT-1016 Face 1). For a whole-file rebuild, a
  new-edge target that stands `Failed` refuses the cluster before the walk.
  Two kinds of target are exempt: an unsettled member, and the prelude
  reached only through the fallback bit.
  - *As built (`f95f0a3a`).* The check runs for `WholeSource` provenance,
    which only a rebuild carries; a first registration at a fresh load is
    `Increment` provenance and is not checked. At a fresh load a dependency
    wait fails fast on a failed module, so the gap is a module whose
    qualified reference resolves, with no wait, against a name a failed
    module's table still holds (a Pass-0 re-export). Such a module compiles
    at a restart and is refused by a session rebuild. *Falsifier:* `qa`
    reproduces that disagreement. *Trigger and remedy:* the same check runs
    for a first registration, which needs the provenance to tell a first
    registration from a REPL turn.
  - The error is that module's own error, as the scheduler's fail-fast sites
    return it (spec §8.5.4 item 5). It records the module as `M`'s failure
    dependency.
  - Resolution does not catch this. A qualified name resolves against the
    failed module's table, which keeps its failed attempt's Pass-0
    declarations. Without the refusal, a member that a follow-on rebuilt after
    a refused cycle member compiled against that member's failed table,
    although a restart fails it. QA measured this with `a` and `b` on a
    qualified cycle (2026-09-30, `.local/s122-helper-followon-qa-scratch/`).
  - An unsettled member's standing is pre-plan, so it is skipped here as in
    the walk. Otherwise a module saved together with the repair of its failed
    dependency would be refused before that repair runs.
  - The prelude edge is exempt because a module does not wait on the prelude
    at a fresh load (§6.12). A restart therefore compiles a module with the
    bit on beside a failed prelude when it names no prelude name, and the
    session must end the same way (ACT-1014).
  - An increment is exempt. Its live table holds earlier generations, whose
    edges were checked when they published. An increment runs only while
    the session is unlocked, when no module stands failed or waits
    ([REPL lifecycle §1.3.1](repl-lifecycle.md#131-session-lock)), so those
    edges reach no failed module.
- **Refusal.** A path from a new-edge target back to `M` refuses the cluster
  with `circular dependency detected: M -> X -> … -> M`, rendered by
  `scheduler::CycleError::render`, the format every cycle diagnostic shares.
  It is located at the cluster's first reference to `X` when one is found,
  otherwise at the cluster head. It records `X` as `M`'s failure dependency
  ([REPL lifecycle §1.2.1](repl-lifecycle.md#121-failure-dependencies)).

**Pass-0 fail-fast on a failed module** (ACT-1014's helper end).

- **Rule.** Pass 0's `import` or `export` of a module that has a table and
  stands `Failed` fails the attempt with that module's error, and records the
  module as a failure dependency. It does not resolve names against the
  failed table. This is the scheduler's existing fail-fast, which a qualified
  reference to a name missing from that module already reaches.
- **Why.** Today both Pass-0 handlers install from any present table. A
  follow-on that rebuilds the prelude against `x`'s refused generation
  therefore reports `(export [x [one]])` as `'one' not found in module 'x'`.
  That is the save's only prelude notice, so the cycle is never named
  (spec §8.10.2; QA's attribution in ACT-1014). The fail-fast carries `x`'s
  own refusal, `x -> prelude -> x`.
- **Scope.** It applies in every mode and to an increment, because the
  declarations are the attempt's own forms.
  - For an `import`, and for a declaration of a name the failed table lacks,
    the outcome does not change; the message and its location do (see
    *Diagnostic*). Such an attempt already failed, at the
    signature barrier or on the unresolved name.
  - An `export` of a name the failed table still holds is newly refused. The
    barrier's members exclude export targets, and spec §8.10.3 compiles a
    dependent only after its dependency is fully processed.
  - Like the qualified fail-fast, it does not consult unsettled members. The
    error may therefore come from a later member's earlier attempt.
- **Not covered by this rule:** an `import` or `export` of a module that is
  still in flight at a fresh load (ACT-1016 Face 2). That module is not
  `Failed`; the declaration readiness gate below answers it.

**Declaration readiness** (ACT-1016 Face 2; built at `870aacd8`).

*The fault.* Neither Pass-0 handler waits on a module in flight. The export
handler installs from any present table. The import handler's own fast path
requires a terminal typecheck, but a non-terminal module with a table falls
through to `try_cache_hit_load`, whose guard answers "satisfied" for any
present table, and the import installs from it. A module in flight holds a
seeded table without its definitions, so on Face 2's fixture `a`'s
`(export [b [g]])` reports `'g' not found in module 'b'` while `b` waits on
`a`. Requiring a terminal typecheck in both handlers is not the fix: a parent
whose generation has published is still non-terminal while it drives its
declared children, so every child's `(import [super …])` then waits on a
parent that waits on it, and a legal program is refused as a cycle
(`superp.test -> superp -> superp.test`; measured by `dev` on `f95f0a3a`).

*What the spec makes legal* (spec §8.3.8, §8.4.0, §8.5.4, §8.10):

| Program | Spec reading | Outcome |
|---|---|---|
| A child imports or exports names of its parent (`super`, or the parent's full path), and the parent reaches the child only by declaring it | §8.3.8: a one-directional child → parent import is supported; `super` only names the parent. §8.4.0: an export is the same operation as an import | accepted in every mode |
| As above, and the parent also reaches the child through an import, an export or a qualified reference (`p.child/x`) | §8.3.8's mutual configuration; a qualified reference is an edge at parity with an import (§8.5.4 item 6). §8.10.2 requires the error | a circular-dependency error naming the path |
| Two modules that are not parent and child, each reaching the other through an import, an export or a qualified reference | §8.10.1 puts `export` in the graph; §8.10.2 and §8.5.4 item 6 require the path, never an unresolved name | a circular-dependency error naming the path |

QA's ACT-1016 record reads the middle row the same way.

*The predicate.* A Pass-0 `import` or `export` of module `D` installs from
`D`'s table exactly when `D` is **ready for declaration**: its typecheck is
terminal, or its current generation has **published**. Otherwise, when `D`
has a table, the declaration waits on `D` through the ordinary dependency
edge (`block_dep`), whose acyclicity check names any cycle; when `D` has no
table it loads as today. `refuse_failed_table` still runs first.

- **The published fact.** The scheduler records, per module, that its current
  generation has published. It is set at the one site where a whole cluster's
  outcome is `Done` and published, in `finish_pass2`, before
  `drive_submodules` drives any declared child; both the worker and the eval
  entry pass through it (Principle 11). A macro checkpoint does not set it:
  a checkpoint publishes clauses, not the generation. Every new whole-source
  attempt of the module starts with the fact off: a registration, a rebuild's
  reset and a failure reset.
- **One home.** The predicate is a scheduler query read under the same lock
  as the terminal-pool test. Both Pass-0 handlers read it, and so does the
  tracked branch of the qualified-reference gate (`fq_module_is_loaded`),
  whose own documentation says it mirrors the import gate (Principle 7). The
  signature barrier reads it for a member that shares a cycle with the
  waiter (*Route independence* below); every other terminal-typecheck reader
  keeps the terminal predicate.
- **Publication wakes the declaration waiters.** When the fact is set, the
  scheduler releases every module waiting on `D` through a whole-module
  dependency edge, as the terminal sweep does. The eval thread's wait at a
  turn's dependency gap ends on it too. A released waiter retries from the
  top, idempotently, and its declaration now installs. Without this, a reader
  that arrived before `D` published would keep its edge to `D` while `D`
  waits on its children, and whether a cycle is reported would depend on
  arrival order.
- **`/mod` is not a declaration read.** `/mod`'s load of `D` waits until
  `D`'s in-memory code is complete, not until it publishes
  ([§8.5.1](#851-mod-target), step 4). The switch makes `D` the module the
  session's turns publish into. At publication a pool worker still drives
  `D`'s attempt through its declared children to its terminal typecheck, so
  a turn in `D` then would be a second writer of a module the pool is
  driving, which Invariant SW
  ([signature-body prepass](signature-body-prepass.md#invariant-sw--single-writer-single-orchestrator-per-module))
  forbids. A declaration or a qualified
  reference only reads `D`'s table, which publication has completed.
- **Why a published table is a complete read** (spec §8.5.4 item 7). After
  publication the only work left in `D`'s attempt is driving its declared
  children. Every name `D` declares, defines or re-exports is in its live
  table, which is what a terminal read sees of `D`. A child's later
  publication writes only that child's own records into `D`'s table, such as
  an implementation of `D`'s trait, and a reader reads those at typecheck
  as it reads any module's.
- **`try_cache_hit_load`'s guard is unchanged.** The handlers no longer reach
  it with a table. Its other callers keep its answer: a parent's drive of a
  child already in flight, which must not wait, and the prelude injection,
  which never waits (§6.12).
- **Not changed.** The signature barrier's members still exclude export
  targets (§6.12, *Not taken*). The wait is the body-free dependency wait an
  import already takes. Declared children are no edge in any graph that
  decides a cycle (§6.9) until the ruling below; the barrier reads them only
  for reach (*Route independence*).

*Effect.* An export to a module in flight becomes a wait edge. At a fresh
load the scheduler therefore reports `a -> b -> a` before either module
installs from the other, which makes the §6.12 premise ("every other
dependency edge is a wait at a fresh load") true for exports. The reload leg
is answered by the publication check. For the parent and child cycle, `p`'s
qualified reference drives `p.child` before `p` publishes, so the child's
declaration of `super` waits on an unpublished `p` that waits on it, and the
scheduler reports `p -> p.child -> p`.

*Undecided by the spec* (with the user). Parent `P` declares `(mod c)`; `c`
imports `z`; `z`, which is not `P`'s child, imports `P`; `P` reaches neither
`c` nor `z` except through the declaration. Spec §8.10.1 lists `mod` in the
dependency graph, which makes `P → c → z → P` a cycle; read the same way, the
direct `super` import of row 1 would be a cycle, which §8.3.8 accepts. The
spec does not say whether §8.3.8's acceptance covers only a child's direct
dependency on its parent, or means a `mod` declaration never closes a cycle
back to the declaring parent. This design does not answer that question.
Whatever the answer, the outcome must not depend on the route
([ACT-1081](../../sprints/actions/ACT-1081-module-graph-through-a-declared-child-is-accepted-or-refused-by-load-route-intake.md)).

**Route independence** (ACT-1081; designed 2026-11-18, not in source at
`66bc7b8a`). Private to `src/`; no public API, carrier, schema or ABI change.

*The fault.* This section expected the program above to be accepted on
every route; the source does not deliver that. `qa` measured it on
`2d3a5b3e`:

- under `--run` it is refused as a cycle when the entry imports `P` or `z`,
  and runs when the entry imports `P.c`;
- in the REPL, `(z/zf)` reports the cycle, and `(P.c/cf)` in the next turn
  evaluates;
- a save that closes the graph is accepted, and a restart agrees.

The mechanism, read from source at `66bc7b8a`:

- The static gate and the publication check read no declared-child edge, so
  they accept the program.
- A parent's drive of a declared child it registers waits on the child
  (`drive_submodule` through `block_dep`). That edge is in the wait graph and
  not in the shared predicate.
- The signature barrier waits for each closure member's terminal typecheck
  (`gate_body_on_signature_barrier`). A parent is not terminal until its
  declared children are, so `z`'s barrier on `P` waits behind `P`'s wait on
  `c`, which waits on `z`: `z -> P -> P.c -> z`. The barrier exempts the
  root's ancestors by the shape of their names. That covers row 1 and not a
  third module.
- A parent's drive of a child already in flight does not wait. When the entry
  imports `P.c`, `P` therefore goes terminal before `c`, `z`'s barrier opens,
  and no wait cycle forms.
- A REPL turn that follows a failure takes the route its own expression
  names, so a module reported failed can evaluate in a later turn.

*The rule.* Whether a module graph is accepted depends on its files, never
on the route or the arrival order that loads them. One **completion graph**
`C` carries every edge the shared predicate yields (imports that load,
exports, qualified references, recorded edges and the prelude edge) and,
besides those, an edge from each parent to each declared child.

1. **A parent's completion includes every declared child,** whether its
   drive registers the child or finds it already in flight. A drive of an
   in-flight child waits on it too. Otherwise a reader of the parent's
   completion would see a child's records on some routes and not others.
2. **The signature barrier reads one of two readinesses, per member.** A
   member that lies on a cycle of `C` with the waiting root is read at its
   publication (*Declaration readiness*). Any other member is read at its
   completion, which is today's terminal predicate. Both are fixed by the
   files. This replaces the barrier's name-shape ancestor exclusion, which
   is deleted ([Principle 19](../arch/principles/19-no-module-privileged-by-name.md)):
   a child that depends on its parent lies on the cycle formed by the parent's
   declaration and the child's own edge back, so it reads the parent at
   publication as before. The root itself stays excluded.
3. **Which cycles of `C` are errors is decided in one place.** The static gate
   runs at the top of every cluster, rooted at the compiling module, and a
   module on a cycle reaches it. Any route that loads a module of an error
   cycle therefore compiles one and refuses there. The publication check
   refuses a save that closes an error cycle, and the gate refuses the same
   files at a restart.

Together these give one outcome on every route. An error cycle is refused
before any of its waits. An accepted cycle forms no wait cycle, because
around every cycle of `C` each dependent reads its dependency at publication,
and a module publishes before it drives its children. The REPL retry face
goes with them, because a retried turn derives the same outcome from the
same files.

*The ruling point.* One fact changes with the user's ruling: the error
clause of the cycle predicate in the one edge home
(`src/process_form/dependency.rs`, beside `DeclaredEdges`), which the static
gate and the publication check both read. Rules 1 and 2 are the same under
either ruling.

- **If a `mod` declaration can close a cycle:** every cycle of `C` is an
  error except §8.3.8's direct pair, the declared-child edge to `c`
  followed by `c`'s own dependency on its declaring parent (row 1). ACT-1081
  is refused on every route. The path is named from the module the route
  compiles first, so it is `P -> P.c -> z -> P` or a rotation of it. A
  grandchild that imports its grandparent is refused too, because it is not
  the direct pair.
- **If a `mod` declaration never closes a cycle:** a cycle of `C` is an
  error only when it holds no declared-child edge, which is today's answer.
  ACT-1081 runs on every route. By rule 2, `z` typechecks before `c`
  publishes on every route. `z` therefore never sees a record that `c` adds
  to `P`, such as an implementation of `P`'s trait. A use of one is refused
  as a missing implementation on every route, although spec §7.11.1 makes
  an implementation visible wherever its trait and type are reachable. The
  user's question therefore carries this consequence. Under the other
  ruling, §7.11.1 holds unchanged, because no accepted cycle passes through
  a declaration.

Until the ruling, the error clause keeps today's answer, so the
ruling-independent rules 1 and 2 make every route accept ACT-1081. When to
build them is `sprint`'s decision.

*Cost.* Reach through declared children makes the gate's walk parse each
visited module's declared children, once per cluster under the existing
memo. The full suite's wall time is the measurement.

*Falsifiers.*

- REPRO-1081's routes disagree, in a batch mode or in a REPL order.
- `CRANELISP_SCHEDULER_TRACE` shows a barrier wait on a member that shares a
  cycle of `C` with the waiter, or a parent that turns terminal before an
  in-flight declared child.
- A module that reaches a parent and does not lie on a cycle with its
  children sees a child's implementation on one route and not on another.

*What `dev` builds* (`src/process_form/dependency.rs`, `src/scheduler.rs`),
with module rows:

- the drive of an in-flight declared child waits on it, and the parent turns
  terminal only after the child;
- `z`'s barrier on `P`, in the ACT-1081 shape, opens at `P`'s publication;
  `y`, which imports `P` and does not lie on a cycle with `c`, stays blocked
  until `c` completes; row 1's child opens at its parent's publication with
  the ancestor exclusion deleted;
- the gate's walk reaches a declared child, and under today's error clause a
  cycle through a declaration is no error while a cycle without one is.

*End-to-end cells.* Turn green: REPRO-1081, which asserts agreement and not
the outcome. Stay green: row 1's and row 2's cells and the §6.12 prelude
cells, as listed under *End-to-end cells* above. For `qa` to allocate:
`y`'s case, with a child's implementation of its parent's trait used from
`y` on every route; and, once ruled, the outcome clause and the save and
restart legs of REPRO-1081.

*Falsifiers.*

- A leg of Face 2 that reports a name not found in `a` or `b`, or completes
  without naming the cycle.
- A row-1 program refused as a cycle, or a row-2 program that compiles or
  reports an unresolved name.
- Two runs of one program whose outcomes differ in whether a cycle is
  reported.

*As built (`870aacd8`).* The published fact, its resets and the predicate
are in `src/scheduler.rs`. Both Pass-0 handlers and the qualified-reference
gate's tracked branch read the predicate (`src/process_form/dependency.rs`).
The release at publication runs on both paths. The eval thread's wait takes
the readiness it needs (`src/eval.rs`): a turn's dependency gap waits for
declaration readiness, and `/mod` waits for in-memory completion.

*Module evidence (landed with `870aacd8`).*

- `pass0_declaration_of_an_in_flight_module_waits_on_it` and
  `pass0_declaration_of_a_published_module_installs_its_names`
  (`src/process_form/dependency.rs`). For `import` and `export`, an
  unpublished, non-terminal module with a table makes the declaration wait
  and install nothing. A published, non-terminal module installs its names
  and records no edge.
- In `src/scheduler/tests.rs`:
  - `published_generation_is_ready_for_declaration_until_a_new_attempt`
    covers the fact and its reset;
  - `publication_requeues_whole_module_waiters_before_terminal` and
    `block_on_a_published_module_requeues_not_strands` cover the release;
  - `eval_dependency_wait_ends_at_publication` covers the eval wait.
- `startup_child_export_of_its_parent_reads_the_published_parent`
  (`src/session_v4/persistence_tests.rs`) covers row 1 at a fresh load.

*End-to-end cells.*

- Turn GREEN: `tests/spec_08_modules.rs::export_closed_cycle_run_reports_cycle_neg`,
  `export_closed_cycle_startup_reports_cycle_neg` and
  `s124_modules_super_cycle_neg_run`, `_link` and `_repl`.
- Stay GREEN: in `tests/spec_08_modules.rs`, `super_import_resolves_parent_fn`,
  `super_import_resolves_parent_type_constructor`,
  `mod_test_child_super_imported_parent_trait_resolves_as_constraint`,
  `s124_modules_super_run`, `_link` and `_repl`,
  `export_dependency_without_cycle_control`, `module_cycle_detection_neg`
  and the `fq_ref_cycle_*` cells; in `tests/repl_persist.rs`,
  `persist_bug_user_cl_preserves_original_str_not_expanded_str_concat` and
  `persist_bug_macro_usage_in_defn_survives_session_restart`; and the
  §6.12 prelude cells.
- For `qa` to allocate:
  - the undecided program in `--run` and the REPL, and a session save that
    closes it: allocated as REPRO-1081, which asserts that the routes agree
    (*Route independence*);
  - an `(export [p [x]])` from a child, spelled by its parent's full path,
    beside `super`;
  - a repeat-run cell for the arrival-order falsifier;
  - `/mod p` where `p` declares children that import `super`. A definition
    turn in `p` right after the switch publishes, and the children's names
    resolve.

**Face 1 status.** The failed-dependency refusal above (*The check*, *Failed
dependency*) is built at `f95f0a3a` for a whole-file rebuild, with
`worker::tests::failed_dependency_refusal::*` (the positive row RED with the
refusal disabled). Its fresh-load gap is stated under *Failed dependency*.
- **As implemented.** Both Pass-0 handlers in `src/process_form/dependency.rs`
  call one table check before they install or wait. `handle_import` calls it
  after the private-submodule check, and `handle_export` calls it before it
  installs. The check runs before the eval/pool branch, so both paths reach
  it. The scheduler's I3 body now lives in one locked helper, which
  `block_for_typecheck` and Pass 0 share. There is still one error builder
  and one site that records a failure dependency. A failed module with no
  table takes the load path instead: its wait fails fast with the same error
  or, on the eval path, retries after the purge (review N2).
- **Diagnostic.** The Pass-0 fail-fast, the qualified fail-fast and `block_for_typecheck`
  share one builder, `refuse_failed_dependency_locked` in
  `src/scheduler.rs`. The failed-module wait report
  (`module_failed_error`) uses the same wrapped text, so the rules below
  apply to all four.
  - **Location: the failed module's own location, its file included.** It
    points at the fault the user must fix. The reference site is used only
    when the failed module has no stored error. As delivered at `aed0fcb1`,
    `--run`, `--link` and the reload notice name the failed file
    (`helper.cl:1:…`, `[errors: helper.cl]`). Guard:
    `tests/spec_08_modules.rs::failed_import_location_belongs_to_named_file_neg`.
  - **Prefix: one located category prefix** (REPL §5.5, which the user's
    S123 Phase 2 → 3 ruling applies here). The wrapping error owns the one
    location. Its text is `module '<m>' failed:` followed by the failed
    module's own error without any span: a module error contributes its bare
    message, as today. Any other located error contributes its category word
    and bare message, for example `type error: type mismatch …`. A platform
    error contributes its own text, which has no span. The category stays
    because it tells the user what kind of fault to look for. The span goes
    because the wrapper already locates it. Every wrap therefore adds no
    second located prefix, whatever its nesting depth.
  - **Not designed: an accessor in `cranelisp-types`.** `src/` derives the
    category word from the public error variant. A new
    `cranelisp-types` accessor would be an inter-crate API change, which
    routes through `arch` and the user gate.
  - **Open (prefix only).** Today the non-module branch of `wrapped_message`
    in `src/scheduler.rs` renders the inner error in full, so every seam
    prints `module error in …/helper.cl: at 11..38: module 'helper' failed:
    type error at 11..38: …`. RED:
    `tests/spec_08_modules.rs::failed_import_has_one_located_prefix_neg`
    (K-3). `dev` adds a unit row at the shared builder. It asserts one located
    prefix for a stored type error and for a stored module error, and the
    failed module's file as the location.

**Exactness.** When `M` is checked, every module outside the pass and every
member rebuilt earlier in it holds its final generation. A cycle created in a
pass is therefore refused at its last-rebuilt member, and no stale pre-plan
edge refuses `M`. On a fresh load the scheduler reports a genuine cycle as a
wait cycle before either member publishes, so `--run` and `--link`
diagnostics do not change. An implicit-prelude cycle is the exception: a
module does not wait on an in-flight prelude, so the scheduler sees no wait
cycle. The static gate, this check or the failure exit's cycle precedence
reports it ([§6.12](#612-the-implicit-prelude-dependency)). An `export` of
a module still in flight at a fresh load waits on it through the declaration
readiness gate, so its cycle is a wait cycle too.

**Cost.** The walk visits the targets' dependency closure once per check and
computes each visited module's edges once. It runs for every prepared
cluster. The full suite's wall time is the measurement.

**Grade: asserted with a named falsifier.** Every generation and increment
passes the prepare step. Falsifiers:

- after a completed turn or plan, the live tables of modules whose latest
  attempt compiled contain a cycle. A failed attempt's table keeps its Pass-0
  declarations and publishes no generation;
- a whole-file rebuild publishes while a module it has an edge to stands
  `Failed`. An unsettled member and the prelude reached through the bit are
  the exceptions;
- a Pass-0 `import` or `export` of a module standing `Failed` reports an
  unresolved name.

**Potential extension: an increment's own edges.** A REPL turn whose staged
edges or owed lookups reach a module standing `Failed` publishes when every
name it uses survives in that module's table. Spec §8.5.4 item 5 asks for a
chained failure. This is inferred from the whole-source mechanism, not
observed. Trigger: `qa` reproduces it. The same refusal would then read only
the turn's staged edges and owed lookups, never its earlier generations.

**Module evidence (`dev`).**

- An increment in `a` whose staged callee reaches `b`, while `b`'s live table
  reaches `a`, is refused naming `a -> b -> a`; `a`'s table is unchanged. The
  same turn is accepted when `b` does not reach `a`.
- A rebuild of `M` whose new edge reaches `X`, with `X` among the members
  rebuilt later and `X`'s live table reaching `M`, is accepted. With `X` not
  excluded, it is refused.
- A macro checkpoint in `a` whose clause calls `b/g`, while `b`'s live table
  reaches `a`, is refused naming `a -> b -> a`, and `a`'s table holds no
  macro. The same checkpoint is accepted when `b` does not reach `a`, and
  during a rebuild of `a` with `b` among the later members.
- Pass-0 fail-fast, in `src/process_form/dependency.rs`
  `bare_module_name_tests`:
  - `pass0_declaration_of_a_failed_module_fails_with_its_error`. An `export`
    or `import` of `w`, of a name `w`'s table holds or lacks, while `w` stands
    `Failed` with a present table, fails with `w`'s error rather than a
    `not found in module 'w'`. It records `w` as a failure dependency and
    installs no candidate. All four legs were RED on `d056842f…` and are GREEN
    on `f0d1006f…`.
  - `pass0_declaration_of_a_compiled_module_installs_its_names` is the
    negative. With `w` compiled, both install as before and record nothing.
    It is GREEN before and after.
  - With the fail-fast planted absent, the positive row is RED on all four
    legs and the negative stays GREEN (`dev`'s report,
    `.local/s122-helper-followon-dev-result.md`).
- Failed dependency, built at `f95f0a3a` as
  `worker::tests::failed_dependency_refusal::*`:
  - A rebuild of `M` whose staged callee is in `w`, while `w` stands `Failed`
    and `w`'s table still holds the called name, is refused with `w`'s error,
    and `w` becomes `M`'s failure dependency.
  - The same rebuild is accepted with `w` compiled, and with `w` among the
    later members.
  - An increment in `M` calling the same name is accepted, which is the
    increment exemption.
  - A rebuild of `x` with the bit on and no prelude name is accepted while
    the prelude stands `Failed`, which is the prelude exemption.
- The prelude rows are in [§6.12](#612-the-implicit-prelude-dependency); the
  plan rows are in
  [REPL lifecycle §1.2](repl-lifecycle.md#12-poll-and-reload).

End to end:
`tests/repl_persist.rs::watch_save_closing_qualified_module_cycle_reports_circular_dependency`
and its acyclic control,
`tests/repl_persist.rs::repl_definition_closing_qualified_module_cycle_refused_and_not_written`,
and the macro face,
`tests/repl_persist.rs::repl_defmacro_clause_closing_qualified_module_cycle_refused_and_not_written`
with `repl_defmacro_clause_calling_acyclic_qualified_dependency_accepted_control`;
the `--run` cycle cells stay green. ACT-1016 allocates the evidence for the
failed-dependency refusal and for Face 2.

### 6.12 The implicit prelude dependency

Status: **designed 2026-09-30** (ACT-1014); fresh-load reach through
`export` or a qualified reference **revised 2026-09-30** after QA's
[adjudication](../../tests/plan/s122-evidence-delta.md#design-residuals--adjudication-2026-09-30).
Implemented in the S122 working tree and reconciled with it on 2026-09-30.
The walk's file-derived aliases (below) were delivered at source `d056842f…`
on 2026-09-30. The helper end of ACT-1014 needed §6.11's Pass-0 fail-fast
(the outcome below). It is implemented at source `f0d1006f…`, uncommitted,
and the helper-end row is GREEN there. The finding-scoped review of the
fail-fast and the alias change found no blocking or required finding. QA
judged ACT-1014 adequate and closed it on 2026-09-30
([helper-end adequacy](../../tests/plan/s122-evidence-delta.md#act-1014-helper-end--final-adequacy-2026-09-30)).
Private to `src/`; no public API, carrier, schema or ABI change.

**Rule.** The implicit import is a dependency on `prelude`, like the
`(import [prelude [*]])` it stands for (spec §8.8.1, §8.10.1; the user's
2026-09-30 ruling). A module whose fallback bit is on
([§6.5](#65-entry-module-and-the-implicit-prelude)) has the edge
`M → prelude` in every graph int checks or orders by. How the prelude reaches
`M` makes no exception: a module with the bit on that the prelude depends on
closes a cycle, which is refused (spec §8.10.2). A null import suppresses the
bit and is itself no edge (spec §8.3.7), so `(import [prelude []])` is the
remedy the spec names.

**Where the edge enters.** One fact, four readers:

| Graph | Owner | What it refuses |
|---|---|---|
| Static import-closure gate ([§6.9](#69-bare-module-names-in-import-and-export)) | `static_import_closure` and its file walk | A cycle through an `import`, at the first cluster whose walk sees it: a fresh load in every mode, a REPL turn, a whole-file rebuild |
| Reload graph ([REPL lifecycle §1.2](repl-lifecycle.md#12-poll-and-reload)) | selection, order and the order check | Nothing itself; a prelude save selects every module with the bit on and orders it after the prelude |
| Publication check ([§6.11](#611-module-cycles-at-publication)) | the commit-planning step | A generation that closes the cycle through a re-export or a qualified reference |
| Cycle precedence at the failure exit (below) | the attempt failure exit of [REPL lifecycle §1.2.1](repl-lifecycle.md#121-failure-dependencies) | Nothing new; a failed whole-source attempt on such a cycle reports the cycle instead of its own error |

- **Static gate.** The walk adds the edge beside a module's loading imports.
  For the root it follows the fallback bit this attempt sets; the `Replace`
  arm sets the bit before the gate runs. For each walked file it applies the
  spec §8.8.1 predicate to that file, the one the bit and the injection use.
  The target is the prelude file the injection discovers. With no prelude
  file there is no edge (spec §8.8.3), and the prelude has no edge to itself
  (spec §5.9).
- **The barrier does not wait on the edge.** The signature barrier's members
  stay the closure over written imports. A parent waits for its declared
  children before it is terminal (the FIXME 0342 deferral in
  `process_cluster_once`), and a declared child of a module the prelude
  re-exports keeps the implicit import: the stdlib's `(mod- test)` children
  do. A barrier wait on the prelude would deadlock `prelude → parent → child →
  prelude`, although declared children are not dependency edges (§6.9;
  [REPL lifecycle §1.2](repl-lifecycle.md#12-poll-and-reload)). The prelude's
  readiness stays with its injection (§6.5).
- **Reload and publication predicate.** The edge is present exactly when the
  module's bit is on. Each reader supplies the bit of the generation it
  reads: `SharedState.prelude_fallback` for a live or staged table, and the
  bit that its records imply for an established reference. The predicate's
  bit parameter therefore carries a real value at every caller, and the
  reach computation (`add_prelude_fallback_edges`) is deleted.
- **A null import is no edge.** The reload predicate counts only imports that
  load, as the static gate already does. A qualified or aliased use through a
  null import is still recorded, as a callee or lookup edge. Measured
  2026-09-30 on the delivered binary (`b3015064…`), with `x.cl` holding
  `(import [prelude []])` and the prelude importing `x`: `/mod x` then
  `(defn k [] 2)` is refused as `x -> prelude -> x`, and a save of either
  file fails, ordering the prelude before `x` (probes N2–N4 in
  `.local/s122-reload-tails-design-probe/`). The same misreading reaches a
  fresh load in every mode: a prelude that imports a null-importing helper
  and publishes a definition is refused as `prelude -> mymod -> prelude` by
  the publication check at its own cluster, while an import-only prelude
  publishes nothing and passes (face C, `test`'s probe of 2026-09-30,
  `.local/s122-prelude-ruling-test-result.md`). The publication check reads
  the reload predicate, so this correction removes face C with no further
  site. The cache-validity edge set keeps null imports
  ([§7.6](#76-dependency-record-and-validity)); over-invalidation there is
  harmless.

**Refusal by a failed prelude** (review of 2026-10-01; REPL §14.5, spec
§8.8.1). An implicit import must refuse against a failed prelude as an
explicit `(import [prelude [*]])` does through the Pass-0 fail-fast.
`inject_prelude_if_needed` loads the prelude when it has no table, and the
dependency wait then refuses a module whose prelude fails. When the prelude
already has a table, a failed rebuild's fresh, empty one included, it loads
nothing and refused nothing, so a dependent compiled against that table and
failed on its own names.

- **Rule.** When the prelude stands `Failed` in the scheduler, the injection
  refuses a module whose fallback bit is on through `refuse_failed_dependency`,
  recording the prelude as its failure and refusing dependency. The module
  then waits ([REPL lifecycle §1.3.1](repl-lifecycle.md#131-session-lock)).
  This holds at a whole-file rebuild and at a fresh load, so a restart and
  the session end the same way.
- **Cycle exception.** A module that the failed prelude reaches is on a cycle
  with it, not a dependent of it. The injection does not refuse it, and the
  reload executor's waiting check does not hold it
  ([REPL lifecycle §1.2](repl-lifecycle.md#12-poll-and-reload), Waiting).
  It proceeds as at a fresh load: it compiles when it names no prelude name,
  and otherwise cycle precedence at the failure exit names the cycle. The
  reach is the one this section's failure-exit walk computes; no second walk
  is added.
- **Barrier unchanged.** The refusal reads the prelude's settled state; it is
  not a barrier wait, so the deadlock the barrier bullet describes cannot
  arise.

**Reach the static gate does not see.** The static walk follows loading
imports only, because its closure is also the barrier's members. At a fresh
load, a module `x` with the bit on that the prelude reaches only through
`export` or a qualified reference, directly or through other modules,
therefore compiles against the in-flight prelude. Either:

- `x` compiles. Then the publication check refuses the first member of the
  cycle that publishes after the other members' edges are live, the
  prelude's cluster at the latest (§6.11 exactness), naming the cycle; or
- `x` fails in its own source, typically on a prelude name the in-flight
  prelude does not yet hold. Spec §8.5.4 item 6 requires the cycle here, not
  the unresolved name.

The second case is closed by **cycle precedence at the failure exit**. The
exit that records a failed whole-source attempt's dependencies
([REPL lifecycle §1.2.1](repl-lifecycle.md#121-failure-dependencies)) also
asks, for a module `A` with the bit on, whether the prelude reaches `A`:

- **The walk.** It starts at the prelude and uses the static gate's file walk:
  resolve, read and parse each file, with an unreadable or unparseable file a
  leaf. From each file it follows the edges §1.2.1 extracts from an attempt's
  forms:
  - `import` targets that load and `export` targets, resolved through the
    file's declared children;
  - the module of each qualified symbol written outside reader-quoted data,
    substituted through the aliases that file declares: its import aliases,
    resolved through its declared children, and its `mod` short names.

  Prelude edges are not followed; the walk starts there.
- **Aliases come from the walked file.** A walked module's Pass 0 writes the
  same aliases to the session carrier, but it may not have run when the
  failing module's exit fires. The walk therefore collects each parsed file's
  aliases into a walk-local set, with the keys and targets Pass 0 derives,
  and substitutes through the one `cranelisp_types::substitute_module_alias`.
- **A qualifier through another module's mount resolves at the fixpoint.**
  Spec §8.4.4 export mounts are public aliases (S124), so a file's qualifier
  can read an alias that another file declares. Spec §8.5.4 item 6 requires
  such a qualified cycle to be reported. The walk must therefore not depend
  on the order in which it visits files:
  - A walked file's qualifier that does not substitute to a module file stays
    *pending*. The walk does not drop it as a leaf.
  - The walk also follows an edge from the writing file to the qualifier's
    owner. The owner is the longest proper prefix that resolves to a module
    file (`p` for `p.s`). Spec §8.4.4 steps 2–3 resolve the mount there, so
    the qualifier depends on the owner.
  - When a visit adds aliases, the walk substitutes every pending qualifier
    again through the enlarged set. A qualifier that now names a module is
    followed as an edge from the file that wrote it.
  - The walk stops when the queue is empty and no pending qualifier
    resolves. The alias set only grows and the qualifiers are finite, so the
    walk terminates. Its result is the least fixpoint, which does not depend
    on queue order.

  - A substitution can reveal another owner: with `p` mounting `q` as `s`
    and `q` mounting `x` as `t`, `p.s.t/y` substitutes to `q.t/y`, whose
    owner is `q`. The walk follows that owner as an edge from the writing
    file, as it follows the first, and keeps the rewritten qualifier
    pending.

  A name-less mount stays no edge (§6.13): the cycle runs through the
  qualifier, not through the export. *As built at `2dec7450`:* the pending
  set, the re-substitution and the first owner edge. The revealed owner is
  not followed: a substitution that does not name a module file never
  enqueues its new owner, so a chain of mounts misses the cycle (`review` of
  `2dec7450`; ACT-1079, *The cycle walk*). It is not observable while
  ACT-1079's resolver refusal stands, and it is corrected with that
  resolver, with its module row (§6.13, *A qualified reference through a
  mount*).
- **The report.** When the walk reaches `A`, the attempt fails with
  `circular dependency detected: A -> prelude -> … -> A`, rendered by
  `scheduler::CycleError::render`, at the location of the error it replaces.
  Otherwise the original error stands.
- **Why only the prelude edge.** The premise is that every other dependency
  edge is a wait at a fresh load, so the scheduler reports its cycle before
  one member compiles against the other (§6.11). The prelude edge is the one
  no module waits on (the barrier bullet above). The premise holds for an
  `export` because §6.11's declaration readiness gate makes it a wait edge
  (ACT-1016 Face 2, built at `870aacd8`).
- **It changes a diagnostic, never an outcome.** The attempt has already
  failed, so an edge the walk over-approximates can mislabel a failure but
  cannot reject a program. The reader-quote shield, `cranelisp_types::quote_head`
  (the one classifier, as the expander uses it), keeps a qualified symbol in
  quoted data, such as a macro template, from counting. Principle 24's ban
  on identity scans does not apply: the walk derives no compile-necessary
  identity.
- **Declared children stay out of the walk**, as out of every cycle graph. A
  declared child of a prelude dependency that fails on a prelude name keeps
  its own error; that shape is
  [ACT-1015](../../sprints/actions/ACT-1015-declared-child-reads-in-flight-prelude-intake.md)'s
  intake (an unconfirmed lead, carried to S123), not a cycle.
- **Deterministic and mode-uniform.** The walk reads files and the failed
  module's identity, not scheduler or session state, so the report does not
  depend on interleaving. `--run`, `--link`, REPL startup and a restart share
  the fresh load and report one path.
- **Whole-source attempts only**, as the record. An increment that closes the
  cycle is refused by the publication check before it can fail otherwise.
- **Not taken:** following export targets and qualified references in the
  static gate. That would change the barrier's members or need a second
  closure. It would also make every module with the bit on parse the
  prelude's re-export closure on every load: thirteen stdlib modules today,
  which needs a session memo. The failure exit pays only when an attempt
  fails.

**Outcome for ACT-1014's shape.**

- **Reach through an import.** A save that adds `(import [x [one]])` to the
  prelude, while `x` has the bit on:
  - the prelude's rebuild is refused at the static gate, naming
    `prelude -> x -> prelude`;
  - `x` and every other module with the bit on fail and lock on their
    rebuilds;
  - a restart on the saved files reports the same path at the entry's first
    cluster.

  Both refuse `(x/get (P 4))`.
- **Reach through `(export [x …])` or a prelude function calling `x/…`.** In
  the session:
  - the plan's pre-plan edges order the prelude before `x`;
  - the prelude's rebuild publishes, because `x` is a later member whose
    edges are not yet settled (§6.11);
  - `x`'s rebuild is refused by the publication check, naming
    `x -> prelude -> x`;
  - the order check's follow-on rebuilds the prelude with its dependents. The
    prelude fails through §6.11's Pass-0 fail-fast on the failed `x`, which
    carries `x`'s refusal naming the cycle. A qualified reach already fails
    this way;
  - `x` is rebuilt again. If it names a prelude name, it fails on that name,
    and cycle precedence reports `x -> prelude -> x`. Otherwise it compiles,
    because a module does not wait on the prelude.

  The save ends with the prelude failed and the cycle named, and with `x` as
  a restart leaves it.
- **A save of `x` that drops its null import (the helper end),** while the
  prelude reaches `x` by `export` or `x/…`:
  - the pre-plan edges order `x` first. `x` publishes, because the prelude is
    a later member, and the prelude is refused, naming
    `prelude -> x -> prelude`;
  - the follow-on for `x` orders the component `[prelude, x]`. The prelude
    publishes, and `x` is refused, naming `x -> prelude -> x`;
  - the follow-on for the prelude fails it through the Pass-0 fail-fast, with
    `x`'s refusal. `x` then compiles.

  The save ends with the prelude failed and locked, the cycle named, and `x`
  compiled. The save that restores the null import rebuilds `x` without the
  edge and then the prelude, and both are accepted.
- **Restart parity.** A restart on the saved files ends each module as the
  session does. The prelude is refused and names the cycle. `x` compiles
  unless it names a prelude name, because at a fresh load it publishes before
  the prelude's edges are live (§6.11, Exactness). QA's restart probe
  confirms `x/one` compiles (ACT-1014).
- **With `x` null-importing the prelude** and naming no prelude name, the
  session and the restart accept every form of reach.

**Superseded.** The 2026-09-29 reach rule, which kept a fallback edge only
for a module outside the prelude's reach on the strength of spec §8.8.2's
order, is retracted by the ruling. Fixtures whose prelude imports a module
with the bit on are cyclic under the ruling; `qa` holds the census.

**Cost.**

- **The static gate.** A module with the bit on now walks the prelude's file
  and its import closure once per cluster fingerprint. The stdlib prelude
  imports nothing, so that is one parse.
- **Cycle precedence.** A successful attempt pays nothing. A failed
  whole-source attempt with the bit on pays at most one read and parse of
  each file the prelude reaches. A fresh load already parses those files once
  to load them.
- **Measurement.** The full suite's wall time; a material rise refutes the
  claim. `dev`'s single run at the implemented source reported 113.8 s under
  nextest, against the standing figure of about 170 s, so the claim stands.

**Grade: asserted with a named falsifier**, as §6.11. Falsifiers:

- after a completed load, turn or plan, the prelude's live table reaches a
  module whose bit is on, both modules' latest attempts having compiled. A
  failed attempt's table keeps its Pass-0 declarations, so a failed prelude
  that still exports `x` does not refute the claim;
- a failed fresh load whose files put a module with the bit on on a cycle
  through the prelude reports another error for that module.

**Module evidence (`dev`).** Arm each row RED on the pre-fix source where its
seam exists.

- The predicate: a module with the bit on has the prelude edge whether or not
  the prelude reaches it; a module holding `(import [prelude []])` has none;
  `(import [prelude [x]])` is an edge; a null alias import is none.
- The static gate, over a temporary project whose prelude imports `x` with
  the bit on: the roots `prelude`, `x` and a third module with the bit on each
  report the cycle, starting where the walk enters it: `x -> prelude -> x`
  from `x`, `prelude -> x -> prelude` from the others. With `x`
  null-importing the prelude, none does. The barrier's members for a root with the bit on and no imports
  exclude the prelude.
- The publication check:
  - a prelude generation re-exporting `x` with the bit on is refused;
  - with `x` null-importing, it is accepted, and so is an increment in `x`
    (probe N2);
  - a prelude generation that imports a null-importing module and publishes
    a definition is accepted (face C).
- Cycle precedence, over a temporary project in which `x`, with the bit on,
  fails on a bare prelude type:
  - with the prelude reaching `x` through `export`, and through a function
    calling `x/…`, the failure reports `x -> prelude -> x`, not the name;
  - with the prelude exporting `a` and `a` importing `x`, it reports
    `x -> prelude -> a -> x`;
  - with the prelude exporting `a`, `a` null-importing the prelude and
    reaching `x` only as `y/one` through `(import [(x y) []])`, and no alias
    in the session carrier, it reports `x -> prelude -> a -> x`;
  - with `x` null-importing the prelude and failing on another missing name,
    that name's error stands.
  - Over-reach negatives, each keeping `x`'s own error:
    - the prelude names `x/one` only inside a quoted macro template;
    - `x` is a declared child of a module the prelude exports.
  - Mount reach (built at `2dec7450`). The prelude imports `p [z]` and
    calls `p.s/y`, and `p.cl` declares `(export [(x s) []])`. The walk
    reports `x -> prelude -> x`. A second leg has a prelude that writes
    `p.s/y` without importing `p`, and reports the same cycle through the
    owner edge. As controls, with `p`'s mount targeting another module `w`,
    or with the mount absent, `x`'s own error stands.
  - Chained mount (with ACT-1079's correction; RED on `f95f0a3a`). The
    prelude writes `p.s.t/y`, `p` mounts `q` as `s` and `q` mounts `x` as
    `t`. The walk reports the `x` and prelude cycle whichever file it visits
    first.
- The plan: a save of a null-importing `x` orders `x` before the prelude and
  both succeed (probe N3); a save of the prelude succeeds (probe N4).
- The helper end:
  `src/session_v4/persistence_tests.rs::helper_save_dropping_its_prelude_opt_out_is_refused_as_a_cycle`.
  It is re-realised to ACT-1014's repaired condition. It covers `export` and
  `x/one` reach in both directions: the helper end, and the twin leg in
  PD-4's direction.
  - Its `export` variant was RED on `d056842f…` in both directions, for the
    unresolved name. All four legs are GREEN on `f0d1006f…`. Each closing save
    names `x -> prelude -> x` and ends with `x` compiled and the prelude
    refused, which matches an in-process `no_cache` restart.
  - The kept-bit plant turns it RED, and so does the fail-fast planted
    absent.
  - ACT-1014 assigns the staged-edge plant to the seam row
    `worker::tests::publication_cycle_follows_the_staged_module_s_own_prelude_edge`.

End to end:

- `tests/repl_persist.rs::prelude_save_importing_prelude_dependent_module_agrees_with_restart`;
- the ruled cells PD-1 to PD-3, PD-4 (export reach), PD-5 (qualified reach)
  and the control PD-4c
  ([QA allocation](../../tests/plan/s122-evidence-delta.md#design-residuals--adjudication-2026-09-30));
- face C's fresh-load witness, the repaired
  `tests/repl_watch.rs::watch_errors_block_evaluation_no_last_known_good`.
  Whether it also gets a cell in every mode is `qa`'s decision.

### 6.13 Import and export entries and export mounts (S124)

**Status: landed at `42e6d929` (rows D3, D10); the two regeneration
corrections (*Regeneration*) at `74aa7a52`.** A qualified reference through a
mount whose owner is not loaded is designed below and not scheduled
(ACT-1079). The carrier is packet
row D3 ([import and export entries](../arch/interfaces.md#import-and-export-entries)):
a names list is `None`, `Glob` or `Specific` of `ImportEntry` values, each a
`Name { source, local }` or a `MemberGlob(parent)`, and `ExportSpec` gains its
mount `alias`. The frontend is the only producer and derives `local`
([frontend modules §2.2](../frontend/modules.md#22-the-bound-name-is-derived-here-once)).
This section is the binary's side. It lands as the consumer step of D3's
callee-first migration, with D3's cache-schema bump, and corrects ACT-0997,
ACT-1055 and ACT-1056 together.

**Installation (`src/imports.rs`).**

- **Per entry.** A specific list installs each entry in source order. A `Name`
  entry reaches the candidates of `source` in the source module, with the
  existing existence, visibility and subtree checks, and binds each under
  `local`. A `MemberGlob` entry projects the parent's public members as today
  and binds each under its bare member name. The exposures of one list are the
  union of its entries' exposures; duplicates deduplicate in
  `expose_candidate` and distinct sources coexist (§8.6.4).
- **No written spelling is read.** The installer never binds `source`, and
  never derives a bare name from it. Binding a dotted entry under its dotted
  spelling (ACT-1055) therefore has no code path.
- **Import and export share it.** The same per-entry collection serves both;
  they differ only in visibility and in the export's declared-export record,
  which records each entry's `local` (§6.7).
- **Locations.** The carrier holds no per-entry span, so an installer error
  (not found, not public) is located at the spec. The frontend's own entry
  errors are located at the element.

**Name-less specs are one rule for both forms.** `(import [m []])` loads
nothing and registers only its alias (spec §8.3.6, §8.3.7). `(export [m []])`
and `(export [(m a) []])` follow the same rule (§8.4.0): the export handler
registers the mount, if any, and loads nothing. A bare `(export [m []])` is
therefore a definite no-op: it re-exports nothing, registers no mount, loads
nothing and is not refused (spec §8.4.4, as ruled under S124-Q4). Every predicate that asks
whether a spec loads (the handlers, the reload edges and test selection) reads
one helper over either spec, so imports and exports cannot answer
differently. A qualified reference through a mount auto-loads its
target (spec §8.5.4), as one through an import alias does. The dependency
record still keys every export target, as it keys every import (§7.6).

**A qualified reference through a mount loads the mount's owner** (ACT-1079;
designed S124 W8, not scheduled: the user has not pulled ACT-1079 into S124).

- **Rule.** Spec §8.5.4 makes a qualified name self-sufficient, and §8.6.6
  resolves a mount at the longest dot-separated prefix that is a known module,
  then restarts on the rewritten path. A reference therefore loads each owner
  its resolution needs, in turn, and never fails because an owner was not
  loaded. For `p.s.t/y`, with `p` mounting `q` as `s` and `q` mounting `x` as
  `t`: `p` loads, `p.s.t` becomes `q.t`, `q` loads, `q.t` becomes `x`, and
  `x` loads.
- **Where.** The qualified-reference gap protocol (§6.3), at
  `drive_module_dep`, which both gap paths reach. When a gap's module path
  resolves to no module file, the driver loads the owner instead: the
  longest proper prefix that resolves to a module file, by the same rule the
  §6.12 walk uses. The cluster retries from the top, as after any gap, and
  resolution substitutes through the now-loaded owner's mounts. A path with
  no file-backed prefix keeps today's located "not found" refusal (spec
  §8.5.4 item 3). Each owner load is an ordinary dependency edge, so a cycle
  through an owner is reported like any other.
- **Termination.** Each retry loads a module not loaded before, and modules
  are finite. A rewritten path that names no file and whose owner is already
  loaded with no mount for the next segment is the refusal. The §8.6.6
  depth limit bounds the substitution itself.
- **No inter-crate change is assumed.** The gap already names the rewritten
  path (`q.t` in ACT-1079's subject B). If typecheck turns out to report such
  a path as a hard error instead of a gap, that is a return to `arch`, not a
  binary work-around.
- **The cycle walk.** The §6.12 walk's revealed-owner edge lands with this
  correction, because only then is it observable.
- **Evidence.** ACT-1079's REPRO-1079-a to -c and its two `dev` module rows:
  a path whose file-backed prefix declares the mount resolves with that
  prefix unloaded, and through two mounts; the walk visits a revealed owner.

**Export mounts — the writer** ([alias contract](../arch/module-alias-scoped-lookup.md)
§5.1; `arch` names the binary as its owner).

- **One function, two routes.** One crate-private function installs a
  module's mount: a `Public` alias entry under
  `cranelisp_types::module_alias_key(<exporting module>, <alias>)`, targeting
  the module the spec resolves to through §6.9's resolver. The fresh route
  calls it from the export handler, before any load decision. The restore
  route calls it from the declared-alias installer, which now reads the
  restored table's `exports` beside its `imports` and `submodules`. A
  whole-file rebuild's session-state reset removes the module's mount keys
  with its import-alias and submodule keys.
- **Declaration errors are raised here.** This writer is the declaration
  seam §5.1 names. It refuses, located at the spec:
  - a mount alias equal to a child the module declares (`mod` or `mod-`),
    read from the declared children, so the order of the `mod` and `export`
    forms does not matter;
  - a mount alias already held by a mount of the same module to a different
    target, in this form, an earlier form or an earlier REPL turn.

  A repeated mount to the same target is idempotent. Each refusal is a
  §8.6.4-family error and fails the attempt like any other Pass-0 error.
- **One key mint.** The import-alias writer's private `alias_key` helper
  deletes in this change-set, so both alias writers key through the
  types-owned mint (§12.1 reject 4, §16.0).
- **The index path writes no mount.** Its isolated tables never write live
  session state ([index-worker isolation](index-worker-isolation.md)).
- **Lookup is unchanged.** No probe, precedence or visibility rule is added.

**Other consumers.**

- *Regeneration (`src/save.rs`).* The rule is that a regenerated names list
  binds exactly what its specs bound (REPL §15.4 rule 1). Import and export
  share the entry renderer.
  - **Entries.** A `Name` entry renders as its `source` when `local` equals
    `cranelisp_types::bare_member_name(source)`, and as `(source local)`
    otherwise, so `Shade.Blue` and `Some` keep their written form and a
    rename keeps its rename. A `MemberGlob` renders as `Parent.*`.
  - **A lone `*` entry renders as `(* *)`.** `[*]` is the glob only when `*`
    is the list's sole element (spec §8.3.2), so a `Specific` list whose one
    entry would render as `*` renders it in rename form. In a list of two or
    more entries `*` renders bare; spec §8.3.2 reads it there as the operator.
    The earlier design omitted this distinction. Under it,
    `(import [m [(* *)]])` regenerates as the glob `(import [m [*]])`, and
    the same error widens an export.
  - **Merging specs for one module and alias.** A glob and a specific list
    stay separate. Each module and alias gets at most one glob group and at
    most one list group. The specific entries concatenate into the list
    group, with equal entries removed. A name-less spec contributes nothing
    to the group that already exists for that module and alias. When no
    group exists it forms a list group, which renders as `[]`. Each group
    renders as its own pair, in the order it first appeared. Two pairs for
    one module are valid (spec §8.3.9, §8.3.10), and their effects union
    (§8.3.11). The earlier design let `Glob` absorb the list, which drops
    every rename: `(import [m [*] m [(f g)]])` regenerated as
    `(import [m [*]])`, so `g` was unbound after a restart. A glob cannot
    absorb a list and keep its effect. A rename binds a local name that the
    glob does not bind, and the entries cannot share the glob's list,
    because there `*` would read as the operator.
  - An export with a mount renders `(m alias)` as its specifier. Export
    specs are rendered one pair per spec and are not merged.
- *Restore (`process_form/cache_restore.rs`).* The re-export dependencies it
  derives from `exports` carry the entries unchanged, and the mounts install
  through the writer above.
- *`/imports` (`session_v4/lifecycle.rs`).* Each binding's synthesised spec
  holds one `Name` entry whose `source` is the binding's source symbol and
  whose `local` is the bound name.
- *Test selection.* A specific list is an edge exactly when it has an entry;
  the list-level member glob it matched is gone.
- *Dependency record and reload edges.* Unchanged apart from the name-less
  rule above.

**An import alias and a mount sharing a spelling** (spec
[§8.4.4](../../spec/08-modules.md#844-module-mounting-on-export), "Import
alias and export mount sharing a spelling", and §8.6.4; user ruling S124-Q4,
candidate B, 2026-11-17). An import alias and an export mount of one module
are stored under the same key, `module_alias_key(<module>, <alias>)`, and the
lookup holds at most one entry per key
([alias contract](../arch/module-alias-scoped-lookup.md) §2.1–§2.2). The two
writers enforce the mixed pair together:

- **Different targets refuse.** Each writer reads the other family's
  declarations from the module's records (`imports` and `exports`), so the
  refusal does not depend on form order, the REPL turn or the route. Targets
  are compared as the modules §6.9's resolver yields, never as spellings. The
  refusal is a §8.6.4-family error located at the second declaration, and it
  fails the attempt like the mount refusals above.
- **Equal targets form one public route.** The key holds one entry, and its
  visibility is a function of the declarations, not of write order: it is
  `Public` exactly when the module mounts the spelling. The mount writer
  writes `Public` over an equal-target import alias; the import-alias writer
  never lowers a `Public` entry. The restore route therefore yields the same
  entry as the fresh route whichever family its installer reads first, and a
  whole-file rebuild reinstalls whatever the saved source declares.
- **Regeneration keeps both forms.** The import and the export are separate
  records in `imports` and `exports`, and each re-emits in its own section
  (§1.3 of [session persistence](session-persistence.md#13-section-order)),
  so the pair round-trips as written.
- **Prerequisite.** The import-alias writer's own duplicate-alias refusal
  (`qa` lead R-A2; spec §8.6.4, two import aliases binding one alias) lands
  in the same change-set, because the mixed-pair branch reads the import
  family as a set of single routes.

The mount writer does not land without the mixed-pair branch: without it, the
later writer replaces the earlier entry under the shared key, and the alias is
silently rerouted. Two private routes and one public route under one spelling
were not chosen (candidate C) and have no shape here.

**Impl identity under a renamed import (ACT-0997; packet row D10, approved 2026-11-17).**
Today, regeneration labels an impl from its settled trait and type names, but
the live turn and rehydration label it from the head as written. Under a
renamed import the two labels differ, so every later regeneration of the
module would be refused. The fix is that every route reads the identity from
one record.

- **Determinant.** The writer's `WrittenTraitImpl` is the determinant. It
  holds the settled pair and, under D10, the head's `authored_label`. It is
  the one carrier present on every path, including a cache-restored table
  that nothing typechecked. A route first gets the form's label from
  `TraitImpl::authored_label()`. It then makes one keyed read of the module's
  records by that label, and takes the identity from the matching record's
  settled pair. No route resolves a head name again
  ([Principle 24](../arch/principles/24-resolve-once.md)), and none reads
  `CheckResult`. The label is the head as written, each reference with its
  written qualifier, taken before the higher-kinded rewrite; it is compared
  for equality only and is never an identity or display source
  ([approved changes, D10](../arch/interfaces.md#approved-changes-not-yet-in-source-s124)).
  The binary's own derivation (`definition_result_symbol`'s `impl` arm with
  `impl_echo_type_name`) drops both qualifiers and is deleted, not moved.
- **Routes.**

  | Route | Form | Record | Paths served |
  |---|---|---|---|
  | Live turn: the staged introspection record, the turn receipt and the definition result | the turn's built `impl` | the staging table's record, which typecheck upserts on success | REPL turn, fresh file load, whole-file rebuild on reload |
  | Rehydration (`save.rs::rehydrate_introspection_from_source`) | the backing file's `impl` forms, built as today | the table's persisted records, which carry the label | cache restore, fresh declaration load |
  | Regeneration (`save.rs::generate_impls`) | — | the module's records, enumerated | every path |
  | Definition echo and impl lookup (`src/repl/format.rs`) | — | the record named by the result's identity | every path |

  The rebuild prologue and the redefinition gate already key records by
  `trait_impl_key` over the settled pair, and they do not change.
- **A form matches exactly one record, or none.** This is `arch`'s rule for
  D10 ([approved changes](../arch/interfaces.md#approved-changes-not-yet-in-source-s124)):
  the label is not part of a record's key and nothing makes it unique within
  a writer, so a form matches only when exactly one of the writer's records
  carries its label. None or several is no match, reported, and never a pick.
  The keyed read therefore returns one of three answers (one record, none,
  several), and each route maps the last two to the same outcome:
  - *Rehydration* leaves the form unkeyed, skips it, and §2.4.3 reports what
    is then unrendered.
  - *The live turn* raises its located invariant error at publication, like
    the turn receipt's existing one.

  No fixed file scope should produce several: §8.6.5 rejects a second impl
  under one head as ambiguous, and §8.6.4 forbids re-pointing an alias. That
  argument is asserted, not measured; its falsifier is either report firing.
  No uniqueness check is added at `upsert_written_trait_impl` (rejected in
  the row: a restored sidecar bypasses upsert, so the read needs the rule
  anyway).
- **Live-turn timing.** The record exists only once the cluster has checked.
  The build stage therefore keeps the form's label for each staged impl
  record. Publication derives the key from the staging table's record, which
  is the defer shape of
  [Principle 26](../arch/principles/26-record-from-settled-state.md), under
  the exactly-one rule above.
- **The identity is the settled pair, held injectively.** The bare
  `Trait.Type` rendering drops each name's module. It is therefore already
  shared by `(impl Show Box)` for a local `Box` and `(impl Show lib/Box)`
  written in the same module, and a rename makes that case ordinary:
  `(import [lib [(Box B)]])` beside a local `Box`. The introspection key, the
  receipt and the result therefore hold the settled pair through an injective
  rendering, and the types crate already mints one (`trait_impl_key`).
- **Human-facing output.** The `impl <trait> for <type>` echo and the §2.4.3
  refusal render each half, qualified by its own module (REPL §1.1
  canonical-home qualification), from the record's settled names. They do not
  parse the key. The echo's current re-resolution of each bare half in the
  asking scope is removed for impls. Under a rename it misnames the type, or
  finds a different same-named one.
- **Regeneration enumerates the records alone.** Rows 1 and 2 of
  [session persistence §12.3](session-persistence.md#123-enumeration) add no
  identity that row 3 lacks. A shell written in the module has its record
  there, and an impl has an introspection record only once it has published,
  which writes its record. Both rows are therefore removed, with row 2's
  form-head discriminator
  ([Principle 7](../arch/principles/07-single-source-of-truth.md)). A
  record-less impl found while building is a defect to report, not a reason
  to keep them.

**Evidence (for `qa`).** The committed REDs of ACT-0997, ACT-1055 and
ACT-1056, the mount-collision negatives §8.4.4 owes, the S124-Q4 mixed-pair
cells (equal targets compose, different targets refuse) in both declaration
orders, and ACT-0997's impl-identity cells. The impl-identity cells are a
renamed type import and a renamed trait import, each persisted with a later
definition and then cold-restarted. Each cell also shows the definition echo
naming the canonical type. `dev` unit rows:

- impl identity: a local `Box` and an imported `Box` renamed to `B` are two
  impls in one module, and both regenerate;
- a qualified head and a bare head of the same spelling are kept distinct;
- an impl whose form has no matching record is not rehydrated;
- two records carrying one label are no match on both routes: rehydration
  leaves the form unkeyed and reports it, the live turn raises its located
  invariant error, and neither record is picked. The records are planted
  directly in the table, because no fixed source produces them; the
  one-record control keys the form.

Further unit rows: a
mixed list installs every entry; a dotted entry binds its member and not its
dotted spelling; a rename binds `local` only; a mount installs on both routes
and is removed by a rebuild; each collision refuses regardless of form order;
an import alias and a mount to one target leave one `Public` entry in both
orders and on both routes, and to different targets refuse in both orders; a
second import alias for one spelling refuses (R-A2); a name-less export loads
nothing and a bare `(export [m []])` is accepted with no mount; regeneration
round-trips each entry shape and the equal-target pair.

**The two regeneration corrections** (built at `74aa7a52`). The merge and
the renderer in `src/save.rs` follow the *Regeneration* rules above. The unit
rows are at `generate_imports` and `generate_exports`. Rows marked RED fail on
`42e6d929`; the controls pass there and after:

- RED: `m [*]` merged with `m [(f g)]` renders both pairs in the order they
  first appeared, for both input orders. RED: `m [*]` with `m [f]` renders
  both pairs. Control: two equal lists render one pair;
- RED: a lone `Name("*", "*")` renders `[(* *)]`, for an import and for an
  export. Control: `[+ *]` renders unchanged;
- control: a name-less spec merged with a glob, and merged with a list, adds
  no pair.

The e2e cells for `qa` to allocate are REPL persistence cells, run cold
after a restart on the regenerated file:

- **Rename survives a glob.** `m.cl` defines `f`. The turn
  `(import [m [*] m [(f g)]])` is followed by `(defn h [] (g))`. After the
  restart, `h` evaluates. As a control, the same cell with the two pairs in
  separate `import` forms.
- **Selective `*` stays selective.** `m.cl` defines `*` and `other`, and the
  importer null-imports the prelude so that bare `*` is `m`'s. After
  `(import [m [(* *)]])` and the restart, `*` resolves and bare `other` is an
  undefined-name error. The export leg puts `(export [m [(* *)]])` in the
  backing module, and an importer of it does not see `other` after the
  restart.

---

## 7. Cache + linker orchestration (Decisions 34, 37)

The cache artefact is a module's own symbol table: `.meta.json` is the serialized
`SymbolTable<(), ()>` stamped with the schema version, beside the module's `.o`.
The nice worker writes both from `symbol_tables` alone; no parallel store of
programs or structures feeds it. `design/backend/module-caching.md` owns the
format and its versioning; int stamps and consumes it.

### 7.1 Cache-hit flow inside `register_module`

Per Decision 37 the cache-hit decision lives inside the recursive dependency flow,
not in a parallel orchestrator. `process_form/cache_restore.rs::try_cache_hit_load`
is its one entry point. Every dependency handler (import, export, `mod`, implicit
prelude) calls it before falling through to a fresh build, and it recurses into the
restored module's own imports, so cached and fresh modules mix in any combination.

```text
register dependency M:
  if try_cache_hit_load(M):           # valid record (§7.6), .meta.json (+ .o unless generic-only)
    install M's decoded table
    re-resolve M's platform declarations
    register M with the scheduler as typechecked-from-cache, its object load held
    recurse into M's imports, re-export targets and callee modules (§7.6.1);
      never its lookup dependencies (§7.6.2)
    enrol M's written trait impls and declared children
    release M's object load            # on every exit path of the restore
  else:
    register M for a fresh typecheck

LoadObject(M) — run only by the holder of M's claim; claimable once M's load
is released, unclaimed and M has not failed:
  map M.o through cache::load_cached_object -> per-target addresses
  store each address in its GOT slot
  attach Code::Linker(shared Arc<Linker>) to each restored entry
  complete the claim: loaded, or failed with the load error

Step that runs compiled code (REPL expression turn, /run-tests, /run-all-tests;
--test's run_tests):
  wait until no cached object load is held, claimable or claimed
  if a cached object load has failed: report it and run nothing
  if shutting down with a load outstanding: report it incomplete and run nothing
  run
```

- **Tables before link; slot contents at run time.** Loading `M.o` binds each
  `__cranelisp_got_X` data symbol its code references to `X`'s GOT base, so
  `X`'s table must already be installed. The slot contents `X`'s own load or
  JIT fills may arrive later, because calls read another module's GOT at run
  time. Typecheck, fresh or restored, fixes each module's slot layout.
- **Table before readiness.** The decoded table installs before the scheduler
  registration, because that registration releases waiters that read it.
- **Restore before load.** The restorer holds `M`'s object load from `M`'s
  registration until `M`'s restore returns.
  - The walk restores every cache-hit dependency synchronously, so every table
    that `M.o` references through a walked edge exists when the hold releases.
  - The hold is scoped to the restore: every exit path releases it, including a
    failed dependency registration. A table still missing then fails `M`'s load
    loudly (*No swallowed failures*, below).
  - The walk borrows the hold, so the hold cannot be released before the walk
    returns. Binding it to an unused name would make that ordering depend on
    the binding's spelling.
  - Typecheck readiness keeps its position. Registration still releases
    signature waiters at once, and every reader sees the same scheduler state as
    before; only the load is deferred.
  - The walk never processes a cluster or waits on another module, so a hold
    always ends when its restorer's synchronous walk returns.
  - RR-1 face (i) was the unheld form: a worker claimed `a.o` between `a`'s
    registration and the walk's installation of its callee `c`
    (`tests/plan/s122-evidence-delta.md`
    [closing judgment](../../tests/plan/s122-evidence-delta.md#defects-and-questions-for-the-user)).
- **One load entry.** The scheduler grants a cached-object load only as a
  claim value that it alone can construct, and it grants none while the load
  is held. The object loader accepts only that value, so a load without a
  claim does not compile. The priority ladder's load item carries the claim;
  the macro recogniser obtains one by asking the scheduler (§6.8).
  - A claim request answers *claimed*, *loaded*, *pending* (held, or claimed
    elsewhere) or *unavailable* (not a cached-object state, failed, or
    shutting down). A caller that needs the object waits while the answer is
    *pending*, then asks again. After a hold releases it may take the claim
    itself; after another claimant's load ends it finds the object loaded, or
    the module failed. It never loads a second copy.
  - The wait is bounded: a hold ends with its restorer's walk, a claim with
    its load, and neither waits on another module's progress.
  - A claim ends exactly once. The loader completes it as loaded or failed.
    Dropping it uncompleted, including by unwinding out of a panicking load,
    fails the module with a load-abandoned error and wakes every waiter. No
    claimant, on any thread, can therefore strand a claim and hang a later
    wait. The scheduler failure is reported by the claim alone; the ladder's
    panic guard only keeps its worker alive. A failure completion acts only
    while the module is still claimed, so a claim that outlives a
    re-registration cannot fail the new registration. A loaded completion
    is not so guarded (*Claim and re-registration*, below).
  - The claim, the ladder's scan and the execution wait (below) read one
    classification of a module's cached-load state. A module that is not in a
    cached-object state, such as a fresh registration, is never *pending*.
    Whether a load is claimable depends only on this state, not on whether
    the module's object file is current.
  - A second concurrent load would also publish its own code owners over the
    first load's, dropping one mapping while GOT slots may still address it.
- **Load before execution.** A cache-restored module is typecheck-ready
  before it is in memory: registration publishes its signatures, and its code
  arrives only when its load ends. A fresh module is never in that state,
  because its in-memory notification precedes its typecheck-done transition.
  A REPL turn can therefore compile against a restored module whose load is
  outstanding, and its code then calls an unfilled GOT slot. That was RR-1
  face (ii)
  ([QA attribution](../../tests/plan/s122-evidence-delta.md#rr-1-face-ii--attribution-and-readiness-correction-evidence-2026-09-27)).
  - Before the REPL runs compiled code, it waits until no cached-object load
    is held, claimable or claimed. At shutdown it returns an outstanding load
    as incomplete, never as readiness. The steps that run code are an expression
    turn's execution, the `/run-tests` and `/run-all-tests` commands, and
    `--test`'s `run_tests` ([test runner §6.1](test-runner.md#61-prepare)). For
    the test runner, the wait precedes test discovery; an eligible test whose
    code is still absent is reported as a failure, never skipped.
  - Running code requires a readiness value that only this wait returns, so
    a REPL execution step that skips the wait does not compile.
  - The wait is global over cached loads, not scoped to what the turn can
    reach. It needs no enumeration of a turn's runtime reach, whose
    completeness (§7.6.1) is only asserted, and it covers every cache-hit
    entry (table below). A turn may wait for an unrelated outstanding load;
    that wait is bounded as above.
  - A failed cached load refuses the step: the REPL reports that module's
    load failure and runs nothing (*No swallowed failures*). Because the REPL
    does not know whether the step reaches the failed module, the refusal
    repeats on every code-running step while the failure stands. It stands
    until the module is re-registered, as when its source changes, until a
    failed-module reset forgets it (*Forgotten failed load*, below), or until
    the session restarts. Definition, import and introspection turns are
    unaffected.
  - The wait holds no symbol-table guard and no REPL check-state lock, because
    the loads it waits for take them.
  - `--run` already waits for every module before executing, which is
    stronger. The linked stub links statically and needs no wait. REPL and
    `--run` thus share one condition: no code runs before every cached load
    it could reach has ended (Principle 11).
  - Coverage by cache-hit entry. Every entry calls `try_cache_hit_load`, which
    registers the module, held, before it returns. A restore on the eval
    thread returns within the turn, before the turn's execution step. A
    restore on a pool worker returns inside the typecheck of the fresh
    dependency that reached it, which ends before the turn's typecheck can
    use that dependency's signatures.

    | Entry | Eval thread | Pool worker (fresh dependency) |
    |---|---|---|
    | `import` (`dependency::handle_import`) | covered | covered |
    | Qualified-reference autoload (`dependency::drive_module_dep`) | covered | covered |
    | `export` target (`dependency::handle_export`) | covered | covered |
    | `mod` and declared children (`dependency::enrol_declared_submodule`) | covered | covered |
    | Implicit prelude (`dependency::inject_prelude_if_needed`) | covered | covered |
    | Walk-nested restore (`cache_restore::register_cached_dependency`) | covered | covered |
    | Trait-home restore (`cache_restore::prepare_cached_trait_homes`) | covered | covered |

  - **Not covered (open residuals).** None is observed.
    - *Fresh work still in flight.* The wait does not cover a fresh module
      that a restore walk registered after a cache miss and that no turn has
      waited for. This is the execution half of the fresh-dependency residual
      below, and its falsifier covers it.
    - *Installed but not yet registered.* `try_cache_hit_load` installs a
      table before it registers the module. A second restorer of the same
      module in that window treats the table as satisfied (*Concurrent
      discovery is idempotent*, below). A turn could then execute before the
      first restorer registers the load. Falsifier: a face (ii) session on
      the corrected build whose module trace shows that module restored by a
      pool worker during the turn.
    - *Forgotten failed load.* Every failed-module reset (after a failed
      dependency wait, a failed code turn, or a failed load's
      record at startup or for `/mod`) also resets a failed cached load, but it leaves the
      module's table installed, because the module was once terminal. A later
      step then no longer refuses, and a call into that module can reach an
      unfilled slot. This predates RR-1. Falsifier: force a cached load
      failure, trigger a failing dependency wait, such as an import of a fresh
      module that imports the failed one, then call into the failed module.
    - *Macro clause execution.* The recogniser loads only the macro's home
      module. A clause that calls a function in another restored module with
      an outstanding load is outside this wait, and a pool worker cannot use
      it without claiming loads itself. Trigger: an aborted expansion or a
      crash in a clause that calls into another restored module.
    - *Claim and re-registration* moved out of this list: it is designed
      below (*A claim ends inside its registration*).
- **A claim ends inside its registration (designed S124, ACT-0994; not in
  source and not scheduled: deferred past S124 by the user).** Import turns
  do not wait for cached loads, so today a watcher reload can re-register a
  restored module while a pool worker's claim is still loading it. The stale load then stores GOT slots and publishes code
  owners into the table the reload's prologue has just installed, and its
  loaded completion marks the fresh registration in memory, so an in-memory
  wait covering that module can return before its fresh code is compiled.
  Not observed; it predates RR-1. Two rules close it, one per face:
  - *A reload waits out the cached load.* A module is settled for a reload
    only when no worker is mid-pass on it and its cached load is not held,
    claimable or claimed, the classification the execution wait reads
    (*Load before execution*). Every reload prologue already begins with the
    one settle wait, so the condition is added there and nowhere else. After
    the wait the load has ended or never existed, and nothing makes it
    claimable again short of a new cached registration, which an existing
    module never receives. No stale load can therefore reach the fresh
    table. The wait is bounded as the claim's is, and holds no table guard
    or check-state lock, because the load takes them.
  - *A loaded completion acts only while the module is still claimed*, as a
    failure completion already does. A re-registration leaves the module
    with no cached load, so a completion arriving after one changes nothing:
    the fresh registration is not marked in memory and its reservations are
    untouched. This binds the completion to its registration without a
    registration counter, because a module re-enters *claimed* only from a
    cached registration of an unregistered module. It also covers any
    re-registration path that a future change adds without the settle wait.
  - *Rejected:* stamping each claim with a registration generation and
    discarding a stale completion. It closes the completion face only; the
    stale load's publication into the fresh table would remain.
  - *Evidence, with `dev`(`src/`), at the scheduler module tier* (the window
    is one worker's in-flight load, which a process test cannot hold open;
    [S124 evidence delta §4.2](../../tests/plan/s124-evidence-delta.md#42-act-0994--no-public-reproduction)).
    (1) Register a module from cache, release its hold, take its claim,
    re-register it, complete the claim as loaded: the fresh registration is
    not in memory and its typecheck work stays queued. RED today, which
    marks it in memory. (2) With a claim outstanding the settle wait does
    not return; it returns once the claim completes. Today it returns at
    once. Negative legs: a fresh registration and a module whose load has
    ended settle at once. Neither row shows that a real session reaches the
    window.
- **Fresh dependency of a restored module (open residual).** When the walk
  registers a dependency fresh because its cache entry misses, that
  dependency's table need not exist when the hold releases. `M`'s load can then
  fail with an unresolved GOT symbol although the program is valid. `M.o` also
  embeds slot indices from the build that wrote it, and nothing yet shows that
  a fresh rebuild of unchanged source assigns the same ones. The slot half
  closes with the slot-layout key
  ([§7.6.3](#763-slot-layout-identity-act-1052)): a dependency that will be
  built fresh has no layout to match, so `M` misses. The table-existence half
  stays open.
  - Not observed. Falsifier: after a cold run, delete only `c`'s cache entry,
    then restore `a` warm in the REPL and under `--run`, and compare with
    `--no-cache`.
  - Holding the load until such a dependency leaves typecheck is not designed:
    it deadlocks when that dependency expands a macro homed in `M`.
- **Concurrent discovery is idempotent.** A dependency whose table is already
  installed, by a concurrent restore or the prelude preload, is satisfied
  without a re-read.
- **Generic-only modules have no object.** A module whose only definitions are
  slot-less templates writes no `.o`; its metadata restores and it registers with
  nothing to load. A missing `.o` with codegen targets is a miss.
- **No swallowed failures.** A restored callable whose address the `.o` does not
  define is a hard load error. A published NULL slot would be reachable from its
  callers.
- **A failed platform re-resolution is a cache miss.** If a recorded DLL cannot be
  loaded, the restore returns a miss and the caller takes the fresh path. The
  decoded table is already installed at that point. Nothing yet shows that the
  fresh path replaces it, or that a later handler does not take it as satisfied
  (§16.0).
- **Restoration parity.** A restored world must match a fresh one ([restoration parity](#75-restoration-parity)).
- **Assurance.**
  - *Structural:* the hold is released on every exit and spans the whole
    walk; every cached-object load holds a claim; every claim ends, including
    by unwinding; every REPL code-running step has passed the execution wait.
    Review confirms that the claim value and the readiness value have no
    constructor outside the scheduler.
  - *Measured:* a claim honours the hold and is exclusive; an abandoned claim
    fails its module and wakes a waiter parked before it; the execution wait
    waits for held, claimable and claimed loads, reports a failed one, and
    passes at once when none is outstanding. Scheduler rows with planted
    faults carry these. End to end, the RR-1 cell, its `c`-first sibling and
    the expression-turn cell show face (ii) as zero across QA's allocated
    sessions.
  - *Asserted, with the loader's unresolved-symbol hard error as falsifier:*
    every table that `M.o` references is reached by the walk (§7.6.1 *Risk*).

### 7.2 Backend entry points

- `compile_to_module` is generic over the Cranelift `Module`. It serves the JIT for
  fresh builds and the object module for the nice worker's `.o` and `--link`. It fills
  GOT slots and returns compilation artefacts. It never owns the `Arc<Jit>`; int
  attaches `Code::Jit` afterwards (§5.2).
- `cache::load_cached_object` maps a cached `.o` into a `Linker` and returns
  per-target addresses; int stores the addresses in the GOT and attaches
  `Code::Linker`.

### 7.3 Cache schema versioning (Decision 34)

The nice worker stamps `SymbolTable.schema_version` with backend's
`CACHE_SCHEMA_VERSION` on every write. On load, a version or build-id mismatch is a
`CacheStale` reason like any other: the entry is treated as missing, the module is
rebuilt fresh and the next write replaces the stale files. Staleness produces no
user-visible message. Backend owns the constant and its bump policy.

Per-module validity is backend's manifest check: the global keys, then the
module's own source hash, then its dependency record
([dependency record and validity](#76-dependency-record-and-validity)).

### 7.4 Linker retention

- Every entry restored from one `.o` holds a clone of the same `Arc<Linker>`; the
  mapped pages unmap when the last clone drops (§5.3).
- Cache-hit owner publication drops a displaced owner rather than pooling it. It is
  one of the two non-pooling paths `session-transaction.md` §6.1 names.
- Result drop-glue addresses follow the same rule as callable code. A fresh-JIT
  `DropGlueArtifact.jit_address` is usable only while paired with its
  `Code::Jit(Arc<Jit>)`; a cache-hit address from `Linker::get_symbol` only while
  paired with `Code::Linker`'s `Arc<Linker>`. The armed program-result owner carries
  the pair through display, exit conversion and the glue call. Linked startup needs
  no host `Arc`, because system-linked text stays mapped until process exit
  (`result-owner.md`).

### 7.5 Restoration parity

A restored module holds every relationship the fresh build holds. Each restore
step is the same call the fresh path makes, at the equivalent lifecycle point
(Principle 11). Do not add a cache-only parallel path. `try_cache_hit_load`
returns `Result<bool, CranelispError>`:

- **Miss, `Ok(false)`, falls through to a fresh build.** This covers:
  - a stale or absent manifest entry (§7.6);
  - every sidecar the backend decoder refuses as `CacheStale`
    (`design/backend/module-caching.md` §14.7);
  - a macro clause off the canonical ABI;
  - malformed trait-impl provenance;
  - an unrestorable trait home or platform.
- **`Err`, never downgraded to a miss.** This covers conflicting live state,
  such as a trait-impl record that diverges from its home's live occupant, and
  a failure in a dependency registration the restore recurses into.

| Relationship | Fresh path | Restore rule |
|---|---|---|
| Declared children | `dependency.rs::enrol_declared_submodule` after the parent's cluster commits | The same registrar, over the persisted `submodules`, after the parent table installs, so a child's `super` import sees it. Private and public children take one path, and an existing child is a no-op. |
| Trait impls the module wrote | The typecheck producer appends `WrittenTraitImpl` records (`design/arch/trait-impl-cache-carrier.md`) | Restore each foreign trait home first. After the writer table installs, re-enrol every record through the types-owned `enrol_written_trait_impl`. `Enrolled` and `AlreadyEnrolled` succeed; a divergence is an error, never a silent pick. An empty record vector is trusted as written: never default it, rescan the trait home or rebuild it from mangled names. |
| Module aliases | Session `ModuleAliases`, keyed by `cranelisp_types::module_alias_key` (`design/arch/module-alias-scoped-lookup.md`) | Rebuilt from the persisted `imports` and `submodules` by the same writers. The resolver in [§6.9](#69-bare-module-names-in-import-and-export) resolves each import alias's target. The map is unserialized session state, so aliases add no cache field. |
| Import and re-export targets | The resolver in [§6.9](#69-bare-module-names-in-import-and-export), over the cluster's declared children | The same resolver, over the restored table's `submodules`. The restore walk never reads a persisted bare spelling as an absolute module. |
| Monomorphic instances | `Concrete` entries in the demanding module's table, each with its `minted_from` link | Restored with that table; no separate step. |
| Platform functions | Platform load wraps the DLL's GOT (`design/arch/platform-interface.md` §6.4) | The persisted declarations re-run the same load; a failure is a miss ([cache-hit flow](#71-cache-hit-flow-inside-register_module)). |
| Lookup dependencies | Typecheck and the macro recogniser record into staging, and publication unions them into the table ([lookup dependencies](#762-lookup-dependencies)) | Restored with the table; no separate step. They are validity edges only, so restore loads none of them. A later compilation that needs one loads it on demand (`spec/08-modules.md` §8.5.4). |

The types crate defines lifecycle legality of a decoded table. The backend
decoder maps only an instance-key mismatch from `validate_lifecycle` to
`CacheStale`, and restore adds no further check. The restore path must not grow
an int-private copy of a lifecycle rule to close that gap (§16.0).

### 7.6 Dependency record and validity

A cached module restores only if every source its artefact was derived from is
unchanged. An importer's `.meta` and `.o` embed more than its dependencies'
declared signatures. They also embed GOT slot indices, ADT layouts, expanded
macros, monomorphic instances compiled from generic bodies, and types inferred
through the dependency. Any of these can change when a module deeper in the
graph changes, even though the direct dependency's own source does not.

- **The record is the transitive closure.** A module M's manifest entry maps
  every module reachable from M through its edges to the identity of the
  version M was compiled against: its source hash and, from S124, its
  authored slot layout ([§7.6.3](#763-slot-layout-identity-act-1052)). M
  itself is excluded.
  - Direct-import hashes alone are insufficient. In `c → a → b`, an edit to `b`
    can change `a`'s published types or slot layout while `a`'s source stays the
    same, so a restored `c` would use the stale interface.
  - Validating recursively through other modules' current manifest entries is
    also unsound: a rebuilt `a` rewrites its own entry to match the new `b`.
- **Edges.** A module's edges are:
  - every import spec, including alias-only and null imports
    (`spec/08-modules.md` §8.3.6–8.3.7), because qualified access still reads
    the target;
  - every re-export target;
  - every declared child;
  - the prelude, when the module's prelude-fallback bit is set;
  - every callee module: the storage home of each callable M's bindings
    call ([callee-module edges](#761-callee-module-edges));
  - every lookup dependency: each module whose table answered a qualified
    reference while M compiled ([lookup dependencies](#762-lookup-dependencies)).

  The restore walk loads a subset of these edges, the **load edges**
  ([cache-hit flow](#71-cache-hit-flow-inside-register_module)):
  - each import and each export whose names list loads, resolved through the
    module's declared children. The null-import rule is `names_load` in
    `src/imports.rs`, which every int reader of "does this spec load" calls:
    the Pass-0 handlers, the reload edges, the static closure, test
    selection and the restore walk. A name-less import or export is no load
    edge;
  - every callee module;
  - every declared child, which the walk enrols.

  The load edges exclude lookup dependencies and compiler-owned modules. They
  also exclude the prelude, which the injection loads when the fallback bit
  is on (§6.5) rather than the walk. As built at `42e6d929`, the set is
  composed inline in `cache_restore.rs::walk_restored_module`; no one
  function returns it. The reload edges (`dependency_record::reload_edges`)
  are a different set, with the prelude and lookup dependencies and without
  declared children. A consumer outside the walk, such as `arch`'s proposed
  traced-module set ([tracing §5.1](../arch/tracing.md#51-which-modules-a-form-covers--with-the-user-2026-11-18)),
  must not compose its own copy. When the user decides §5.1, the walk's
  composition moves into one crate-private enumerator in
  `cache/dependency_record.rs`, which the walk and that consumer both read.
  No consumer needs it before then.
  Define the edge set once (Principle 7). The fallback bit has one structural rule, shared by
  the restore environment and the index writer. Two kinds of module are
  excluded:
  - `primitives` and `macros`, which are compiler-owned and keyed by the build
    identity and compiler fingerprint;
  - platform modules (see *Known gaps* below).

  The edges are read from a module's table, except for the index writer. Its
  private table does not carry the structural declaration fields, so its edges
  come from the structural peel of the source it typechecked, plus the
  callee modules of its private table after typecheck.
- **Whole-source hashes.** Each member is keyed by its whole source, not by its
  interface. An importer's artefact contains code compiled from its
  dependencies' generic and macro bodies, so an interface hash would have to
  cover those bodies. Interface hashing remains backend's future optimisation
  (`design/backend/module-caching.md` §12).
- **Record from settled state (Principle 26).** A writer builds M's record when
  it writes M's manifest entry, from the versions this session loaded:
  - a member's hash is the one the session stashed when it loaded that module,
    whether by a fresh registration or a cache hit. It is never a re-read of the
    file at write time;
  - a restored member contributes itself and its own validated record. The
    writer does not walk the restored member's table, whose dependencies may
    still be building;
  - a fresh member's edges come from its live table, which is complete once its
    typecheck is.

  A member is unsettled if it is not loaded, not yet typechecked, or has no
  stashed hash. An empty or partial map is never recorded as a stand-in.
  - **Defer, retry once, then drop.** If any member is unsettled when M is
    written, M's entry is deferred. The deferred entries are retried once
    object codegen has drained, immediately before the manifest flush. An
    entry still unsettled then is not written. If M has no earlier manifest
    entry, the next session rebuilds M. Otherwise the earlier entry stays and
    still keys the rewritten `.meta` and `.o`
    ([rewritten restored modules](#762-lookup-dependencies)). The intended
    outcome is a miss or a sound hit, never stale service. §7.6.2 grades the
    retained-entry case.
  - **Why deferral is needed.** A declared child that imports `super`
    typechecks while its parent still waits on it, so its writer meets an
    unfinished parent.
  - **Prelude edge.** A prelude edge is dropped when the session holds no
    prelude table, because no prelude file resolved. Without this, no module
    of a prelude-less project would ever be recorded (*Known gaps*).
- **One builder, every writer.** Every manifest write builds its record with
  this one builder: the nice worker's object write, its no-object write
  (generic-only, types-only and imports-only modules), and the index worker's
  `.meta` write ([index-worker isolation](index-worker-isolation.md) §3). The
  index entry is keyed by the hash of the source the index typechecked. The
  index worker writes no loaded-source stash, because it loads no module.
- **Validation.** Validity is backend's `check_manifest`: the global keys, M's
  own source hash, and a current-hash map that int builds from exactly the keys
  M's entry records.
  - A member's current hash is the hash of the file that the loading handler
    would resolve for that path now.
  - A member that cannot be resolved or read is a miss.
  - Int's validity query takes a source of current hashes, not a caller-built
    map, so no int caller can run the dependency comparison over nothing
    (Principle 18).
  - Session cache state keeps each restored module's validated record for the
    builder. A fresh registration of that module supersedes it.
- **Compatibility.** The manifest's shape is unchanged. Its module-to-hash map
  holds the closure, which lookup dependencies enlarge. Callee-module edges
  read an existing persisted fact. Lookup dependencies add one persisted
  `SymbolTable` field to `.meta.json` under cache schema 30. Backend owns that
  bump (§7.3). A schema-29 sidecar is stale and its module rebuilds. Any new
  build identity already invalidates every older `.meta` and discards the
  manifest.
- **Known gaps.** Each open gap below can serve a stale artefact silently.
  - **Status.** Gap 1's correction is committed at `56e4d2e1` and reviewed,
    and QA judged the evidence adequate on 2026-09-26 (§7.6.2). Its
    empty-publication defect, LD-9, is corrected and reviewed in the uncommitted tree (§7.6.2.1). No user ruling accepts gaps 2–6; their disposition is
    open (§16.0). QA's evidence plan
    lists gaps 4 and 5 as unallocated accepted residuals. This design does not
    accept them on the user's behalf.
  - **Gap 7 (C-A)** is the only user ruling.

  The gaps:
  1. **Qualified references outside `callees`.** Before
     [lookup dependencies](#762-lookup-dependencies), only a qualified
     callable target was an edge. The user approved the carrier for the
     other kinds on 2026-09-26; §7.6.2 records int's half and its status.
  2. **Version conflicts in one closure.** The builder resolves a member
     reached both through a walked edge and through a restored member's record
     to the walked (loaded) hash. Between two restored records, the first one
     reached wins. The two hashes differ only after a same-session source
     change. When they do, recording the newer hash can let an importer
     restore next session against a restored member that was derived from the
     older version. A builder unit pins the rule as built; no end-to-end
     fixture is constructed.
  3. **Write-time stash reads.** The builder reads the stash when the entry is
     written or retried, not when the importer was compiled. The REPL's
     per-turn persist refreshes a module's stash. So an importer compiled
     before a redefining turn, but written after it, records the dependency's
     new hash. Falsifier: needs nice-worker ordering control, which no fixture
     has yet.
  4. **Same-session disk edit.** A dependency is edited on disk after this
     session loaded it, and a same-session importer then restores. The disk
     hash can then match a record written against the edited file while the
     live module is still the older version. Falsifier: in the REPL, edit
     `b.cl` without reloading it, then `/import` a cached `a`.
  5. **Platform signatures.** A platform DLL's manifest signatures change
     without a `.cl` edit. Falsifier: rebuild a DLL with one changed signature
     and check whether a cached importer restores.
  6. **Absent prelude.** A module cached while no prelude resolved records no
     prelude member, so adding a prelude later does not invalidate it. A
     prelude name that collides with an explicit import makes bare use
     ambiguous under a fresh build (`spec/08-modules.md` §8.8.1), so the
     cached run would wrong-accept. Falsifier: cache `a`, which uses bare `f`
     from `(import [u [f]])`, with no prelude; add a `prelude.cl` exporting
     `f`; compare with `--run --no-cache`. The stored format has no absence
     sentinel.
  7. **Corrupted or hand-edited cache content.** The user declined hardening
     (`tests/plan/s122-evidence-delta.md` §C-A).

#### 7.6.1 Callee-module edges

**Status: built; QA evidence adequate as a bounded correction (2026-09-25).**
The user approved this as a private correction. It reads the existing public
`SymbolTable` API and adds no public API, carrier, field or schema change.
Evidence and limits: [F1 acceptance](../../tests/plan/s122-evidence-delta.md#f1-acceptance-and-qr-classification-2026-09-25).

- **The fact.** Typecheck resolves each reference once. It records the
  terminal storage identity of each `Plain` or `TraitMethod` callable in the
  binding's `callees`; trait-method edges name the implementing module
  (`crates/cranelisp-typecheck/src/program/callees.rs`). `callees` is
  serialized on `Life::Template` and `Life::Concrete`. Every `.meta.json` and
  the index worker's private table therefore already hold it.
- **One enumeration (Principle 7).** `src/callee_edges.rs::binding_callees`
  is the one crate-private enumeration of a binding's callees across
  callables, overload arms and macro clauses, in template and concrete lives.
  Redefinition's blocking-dependent scan and the cache both call it; neither
  keeps a copy.
  - It is generic over the code store: redefinition reads live
    `Binding<Code>` values, and the restore walk reads the decoded
    `SymbolTable<(), ()>` before it is installed.
  - It sits outside `redefine` so that `cache` does not depend on it.
  - It enumerates a recorded resolved fact. It is not a scan for identity
    (Principle 24).
- **The callee-module set.**
  `cache/dependency_record.rs::callee_modules` gives the module of every
  enumerated identity in a table. It excludes the table's own module and
  compiler-owned modules through the filter every other edge uses.
- **Record consumers.**
  - `ModuleEdges::of_table` unions the callee-module set with the declared
    edges. The nice worker's writes and `build_dependency_record`'s walk of
    fresh members use this constructor, so the closure follows callee edges
    transitively.
  - `session_v4/index_worker.rs::index_typecheck_into_private` takes its
    declared edges from the structural peel. After the staged publish succeeds,
    it adds the callee-module set of the private module table. A failed index
    typecheck writes nothing.
- **Restore consumer.** `process_form/cache_restore.rs::try_cache_hit_load`
  loads each callee module.
  - `extract_cached_specs` extracts the set before the table is moved.
  - The callee walk runs after the import and re-export walks.
  - Imports, re-exports and callee modules share the per-dependency step
    `register_cached_dependency` (Principle 11). It skips compiler-owned
    modules, `prelude` and installed modules, resolves the file, tries a cache
    hit, and otherwise registers the module fresh.
  - The null-import skip applies to import specs only. A module that is both
    a null-import target and a callee is loaded, because the fresh build
    auto-loads it (`spec/08-modules.md` §8.5.4).
  - Callee modules are not carried as `ImportSpec` values, which would
    misrepresent them as imports.
  - The walk installs no names in the restoring module, as §8.5.4 edge 10
    requires.
  - A callee cycle stops at the installed-module check, as an import cycle
    does.
- **Unchanged.**
  - Explicit edges, their restore walks and the null-import rule for import
    specs.
  - The validated record is never used as the restore list: it is the
    staleness key, and it holds null-import targets that §8.3.7 never loads.
  - The builder's settlement, deferral and prelude rules (Principle 26).
  - The manifest and `.meta.json` shapes. This correction changed neither;
    lookup dependencies later add one `.meta.json` field (§7.6.2).
- **Failure direction.** An unresolvable or unloaded callee module makes the
  record unsettled, or makes validation miss. Either way the next session
  rebuilds the module. The correction can lose a cache hit; it cannot serve a
  stale one.
- **Redefinition.** `callees` is replaced when a body re-settles, so the
  edges follow REPL redefinition without over-approximating.
- **Risk.** `callees` completeness now gates cache validity and restore
  loading, as well as redefinition blocking. A missed callee becomes stale
  service or an unresolved GOT, not only a missed blocker.
- **Limits.** The correction covers only references recorded in `callees`.
  The five kinds in [lookup dependencies](#762-lookup-dependencies) stayed RED
  with unchanged faces. That measurement is not acceptance evidence for this
  correction.
- **Evidence.** Independent review accepted the change, and QA judged the
  evidence adequate ([F1 acceptance](../../tests/plan/s122-evidence-delta.md#f1-acceptance-and-qr-classification-2026-09-25)).
  - **Acceptance.** Both callable guards in `tests/cache.rs` failed for the
    intended reasons before the correction, and pass on the delivered source
    in `dev`'s full-suite run and `test`'s cache-target run. The `cache_dep_*`, restored-chain
    and CD-1 cells stayed GREEN.
    - `cache_fq_only_dependency_change_under_cached_importer_matches_uncached_run`:
      the cached run's exit code matches the uncached run after `b` gains a
      `defn` ahead of `f`. The code was 99 against 11 before the correction.
    - `cache_fq_only_dependency_change_not_imported_by_entry_matches_uncached_run`:
      the warm run restores `b`, which no import names. It previously failed
      with `unresolved symbol: __cranelisp_got_b`.
  - **`cache/dependency_record` units.**
    - The callee-module set covers every callable kind, in template and
      concrete lives. A decoded table yields the same set.
    - It excludes the module itself and compiler-owned modules.
    - A table without callees yields exactly its declared edges.
    - A fresh member whose only link to a module is a callee brings that
      module into the closure.
    - A callee module with no loaded source leaves the record unsettled.
  - **`index_worker` unit.** A module that reaches a loaded module only
    through a qualified call records that module among its edges.
  - **`redefine`.** The existing blocking-dependent units stay GREEN.
  - The restore walk has no unit tier; the second guard is its measurement.
    The null-import rule is fenced by FN-1, which runs its restore leg since the
    alias-only registration repair (`bc675d86`).
    The callee-cycle rule is asserted with a falsifier.

#### 7.6.2 Lookup dependencies

**Status: built at `56e4d2e1` (2026-09-26); reviewed with no blocking or
required finding; [QA judged the evidence adequate](../../tests/plan/s122-evidence-delta.md#adequacy-2026-09-26).** The int unit rows, the QR and LD
cells and one full suite pass on the delivered source. The LD-6 fault arming
was observed before the final lint edits; the LD-8 deferral trace was
re-observed on the final binary ([evidence plan](../../tests/plan/s122-evidence-delta.md#qualified-lookup-dependencies--evidence-delta-2026-09-26)).
Int adds no public API: it consumes the approved types recorder unchanged.
The user approved module-wide insert-only maintenance, the exact types API and
cache schema 30 (`sprints/archive/sprint-122.md` §"Lookup dependency implementation
approval — 2026-09-26"). [Qualified lookup dependencies](../arch/interfaces.md#qualified-lookup-dependencies)
defines the fact, carriers and maintenance. This section designs int's
producer, consumers and lifecycle within them.

- **Int's producer: qualified macro heads.** Typecheck records every other
  qualified kind. Int records the macro-head module (§6.8), for two reasons:
  - macro recognition runs before typecheck;
  - a head's expansion leaves no reference to the head's module in the
    expanded form.

  Int records the module after alias substitution, never the alias. It records
  nothing for `/expand`.
- **Attempt state until publication.** Expansion runs before the cluster's
  staging table exists. The recognised modules therefore accumulate in the
  cluster attempt, beside the expanded forms.
  - A dependency gap returns the already-expanded prefix as its continuation,
    and a retry does not re-expand that prefix (§6.2;
    `s117-conformance-recovery.md` §2.1). The accumulated modules therefore
    travel in the continuation.
  - The continuation is one value, the remaining forms plus the set. The
    pool worker, the eval retry loop and the redefinition re-check loop each
    store and return it whole. Its only empty-set constructor is the one for
    unexpanded source, so a holder cannot drop the set while keeping an
    expanded prefix without rebuilding the value from source.
  - A retry from the top starts empty, because its source is unexpanded. A
    gap after the attempt's final publication continues from empty source,
    because that publication already recorded the set.
  - A failure drops the attempt, so nothing unsettled is recorded
    (Principle 26).
- **Recording at publication.** Every staged publication an attempt makes
  records the attempt's accumulated modules into that publication's prepared
  staging after its check succeeds, through the types recorder. Live
  publication consumes that staging and unions the set into the table.
  - Recording follows the publication plan. The plan dry-runs publication on
    a cloned table map, which codegen reads; that clone lacks the recorded
    set. Neither the plan nor codegen reads lookup dependencies, so the order
    changes no outcome. A new reader of lookup dependencies between plan and
    publication must read the prepared staging, not the plan's tables.
  - **An attempt that owes a fact publishes.** The final check makes no
    staged publication only when the attempt owes the live table nothing.
    The owed facts are its checkable entries and its accumulated lookup
    dependencies. See
    [the empty-publication correction](#7621-empty-publication-correction).
    A whole-file rebuild owes nothing further: its fresh table already holds
    none of the prior generation
    ([session transaction §7.3.1](session-transaction.md#731-the-whole-file-rebuild)).
  - The finalize path without a session commits directly and records no
    macro heads. Only unit harnesses reach it; every production compiler
    context carries the session.

  Two kinds of publication exist:
  - **The final cluster check.** Every mode reaches it through
    `process_cluster_once`, so there is one site (Principle 11).
  - **Macro checkpoints** (`s117-conformance-recovery.md` §2.1). A checkpoint
    publishes before the final cluster and survives that cluster's failure.
    It therefore records the modules accumulated so far. This can include a
    module recognised for an unrelated earlier form. Module-wide granularity
    makes that harmless.
  - **Clause staging.** A checkpoint typechecks its clause bodies in a
    scratch staging table, then publishes a separately assembled table.
    Typecheck's lookup dependencies land in the scratch table, so the
    checkpoint must carry them into the published table with its retained
    instances. Otherwise every qualified reference in a macro body is lost.
- **Consumers.**
  - **One table-recorded edge set.** A table's recorded edges are its
    callee modules plus its lookup dependencies, filtered by the same edge
    rule as every other edge (own module and compiler-owned modules
    excluded). `ModuleEdges::of_table` and the index worker's post-publish
    step both take this one union (Principle 7). Recording is unfiltered
    apart from the types recorder's own-module rule, so a clause body records
    the compiler-owned `macros`; the filter belongs to the consumer.
  - The index worker expands no macros. Typecheck's records reach its
    private table through the same staged publication.
  - **Not a load, link or restore edge.** The restore walk, the object load
    and `--link` ignore lookup dependencies (§7.1, §7.5). A warm `--link`
    therefore omits a lookup-only module's object, while a fresh one includes
    it because the fresh compile loaded it. Nothing binds that object, so the
    difference is not observable.
  - **Not a redefinition blocker.** Blocking-dependent detection still reads
    `callees` only.
- **Table lifecycle.** Census of 2026-09-26 (production `src/`):
  - The session never removes or swaps a live module table.
  - A table starts in one of three ways:
    - empty, at first fresh registration, followed by a full compile;
    - decoded by a cache restore, carrying the persisted set of the compile
      that wrote it;
    - decoded by the REPL entry-slot preload, followed by a full compile from
      source.
  - A reload recompiles every form onto the existing table (`Replace`
    preserves slots). A REPL turn compiles its forms onto it. Both union into
    the set.
  - Consequences:
    - no path installs a table and then compiles only part of its module, so
      a table's set covers every form compiled into it;
    - within a session no set shrinks. A qualified reference dropped by
      redefinition or reload stays recorded;
    - a stale member costs misses only. It heals once a session misses the
      module's entry and compiles it onto a new empty table. The preload runs
      only on a valid entry, so it skips that session.
- **Rewritten restored modules.** A restored module's set can name a module
  this session never loaded, because restore loads no lookup dependency. If
  the module is rewritten, its record reaches that member and stays
  unsettled.
  - Rewrites include a REPL turn, the quit-time final persist and a
    dependent re-check.
  - The entry is deferred, then dropped. The earlier entry remains
    (§7.6, *Defer, retry once, then drop*).
  - **Defining turn.** The persisted source changes, so the earlier entry's
    own hash misses next session. The module rebuilds.
  - **Dependent re-check.** It follows a dependency whose source changed. The
    earlier record holds that dependency's older hash, so it misses.
  - **Expression turns and the quit-time persist.** Source and dependencies
    are unchanged, and the earlier entry was validated this session. It
    restores the rewritten artefact, which adds only session-local expression
    wrappers.
  - A module compiled on an empty table never reaches this state, because a
    qualified lookup answers only from a loaded table. A preloaded entry
    module reaches it only through a stale member, and the outcomes above
    apply.
  - **Accepted cost.** A defining turn in a restored module with a
    lookup-only member forces one rebuild of that module next session. No
    object is loaded to avoid it.
- **Assurance.** Grades follow QA's allocation, whose evidence QA judged
  adequate on 2026-09-26. LD-9 subsequently went RED to GREEN; its
  correction and required review repair are complete (§7.6.2.1).
  - **Carried across a gap.** *Measured* for the pool worker by the carry row
    and LD-6: seeding the resumed set empty turned both RED while LD-7 stayed
    GREEN. *Asserted* for the eval and redefinition holders, which hold the
    same value. Falsifier: a REPL turn expands an FQ macro head, gaps on an
    unloaded module, and the next session serves the old expansion after the
    head's macro changes.
  - **Macro heads recorded: asserted, with a named falsifier.** All compiling
    recognition passes through the one cluster recogniser, whose path QR-5
    and LD-6 measure. Falsifier: a qualified macro head expanded outside that
    recogniser whose home change leaves a cached run equal to the pre-change
    run.
  - **Retained earlier entry is sound.** *Measured* for the expression turn
    and the quit-time persist by LD-8, which passes on the delivered source.
    Its arming, the observed deferral of the restored module's entry, was
    re-observed on the final binary (see the evidence plan adequacy record).
    *Asserted* for the dependent re-check. Falsifier:
    a rewrite of a restored module that leaves its source and every recorded
    member unchanged, yet whose rewritten artefact executes code compiled
    against a module version its earlier record does not hold.
- **Acceptance guards.** One `tests/cache.rs` cell (`--run`) per kind was RED
  with its explicit-import sibling GREEN before this change
  ([QR classification](../../tests/plan/s122-evidence-delta.md#f1-acceptance-and-qr-classification-2026-09-25)).
  The type-only kind is a memory-safety exposure: a stale importer
  under-releases. A constructor-only home the importer's object does not bind
  already restored correctly (`cache_qualified_constructor_only_home_restores_warm`).
  LD-2 to LD-8 cover re-export chains, rewrites of restored modules, the
  load fence, warm spellings, the carry and clause bodies.

  | Kind | Guard |
  |---|---|
  | Re-export first hop (`b/f`, where `b` re-exports `c/f`) | `cache_qualified_reexport_first_hop_change_matches_uncached_run` |
  | Constructor, value and pattern positions | `cache_qualified_constructor_tag_change_matches_uncached_run` |
  | Dotted accessor | `cache_qualified_accessor_field_order_change_matches_uncached_run` |
  | Type-only reference | `cache_qualified_type_only_field_change_matches_uncached_allocator_counts` |
  | FQ macro head | `cache_qualified_macro_head_expansion_change_matches_uncached_run` |

- **Int unit rows** (submodule × scenario; Principle 23):
  - `cache/dependency_record`:
    - the table-recorded edges of a table carrying both callees and lookup
      dependencies are their union, without its own or compiler-owned
      modules;
    - a decoded table yields the same set;
    - a fresh member whose only link is a lookup dependency brings that
      module into the closure;
    - a lookup member with no loaded source leaves the record unsettled;
    - a restored member settles from its record without its lookup members
      being loaded.
  - `session_v4/index_worker`: a module that reaches a loaded module only
    through a qualified type reference records it among its edges.
  - `process_form`:
    - an alias-qualified macro head publishes the target module, not the
      alias;
    - a bare head publishes nothing;
    - a cluster whose check fails publishes nothing;
    - **the carry row:** an FQ macro-head expansion, then a later reference to
      an unloaded module (gap, then retry), publishes the head's module;
    - **the checkpoint row:** a qualified reference inside a macro clause
      body reaches the published macro table.
  - `expander`: `/expand` of a qualified macro head changes no table.
- **Rejected.**
  - *Walking schemes and concrete views for type and constructor homes*
    (formerly B1). It would enumerate one relation a second time, beside
    resolution's record (Principle 7).
  - *A session-side, unpersisted set of macro homes* (formerly C1). A restored
    module's rewrite would drop it, which is the original under-keying.
  - *Recording at recognition directly into the live table.* It would record
    from unsettled state. It would also write the table the recogniser is
    reading.
  - *Loading lookup dependencies on restore.* Validity needs only their
    hashes (the user's 2026-09-26 direction).
  - *Settling an unloaded member from the module's own earlier record.* This
    keeps a hit after a defining turn. It needs the earlier record retained
    past the source refresh, plus a second settlement rule. Build it only if
    the rebuild cost is measured to matter.
  - Optimisation-aware selectivity is
    [ACT-0992](../../sprints/actions/ACT-0992-optimisation-aware-cache-invalidation.md).

##### 7.6.2.1 Empty-publication correction

**Status: implemented and independently reviewed, uncommitted (2026-09-26).**
LD-9 and its allocated module evidence pass. The required R-1 correction
passed its finding-scoped re-review.

- **Regression (LD-9, RED to GREEN).** Before correction, `(b/m)` expanded to `(begin)`, leaving
  the cluster with no checkable entry and no reload demand. The final check
  returned no prepared publication. `finalize_cluster` dropped the
  attempt's accumulated set on that arm, so `a`'s entry was written without
  `b`. After `m` changes to expand to a `defn` that `main` calls, the cached
  run restores the stale `a` and fails, while the uncached run exits 99. The
  anchored sibling, where `a` also defines `anchor`, is GREEN.
  - Guard:
    `tests/cache.rs::cache_qualified_macro_head_with_empty_expansion_change_matches_uncached_run`
    ([allocation](../../tests/plan/s122-evidence-delta.md#post-checkpoint-qa-batch--db-1-r1-v-ld-9-and-citation-pass-h1h4-2026-09-26)).
  - The same arm drops the set for any expansion that leaves no checkable
    entry, such as one yielding only structural forms. An expansion yielding
    only macro definitions records through its checkpoint.
- **Correction: one publication decision over everything the attempt owes.**
  - The prepare step takes one decision, "nothing to check, yet something to
    publish", starting from an empty staging. Do not add a second one.
  - The attempt's lookup dependencies travel into the prepare step as the
    owed value. The value's own emptiness test is the whole no-publication
    condition. A fact later added to what an attempt owes joins that value,
    so the decision cannot omit it (Principle 7, Principle 26). The whole-file
    rebuild's established reference is a check input, not an owed fact, and
    does not join it.
  - The prepare step records the set into every prepared publication it
    returns, including the empty one. This replaces the caller's recording
    after the call, so the final check has one recording site. Recording
    still follows the publication plan; the note in §7.6.2 stands.
  - An empty publication with no targets builds no JIT. Its scheduler
    notification equals the one for no publication. Staged publication
    unions the set into the live table, as the
    [interfaces maintenance fact](../arch/interfaces.md#qualified-lookup-dependencies)
    requires.
  - An attempt owing nothing still makes no publication.
- **Unchanged.** Public API, the types recorder, the cache schema, the macro
  checkpoint's recording, the restore walk and every other mode path. All
  three modes reach this through `process_cluster_once` (Principle 11).
- **Grade.** *Structural* at the decision: the one emptiness test destructures
  the owed value exhaustively, so a fact added to it does not compile (E0027)
  until the decision names it. That an owed fact joins the value, and that
  its term is correct, rest on this design rule and the unit rows below.
  *Measured* by LD-9 and the positive unit rows observed RED then GREEN;
  the negative rows remained GREEN.
  - The REPL turn path shares the core, so it is *asserted*. Falsifier: a
    REPL turn `(b/m)` with an empty expansion, whose persisted module
    restores next session after `m` changes, differs from `--no-cache`.
- **Unit rows** (Principle 23):
  - `worker`:
    - a cluster with no checkable entry and a lookup set
      returns a prepared publication whose staging holds the set;
    - the same cluster with an empty set returns no publication.
  - `process_form`, beside the §7.6.2 rows: a module whose only form is an
    FQ macro head expanding to `(begin)` publishes the head's module. The
    negative leg is a bare head with the same expansion, which publishes
    nothing.
- **Rejected.**
  - *Record into the live table on the no-publication arm.* This bypasses
    staged publication, which the interfaces maintenance fact requires, and
    adds a second recording site.
  - *A caller-side empty commit in `finalize_cluster`.* This duplicates the
    prepare step's empty-staging arm and its decision (Principle 7).
  - *Always publish.* Imports-only modules and empty turns would pay a
    publication plan for no owed fact. It would also overwrite their
    unresolved-dispatch product. Neither cost is measured as acceptable.
  - *Synthesise a placeholder form for an empty expansion.* This invents
    source the program does not contain.

#### 7.6.3 Slot-layout identity (ACT-1052)

**Status: built at `3c4c0f7b`, with the backend's `CACHE_SCHEMA_VERSION` 34
and the `dependency_hashes` rustdoc correction at `f3f9cc47`; the stored
layout ends at a `.meta` rewrite at `c53a3f4b`; the shared decode that
repays its warm-start cost is built at `2d3a5b3e`, and the cost obligation
is closed (*Cost* below).** Private to `src/`. No
public API change: `CachedModuleRef::dependency_hashes` stays a map of opaque
strings and `check_manifest` is unchanged ([BC](../arch/bounded-contexts.md)
§6, the cached object's validity record). It changes what a persisted value
means, which the schema bump records.

**The fault.** An importer's object embeds the GOT slot index of each
callable it calls in a dependency. A REPL language-type change with no caller
gives the callable a fresh slot and retires the old one
([session transaction §7](session-transaction.md#71-the-commit-gate-is-the-single-slot-policy-authority)),
and the faithful write persists the moved layout (§8.2 there). A later edit
that restores the text leaves the dependency's source hash unchanged, so an
importer compiled against the old layout validates and calls a retired slot.
`qa` confirmed the mechanism with a control that differs only in whether the
slot moves (ACT-1052, K-6).

**The rule.** Each member of a record is keyed by its *derivation key*: its
source hash together with a fingerprint of its authored slot layout.

- **Authored slot layout.** The map from each codegen target of the member's
  table to its slot index, excluding minted instances (`minted_from:
  Some(_)`) and the synthetic `__expr`. This is the set another module's
  object can embed. The exclusion is the same ground on which the entry
  preload releases those slots
  ([session transaction §8.2](session-transaction.md#82-faithful-writes),
  "Why a release is safe"): one ground, two readers. Retired slots are not
  part of it; only live assignments are.
- **Writing.** The record builder keys each walked member, fresh or restored,
  by its stashed source hash and the layout of its live table when the entry
  is written. An inherited member keeps the key its restored record holds.
- **Validating.** The current key of a member is its current source hash
  (as today) and the layout of the version the session will link the
  importer against:
  1. the member's live table, when the session holds one: a terminal table,
     a restored table, or the entry after its slot preload;
  2. otherwise the authored layout of the member's stored `.meta`;
  3. otherwise none, which is a miss.

  A member still being built fresh holds an empty or prior-generation live
  table, so its key does not match and the importer misses. That is the
  sound answer, because fresh numbering is not shown to reproduce a stored
  layout (§7.1, fresh-dependency residual).
- **One current-key source.** Today's current-hash source becomes the
  current-key source, and every validity query goes through it: the
  dependency handlers' restore check, the index worker and the lifecycle's
  own query. No caller compares layouts itself (Principle 7).

**Why not the alternatives.**

- *Make slot layout a function of source.* Not possible without renumbering
  live slots, which cached objects and frozen code embed (§8.1 there).
- *Invalidate importers when a module's layout moves.* A sweep of the
  manifest at write time would cover this face, but it is a second mechanism
  beside validation, it acts only at the next flush, and it cannot see a
  dependency rebuilt fresh with different numbering.
- *A typed layout field on the manifest.* Returns to `arch`'s gate and buys
  nothing the opaque key does not.

**Cost.** `dev` measured an exemplar warm `--run` (debug) at about 0.96 s
before the change and 1.23 s after it. A rise of over a quarter on the path
the cache exists to make fast is material.

- **Attribution** (`dev`'s profile of a warm debug `--run
  exemplar/tests.cl`). The run made 37 cache checks over 1,030 member keys,
  in about 400 ms.
  - The stored half takes about 300 to 308 ms: 36 decodes of a member's
    `.meta`, made only to read its layout.
  - The modules' own restore decodes the same files again, about 302 ms in
    35 decodes. That cost predates the change.
  - The live half, fingerprinting loaded members, takes 7 to 8 ms.
  - Re-reading and hashing source takes about 90 ms, which predates the
    change.

  The added cost is therefore a second decode of a file the session decodes
  anyway.
- **The remedy: one decode per stored `.meta`.** `ObjectCache` holds the
  decoded stored module, not only its layout. Validation's rule 2 reads the
  layout from it, and the member's metadata restore takes the same value
  instead of reading the file again. The held value exists only while the
  session holds no table for the member. It ends when the session first
  holds a table for the member, whether by that restore or by a fresh load,
  and when its `.meta` is rewritten (`ObjectCache::write_meta`, as built at
  `c53a3f4b`). Validation reads a live table whenever one exists (rule 1),
  so it never needs a held value after that point. Correctness never depends
  on the hold, because a missing value is decoded from the file. It uses the
  backend's public `try_load_cached_module` and `CachedModule` unchanged, so
  it is private to `src/`. It changes no persisted value, no schema and no
  public item.
- **Why this meets the bar.** Validation and the metadata restore share one
  decode per restored member, so the decode the change added is gone. What
  remains of the added cost is the live half, 7 to 8 ms, which is not
  material. The live half therefore gets no memo.
- **Measured at `2d3a5b3e`** (`qa`, four warm debug runs of `--run
  exemplar/tests.cl`): 0.89 to 0.94 s, against 0.96 s before the change. The
  bar is met.
- **The object load's decode is not part of this obligation.** A restored
  member is still decoded twice: once for validation and its metadata
  restore, and once more when its object is loaded
  (`worker.rs::load_cached_module_via_linker`, 33 of 70 decodes on that
  run). The second read predates S124, so it is in the 0.96 s baseline; the
  attribution above omitted it. No requirement or bar asks for it, so the
  design asks for nothing further.
  - *Potential extension.* The object load takes the facts it needs from
    the decode the metadata restore already took, or from the restored
    table, instead of reading the file again. *Trigger:* a warm-start
    requirement, or a profile in which that decode is the largest share of
    a warm start the project wants faster.
- **Not taken: a manifest self-key.** Recording each member's derivation key
  in its own manifest entry would remove validation's decode, but the
  member's restore would still decode the file. It saves a decode only for a
  member that validation reads and the session never restores: one in 36
  here. It needs a schema bump in `dev` (backend) and a change to the rule
  "the module itself is never a member". *Trigger:* a profile in which
  validation decodes a material number of members that are never restored.
- **Falsifier.** With the shared decode, the warm start stays materially
  above 0.96 s, or the profile shows more than one decode for a restored
  member outside its object load. The cost is then elsewhere and is profiled
  again. Neither was observed at `2d3a5b3e`.
- **What `dev` builds** (`src/cache.rs`, `src/process_form/cache_restore.rs`).
  The held decoded module in place of the held layout, the take at the
  metadata restore, and the end when the session first holds a table.
  Module rows:
  - a validation followed by the member's restore decodes the file once;
  - a rewrite between them makes the restore read the new file;
  - a member loaded fresh after validation holds no decoded value;
  - `a_stored_meta_overwrite_is_read_by_the_next_validation` stays green.

**Constraints for `dev`.**

- A live-table read during validation takes a read guard on the member's
  table only, and never while the caller holds a mutable guard on the same
  map shard.
- The key's string form is private. It must not be equal to any
  source-hash-only string, so a record written before the change is a miss
  even without the schema bump.

**Gaps it does not close.** §7.6's gaps 2 and 3 apply to the layout half as to
the hash half: a write-time read can record a layout the importer was not
compiled against. *Falsifier for the rule as a whole:* another derived fact
that a REPL increment can change while the source text returns to an earlier
version, observed as a stale restore whose members' keys all match.

**Evidence (for `qa`).** K-6 and its control in `--run`, `--link` and the REPL
`/mod` leg. Unit rows: a layout move with an unchanged hash makes a record
stale; an unchanged layout and hash keeps it valid; a minted instance or
`__expr` slot change does not invalidate; a member with no live table and no
stored `.meta` is a miss; a member being built fresh is a miss; an S123-era
record is a miss.

---

## 8. REPL flow

An executed `EvalResult::Val` is an ownership-bearing result, not a freely
copyable display tuple. REPL formatting observes the live value completely and
then consumes its armed owner, invoking canonical type glue exactly once for an
owning result. Definition/bare-symbol display does not fabricate ownership. IO
unwrapping occurs once at the program-driver boundary; the formatter has no
private IO-result release path. See `result-owner.md` §§2, 4.2, and 4.4.

### 8.1 Eval cursor + defn_order append

Per `facades/int.md` invariants 9 + 10: definitions append to `current_repl_module` (not `user`); `Sess::eval` for a defining form calls `Sched::append_form(current_repl_module, sexp)` and waits for that single symbol's typecheck + jit. The whole module is NOT re-typechecked.

`SymbolTable::append_defn_order(&mut self, sym: Symbol)` — brief per-eval `&mut SymbolTable` window (microseconds). The same shape as Phase 0; the only other `&mut SymbolTable` operation. `defn_order` records canonical first-registration ordering; redefinition replaces in place, preserving original position. (Per Decision 39.)

### 8.2 Introspection populate (Decision 38, mode-conditional)

After `process_form` succeeds for an eval, when `shared.introspection.is_some()`:

```text
introspection.insert(fq, Introspection {
  source: Some(eval_text),                     // for REPL evals; for file-based modules, sliced from file Arc<str> at parse-time
  sexp: Some(expanded.clone()),
  clif_ir: ...,                                // populated post-codegen in worker (Decision 41 — backend writes directly)
  code_size: ..., compile_duration: ...,       // populated post-codegen in worker
  // NB: no `disasm` field — derived on demand (§4.3, §8.2.1)
})
```

Production batch (`shared.introspection == None`) skips the populate path entirely.

### 8.2.1 `/disasm` — on-demand disassembly (Decision 41)

`/disasm <name>` does NOT read a stored field. The handler
(`src/repl/commands.rs::handle_disasm`) re-derives the disassembly at the keystroke:

```text
handle_disasm(name):
  if name empty            -> usage line
  fq = FQSymbol { module: current_module_path(), symbol: name }   // same resolution as /clif's get_introspection
  code_size = introspection[fq].code_size                          // captured at codegen
      else -> "Error: no disassembly available for '<name>'"       // not compiled / no metadata
  match cranelisp_backend::produce_disasm(&fq, code_size, &shared.symbol_tables):
    Ok(text) -> "; disasm for <name>\n{text}"                      // header + capstone lines
    Err(_)   -> "Error: no disassembly available for '<name>'"     // slot empty / not compilable
```

Design points:

- **`produce_disasm` is ALREADY public** (`crates/cranelisp-backend/public-api.txt`;
  def `crates/cranelisp-backend/src/lib.rs`). The S87 fix is pure wiring at the
  int boundary — **no backend surface change, no `cranelisp-types` edit**
  (/arch Phase-2 confirmed: no interface delta).
- **`code_size` is the bridge.** `produce_disasm` requires the caller to supply
  `code_size` (the backend does not persist it; §"The caller supplies code_size"
  in `lib.rs`). int already captures `code_size` eagerly into the introspection
  record (`worker.rs` step 7), so the handler reads it from there and forwards it.
  A name with no `code_size` (never compiled, or batch mode with no introspection
  map) yields the graceful "no disassembly available" line — same shape as the
  other introspection handlers.
- **Symbol-table lookup is backend-side.** `produce_disasm` itself resolves the
  GOT slot from `shared.symbol_tables` and reads the live code bytes; int hands
  it the `FQSymbol` + `code_size` + a `&DashMap` of the symbol tables. The
  module of `fq` is the current REPL module (identical resolution to `/clif`'s
  `get_introspection`), so `/disasm` and `/clif` resolve the same symbol.
- **Why not eager?** See the §4.3 disasm note — disasm is the most expensive
  metadata and rarely read; deriving it on the keystroke keeps every REPL eval
  cheap (Principle 6 — complexity has a budget; the production-batch path pays
  nothing, the REPL pays only when asked).
- **Contrast with `/clif` (the working sibling).** `/clif` reads the eagerly
  captured `intr.clif_ir` (cheap to capture, captured at codegen). `/disasm`
  cannot mirror that path because no `disasm` field is populated — and per
  Decision 41 it SHOULD NOT be. `/disasm`'s correct shape is the re-derivation
  above, not "populate the field too."
- **Vestigial accessor.** `CompilerSession::symbol_disasm()` reads the dead
  `intr.disasm` field; it has no correct caller after this rewire and should be
  removed alongside the field (§4.3 historical note). `/dev` removes both in the
  same change-set or leaves a one-line `// dead — see int.md §4.3` if removal is
  scoped out; the design intent is removal.

This closes the S86 ledger guard `disasm_command_shows_native_code_for_compiled_fn`
(spec: `repl/spec.md §3.1`).

### 8.2.2 `/info` macro card — clause-count line (`repl/spec.md §11.2.2`)

`/info <macro>` renders through `format_def_entry` → `format_macro_display`
(`src/repl/format_type.rs`). Per `repl/spec/11-macro-introspection.md` §11.2.2 the macro card MUST, for a
**multi-clause** macro, emit a clause-count summary line after the per-clause
signature lines:

```
:user/cond ; defmacro - Multi-way conditional
; [x] -> Sexp
; [x body & rest] -> Sexp
  2 clauses
```

Current `format_macro_display` emits the `:module/name ; defmacro` line, the
docstring comment, and one `; <params> -> Sexp` line per clause — but NOT the
count line. That omission is the S86 ledger guard
`info_multi_clause_macro_shows_clause_count` (spec: `repl/spec.md §11.2.2`).

Design points:

- **Rendering home is `format_macro_display`.** The clause count is computed
  from the same `clauses: &[MacroClauseInfo]` slice the renderer already
  iterates — `clauses.len()`. No new data is needed; `clauses_meta` is already
  carried on the `DefKind::Macro` entry, so the count datum is available — this
  is a rendering gap, not a data gap.
- **Format: `  N clauses`** — two leading spaces, no `;` prefix (it is a summary
  line, not a comment line), matching the spec worked example exactly. Append it
  as the final line of the returned string.
- **Gate on `clauses.len() > 1`.** The spec's single-clause worked example
  (`/info when`) shows NO count line; only the multi-clause example carries it.
  Emit the line only when there is more than one clause. (Pluralisation is moot
  under this gate — the count is always ≥ 2, so a fixed `"clauses"` is correct;
  no `clause`/`clauses` branch needed.)
- **Scope: `format_macro_display` only — do NOT touch `/sig` or bare display
  divergently.** `/sig` renders macros through a *different* path
  (`format_entry_sig`, NOT `format_macro_display`), so it is unaffected and its
  `[Tested]` guards (`bare_macro_lookup_shows_clause_signature`) stay green.
  `format_macro_display` is ALSO reached by the bare-`defmacro` display
  (`format_def_entry` at the eval-result site) and `/info`; both existing guards
  there (`defmacro_display_single_clause`, `defmacro_display_multi_clause`,
  `bare_macro_lookup`) assert with `contains`, so appending the count line to a
  multi-clause macro is non-breaking. The single-clause guards never trip the
  `> 1` gate.
- **No interface delta.** Pure int-side rendering; `clauses_meta` already on the
  symbol-table entry. /arch Phase-2 confirmed no `cranelisp-types` change.
- **Resolver split.** This is the `/repl` half of the Stage-A pair (the spec
  format question is `/repl`-owned: `repl/spec.md §11.2.2` is the normative
  contract); the rendering lives in `src/` (the `/int`-owned surface). See the
  Phase-4 wave note below on whether the two src/ fixes are one `/dev`
  invocation or two.

### 8.3 `regenerate_backing_file` (Decision 39)

Regeneration renders the module's structural fields and each selected entry's
authored-form introspection record, rehydrating missing records from the
backing file first. It writes nothing if any selected entry has no authored
form. [Session persistence §§1–2](session-persistence.md) owns the sections,
record writers, rehydration and refusal. Introspection is the only store of
per-definition authored text; the cache metadata carries none
([Session persistence §2.4.2](session-persistence.md#242-backing-file-rehydration)).
Cited principle: P7.

### 8.4 Watcher integration

Per `facades/int.md` invariants 7 + 8 + bounded-context §6.2:

1. REPL startup loads the entry module and waits for every registered module's in-memory readiness before the first prompt. Afterwards, a REPL step waits only for outstanding cached loads, and only before it runs compiled code ([load before execution](#71-cache-hit-flow-inside-register_module)).
2. `set_repl_input_active(true)` opens the watcher window during `read_line`; `set_repl_input_active(false)` closes on input submission.
3. Watcher events do NOT flow directly into compilation. They cross to the REPL cadence at a poll point and become one reload plan: each changed module and its dependents is rebuilt whole from its saved file, in dependency order ([REPL lifecycle §1.2](repl-lifecycle.md#12-poll-and-reload); [session transaction §7.3](session-transaction.md#73-the-watcher-and-reload-path)).

`watch.rs` owns the `notify`-based watcher and the `WatcherChannel` mpsc. The REPL polls at prompt boundary; the prompt-window mechanism is the closure that prevents mid-input watcher interleave.

### 8.5 Slash commands — composed flows over the existing primitives

Per `facades/int.md` §"Composed introspection flows": slash commands are composed flows over `CompilerSession` accessors and other facade calls — not new facade surface. The 17 commands (`/sig`, `/doc`, `/help`, `/type`, `/info`, `/source`, `/sexp`, `/ast`, `/clif`, `/disasm`, `/time`, `/mem`, `/list`, `/imports`, `/exports`, `/expand`, `/mod`, `/reload`, `/run-tests`) all dispatch through `Sess::process_commands`, which decodes the input into a `SlashCommand` enum and either reads the introspection store directly (`/source`/`/sexp`/`/clif`/`/disasm`/`/time`), composes a frontend / typecheck call (`/expand`), or composes a runtime-side primitive (`/mem`, `/run-tests`).

Universal output format (Sprint 14): `:Type {value|name} ; {classification} - {docstring}` + optional related symbol comment lines. Defined in `repl/spec.md`; implemented across `Sess::format_*` family.

#### 8.5.1 `/mod` target

Status: **designed 2026-09-29** (ACT-1010 M2, NAV-1). Private to `src/`.

**Rule.** `/mod <name>` switches only to an existing module and never creates
one. A module not yet loaded is loaded by the switch. An unknown name reports
an error naming it and leaves the current module unchanged
(`repl/spec/03-slash-commands.md` §3.9; `repl/spec/08-module-demos.md`,
Scenario 7). The user ruled on
2026-09-29 that `<name>` is read by the language's module-name resolution,
with that code shared; `spec` records the ruling in
`repl/spec/03-slash-commands.md` §3.9. Bare `/mod` returns
to the entry module.

**Flow.** `/mod` adds no resolver and no loader of its own:

1. **Resolve.** Read `<name>` from the current module through the one
   bare-module-name resolver (`imports::DeclaredChildren`, §6.9), built from
   the current module's declared children. A declared submodule `M.name`
   therefore wins over a root module `name` (spec §8.11.2.1); a dotted name is
   absolute.
2. **Loaded.** If the session holds a table for the resolved module, switch
   to it. A cache-installed generation is first recompiled from source
   ([session persistence §2.4.5](session-persistence.md#245-editing-a-cache-installed-module)).
   A module standing failed is loaded: `/mod` switches, and the session
   lock refuses code turns in every module.
3. **Search.** Otherwise locate its file with `pipeline::resolve_module_file`,
   the root-then-lib search every `import` and qualified reference uses. No
   file reports `Module '<name>' not found.` through the error line; the
   current module and the set of tables stay unchanged.
4. **Load.** Otherwise load it through the language's load-on-reference: the
   dependency drive a qualified reference at the prompt runs
   (`drive_module_dep`, §6.2), then the eval thread's wait
   (`register_dep_for_eval`). The wait ends when the module's in-memory code
   is complete, not at its publication, because the switch makes it the
   module turns publish into ([§6.11](#611-module-cycles-at-publication),
   *`/mod` is not a declaration read*). Build the eval thread's `ModuleCompiler` once
   for `eval.rs` and `/mod`; do not add another inline construction. A
   cache hit takes step 2's recompile. On success, switch; `sync_watcher`
   after the turn watches the file (REPL §14.1). On failure, report the load
   error, the chained §8.5.4 edge-5 diagnostic, and do not switch. The
   failed load's record
   ([REPL lifecycle §1.3.1](repl-lifecycle.md#131-session-lock)) then
   resets only the modules this load left `Failed`, records each one that
   failed in its own source in the failed set, which locks the session
   (REPL §3.9, §14.5), lets each one a dependency refused wait, and purges
   the never-compiled tables, so no phantom remains.

**Structure.** `set_current_module` no longer creates a table: `/mod` is its
only production caller and reaches it only with a loaded module, so the
current module always has a table without a create-if-absent. The
`install_module_session_env` call in `handle_mod` existed for the blank table;
a loaded module already carries its session environment from its load or
restore, so the call is removed once the rows below show that environment
unchanged.

**Consequences.**

- A startup-failed dependency has no table after recovery
  ([REPL lifecycle §1.3.1](repl-lifecycle.md#131-session-lock)), so `/mod` to
  it loads it, reports its failure and stays put. It still stands failed,
  and its file stays intact.
- A module loaded from a file this way is compiled from source this session,
  so regeneration writes every definition the file held.
- Loading a module that stood failed and whose saved file has since been
  fixed, before the watcher polls, compiles it while it still stands
  failed. The next poll's reload of that file removes it from the failed
  set.

**Module evidence (`dev`).**

- `handle_mod` on an unknown name returns the error naming it and leaves the
  current module and the set of tables unchanged.
- On an unloaded file-backed module it loads the file and switches; the
  module's definitions resolve.
- A declared submodule wins over a root module of the same name.
- On a file that fails to compile it reports the error, stays put, leaves
  no table and leaves the module standing failed; the session-lock rows
  are [REPL lifecycle §1.3.2](repl-lifecycle.md#132-module-evidence-dev).

End to end: NAV-1, NAV-2 and the six NAV-3 fixture repairs
([navigation](../../tests/plan/s122-evidence-delta.md#mod-navigation-nav-1nav-3));
`tests/repl_persist.rs::persist_mod_definition_keeps_dependency_source_failed_at_startup`
stays green.

### 8.6 Live redefinition — guarded publication and slot versioning

`repl/spec/18-redefinition.md` §18 is normative: a replacement is fully checked
and compiled before live state changes, and an ordinary callable redefinition
never recompiles a dependent, marks a symbol broken or installs a trap. Int
realizes it inside the ordinary prepared transaction:

- the guard rejects a declaration-class or visibility change and a
  language-type change with a blocking dependent; inferred ownership modes are
  not compared ([session transaction §2.4](session-transaction.md#24-ownership-modes-are-not-compared));
- an admitted generic base or overload family rematerializes its prior
  concrete instances into the same candidate (`design/int/s122-closure.md` §2);
- the commit gate's `RedefKind` decides slot reuse versus a fresh slot, and
  every displaced compiled owner enters the session retention pool.

A reload of a saved file is not a redefinition: it is a whole-file rebuild
whose only redefinition check is the §14.8 type boundary.

Full design: **`session-transaction.md`**. The S102 persistence and dev-loop
cures it relies on are in **`s102-defect-wave.md`**.

---

## 9. Error formatting (Decisions 39 + 42)

`Sess::format_error(&self, err: &CranelispError) -> String` is the integration-layer formatter. It resolves `ErrorLocation` against the current mode and chooses a display strategy:

| Available | Strategy |
|---|---|
| `ctx` (inline snippet) populated | Use it directly — parser path is self-contained |
| `fq` populated + introspection enabled | Look up `shared.introspection[fq].source`; slice using `line_col` for inline rich display |
| Neither (production batch) | `file:line:col: error: message` style |

REPL display path AND production batch CLI display path call this — one formatter, mode-conditional input. Cited principle: P11 (single pipeline — error formatting is one path with mode-conditional input, not separate REPL vs production).

**Error variants formatted**:
- `CranelispError::Parse` / `Reader` / `Expansion` / `Type` / `Codegen` — go through the `ErrorLocation` resolution path above.
- `CranelispError::Platform(PlatformError)` — per Decision 42, post-FIXME 0104. Each variant carries `ErrorLocation`. `format_error` adds a `Platform(PlatformError)` arm using the same mode-conditional source-resolution path. The `(platform "name")` form's span flows into the `location` field at the load call site.
- `CompilationError` (from backend, post-FIXME 0100 Phase 2) — variants like `SymbolNotCompilable` carry `ErrorLocation`; same path.

`Warning` carries the same `ErrorLocation` shape; `Sess::format_warning` (or the same formatter, type-dispatched) handles the warning case uniformly. Cited principles: P5 (testability — error structure is permissive data, formatter is policy layer; both independently testable), P7 (single formatter).

### 9.1 The compiler-stage SUBJECT is presented, never carried — RULING (S119, FIXME 0915 item 4)

`/qa` split FIXME 0915 (S118 P6 close): items 1–3 (the doubled located prefix,
`user/user/…`, and the `0..0` span) are backend frame-composition defects; item 4
— **the subject presentation** — is int's, and this is its ruling.

Two spellings reach the user that never should
(`repl/spec/05-error-presentation.md` §5.5):

| Seen | What the user wrote |
|---|---|
| `codegen failed for user/__expr: …` | the expression they just typed |
| `codegen failed for user/user/then$primitives/IO$Int+primitives/IO$Int: …` | `then` |

**Ruled: int rewrites the SUBJECT at the display boundary; the carrier is never
touched.** This is Decision 39 applied unchanged — coordinates and identities
travel as data, formatting happens downstream in int — and it is why the fix is
not "stop naming the instance in the error". The `Symbol` backend put in
`CompilationError::CodegenFailed` is **correct data**: it is the compilation unit
that failed, it is what a `/clif`/`/disasm` probe takes, and it is what a future
cache or attribution reader keys on. Only its *rendering to a human* is wrong.

Three normative statements:

1. **One subject-presentation function, in `format_error`'s neighbourhood, and
   nowhere else.** It maps a compilation subject to the name the user would
   write: `__expr` → the entered form (or the neutral phrase "this expression"
   when no form text is available); a monomorphised instance
   `f$T1+T2` → its base `f`; an already-qualified symbol → itself, not
   re-composed. **It is a presentation projection, not a resolver** — it must
   never look a name up, and it must never become a second home for the
   `$`-mangling scheme. The mangle's canonical home is backend/types; int reads
   the projection inverse only (the `bare_member_name` precedent,
   `dotted-ctor-canonical-keys.md` §10.4).
2. **It applies at `Sess::format_error`, once, for every error variant that
   carries a compilation subject** — not at the `CompilationError` `Display`
   (that is backend's and is items 1–3), and not per-command. §9's table already
   makes `format_error` the single mode-conditional formatter for REPL and batch
   alike; a per-site rewrite would be the `display-envelope-mirror` class.
3. **Presentation must not erase the investigative handle.** Where the internal
   subject is the only way to reach the failing artifact (`/clif`, `/disasm`),
   the projection may render the user-facing name and keep the internal spelling
   available in the same diagnostic — but as a *labelled* secondary, never as the
   headline noun. The self-documenting-REPL principle is that the diagnostic's
   central noun must be actionable at the prompt; `then` is, `user/then$…` is not.

**Sequencing.** Items 1–3 change the string int receives; item 4 changes how int
renders the subject inside it. They are independent in mechanism but **the guard
is shared**: every currently-reachable e2e trigger for this frame is FIXME 0907's
refusal, so a guard authored against it dies when 0907 lands. `/qa` has deferred
the §5.5 frame guard to be authored in the 0907/0903 fix window against whatever
codegen-refusal trigger remains. Int's rider rides that guard; it does **not** get
a private one keyed on 0907's message text.

**Non-goal.** The `Bind`/`IO` undiscoverability the FIXME calls "the sharpest
part" is 0907's (they are seeded by `src/bootstrap.rs`, which is why `Pure`
introspects and `Bind` does not). It is recorded there and is not this rider.

---

## 10. Concurrency model

This section is an overview; the structural diagrams live in `design/int/concurrency/` (target-state, scheduler-lifecycle, dependency-protocol-target, symbol-publication-target, compilation-cadence-batch-run).

**Shape** (from `facades/int.md` §"SharedState" + Decision 38):
- Workers spawn only after fallible bootstrap inside `CompilerSession::new` has
  produced the complete seed world; each receives its own `Arc<SharedState>`
  clone (refcount bump). They live for the session — never per-call
  `thread::scope`. Joined on `Drop` via `WorkerPool`.
- `take_priority_work_blocking` parks workers on a condvar inside `CompileScheduler`; wakeups come from `enqueue_jit` / `register_module` / `notify_*`.
- A worker that hits a dependency gap returns to the pool and its module is requeued; only the REPL eval thread and the whole-session initiator wait on readiness (§6.2).
- The IO trampoline forks Par nodes onto rayon (rayon pool size from `SessionSettings`).

**Invariants**:
1. Workers never see `&mut SharedState` — only `&shared.*`. All mutation through interior mutability of contained types.
2. Per-symbol mutability discipline (§4.1) — no whole-module `&mut SymbolTable` after Phase 0.
3. Scheduler is *the* coordination authority — there is no separate `DependencyService`. The runtime/platform diagrams' merge of work-dispatch + wait/release into one structure is binding.
4. One orchestrator per module: a module is claimable or owned, never both, and in-progress cluster state stays on the owner's frame (§6.2 and Invariant SW in `signature-body-prepass.md`).
5. GOT slot writes are atomic-Release; reads are atomic-Acquire (Decisions 31 + 23). REPL redefinition retargets atomically before the old `Arc<Jit>` can drop.
6. A mutual import is a deterministic cycle error at the import site, not a deadlock (§1 constraints; §6.2).

The audit's F4 (worker orchestration split across files) collapses under the target shape: priority + nice loops both live in `worker.rs` (or `workers/` subtree); scheduler state in `scheduler.rs`; `SharedState` in `session_v4.rs`.

---

## 11. Observability — three ring buffers + introspection

The observability surface has four sinks, all int-owned. `observability.md` is
the canonical carrier for activator semantics, placement constraints and dump
mechanics; this table is the one-glance map, and `src/sched_dump.rs`'s SIGUSR1
live-state snapshot (a fifth instrument, not a sink) is in its §8.

| Sink | Activator | What it observes | Implementation |
|---|---|---|---|
| Scheduler trace | `CRANELISP_SCHEDULER_TRACE=1\|*\|<module-list>` | Worker lifecycle, scheduler dispatch, pool transitions, `is_typechecked` hit/miss | `src/observability.rs` (+ `observability/tests.rs`) |
| IO trace | `CRANELISP_IO_TRACE=1\|*` | IO trampoline transitions, platform effects, Par fork-join | `src/io_trace.rs` |
| GOT trace | `CRANELISP_GOT_TRACE=1\|*` | GOT-slot writes: JitWrite, LinkerWrite, Redefinition, SlotFreeze | `src/got_trace.rs` |
| Introspection store | `RunMode::Repl` only (D1 §4) | Per-symbol metadata: source, sexp, clif_ir, code_size, compile_duration | `SharedState.introspection` |

The first three are per-thread `VecDeque<Event>` ring buffers with FIFO overflow; activated by env-var; flushed to stderr at session end (with merge-sort across threads via shared `TRACE_ANCHOR` `Instant`; the IO sink's cross-thread half is currently unreachable — `observability.md` §10). Sinks 2 + 3 are reached via observer-callback contracts owned by their originating crates: `cranelisp_intrinsics::register_io_observer(...)` (Decision 40 — the registration host moved to intrinsics with the D43 split of the former `cranelisp-runtime`) and `cranelisp_backend::register_got_observer(...)` (FIXME 0099). `main` registers the observers when the activator is on, no-ops otherwise; the relaxed-load null check costs one branch per call site in the unregistered case.

**The pattern is uniform across the three ring buffers**: each crate that originates events defines the taxonomy (`IoEventTag` / `GotEventTag` / scheduler events), exposes a registration function, and emits through the registered observer. int implements the ring-buffer state, formatter, and dump.

The fourth sink (introspection) is a per-key store, not a ring; it serves slash commands and the rich error formatter. It overwrites on REPL redefinition (per the Decision 31 carry-forward invariant — same key, fresh data).

**Production-batch cost** (`--link` and `--run`): zero — `shared.introspection == None` means no populate paths run; no observers are registered, so the ring-buffer call sites no-op after the relaxed load + null check.

---

## 12. Quality attributes

| Attribute | This crate's stewardship |
|---|---|
| Simplicity (P6) | 2026-04-23 src audit (Git history), F1+F2+F5 are the operative complexity gaps. The 38/39/41 simplification removes three dimensions (per-form RefMut, `module_sources`, the int-side post-loop unpacking after `compile_to_module`). The S64 module decomposition (§3.3) closes the rest. Decision 35/41's `Code` enum is single-cleavage Cranelift exposure — one site, not scattered. |
| Maintainability (P1, P2) | Audit's "split `session_v4.rs` by responsibility" is the centrepiece. Per-symbol mutability + `process_form`-as-sole-crossing closes F3. The three-instance observability pattern (alongside introspection) closes F7's "long historical narratives in hot paths" by routing rationale into `design/int/observability.md`. |
| Observability | §11. Four sinks; one pattern; all production-batch zero-cost. The four-pattern uniformity is a deliberate design choice — once a developer learns the IO-trace shape, the GOT-trace and scheduler-trace shapes are mechanically the same. |
| Concurrency-safety (P4) | §10 invariants. Decision 31 reclaim safety invariant ("Arc-refcount-zero means no fn pointer reachable") is upheld by the GOT swap discipline + the language-level "function values are heap closures, not raw code pointers" rule. Per-symbol mutability discipline removes the per-form whole-module write lock. |
| Performance (P6) | One JIT per compile batch (§5.2); a long-lived per-worker JIT (withdrawn Decision 28) coalesces batches and defeats reclaim. Persistent worker pool (Decision 27) avoids per-module thread spawn cost. Cache-hit-via-`LoadObject` skips codegen entirely on cache-hit. Production batch zero-overhead introspection (`shared.introspection == None`) and zero-overhead observer ring buffers (no observer registered → relaxed load + null-check branch). |
| Testability (P5) | `process_form` is a free function over `&SharedState` — testable with a synthetic SharedState. The scheduler's wait/notify primitives are unit-testable in isolation. `Introspection` populate paths are conditional on a single discriminator — easy to assert in integration tests. The observer contracts are unit-testable: register a captured-events observer; assert events fired in the expected order. |

At the typed result exit, one owner state machine accepts three keyed
code-housing adapters; scalar results stay call-free; observe-before-release and
exact-once behaviour are unit-testable with recorded callbacks
(`result-owner.md` §7).

### 12.1 Standing review rejects

Each item names a structure int must not reintroduce. The subject document
carries the rule; this list is the review checklist.

1. **A second lifecycle representation** — an int predicate re-deriving slot
   legality, origin×state legality, concreteness or tombstone conservation
   (`design/arch/symbol-table-lifecycle.md`).
2. **A source-form instantiation replay** — re-injecting an `__expr` or any
   other form to re-mint instances; reload carries demands as data
   (`design/int/s122-closure.md` §2).
3. **A cache-specific parallel** — child, written-impl or alias restoration on
   the restore branch only; a silent pick on written-impl divergence; any
   tolerance for an empty `written_trait_impls` vector ([restoration parity](#75-restoration-parity)).
4. **An alias outside the one mint** — a `module_aliases.insert` key not produced
   by `cranelisp_types::module_alias_key`, a bare-key fallback beside the
   scoped walk, or a substitution that accepts an undeclared alias.
5. **A name-shape test in presentation** — branching on `def`, `-def`, a
   `*-def` suffix, `stdlib` or a module identity (Principles 10 and 19).
6. **A projected macro presentation** — a presentation scheme, parallel store,
   post-publication scan, dry invocation typecheck or cache field predicting the
   type of invoking a macro (`s117-conformance-recovery.md` §6).
7. **A compensating RC walk in `src/marshal.rs`** — the releaser is intrinsics'
   `consume_sexp` (`macro-turn-ownership.md`, protocol Rule 5).
8. **A lexical annotation test** — a `starts_with(':')` or string-prefix
   dispatch standing in for `Sexp::Annotated`
   (`design/arch/annotated-sexp-node.md` §7).
9. **A GOT-cursor write or a direct platform pointer store** — manifest slots
   are ordinary claims and the DLL owns its slab
   (`design/arch/platform-interface.md` §6.4).
10. **A panic at the platform load boundary** — manifest refusals are located,
    diagnosed load errors.
11. **A macro-specific publication writer** — macro checkpoints publish through
    the ordinary prepared publication, including `fresh_jit_drop_glues` pairs.
12. **A split compiled publication or early owner release** — publishing before
    every compiled owner attaches, owner-bearing ordinary staging, or dropping a
    returned owner before refused GOT cells are restored
    (`design/arch/symbol-table-lifecycle.md` §4.4).
13. **A retained temporary macro world or replayed checkpoint** — any
    `PreparedMacroTurn`, `TurnCheckWorld`, `TurnDelta`, candidate-clause
    invocation, reserved unpublished slot or cross-module rollback; or a retry
    that re-expands an already-committed macro (`s117-conformance-recovery.md`
    §1.1.2).
14. **A binding-shaped closure gate** — any exposure predicate over `Binding`
    beside the [candidate-shaped export-closure gate](#67-public-candidate-exposure--the-export-closure-gate).
15. **A bootstrap lifecycle panic** — `unwrap`, `expect` or `unreachable!`
    asserting a fallible lifecycle transition during session construction.
16. **Dependent recompilation on an ordinary redefinition** — re-typechecking,
    recompiling, breaking or trap-patching a dependent where §18 requires
    rejection (`session-transaction.md` §0).
17. **A second program-result releaser or an unguarded release target** — a
    release key re-derived from the observed type, a raw glue address without
    its `Code` owner, or an `IO` branch in a formatter (`result-owner.md` §7).
18. **A second bare-module-name rule** — deciding what a bare `import` or
    `export` module name refers to from symbol-table registration, a file probe
    or form order. Reading a persisted spelling as an absolute module outside
    the one resolver is also rejected
    ([§6.9](#69-bare-module-names-in-import-and-export)).
19. **A pre-typecheck rewrite that mints or shares a span** — a node built by
    an int AST transform whose span is not that of the written node it
    replaces in the same role, or one span on two output nodes
    ([bind-chain analysis §3.6](bind-chain-analysis.md#36-reconstruction)).

---

## 13. Decision register (int-relevant)

Active Decisions affecting int (operative this sprint or constraint-bearing):

| Decision | Headline | Status for int |
|---|---|---|
| 30 | Form-by-form scheduler deadlocks on mutual imports | Resolved: a mutual import is a cycle error at the import site ([§6.2](#62-cluster-orchestration)) |
| 31 | One `JITModule` per batch; `Arc<Jit>` on entry; custom Drop | Operative (§5.3); no current test observes reclaim |
| 35 | `Code` owns lifetime only; addresses live in the GOT | `Code` lives in `cranelisp-backend`; int re-exports it and instantiates the session table (§5.1) |
| 40 | `trace.rs` + `io_trace.rs` relocate to int; runtime exposes `IoObserver` | Operative (§11) |
| 41 | Backend publishes slot addresses and returns artifacts | Operative for slot publication and artifacts; int attaches `Code` (§7.2). The compile batch, not the symbol, is the JIT unit (§5.2) |
| 42 | `PlatformError` adopts `ErrorLocation`; lives in `cranelisp-types` | Operative (§9) |

Legacy Decisions (outcome embodied in architecture; located through [the decision index](../arch/decisions/README.md)) — int-specific embodiments include 9, 21, 22, 23, 24, 25, 26, 32, 33, 34, 36, 37, 38, 39. Each of these is "as-built" inside int today; the source code reflects the commitment.

Retracted/superseded Decisions deleted (rely on git for history) include 28 (per-worker persistent JIT — superseded by 31).

---

## 14. As-designed vs as-built

The S64 destination rows this section once tracked have landed (verified
against source 2026-09-21): gap orchestration matches typed `CheckError::Gap`;
the GOT, IO and scheduler trace sinks live in `src/`; `PlatformError` is a
structured `cranelisp-types` enum; `display.rs` lives in `src/`; the legacy v3
`session.rs` is deleted; and the god-file decomposition is complete (§3.3).
`src/lib.rs` exports ten public modules; no filing currently tracks narrowing it
further. Open Binary/int work is §16.0.

---

## 15. Subordinate topic docs

`design/int/AGENTS.md` §"Document index" is the triage of record: it names the
master, the durable subsystem docs, the active subordinate feature docs, the
reference lineage and the historical records, and it is the collection
declaration those documents are established through. Do not maintain a second
inventory here — a per-doc table in the master decays against the directory it
describes, and the S64 table that stood here had drifted on counts, on
dispositions never executed, and on files since deleted.

---

## 16. Open obligations

### 16.0 Open Binary/int obligations (verified against source 2026-09-21)

The S121 C6 visit delivered most of its bundles; these obligations remain open
in source. Each owning filing stays the tracker; this list is the design intent.

- **S124 (designed 2026-11-16, Phase 3).** Designed to the user's Phase 2
  rulings and the 2026-11-17 approvals of rows D8, R10-9, D10 and D11 and
  rulings on S124-Q4 to Q6, and the 2026-11-17 approval of row R10-10, the
  S124-Q8 ruling, the scoping of ACT-1063 and ACT-1065, and row D12 with
  its category condition (`sprints/SPRINT.md`, Notes), and to `arch`'s S124 contracts
  ([approved changes](../arch/interfaces.md#approved-changes-not-yet-in-source-s124)).
  ACT-1050 and ACT-1065 landed at `32e434dc` (W4), D4 at `441e31ea`, and
  D3 and D10 at `42e6d929`. W8 landed the cycle-precedence mount reach at
  `2dec7450`, the regeneration corrections at `74aa7a52`, D7 at `7cceedc4`,
  the entry-module fact at `109f008b`, ACT-1061 at `b3e3887e`, ACT-1036 at
  `e294852f`, ACT-1052 at `3c4c0f7b` with the backend's bump at `f3f9cc47`,
  ACT-1016 Face 1 at `f95f0a3a`, the declaration readiness gate (ACT-1016
  Face 2) at `870aacd8`, the definition origin across a dependency retry at
  `98ea54a0`, the end of a stored layout at a `.meta` rewrite at
  `c53a3f4b`, ACT-0973's refusal at `68f042d5` after the exemplar's split
  (`efa4d8df`), the refusal of a `main` whose result type is not fixed at
  `098f0980`, and ACT-1052's shared decode at `2d3a5b3e`.
  - *Still open after W8 (read at `66bc7b8a`):*
    - the location of the batch `discover-tests` refusal (ACT-1036's last
      leg), designed in
      [test runner §7.3](test-runner.md#73-batch-refusal-of-discover-tests),
      Location;
    - route independence of a graph through a declared child (ACT-1081),
      designed in §6.11, *Route independence*; its outcome waits on the
      user's ruling;
    - Face 1's fresh-load gap (§6.11, *Failed dependency*).
  - *Designed, not scheduled:* a qualified reference through a mount loads
    the mount's owner (ACT-1079,
    [§6.13](#613-import-and-export-entries-and-export-mounts-s124)), with
    the §6.12 walk's revealed-owner edge.
  - *Cached-object validity (ACT-1052):* [§7.6.3](#763-slot-layout-identity-act-1052).
    The record keys each member by source hash and authored slot layout.
  - *Import and export entries and mounts (D3; ACT-0997, ACT-1055,
    ACT-1056):* [§6.13](#613-import-and-export-entries-and-export-mounts-s124).
  - *Export cycles (ACT-1016):* Face 2 is the declaration readiness gate and
    Face 1 the failed-dependency refusal, both in [§6.11](#611-module-cycles-at-publication).
  - *Mode-ABI gate removed (D7; ACT-0953):*
    [session transaction §2.4](session-transaction.md#24-ownership-modes-are-not-compared).
  - *Platform forms outside the entry (ACT-0973):*
    [io-integration §2.1](io-integration.md#21-form-routing).
  - *`main` refusal location (ACT-1036), including a `main` that is not a
    function:* [io-integration §1](io-integration.md#1-running-a-program).
    Each refusal about an existing `main` is located at the written form
    that declared it, read from a definition-origin span the session keeps
    in every mode. The declaration's own span is synthetic for a
    macro-produced `main`.
  - *`HeapCategory::Value` removed (D4).* The result owner's two `Value` arms
    delete ([result owner §1.1](result-owner.md#11-classification-is-a-shared-predicate-not-an-absence-test)).
    The value display's flattened-word arm deletes in the same change-set:
    after D4 such a value is a heap object, and a display that still read the
    word as the field would print a pointer as `(Box <address>)`. The display
    then renders it through its ordinary nullary-or-heap branch, and asks no
    layout predicate of its own. Its four flattened-word module rows become
    heap-shaped rows of the same displays; REPL §1.5's guarantees are
    unchanged.
  - *Mount and import-alias sharing a spelling (S124-Q4, ruled B):*
    [§6.13](#613-import-and-export-entries-and-export-mounts-s124). Equal
    targets form one `Public` entry; different targets refuse in either order.
  - *A `/sh` save is reported before the next prompt (ACT-1061, S124-Q6
    ruled A):* [REPL lifecycle §1.2](repl-lifecycle.md#12-poll-and-reload),
    Poll points. The post-turn poll after a `/sh` turn compares every
    recorded source, so recognition does not wait on notification delivery.
  - *Macro-before-use in regeneration order (S124-Q5, ruled A):* the
    constraint the carried ACT-1005 correction must keep is recorded in
    [session persistence §1.4](session-persistence.md#14-dependency-ordering).
    Nothing is built in S124; the present grouping already satisfies it.
  - *An inline `bind` continuation loses its type (ACT-1050), in source at
    `32e434dc`:*
    [bind-chain analysis §3.6](bind-chain-analysis.md#36-reconstruction).
    The rewrite rebuilds each sequential step from the spans of the nodes it
    consumed, so no span names two nodes. No published type changes, and
    nothing is asked of typecheck.
  - *A user function spelled `bind` is taken for the primitive (ACT-1065),
    in source at `32e434dc` except the renamed-import row, which lands with
    D3
    ([bind-chain analysis §7](bind-chain-analysis.md#7-open-obligations)):*
    [bind-chain analysis §3.1](bind-chain-analysis.md#31-pattern-recognition).
    The pass resolves each callee once, through the committed
    `ResolutionScope` behind a lexical layer and the cluster's own
    declarations. A step is the primitive only when that resolution reaches
    the one identity bootstrap installs. The same answer supplies the
    platform-effect class and the timer leaf, so the pass's split-spelling
    lookups are deleted. The root already consumes `ResolutionScope`: no
    public API changes.
  - *A "no `main`" refusal (S124-Q8, ruled B):*
    [io-integration §1](io-integration.md#1-running-a-program). One gate
    produces it as row D12's `BatchError::MissingMain`, and `src/main.rs`
    renders it as the formatter's line without a position, keeping the
    `module error` category.
  - *A trait-method or multi-arity `main` (ruled 2026-11-17, spec §10.6):*
    [io-integration §1](io-integration.md#1-running-a-program). The gate
    already gives both the required outcome: a trait method never binds the
    entry table's `main`, so it takes the "no `main`" refusal; a
    multi-arity `main` is not a single callable, so it takes the located
    refusal of ACT-1036. No further change.
  - *A cached load across re-registration (ACT-0994), designed and not
    scheduled:* the persistence group carries past S124 by the user's third
    deferral (`sprints/SPRINT.md`, Notes). Design:
    [§7.1](#71-cache-hit-flow-inside-register_module), *A claim ends inside
    its registration*. The reload's settle wait also waits out the module's
    cached load, and a loaded completion acts only while its module is still
    claimed. Private to `src/`; the scheduler module rows carry the
    evidence.
  - *An inline primitive as a value (ACT-1063): no correction belongs to
    this surface* (read 2026-11-17). Typecheck accepts `(let [b bind] …)`
    and records the value reference: the backend passes its arity and
    known-function reads and refuses at its GOT-slot read
    (`fn_as_value.rs`, `emit_wrapper_call`). The wrapper already has an
    inline-primitive arm for the Vec primitives. It has none for the four IO
    combinators, whose lowering is the backend's (`IoCombinator`). The
    backend's wrapper arm is the correction, and it needs nothing from int.
    - *A latent representation fault int owns, not part of the correction.*
      `src/bootstrap.rs` installs `bind`, `race`, `select` and `sleep` as
      host-promised callables, which claims a host symbol imported by name.
      None exists, because the backend lowers each one inline. Their
      truthful state is `Life::Inline`. If the backend keys its wrapper arm
      on that state, int's bootstrap change joins the correction and ACT-1063
      crosses two surfaces: the user's named-carry condition. Keyed on the
      `IoCombinator` classification of the resolved entry, as the Vec arm is
      keyed on the entry's kind, it stays one surface. That choice is
      `design`(backend)'s. Changing the bootstrap state alone would send
      these combinators down the wrapper's Vec arm, so it must not land
      alone. After ACT-1065 the pass no longer reads this state (§3.7).
  - *S123 rows in `src/`.* R10-3 landed at `1e4b0ce4`, deleting the root's
    cache-packet writer with the backend's family. K11-d moves the root's test-only `lenient_from_expr`
    calls to the types `test_support` path; the root's dev-dependency on
    `cranelisp-types` enables `test-support`. D2, D5, D6, D9, R10-1, R10-2,
    R10-5 to R10-7 and K11-a to K11-c have no consumer in `src/` (read
    2026-11-16).
  - *Rows approved 2026-11-17, in `src/`.* R10-9 (superseding R10-6) and
    R10-10 move every root reader and writer of a heap layout to the
    intrinsics definitions, so no layout value is restated in `src/` (read
    2026-11-17):
    - `src/display.rs` reads the backend's `heap::{HeapAdt, HeapVec}`; it
      moves to `cranelisp_intrinsics::alloc::HeapAdt` and
      `vec_runtime::{LEN_OFFSET, DATA_PTR_OFFSET}`.
    - `src/session_v4/test_runner/run.rs` reads the backend's
      `HeapAdt::field_offset` for a failed test's reason; it moves to
      `alloc::HeapAdt`.
    - `src/session_v4/test_runner.rs` names no backend struct. It writes and
      reads all three layouts as literal offsets. Its ADT allocator writes
      the tag and fields and sizes the payload, and moves to
      `alloc::HeapAdt`'s offsets and payload size. Its test-wrapper closure
      is written and its capture read, and both move to
      `alloc::HeapClosure`. Its Vec reader of module paths and its Vec
      builder read the data pointer, and they read and write the length; both
      move to `vec_runtime::{LEN_OFFSET, DATA_PTR_OFFSET}`. Writing the length
      uses the same constant as reading it, so R10-10's two root edges cover
      the writes.
    - Not taken: the module-path reader could use the published
      `vec_runtime::with_vec_strings` and stop reading the Vec layout. That is
      a new root consumer edge no packet row names; it goes to `arch` if
      wanted.
    D8 and D11 have no consumer change in `src/`: nothing
    in the root calls the spark or trace exports, and `src/marshal.rs` calls
    `heap_string::string_read` by Rust path, which D11 keeps (read
    2026-11-17). D10 is the impl-identity part of §6.13.
  - **Order and dependencies.**
    1. Independent of the other surfaces, in any order: ACT-1036, ACT-0973,
       ACT-1016, ACT-1052, ACT-1081. ACT-1052 carries a cache-schema bump.
       ACT-0973's refusal lands after the exemplar moves its platform
       declaration to its entry. ACT-1081's error clause lands after the
       user's ruling; its other two rules do not wait on it.
    2. D3: after the types carrier and the frontend producer, as one
       callee-first migration with its own schema bump. The impl-identity
       part (row D10) lands in D3's migration and shares D3's bump. The mount
       writer lands only with its mixed-pair branch (§6.13) and the
       import-alias writer's duplicate refusal.
    3. D7: with the types removal, after `qa` allocates the mode-change
       redefinition cell.
    4. D4: in the backend's D4 change-set, after the structural close.
    5. R10-3: in the backend's R10 change-set, after D2. K11-d: with the
       types change-set.
    6. ACT-1050 (landed at `32e434dc`): in the producer-correction row of
       the backend's order
       ([release contract §7.7](../backend/non-concrete-release-contract.md#77-order)).
       It lands after the census's first reading, which is `qa`'s named
       refuter of the attribution and would lose its subject if the fix came
       first. It lands before the zero read, and so before close step 2,
       which would refuse the subject. It is independent of items 1 to 5 and
       needs no cache-schema bump, because a build-id change already
       invalidates cached objects (§7.3). Emission acceptance: an attributed
       re-baseline limited to functions with a rewritten sequential step.
       Each such continuation's symbol takes the `fn` form's span, and an
       unused heap parameter gains its release. Any other diff is a defect.
       ACT-1065 lands in the same change-set, because both edit chain
       collection and reconstruction. Its acceptance is in
       [bind-chain analysis §7](bind-chain-analysis.md#7-open-obligations).
    7. R10-9 and R10-10's root readers and writers: in the same callee-first
       migration as the backend's deletion, after intrinsics' additions and
       before K11-a.
    8. ACT-1061: independent of items 1 to 7; a `dev` change in the watcher
       and the `/sh` dispatch, with its unit test at the poll seam.
    9. ACT-1036 and S124-Q8 (row D12): one change-set, because both edit
       the gate. The definition-origin span lands first in it, with its
       unit test at the attribution seam; then the located refusals, the
       single producer and `BatchError`, and the renderer last.
  - **Found while reading, routed elsewhere.**
    - ACT-1039 is not int's. Trace discovery skips a slot whose GOT word is
      0 at codegen (`trace_codegen.rs`, `discover_traced_fns_from_tables`).
      `--run` compiles the entry as one batch and fills its slots at
      publication, after codegen; the REPL published `fib` in an earlier
      turn, and `--link` compiles after publication. The mode divergence
      follows from discovery reading run-time slot contents at compile time.
      Int's batching is the prepared turn every mode shares and should not
      change to serve it. `qa`'s refuter (`CRANELISP_GOT_TRACE`) confirms or
      refutes this before `design`(backend) places the fix.

- **S123 (designed 2026-11-15, Phase 3).** Designed to the
  user's Phase 3 rulings (`sprints/archive/sprint-123.md`) and arch's
  [panic and environment contract](../arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics) (bounded contexts §4b invariants 13 and 18, and §6).
  Each item's design, and its build status, lives in the section named here.
  - *Agent on by default:* [agent §6.3–§6.4](agent.md#63-provider-selection).
    The default feature set gains `agent`, the provider fallback is removed,
    and the banner reports the activation answer.
  - *Environment files and baked switches:* [environment](environment.md).
    The supply is built (W3); environment §2.4–§2.5 record the readings
    taken on `dev`'s open points.
  - *Panics end the process (host side):*
    [io-integration §1.2](io-integration.md#12-a-runtime-panic-ends-the-process-the-host-side),
    [observability §7.1](observability.md#71-process-exit-and-panic-wiring)
    and [test runner §6.5](test-runner.md#65-the-test-child). This deletes
    ACT-1041's host locus. Macro-expansion panics and platform dispatch faults
    end the process too.
  - *Broken symbols:* [session transaction §5.2](session-transaction.md#52-no-symbol-is-left-broken).
    The redefinition guard is the compile-time refusal. The superseded
    residue was deleted in W4, and P13 is built in the W4 tree.
  - *ACT-1047, ACT-1048 and ACT-1020:* [REPL lifecycle §1.2](repl-lifecycle.md#12-poll-and-reload)
    (Absent is a recorded state; A deleted backing file needs nothing) and
    [§6](repl-lifecycle.md#6-project-root-resolution).
  - *Entry settled at publication (W1):* [§6.1.2](#612-the-entry-is-settled-before-the-eval-thread-owns-it).
  - *Failed-dependency refusal prefix (W1):* [§6.11](#611-module-cycles-at-publication),
    Diagnostic.
  - *ACT-1035:* [session transaction §2.5](session-transaction.md#25-trait-implementation-redefinition);
    built in W4.
  - **Deltas at the user gate.** `arch` settled them as packet rows
    (`sprints/s123-api-packet.md`); the user's gate decides each:
    1. Packet row P8, consumed as stated: `src/exe.rs` calls
       `capture_runtime_switches` at `--link`, the startup stub imports
       `cranelisp_install_runtime_switches`, and `cranelisp-exe-bundle` adds
       its `pub use`. Int names no switch.
    2. Packet row P11: intrinsics publishes `panic::PANIC_REPORT_PREFIX`
       and `panic::PANIC_EXIT_STATUS` for the test supervisor
       (`src/session_v4/test_runner/`), a new root → intrinsics consumer edge
       to two items; intrinsics `public-api.txt` +2. If the user declines it,
       int keeps a private copy guarded by the end-to-end panic cell
       ([test runner §6.5](test-runner.md#65-the-test-child)).
    3. Rows P1–P5 and P9 remove items the binary consumes today. Int deletes
       those consumers in the same change-sets: the REPL's trap arm and
       `runtime error:` display, `trampoline`'s slot read, the expander's
       slot read, the runner's per-test bracket, `compose_dispatch_error`, and
       the stub's error block and drain call.
    4. Packet row P12, root crate (no baseline): `CompilerSession::run_tests`
       becomes the child's engine, and `session_v4::supervise_tests` returns
       the unchanged `TestRunReport`. The signatures are the packet's;
       [test runner §6.5](test-runner.md#65-the-test-child) adopts them.
    5. Packet row P13, after the residue deletion: remove
       `cranelisp_backend::compile_trap_stub`, `cranelisp_types::Life::Broken`
       with `SymbolTable::mark_broken`, `BrokenProvenance` and
       `BrokenTransition`, and the match arms on `Broken`. `arch` finds no
       cache-schema bump: a broken entry is never written
       ([session transaction §8.3](session-transaction.md#83-broken-modules-are-not-persisted)).
       Scheduling, with packet B3 at S123 close or in S124, is the user's.
       Both halves are built in the W4 tree, uncommitted:
       `compile_trap_stub` and `Life::Broken` are gone
       ([session transaction §5.2](session-transaction.md#52-no-symbol-is-left-broken)).
    6. `env_files` is binary-private (`mod env_files` in `main.rs`). As
       built, the root library also gains `pub mod agent_activation`
       ([agent §6.3](agent.md#63-provider-selection)): `pub mod agent`'s
       public `AgentLink` carries its `DormantReason`, and
       `AgentState::activation` returns its `AgentActivation`, so the module
       must be public. No packet row names it. The root crate has no baseline;
       whether the new item needs the user gate is `arch`'s ruling.
  - **Evidence conditions for `qa`**, proposed here and allocated in
    [the S123 evidence delta](../../tests/plan/s123-evidence-delta.md):
    - *Agent:* a plain `cargo build` REPL prints the banner line.
      `--no-agent` reports off. An unset provider is dormant and names the
      variable even with `ANTHROPIC_API_KEY` present, and transmits nothing.
      An unrecognised value is dormant and names that value. The agent-free
      build's banner says the agent is not built in, and that build keeps the
      `--agent` and `--yes` errors.
    - *Environment:* the §4 unit rows of [environment](environment.md).
      End to end: a project `.env` supplies a `CRANELISP_*` switch;
      precedence is process over `.env` over user file; `XDG_CONFIG_HOME`
      relocates the user file; a foreign key such as `PATH` is ignored;
      `CRANELISP_ENV_FILE` and `CRANELISP_USER_ENV_FILE` redirect and
      `CRANELISP_NO_ENV` disables both; a malformed line, on a foreign key
      too, and an unreadable file are located startup errors without a
      value. The suite's repository-level declaration must not depend on a
      developer's files.
    - *Baked switches:* a runtime switch set at `--link` takes effect in the
      executable without being in its environment; set only at run time, it
      has no effect; agent variables are absent from the executable's bytes.
    - *Panics, host side:* the ACT-1041 `--run` cell (the message once, no
      `codegen error`, no `0..0`, exit non-zero), then the
      `error: runtime panic:` prefix, plain on stderr, in every mode. A REPL
      panic ends the process after the output already written. TTY history
      keeps the panicking line. Trace sinks flush on a panic exit. A macro
      clause that panics ends `--run` and the REPL with its message. A
      platform dispatch fault ends the process with its message.
    - *Test runner:* a panicking test is `PANIC: <message>` and the run
      continues, in `--test` and `/run-tests`; a test after it still runs. A
      child dying by signal while a test is open is one failed test. A
      `/run-tests` whose test references `discover-tests` fails with the
      §16.6 diagnostic and runs no test. A REPL child writes no cache file.
      Negative leg: a passing run's report is unchanged from today's.
    - *Broken symbols:* a language-type change with only a template caller is
      refused, naming it. After the residue's deletion the §18 cells stay
      green, together with `qa`'s S122 generic-edit probe shape.
    - *ACT-1047:* FC-1 with its control, plus the load leg (`(k)` gives 9 and
      the file holds `k` and `h`).
    - *ACT-1048:* the Deleted backing file row of
      [REPL lifecycle §1.3.2](repl-lifecycle.md#132-module-evidence-dev),
      under the user's 2026-11-16 ruling: no detection, notice or consent.
    - *ACT-1020:* `cranelisp core.str` loads `core/str.cl` in `--run` and the
      REPL, and a REPL empty start with that target writes `core/str.cl`.
      Control: an undotted target.
    - *ACT-1035:* the REPL cell and both controls. The `begin … keep` and
      `begin` without `keep` pair from
      [session transaction §2.5](session-transaction.md#25-trait-implementation-redefinition)
      discriminates the mechanism.

- **`--test` and the shared test runner (S122, ACT-0988).** Implemented as
  [test runner](test-runner.md) describes, and QA judged it adequate
  ([runner adequacy](../../tests/plan/s122-evidence-delta.md#shared-test-runner--final-adequacy-2026-09-28)).
  Open: the user's Phase-5 acceptance.

- **Batch missing entry (S122 K1, ACT-1004).** Entry registration refuses a
  missing entry file for every batch mode
  ([§6.1.1](#611-a-missing-entry-source-file)). Implemented, reviewed and
  QA-adequate on 2026-09-30. Open: commit, the fresh final run (K4) and the
  user's Phase-5 acceptance.

- **Persistence corrections (S122, ACT-0998).**
  - Records are written only from published state
    ([session persistence §2.4.1](session-persistence.md#241-who-writes-a-record)),
    and a cache-installed module is recompiled before `/mod` makes it current
    ([§2.4.5](session-persistence.md#245-editing-a-cache-installed-module)).
    Both are implemented in the working tree. QA judged them adequate on
    2026-09-28, subject to the review repairs its delta names. Open: commit
    and the user's Phase-5 acceptance.
  - **Restart boundary.** A reload that would change a
    live type's structure fails with the restart remedy (REPL §14.8, §18.5).
    The design is the guard's type pass
    ([session transaction §2.6](session-transaction.md#26-type-re-establishment-repl-185-148)).
    A reload's outcome is the reloaded module's own state
    ([§1.3 Outcome](repl-lifecycle.md#13-failed-module-and-the-session-lock)). The imported-module
    case relies on the barrier fail-fast
    ([error cascade §4.1](step9-error-cascade.md#41-cascade-construction)).
    Each of these sections names its guards. There is no public API change.
    - The open design risks are the §1.3 Outcome coverage hypothesis and
      §4.1's order-dependent stranding face. Each is asserted with a named
      falsifier, and neither is measured.
  - **Session lock (Phase 6b, user rulings of 2026-10-01).** A module
    standing failed, after a save, at startup or in a `/mod` load, locks the
    session: every code turn is refused, no backing file is regenerated, the
    dependents of a failed module wait, and `/quit` and EOF exit 0 (REPL
    §14.5, §0.1). The §14.8 refusal is one cause of the one failed set
    ([REPL lifecycle §1.2, §1.3.1](repl-lifecycle.md#131-session-lock)). It
    replaces the per-module lock and the startup repair at the prompt, and
    repairs ACT-1044's parse-failure exit. Designed 2026-10-01; the source
    reservation is [S122 closure §8](s122-closure.md#8-session-lock-phase-6b).
    Delivery and acceptance status is in the
    [evidence delta](../../tests/plan/s122-evidence-delta.md) and the
    ACT-1010 and ACT-1044 filings.
  - **Whole-file rebuild (ACT-1007, ACT-1012, qualified dependents).** A
    reload rebuilds its module from a fresh table that keeps the module's GOT,
    so everything its saved source omits — definitions of every class,
    imports, macros, impls — leaves scope, introspection and the regenerated
    file
    ([session transaction §7.3](session-transaction.md#73-the-watcher-and-reload-path);
    [§6.10](#610-the-import-generation)). Dependents, including modules that
    reach it only through qualified references, rebuild after it in the same
    plan or lock
    ([REPL lifecycle §1.2](repl-lifecycle.md#12-poll-and-reload)).
    - The user approved the quiescent whole-file boundary on 2026-09-29.
      It adds no public API (+0/−0 on every guarded baseline), cache schema
      or ABI change.
    - Status: implemented with the retirements in session transaction
      §7.3.5, and QA judged it adequate on 2026-09-29
      ([rebuild adequacy](../../tests/plan/s122-evidence-delta.md#whole-file-rebuild-and-qualified-dependents--final-adequacy-2026-09-29)).
      Open: the user's Phase-5 acceptance. The earlier per-definition removal
      and candidate-withdrawal designs are withdrawn.
    - Guards: C2, RM-1 to RM-5, FL-3, FQR-1 and FQR-2 end to end, and the
      module rows in session transaction §7.3.4 and REPL lifecycle §1.2
      and §1.3.1.
- **Annotation-mirror tail** (re-verified in source 2026-09-30). No filing
  tracks it: FIXME 0708, its former tracker, is retired, so this entry is the
  record. Four lexical `src/` mirrors of the retired pre-fold annotation shape
  survive and each goes one way:
  `worker::leading_annotation_len` (a constant-`0` stub) deletes with its
  caller's `annotation_prefix` plumbing and its pin test;
  `save.rs::is_bare_colon` and `expander::is_annotation_symbol` are re-expressed
  as matches on `Sexp::Annotated`; `pretty.rs::is_type_annotation_list`, its
  `pp_type_annotation_list` helpers and the `starts_with(':')` symbol-role arms
  delete, because the printer's `Sexp::Annotated` arms already render the
  annotation. The printer deletion removes a wrong-accept, not dead code: a
  macro can mint a symbol spelled with a leading colon, which is not an
  annotation and must render with an ordinary role. Its arming evidence is a
  printer unit row that fails before the deletion — a hand-built
  `(:Int 42)`-shaped list with a colon-spelled head symbol takes no
  type-annotation span — plus colour-off identity and colour-on span rows.
- **Import-alias key mint.** The one import-alias writer,
  `src/imports.rs::install_import_alias`, still keys through the private
  `alias_key` helper. The key value equals
  `cranelisp_types::module_alias_key`'s, but the private mint must delete so the
  one types-owned mint is the only key source (§12.1 reject 4). It deletes in
  the S124 D3 change-set, which adds the second alias writer (§6.13).
- **Located platform-signature refusal (FIXME 0933).** A manifest signature
  whose checked type retains a free type variable is refused structurally:
  `SymbolTable::install_platform` requires a concrete type, and
  `register_platform_in_tc` wraps the refusal as a load error naming the
  platform module and function. Int owns the frame: the refusal must stay a
  diagnosed load error, never a panic, and should name the offending leaf. No
  test pins this refusal, and whether the current text names the leaf is
  unverified; the filing stays open until a platform-module unit row shows a
  concrete signature registering and a bare-lowercase-leaf signature refusing.
- **Load-boundary lifecycle validation.** The cache decoder treats only an
  instance-key mismatch as stale ([restoration parity](#75-restoration-parity)). Whether other invalid decoded
  lifecycle states can restore is unmeasured. The falsifier is a decoded table
  with any other invalid lifecycle state that restores instead of regenerating.
  The user deferred hardening; `qa` holds it as an accepted residual
  (`tests/plan/s122-evidence-delta.md` §C-A). Any fix belongs to the
  types/backend owners.
- **Dependency-record validity (CD-1; source read 2026-09-25).** The
  [dependency record](#76-dependency-record-and-validity) is realised at
  `94486f24`: every writer records its closure through the one builder, and
  validity is driven by the recorded keys. The `cache_dep_*` and restored-chain
  cells in `tests/cache.rs` guard it. Open:
  - **Callee-module edges (review F1).** Built
    ([callee-module edges](#761-callee-module-edges)); both callable guards
    pass on the delivered source. QA judged the evidence adequate as a bounded
    correction ([F1 acceptance](../../tests/plan/s122-evidence-delta.md#f1-acceptance-and-qr-classification-2026-09-25)). CD-1 discharges §7.6's opening sentence for
    qualified callable references only. The FN-1 null-import fence is armed.
    Open: the user's Phase-5 acceptance.
  - **Qualified-reference kinds outside `callees`.** Int's half of
    [lookup dependencies](#762-lookup-dependencies) is committed at
    `56e4d2e1`, and its guards pass. Review found no blocking or required
    finding. QA judged the evidence adequate on 2026-09-26. Open: the user's
    Phase-5 acceptance.
  - **LD-9:** [empty-publication correction](#7621-empty-publication-correction)
    implemented and reviewed, uncommitted. Its regression and allocated unit
    evidence pass; R-1 is resolved. QA judged the evidence adequate, subject
    to that now-completed review repair.
  - **RR-1 (REPL cache-restore race).** The user prioritised it on
    2026-09-27.
    - Face (i): §7.1's *restore before load* and its claim are committed at
      `236aa44d`. QA's remeasure found zero face (i) sessions in 2000.
    - Face (ii), a REPL SIGSEGV at the first call, is attributed by a
      discriminating control: a REPL turn executes into a restored module
      whose load is outstanding. Its correction is §7.1's *load before
      execution*. The same `src` visit makes the claim a scheduler-minted
      value that ends on every path (*one load entry*), closing review R-1
      and R-2. Committed at `236aa44d`; review found no blocking finding.
      `test`'s stress found zero failures of any face in 2000 sessions, and QA
      judged the evidence adequate on 2026-09-27. Open: the `fixed=` sha
      stamps and the user's Phase-5 acceptance.
    - All of it is private to `src/`, with no public API, carrier, schema or
      ABI change.
    - Open residuals: §7.1's fresh-dependency residual and the five
      *load before execution* exclusions, including *Claim and
      re-registration* (review FA-1, QA intake).
  - **Unaccepted gaps 2–6** (version conflict, write-time stash, same-session
    disk edit, platform signatures, absent prelude). These need a disposition
    through `sprint`.
  - **Deferred-entry drop (review F2).** A deferred entry is retried before the
    flush, so a child that imports `super` is recorded once its parent
    settles. An entry still unsettled then is not written; an earlier entry
    for the module stays (§7.6.2 grades that case). No `tests/cache.rs`
    cell covers a `super`-importing child or a mutual-import pair; that is
    `qa`'s fence gap.
  - **Index `.meta` structural fields.** The index-written table has empty
    `imports`, `exports` and `submodules`. A restore from it therefore walks
    none of its dependencies and rebuilds no aliases or fallback bit from them
    ([restoration parity](#75-restoration-parity)). This predates CD-1 and is
    unmeasured. Falsifier: in the REPL, let the index write a module that
    imports another, then import it and compare its restore with a fresh
    build. Attribution belongs to `qa`.
  - **Behaviour change and unmeasured points.** A changed recorded dependency
    now also skips the REPL entry-slot preload, so the module gets fresh
    numbering. Restore-time closure hashing and the trait-home reverse
    dependency are unmeasured.
  - **`dev` cleanup (review F5, F6).** `introduce_module` is an uncalled
    cache-install path that skips validity. Two compiler-owned module lists
    are duplicated.
- **Bare import and export module names (IR-1; implemented 2026-09-27).**
  The private correction applies §8.11.2's declared-child rule through one
  resolver. The former RED cell now passes:
  `tests/spec_08_modules.rs::import_and_export_of_undeclared_file_backed_child_resolve_to_root_module`.
  [§6.9](#69-bare-module-names-in-import-and-export) is the correction. It is
  built, independently reviewed and QA-adequate, with no public API, carrier,
  schema or ABI change. The residuals in §6.9 retain their QA intake status.
- **Abandoned restore after platform failure (verified 2026-09-24).**
  `reresolve_cached_platforms` runs after `install_cached_table`, so a
  platform-load miss returns `Ok(false)` with the decoded table installed
  ([cache-hit flow](#71-cache-hit-flow-inside-register_module)). No test exercises this branch. The falsifier: a cached module whose
  recorded DLL is absent at restore. Check whether the fresh build replaces the
  table and reports the load error, and whether a second importer's
  already-installed guard takes the stale table as satisfied. Attribution
  belongs to `qa`.

---

## 17. Sketch consultation

**Skipped.** The sketch was single-threaded and had no scheduler, no workers, no SharedState, no per-batch JIT, no observer contracts, no introspection store — none of int's load-bearing structures have a sketch antecedent. Decisions 31, 38, 39, 40, 41, 42 are all post-S58 reframings or pre-implementation commitments. Sketch consultation would have produced synthetic comparison content without value.
