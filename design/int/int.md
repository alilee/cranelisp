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

**S121 correction, approved 2026-09-04.** Committed publication outcomes leave
processing in one stack-owned, move-only receipt and are settled once by eval,
dependent recheck, or the pool route before that route handles `Done`, `Gap`,
or `Err`; neither scheduler/session state nor source continuation stores them.
Source does not realise this receipt; §16.0 records the gap. Public exposure is guarded only at `NameCandidate` routes—the obsolete
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

1. **`CompilerSession` is the high-level facade.** A single object that `::main` constructs and drives. Construction is fallible and returns `Result<CompilerSession, CranelispError>` because bootstrap uses the same fallible lifecycle machine as every other birth route. It wraps an `Arc<SharedState>` (the worker-shareable subset) plus initiator-thread-only state (watcher channel, REPL eval cursor, worker pool handles, accumulated warnings). Every CLI mode (`--run`, `--link`, REPL) constructs the same `CompilerSession`; the only difference is which methods are invoked after `register_module`. Per Principle 11 (single pipeline; mode parameters) — there is exactly one `process_form`, parameterised by mode (and the mode discriminator IS `shared.introspection.is_some()`, not a separate flag).
2. **No re-exports of `cranelisp-types` items beyond the checked Binary/int
   public surface.** Per Principle 15 (facade types live with their behavior),
   int imports from each implementation crate directly. Any convenience
   re-export is retained only when it remains present in the current checked
   public surface; the root library has a small consumer audience.
3. **`Code` is re-exported, not defined, here.** `Code` lives in `cranelisp-backend`; `src/code.rs` re-exports it and instantiates the session table (§5.1). Backend fills GOT slots inside `compile_to_module`; int attaches the `Code` owner afterwards (§7.2). `cranelisp-types` never depends on backend (Principle 3).
4. **The test harness has one public entry.** `CompilerSession::run_tests` returns a `TestRunReport` whose accessors are its text, its warnings and its exit code; the user approved this delta on 2026-09-28. It is the only public item the `--test` harness adds. Selection, the eligibility scan and the run-and-report core that it shares with `/run-tests` and `/run-all-tests` stay crate-private ([test runner](test-runner.md)).

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
| Cluster processing | `cluster.rs` (`process_cluster` → `ClusterOutcome::{Done, Gap}`; `ProcessedCluster` carries warnings, resolved imports, introspection records, the committed `RedefinitionOutcome`s and the boxed `PreparedCommit`, which lives in `worker.rs`). The approved move-only publication receipt is not realised; see §16.0. |
| REPL eval | `eval.rs` (form-chain eval, bare-symbol introspection, dep registration); `repl_input.rs` (the `ReplInput` TTY/non-TTY abstraction) |
| REPL command/display surface | `src/repl/` — five files; §3.3 states the structure and `src/CLAUDE.md` §"Session/REPL module map" lists the members |
| Live redefinition | `redefine.rs` — the guarded-redefinition gate, blocking-dependent scan, instance-rematerialization policy, `RedefKind` slot classification and the retention pool (`session-transaction.md`); it still carries the superseded dependent-recompilation machinery recorded in `design/int/int.md` §16.0 |
| Import/export + prelude fallback | `imports.rs` (+ `imports/tests.rs`) — the int-side installer; the `prelude_fallback` mechanism (`src/CLAUDE.md` §"Prelude as a resolution FALLBACK") |
| Bootstrap seeds | `bootstrap.rs` — `mount_synthetic_modules` (special forms, intrinsic types, `macros`/`Option`/`IO`/`Trace` seeds) |
| Macro execution | `expander.rs` (the `JitMacroExpander` invocation core + expand loop); `marshal.rs` (sexp marshaling) |
| Display / pretty-print | `display.rs` (`display::envelope` + value render); `pretty.rs` (`pretty_print`/`pretty_print_plain`); `styled.rs` (the `Role`/`StyledDoc` vocabulary + `styled::render`, the sole style-table site); `style.rs` (raw style helpers); `syntax.rs` |
| Save / regenerate | `save.rs` — `regenerate_backing_file` (Decision 39; source-text-first regen, `src/CLAUDE.md` §Degraded startup) |
| Cache orchestration | `cache.rs` (the `ObjectCache` facade over session cache state: the validity query, loaded-source records, deferred entries); `cache/dependency_record.rs` (the dependency record, its one edge set, the one builder, deferral and the current-hash source, §7.6); `callee_edges.rs` (the one callee enumeration, shared with `redefine.rs`, §7.6.1); `session_v4/nice_worker.rs` (the `.meta`/`.o` and manifest writer); `session_v4/index_worker.rs` (index `.meta` writes); `process_form/cache_restore.rs` (restore). `cache_writer.rs` has no caller |
| `--link` + exe-bundle | `exe.rs` (`validate_main`, alias-`.o`, linker invoke); `link/{mod,gnu,apple}.rs`; `crates/cranelisp-exe-bundle/` |
| Platform DLL orchestration | `platform.rs` (+ `platform/tests.rs`) — `load_platform_dll`, `/platform-schema`, `ABI_VERSION` gate; `marshal.rs` (host↔DLL) |
| Auto-IO scheduling (compile-time) | `bind_chain_analysis.rs` (+ `bind_chain_analysis/tests.rs`) — §10.12 `bind!`-chain → `ParBind` / `LaunchContinue` transform (`bind-chain-analysis.md`) |
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

`src/CLAUDE.md` §"Session/REPL module map" lists each file's members. The design rules:

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
  `Resolved::canonical` by direct probe (`crates/cranelisp-types/CLAUDE.md` §"Resolution
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
1. **Phase 0** in `register_module`: `entry(m).or_default()` → `write_structural_decls(decls)` + `defn_order` seed → drop RefMut. Microsecond-scale; once per module.
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

```text
register_module(module):
  parse → ParseProduct { forms, structural }
  // Phase 0: brief &mut SymbolTable hold
  {
    let mut st = symbol_tables.entry(module).or_default();
    st.write_structural_decls(structural);            // imports/exports/platforms/submodules
    st.seed_defn_order(forms);                        // first-registration order
    // RefMut drops here.
  }
  // Cache-hit decision lives in the recursive flow per Decision 37 (§7).
  scheduler.register_module(module);                  // dispatches PriorityWork::Typecheck
  for each import in structural.imports:
    register_module(import.module_path);              // recursive
```

The Phase 0 block is microsecond-scale. The RefMut drop *must* happen before `scheduler.register_module` so workers picking up `PriorityWork::Typecheck` find the SymbolTable reachable via shared `.get()` only.

**Queue-priority rule (`delays_other`)** — `scheduler.register_module(module, delays_other)` routes the module into the prioritised `TypecheckFirst` queue when `true` and `TypecheckNext` when `false`. The flag answers one question: *is some other module's progress waiting on this one?*

- **Every dep-registration site passes `true`** — the `process_form/dependency.rs` handlers and drive seam (both cluster wrappers, §6.2) and the cache-restore transitive-import registration. A dep is registered precisely because something is blocked on it, and even where the immediate registrant has already finished (cache-restore's fire-and-forget recursion), any other module importing that dep will block on it.
- **`false` is for entry-module registration by the thread that is itself the whole-world waiter** — `register_module_with_source`, `reload_module`'s watcher-seed fallback, and `recover_startup_failure`'s re-drive. Nothing else is queued behind them.

A `false` at a dep site is a silent divergence: the dep lands in the unprioritised queue behind unrelated work while a blocked caller waits. (S59/S60 lineage; the rule is the one durable residue of the dual-path persistence collapse.)

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
cycle error at the import site, not a deadlock.

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
auto-loads through the same `drive_module_dep` seam (`src/CLAUDE.md` §"FQ auto-loading").
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
  - A prelude restored from cache establishes the same fallback as a fresh load
    ([restoration parity](#75-restoration-parity)).
    `tests/cache.rs::cache_repl_minimal_plain_fn_prelude_restored_on_session_2`
    guards the REPL second-session shape.
  - Only public prelude bindings are reachable as bare names.
  - `/imports` lists prelude-provided names in a separate `Prelude (implicit)` group when
    the bit is ON.
  - `SymbolTable.imports` records only user-authored `(import …)` forms. The implicit
    prelude import is never recorded there: source regeneration and duplicate-import
    warnings reason about what the user wrote. Its resolved effect lives in the
    module's name candidates. `writer_does_not_record_implicit_prelude_in_imports`
    pins this.

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
      dependency wait, a T1 redefinition rollback, or degraded startup
      recovery) also resets a failed cached load, but it leaves the
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
    - *Claim and re-registration.* A claim is not bound to the registration
      it was granted for. Import turns do not wait for cached loads, so a
      watcher reload can re-register a restored module while a pool
      worker's claim is still loading it. The stale load keeps storing GOT
      slots and publishing code owners into the live table, and its loaded
      completion marks the fresh registration in memory, so an in-memory
      wait covering that module can return before its fresh code is
      compiled. This predates RR-1. Falsifier: edit a restored module's
      source while its cached load is outstanding, then call into it, and
      observe the pre-edit body or a signal.
- **Fresh dependency of a restored module (open residual).** When the walk
  registers a dependency fresh because its cache entry misses, that
  dependency's table need not exist when the hold releases. `M`'s load can then
  fail with an unresolved GOT symbol although the program is valid. `M.o` also
  embeds slot indices from the build that wrote it, and nothing yet shows that
  a fresh rebuild of unchanged source assigns the same ones.
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
  every module reachable from M through its edges to the source hash of the
  version M was compiled against. M itself is excluded.
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

  The restore walk loads a subset of these edges ([cache-hit flow](#71-cache-hit-flow-inside-register_module)).
  It skips name-less imports, the implicit prelude and lookup dependencies.
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
cache schema 30 (`sprints/SPRINT.md` §"Lookup dependency implementation
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
    The owed facts are its checkable entries, its reload demands and its
    accumulated lookup dependencies. See
    [the empty-publication correction](#7621-empty-publication-correction).
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
  - The prepare step already takes the decision "nothing to check, yet
    something to publish" for reload demands. It starts from an empty
    staging, and the demands add their targets. Extend that decision; do not
    add a second one.
  - The attempt's lookup dependencies travel into the prepare step beside
    its reload demands, as one value holding both. The value's own emptiness
    test is the whole no-publication condition. A fact later added to what an
    attempt owes joins that value, so the decision cannot omit it (Principle
    7, Principle 26).
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
    - a cluster with no checkable entry, no reload demand and a lookup set
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
3. Watcher events do NOT flow directly into compilation. They cross to the REPL cadence at a poll point and become `re_register_module` calls.

`watch.rs` owns the `notify`-based watcher and the `WatcherChannel` mpsc. The REPL polls at prompt boundary; the prompt-window mechanism is the closure that prevents mid-input watcher interleave.

### 8.5 Slash commands — composed flows over the existing primitives

Per `facades/int.md` §"Composed introspection flows": slash commands are composed flows over `CompilerSession` accessors and other facade calls — not new facade surface. The 17 commands (`/sig`, `/doc`, `/help`, `/type`, `/info`, `/source`, `/sexp`, `/ast`, `/clif`, `/disasm`, `/time`, `/mem`, `/list`, `/imports`, `/exports`, `/expand`, `/mod`, `/reload`, `/run-tests`) all dispatch through `Sess::process_commands`, which decodes the input into a `SlashCommand` enum and either reads the introspection store directly (`/source`/`/sexp`/`/clif`/`/disasm`/`/time`), composes a frontend / typecheck call (`/expand`), or composes a runtime-side primitive (`/mem`, `/run-tests`).

Universal output format (Sprint 14): `:Type {value|name} ; {classification} - {docstring}` + optional related symbol comment lines. Defined in `repl/spec.md`; implemented across `Sess::format_*` family.

### 8.6 Live redefinition — guarded publication and slot versioning

`repl/spec/18-redefinition.md` §18 is normative: a replacement is fully checked
and compiled before live state changes, and an ordinary callable redefinition
never recompiles a dependent, marks a symbol broken or installs a trap. Int
realizes it inside the ordinary prepared transaction:

- the guard rejects a declaration-class or visibility change, a
  language-type change with a blocking dependent, and a same-type replacement
  whose ownership ABI differs;
- an admitted generic base or overload family rematerializes its prior
  concrete instances into the same candidate (`design/int/s122-closure.md` §2);
- the commit gate's `RedefKind` decides slot reuse versus a fresh slot, and
  every displaced compiled owner enters the session retention pool.

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
| GOT trace | `CRANELISP_GOT_TRACE=1\|*` | GOT-slot writes: JitWrite, LinkerWrite, Redefinition, SlotFreeze, TrapPatch | `src/got_trace.rs` |
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
14. **Persistent publication receipts** — committed outcomes in a scheduler
    mailbox, `SharedState`/`ModuleState`, parking record, cache field or source
    continuation (`s117-conformance-recovery.md` §1.1.3).
15. **A binding-shaped closure gate** — any exposure predicate over `Binding`
    beside the [candidate-shaped export-closure gate](#67-public-candidate-exposure--the-export-closure-gate).
16. **A bootstrap lifecycle panic** — `unwrap`, `expect` or `unreachable!`
    asserting a fallible lifecycle transition during session construction.
17. **Dependent recompilation on an ordinary redefinition** — re-typechecking,
    recompiling, breaking or trap-patching a dependent where §18 requires
    rejection (`session-transaction.md` §0).
18. **A second program-result releaser or an unguarded release target** — a
    release key re-derived from the observed type, a raw glue address without
    its `Code` owner, or an `IO` branch in a formatter (`result-owner.md` §7).
19. **A second bare-module-name rule** — deciding what a bare `import` or
    `export` module name refers to from symbol-table registration, a file probe
    or form order. Reading a persisted spelling as an absolute module outside
    the one resolver is also rejected
    ([§6.9](#69-bare-module-names-in-import-and-export)).

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

`design/int/CLAUDE.md` §"Document index" is the triage of record: it names the
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

- **`--test` and the shared test runner (S122, ACT-0988).** Implemented in
  source as [test runner](test-runner.md) describes; the obligation closes on
  verification, which is pending. Its open items are the verification state
  recorded in that design's status line; no design decision is outstanding.

- **Persistence corrections (S122, ACT-0998).**
  - Records are written only from published state
    ([session persistence §2.4.1](session-persistence.md#241-who-writes-a-record)),
    and a cache-installed module is recompiled before `/mod` makes it current
    ([§2.4.5](session-persistence.md#245-editing-a-cache-installed-module)).
    Both are implemented in the working tree. QA judged them adequate on
    2026-09-28, subject to the review repairs its delta names. Open: commit
    and the user's Phase-5 acceptance.
  - **Restart boundary.** A reload that would change a
    live type's structure fails with the restart remedy, and the saved file
    is retained until a successful reload or a restart (REPL §14.8, §18.5).
    The design is the guard's type pass
    ([session transaction §2.6](session-transaction.md#26-type-re-establishment-repl-185-148))
    and the restart-required marker
    ([REPL lifecycle §1.3.1](repl-lifecycle.md#131-restart-required-failure)).
    A reload's outcome is the reloaded module's own state
    ([§1.3 Outcome](repl-lifecycle.md#13-failed-reload)). The imported-module
    case relies on the barrier fail-fast
    ([error cascade §4.1](step9-error-cascade.md#41-cascade-construction)).
    Each of these sections names its guards. There is no public API change.
    - The open design risks are the §1.3 Outcome coverage hypothesis and
      §4.1's order-dependent stranding face. Each is asserted with a named
      falsifier, and neither is measured.
- **Annotation-mirror tail (FIXME 0708).** Four lexical `src/` mirrors of the
  retired pre-fold annotation shape survive and each goes one way:
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
  one types-owned mint is the only key source (§12.1 reject 4).
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
- **Superseded dependent-recompilation machinery.** `src/redefine.rs` still
  contains the S101–S103 transaction (`run_transaction`, `mark_broken` and trap
  stubs, the T1 end-of-turn reload and its error block, `TransactionReport`
  sections). It serves no current requirement and should delete
  (`session-transaction.md` §0). Reachability differs by leg. The per-symbol
  transaction runs only for an admitted language-type change, which the guard
  admits only without a blocking dependent, so its closure should be empty
  (read from source). The T1 reload is not guarded that way: a redefinition
  where either the prior or the staged entry is slot-less — for example a
  same-type generic body edit after realization, which changes no slot shape —
  whose target has compiled callers satisfies `is_t1_downgrade`, and
  `drive_t1_full_cure` would then reload the target and dependent modules,
  which §18.1 excludes. `qa`'s S122 REPL probe of that shape (generic `f`,
  named compiled caller `g`, same-type body edit, concrete twin as control)
  observed conforming public behaviour: `g` returned the new value, the turn
  printed only the ordinary confirmation, and no dependent was visibly
  re-typechecked. Whether the reload leg executed is still unobserved — the
  probe's sentinel was unarmed and confounded by stale macro persistence — so
  this remains a suspected defect, not a confirmed one. The discriminating
  observation is at the seam: whether `drive_t1_full_cure` reaches
  `reload_module` on that input.
- **Unrealised publication receipt.** The approved 2026-09-04 rule (the S121
  correction above; `s117-conformance-recovery.md` §1.1.3) moves committed
  outcomes in a move-only `PublicationReceipt` owned by a `ProcessAttempt`
  wrapper. Neither type exists in `src/`. Committed `RedefinitionOutcome`s
  ride `ProcessedCluster` inside `ClusterOutcome::Done`, and eval settles them
  through `apply_redefinition_outcomes` only on paths that reach it; an error
  returned from `codegen_and_execute` skips settlement. Standing reject 14
  holds: nothing stores the outcomes in scheduler or session state. Today the
  only consumers of those outcomes are the superseded machinery above, so
  whether the rule is still owed or retires with that machinery is an
  authority question for `arch` and the user, not a wording fix.

---

## 17. Sketch consultation

**Skipped.** The sketch was single-threaded and had no scheduler, no workers, no SharedState, no per-batch JIT, no observer contracts, no introspection store — none of int's load-bearing structures have a sketch antecedent. Decisions 31, 38, 39, 40, 41, 42 are all post-S58 reframings or pre-implementation commitments. Sketch consultation would have produced synthetic comparison content without value.
