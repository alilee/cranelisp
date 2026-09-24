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
- Macro-head recognition (`cranelisp_types::resolve_macro_head`) and reader-quote folding (frontend). int owns the Pass-1 expand walk and macro execution (`src/expander.rs`, `src/marshal.rs`; `src/CLAUDE.md` §"Macro expansion")
- Type inference (typecheck)
- Code emission (backend) — backend writes its own `Code::Jit` directly via Decision 41
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
- Per-batch JIT lifetime (Decision 31, amended by Decision 41 — per-symbol cardinality) — never a long-lived per-worker JIT.

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
3. **`Code` re-export per Decision 41.** `Code` lives in `cranelisp-backend/src/code.rs` (moved per Decision 41 from the previous `src/code.rs` location). int re-exports `pub use cranelisp_backend::Code;` for session-boundary `SymbolTable<Code, ()>` instantiation. Backend constructs `Code::Jit` directly inside `compile_to_module` and writes via `SymbolTable::write_code(&self, sym, code)`; int no longer wraps a backend return tuple. Principle 3 protection (no `cranelisp-types → cranelisp-backend` dep) survives intact.

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
| Cache orchestration | `cache.rs`; `cache_writer.rs` (background `.o`/`.meta` emit) |
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
- `process_form` after parse + macro expansion: write `source` + `sexp`.
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
- the cluster's forms ride the work packet (`PriorityWork::Typecheck`), kept on the
  scheduler's own `ModuleState` for requeue; no shared map parks forms or suspended state;
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

**Termination** — each gap advances dependency state monotonically, so each retry sees
strictly more committed state. The loop ends on success, a non-gap error, or a cycle error.

### 6.4 `notify_*` cadence

Per Decision 30 reframed by Decision 38 — scheduler notifications are *ordering* primitives (parallel macro-dep compilation, phased completion), not lock-safety primitives. Workers call:

- `notify_symbol_typechecked(fq)` after `check_form` writes the entry.
- `notify_typecheck_done(module)` after the last form in a module finishes.
- `notify_typecheck_done_from_cache(module)` for cache-hit (Decision 37) — enqueues `LoadObject` not `Jit`.
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
  if try_cache_hit_load(M):           # valid .meta.json + .o, decoded and installed
    re-resolve M's platform declarations
    register M with the scheduler as typechecked-from-cache  # enqueues LoadObject(M)
    recurse into M's imports          # cache-load or register fresh, per dependency
  else:
    register M for a fresh typecheck

codegen worker, LoadObject(M):
  map M.o through cache::load_cached_object -> per-target addresses
  store each address in its GOT slot
  attach Code::Linker(shared Arc<Linker>) to each restored entry
```

- **Order independence.** Typecheck, fresh or restored, fixes each module's GOT slot
  layout. Codegen fills slot contents, and cross-module calls read another module's
  GOT at run time, so modules load in any order.
- **No swallowed failures.** A restored callable whose address the `.o` does not
  define is a hard load error. A published NULL slot would be reachable from its
  callers.
- **A failed platform re-resolution is a cache miss.** If a recorded DLL cannot be
  loaded, the restore is abandoned and the module takes the fresh path, which reports
  the load error normally.
- **Restoration parity.** A restored world must match a fresh one
  (`cache-hit-loading.md` §0).

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

```text
regenerate_backing_file(module):
  let st = shared.symbol_tables.get(module)?;
  let intro = shared.introspection.as_ref().ok_or(IntrospectionRequired)?;
  let mut text = String::new();
  for sym in st.defn_order():
    let fq = FQSymbol::new(module, sym);
    if let Some(info) = intro.get(&fq):
      if let Some(src) = &info.source: text.push_str(src); text.push('\n');
  atomic_write(module_file_path(module), text);
```

The old `module_sources: DashMap<ModuleFullPath, Arc<str>>` field on SharedState is GONE. Per-defn source on `Introspection.source` is the only source store. Cited principle: P7 (single source of truth — per-defn source has one home).

### 8.4 Watcher integration

Per `facades/int.md` invariants 7 + 8 + bounded-context §6.2:

1. REPL never calls `wait_for_*` at startup — the prompt is responsive immediately. The first iteration's STEP 4 `wait_for_inmem_codegen()` catches up the entry module's code.
2. `set_repl_input_active(true)` opens the watcher window during `read_line`; `set_repl_input_active(false)` closes on input submission. STEP 4 catches up everything triggered during the prompt.
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
   tolerance for an empty `written_trait_impls` vector (`cache-hit-loading.md`
   §0).
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

---

## 13. Decision register (int-relevant)

Active Decisions affecting int (operative this sprint or constraint-bearing):

| Decision | Headline | Status for int |
|---|---|---|
| 30 | Form-by-form scheduler deadlocks on mutual imports | int's scheduler exhibits the deadlock; workaround via `discover-tests` |
| 31 | One `JITModule` per batch; `Arc<Jit>` on entry; custom Drop | Operative (§5.3); no current test observes reclaim |
| 35 | `Code` owns lifetime only; addresses live in the GOT | `Code` lives in `cranelisp-backend`; int re-exports it and instantiates the session table (§5.1) |
| 40 | `trace.rs` + `io_trace.rs` relocate to int; runtime exposes `IoObserver` | Pre-implementation; FIXME 0103 |
| 41 | Backend publishes slot addresses and returns artifacts | Operative for slot publication and artifacts; int attaches `Code` (§7.2). The compile batch, not the symbol, is the JIT unit (§5.2) |
| 42 | `PlatformError` adopts `ErrorLocation`; lives in `cranelisp-types` | Pre-implementation; FIXME 0104 |

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

## 16. Open questions / FIXMEs filed

### 16.0 Open Binary/int obligations (verified against source 2026-09-21)

The S121 C6 visit delivered most of its bundles; these obligations remain open
in source. Each owning filing stays the tracker; this list is the design intent.

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
- **Import-alias key mint (FIXME 0798 residue).** The fresh and restore
  import-alias writers in `src/imports.rs` still key through the private
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
  instance-key mismatch as stale (`cache-hit-loading.md` §0). Whether other
  invalid decoded lifecycle states can restore is unmeasured; attribution
  belongs to `qa` and the fix, if needed, to the types/backend owners.
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

**S64-era FIXMEs (0098/0099/0100/0103/0104/0108) have all CLOSED** (W-Macro, the trace relocation, the platform-interface landing, the display absorb, and the cluster-atomic restructure resolved them — verified against source S81). The current int FIXME backlog (S81 "clean & green", Phase 3 design):

**S81 Wave 9a — light int items:**

- **FIXME 0013** (`/int`) — `observability.rs::reset_panic_hook_installed_for_tests` mutates process-global panic-hook state without a serialisation lock. Add a `static TEST_GUARD: Mutex<()>` and take it at the top of every test that touches the install path. ~10 LOC; test-only; no baseline impact.
- **FIXME 0217** (`/int`) — inline-module spec §8.2.2 step-2 parent-file rewrite. `handle_mod` (`worker.rs:2650`) calls `write_inline_mod_to_disk` (step 1) but never rewrites the parent file's `(mod name forms…)` → `(mod name)` (step 2). Real behavioural gap (the "one-time creation" + "indistinguishable from manually created" semantics are violated; `inline_body` persists in the symbol table forever). Needs the rewrite + a reload of the parent's structural decls + a new integration test (target /qa for the test). Files: `worker.rs`, possibly `repl/spec/15-session-persistence.md` §15.4.
- **FIXME 0266** (`/dev (int)`) — move the `trace` SpecialForm metadata entry from the `primitives` module to root `""`. As-built: `bootstrap.rs::register_trace_type` (~L894) inserts it into the `primitives` table; the 2026-06-04 root-special-form ruling + corrected FIXME 0241 Trace row require it at root `""` alongside the structural special forms. ~1-line mount-move (the `Trace`/`TraceCall` ADT + accessors STAY in `primitives` — form/ADT asymmetry). Regression check: `/imports`/`/exports primitives`/`/info trace` reflect the new placement; recognition is parser-side (`Expr::Trace`) and does not consult this entry, so dispatch is unaffected.

**S81 Wave 9b — FIXME 0109 Waves A/B/C only** (see §3.4). The carry boundary: Wave D + the dependent observability harvest cluster co-carry to the next arc sprint.

**Verify-and-plan / cross-skill-gated:**

- **FIXME 0101** (`target: /sprint`) — runtime + platform audit-pass scheduling. **NOT an int-impl item** — it is a `/sprint` scheduling request for `audits/runtime-*.md` + `audits/platform-*.md` passes, and it concerns the runtime/platform crates, not `src/`. No int action; flag to `/sprint` that it sits outside the int component clearance.
- **FIXME 0220** (`target: /arch`) — cache-hit Introspection rehydration. **/arch design question first** — the FIXME explicitly filed `target: /arch` to arbitrate WHERE the rehydration trigger sits (lazy-per-symbol vs eager-per-module vs per-first-edit) + WHETHER to serialize a minimal per-symbol `source_range: Option<Range<usize>>` into the cache. Until /arch rules, the int implementation (a `SharedState::rehydrate_introspection(fq)` private path) cannot be specced. **Blocked on /arch; not actionable as int-impl this wave.** Surface to `/sprint` as needing an /arch ruling before any int wave can take it.
- **FIXME 0281** (`target: /design`) — int-facade trim of the dead `priority_boost_jit`/`wait_for_inmem` priority-codegen machinery. **Folds into FIXME 0298** (the int-facade retire/doc-reorg, a W1 doc item, `target: /arch`). The source already deleted the subsystem (S76 W3 — confirmed: `priority_boost_jit`/`wait_for_inmem`/`PriorityEntry`/`BlockingJitCodegen` are gone from `scheduler.rs`; only `unblock_module` remains); `facades/int.md` still describes it (L649-650, L1077, L1195-1196, L1229). Since 0298 retires `facades/int.md` wholesale (migrating its internal-orchestration content to `design/int/` + `src/` rustdoc), the 0281 trim is subsumed: the dead pseudocode simply does not carry over into the migrated docs, and `scheduler.rs`'s `unblock_module` is documented in its rustdoc. **Recommendation: close 0281 as folded-into-0298** rather than authoring a standalone facade patch on a doc that is being retired. (If 0298 slips past S81, do the standalone trim as a fallback.)

**FIXME 0316 consumer-side (int half of the Wave-1 0316 work):**

- **`insert_detecting_ambiguity` terminal-resolve** (`imports.rs:282-332`, `target: /dev (int)`). Per the /arch Phase-3 ruling (SPRINT.md §3): before emitting `Ambiguous`, chain-follow BOTH the existing and incoming `Import` edge to their terminal `(home_module, canonical_symbol)` via `cranelisp_types::resolve_terminal_entry_and_home` (already `pub` — confirmed exported at `resolve.rs:67`; NO promotion needed) and dedup if the terminals match. Replaces the immediate-source `s1 == s2` test at L301. Pure spec-conformance fix (§8.6.4 "same original definition is NOT ambiguous"). The existing visibility-upgrade branch (L297-309) stays. Needs a /qa test for the glob+re-export-specific overlap case.
- **`recognize_macro_head` collapse to `resolve_with_fallback`** (`expander.rs:262`, the `pub(crate) fn`). Once /arch authors `cranelisp_types::resolve_with_fallback` (the new pub fn unifying the 5 prelude-fallback wrappers — types-side, /arch-owned, lands Wave 1 first), the expander's hand-rolled 3-step retry (first-hop resolve → on-miss-if-bit-on retry-rooted-at-prelude → public-only filter) collapses to one call. **Cross-crate dependency: int rebuilds against the new types seam AFTER /arch lands it.** The 4 checker.rs wrappers are typecheck-owned (the int half is just this expander wrapper). No int baseline impact (binary).

These are tracked in `design/arch/fixmes/NNNN-*.md`; this section mirrors them for design-intent visibility. The S64 audit-recommendation items (`scheduler_trace/` rename, subordinate-doc sweep) are retired: the `*_trace` rename did not survive the S76 trace relocation, and the doc-currency sweep is subsumed by the 0298 facade-retire reorg.

### 16.1 S114 Track C (src/) — design-of-record

Four design-bearing items + three riders, each with a subordinate doc or a
dev-direct disposition:

- **FIXME 0638** (macro-alias double-free ×5) — the current cure is the
  single-owner transfer in `macro-turn-ownership.md` Rules 1–3; Rule 2 records
  why it does not reopen the defect, and the five pins guard it.
- **FIXME 0670** (int qualifies a value binder) — `expansion-qualification-scope.md`.
  `qualify_expanded_sexp` becomes scope-aware, skipping the value-level binder
  slots (defn/fn params, let names, match var-patterns) by sharing the expander's
  `is_binding_form`/`params_scope`/`pattern_binders` enumeration. Wave-1 of the F8
  three-wave chain (int-first, strict; then frontend reject re-lands, then cells).
- **FIXME 0604** (foreground prelude-table write race) — closed structurally by
  the export-closure gate, §6.7, which also records its evidence limit.
- **"in expansion of" on the def/const finalize path** (S113 carry) —
  `macro-diagnostic-reanchoring.md` §2.1. Second application site of the existing
  pure re-anchor transform at the `check_program_compat` finalize seam
  (`process_form.rs:468`); no new mechanism.

**Riders (dev-direct — design constraint noted, no subordinate doc needed):**

- **FIXME 0671** (PS-D1 — impl-confirmation line stamps the asking module, not
  each name's canonical home; `src/repl/format.rs:497-501` + `:707-710`).
  **Dev-direct** under `resolve-home-enumeration.md` §3 rule-1 authority — the
  design constraint is the only load-bearing part: resolve the **trait's** home
  (chain-follow the trait ref / `TraitImpl.impl_module` back-pointer) and the
  **type's** canonical home each **once**, and root the `impl <trait-home>/Trait
  for <type-home>/Type` line at those homes — never `push_fq_name(module, …)`
  from the asking module (P24 "resolve once", P26 read the settled home). Same
  CLASS as the S112-guarded `impl user/Functor for user/Functor` defect. `/testing`
  pins first (repl/spec.md §1.3); `/repl` tightens §1.3 to the canonical-home rule
  (6b). No int design elaboration beyond this constraint.
- **FIXME 0674** (startup restore notice, `repl/spec/15-session-persistence.md` §15.2.2) — **dev-direct**.
  Implement at the session-restore seam: emit `; resumed N definitions from
  <file>` when startup restores a **non-empty** backing file, **suppressed** when
  absent/empty (fresh-dir transcripts stay byte-identical). Count = restored
  **definitions** (§15.7), not transient expressions; startup chrome, never
  persisted. Land the guard both ways. Wording/count/empty-suppression are
  `/repl`-owned (spec'd); no int design elaboration.
- **FIXME 0675** (cheatsheet multi-sig settled facts, `src/syntax/cheatsheet.txt`)
  — **dev-direct**, pure static-primer content. `/repl` specifies the exact
  `INDEPENDENT` block (0575: `fn` single-arity, multi-arity is `defn`-only; 0576:
  clauses type-check independently, shared param names carry no shared type),
  inserted after `EXAMPLE`, before `NOT`. No test owed; no int design elaboration.

---

## 17. Sketch consultation

**Skipped.** The sketch was single-threaded and had no scheduler, no workers, no SharedState, no per-batch JIT, no observer contracts, no introspection store — none of int's load-bearing structures have a sketch antecedent. Decisions 31, 38, 39, 40, 41, 42 are all post-S58 reframings or pre-implementation commitments. Sketch consultation would have produced synthetic comparison content without value.
