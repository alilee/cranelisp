# Concurrency architecture — the compiler-internal scheduling axis

**Owner**: `design` (int). **Status**: current — the single inventory of where
the binary/integration layer is concurrent, why, and which document carries each
invariant.

**Scope.** This is the *compiler-internal* scheduling axis only: the scheduler,
the worker pool, the session data plane, and the diagnostic/host edges. The
**language-level** effect-concurrency runtime (atomic RC, IVars, sparks, the IO
reactor) is a runtime-library concern owned by `design/intrinsics/reactor.md`
and `design/arch/effect-concurrency.md`; `/int` is a host-client of it
(`design/int/CLAUDE.md` §Ownership), not its designer. Do not record runtime
concurrency here.

**Diagram companion**: `design/int/concurrency/` carries the as-built structural,
protocol and lifecycle views of the same inventory.

## 1. Where concurrency is justified

Concurrency is admitted in four places, each because it buys something the
serial shape cannot:

1. **Inter-module compiler throughput** — independent modules typecheck and
   codegen in parallel.
2. **Latency hiding for macro expansion** — a macro dependency needs callable
   code while other work continues.
3. **Background object production** — `.o` output and cache writes are lower
   urgency than the in-memory code an execution needs now.
4. **Asynchronous host edges** — OS file-change notifications and per-thread
   diagnostic capture must not block the REPL loop.

Everything else in `src/` is serial by intent. A new concurrent surface needs
one of these four justifications or it does not belong here.

## 2. Inventory of current structures

### 2.1 `CompileScheduler` — the coordination kernel

`src/scheduler.rs`. Owns module lifecycle and work coordination only — never
ASTs, symbol tables or compiled code. All scheduler state sits behind one
`Mutex<SchedulerState>`.

Interface groups: registration (`register_module`, `register_module_cached`,
`re_register_module`), worker claim (`take_priority_work_blocking`,
`take_object_codegen`), waiting (`block_for_typecheck`,
`wait_module_inmem_complete_blocking`, `wait_inmem_complete`), completion
(`notify_typecheck_done`, `notify_inmem_codegen_complete`,
`notify_object_codegen_complete`), plus failure/reset/shutdown.

Blast radius is systemic, so the scheduler is the one place where a change must
be argued against the whole protocol rather than a local call site.

### 2.2 Worker pool — priority and nice workers

`src/worker_pool.rs` owns spawn, parking and join for both worker classes;
`src/worker.rs::priority_worker_loop_shared` and
`src/session_v4/nice_worker.rs::nice_worker_loop` are the two loops. Workers are
session-persistent: spawned at session init, parked on a condvar, joined in
`Drop`. The delivered lifecycle contract — spawn, park/wake, enqueue-not-spawn,
per-batch JIT, shutdown ordering and its acceptance criteria — is
`design/int/persistent-workers.md`, which live source and tests cite by section.

Priority workers carry the typecheck/JIT path and the dependency service;
nice workers consume `TypecheckDone` modules, compile object output and write
cache artifacts.

### 2.3 `SharedState` — the concurrent session data plane

`src/session_v4.rs::SharedState`. Field-level protection is explicit (`Mutex`,
`DashMap`, atomics); the design constraint is *who may reach a field*, not
whether the field is safe.

| Group | Fields |
|---|---|
| Authoritative compiler state | `symbol_tables`, `typecheck_products`, `next_type_id`, `module_aliases`, `prelude_fallback`, `declared_exports`, `introspection` |
| Session, config and cache support | `project_root`, `lib_dirs`, `platform_dirs`, `cache`, `file_to_module`, `run_mode`, `promote_nice_workers` |
| Lifetime and retention roots | `kept_dlls`, `retained_code`, the scheduler reference |
| Test-run support | `test_runner_state` |

Two field groups that earlier revisions of this document recorded are **gone**,
and their absence is load-bearing:

- the cross-thread publication/resumption maps (`module_sexps`,
  `suspend_states`) were deleted by the S78 in-call-stack cluster restructure —
  a caller's cluster state lives on its own stack frame and no worker reads it
  (`design/int/int.md` §6.2);
- REPL-only state (`current_module`, `repl_check_state`) and the duplicate
  `cached_modules` store were removed (S67 Cluster B); the scheduler's
  per-module set is the single cached-module authority.

### 2.4 Dependency publication and readiness

`src/process_form/dependency.rs` is the one dependency service:
`handle_import` discovers, `register_dep` registers, and the caller blocks on
the scheduler. `Session::register_dep_for_eval` (`src/eval.rs`) is a **scoped
wait only** — it does not re-register, re-publish or republish caller sexps,
because the cross-thread map those steps fed no longer exists.

The phase-ordering invariant that makes readiness observation safe is the
signature/body pre-pass barrier: `design/int/signature-body-prepass.md`.

### 2.5 Symbol publication and typecheck visibility

`SharedState.symbol_tables`, typecheck's `ensure_module_exists` and form
finalization, `notify_typecheck_done`, and the readers that observe readiness
then read tables.

Its invariants are carried by construction, not by prose, in two companion
documents: `design/int/index-worker-isolation.md` (the background index feed)
and `design/int/int.md` §6.7 (the foreground export-closure gate, including
candidate-batch validation before table or GOT publication).

### 2.6 Code publication, GOT and retention

`src/code.rs`, `crates/cranelisp-types/src/got.rs`, backend JIT/linker results,
and `ModuleEntry::Def.code`. Compiled code lives on symbol-table entries; the
GOT slot swap is the dynamic publication mechanism; `Arc<Jit>` / `Arc<Linker>`
carry the lifetime root for the raw code pointers baked into compiled callers
and heap closures.

Retention of a *displaced* owner is the session retention pool
(`SharedState.retained_code`), specified in
`design/int/session-transaction.md` §6–§7 under Principle 22. This is the
surface where raw pointers, `unsafe impl`s and temporal lifetime invariants
meet; keep the concurrency narrow and the invariants named.

### 2.7 Cache-hit loading

`try_cache_hit_load` (`src/process_form/cache_restore.rs`),
`load_cached_module_via_linker` (`src/worker.rs`) and
`register_module_cached`. Metadata restores cheaply, in-memory code loads when
needed, and a cached module joins the same scheduler-driven pipeline as a fresh
one after registration. Design: [`int.md` §7](int.md#7-cache--linker-orchestration-decisions-34-37).

Cache-hit publication has explicitly narrower retention guarantees than staged
or compiled publication — see `session-transaction.md` §6.1.

### 2.8 Platform DLL retention

`src/platform.rs::LoadedPlatform` and `SharedState.kept_dlls`. Load once, retain
the `dlopen` handle for the session lifetime, and reach the platform functions
through GOT-indirect dispatch over a slab whose validity rests on that retained
handle; call sites never manage DLL lifetime. The loader ABI gate and
`/platform-schema` are in `design/int/io-integration.md`.

### 2.9 File watcher

`src/watch.rs`. OS notifications arrive on a callback thread and are handed to a
channel; the REPL polls at prompt boundaries (`poll_changes`) and content
hashing (`update_content_hash`) suppresses self-writes and metadata noise. The
watcher owns its callback, channel and hash state; compiler logic sees only the
polling interface.

### 2.10 Observability

`src/observability.rs` (scheduler trace), `src/io_trace.rs`, `src/got_trace.rs`.
Per-thread ring buffers, `publish_thread_buffer` on thread shutdown,
merge-sorted `flush_to_stderr`, parse-once env gating, panic-hook installers.
Diagnostic-only and narrow. Design: `design/int/observability.md`.

## 3. How this surface is kept under control

The race lineage this surface went through (S61 H4→H6, then S78 and S93) settled
four standing rules. They are the transferable part of that history; the record
itself is `design/int/heisenbug-race-closure.md`.

- **Prefer removing concurrency to proving more of it.** When a surface is hard
  to model or structure-test because too many components race at once, the first
  move is to simplify the design. The shared re-read surface was removed (S78)
  and the phase ordering made structural (S93); neither was a better test.
- **A per-interleaving cure predicts its own successor.** When a second cure in
  the same family is needed, the question stops being "which window is open" and
  becomes "why is this state shared at all".
- **Stress runs are weak regression guards, never closure proof.** An N-run
  clean gate bounds the observed failure rate near `1/N` with weak confidence; it
  does not show absence. Keep stress runs for regression comparability, and take
  closure from a structural change or an instrument proven to detect.
- **A new shared-state site states its invariant before it lands.** Its author
  supplies the classification (`atomic-by-construction`, `under-lock-L`,
  `published-then-read`, `invariant-unclear`), the invariant in one sentence, the
  reader classes affected, and the intended proof mode. An author who cannot
  state the invariant crisply has found a design question, not a documentation
  gap.

Where an invariant can be made unconstructable it is, and the owning document
says so: isolation by construction (§2.5), the pre-pass barrier (§2.4), the
single cached-module authority and stack-local cluster state (§2.3).

## Cross-references

- `design/int/int.md` — the Binary/int master; §6.2 is the in-call-stack cluster
  model this axis runs on.
- `design/arch/bounded-contexts.md` §6 — the canonical int bounded context
  (cadences, handoffs, constraints).
- `design/arch/sequences/` — the architectural-altitude cadence diagrams.
- `design/arch/effect-concurrency.md`, `design/intrinsics/reactor.md` — the
  language-level concurrency axis, deliberately out of scope here.
