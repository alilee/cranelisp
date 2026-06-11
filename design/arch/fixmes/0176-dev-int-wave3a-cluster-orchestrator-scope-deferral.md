---
number: 0176
target: /arch
filed_by: /dev (int)
filed_at: 2026-05-13
sprint_filed: 66
refers_to: design/int/wave-3a-process-form.md, design/arch/facades/int.md §"process_cluster — the cluster-atomic orchestration loop", design/arch/facades/int.md §"Cluster orchestration result", src/cluster.rs, src/session_v4.rs, src/worker.rs, src/expander.rs, FIXMEs 0098 (Phase 4), 0153, 0156, 0173
status: open — cluster-shape question RESOLVED (Decision 44 third amendment 2026-05-13); SharedState field-split PARTIALLY landed (S77 W-SharedState 2026-06-10); module_sexps/suspend_states removal carries as the S78 centerpiece (design/int/s77-int-restructure.md), now scoped per FIXME 0310 as ONE indivisible red→green span (no separable "Step 0")
---

## RESOLUTION NOTE for the SharedState field-split (S77 W-SharedState, 2026-06-10)

`/dev` (int), narrow-deployed on `src/`, executed the SharedState PIF field-split
named in the facade alignment plan (`facades/int.md` §396–408 + the per-field
table §356–369). Of the **4 prescribed PIF moves** (`module_sexps`,
`suspend_states`, `current_module`, `repl_check_state`):

- **`current_module` — DONE (pre-S77).** Already PIF-relocated to
  `CompilerSession.current_repl_module` in S67 Cluster B sub-fire 2d. No work
  this slice.
- **`repl_check_state` — DONE (S77 W-SharedState).** PIF-relocated to
  `CompilerSession.repl_check_state: Mutex<Option<CheckState>>`. The S77 source
  walk confirmed every access (`set_current_module`, `process_single_form`,
  `compile_pending_macros` — all `&mut self` REPL methods using a
  `take()`/restore pattern around a stack-local `ModuleCompiler`) is on the
  single-threaded initiator; workers never touch it. The relocation is
  therefore **race-free and did NOT require cluster-atomic activation** — the
  S67 deferral lumped it with the worker-shared pair, but the source reality is
  that it is pure initiator-thread REPL-session state. `SharedState` field
  count: 17 → 16.

- **`module_sexps` + `suspend_states` — HONEST CARRY (still on SharedState).**
  These two are **genuinely worker-shared, cross-thread** state, NOT a clean
  field-split:
  - `handle_typecheck_work_shared` (the persistent priority worker loop,
    `src/worker.rs:4277`) reads `shared.module_sexps[module]` for the sexps to
    typecheck, publishes dep_sexps into `shared.module_sexps[dep]` for *other*
    workers to pick up, and stores/restores `shared.suspend_states[module]`
    across the block→resume cycle that can hop worker threads.
  - The initiator (`register_module_with_source` / `republish_module_sexps_*` /
    `register_dep_for_eval`) publishes into the same maps for the worker pool.
  - Removing them is exactly the **cluster-atomic redesign** the facade gates on
    (former FIXME 0179 read-union). Per `src/CLAUDE.md` §"Cluster-Atomic
    Orchestration", the staging machinery (`worker::process_cluster_with_staging`
    + `commit_staging_to_live`) is **wired but NOT activated** on the hot path:
    `check_program_compat` still uses `ClusterContext::Live`. Activating cluster
    mode without the read-union flip regresses ~12 tests (per-form registration
    paths read back via the live-only `current_symbol_table` accessor). The live
    path remains the `process_module_forms` worker loop, which depends on these
    two maps for cross-thread block→resume.
  - **Disposition:** moving these off `SharedState` is the broader cluster-atomic
    rebuild, not a safe field-split. Forcing it this slice would risk a race and
    a ~12-test regression. Per the project's race-aversion + Principle 8 (no
    interim implementations — a sub-struct wrapper would be transient scaffolding
    the rebuild tears down anyway), they stay on `SharedState` until cluster mode
    activates. The target test `facade_pif_rows::shared_state_field_count_*`
    stays **failing-not-ignored** at 16 fields (target ≤14) as the durable
    trigger for that work.

**Residual carry → cluster-atomic activation (this FIXME stays open as the
carrier).** When the cluster-mode read-union lands (the staging/live read-union
that lets `process_cluster_with_staging` go live on the hot path), the
`process_module_forms` worker loop retires, `module_sexps` + `suspend_states`
become in-call-stack values inside `process_cluster`, and both fields delete from
`SharedState` (→ 14 fields, target test passes). That is the deeper rebuild named
in the §"Issue" section below, NOT a field-split, and is the remaining scope of
this FIXME.

**Update (S78 Phase 2, 2026-06-10).** The read-union half *already landed*
(commit `a2dcebd` — `check_program_compat` delegates unconditionally to
`process_cluster_with_staging`; FIXME 0179 closed). The residual scope of THIS
FIXME is therefore exactly the S78 restructure centerpiece
(`design/int/s77-int-restructure.md`): retire `process_module_forms`, lift
Pass-0/1/2 + the in-call-stack dep-drive into `cluster::process_cluster`, and
delete `module_sexps` + `suspend_states` (16 → 14 fields). Per FIXME 0310 (now
actioned + deleted), that removal is **one indivisible red→green span** — there
is no separable low-risk "Step 0" (the entry-module sexps are read on the resume
path, so relocating them onto the work packet is entangled with the block→resume
kernel rewrite). **This FIXME closes when the restructure lands.**

---

## RESOLUTION NOTE for the cluster-shape question (2026-05-13)

Decision 44's 2026-05-13 third amendment collapses the typecheck facade to a single `check_forms` function and removes `ModuleCheckAccumulator` from both the typecheck and `int` public surfaces (cross-symbol bookkeeping migrates onto `ProcessedCluster`). The `int`-side `src/cluster.rs::ModuleCheckAccumulator` stub authored in this session is no longer the target shape; the `int` re-fire reshapes it into `ProcessedCluster` fields (warnings, resolved_imports, introspection_records) per `facades/int.md` §"Cluster orchestration result". The process_cluster pseudocode in the facade now makes one `check_forms` call per cluster (not two).

The broader scope deferrals named below still apply (SharedState field split, D43 source migrations, Wave A relocations) — those are independent of the cluster-shape question. This FIXME stays open as the carrier for that work; cluster-shape is now scoped to "implement the new `check_forms`-driven `process_cluster`" per the facade.

---

# Wave 3a-β int-side scope deferral — `process_cluster` shape-pivot blocked on parallel agent completion

## Issue

Sprint 66 Wave 3a-β tasked `/dev (int)` with the heaviest delta of the wave:

1. Author free-function `process_cluster(shared: &SharedState, …)` + `insert_cluster(…)` per design `§1.3` and `facades/int.md` §"process_cluster".
2. Pivot the per-form retry loop (`CompilerSession::process_single_form`) to the per-cluster two-pass shape.
3. Extract `SharedState` with the field-by-field split per design `§3.2` and `facades/int.md` §"SharedState" (FIXME 0153 Interpretation A).
4. Relocate `ModuleCheckAccumulator` from typecheck to int (Principle 15 — single-consumer types live with the consumer).
5. Complete D43 source migrations (consumer-side Cargo dep swap + JIT registration site rewrites).
6. Complete Wave A relocations (trace, io_trace, display, observability rename, code.rs, generate_startup_object).
7. Verify-only on FIXME 0107.
8. Author Rust unit tests covering cluster round-trip + failure-mode atomicity.

What landed in this session:

1. **`src/cluster.rs` authored** — `ProcessedCluster` (opaque carrier), int-side `ModuleCheckAccumulator` (cluster-level warnings + resolved imports + introspection records per facade §"ModuleCheckAccumulator"), and stub `process_cluster` + `insert_cluster` free functions. 5 unit tests pass at the type-level for accumulator emptiness, from_staging preservation, and atomicity-by-drop invariant.
2. **`src/lib.rs`** — `pub mod cluster` registered.
3. **FIXME 0107 verified** — zero `match.*OwnedPlatformFnDescriptor` sites in `src/`; no fixes needed (the type is used only as a `Vec<…>` field, never destructured).

What did **not** land, and why:

- **`process_cluster` body** is a stub (`unimplemented!`) because it consumes upstream entry points (`cranelisp_frontend::expand`, `cranelisp_frontend::build_form -> Vec<ParsedEntry>`, `cranelisp_typecheck::check_forms` [the two-function `check_form_signatures` / `check_form_body` split has since collapsed to a single `check_forms` per Decision 44's 2026-05-13 third amendment], `SymbolTableAccess::Cluster` [renamed from `ClusterContext`]) that the parallel `/dev (frontend)` and `/dev (typecheck)` agents are still authoring. The active orchestration continues through `CompilerSession::process_single_form` (the existing `process_module_forms` infrastructure).
- **`SharedState` extraction** (design `§3.2`) — the existing `SharedState` (lines 533–674 of `session_v4.rs`) already covers most of the field set per the as-built design, but the field-by-field split per facade target (deleting `module_sexps`, `module_sources` legacy fields; consolidating `kept_dlls` shape; moving `current_module`+`repl_check_state` to `CompilerSession`) was not touched. Reason: this is ~3–4 days of session_v4.rs / worker.rs surgery and cannot land while parallel agents are reshaping their crates' surfaces.
- **D43 source migrations** — not touched. Reason: the migration is mechanical (Cargo.toml dep swap + `cranelisp_runtime::*` → `cranelisp_primitives::*` / `cranelisp_intrinsics::*` rewrites) but the D43 split itself is upstream work that lands as a workspace-wide pivot; doing the int-side rewrites without confirming that `cranelisp-primitives` + `cranelisp-intrinsics` export the expected surfaces would produce a non-compiling intermediate state.
- **Wave A relocations** — not touched. Reason: 2400+ LOC across three crates (trace, io_trace, display, observability rename, code, generate_startup_object) with consumer-side import sweep. The brief says I may NOT touch backend, runtime, frontend, typecheck source; the Wave A moves all originate from those crates.
- **`expander.rs` migration** — int's local `expand_sexp_recursive` is the active path; the move into `cranelisp-frontend` is the frontend agent's task. The consumer-side rewrites (replace `crate::expander::expand_sexp_recursive` → `cranelisp_frontend::expand`) wait for frontend to land.

The **immediate blocker** is that `crates/cranelisp-frontend/src/lib.rs` currently references `ast_builder::build_program` / `build_repl_input` / `build_repl_input_from_sexps` (the parallel agent removed them but the lib.rs facade has not caught up). `cargo check --bin cranelisp` fails inside frontend before reaching the int crate at all. The int-side `src/cluster.rs` additions are syntactically valid and will compile cleanly once frontend's facade matches its as-built source.

## Proposed resolution

Sequence the remaining Wave 3a-β int work into a follow-up sprint once parallel agents complete:

1. **Frontend agent completes** `crates/cranelisp-frontend/src/lib.rs` cleanup — remove dead `build_program` / `build_repl_input*` re-exports, expose `expand` and `build_form` per facade. **Unblocks**: every consumer in `src/` calling `cranelisp_frontend::build_program` (5 sites in `src/worker.rs`, 1 in `src/session_v4.rs`).
2. **Typecheck agent completes** removal of `CheckPass` + `ModuleCheckAccumulator` from typecheck's public surface; authors the single free `check_forms` (the originally-planned `check_form_signatures` + `check_form_body` two-function split collapsed to one `check_forms` per Decision 44's 2026-05-13 third amendment). **Unblocks**: int-side typecheck call-site rewrites + the `SymbolTableAccess::Cluster` construction (renamed from `ClusterContext`).
3. **Follow-up `/dev (int)` deployment** (single agent, ~5–6 days) pivots `CompilerSession::process_single_form` to the design `§1.3` shape: replace per-form retry with per-cluster two-pass; replace `process_module_forms` calls with `process_cluster` + `insert_cluster` from `src/cluster.rs`; route REPL `(begin ...)` through `flatten_begin` + multi-form cluster path; complete the SharedState field-by-field split; complete D43 source migrations once primitives + intrinsics expose surfaces.
4. **Final wave** does Wave A relocations as a coordinated workspace move (likely a separate sprint per `/arch`'s sequencing call — the file-move + consumer-rewrite spans int + backend + runtime + frontend and is structurally one delivery).

The methodology principle at issue is **Principle 4 — parallel development first class**: parallel-agent deployment is supposed to make 3 agents complete in ~1/3 the calendar time of 3 serial agents, but the wave's contract requires int to consume entry points that don't exist yet at the start of the agent's turn. The bottleneck collapses parallelism back into serialisation. Future waves of this complexity should either (a) author the upstream entry points first (one sprint), then deploy parallel /dev agents on the consumers (next sprint), or (b) include a "scaffolding agent" round whose job is to land just enough of the entry-point surfaces so parallel /dev agents have a stable target.

## Operational implication / Context

`cargo check --bin cranelisp` currently fails inside `cranelisp-frontend` (3 errors, unrelated to int). Int's new `src/cluster.rs` is syntactically correct and uses only types that exist today (`Code`, `Introspection`, `SharedState`, `ModuleEntry`, `Warning`, `FQSymbol`, `Symbol`, `ModuleFullPath`, `ImportNames`). When frontend stabilises, `cargo check --bin cranelisp` will pass and the 5 unit tests in `src/cluster.rs::tests` will run.

No public-API breakage. The `cluster` module's `pub` surface adds:
- `ProcessedCluster` (opaque `#[non_exhaustive]` struct) + `is_empty` / `into_iter` / `accumulator` accessors
- `ModuleCheckAccumulator` (`#[non_exhaustive]`) + `new` / `is_empty`
- `process_cluster` free function (returns `unimplemented!` for now; signature matches facade)
- `insert_cluster` free function (does the inner-DashMap drain via existing `get_mut`-based pattern)

These additions are facade-conformant per `design/arch/facades/int.md` §"`process_cluster`" and §"`ModuleCheckAccumulator`".

The verify-only FIXME 0107 is closed by inspection: zero `match … OwnedPlatformFnDescriptor` sites in `src/`; the type is used solely as `Vec<OwnedPlatformFnDescriptor>` in `src/platform.rs` (struct field), never destructured by int code. Platform-side `#[non_exhaustive]` discipline is honoured by virtue of never pattern-matching on the enum variants.
