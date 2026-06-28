# Sprint 94 — Slice-2 completion (real effect-node await) + 0424 / 0430 drain — Failing-test PLAN (Phase 3 deliverable)

**Owner:** `/qa`. **Status:** PLAN ONLY — no test code yet. The failing tests land in
**Phase 5 Stage 1** (QA-first, sprint-wide, before any per-crate D/D/R cycle). This
document enumerates the test surface so `/sprint` + the user can review coverage before
implementation waves are allocated.

**Scope source:** `sprints/SPRINT.md` (S94 Scope 1 — real effect-node await; Scope 2 —
FIXME drain 0424 + 0430; the Phase-2 R1–R6 revisions). **Contract of record:**
`design/arch/effect-concurrency.md` §13 "S94 R1" + Appendix B §"the ratified
backend↔intrinsics poll-shape Effect-node seam (S94, R1 — the /dev contract)" — the
"What /qa can assert" list (a)–(d) is the Phase-5 Stage-1 acceptance contract.
**Design of record (interior):** `design/int/reactor.md` §2/§3/§4 (reactor, strand sink,
the S93 as-built boundary /design int refreshes this sprint). **ABI guard target:**
`crates/cranelisp-platform/src/concurrency.rs` (`ConcurrentPlatformFn.drop_state`,
landed S94 R1, no `ABI_VERSION` bump) + `crates/cranelisp-platform/src/tests.rs:1033`
(`concurrent_platform_fn_repr_c_field_order_v7`, to extend). **0424:**
`effect-concurrency.md` Appendix B step 3 + arch R5. **0430:**
`design/arch/fixmes/0430-design-docstring-into-source-regen.md` (candidate 1 ratified
by /design this sprint) + `src/save.rs::{generate_fns_and_macros,render_decl_sexp}`.

## Baseline (Phase-3 sanity, `/qa` 2026-06-27)

Carried from the S93-close report (`sprints/SPRINT.md` Notes; not re-run this Phase —
PLAN only): default `cargo nt` **1677 passed**; `cargo nt-concurrency` **330**;
`cargo nt-concurrency-runtime` **171**. Source-of-truth checks done this Phase:
`IO_TAG_EFFECT_POLL` exists **nowhere** on HEAD (only `IO_TAG_EFFECT` —
`crates/cranelisp-intrinsics/src/io.rs:10`), so every (a)/(b)/(c) row that names it is
RED-first by construction; `src/Cargo.toml` carries **no** `concurrency-runtime`
passthrough yet (S94 Scope step 4 adds it — see Gap G1). **Any RED after this point is
in-scope work.**

## Conventions / legend

- **Lane** (where the row runs — the four canonical invocations):
  - `nt` — `cargo nextest run` (feature-OFF, the release gate; e2e binary + all
    default-feature unit tests).
  - `nt-concurrency` — `-p cranelisp-types -p cranelisp-platform -p cranelisp-intrinsics
    --features cranelisp-intrinsics/concurrency` (ABI-v7 layout-contract unit guards).
  - `nt-concurrency-runtime` — `-p cranelisp-intrinsics
    --features cranelisp-intrinsics/concurrency-runtime` (the reactor implementation —
    mio reactor + `EffectPoll` + strand sink + demo leaves; unit-tier in intrinsics).
  - `agent` — `cargo nextest run --features agent --test agent` (the `#[cfg(feature =
    "agent")]` Document-write surface).
  - **`reactor-e2e` (PROPOSED — Gap G1)** — `cargo nextest run --features
    concurrency-runtime --test concurrency_reactor` (the binary built with the
    `concurrency-runtime` passthrough so a compiled-from-source program drives
    `cranelisp_run_io` through the real reactor). **Not yet a `.cargo/config.toml`
    alias — see Gap G1.**
- **Tier**: `unit` (`/dev`-authored, `#[cfg(test)]` in the owning crate, named here for
  surface completeness — landed in the same change-set as the fix per the
  mandatory-unit-test-per-fix discipline) or `e2e` (`/qa`-authored, `tests/*.rs`,
  subprocess via the `Cranelisp` builder). **No middle tier** (`tests/CLAUDE.md`).
- **Posture**: `RED-first` = a failing guard the fix flips green; `regression-replay` =
  an existing S93 guard that must stay green; `present` = already on HEAD.
- **P/N**: positive (correct behaviour appears) / negative (wrong behaviour absent).

> **Why so much of the headline is unit-tier (a key reconciliation, `/qa` 2026-06-27).**
> The reactor lives in `cranelisp-intrinsics` and is only ever compiled with
> `concurrency-runtime` ON. The default/`--link` binary **never** enables that feature
> (the deployment invariant, `reactor.md` §1). So the suspend/resume *mechanism* is
> reachable from outside the intrinsics crate ONLY through a binary built with the
> `concurrency-runtime` passthrough — which needs both the src/ passthrough (Scope
> step 4) **and** a dedicated e2e lane (Gap G1). The genuine R2 "real leaf through the
> full macro→backend→loader path" assertion is the **`reactor-e2e` row** (b/c);
> everything else is unit-tier substrate proof.

---

## §1 — Scope 1: real effect-node await (the headline). Seam ⇒ `effect-concurrency.md` App-B §"ratified … seam" (a)–(d)

### 1A — (a) feature-off byte-identical: no `IO_TAG_EFFECT_POLL` ever constructed

The byte-identical-when-off obligation (R3). The backend's second arm is keyed on the
effect's declared *shape* (`blocking == 0`), needs **no cargo feature**, and is reached
only by concurrency-gated poll effects — so a default build must construct **only**
`IO_TAG_EFFECT` for the blocking effects that are every real platform today.

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `effect_site_blocking_builds_io_tag_effect_not_poll_neg` | unit (`cranelisp-backend`) | `nt` | a blocking (`blocking == 1`) effect's effect-site codegen builds an `IO_TAG_EFFECT` node and **never** an `IO_TAG_EFFECT_POLL` node — the v6 arm is structurally unchanged | N | RED-first (tag is new) |
| `poll_shape_effect_builds_io_tag_effect_poll_with_closure_env` | unit (`cranelisp-backend`) | `nt` | a poll-shape (`blocking == 0`) effect builds an `IO_TAG_EFFECT_POLL` node whose field-0 is a host-built state-closure `[header \| code_ptr = GOT-loaded poll-fn \| drop_glue_ptr \| env = result-slot + i64 args + scratch]` (App-B seam decision 1/2) | P | RED-first |
| `real_io_program_default_build_output_unchanged` | e2e | `nt` | a small real-IO `--run` program (e.g. `(print …)`) produces byte-identical stdout/exit through the default (feature-off) binary — the v6 blocking path is observationally unchanged | P | regression-replay (existing `spec_10_io` coverage; named for the byte-identical edge) |

> **`real_io_program_default_build_output_unchanged` is a thin /qa addition** over the
> standing `spec_10_io.rs` IO coverage — its job is to pin the App-B(a) claim "the v6
> blocking path is byte-identical" at the e2e edge, not to add new IO surface.

### 1B — (b) feature-on real-node await: suspend/resume + Par overlap through `cranelisp_run_io`

The headline acceptance (R2/R6). PRIMARY = the `reactor-e2e` row (a real
`declare_platform!`-emitted **in-tree** poll leaf compiled from source, no cdylib —
R6). The unit rows are the intrinsics-side substrate proof + the S93 fixture-leaf
replay.

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `real_leaf_suspends_and_resumes_through_run_io` | e2e | **`reactor-e2e`** (Gap G1) | a compiled-from-source program using ONE real in-tree async leaf, run via the `concurrency-runtime` binary, drives `cranelisp_run_io` and the strand stream shows `EffectDispatched → EffectSuspended → EffectResumed` for the leaf (App-B(b) single-leaf) | P | RED-first |
| `two_real_leaves_in_par_overlap_max_not_sum_one_thread` | e2e | **`reactor-e2e`** (Gap G1) | TWO real in-tree async leaves in a `(par …)` / auto-IO-parallel form overlap on ONE reactor thread — wall-clock ≈ **max**(delay) not sum, no thread-per-read — the App-B(b) two-leaf acceptance; strand stream interleaves two distinct `StrandId`s | P+N | RED-first |
| `run_io_async_effect_arm_awaits_effectpoll_for_poll_node` | unit (`cranelisp-intrinsics`) | `nt-concurrency-runtime` | `run_io_trampoline_inner_async` (`io.rs:128`) `.await`s an `EffectPoll` for an `IO_TAG_EFFECT_POLL` node and forces synchronously (no await) for `IO_TAG_EFFECT` — the real async Effect arm exists (closes the §4 as-built delegate-to-sync boundary) | P | RED-first |
| `two_async_reads_overlap_max_not_sum_one_thread` | unit (`cranelisp-intrinsics`) | `nt-concurrency-runtime` | **S93 fixture-leaf overlap demo** (`reactor/tests.rs:224`) stays green — the substrate regression guard (R2: fixture leaf retained) | P | regression-replay |
| `single_leaf_suspend_resume_through_reactor` | unit (`cranelisp-intrinsics`) | `nt-concurrency-runtime` | S93 single-leaf suspend/resume (`reactor/tests.rs:102`) stays green | P | regression-replay |

### 1C — (c) result extraction: generic env-offset read

App-B seam decision 3 — the S93 fixture's `ResultReader` fn-pointer collapses to a
host-known offset read. Two halves: backend bakes the result-slot location; intrinsics'
generalized `EffectPoll` reads it on `Poll::Ready`.

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `effect_poll_node_reserves_result_slot_at_host_known_offset` | unit (`cranelisp-backend`) | `nt` | the `IO_TAG_EFFECT_POLL` state-closure env reserves the result slot at the host-known location (baked node field or fixed env offset — /design backend+int's interior choice) the trampoline reads | P | RED-first |
| `effect_poll_reads_i64_result_via_generic_offset_read` | unit (`cranelisp-intrinsics`) | `nt-concurrency-runtime` | the generalized `EffectPoll` reads the leaf's i64 result generically from the env result slot on `Poll::Ready` (no per-effect `ResultReader`) | P | RED-first |
| `real_leaf_i64_result_reads_back_correctly` | e2e | **`reactor-e2e`** (Gap G1) | the App-B(c) end-to-end: a real leaf's i64 result (scalar or heap base pointer) is observable in the program's value after `cranelisp_run_io` returns | P | RED-first |

### 1D — (d) `--link` links no executor

App-B(d) structural guard. The `--link` / exe-bundle path must never request
`concurrency-runtime`, so a linked binary is executor-free (`mio`/`futures` never
compiled in — the `dep:`-gated guarantee, `reactor.md` §1).

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `link_io_program_runs_without_executor` | e2e | `nt` | a small IO program `--link`ed then RUN succeeds (exit 0, correct stdout) — the linked binary works with no reactor/executor present (the executor-free-link guarantee, observed by it running correctly) | P | regression-replay (existing `link.rs` coverage; named for the no-executor edge) |
| `link_path_does_not_enable_concurrency_runtime_neg` | unit (`src/`) | `nt` | the exe-bundle / `--link` build path never enables `concurrency-runtime` (structural assertion on the feature wiring — the deployment invariant Scope step 4 must preserve) | N | RED-first if Scope-step-4 passthrough is mis-wired; else `present`-extension |

> **`link_path_does_not_enable_concurrency_runtime_neg` is a /dev (src/) unit** because
> it inspects the binary's own feature wiring — not reachable from a subprocess. /qa
> names it; /dev lands it with the Scope-step-4 passthrough.

### 1E — (e) ABI guard: extend the v7 field-order pin to `drop_state`

The reserved-now `ConcurrentPlatformFn.drop_state` field (App-B seam decision 4; landed
S94 R1, no `ABI_VERSION` bump) must be pinned in the existing frozen-field-order guard
so a future reorder/removal is caught.

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `concurrent_platform_fn_repr_c_field_order_v7` (EXTEND) | unit (`cranelisp-platform`) | `nt-concurrency` | extend the existing guard (`tests.rs:1033`) to include `offset_of!(ConcurrentPlatformFn, drop_state)` in the strictly-increasing offset vector, positioned **between `poll` and `param_count`** per the landed layout (`concurrency.rs:148`); the monotonic-offset + last-field-is-`concurrency` invariants still hold | P | RED-first (drop_state not yet in the offset vector) |

> The guard already lives at `crates/cranelisp-platform/src/tests.rs:1033` and passes on
> HEAD for the 12 pre-drop_state fields. EXTENDING it to the 13th field is the only ABI
> change S94 makes; it is a one-line addition to the `offs` array + the
> between-`poll`-and-`param_count` ordering assertion. /dev-authored (unit in the crate).

---

## §2 — Scope 2a: FIXME 0424 — dependent-binding spark substrate (par-map / par-reduce floor)

Per arch R5: apply-arg sparking already ships; the new substrate is the **dependent
binding spark on the `let` path** (spark a dependent binding as an IVar, force on demand
via existing `ivar_force` — backend-only, no new runtime, no public-API impact). The
stdlib `par-map`/`par-reduce`/`par-map-reduce` are ordinary `.cl` defs (`/stdlib`, a
separate wave) — **NOT testable in `tests/`** (free-standing rule: zero stdlib
dependency). So /qa's e2e exercises the **substrate** via inline par-map/par-reduce-shaped
programs defined with primitives + special forms only. The floor: never wrong, never
slower-than-sequential.

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `let_path_dependent_binding_sparks_as_ivar_forced_on_demand` | unit (`cranelisp-backend`) | `nt` | a dependent `let` binding lowers to an IVar spark + `ivar_force` on demand (the limit-#2 generalization) — the seam the floor stands on | P | RED-first |
| `par_map_shaped_inline_results_identical_to_sequential` | e2e | `nt` | an inline par-map-shaped program (Cons-recursion applying a fn to each element, defined with primitives + special forms, **no stdlib import**) produces results **identical** to a sequential `map` over the same input — the correctness floor (never wrong) | P | RED-first / verify-on-HEAD (apply-arg path may already pass; the let-dependent shape is the new bit) |
| `par_reduce_shaped_inline_results_identical_to_sequential` | e2e | `nt` | an inline par-reduce-shaped program (dependent accumulator over the `let` path) produces the same result as a sequential fold — pins the dependent-binding spark's correctness | P | RED-first |
| `par_map_shaped_inline_not_slower_than_sequential` | e2e | `nt` | the inline par-map workload (each element a measurable CPU-bound computation) completes in wall-clock **≤** the sequential version (the floor: never slower than sequential; assert with a generous margin to avoid flake) | P | RED-first |

> **Timing assertions are flake-prone — keep the margin generous.** The floor is "not
> slower than sequential," not "N× faster." Assert `parallel ≤ sequential × 1.1` (or
> similar) rather than a hard speedup ratio; the correctness rows are the load-bearing
> guards, the timing row is the floor sentinel. Per `tests/CLAUDE.md` flag-slow-tests:
> size the per-element work so the e2e stays well under the 100ms-per-test budget while
> the serial sum is still distinguishable from the overlapped wall-clock.

---

## §3 — Scope 2b: FIXME 0430 — docstring-into-source regen (the S89-descoped `set-doc`)

Candidate 1 (docstring-aware `render_decl_sexp`) ratified by `/design` this sprint +
the reconciliation rule (live `Def.docstring` authoritative when `Some`; emit the
sexp's own docstring only when the live field is `None`; never double-emit). /dev (src/)
re-lands the S89-W3-removed `set-doc` Document-write surface against that contract. This
is a **defect-grade persistence repro** (the §17.15.3 durable promise the half-feature
failed to deliver) — it owes a failing-not-ignored e2e + a renderer unit.

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `render_decl_sexp_emits_live_docstring_and_reconciles` | unit (`src/save.rs`) | `agent` (or `nt` if the renderer is not feature-gated) | `render_decl_sexp` (given the entry's `Option<&str>` docstring) inserts the live docstring after the param vector; when the stored sexp ALSO carries a docstring AND the live field is `Some`, the **live** one wins and the sexp's is dropped (no duplicate); when live is `None`, the sexp's own docstring round-trips | P+N | RED-first (renderer contract changes; `set-doc` surface descoped on HEAD) |
| `set_doc_docstring_survives_session_restart` | e2e | `agent` | `set-doc <symbol> <text>` then session-restart (`save::generate_fns_and_macros` round-trip to disk + reload) → `/doc <symbol>` shows the docstring (the §17.15.3 durable-memory promise; the repro that was descoped S89) | P | RED-first |
| `set_doc_does_not_duplicate_docstring_on_restart_neg` | e2e | `agent` | a symbol whose original `(defn …)` source already carried a docstring, after `set-doc` overwrites it then restarts, shows the **new** docstring exactly once — no double docstring in the regenerated `.cl` (the reconciliation rule, negative face) | N | RED-first |

> **Lane note for 0430.** `set-doc` is `#[cfg(feature = "agent")]` (descoped from
> `src/agent/{pull,stub}.rs` in S89 W3 — see the FIXME). The e2e rows therefore run in
> the `agent` lane (`cargo nextest run --features agent --test agent`), beside the
> existing agent Document-mode coverage. The `render_decl_sexp` unit's lane depends on
> whether the renderer change is itself feature-gated — `/design`'s candidate-1
> ratification should state this; if the renderer is agent-only, the unit is `agent`,
> else `nt`. Flagged for /design to confirm (Gap G2).

---

## §4 — Real in-tree leaf fixture (R6) — confirmation

The §1B/§1C `reactor-e2e` rows need a **real `declare_platform!`-emitted async-capable
leaf** (R2). **R6 confirmed from the contract: NO separate cdylib is required** — an
in-tree async-capable `DefKind::PlatformEffect` (the `declare_platform!` poll-emission
arm applied to an in-tree platform, e.g. an `async-read`-shaped real effect) satisfies
R2 and keeps the wave self-contained (`SPRINT.md` R6; App-B demo-leaf paragraph). The
S93 hand-written fixture poll-fns (`async_read_pollfn` / `timer_write_pollfn`,
`reactor.rs:613`/`687`) stay as the intrinsics-side substrate guards (§1B
regression-replay rows) but do **not** satisfy R2 on their own (they bypass the
macro→backend→loader path). The real leaf is a `/platform` + `/dev` deliverable (the
`declare_platform!` poll-emission, Scope step 1); /qa's e2e *consumes* it from compiled
source. The fixture is a platform effect (not stdlib), so the free-standing-test rule is
satisfied: the e2e program uses the in-tree leaf via the platform-effect surface, with
no `stdlib/` dependency.

---

## §5 — Flagged gaps blocking / shaping Stage-1 authoring

- **G1 — the `reactor-e2e` lane does not exist; the binary has no `concurrency-runtime`
  passthrough (`target: /int` + `/arch`).** The genuine R2 end-to-end rows (§1B
  `real_leaf_suspends_and_resumes_through_run_io`,
  `two_real_leaves_in_par_overlap_max_not_sum_one_thread`; §1C
  `real_leaf_i64_result_reads_back_correctly`) need (i) `src/Cargo.toml` to forward a
  `concurrency-runtime` passthrough feature (Scope step 4 — **in scope this sprint**,
  not yet on HEAD), AND (ii) a `.cargo/config.toml` alias
  (`nt-reactor-e2e = "nextest run --features concurrency-runtime --test
  concurrency_reactor"`, mirroring the FIXME-0449 lanes). `.cargo/config.toml` is
  `/arch`-owned; `/qa` cannot add it (this task edits only `tests/plan/`). **Resolution
  path:** /int lands the passthrough (Scope step 4); /arch adds the lane alias (one
  line, additive — same shape as `nt-concurrency-runtime`). **If the lane is not added,
  the §1B/§1C `reactor-e2e` rows have no home** and the R2 "real leaf through the full
  path" acceptance degrades to backend-unit + intrinsics-unit only (which R2 explicitly
  warns is "unexercised scaffolding"). **Does not block** the §1A/§1D/§1E/§2/§3 rows.
  Flag to /sprint at the wave gate.
- **G2 — 0430 renderer-unit lane (`target: /design`).** Whether
  `render_decl_sexp`'s docstring-aware change is itself `#[cfg(feature = "agent")]` (so
  the unit runs in the `agent` lane) or feature-free (so it runs in `nt`) depends on
  /design's candidate-1 ratification shape. Minor — affects only the lane label on
  `render_decl_sexp_emits_live_docstring_and_reconciles`. /qa authors to whichever
  /design ratifies.

These are surfaced here (not filed as FIXMEs) per the task constraint (edit only
`tests/plan/`); `/sprint` routes G1/G2 to /int + /arch + /design at the Phase-4 wave
gate.

---

## §6 — Phase-3 exit gate confirmation

`/qa` confirms it has enough from the ratified seam (`effect-concurrency.md` App-B
§"ratified … seam" (a)–(d) + §13 S94 R1) to draft the Phase-5 Stage-1 failing tests:

- **(a) feature-off byte-identical (§1A)** — 2 backend units (RED-first: no poll node
  for blocking; poll node for poll-shape) + 1 e2e byte-identical replay. Anchor:
  App-B(a) + seam decisions 1/2.
- **(b) real-node await (§1B)** — 2 `reactor-e2e` rows (single-leaf + two-leaf overlap,
  RED-first, **Gap G1**) + 1 intrinsics unit (real async Effect arm) + 2 S93
  regression-replays. Anchor: App-B(b) + `reactor.md` §4 (boundary closed).
- **(c) result extraction (§1C)** — 1 backend unit (result-slot offset) + 1 intrinsics
  unit (generic read) + 1 `reactor-e2e` row. Anchor: App-B(c) + seam decision 3.
- **(d) --link no executor (§1D)** — 1 e2e link-and-run replay + 1 src/ unit
  (feature-wiring negative). Anchor: App-B(d) + `reactor.md` §1.
- **(e) ABI guard (§1E)** — extend `concurrent_platform_fn_repr_c_field_order_v7` to pin
  `drop_state` (1 line; `nt-concurrency` lane). Anchor: seam decision 4 +
  `concurrency.rs:148`.
- **(f) 0424 dependent-binding spark (§2)** — 1 backend unit (let-path IVar spark) + 3
  e2e (par-map identical, par-reduce identical, par-map not-slower; inline/free-standing,
  `nt` lane). Anchor: App-B step 3 + arch R5.
- **(g) 0430 docstring regen (§3)** — 1 save.rs unit (renderer insert/replace/reconcile)
  + 2 e2e (restart-persistence + no-duplicate; `agent` lane). Anchor: FIXME 0430
  candidate 1 + reconciliation rule.

**Fixture (§4):** R6 confirmed — no separate cdylib; in-tree `DefKind::PlatformEffect`
real leaf (a `/platform` + `/dev` deliverable the e2e consumes).

**Counts:** 19 planned rows — **9 e2e (`/qa`-authored:** 5 `reactor-e2e`/`nt` for Scope 1,
3 `nt` for 0424, … and 2 `agent` for 0430 — net 4 `reactor-e2e`, 3 default-`nt` Scope-1
replays/floor, 3 `nt` 0424, 2 `agent` 0430**); 10 unit (`/dev`-authored, named for surface
completeness + the mandatory-unit-per-fix discipline). 6 of the 19 are
verify-on-HEAD/regression-replays; 13 are RED-first.

### Open verdict for /sprint + user

The Stage-1 surface is **draftable now** for (a)/(c-partial)/(d)/(e)/(f)/(g). The
**(b) + (c-e2e) headline rows are draftable but un-runnable until Gap G1 lands** (src/
passthrough + the `reactor-e2e` lane alias). Recommend /sprint sequence Scope-step-4
(src/ passthrough) + the `.cargo/config.toml` lane alias **early** in the reactor wave so
the headline acceptance rows have a home before /dev claims the slice green.
