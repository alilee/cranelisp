# Sprint 93 — Reactor Gate: race stabilisation + ABI-v7 dormant contracts — Failing-test PLAN (Phase 3 deliverable)

**Owner:** `/qa`. **Status:** PLAN ONLY — no test code yet. The failing tests land in
**Phase 5 Stage 1** (QA-first, sprint-wide, before any per-crate D/D/R cycle). This
document enumerates the test surface so `/sprint` + the user can review coverage before
implementation waves are allocated.

**Scope source:** `sprints/SPRINT.md` (S93: race gate + ABI-v7 dormant contracts + FIXME
drain). **Design of record:** `design/int/signature-body-prepass.md` (the gate fix +
§6 "/qa isolation hook"); `design/int/heisenbug-race-closure.md` §7–§8 (the tactical
lineage + H6/H7 evidence); `design/arch/effect-concurrency.md` §5/§6/§11/§12 (the ABI-v7
layout contracts). **Ledger anchor:** `tests/plan/ledger.md`:2118 (the H6/H7 residue row).

## Baseline (Phase-3 sanity, `/qa` 2026-06-27)

`cargo nextest run` → **1648 passed / 0 failed / 0 skipped** (41s wall — the heavy
trace + `repl_persist_race` subprocess tests dominate; per-test budget is fine). The
S81 "14 intentional failing" guards have all since flipped green — the current
canonical suite is **clean (0 failures)**. `cargo build -p cranelisp-platform
--features concurrency` compiles clean. **Any RED after this point is in-scope work.**

## Conventions / legend

- **Tier**: `unit` (`/dev`-authored, `#[cfg(test)]` in the owning crate, named here for
  surface completeness — `/dev` lands them in the same change-set as the fix per the
  mandatory-unit-test-per-fix discipline) or `e2e` (`/qa`-authored, `tests/*.rs`,
  subprocess via the `Cranelisp` builder). **No middle tier** (`tests/CLAUDE.md`).
- **Posture**: `RED-first` = a failing guard the fix flips green; `load-guard` = an
  existing intermittently-green stress test the gate must make deterministically green;
  `present` = the guard already exists on HEAD.
- **P/N**: positive (correct behaviour appears) / negative (wrong behaviour absent).
- The race-gate deterministic/loom tests are necessarily **unit-tier**: the injection
  seam (`signatures_ready_for_test` + the `P_publish`/`P_read` pause-gates) is reachable
  only inside `src/scheduler.rs`, not from the binary's outside surface. `/qa`'s gate
  contribution is the **e2e contention guard** (existing) + the **e2e cycle-error** row.

---

## §1 — Race gate (THE priority): the H6/H7 import/typecheck race

The gate's shape is **isolate-then-fix** (`SPRINT.md` 1a/1b): turn the "unisolated
recurring failure" (`'helper-val' not found in module 'helper'`, ~5–10% under 6-thread
contention) into a **pinned deterministic** failing test, then the structural
signature/body pre-pass (`signature-body-prepass.md` §2 Invariants PP + SW) flips it
green and keeps it green under contention.

### 1A — Deterministic structured-interleaving pin (unit, `src/scheduler.rs::tests`, `/dev`)

The **gate's regression pin**. Seam: the scheduler readiness API, instrumented with the
S61 `#[cfg(test)]` accessor pattern extended with `signatures_ready_for_test` + two
injectable pause-gates (`signature-body-prepass.md` §6 tier 1):

- **P_publish** — between "set `helper` pool → `TypecheckDone`" and "all of `helper`'s
  symbols visible in `symbol_tables[helper]`" (the §3.6 publication window).
- **P_read** — in the dependent's resume path, after `is_typechecked(helper)` returns
  true, before the body reads `symbol_tables[helper]` for `helper-val`.

| Test name | Tier | Asserts | Seam | P/N | Posture |
|---|---|---|---|---|---|
| `scheduler_race_read_inside_publish_window_finds_sibling_symbol` | unit | 2-module graph `helper ← user`, two simulated orchestrators (eval `t1`, worker `t2`); force `t1` to take **P_read inside the window P_publish has opened** → assert the body read finds `helper-val`. **Pre-fix:** an interleaving exists where it does NOT (RED). **Post-fix:** P_read is in Phase B, unreachable until `await_signature_barrier`, so the interleaving cannot occur — GREEN in every schedule. | `src/scheduler.rs` readiness API + `signatures_ready_for_test` + P_publish/P_read | N | RED-first |

### 1B — Loom / exhaustive-interleaving variant (unit, `src/scheduler.rs::tests`, `/dev`)

The strongest form (`signature-body-prepass.md` §6 tier 2) — the deterministic
replacement for the 6-thread stress repro's nondeterminism. **Adopt if the seam supports
loom** (model `symbol_tables[helper]` as a loom cell, the pool transition as a loom
atomic, two loom threads). If loom adoption is deferred, 1A alone is the pin and the loom
row carries an `#[ignore = "loom adoption — S94"]` row in this plan (NOT in the suite).

| Test name | Tier | Asserts | Seam | P/N | Posture |
|---|---|---|---|---|---|
| `scheduler_race_loom_observe_ready_implies_symbol_published` | unit | In **all** loom interleavings: "observe `is_typechecked(helper)`" ⟹ "subsequent read of `symbol_tables[helper]` contains `helper-val`." Loom exhaustively finds the pre-fix counter-interleaving and proves its absence post-fix. | loom model over the scheduler readiness atomics | N | RED-first (or `#[ignore]` if loom deferred) |

### 1C — Per-step structural unit seams (unit, `src/scheduler.rs::tests`, `/dev`)

The pre-pass `/dev` plan (`signature-body-prepass.md` §7) lands each step with its own
unit test first. Named here so the gate's surface is complete; all `/dev`-authored,
RED-first, single-threaded/deterministic:

| Test name | Tier | Asserts | Seam | P/N | Posture |
|---|---|---|---|---|---|
| `dependency_closure_acyclic_orders_leaves_first` | unit | acyclic 3-module graph → leaves-first `ClosureOrder` | `dependency_closure` (§7 step 1) | P | RED-first |
| `dependency_closure_two_cycle_returns_cycle_error` | unit | 2-cycle → `CycleError` (reuses `detect_cycle_locked`) — the D0030 coarse-reading basis | `dependency_closure` | N | RED-first |
| `signature_barrier_blocks_until_last_module_registers` | unit | N modules under scoped threads; barrier blocks until the last `register_module_signatures`, then opens | `await_signature_barrier` (§7 step 2) | P | RED-first |
| `single_writer_exclusive_claim_one_drives_other_awaits` | unit | two simulated claimers race one module → exactly one drives Phase-A; the other awaits the barrier (successor to S61 `try_unblock_locked_suppressed_*`) | exclusive pop / `eval_owned` removal (§7 step 3) | N | RED-first |
| `worker_phase_split_no_signature_gap_returned` | unit | a worker driving a 2-module import never returns a signature `ClusterOnce::Gap`; retry-from-top survives only for codegen gaps | `process_cluster_once` split (§7 step 4) | N | RED-first |
| `import_path_has_no_notify_symbol_typechecked_call` | unit | after the barrier lands, no `notify_symbol_typechecked` call remains on the import path (Principle-7 net-neutrality guard — the per-symbol readiness subsystem is **retired**, not paralleled) | dead-scaffolding sweep (§7 step 6) | N | RED-first |

> **Net-neutrality is load-bearing (`signature-body-prepass.md` §5 / Principle 6).** The
> barrier MUST **replace** the per-symbol wait/notify subsystem + the `eval_owned` /
> `eval_in_flight` flag family — not add a parallel protocol. `import_path_has_no_notify_symbol_typechecked_call`
> is the structural guard that the old path is gone. If `/dev` cannot achieve
> net-neutrality, that is the §7 arch-revisit signal (file FIXME `target:/arch`).

### 1D — E2E gate guards (`/qa`-authored)

| Test name | Tier | File | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `heisenbug_race_reduced_concurrent_import_pairs` | e2e | `tests/repl_persist_race.rs` | **Existing contention guard** (6 threads × 2 sequential import pairs, 10 trials; ledger:2118). Currently intermittently-green (passed in the 1648 baseline; fires ~5–10% under load). The gate requires it **deterministically green 20/20 under full-suite load** post-fix. | N | load-guard |
| `mutual_import_pair_diagnoses_cycle_not_hang` | e2e | `tests/spec_08_modules.rs` (new row) | two modules `a`/`b` each `(import [other [*]])` → assert the process **terminates within a bounded timeout** with a **cycle-detected diagnostic at the import site**, NOT a hang and NOT a panic. **HEAD: deadlocks (D0030 / FIXME 0426) → RED via timeout.** Post-fix (coarse reading): clean cycle error → GREEN. | P+N | RED-first (**conditional — see gap G1/FIXME 0448**) |

> `mutual_import_pair_diagnoses_cycle_not_hang` is the e2e-observable face of the D0030
> subsumption. Its assertion depends on **which reading `/arch` confirms (FIXME 0448)**:
> *coarse* (S93 default) → assert clean cycle-error; *fine* → assert the mutual import
> **compiles successfully**. Authored to the coarse reading (the gate's actual fix);
> re-pointed only if 0448 resolves fine. Either way it is RED-first on HEAD (hang).

### 1E — Pass criterion (the behavioural gate)

The gate is met when **all** hold:

1. `scheduler_race_read_inside_publish_window_finds_sibling_symbol` (1A) — **green in every
   schedule** (deterministic); loom variant (1B) green-in-all-interleavings if adopted.
2. `heisenbug_race_reduced_concurrent_import_pairs` (1D) — **green 20/20 under full-suite
   contention** (the load guard).
3. `mutual_import_pair_diagnoses_cycle_not_hang` (1D) — green (no hang; clean diagnostic).
4. Full suite shows **no RED beyond these named guards** while RED-first, then **0
   failures** once the fix lands.

The deterministic pin (1A/1B) answers "is the interleaving impossible by construction?";
the stress guard (1D) answers "does it survive real contention?" — both required, they
answer different questions (Principle 5). **The reactor (slice-2) implementation does not
begin until this criterion is met** (`SPRINT.md` Scope 1 gate).

---

## §2 — ABI-v7 effect-concurrency contracts (dormant / gated)

These landed in Phase 3 (`/arch`): `cranelisp_types::{ConcurrencyDescriptor, Poll,
PollFn}`, `cranelisp_platform::{HostCtx, Waker, WakerVTable, PollFn, ConcurrentPlatformFn}`,
`cranelisp_intrinsics::{StrandId, StrandEvent}`, all behind the off-by-default
`concurrency` feature; `ABI_VERSION` 6→7. The guards verify the contracts **compile under
the feature, stay absent in the default build, and the bridge round-trips** — they are
NOT behavioural (the reactor is unbuilt), so they are **entirely unit-tier** plus the
existing default-build absence e2e.

### 2A — What `/arch` already landed (`present`)

| Guard | Location | Status |
|---|---|---|
| `ABI_VERSION == 7` | `crates/cranelisp-platform/src/tests.rs:308` | present |
| concurrency types compile under `--features concurrency` | `crates/cranelisp-platform/src/concurrency.rs` + gated `pub use` in types/intrinsics | present (verified `cargo build --features concurrency`) |
| default-build absence / v6 field-order frozen | `tests/facade_pif_rows.rs` (diffs `public-api.txt`, generated WITHOUT the feature) | present (v6 `PlatformFn` rows pinned) |

### 2B — Owed guards (`/dev`-authored, gated `#[cfg(feature = "concurrency")]`)

**Coverage gap found (`/qa` 2026-06-27):** the `cranelisp-types/src/scheduling.rs`
`#[cfg(test)] mod tests` is **NOT** gated under `concurrency` and contains **zero**
tests for the v7 types — `from_scheduling_class`, the `ConcurrencyDescriptor` layout, and
the `Poll` repr are **uncovered**. These are owed:

| Test name | Tier | Crate / location | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `concurrency_descriptor_from_scheduling_class_bridges_three_classes` | unit | `cranelisp-types` scheduling tests (gated) | `from_scheduling_class(Sequential)` → `{token:1,cardinality:1,budget:0,blocking:1}`; `Commutative` → `{0,0,0,1}`; `ResourceSerial` → `{0,1,0,1}`; `_reserved == [0;3]` for all | P | RED-first |
| `concurrency_descriptor_repr_c_layout_and_inert_budget_present` | unit | `cranelisp-types` (gated) | `size_of::<ConcurrencyDescriptor>()` is the frozen v7 size; `token`/`cardinality`/`global_budget`/`blocking`/`_reserved` field offsets stable; the **inert `global_budget` slot is present** (the field reserved now to avoid a 7→8 bump — `SPRINT.md` arch R5) | P | RED-first |
| `poll_repr_i32_ready_zero_pending_one` | unit | `cranelisp-types` (gated) | `Poll::Ready as i32 == 0`, `Poll::Pending as i32 == 1` (the C-ABI collapse is byte-stable) | P | RED-first |
| `concurrent_platform_fn_repr_c_field_order_v7` | unit | `cranelisp-platform` (gated, beside `tests.rs:308`) | `ConcurrentPlatformFn` `#[repr(C)]` field order/offsets match the frozen v7 layout (`name`/`poll`/`param_count`/… per `concurrency.rs`) — the poll-shape successor to v6 `PlatformFn` | P | RED-first |
| `strand_id_root_is_zero_and_event_kinds_present` | unit | `cranelisp-intrinsics` (gated) | `StrandId::ROOT == StrandId(0)`; the slice-2 `StrandEvent` kinds construct (suspend/spawn/cancel/…) — the correlation newtype is landed | P | RED-first |
| `concurrency_descriptor_absent_from_default_public_api_neg` | e2e/unit | `tests/facade_pif_rows.rs` (new `_neg` row) | the default `cranelisp-types`/`-platform` `public-api.txt` does **NOT** name `ConcurrencyDescriptor` / `ConcurrentPlatformFn` / `Poll` (byte-identical-when-off, frozen edge intact) | N | present-extension |

### 2C — Gap G2: the `--features concurrency` lane — RESOLVED (`/arch` S93, FIXME 0449)

Every 2B unit guard is `#[cfg(feature = "concurrency")]`, so it **never runs** under the
canonical `cargo nextest run` (feature off). A gated test no lane exercises is invisible —
the same failure-class the failing-not-ignored discipline exists to prevent.

**Resolution (`/arch`, FIXME 0449 deleted).** An additive cargo alias runs the gated
guards with the feature ON for exactly the three contract crates:

```
cargo nt-concurrency
```

(defined in `.cargo/config.toml`, mirroring the existing `nt` alias; expands to
`cargo nextest run -p cranelisp-types -p cranelisp-platform -p cranelisp-intrinsics
--features cranelisp-intrinsics/concurrency`). `cranelisp-intrinsics/concurrency`
**transitively** enables `cranelisp-platform/concurrency` and
`cranelisp-types/concurrency`, so one feature flag covers all three crates in one
invocation.

This is **additive — a companion to `cargo nt`, NOT a replacement.** The default
`cargo nt` run and the `cargo public-api` api-check both stay feature-OFF, so the
dormant-contract absence guard (the §2B `_neg` row in `tests/facade_pif_rows.rs`) and the
frozen `public-api.txt` edge remain asserted **without** the v7 types — the lane never
pulls `concurrency` into the default/production build.

**Lane-liveness proof.** `/arch` landed one shallow gated smoke
(`cranelisp-types` `scheduling::tests::concurrency_lane_executes_gated_tests_smoke`,
`#[cfg(feature = "concurrency")]`) so the lane demonstrably **executes** a gated body —
verified: it runs under `cargo nt-concurrency` (1 extra test vs. feature-off) and is
**compiled out** under `cargo nt`. The substantive 2B layout/bridge guards (`/qa` +
`/dev`, this Phase) drop into the same lane and count as coverage the moment they land;
the smoke may be kept or absorbed once the richer guards exist.

**CI:** there is no CI workflow file — CI is by-convention `cargo nextest run` (root
`CLAUDE.md` §Testing). The canonical run is now the **pair**: `cargo nt` (feature-off,
the release gate) + `cargo nt-concurrency` (feature-on, the dormant-contract guards),
plus the unchanged feature-off `cargo public-api` api-check.

---

## §3 — FIXME drain — test dispositions

For each drain-set FIXME: does it need a failing repro test (defect) or is it doc/design
closure (finding)? Per `memory/feedback_no_fixme_with_failing_test.md`, a finding closes
on documentation; only a defect owes a failing-not-ignored repro.

| FIXME | Target | Class | Test owed? | Disposition |
|---|---|---|---|---|
| **0410** | /repl | finding (ergonomic; current behaviour spec-correct) | **No.** Doc/design closure. *If* /repl + /spec settle §8.11.4 present-default semantics and /int implements the scaffold writer, that increment owes its own unit (default-content + no-overwrite + resolution-unchanged) + e2e (REPL launch on bare project dir creates file, still resolves prelude) — but those land **with the implementation**, not this sprint's drain. | doc-only this sprint |
| **0423** | /int | **defect** (source-regen writes CWD-relative; stray root dirs; `: Type` spacing) | **Yes — `/qa` repro.** `tests/regression.rs::regen_writes_lib_dir_relative_not_cwd_neg`: run the binary with CWD = fresh tmpdir ≠ lib-dir, exercise a `(mod test)` module, assert **no stray backing files appear outside the lib-dir** (currently they do → RED-first). Second assertion: regen emits `:Type` (no space), not `: Type` (`memory/annotation-reader-macro-binds-following-form`). | **failing repro** |
| **0430** | /design | finding (descoped half-feature removed, nothing broken ships) | **No** — explicitly "no failing repro owed." Durable record of the descoped `set-doc` increment. When /design specs the docstring-into-source regen and /dev re-lands `set-doc`, that increment owes the persistence e2e (`set-doc` then restart → `/doc` shows it). Not this sprint. | doc-only |
| **0433** | /spec | **arbitration** (§4.8.4 example vs §6.2 grammar contradiction) | **Conditional.** If /spec rules literal patterns are **not** a feature → fix §4.8.4, doc-only closure. If /spec rules they **should** be supported → it becomes a defect and `/qa` owes a failing repro: `tests/spec_06_pattern_matching.rs::match_literal_pattern_dispatches` (+ a `_neg` that a non-matching literal falls through) — a **+Neg** pair. **`/qa` cannot author until /spec arbitrates.** | **blocked on /spec ruling** → then +Neg repro or doc-only |
| **0434** | /qa | **coverage sweep** (qualified-vs-bare name positions — proactive class, no single defect) | **Yes — `/qa` sweep.** See §3.1 below (scoped). The D-qual-impl-target repros already exist; this generalises the guard across every REPL-display-qualified name-position. Gate-relevant for the sprint that fixed D-qual-impl-target (S91) — do the sweep while context is hot. | **`/qa` sweep (this sprint)** |
| **0440** | /design | finding (REPL-only introspection Principle-7 dedup; not a compile-path divergence) | **No** — explicitly "no new failing test required." The existing `list_classification_tests.rs` + `repl_introspection.rs` byte-identity tests are the regression guard for the /design + /dev refactor. | doc/refactor-guarded |
| **0446** | /repl | finding (normative-home gap for `CRANELISP_SPARK_BUDGET` / `CRANELISP_NO_LENIENT`) | **No** — "no defect, no failing test." /repl adds the env-var rows to `repl/spec.md §0`. | doc-only |

### 3.1 — FIXME 0434 sweep scope (`/qa`-owned, this sprint)

The sweep adds a **qualified-AND-bare pair** (or a `_neg` that the qualified form must NOT
re-root) for each name-position the REPL displays qualified. Scoped to the
REPL-display-qualified positions named in the FIXME (impl targets ✓ already done by the
D-qual-impl-target repros):

| Test name | Tier | File | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `type_annotation_qualified_and_bare_resolve_identically` | e2e | `tests/spec_04_expressions.rs` | `:primitives/Int x` and `:Int x` (under prelude) infer/resolve to the same canonical type; the qualified form is NOT re-rooted to `user/primitives/Int` | P+N | RED-first if the position is unswept (verify on HEAD) |
| `deftype_deftrait_reference_qualified_and_bare_equiv` | e2e | `tests/spec_07_traits.rs` | a `deftype`/`deftrait`/`impl` **type reference** in qualified vs bare form resolves to the same canonical name | P+N | verify-on-HEAD |
| `match_qualified_constructor_pattern_resolves` | e2e | `tests/spec_06_pattern_matching.rs` | a qualified constructor pattern (`user/Color.Red` form per the FIXME) in `match` resolves identically to the bare form | P+N | verify-on-HEAD |
| `import_mod_target_qualified_and_bare_equiv` | e2e | `tests/spec_08_modules.rs` | qualified vs bare import/`mod` targets resolve identically | P+N | verify-on-HEAD |

> **`verify-on-HEAD`**: D-qual-impl-target was fixed in S91, so sibling positions **may
> already pass** — each row is authored and run on HEAD first. A row that passes is a
> standing `[Tested+Neg]` guard against regression of the qualified path (the structural
> blind spot the FIXME names); a row that **fails** is a newly-surfaced sibling defect →
> handed to `/frontend` (the D-qual-impl-target resolver) with the minimal repro. Either
> outcome closes the sweep with committed tests. Spec-side: coordinate the `[Tested+Neg]`
> flip on `spec/07-traits.md §7.3.1` with `/spec`.

---

## §4 — Regression + conditional reactor e2e

- **Baseline green confirmed**: 1648/1648 (§Baseline above). The drain + gate work must
  not regress it; the only new RED is the in-scope RED-first rows.
- **`run_through_all_modes` replay**: the `mutual_import_pair_diagnoses_cycle_not_hang`
  row and the 0423/0434 e2e rows run through the modes their behaviour spans (REPL +
  `--run`; the regen row is `--run`/runner-CWD specific).
- **Conditional reactor e2e (stretch — spillable to S94).** *If* the slice-2 minimal
  host-reactor + one async-leaf effect lands (`SPRINT.md` ranked deliverable 3,
  feature-gated, byte-identical-when-off), it owes an **e2e** under `--features
  concurrency`: `tests/concurrency_reactor.rs::two_slow_reads_overlap_one_thread` —
  assert two slow reads **overlap on the reactor** (wall-clock < serial sum), **no
  thread-per-read**, and a **strand-correlated event stream is visible** (the acceptance
  target). **Flagged conditional**: authored only if the reactor lands this sprint;
  otherwise it carries to S94 with the slice. Its observability surface is dev-facing only
  (no user-visible spec change — `/arch` FIXME 0447 / `/spec` rules visibility).

---

## §5 — Phase-3 exit gate confirmation

`/qa` confirms it has enough to draft the Phase-5 Stage-1 failing tests:

- **Race gate (§1)**: 1 deterministic pin + 1 loom variant + 6 per-step structural unit
  seams (`/dev`, `src/scheduler.rs::tests`); 1 e2e load-guard (existing) + 1 e2e
  cycle-error row (`/qa`, RED-first). **Pass criterion stated (§1E).** This is the
  non-negotiable gate.
- **ABI-v7 (§2)**: 3 `present` guards confirmed; **6 owed guards** named (5 unit + 1
  `_neg`), addressing the uncovered `from_scheduling_class` / descriptor-layout / `Poll`
  gap. **Gap G2 RESOLVED** (`/arch`, FIXME 0449 deleted) — the gated guards run via the
  additive `cargo nt-concurrency` lane (§2C).
- **FIXME drain (§3)**: 2 failing repros owed (**0423** defect; **0434** sweep, this
  sprint); 1 conditional on a /spec ruling (**0433**); 4 doc/design-only (0410, 0430,
  0440, 0446).

### Flagged gaps blocking Stage-1 authoring

- **G1 — FIXME 0448 (`target:/arch`, already filed by /design):** the
  `mutual_import_pair_diagnoses_cycle_not_hang` assertion (clean cycle-error vs.
  successful mutual-import compilation) depends on the coarse-vs-fine reading. Authored to
  **coarse** (the gate's actual fix, src/-only); re-pointed only if /arch rules fine. Does
  NOT block the gate.
- **G2 — RESOLVED (`/arch`, FIXME 0449 deleted):** the §2B gated guards now run via the
  additive `cargo nt-concurrency` lane (`.cargo/config.toml`; §2C). No longer blocks the
  ABI-v7 guards counting as coverage.
- **0433 — blocked on /spec arbitration:** `/qa` cannot author the literal-pattern repro
  until `/spec` rules whether literal patterns are a language feature.
