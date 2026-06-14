# Sprint 82 — /qa Test Plan (Phase 3 Design)

Decks-clearing sprint. Three workstreams: **D** (7 defect guards → green),
**H** (legacy harvest-and-delete, 20 files / 12 FIXMEs), **F** (FIXME drawdown).

This plan is the `/qa` deliverable for Phase 3. The harvest measurement-gate
methodology (§2) is the centerpiece — spelled out so Phase-5 harvest agents can
execute it file-by-file.

Starting state (S81 close): **1290 passed / 14 failing-not-ignored e2e defect
guards / 2 unit-tier repros / 0 skipped.** A genuine regression is any RED
beyond these 16 named guards.

---

## Workstream D — the 7 defect guards (already authored; fix flips them)

All guards exist in the suite as of S81 close (failing-not-ignored). `/qa`'s
Phase-5 D work is NOT to author them — it is the **repro-before-handoff gate**
for `0342` and `0340` (§1.2 / §1.3 below) and to verify each guard flips green
when `/dev` lands the fix, with a unit-tier repro at the seam.

### Guard inventory (the 14 e2e + 2 unit starting state)

| FIXME | e2e guard(s) (file::fn) | failing | unit-tier repro at seam | `// spec:` anchor |
|---|---|---:|---|---|
| `0337` | `spec_08_modules.rs::bare_mod_decl_resolves_sibling_file_for_entry_main`; `::bare_mod_decl_neg_does_not_seek_nested_submodule` | 2 | OWED — `src/` (module resolution) `#[cfg(test)]` at the bare-`(mod name)` sibling-resolve seam | spec/08-modules.md §8.2 |
| `0338` | `repl_introspection.rs::bare_trace_special_form_carries_type_prefix`; `::info_resolves_trace_special_form`; `::info_resolves_if_special_form`; `::sig_resolves_trace_special_form` (+ `::bare_if_special_form_carries_type_prefix_control` is a PASSING control, not a guard) | 4 | OWED — `src/` REPL display + `/info`·`/sig` introspection dispatch | repl/spec.md §4.1.5 (`:Type` prefix) + §3.6 (`/info`) + §3.1 (`/sig`) |
| `0340` | `trace.rs::trace_captures_call_name_and_operands`; `::trace_neg_no_placeholder_name_or_empty_args` (**capture** half only) | 2 | OWED — split per crate: capture → `cranelisp-intrinsics` (trace bodies/descriptor); timing → `cranelisp-backend` (per-call GOT rediscovery) | spec/04-expressions.md §4.12.3 |
| `0341` | `spec_07_traits.rs::stacked_trait_bounds_single_param_compiles`; `::stacked_trait_bounds_two_params_compiles` | 2 | PRESENT — `crates/cranelisp-frontend/src/ast_builder.rs::stacked_trait_bound_annotations_attach_to_single_param` | spec/07-traits.md §7.8.2 |
| `0342` | `spec_08_modules.rs::super_import_resolves_parent_fn`; `::super_import_resolves_parent_type_constructor` | 2 | OWED post-triage — lands in whichever crate Step-2 introspection elects (typecheck resolve.rs OR src/ load-ordering) | spec/08-modules.md §8.3.8 |
| `0343` | `repl_persist.rs::mod_submodule_body_survives_source_regeneration` | 1 | OWED — `src/` (save.rs / session_v4 regen) at the `generate_mod_decls` / regen-gate seam | repl/spec.md §15.4 + spec/08-modules.md §8.2.2 |
| `0344` | `spec_04_expressions.rs::polymorphic_accumulator_fold_does_not_over_unify` | 1 | PRESENT — `crates/cranelisp-typecheck/src/program/tests.rs::fold_polymorphic_accumulator_does_not_over_unify` | spec/03-types.md §3.4 |
| | **total** | **14** | **2 present + 5 owed (from `/dev`)** | |

**Unit-test-per-fix obligation (CLAUDE.md §Testing).** `0341` and `0344` already
ship a unit-tier seam repro (S81). The other five fixes (`0337`/`0338`/`0340`
×2 crates/`0342`/`0343`) MUST land a `#[cfg(test)]` unit at the seam in the SAME
change-set as the fix — `/dev`-authored (these are unit tests in `crates/*/src`
or `src/`, not `/qa`'s tier). `/qa`'s acceptance check at Phase 6 confirms the
unit exists alongside the flipped e2e guard.

### 1.2 `0342` — repro-before-handoff gate (Rev 2)

`0342` MUST NOT enter `/dev` until `/qa` runs the Step-2 introspection probe that
decides ownership. The two e2e guards above are the repro; the deciding artifact
is a **`/info`-on-parent** check at the failure point:

- Add (or run in-session) a `repl_capture("/info superp/helper\n")`-shape probe
  against the failing two-file project, per tests/CLAUDE.md §"Isolating
  Cross-Crate Failures" Step 2.
- **Decision rule:**
  - *missing symbol* (parent `helper`/`Box` absent from the table when the
    submodule typechecks) → **int load-ordering** (`src/`): the submodule's
    typecheck fires before the parent's defs land in the shared tables. typecheck's
    bounded module-locality walk (Principle 17) returning "not found" is *correct*
    here — the bug is orchestration.
  - *present-but-unreached* (parent symbol IS in the table but the `super` resolve
    path doesn't reach it) → **typecheck** (`resolve.rs`).
- The handoff brief names the probe result + the elected crate. The unit-tier
  repro then lands in that crate.

### 1.3 `0340` — two split repros (Rev 2)

The defect is two independent failures; route each to its own crate.

- **Capture repro (PRESENT):** `trace.rs::trace_captures_call_name_and_operands`
  + `::trace_neg_no_placeholder_name_or_empty_args` already assert the
  output-correctness half (name = `add-i64` not `"::trace::"`; args not
  `SList.SNil`). → **`cranelisp-intrinsics`** (trace bodies / `DisplayDescriptor`).
- **Timing repro (OWED — `/qa` authors in Phase-5 Stage 1):** a NEW guard
  asserting `(trace (small-expr))` completes **sub-second**. Timing is
  non-deterministic, so the existing capture guard deliberately omits it. The
  timing guard must be written to be a stable signal, not a flaky one:
  - Measure wall-clock around a single `repl_capture("(trace (add-i64 1 2))\n")`.
  - Assert a **generous ceiling** well below the reported ~31s but well above
    normal jitter — recommend **< 5s** (the observed bad path is ~31s; a healthy
    path is ~0.12s; 5s is a 6× margin over bad-path-impossible while ~40× over
    healthy). Keep it `#[ignore]`-free (failing-not-ignored) but document the
    ceiling rationale inline so it is not mistaken for a tight perf microbench.
  - Route → **`cranelisp-backend`** (per-call rediscovery iterating all GOT
    slots). The `/dev` backend fix lands its own unit/criterion at the
    rediscovery seam.

  *Note:* this timing guard is the ONE Workstream-D e2e test `/qa` authors
  failing-first in Phase-5 Stage 1 (everything else in D is already present).

### 1.4 `0337` — CI-coverage corrective (intrinsic to its close)

Beyond the two existing guards, `0337`'s close REQUIRES extending CI to run a
multi-file directory example — the gap that let the breakage sail through every
sweep. `/qa` authors this in Phase-5 Stage 1:

- Extend `tests/examples.rs` (the canonical `examples/*.cl` umbrella, currently
  excludes `16-modules/` "a directory, not a top-level .cl file") to run a
  **directory-entry** example: `examples/16-modules/main.cl`, asserting its
  documented exit (the file's own comment says 303; confirm against the example
  at author time and assert that checksum).
- This is a real, durable CI extension — NOT a defect guard. It stays green once
  `0337` is fixed and catches future multi-file-module regressions. It is the
  third deliverable of `0337` alongside the two failing guards.
- The two-file *minimal* repro already lives in `spec_08_modules.rs` (the
  reduced form `/qa` produced per the protocol); `examples.rs` adds the
  realistic-shape CI coverage. Both are needed — minimal for debugging, realistic
  for the coverage corrective.

---

## Workstream H — the HARVEST MEASUREMENT GATE

The confidence-to-delete exercise. 20 files / 1,323 tests / 12 FIXMEs. Build on
the **existing S64 dedup-audit methodology** (`tests/plan/wave-5.5-dedupe-audit.md`
+ the six `wave-5.6-*-reaudit.md` per-file audits) — that work already
dispositioned much of `e2e/ring0/ring1/ring2/sketch_port` at per-test
granularity. Phase-5 Stage 1 EXTENDS those audits to full coverage and to the
files never audited, then harvests + deletes.

### 2.1 The gate, stated as a hard rule

> **NO legacy assertion is dropped without a written disposition.**

For each of the 20 files, produce a per-file **disposition doc** mapping every
legacy assertion to exactly one of three dispositions:

| Disposition | Meaning | Action |
|---|---|---|
| **COVERED** | An active test already asserts this behaviour | Name the active test (`tests/file::fn` or `crate::module::fn`). No harvest. |
| **GAP** | Genuine coverage hole — no active test asserts it | Harvest: author a `#[cfg(test)]` unit (or e2e where parity-shaped) in the owning crate, `// spec:`-annotated. |
| **OBSOLETE** | Tests retired behaviour / a non-spec implementation detail / a known-defer | Drop with a one-line written reason (cite the superseding spec/decision/FIXME). |

A file is **DONE only when deleted** — file + `tests/legacy/README.md` row +
FIXME closed. Partial-sprint progress is measured in whole files removed, never
in assertions touched. The whole-file-deletion discipline keeps any under-run
shipping complete units.

### 2.2 How the audit is performed (read-only, parallelizable)

The dedup-audit is **read-only** and fans out in parallel (per CLAUDE.md
"read-only fan-outs may run in parallel"); only the harvest *edits* serialize.

Per file, the audit agent:

1. **Enumerate assertions.** Walk every `#[test]` fn in the legacy file; for each,
   list its distinct behavioural assertions (a multi-assert test is multiple
   rows — per Wave-5.5 risk class 5, collapsing multi-assert tests to a single
   e2e witness loses internal-step coverage; each step gets its own row).
2. **Match against the active suite.** For each assertion, search the active
   tier (`tests/*.rs` e2e + `crates/*/src` `#[cfg(test)]` unit) for an existing
   test asserting the same behaviour. Use spec-anchor + behaviour, NOT
   source-file shape (per the S64 "spec-anchored re-authoring naturally
   deduplicates" finding). Record the match → COVERED with the named test.
3. **Apply the Wave-5.5 risk lens before tagging COVERED.** Do not tag COVERED on
   a surface-string match alone. Check the five risk classes that caused the
   S64 concern:
   - regression-named tests with specific defect lineage (preserve as
     REGRESSION-GUARD if the active suite lacks the lineage);
   - context-sensitive assertions (same surface, different syntactic shape →
     different compile path → may be a real GAP);
   - mode-shape interactions (integration vs subprocess vs Rust-API exercise
     different pipelines);
   - mainstream-looking edge cases (the `/reset` precedent);
   - multi-assertion collapse (per step 1).
   If any risk class applies and the active coverage does not cover it → GAP, not
   COVERED.
4. **Tag the residue.** Anything not COVERED is GAP or OBSOLETE; OBSOLETE
   carries its written reason.
5. **Emit the disposition doc** (see §2.3).

### 2.3 The artifact — per-file disposition doc

One doc per file under `tests/plan/`, named
`s82-harvest-{file}.md` (e.g. `s82-harvest-lenient.md`). Where a S64
`wave-5.6-{file}-reaudit.md` already exists, the S82 doc may extend/supersede it
(cite it). Each doc contains:

- **Header:** file, LOC, test count, owning crate(s), FIXME number.
- **Disposition table:** one row per assertion — `{legacy fn / assertion} |
  COVERED (named active test) | GAP (→ target crate + planned unit name) |
  OBSOLETE (reason)`.
- **Summary line:** `N assertions: C covered / G gap / O obsolete` — this is the
  measured number that turns "re-port 1,323 tests" into "port the G gaps,
  confirm the C, drop the O."
- **Exit checklist:** (a) every assertion dispositioned; (b) all G harvested +
  green in the owning crate; (c) file deleted; (d) README row removed; (e) FIXME
  closed (deleted with a commit naming what was resolved).

### 2.4 Exit condition per file

A file exits (is deleted) when: **every assertion is dispositioned in writing**
AND **every GAP has landed** as a `#[cfg(test)]` unit/e2e (green, `// spec:`)
in the owning crate. Then `/dev` (or `/qa`/`/port` for their slices) deletes the
file + README row + FIXME, single commit.

### 2.5 Partition confirmation + flags

The `0134` partition is **confirmed**:

- **typecheck** = AST/type-shape + inference assertions + `assert_type_error`
  callsites → translate to direct `tc.check()` invocations. Largest share.
- **backend** = `assert_rc_balanced` + closure-capture + Vec-COW codegen → RC
  counter / CLIF inspection at the unit tier.
- **int** = `compile_both()` batch/REPL **parity** = an **e2e** property already
  exercised by the canonical e2e suite's `run_through_all_modes` discipline →
  **mostly delete** (e2e-covered; no int unit harvest warranted, per the S81 W-E
  int review on `0134`). int's `target:` is retained only as the multi-skill
  coordination anchor.

**No mis-assignment found.** Two notes to carry into Phase 5:

- **Co-owner relabel (post-D43):** `cranelisp-runtime` no longer exists. The
  `0130` (ring4_trace_taxonomy) and `0135` (lenient) "runtime" co-owner is now
  **`cranelisp-intrinsics`** (trace bodies) for `0130` and **`cranelisp-primitives`**
  for `0135`. The README rows still say "/runtime" — `/qa` flags this for the
  README update at delete-time (the README row is removed when the file is
  deleted, so the relabel is moot at exit, but the audit doc must name the
  correct crate as the GAP target).
- **`0136` (sketch_port, 296 tests) is `/qa`-internal** — `/qa` performs both the
  audit AND the harvest (most content is already covered by the spec-section
  carry-forward; `wave-5.6-sketch-port-reaudit.md` already exists). The 11
  known pre-existing sketch_port failures are exercising real compiler corner
  cases — any GAP among them harvests as a failing-not-ignored unit in the owning
  crate (NOT dropped as OBSOLETE just because it fails).

### 2.6 File-by-file work order (Phase 5)

Sequencing recommendation (audits parallel; harvest edits serial per file). Land
`0109` Wave D (session_v4/worker decomposition) **before** the int-slice harvest
so the int harvest targets the decomposed shape, not the monolith.

| FIXME | File(s) | Audit owner | Harvest owner | Notes |
|---|---|---|---|---|
| `0134` | e2e(309)+ring0(216)+ring1(380)+ring2(405) | parallel fan-out | typecheck + backend (int slice = delete) | Extend `wave-5.6-{e2e,ring0,ring1,ring2}-reaudit.md`; int slice e2e-covered |
| `0136` | sketch_port(296) | /qa | /qa | self-contained; `wave-5.6-sketch-port-reaudit.md` exists; preserve 11-failure lineage |
| `0124` | repl_experience(190)+repl_negative_old(31) | parallel | src/ (w/ typecheck, backend) | REPL-experience: many COVERED by `repl_*.rs` active suite |
| `0125` | ring3_repl(41) | parallel | src/ (w/ typecheck) | |
| `0127` | io(76)+io_minimal(5) | parallel | src/ (w/ typecheck, backend) | IO surface: check `spec_10_io.rs` coverage first |
| `0130` | ring4_trace_taxonomy(31) | parallel | typecheck (co: **intrinsics**) | trace taxonomy; co-owner relabel |
| `0133` | v4_jit_reclaim(6) | parallel | backend | small; JIT reclaim |
| `0135` | lenient(32) | parallel | backend (co: **primitives**) | co-owner relabel; check `spec_04` lenient coverage |
| `0143` | examples(15)+examples_run(1)+exemplar(3)+exemplar_solver_correctness(2) | /port | /port | check `tests/examples.rs`/`exemplar.rs` active coverage |
| `0144` | sprint23(61) | parallel | src/ | |
| `0148` | wave6_demo_repros(5) | parallel | src/ (w/ backend, stdlib, port) | demo repros — likely defect-lineage; preserve as REGRESSION-GUARD |
| `0149` | v4_pipeline(47) | parallel | src/ (w/ backend, frontend, platform) | run against decomposed shape (post-0109 Wave D) |

---

## Workstream F — test needs

- **`0021`** (criterion microbench for IO-trace off-path overhead, <1% AC) is
  **/qa-authored**, but **AFTER `0336`** lands the `#[cfg(feature = "bench")] pub
  fn` accessor over the filter-off `record_event` path (NOT a `[lib]` target).
  `/qa` writes a criterion bench measuring trace-disabled overhead vs baseline,
  asserts < 1% off-path, and tightens the integration ceiling. Sequential after
  `0336`; not in Stage 1.
- **`0243`** (narrow heavy typecheck fixtures — adt/checker/traits + shared
  helpers to minimal presets) is **test-internal and `/dev`-owned** (typecheck
  crate unit fixtures, not `/qa`'s tier). It is a green-tests-dominate refactor:
  the fixtures already pass; the work shrinks them. `/qa`'s only interest is
  suite-runtime stewardship — confirm no runtime regression after the narrowing.
  No new `/qa` test.

---

## Stage-1 QA-first note (Phase 5)

What `/qa` authors **failing-first in Phase-5 Stage 1** vs what is already
present:

**Already present (S81) — do NOT re-author:**
- All 14 e2e Workstream-D guards + the 2 unit-tier repros (`0341` frontend,
  `0344` typecheck).

**`/qa` authors in Stage 1 (failing-first / new):**
1. `0340` **timing guard** (sub-second `(trace …)` ceiling, < 5s, → backend) —
   the one new D guard.
2. `0337` **CI corrective** — extend `tests/examples.rs` to run
   `examples/16-modules/main.cl` (directory-entry), assert documented exit. Green
   once `0337` is fixed; not a failing guard.
3. `0342` **introspection probe** — the `/info`-on-parent Step-2 check that
   decides ownership before `/dev` opens (gate, not a permanent guard).

**Harvest GAP tests** are NOT Stage-1 QA-first authoring — they are authored
during the per-file harvest (Stage ≥2), `/dev`-owned for crate-unit GAPs,
`/qa`-owned only for the `0136` sketch_port slice and any e2e-shaped GAP. The
measurement-gate AUDIT (§2.2) runs read-only and parallel ahead of harvest.

**`0021`** is authored after `0336` (sequential F), not in Stage 1.
