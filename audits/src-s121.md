# `src/` Binary / Integration Whole-Context Assessment — Sprint 121

> **Boundary.** `src/` and its binary/exe-bundle integration responsibility:
> compilation, REPL and watcher cadences; session/reload/cache orchestration;
> CLI/linking; display and developer tooling. The language runtime remains an
> intrinsics/backend concern, for which this context is a host client.
>
> **Checkpoint.** Read-only assessment of the S121 Phase-6a working tree at
> `HEAD` `18bca20d`; the tree was intentionally dirty with accepted sprint
> work. This is the only audit artefact written. The accepted Phase-5 gate is
> `/tmp/cranelisp-s121-capacity-isolation-0VnQCq/capacity-measurement-full-nextest-replacement.log`:
> 5,897 run, 5,897 passed, one skipped, in 100.450 seconds.
>
> **Method.** `sprints/METHOD.md` §2.7 acid test and the audit contract.
> Recommendations go to next sprint's user disposition; they neither reopen
> Phase 5 nor authorize implementation.

## 1. Verdict

### Acid test — would a lean, high-quality second implementation look like this?

| Attribute | Grade | Basis |
|---|---|---|
| Design quality | **strong** | The three cadences, one cluster-to-scheduler crossing, one display-rendering authority, host-client runtime seam, and table-owned lifecycle are boundaries a replacement should retain. |
| Design realization | **weak** | A settled S121 C6 design calls for consuming `instantiate_demands` and retiring reload source-form replay, but source retains replay and no Binary/int consumer exists (F-1). Whether that design remains necessary after later redefinition simplification is not established here. |
| Simplicity and volume | **adequate** | The REPL decomposition remains intact, but consequential normal-path functions materially exceed the context's own ~100-line guide (F-3). |
| Duplication and boundary discipline | **strong** | The old bootstrap/typecheck ADT-entry derivation is now single-sourced in `cranelisp_types::build_adt_entries`; int does not recreate runtime internals. |
| Risk-weighted evidence | **adequate** | The accepted full gate and focused capacity evidence cover delivered behavior. They cannot exercise an absent Binary/int consumer; the typecheck API has unit tests only (F-1). |
| Maintainability | **C** | The context remains practicable and its normal seams are recognizable, but an unused public capability plus a retained older replay mechanism multiply future reload/change/review reasoning. Oversize orchestration functions add bounded recurring cost. |
| Memory freshness | **weak** | `src/lib.rs` says the `repl/` module is deleted directly after declaring it live and describes still-live work as future (F-2). |

**Overall.** A second implementation would retain the context's boundary and
most seam choices. It would not leave an approved public foundation with no
production consumer while retaining a purportedly retired mechanism, and it
would not keep contradictory module-map commentary. This is not a claim that
the accepted compiler behavior is unsound: the older replay path has an
established reachability rationale. It is a design-realization and maintenance
finding, whose current authority must be reconciled before it is treated as
work.

## 2. Required capability and fulfilment

In ordinary terms, this context turns a project or REPL turn into compiled and
executable Cranelisp through one pipeline; exposes the specified REPL/CLI
experience; and coordinates reload, cache and developer tooling without owning
the language runtime.

| Obligation | Assessment | Evidence and limit |
|---|---|---|
| Delivered compiler and capacity behavior | **Met at accepted Phase-5 checkpoint** | The authoritative full-gate log reports 5,897/5,897 pass; `sprints/SPRINT.md` records the linked-capacity isolation/control and preserved capacity-1 ordering. This audit did not rerun it. |
| Integration/runtime ownership split | **Met by structure** | `design/arch/bounded-contexts.md` §6 and `design/int/CLAUDE.md` allocate orchestration to int and the reactor/permit/runtime implementation elsewhere; the `cluster`, `worker`, and platform client surfaces conform. |
| S121 reload re-instantiation design | **Unrealized as written** | `instantiate_demands` exists in `crates/cranelisp-typecheck/src/form.rs`, but no production call occurs under `src/`. `src/redefine.rs` still captures `__expr`; `src/session_v4/lifecycle.rs` still accepts/appends `extra_forms`. This is F-1, not a determination that the design is still required. |
| Current source navigation record | **Partly met** | `design/int/int.md` and `src/CLAUDE.md` are useful current maps. The contradictory `src/lib.rs` comment is F-2. |

## 3. Findings and proposed next-sprint routing

Priorities are assessment priorities, not authorized work. No recommendation
has a disposition at this checkpoint.

### F-1 — S121 reload design and current Binary/int realization diverge

**Priority:** high · **Likelihood:** certain (source census) · **Cost class:**
large, cross-context · **Evidence:** direct.

The S121 plan approved inclusion of the set-instantiation entry point and
retirement of source-form replay in the same stream (`sprints/SPRINT.md`,
Phase-2 0553 decision). C6 §4.5, “What retires in the same change-set,” says
`capture_instantiation_drivers`, `reload_module(extra_forms)`, and the
`__expr` introspection read retire together. The current source instead
retains each part:

- `src/redefine.rs::capture_instantiation_drivers` reads the one saved
  `__expr` form;
- `src/redefine.rs::drive_t1_full_cure` passes it to reload; and
- `src/session_v4/lifecycle.rs::reload_module` receives `extra_forms` and
  appends it to freshly parsed source.

The new typecheck entry exists and has unit cases
(`crates/cranelisp-typecheck/src/form.rs:394` and `form/tests.rs`), but a
production-caller census has no `src/` hit. `design/arch/bounded-contexts.md`
§2 likewise calls Binary/int its intended consumer and records it as currently
having none.

This establishes an as-designed/as-built mismatch and an unused cross-crate
capability. It does **not** prove the former set-capture design remains
semantically necessary after the later user-approved redefinition narrowing,
nor does it by itself prove a defect in the older replay behavior.

**Route and recommendation:** `sprint` presents the mismatch at next sprint's
Phase 1. `arch`/`design` (int) must reconcile the current authority: retain and
implement the approved handoff through the required approvals, explicitly
remove/defer the unused capability, or revise the design through the proper
user gate. `/qa` should decide whether a minimal current reload repro/control
shows an observable defect before any implementation is scheduled. No current
sprint work follows from this assessment.

### F-2 — A live module comment contradicts the compiled source map

**Priority:** moderate · **Likelihood:** certain · **Cost class:** small ·
**Evidence:** direct.

`src/lib.rs:96-98` declares `pub(crate) mod repl` and then says the `repl/`
module was deleted, with save, trace and run-tests described as future. The
five-file `src/repl/` surface, save, trace observability and test discovery are
live. The comment conflicts with the otherwise current `src/CLAUDE.md` and
`design/int/int.md` maps and misdirects readers entering the context.

**Route and recommendation:** `/dev` (src) owns the small comment correction;
`/design` (int) checks map alignment on the next scoped source-map edit. The
next-sprint disposition may remove the stale history or replace it with a
current responsibility line; behavioral testing is not warranted.

### F-3 — Core orchestration exceeds its stated local complexity budget

**Priority:** moderate · **Likelihood:** certain · **Cost class:** medium,
local · **Evidence:** direct.

The local convention is approximately 100 lines per function. Current
production functions include `compile_and_publish_prepared` (294 lines,
`src/worker.rs:1275-1568`), `process_regular_form_with_origin` (255,
`src/process_form.rs:1076-1330`), `link_by_name` (216,
`src/session_v4/lifecycle.rs:2120-2335`), and
`load_cached_module_via_linker` (215, `src/worker.rs:1878-2092`). Changes to
publication, owner retention, reload, or cache restoration therefore require
readers to hold several policies at once.

Named phases and adjacent unit tiers mean this audit does not infer that a
generic extraction campaign would be safer now. The excess is maintenance-grade
evidence: the stated budget is not reliably met at consequential seams.

**Route and recommendation:** `/design` (int) decides, when planned work opens
one of these seams, whether a locally cohesive decomposition or a narrower,
truthful exception is appropriate. `/dev` (src) acts only on an approved cut.
Do not schedule a broad refactor from this audit alone.

## 4. Strengths retained from the source sweep

- The S109 bootstrap/typecheck ADT-registration mirror is genuinely converged:
  both writers use `cranelisp_types::build_adt_entries`, leaving context-specific
  settlement to their callers.
- The REPL remains split into command, search, value-format and type-format
  responsibilities rather than regrowing the former monolithic file.
- High-risk seams remain concentrated: staged publication in `worker.rs`, one
  result-owner finalization path, and the host-client platform boundary. No
  int-side reactor or parallel runtime ownership model was found.
- The accepted capacity repair is proportionate: it separates linked execution
  timing while preserving established result and capacity-1 ordering controls.

## 5. Evidence limits

- This audit performed no build, test, binary, REPL, benchmark, or process
  execution. The full-suite result is accepted prior evidence, not reproduced
  here.
- A passing suite demonstrates its covered delivered behavior; it cannot prove
  a source path is absent or exercise a non-existent Binary/int consumer.
- The checkpoint is a dirty working tree. This report makes no commit, release,
  cache-compatibility, or production-readiness claim.

## 6. Disposition record

Pending the user's next-sprint Phase-1 decision:

| Finding | Proposed owner(s) | Proposed disposition | Status |
|---|---|---|---|
| F-1 | `sprint` to present; `arch`, `design` (int), and `qa` for authority/evidence follow-on | Reconcile the approved design with current authority before deciding implementation, removal, deferral, or revision | unresolved |
| F-2 | `dev` (src), with `design` (int) map check | Correct/remove stale module commentary on the next scoped source-map edit | unresolved |
| F-3 | `design` (int), then `dev` (src) if approved | Revisit only when planned work opens an identified function | unresolved |

`audit` files no action from this table and does not block S121 closure.
