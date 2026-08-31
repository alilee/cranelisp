# Sprint 120: FIXME 0917 provenance correction

**Status**: USER ACCEPTED — the user accepted the bounded 0917 correction on
2026-08-31 after independent review and final QA judgment. Commit, archive and
formal closure remain separate, unauthorized actions.

**Goal**: Correct backend value-provenance classification so a match arm that
returns a nullary constructor beside a freshly boxed arm does not strand the
boxed result.

**Audit**: none. This is a deliberately bounded compiler correction used to
exercise the shared delivery roles on real compiler work; the standing audit
rotation is not expanded into this sprint.

## Approved scope

The only product defect in scope is FIXME 0917.

In scope:

- confirm the existing requirement and backend design without changing either;
- publish one compact QA evidence delta for the correction;
- assess the existing independent run/link subject-control evidence before
  implementation and add no duplicate evidence when it is already adequate;
- change `cranelisp-backend` value provenance and its module-level unit tests;
- independently review the delivered backend change;
- run focused backend, run/link, exemplar, CLIF-identity and full-suite gates;
- return the verified result to the user for acceptance before closure.

Out of scope:

- every other open defect, including 0907, 0913, 0916, 0868 and 0869;
- language semantics, public APIs, crate boundaries, cache schemas and any
  source change outside `cranelisp-backend`;
- recapturing or changing golden CLIF output;
- the rejected shared-role integration proof and every pre-existing working-tree
  change produced by it;
- committing, publishing, pushing, archiving or closing without fresh user
  approval.

A request to cross a crate boundary, change semantics, alter independent
acceptance evidence, recapture CLIF, or absorb another failure stops the sprint
and returns to the user for a scope decision.

## Acceptance

1. The two existing `nullary_arm_beside_boxed_arm_0917` run/link cells read an
   exact marginal residual of zero.
2. Backend module evidence pins the `NoReference` lattice point, nullary
   constructor classification, both consumer thresholds and constructor-probe
   monotonicity.
3. Compiler-focused, non-exemplar golden CLIF remains byte-identical; a
   difference is a finding, not an authorized recapture.
4. The backend release gates pass with zero new warnings and the full suite has
   no new compiler failure outside the known carried set.
5. Independent review has no unresolved blocking or required finding, and QA
   recommends acceptance with exact residual risk.

Sudoku cell #21 and its generated golden are downstream observations, not
acceptance authorities. They may be measured and recorded, and a surprising
result may create separate QA intake, but neither may shape, block or reopen the
0917 compiler correction.

## Waves

| Wave | Owner | Outcome | State |
|---|---|---|---|
| 0 | `spec`, `design` | Confirm requirement and repair the bounded backend ruling for the approved scope | complete |
| 1 | `qa`, then `test` | Publish the compact evidence delta and establish the discriminating RED without duplicating adequate evidence | complete |
| 2 | `dev` (`cranelisp-backend`) | Implement the correction and module evidence; pass the backend release gate | complete; downstream generated evidence remains |
| 3 | `review` | Independently inspect the bounded delivery | complete; no backend finding, one authority-record finding repaired |
| 3R | `test` | Land the post-fix reduced compiler golden without touching exemplar evidence | complete; deterministic temporary capture added only entry 10 |
| 4 | `qa` | Judge final adequacy from focused, compiler-focused CLIF and full-suite evidence; classify exemplar observations separately | complete; recommends acceptance with no blocking or required finding |
| 5 | `sprint` + user | Accept, then close or return a bounded correction | accepted; closure not yet authorized |

## Dispatch log

| Wave | Role | Surface | Provider/model | Effort | Outcome |
|---|---|---|---|---|---|
| 0 | `spec` | runtime ownership requirement | Claude `claude-opus-5[1m]` | high | ready; no normative edit or semantic question |
| 0 | `design` | `cranelisp-backend` | Claude `claude-opus-5[1m]` | high | not ready; existing boolean constructor probe cannot express the ruled zero-field distinction |
| 0 | `design` | `cranelisp-backend` design repair | Claude `claude-opus-5[1m]` | high | ready; three-state probe and probeless scalar disposition established |
| 1 | `qa` | 0917 compact evidence delta | Claude `claude-fable-5` | xhigh | ready with blocking scope decision: expected one-frame CLIF drift |
| 1 | `qa` | authority-direction correction | Claude `claude-fable-5` | xhigh | ready; exemplar demoted to downstream observation, compiler-focused evidence allocated |
| 1 | `test` | reduced 0917 evidence | Claude `claude-opus-5[1m]` | high | RED preserved; loci repaired; compiler-focused CLIF input prepared but honestly unwired |
| 1 | `qa` | test-handoff disposition | Claude `claude-fable-5` | xhigh | ready for dev; EXCLUSIONS state accepted and stale QA locus repaired |
| 2 | `dev` | `cranelisp-backend` | Claude `claude-opus-5[1m]` | high | direct pair 2/2; backend 533/533; 42/42 safety fences; full suite 17 carries + one stale golden |
| 2 | `qa` | D4 clarification | Claude `claude-fable-5` | xhigh | ready for review; plan repaired to the owned-threshold property |
| 3 | external review | exact 0917 backend change | Codex | — | refused by host before transfer; destination not yet user-approved |
| 3 | `review` | exact 0917 backend change | primary Codex subagent | inherited | no backend finding; required exemplar-authority record finding accepted and repaired |
| 3 | `design` | finding-scoped acceptance wording | primary Codex subagent | inherited | compiler acceptance separated from downstream exemplar observation |
| 3R | `test` | post-fix compiler-focused CLIF entry | primary Codex subagent | inherited | entry 10 captured twice identically and wired; no existing golden changed |
| 4 | `qa` | final 0917 adequacy judgment | primary Codex subagent | inherited | recommends user acceptance; no blocking or required finding |

## Evidence log

Pre-implementation RED confirmed on 2026-08-31:

- `cargo nextest run --test nullary_arm_beside_boxed_arm_0917` — 0 passed,
  2 failed; both subject/control pairs measured marginal residual 4,402.

Wave-0 readiness:

- `spec` confirmed §12.3.1 with the normative runtime NFRs already requires
  timely release and nullary non-allocation; no requirement change is needed.
- `design` confirmed the correction is backend-private with no public API,
  schema or cross-crate delta, but found one missing interior decision: the
  design calls for identifying a zero-field constructor while
  `value_provenance` receives only an any-constructor boolean probe. It also
  found that scalar-bottom behavior at probeless consumers needs an explicit
  disposition. The approved scope permits confirmation but not amendment, so
  no QA or implementation work proceeds until the user decides whether to
  authorize a bounded backend-design repair.
- The user approved that bounded repair on 2026-08-31. It may resolve the
  constructor-carrier decision and scalar/probeless-consumer disposition in the
  backend design only; all original stop conditions remain.
- QA published `tests/plan/s120-0917-evidence-delta.md` and allocated no new
  independent condition. It verified that the fix necessarily removes the
  guarded protect-inc currently pinned in
  `f4_sudoku.clif::user::eliminate`. The approved scope forbids changing a
  golden, so the sprint stops before `test` or `dev` until the user decides
  whether to authorize an attributed re-baseline of exactly that frame.
- The user rejected that gate: the exemplar must not define decisions for the
  main compiler. The requirement, backend design, reduced 0917 cells and
  backend module invariants authorize and decide the correction. Exemplar and
  exemplar-derived golden evidence may observe downstream consequences only;
  QA must repair its delta before `test` or `dev` proceeds.
- QA repaired the delta: compiler acceptance now runs from requirement and
  backend design through the reduced 0917 cells, backend module invariants and
  reduced compiler-focused CLIF evidence. The exemplar and its derived golden
  are downstream observations only and cannot reopen the correction.
- `test` re-confirmed both direct cells at marginal 4,402, corrected their
  stale locus metadata and prepared a deterministic reduced CLIF input. It
  refused to wire a golden-less entry while the defect is RED; QA accepted
  that as the only truthful pre-fix state.
- `dev` implemented the backend-private correction. The direct run/link cells
  now read exact marginal zero, backend module evidence is 533/533 and the
  named UAF/provenance fences are 42/42. The full suite has the expected 17
  carried compiler REDs plus one stale generated-golden RED. Sudoku passes but
  remains a downstream observation only.
- The attempted external Codex review launch was refused before transfer
  because it was a distinct destination from the approved Claude role
  dispatches. No repository data was transferred.
- The user ruled that an external Codex hop is unnecessary when the primary
  harness is Codex. Review therefore runs as a fresh read-only role subagent in
  this harness; the external refusal remains recorded as a process finding, not
  a delivery blocker.
- Independent review found no backend correctness defect. Its one required
  finding was an authority-record conflict that still named Sudoku as an
  acceptance condition. `design` repaired §6.5 and `sprint` repaired this
  record: compiler acceptance now stands solely on the reduced direct cells,
  backend invariants and compiler-focused evidence; exemplar observations may
  create separate QA intake but cannot shape, block or reopen the correction.
- The post-fix `test` subagent re-ran the direct pair (2/2), obtained a
  temporary entry-10 dump (exit 200), and confirmed both subject/control return
  seams omit the former guarded protect-inc. The checked-in capture script can
  only rewrite the whole corpus, so `test` initially stopped before wiring or
  capture rather than touch existing goldens.
- The user identified that no new capture interface was needed: temporary
  output can prove the drift scope before only the new artifact is retained.
  `test` followed that ruling. Two isolated manifest-equivalent entry-10
  captures were byte-identical (11 frames, 731 lines, SHA-256
  `38c1a0083405841f51e1699da36fc1fdb75a6bea392124f016cd3ba7a570d7c6`),
  then only the new golden and its manifest/script wiring were added. The
  direct pair remains 2/2; entries 01–10 and f1–f3 match; no existing golden
  changed; f4 Sudoku remains the sole untouched downstream drift.
- Final `qa` found no blocking or required issue and recommends user acceptance
  of the bounded compiler correction. It reconciled the §12.3.1 trace band and
  standing test plan. Non-blocking residuals are the unchanged 11 clippy lints
  in untouched files, 17 traced compiler carries, the untouched downstream f4
  drift and cell-21 threshold form, review's maintenance-weight advisory, and
  commit-dependent `fixed=S120/<sha>` metadata.
- The user accepted the bounded FIXME 0917 correction on 2026-08-31. This
  records product acceptance only; no commit, archive, publication or formal
  sprint closure was authorized by that answer.

The final entry will record exact commands, results, changed paths, review
findings, full-suite carry comparison and residual risk.
