---
id: ACT-0965
title: Dispose the src audit residuals — stale module comment, orchestration-function budget, host-extern wiring parity
status: open
priority: advisory
from: audit
to: design
sprint: 122
filed_at: 2026-09-21
refers_to:
  - src/lib.rs
  - src/worker.rs
  - src/process_form.rs
  - src/session_v4/lifecycle.rs
  - src/CLAUDE.md
---

## Request

Provenance: the S121 `src/` whole-context assessment
([historical assessment](https://github.com/alilee/cranelisp/blob/57253cf2/audits/src-s121.md), §3 F-2 and F-3), and the S87 `src`
assessment's F-B ([historical assessment](https://github.com/alilee/cranelisp/blob/57253cf2/audits/src-s87.md)), which S109 reported
"open, unchanged" without carrying it and whose backlog filing (0407) had
already been deleted at S98. The S122 plan proposed dispositions for F-2 and
F-3 but the user has not yet ruled; F-B has never been put to the user. S121
F-1 is not here — the `SPRINT.md` scope row “src S121 F-1 — reload
realization mismatch” carries it. None of the three is approved work.

1. **F-2 — a live comment contradicts the source map.** `src/lib.rs`, directly
   under `pub(crate) mod repl;`, still says the `repl/` module was deleted and
   that save, trace and run-tests are future work; all are live. Proposed:
   `dev` (src) corrects or removes the two lines on the next scoped source-map
   edit; no behavioural test.
2. **F-3 — core orchestration exceeds the local ~100-line function budget.**
   At the S121 checkpoint: `compile_and_publish_prepared` 294 lines and
   `load_cached_module_via_linker` 215 (`src/worker.rs`),
   `process_regular_form_with_origin` 255 (`src/process_form.rs`),
   `link_by_name` 216 (`src/session_v4/lifecycle.rs`). The audit explicitly
   did **not** recommend an extraction campaign. Proposed: when planned work
   opens one of these functions, `design` (int) chooses a cohesive
   decomposition or records a truthful exception to the budget in
   `src/CLAUDE.md`.
3. **S87 F-B — JIT and `--link`/cache paths wire host externs by different
   routes with no parity guard.** `src/worker.rs` (the cache `Linker` path)
   still resolves every `DefKind::PrimitiveExtern` by `dlsym(RTLD_DEFAULT, …)`
   and silently skips a miss, while the fresh JIT uses its exported-symbol
   fallback. No misbehaviour is observed — this is not `qa` defect intake —
   but root `CLAUDE.md` §Pipeline names REPL/`--run`/`--link` divergence as
   always a defect, so a route difference with no guard is a standing
   exposure. Question: accept the two routes with a named falsifier, or ask
   `qa` to allocate one parity observation.

## Completion evidence

- Item 1: the comment is gone or current.
- Item 2: each named function, when next opened, has either a landed
  decomposition or a recorded exception; the action closes once the rule for
  "when opened" is written where `design` (int) will meet it, not after four
  refactors.
- Item 3: a user decision recorded in `design/int/int.md` — accepted residual
  with its falsifier, or a `qa`-allocated parity check.
