---
number: 0460
target: /qa
filed_by: /repl
filed_at: 2026-06-28
sprint_filed: 94
refers_to: repl/spec.md §17.15.4, tests/agent.rs (set_doc_* e2e lane), src/agent/pull.rs (set_doc_missing_symbol_reports_not_found_no_false_success, set_doc_non_userfn_refused_not_recorded)
status: open
---

# e2e coverage for the `set-doc` honest-failure contract (§17.15.4)

## Issue
S94 re-landed the Document-mode `set-doc` write surface with an honesty contract:
a docstring edit on a **missing** target (no local `Def`; includes a qualified
`mod/sym` or a re-exported import) is refused with `no such definition`, and a
docstring edit on a **non-`UserFn`** target (primitive extern / constructor /
type — a kind whose docstring would not survive source regen) is refused with a
message naming "function". In both cases the agent must NOT print the
consultative success line ("recorded …") and must leave the live docstring field
unset. I specced this as `repl/spec.md §17.15.4` this sprint.

The contract is well covered at the **unit tier** in `src/agent/pull.rs`
(`set_doc_missing_symbol_reports_not_found_no_false_success`,
`set_doc_non_userfn_refused_not_recorded`) — both green. The **e2e tier**
(`tests/agent.rs`, the `--features agent` stub lane) covers only the *positive*
round-trip and reconciliation (`set_doc_docstring_survives_session_restart`,
`set_doc_does_not_duplicate_docstring_on_restart_neg`). There is **no e2e guard
for the honest-failure paths**, so `repl/spec.md §17.15.4` currently carries no
`[Tested …]` citation.

This is a **test-coverage gap, not a defect** — the behaviour works and is
unit-tested; no failing repro is owed. The request is e2e completeness so the
spec line gains a traceable citation and the honest-failure UX is guarded at the
binary's outside surface (where the agent prose, not a raw compiler error, must
appear — U5, §16.4).

## Proposed resolution
Add two e2e tests to the `tests/agent.rs` stub lane (mirroring the existing
`set_doc_*` shape — `stub_repl` + `CRANELISP_AGENT_PROVIDER=stub`), each
asserting the negative face through the REPL:

1. **Missing target.** Stub script `tool: set-doc ghost <text>` against a session
   where `ghost` is undefined ⇒ REPL stdout contains a not-found error
   (`no such definition`) and does NOT contain "recorded"; a follow-up
   `/doc ghost` shows no docstring.
2. **Non-function target.** Stub script `tool: set-doc <primitive> <text>`
   against a bare primitive (e.g. `add-i64`) ⇒ REPL stdout surfaces the
   refusal naming "function" and does NOT contain "recorded".

Annotate both `// spec: repl/spec.md §17.15.4`. On landing, add the
`[Tested+Neg tests/agent.rs::…]` citation to the §17.15.4 heading.

## Operational implication / Context
Low priority — the unit tier already guards the seam, and the agent surface is
`#[cfg(feature = "agent")]` (absent from the default ~9s suite). A separate
default-build `.demo` is NOT appropriate: the showcase runs the agent-free
binary, so the honest-failure UX is only reachable through the stub lane in
`tests/agent.rs`. This FIXME is the e2e complement to the S94 unit coverage, not
a defect handoff.
