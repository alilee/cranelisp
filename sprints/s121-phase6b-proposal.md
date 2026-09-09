# Sprint 121 — user-facing completion proposal

**Status:** Approved 2026-09-09 (“yes”); Phase 6b active.
**Owner:** sprint. The user approved this completion package and the explicit
deferral of the separate stdlib `def` application API choice.

The accepted compiler gate is recorded in [SPRINT.md](SPRINT.md): 5,897 passed,
zero failed, one skipped. The Phase-6a role assessments were read-only; their
temporary report directory did not survive the session boundary. This approved
package and SPRINT's completed assessment record retain their outcomes, not a
claim of fresh execution of proposed examples or commands.

## Work grouped by surface

| Stream | Proposed result | Owners and focused evidence |
|---|---|---|
| REPL contract records and demos | Replace retired cascade/broken-symbol demonstrations with guarded redefinition; correct exact-in-scope `/search` behavior and delivered-status records; remove disproven 0832 failure status. | `spec` presents exact record-only spec deltas for user review; `test` revises demos and replays them; `qa` repairs coverage status. No normative behavior changes. |
| User documentation | One pass over live-development, CLI flags, `/syntax`, `/search` and the documentation inventory; qualify obsolete known-limitation claims using their exact evidence. | `docs`; replay changed transcripts and verify references. Consume the settled REPL contract, not a new interpretation. |
| Learning sequence | Rebaseline the live example inventory and stale RED/history claims; add one focused default-method example to the existing traits lesson. | `training`; `test` owns any expected-exit adjustment. Verify the changed lesson and replay the sequence under its established run/link requirements. |
| Standard library | Restore withheld `core.io` self-tests and current module guidance; add the explicit-import annotated-Sexp helpers already allocated by 0780. | `dev` on `stdlib/`; QA allocates the smallest adequate library/API evidence. Do not treat module conformance alone as proof of all IO combinator behaviors. |
| Exemplar | Reconcile current operational records and platform comments; settle the conflicting linked-web-server claims with a scratch link/serve check. | `dev` on `exemplar/`, with `qa`/`test` for the discriminating check. Preserve existing algorithms and accepted performance deferrals. |

Each source surface is visited once, with its records, evidence and review
consequences attached. Source/test execution remains serialized. Read-only
assessment can overlap. The REPL contract/status work supplies the shared
authority for the docs and demo edits; it does not authorize new semantics.

## Decisions and limits

- **0800 face 3 is explicitly deferred; no option selected.** Direct application of a function obtained
  through the stdlib `def` macro is an API choice. The options record is
  `stdlib/def-face-3-options.md`; its old presentation rationale must first be
  reconciled with the approved multi-definition/macro display rules. Sprint
  retains current behavior for this completion package, including its current
  diagnostic. The user approved deferral on 2026-09-09; the API decision returns
  at a future sprint's scope gate.
- `/learn`, complete macro-aware `/search`, the network lesson and the
  exemplar performance/adoption work retain their existing dispositions.
- New contradictory behavior found during replay is isolated and routed to
  QA before a fix-versus-defer decision. A stale failure label does not reopen
  compiler work. Existing green umbrella tests do not prove an unexercised
  warned scenario fixed.
- All specification wording changes still return as exact deltas to the user.
  No crate API, ABI, compiler algorithm, publication, commit or push is included.

## Audit and closure records

The scheduled [`src/` audit](../audits/src-s121.md) is complete. It finds an
unintegrated planned reload API, stale module-map commentary and oversized
orchestration functions. The reload finding requires reconciliation with
later user-approved design changes; it is not proof that the old design should
be implemented or that current behavior is defective. Recommendations are for
next-sprint user disposition, not additions to this implementation package.
The previous audit's disposition section is still a placeholder;
reconcile its R-1–R-8 decisions with actual evidence before claiming sprint
closure. Do not infer completion from the earlier plan.

## Exit condition

Return the updated user-facing artifacts, exact changed-command/example/demo
evidence, and any unresolved decisions for user acceptance. Only then propose
Phase 7 and its exact close operations. This proposal does not authorize them.
