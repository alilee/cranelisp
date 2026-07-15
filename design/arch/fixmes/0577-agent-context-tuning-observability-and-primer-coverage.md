---
number: 0577
target: /repl
filed_by: /qa
filed_at: 2026-07-13
sprint_filed: 108
sprint: S110
supersedes: 0574 (folded in — this is the general agent-context-tuning finding;
  0574 was the syntax-question slice of it)
refers_to: the REPL coding-agent context (primer + harvest) and the observability
  needed to tune it across assistance scenarios — the §27 JSONL activity log
  (repl/spec.md §17.20, src/agent/log.rs), the full trace (§17, src/agent/
  trace.rs), the static primer (src/agent/primer.txt + the `syntax` cheatsheet
  src/syntax/cheatsheet.txt), and the harvest (src/agent/harvest.rs).
status: deferred
---

# Agent-context tuning: primer → ~99% coverage (thread C) + the primer-gap loop (thread D)

## Status: DEFERRED to S110

Threads **A** (§27 log enrichment — the explanatory fields off harness-visible
events) and **B** (route agent syntax/type probes off the user session onto a
private working channel) **shipped in S108/S109**. The observability substrate the
tuning loop reads therefore now exists.

This FIXME is **retained** to track the two remaining, deliberately-deferred
threads. Per the S108 user sequencing directive — *"observability first; scenario
testing later"* — threads C and D defer **with** the `/qa` scenario-testing process
(`tests/plan/agent-context-tuning.md`), because the primer is tuned from mined
signal, not blind. They are scheduled for **S110** (adjust with `/sprint` if the
scenario suite slips).

## Deferred thread C — primer to ~99% coverage

**User direction (S108):** the static language primer baked into the agent context
should cover ~99% of the agent's syntax needs. Do NOT economise primer bytes to
keep it small when the agent then burns multiple syntax-tool calls (and its whole
step budget) per session probing what a fuller primer would answer — the
per-session token+step cost dwarfs the one-time primer size.

**Home split** (corrected framing from 0574): static, spec-dependent
**syntax/semantics** (how `fn`/`defn` multi-arity works, special-form shapes,
annotation placement) belongs in the **primer** (`primer.txt` + the `syntax`
cheatsheet), because it never changes per session. **Harvest** is for
*session-dependent* facts only (which symbols are in scope, prelude status,
existing-defn style — the `agent-prelude-awareness-via-harvest-not-primer` lesson).
So: **static syntax → primer; session state → harvest.**

Settled facts to fold into the primer, with the correct multi-sig example:
- `fn` is single-arity; multi-arity is `defn`-only (**0575**).
- multi-arity `defn` clauses are type-checked independently; each needs its own
  annotations, and matching param names across clauses are no signal (**0576**).

`/repl` specifies the primer coverage target + settled-facts content + the
static/session home rule; the primer edits flow to `/dev`.

## Deferred thread D — the primer-gap loop (`/repl`-owned)

The syntax-tool `question` log (thread A.1, now shipped) is a standing signal for
primer completeness: recurring questions are uncovered primer rows, reviewed and
folded back into the primer **each sprint**. This is a **`/repl`** responsibility
(it owns the agent experience + primer), paired with `/qa`'s eval-scenario process
(`tests/plan/agent-context-tuning.md`) which defines the scenario suite + metrics.

## Dependencies / notes

- Depends on the settled semantics in **0575** (`fn` single-arity) and **0576**
  (independent arity typecheck) for the primer content in thread C.
- Guardrail (`/qa`): "scenario testing later" ≠ "metrics undefined now." The
  now-shipped thread-A fields were built against the metric definitions in
  `tests/plan/agent-context-tuning.md §4`; thread D reads those metrics to drive
  the gap loop.
- The §27 log's graceful/silent/env-opt-in contract (repl/spec.md §17.20) must be
  preserved by every future field — no new REPL output, IO failures swallowed.
