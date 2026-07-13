# Agent Context Tuning — eval-scenario process & metrics

Owner: `/qa`. Companion to FIXME `design/arch/fixmes/0577` (the log-schema
enrichment + primer coverage, owned by `/repl`/`/dev`). This doc defines the
**measurement process** that turns the enriched §27 activity log into a signal for
tuning the agent's context (primer + harvest) across assistance scenarios. It does
NOT specify the log schema (that is 0577 → repl/spec.md §17.20) or the primer
content (0577 thread C).

Related prior art: `agent-testing-strategy.md` (S88/S89 — agent conformance
testing). This doc is distinct: not "does the agent behave correctly" but "does
the *context* let the agent succeed efficiently, and where are its gaps."

## 1. Why this exists

The agent's context is two artifacts with different lifetimes:

- **Primer** (`src/agent/primer.txt` + the `syntax` cheatsheet) — STATIC,
  spec-dependent syntax/semantics. Should cover ~99% of syntax needs (0577 C).
- **Harvest** (`src/agent/harvest.rs`) — SESSION-dependent, what's in scope
  (prelude status, stdlib symbols, existing-defn style).

Tuning either requires a feedback signal: **per scenario, which context gaps
caused inefficiency or failure.** The full trace (`agent_trace.txt`) has the raw
material but is unmineable at scale (16k lines/session). The enriched §27 JSONL
index (0577 thread A) is the substrate; this process reads it.

## 2. The tuning loop

```
1. Define / extend the scenario suite (§3), each with a scenario tag.
2. Run each scenario with logging on:
     CRANELISP_AGENT_LOG=<path>  CRANELISP_AGENT_SCENARIO=<tag>
   The log records the current context-version stamp (primer_hash + harvest_len).
3. Mine the log per scenario (§4 metrics).
4. Attribute each gap:
     static syntax/semantics  -> primer   (0577 C)
     session/in-scope facts   -> harvest  (agent-prelude-awareness-via-harvest lesson)
5. Edit primer/harvest; re-run the SAME scenarios; diff the metrics.
   The context-version stamp makes step 5 a controlled before/after, not eyeballing.
```

The loop is `/repl`-driven for the primer edits (0577 D — recurring questions are
uncovered primer rows); `/qa` owns the suite, the metrics, and the
comparable-runs discipline.

## 3. Scenario suite

The suite is **seeded from real cases, grown as they arise** — NOT invented
(tests derive from real behaviour, not speculation). Each scenario is a fixed
user-prompt sequence run against a fixed starting session, tagged for slicing.

| tag | prompt shape | what it exercises | seeded from |
|---|---|---|---|
| `safe-dial` | AoC-style: model a dial as `Position` (1-D coord) + `Rotation` (L/R sum type), build multi-sig `rotate-position` (2-arg natural + 3-arg indexed) and `fold-rotations` over a Vec | ADT `deftype` (sum + product), multi-arity `defn`, `match`, accessor use, tail recursion | S108 live session (this batch) |
| _(open)_ | _add real scenarios here as they are exercised_ | | |

Discipline: **do not pad the suite with synthetic scenarios** to look thorough.
A small suite of real assistance sessions, each replayable, beats a large
invented one. Log what the suite does NOT yet cover (no silent caps).

## 4. Metrics (jq over the enriched §27 JSONL)

All derive from harness-visible events (0577 A). Per scenario tag:

- **First-submit-typecheck rate** — of `submit` events, the fraction with no
  preceding `repair` for the same `symbol`. North-star: the primer/harvest should
  make the agent's first submit compile.
- **Probes-per-submit** — count of `pull` events (probe tools: `type`, `syntax`,
  `info`, `sig`, `source`) per `submit`. Efficiency signal; a context edit that
  works drives this down. **Step facet (F6, §17.20.3a):** `steps_at_submit` is
  reported alongside the pull count — steps-to-submit catches churn that isn't
  pull-shaped, so a context edit that cuts probes but adds other looping is
  still visible.
- **Error-class histogram** — `error_class` frequency across `repair` AND `pull`
  results (0577 A.2). Recurring classes = highest-value tuning targets.
- **Give-up rate + cause histogram** — `give_up` events per scenario, bucketed by
  `cause` (`step_budget` / `model_declined`) and dominant `error_class` (0577 A.3).
  **Step facet (F6):** `steps_at_give_up` (total steps burned before the stop)
  sharpens the analysis — a `step_budget` give-up at 8 steps and one at 40 are
  different tuning problems.
- **Unresolved-question list** — the `question` field (0577 A.1) on every `pull`,
  deduped and ranked by frequency. This is the direct primer-gap worklist handed
  to `/repl` each sprint.

**F6 disposition (S109, /qa — resolving the `/repl` flag).** There is
deliberately **no standalone step-accounting metric**: F6
(`step`/`steps_at_submit`/`steps_at_give_up`) folds into Probes-per-submit and
the Give-up histogram as the named step facets above. This closes the two-sided
field→metric audit exactly as the `repl/spec.md §17.20.3a` mapping table
records (F6 → Probes-per-submit + the give-up step facet); every §17.20.3a
field now feeds at least one named metric here, and no metric lacks a feeding
field.

Example (once 0577 lands): the S108 `safe-dial` session would show a `give_up`
with `cause:step_budget` + `error_class:AmbiguousType`, probes-per-submit high,
and unresolved-questions including "does `fn` support multi-arity" and "do
multi-arity `defn` clauses share inference" — both static-primer gaps (0575/0576).

## 5. Comparable-runs discipline

- Every mined run is tagged with its **context-version stamp** (0577 A.4). A
  metric delta is only valid between runs whose stamps differ ONLY in the edited
  artifact.
- Re-run the **same** scenario prompts verbatim; a changed prompt invalidates the
  comparison.
- Record each tuning iteration: scenario tag, before/after context version,
  metric deltas, and the primer/harvest edit made. This is the audit trail that
  the ~99% primer target (0577 C) is actually being approached, not asserted.

## 6. Handoffs

- `/repl` — the unresolved-question list (§4) is its per-sprint primer-gap
  worklist (0577 D); the eval loop (§2) is how it validates a primer edit helped.
- `/dev` — implements the log fields (0577 A) that these metrics read; the metrics
  here are the acceptance signal that the fields carry usable information.
- `/sprint` — the suite (§3) and metric deltas feed scope: a scenario class with a
  high give-up rate is a candidate increment.
