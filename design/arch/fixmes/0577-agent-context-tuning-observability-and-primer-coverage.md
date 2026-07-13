---
number: 0577
target: /repl
filed_by: /qa
filed_at: 2026-07-13
sprint_filed: 108
supersedes: 0574 (folded in — this is the general agent-context-tuning finding;
  0574 was the syntax-question slice of it)
refers_to: the REPL coding-agent context (primer + harvest) and the observability
  needed to tune it across assistance scenarios — the §27 JSONL activity log
  (repl/spec.md §17.20, src/agent/log.rs), the full trace (§17, src/agent/
  trace.rs), the static primer (src/agent/primer.txt + the `syntax` cheatsheet
  src/syntax/cheatsheet.txt), and the harvest (src/agent/harvest.rs). Observed
  post-S108 while exercising the agent on a multi-sig build (safe-dial /
  rotate-position) where it probed repeatedly and hit "too many tool steps."
status: open
---

# Agent-context tuning: enrich the §27 log so it explains WHY the context did/didn't serve the agent, and drive the primer to ~99% coverage

## Problem

The user is iteratively tuning the agent's context (primer + harvest) across a
range of assistance scenarios. The full trace (`agent_trace.txt`) has the raw
material but is too large to mine per scenario (16k lines for one session). The
compact §27 JSONL log (`log.rs`) is the right home for tuning signal — it already
records the *struggle* (events `exchange`/`pull`/`repair`/`submit`/`give_up`, keys
`symbol·module·error_class·iteration·turn·tool·ts`, joined to the trace by
`turn`). But it records **that** the agent struggled, not **why the context let
it** — so it can't yet close a tuning loop.

Concretely, in the observed session the agent probed `/type` repeatedly (does
`fn` take multi-arity? — no, 0575; do multi-arity `defn` clauses share inference?
— no, 0576), those probes **scrolled into the user's session**, and it finally hit
"too many tool steps without an answer" and never delivered the function. Every
one of those probes was a *static syntax* question the primer should have
pre-answered.

## Three coupled threads (folds in all of 0574)

### A. Log enrichment — explanatory fields off harness-visible events

Every field below is **derived from state the harness already sees** (a tool
name, a result's error class, the step counter, the composed request, a config
env) — NOT new model narration. Add to the §27 `LogEvent` schema (§17.20.3):

1. **`question` on a `pull`** (the 0574 mechanism). A probe records `tool:"type"`
   but not what the agent wanted to learn. **Require a `question` arg on the
   syntax/type probe tools** and stamp it. This is the single highest-value field:
   it turns "agent was unsure" into "agent was unsure *of X*" — the exact context
   gap. Recurring questions across scenarios = the primer's uncovered rows.
2. **`error_class` on a `pull`** (today repair-only). A probe whose result is a
   parse/type error is a probe that *failed* — the sharpest "the context didn't
   teach this form" signal. `classify_error` already computes it; attach it to the
   pull result.
3. **`give_up` cause.** Today `give_up` carries `symbol` but not why. The harness
   sees the terminal condition — annotate with `cause` (`step_budget` /
   `model_declined`) + the dominant `error_class` it was looping on. "Gave up on
   `rp` after looping 6× on AmbiguousType" is actionable; "gave up on `rp`" is not.
4. **Context-version stamp** (on `exchange` or a session-start event):
   `primer_hash` + `harvest_len` (+ optional harvest-section digest). The trace
   header already shows `primer Nch + harvest Mch`; the *index* needs it too, as
   the key that makes before/after tuning rigorous — attribute a struggle to a
   specific context version, not eyeballing.
5. **`scenario` tag** — an env (e.g. `CRANELISP_AGENT_SCENARIO=safe-dial`) stamped
   on every record, so the flat JSONL slices per assistance scenario. Turns "a
   log" into "a comparable dataset."
6. **Step accounting** — steps-per-submit and total-steps-at-give-up (harness owns
   the counter). The efficiency metric that proves a context edit worked ("primer
   change cut probes-per-submit 6→1").

Keep the enrichment in the **index** (`log.rs`); the **trace** (`trace.rs`) stays
raw content — do not bloat it.

### B. Probe output must not flood the user session (from 0574)

The agent's syntax/type probes are its private reasoning; they scroll the user's
view (`agent> /type …` echoed line after line). Route probes to a private working
channel (or summarise), leaving the user session for conclusions + landed defs.
This is a render/experience change (repl/spec.md §17), impl in src/agent.

### C. Primer to ~99% coverage — static syntax lives in the primer, NOT harvest (corrected framing from 0574)

**User direction (S108):** the static language primer baked into the agent
context should cover ~99% of the agent's syntax needs. Do NOT economise primer
bytes to keep it small when the agent then burns multiple syntax-tool calls (and
its whole step budget) per session probing what a fuller primer would answer — the
per-session token+step cost dwarfs the one-time primer size.

**Corrected home split** (my earlier 0574 draft mis-routed this): static,
spec-dependent **syntax/semantics** (how `fn`/`defn` multi-arity works, special-
form shapes, annotation placement) belongs in the **primer** (`primer.txt` + the
`syntax` cheatsheet), because it never changes per session. **Harvest** is for
*session-dependent* facts only (which symbols are in scope, prelude status,
existing-defn style — the scope of the
`agent-prelude-awareness-via-harvest-not-primer` lesson). So: **static syntax →
primer; session state → harvest.**

Fold the now-settled facts that tripped this session into the primer, with the
correct multi-sig example:
- `fn` is single-arity; multi-arity is `defn`-only (**0575**).
- multi-arity `defn` clauses are type-checked independently; each needs its own
  annotations, and matching param names across clauses are no signal (**0576**).

### D. The primer-gap loop (from 0574) — `/repl`-owned

The syntax-tool `question` log (thread A.1) is a standing signal for primer
completeness: recurring questions are uncovered primer rows, reviewed and folded
back into the primer each sprint. This is a **`/repl`** responsibility (it owns
the agent experience + primer), paired with `/qa`'s eval-scenario process
(`tests/plan/agent-context-tuning.md`) which defines the scenario suite + metrics.

## Proposed resolution

- **/repl** — spec threads A (§17.20.3 schema additions), B (§17 probe channel),
  C (primer coverage target + settled-facts content + the static/session home
  rule), D (the gap loop). Impl of A + B flows to **/dev** (src/agent/log.rs,
  trace/render, primer.txt, tool arg for `question`).
- **/dev** — implement the schema fields (all derived from harness-visible state),
  the `question` required arg on probe tools, the private probe channel, and the
  primer edits `/repl` specifies. Narrow unit tests at each emit seam
  (`error_class` on pull, `give_up` cause, context-version stamp present).
- **/qa** (me) — own the eval-scenario process + metric definitions in
  `tests/plan/agent-context-tuning.md` (companion to this FIXME): scenario suite,
  the `jq` metric queries (first-submit-typecheck rate, probes-per-submit,
  error-class + give-up histograms, unresolved-question list), and the
  comparable-runs discipline (context-version stamp).

## Sequencing (user, S108)

**Observability first; scenario testing later.** Thread **A** (the §27 log
enrichment) ships first — it is the substrate the eval process reads, so it must
exist before any scenario signal can be mined. Threads **C** (primer → 99%
content) and **D** (the gap loop) defer *with* the scenario testing, because you
tune the primer from the mined signal, not blind. Thread **B** (probe channel) is
independent UX and can go with A or defer — `/sprint`'s call.

Guardrail (`/qa`): "scenario testing later" ≠ "metrics undefined now." The
thread-A fields MUST be built against the metric definitions in
`tests/plan/agent-context-tuning.md §4` — each field earns its place by feeding a
named metric. That doc is the acceptance spec for the fields even while scenario
*runs* wait; `/qa` checks this at review.

## Notes

- **Supersedes 0574** — 0574 deleted on filing this; its three threads (probe
  channel, primer 99%, question-log loop) are threads B/C/D here, generalised from
  the syntax slice to the whole primer+harvest context.
- Depends on the settled semantics in **0575** (`fn` single-arity) and **0576**
  (independent arity typecheck) for the primer content in thread C.
- Relates to S108 Inc1 agent max_tokens / step-budget work — the step-exhaustion
  is a live example, and thread A.6/A.3 make it measurable.
- The §27 log's graceful/silent/env-opt-in contract (repl/spec.md §17.20) must be
  preserved by every new field — no new REPL output, IO failures swallowed.
