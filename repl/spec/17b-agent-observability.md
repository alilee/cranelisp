> [REPL specification index](index.md)

### 17.20 Silent Agent Activity Log — Pillar 4 [S90]

Pillar 4 is a **two-sink** recording surface: a compact, greppable **index** (this log, §17.20)
and a full-content **trace** (§17.21), joined by a shared `turn` key (§17.21.3). This section
specifies the **index** half: a **silent, persistent, structured** log of the agent's activity,
written to a **file**, with enough structure to **`grep`/`jq` "where did the agent struggle"** by
hand — the *recording* half of self-tuning, captured now so insight can be extracted manually (and
automated later) (`sprints/SPRINT.md §Pillar 4`; `repl-embedded-agent.md §11.6`, R5). The `/arch`
ruling makes it a **new feature-gated sibling sink** (`src/agent/log.rs` / the reserved
`telemetry.rs` slot); its content companion, the full-content trace, **re-purposes** S89's
`CRANELISP_AGENT_TRACE` from an ephemeral stderr view into a persistent file sink (§17.21). This
section owns the **`/repl` experience details** of the index — that it is silent, where it goes,
its format, and the `turn` key it shares with the trace. [S90]

#### 17.20.1 Silent — Nothing Extra in the REPL [S90]

The log is **SILENT**: writing it produces **nothing extra in the REPL** — no banner, no
"logging to …" line, no per-event echo, no change to any transcript. The human's session looks
**byte-identical** to the same session with logging off; the agent's framed prose, its `agent>`
lines, and its results are exactly as specified in §17.1–§17.19. The log is a **dev-session
artifact** (NG4, `repl-embedded-agent.md §1.3`) — it is written **off to the side**, never
surfaced, and (like the whole agent) never present in a `--link`/`--release` artifact. [S90]

#### 17.20.2 Env-Configurable Location — Sibling to `CRANELISP_AGENT_TRACE` [S90]

The log is **opt-in via an environment variable**, a sibling to the §17.10.2 agent env surface
and to `CRANELISP_AGENT_TRACE`. The normative `/repl` recommendation:

| Variable | Meaning | Default |
|---|---|---|
| `CRANELISP_AGENT_LOG` | Path to the agent activity-log file. **Set** ⇒ the agent appends one structured record per event to this file. **Unset/empty** ⇒ **no log is written** (the default — silent *and* absent). | — (unset = off) [S90] |

Rationale and rules:

- **Off by default, opt-in by setting a path.** Like every agent knob (§17.10.2), it is an
  environment variable, **not** `Cranelisp.toml` (a log path is a per-developer dev-session
  preference, not version-controlled project config). Unset ⇒ no file is created and no logging
  cost is paid. Naming it after a **path** (rather than a `=1` toggle) makes the destination
  explicit and lets each developer/session direct its own log. [S90]
- **Append, persistent, across turns and the session.** When set, each agent event appends to
  the file (the file persists; it is the durable record across the whole session, unlike the
  ephemeral trace). [S90]
- **Feature-gated; absent on the default build.** Like `CRANELISP_AGENT_TRACE` and the whole
  agent, the log exists **only** in an `--features agent` build; on a default (non-`agent`)
  build the variable is inert and **no log is ever written** (feature-OFF stays byte-identical,
  §17.9). [S90]
- **Graceful on an unwritable path.** If `CRANELISP_AGENT_LOG` names a path that cannot be
  written, the agent MUST **degrade silently** — it does **not** crash the session, and
  (consistent with §17.20.1) it does **not** spew errors into the REPL. Logging is a side
  channel; its failure never disturbs the session. [S90]

#### 17.20.3 Format — Persistent JSONL, Greppable by Hand [S90]

The log is **JSONL** — one JSON object per line, one line per agent event — chosen precisely so
`grep`/`jq` extract insight **without a query UI** (`SPRINT.md §Pillar 4`). The **`/repl`
experience requirement** is that the format carry **stable, greppable keys** for the
struggle-signal the user wants to mine — at minimum: an **event type** (e.g. a model exchange, a
pull, a **validator-repair iteration**, a submit/commit, a give-up), the **symbol** involved when
there is one, an **error class** for a repair iteration (the triggering compiler error), a
**repair-iteration count**, the **module**, and a **`turn`** correlation key (§17.21.3) — the
per-turn/exchange index shared with the full-content trace (§17.21) so each compact log line
**joins** to the trace exchange that produced it. (The exact key vocabulary the loop emits is
`/dev`-owned — it consumes the events `pull.rs`/`run_pull`/`run_submit` already produce; this
pins the *experience* requirement: the keys are stable enough that a one-line `grep`/`jq`
extracts "every repair event and its triggering symbol/error" reliably.) The acceptance is
operational: **`grep`/`jq` over the file extracts the repair events and exploration pulls with
their triggering symbols/errors** (`SPRINT.md §Pillar 4 acceptance`). [S90]

The log **stays the compact index** — it carries *metadata-only* keys (event/symbol/error_class/
iteration/module/`turn`, plus the six explanatory fields pinned in §17.20.3a) and **no content**
(no form text, no error message, no model prose). It is
the **greppable index** that tells you *where* the agent struggled; the full **content** of each
exchange lives in the companion trace sink (§17.21), joined by the shared `turn` key (§17.21.3). Do
**not** thicken the log with content fields — its grain is deliberately thin so a one-line `grep`/`jq`
stays fast and the file stays scannable. The §17.20.3a fields do **not** violate this: each is a
short **structured** value (a tool argument, an error-class enum, a cause enum, a hash, a length,
an env tag, an integer counter) — the *subject* of an event, never the *content* of the exchange,
which stays in the trace. [S90]

##### 17.20.3a Explanatory Fields — Each Derived From a Harness-Visible Event, Each Feeding a Named Metric [S109]

The §17.20.3 keys record **that** the agent struggled; the six fields below record **why the
context did or did not serve it**, so the log closes a **tuning loop** rather than only marking
trouble spots (`design/arch/fixmes/0577`). The governing constraints:

- **Derived, never narrated.** Every field is computed from state the **harness already sees** —
  a tool name and its arguments, a result's error class, the step counter, the assembled request,
  a configuration env — **not** from new model narration. Adding a field MUST NOT add a model
  round-trip, a prompt instruction, or any REPL output; it reads what the rig already holds.
- **Each field earns its place by feeding a named metric.** The acceptance coupling is the
  field→metric mapping table below: a field that feeds no metric in
  `tests/plan/agent-context-tuning.md §4` (owned by `/qa`) does not belong in the schema, and a
  metric with no feeding field cannot be computed. `/qa` checks this two-sided match at review.
- **The §17.20 contract is preserved unchanged.** Every field is written under the same
  **silent / env-opt-in / graceful / feature-gated** rules (§17.20.1, §17.20.2): no new REPL
  output, an unwritable-path failure is swallowed, and the fields are absent on a non-`agent`
  build. The keys stay **stable and greppable** so a one-line `grep`/`jq` extracts each metric.

**The six fields (normative schema additions to the §27 `LogEvent`):**

| # | Field | On event(s) | Derived from (harness-visible) |
|---|---|---|---|
| F1 | `question` — the specific thing the probe wanted to learn (e.g. `"does fn take multi-arity"`) | `pull` | a **required** `question` argument on every probe/pull tool (§17.20.3b); stamped verbatim |
| F2 | `error_class` — the compiler-error class of a **failed** probe result (today `repair`-only) | `pull` result | `classify_error` over the pull's result — the same classifier the `repair` path already runs |
| F3 | `cause` + dominant `error_class` — *why* the agent stopped (`step_budget` / `model_declined`) and the class it was looping on | `give_up` | the terminal condition the harness raises + the most-frequent `error_class` in the run-up |
| F4 | `primer_hash` + `harvest_len` — the **context-version stamp** (optionally a per-harvest-section digest) | session-start (or first `exchange`) | a hash of the assembled primer + the harvest character count — the same figures the trace header already prints |
| F5 | `scenario` — the assistance-scenario tag, stamped on **every** record | all events | the `CRANELISP_AGENT_SCENARIO` env (§17.20.3b) |
| F6 | step accounting — `step` (running counter), `steps_at_submit`, `steps_at_give_up` | `submit`, `give_up` | the harness's own step counter at the event |

**Field → metric mapping (the acceptance coupling `/qa` checks).** Each field feeds at least one
named metric in `tests/plan/agent-context-tuning.md §4` (cited, not restated — that doc is
`/qa`'s):

| Field | Feeds metric (`agent-context-tuning.md §4`) | How |
|---|---|---|
| F1 `question` | **Unresolved-question list** | dedupe + frequency-rank `question` across `pull` events → the direct per-sprint primer-gap worklist (thread D, §17.20.3c) |
| F2 `error_class` on `pull` | **Error-class histogram** | frequency of `error_class` across `repair` **and** `pull` results → the highest-value tuning targets |
| F2 (also) | **First-submit-typecheck rate** | a `submit` with no preceding failed `pull`/`repair` for the same `symbol` is a first-time-clean submit |
| F3 `cause` + dominant class | **Give-up rate + cause histogram** | `give_up` events bucketed by `cause` and dominant `error_class` |
| F4 `primer_hash` + `harvest_len` | **Comparable-runs discipline** (§5) — the key **every** metric delta is validated against | a metric delta is only valid between runs whose stamps differ ONLY in the edited artifact |
| F5 `scenario` | **Per-scenario slicing** — the tag **every** metric is computed *per* | the flat JSONL slices into a comparable dataset per assistance scenario |
| F6 step accounting | **Probes-per-submit** (§4) + the step-count facet of the **Give-up rate + cause histogram** (§4) | `pull` count per `submit` proves a context edit cut probes-per-submit (e.g. 6→1); total-steps-at-give-up sharpens the give-up analysis |

The efficiency metrics (probes-per-submit, first-submit rate) prove a context edit **worked**; the
diagnostic fields (`question`, `error_class`, give-up `cause`) say **what to edit**; the stamp
(F4) and tag (F5) make the before/after **rigorous** rather than eyeballed. [S109]

##### 17.20.3b Probe Tools Carry a `question` Argument; the Scenario Tag Is an Env [S109]

Two harness-surface requirements the F1/F5 fields depend on:

- **`question` is a required argument on every probe/pull tool.** A pull tool the agent reaches
  for (§17.2.1 enumerates the probe set) MUST accept — and the harness MUST record (F1) — a
  short `question` string naming *what the agent wanted to learn* by issuing it. A probe records
  `tool:"type"`; the `question` turns *"agent was unsure"* into *"agent was unsure **of X**"* —
  the exact context gap. This is the single highest-value tuning field, so the argument is
  **required**, not optional; a probe with no `question` is a tool-schema non-conformance. The
  wording is the agent's own (model-supplied as a tool argument) — this is the one place a field
  originates in the model, and it is an **argument to a deterministic tool call**, not narration
  bolted onto the log. [S109]
- **`CRANELISP_AGENT_SCENARIO` tags the session (F5).** An env, set per run (e.g.
  `CRANELISP_AGENT_SCENARIO=safe-dial`), whose value is stamped on **every** log record — the
  sibling of `CRANELISP_AGENT_LOG`/`CRANELISP_AGENT_TRACE` (§17.20.2), same silent/opt-in/graceful
  contract. Unset ⇒ the field is absent (or a neutral default); it never gates logging, only
  slices it. [S109]

##### 17.20.3c The Primer-Gap Loop — `question` Log Is the Per-Sprint Worklist [S109]

The F1 `question` log is a **standing signal for primer completeness** (thread D of
`design/arch/fixmes/0577`). Recurring questions across scenarios are the primer's **uncovered
rows**: a syntax/semantics question the agent had to probe for is a question the static primer
(`src/agent/primer.txt` + the `/syntax` cheatsheet, §17.17) should have pre-answered. Each sprint,
`/repl` reviews the deduped-and-ranked unresolved-question list (§4 of the `/qa` eval doc) and
folds the recurring **static** ones back into the primer — static syntax/semantics belongs in the
primer (it never changes per session); **session-dependent** facts (what is in scope, prelude
status, existing-defn style) belong in the harvest (§17.18), never the primer. This is the
`/repl`-owned half of the tuning loop; `/qa` owns the scenario suite + metric definitions
(`tests/plan/agent-context-tuning.md`). The probe set the loop mines is enumerated in §17.2.1 (the
probe *channel* — where probe traffic goes on screen); this section (§17.20.3c) is the *loop* that
reads the resulting `question` log.

> **Sequencing (user, S108, recorded for the reader).** Observability (this section, thread A)
> ships **first** — it is the substrate the eval process reads. Driving the primer to ~99%
> coverage (thread C) and running the gap loop above at scale (thread D) **defer with the scenario
> testing**: the primer is tuned from mined signal, not blind. The `question`/`error_class` fields
> are built **now**, against the `/qa` metric definitions, so the signal exists to mine later.
> [S109]

This log is the **passive recording** half only. The **automated curation/push loop** that would
read it back to curate the primer/cheat-sheet — plus the §4.7/U4 push-transparency header — is
**deferred** (`SPRINT.md §Out of scope`): capture the signal now, extract insight by hand, automate
once the pattern proves worth it. [S90]

### 17.21 Persistent Full-Content Agent Trace — `CRANELISP_AGENT_TRACE=<path>` — Pillar 4 (companion) [S90]

The §17.20 log is metadata-only — too thin, on its own, to extract insight (it names *where* the
agent struggled, not *what* it said or saw). Its companion is the **trace**: a **persistent,
full-content** transcript of every agent exchange — the assembled request and the model's
response — written the same env-path way, **joined to the log by a shared `turn` key** (§17.21.3).
Together they form **two complementary sinks**: the log is the compact **index** (grep to *find*
the trouble spot); the trace is the full **content** (read *what* was sent and returned there). [S90]

This **re-purposes** S89's `CRANELISP_AGENT_TRACE` (`src/agent/trace.rs`). Today that variable is an
**ephemeral stderr** debug view that **truncates** each form/message to ~80 chars — fine for watching
one turn live, useless as a durable record. The new normative behaviour: `CRANELISP_AGENT_TRACE` names
a **path**, and the agent appends the **full, untruncated** transcript to that file. **The stderr sink
is removed** — there is no longer any `eprintln!` trace view; the trace is **path-only**. [S90]

#### 17.21.1 The Contract — Identical to `CRANELISP_AGENT_LOG`, Full-Content Payload [S90]

`CRANELISP_AGENT_TRACE` is a **sibling sink** to `CRANELISP_AGENT_LOG` (§17.20.2) with the
**identical env-path / silent / graceful / feature-gated** contract, differing only in payload (full
content vs. compact metadata):

| Variable | Meaning | Default |
|---|---|---|
| `CRANELISP_AGENT_TRACE` | Path to the agent full-content **trace** file. **Set** ⇒ the agent appends the **full, untruncated** request/response transcript per exchange to this file. **Unset/empty** ⇒ **no trace is written** (the default). | — (unset = off) [S90] |

- **Path-only; the stderr sink is REMOVED.** `CRANELISP_AGENT_TRACE` no longer produces an
  ephemeral stderr view — there is **no `eprintln!` trace** any more. It is **set to a path** (a file
  sink) or it is off. A bare/legacy `=1`-style toggle is **not** a path and writes **no** trace
  (treated as off). This deliberately changes the variable's meaning from "stderr debug view" to
  "persistent full-content file", matching the `CRANELISP_AGENT_LOG` shape. [S90]
- **Silent — nothing extra in the REPL.** Exactly as §17.20.1: writing the trace produces **no**
  banner, no "tracing to …" line, no per-exchange echo, no transcript change. The session is
  **byte-identical** to the same session with tracing off. The trace is a **dev-session artifact**
  (NG4) — written off to the side, never surfaced, never in a `--link`/`--release` artifact. [S90]
- **Append, persistent, across turns and the session.** When set, each exchange **appends** to the
  file; it is the durable content record across the whole session (the old stderr view kept nothing). [S90]
- **Feature-gated; absent on the default build.** Like `CRANELISP_AGENT_LOG` and the whole agent, the
  trace exists **only** in an `--features agent` build; on a default build the variable is inert and
  **no trace is ever written** (feature-OFF stays byte-identical, §17.9). [S90]
- **Graceful on an unwritable path.** Exactly as §17.20.2: an unwritable `CRANELISP_AGENT_TRACE` path
  MUST **degrade silently** — never crash the session, never spew errors into the REPL. The trace is a
  side channel; its failure never disturbs the session. [S90]

#### 17.21.2 The Payload — Full, Untruncated Request/Response Transcript [S90]

Where the log records *that* an exchange happened (§17.20.3), the trace records its **full content**.
Per exchange it appends, **untruncated** (no ~80-char cap):

- the **assembled request** — the message turns sent to the model: each turn's **role** and, within
  it, the **block kinds** (system/context/primer/harvest, the user ask, prior tool results, etc.) and
  their **content** — the actual text, not a length-elided preview; and
- the **model's response** — the response **prose** and any **tool calls** it issued (pull requests,
  Build form-submits, Document edits), with their arguments.

The **content grain** of each block is owned by `/dev` (it consumes what the rig already assembles and
what the provider returns); this section pins the **experience requirement**: what reaches the file is
the **full** request/response — enough to re-read *exactly* what the agent was shown and what it
returned for the turn a §17.20 log line points at — with **nothing truncated**. [S90]

#### 17.21.3 The Shared `turn` Correlation Key — Joining Index to Content [S90]

The two sinks are **joined by a shared `turn` key** — a per-turn/exchange index, monotonic within a
session, stamped identically in both:

- the **§17.20 log** JSONL gains a **`turn`** field on every line (§17.20.3), and
- the **trace** emits a **matching per-turn marker** delimiting each exchange in the file (e.g. a
  `--- turn N ---`-style boundary carrying the same index; the exact marker text is `/dev`-owned),

so the **workflow** is: **grep the log** for a `repair`/`give_up`/struggle signal, read its `turn`,
then **scroll the trace** to that same `turn` marker to read the **full request and response** that
produced it. The `turn` index is the only coupling required between the sinks — each remains
independently writable (one may be set without the other), but when **both** are set they share the
index so the index→content join is mechanical. [S90]

### 17.22 Streaming the Agent's Terminal Answer [S107]

Before S107 the agent produced its whole answer with a single blocking completion, then rendered it
all at once: the user watched a dead prompt until the complete answer materialised (FIXME 0555).
S107 makes the terminal answer **stream** — the prose appears incrementally as the model emits it —
while keeping the rendered result **byte-identical** to the all-at-once render it replaces. This
subsection is the normative streaming behaviour + the guard that protects the goldens. It is
agent-feature-gated (`#[cfg(feature = "agent")]`); feature-off, dormant, or on a non-streaming
provider the REPL behaves exactly as before (see "Fallback" below). [S107]

**What streams — the terminal `Done` prose only (Phase-2 de-risk constraint).** Streaming applies to
the agent's **terminal answer** — the prose the turn ends on (the model's final `Done` response, the
one that produced the dead-prompt pause). **Tool-call turns are NOT streamed this sprint**: when the
agent reaches for a read (§17.2, §17.12) the pull command and its result render as today
(unframed, after the tool runs). This is an explicit, **non-foreclosed** seam — a deliberate S107
non-goal, not an architectural limit — and the streaming design MUST leave it reachable later
(streamed tool-call delta assembly is the fiddly part deferred). [S107]

**How prose streams — line-by-line as deltas arrive.** The terminal answer's **prose** MUST render
**incrementally**: as text deltas arrive from the model, each **complete prose line** is formatted
(markdown → terminal, §17.13.1) and emitted **inside the `▌` frame** the moment it is complete, so
the user sees the answer build line by line rather than after a pause. A partial trailing line MAY be
withheld until its newline arrives (line-granular streaming is sufficient — sub-line/token flicker is
not required). [S107]

**How code streams — it does not; a ```lisp fence renders formatted at fence-close.** A fenced
```lisp / ```cranelisp block **CANNOT stream token-by-token**: the deterministic pretty-printer
(§3.11, §17.13.2) needs the **whole form** to parse and align it. Therefore, while a fence is open,
its body MUST be **buffered** (not echoed raw), and the **formatted, pretty-printed, un-guttered**
block (§17.2 item 3, §17.13.2) MUST be emitted **at the closing fence**. The user sees prose stream
live, then a formatted code block appear whole when its fence closes — never a raw half-formatted
fence. (Phase-2 constraint: this is the buffer-within-fence renderer; the "stream raw then reformat"
half-measure is **rejected**.) [S107]

**The differential invariant (normative MUST — the goldens' guard).** The streamed-then-concatenated
output MUST be **byte-identical** to `render_agent_prose` (§17.13, the all-at-once renderer) over the
**same complete answer text**, with colour off. That is: streaming changes only **when** bytes reach
the screen, never **which** bytes. Concatenating everything the streaming path emits for a turn MUST
equal the single-shot render of that turn's full text — same gutter on prose lines, same un-guttered
formatted code block, same `--no-color` cleanliness (no literal escape codes, §17.13.3). This
invariant is what lets the existing non-TTY agent goldens and the §17.13.2 leaf-styling guards keep
protecting the rendered result even though the emission is now incremental; `/qa` asserts it directly
(feed a multi-delta stub answer, concatenate the streamed emission, compare to `render_agent_prose`
of the whole text). [S107]

**Fallback — a non-streaming path degrades to today's behaviour (Phase-2 de-risk constraint).** When
the agent feature is compiled out, dormant, or backed by a provider that does not stream, the answer
MUST render exactly as before — the whole terminal prose delivered as a single unit through the same
renderer — with **no** user-visible regression. Because the differential invariant holds, "one delta
carrying the whole answer" and "many deltas" produce identical bytes, so the non-streaming path is
just the one-delta case of the same contract. [S107]
