# Agentic-REPL Track — Testing Strategy (S88 → S90)

Owned by `/qa`. Authored Sprint 88, Phase 3 (Step 3.3 — track-wide strategy).
This is the **durable record Wave 3 (S88) / S89 / S90 build against.** It defines
*how* the entire agentic-REPL track is tested — the four lanes, the deterministic
stub `CompletionModel`, and the rung → lane mapping — so that every wave writes
its tests against a fixed strategy rather than reinventing one per rung.

**Scope.** The agentic-REPL track spans rungs 0–7 of the capability ladder
(`sprints/SPRINT.md` §"Agentic capability ladder"): rungs 0–4 = the S88 read-only
Advisor MVP, rungs 5–6 = S89 (agentic Phase 2), rung 7 = S90 (Phase 3). This doc
covers all of them; the S88 Lane-A/B tests themselves are written in Wave 3 by
`/qa` alongside the `/dev` build, **not** in this step.

**Provenance.** Derives from:
- `sprints/SPRINT.md` §"Agentic capability ladder" (rungs 0–7 + per-rung lane column)
  and the §"Testing-strategy linchpin" note (R3-amended: `agent_turn` speaks rig's
  `CompletionModel` *trait* directly).
- `design/int/agent.md` (the implementable int design — §3.2 `agent_turn`, §3.4
  `AgentState.model: Box<dyn rig::completion::CompletionModel>`, §4 pull-as-visible-
  commands, §5 harvester, §6 the rig boundary, §7 primer, §9 reverse-query, §11
  testability notes, §12 S89 seams).
- `design/arch/repl-embedded-agent.md` §6 (primer + validator), §7 (architecture /
  safety — feature gating, the "no private tools" principle), §9 (phasing).
- The S88 `/qa` failing-test plan (`tests/plan/s88-test-plan.md` §"Stage B/C") — the
  agent-feature lane outline this doc generalises into a track-wide strategy.

**Authority order.** This is a `/qa` test-strategy doc. Where it drifts from the
ratified `repl-embedded-agent.md`, the `/arch` Phase-2 verdict, or `design/int/agent.md`,
those win — file FIXME `target: /arch` (cross-crate type/interface) or `target: /design`
(per-crate design gap). The spec anchors this doc cites are normative: `repl/spec.md §17`
(agent experience, `/repl`-owned) and `spec/08-modules.md §8.16` (module preamble,
`/spec`-owned).

---

## 1. The linchpin — a deterministic stub `CompletionModel`

Everything CI-testable about the agent rests on one structural fact (Principle 5,
`design/int/agent.md §1`, §6, §11): **`agent_turn` drives `rig::completion::CompletionModel`,
which is a TRAIT.** The agent loop holds a `Box<dyn rig::completion::CompletionModel>`
(`AgentState.model`, `agent.md §3.4`) and calls its completion method directly. There is
**no project-owned wrapper trait to mock** — the real Anthropic / Ollama providers and a
test stub implement the *same* rig trait. So a test constructs an `AgentState` whose
`model` is a deterministic stub, and the entire agent *logic* — classifier → request
assembly → harvest → pull → render → feed-back → validator-repair — runs with **zero
network, zero API key, zero non-determinism.**

This single seam is what makes the agent's *plumbing* a CI lane (Lane A) and confines
its *model quality* to a separate, non-blocking eval lane (Lane C). The split is the
whole strategy.

### 1.1 Stub shape — what the stub `CompletionModel` must provide

The stub is a test double implementing `rig::completion::CompletionModel` (the exact
associated types / method signature are a Phase-5/Wave-3 lookup against the pinned
`rig-core` version — `agent.md §6.4` pins the version at implementation time; do not
hardcode the trait shape here). Its required capabilities, in the vocabulary of
`agent_turn`'s loop (`agent.md §3.2`):

1. **Scripted turn responses.** The stub is constructed from an ordered script of
   responses, one consumed per `completion()` call within a turn's model↔tool loop.
   Each scripted response is one of:
   - `Done(prose)` — terminal: the agent renders prose and breaks the loop.
   - `ToolCalls(vec)` — the agent must synthesize each call as a REPL command, run it
     through `process_commands`, and re-enter the loop with the results (`agent.md §3.2`,
     §4). A scripted tool-call carries the command intent (e.g. "source of `foo`",
     "info `Num`") that `pull::synthesize_command` turns into `/source foo` etc.
   - For S89 validator tests (rung 5): a `Done(prose + proposed code)` whose code is
     scripted **broken** on the first turn and **fixed** on a later turn, so the
     stage→check→discard repair loop can be exercised deterministically.
2. **An assertable record of the request it received.** The stub captures every
   `CompletionRequest` passed to `completion()` so a test can assert *what the agent
   sent*: the primer is present, the harvested slice contains exactly the expected
   symbols/preambles, the transcript carries the prior turns, the tool-defs are exactly
   the read-only allowlist, and (negatively) that irrelevant / aged-out symbols are
   **absent**. This is how "agent knows the module" (rung 3) is verified deterministically
   — the assertion is over the *assembled request*, not over the model's answer.
3. **Optional latency / streaming behaviour = none.** The stub returns immediately and
   need not stream; streaming is a rig-layer concern (`agent.md §6.2`) covered by the
   real-provider eval lane, not the stub.

The stub lives wherever the agent lane's harness lives. Because the active test suite is
**e2e-only with no middle integration tier** (`tests/CLAUDE.md §"Two tiers, no middle"`),
the stub injection must be reachable **from the e2e surface** — i.e. the binary built
`--features agent` must expose a test-only construction path that swaps the real provider
for the stub. Two candidate mechanisms (a Wave-3 `/int` + `/qa` decision, recorded here
as the open seam):

- **(a) e2e via a test-stub provider selected by runtime config.** `agent/provider.rs`
  (`agent.md §3.1`, §6.3) already selects the provider from runtime config. Add a
  `#[cfg(feature="agent")]` *test* provider variant (e.g. `CRANELISP_AGENT_PROVIDER=stub`
  + a script file path) that builds the stub `CompletionModel` from a scripted-response
  fixture on disk. The e2e test writes the script fixture, sets the env, drives the binary
  via `repl_capture`, and asserts the transcript. This keeps Lane A **e2e** (the sanctioned
  tier) and tests the *real* dispatch/assembly/pull wiring in the *real* binary.
- **(b) unit-tier stub in `src/` (owned by `/dev`).** If a behaviour cannot be expressed
  e2e (e.g. asserting the exact `CompletionRequest` field contents — the request never
  reaches stdout), it is a `#[cfg(test)]` unit test inside `src/agent/` constructing
  `AgentState` with the stub directly and asserting against the captured request. Per
  `tests/CLAUDE.md §"Two tiers, no middle"` + `qa.md §"Testing ownership"`, these unit
  tests are **`/dev`-owned**, written alongside the implementation in the same wave —
  `/qa` does **not** author them. `/qa` specifies *that* they are needed (request-content
  assertions, harvest-ladder selection) via this strategy; `/dev` writes them.

**Resolution rule (per `tests/CLAUDE.md`): prefer (a) e2e.** Request-content assertions
that genuinely cannot surface through the binary's I/O are the legitimate (b) unit-tier
cases — and the binary SHOULD expose enough (a transcript / `--agent-trace`-style echo of
the assembled-request summary, an `/int` testability hook) that the *selection* of
harvested symbols is observable e2e. If it is not, that is a **testability gap in the
binary** → file `target: /int` per `tests/CLAUDE.md §"Two tiers, no middle"` rather than
bridging with an internal-API helper. The stub-provider-by-config mechanism (a) is the
preferred Wave-3 deliverable; it makes the bulk of Lane A genuine e2e.

---

## 2. The four lanes

| Lane | What it tests | Build | In default CI suite? | Determinism |
|---|---|---|---|---|
| **A** | Deterministic plumbing — classifier, request-assembly/harvest, pull-wiring, validator repair, preamble round-trip | `--features agent` + stub `CompletionModel` | **Separate `--features agent` lane** (not the ~9s default) | Fully deterministic — no network/key |
| **B** | Feature-off byte-identical guard | default (no `agent` feature) | **YES — default suite** | Fully deterministic |
| **C** | Model-quality eval — grounding, answer cites real symbol, proposed `(defn …)` parses/typechecks | `--features agent` + **real** provider (Anthropic key OR local Ollama) | **NO — manual/scheduled, env-gated** | Non-deterministic (model output) |
| **D** | Golden-transcript replay — full agent session as a replayable REPL script | `--features agent` + stub replaying scripted tool-calls | Runs in the `--features agent` lane (it is a Lane-A-family test) | Fully deterministic |

The default `cargo nextest run` (~9s, `tests/CLAUDE.md`) **stays agent-free**: only Lane B
runs there. Lanes A and D run in a separate `--features agent` nextest invocation (a CI
lane / `--features agent` profile, `s88-test-plan.md §"Lane mechanics"`). Lane C is never
in any automated suite.

---

## 3. Lane A — deterministic plumbing (the bulk)

The CI lane that proves the agent's *logic*. All tests `#[cfg(feature="agent")]`, in a
dedicated file (`tests/agent.rs`, gated `#![cfg(feature = "agent")]` at the top so the
whole file compiles out by default — `s88-test-plan.md §"Lane mechanics"`). E2e where the
behaviour surfaces through the binary's I/O (preferred); the residual request-content
assertions are `/dev`-owned unit tests in `src/agent/` (§1.1).

### 3.1 Classifier routing (rung 1) — much needs NO backend at all

The classifier (`classify_for_agent` / the read-loop arm, `agent.md §2`,
`repl-embedded-agent.md §5.3`) routes purely on the *parse* result + a feature cut — it
**never calls the model**. So most of this sub-lane needs no stub at all (just the
`--features agent` build). The contract: "parses as a complete form or a slash command →
REPL; unclosed → continuation; else (other parse error) → agent."

| Test (behaviour) | Asserts (feature ON) | Spec |
|---|---|---|
| form → REPL | `(add-i64 1 2)` evals (`:primitives/Int 3`), NOT the agent | `repl/spec.md §17.1` |
| slash → REPL | `/list` → the existing command, NOT the agent | `repl/spec.md §17.1` |
| prose → agent | multi-word prose ("how do I define a function") → agent arm (two bare symbols = parse error → agent) | `repl/spec.md §17.1` |
| unclosed paren → continuation | `(add-i64 1` → continuation (parens-balanced gate), NOT the agent | `repl/spec.md §17.1` |
| `/ask` escape hatch | `/ask why` (a bare word that would otherwise self-doc) → agent | `repl/spec.md §17.1` |
| **+neg: bare-atom self-doc preserved** | bare `add-i64` (no `/ask`) STILL self-documents per `repl/spec.md §4` — the agent does NOT intercept it | `repl/spec.md §17.9` (the §4 surface untouched) |

The bare-atom-self-doc row is the load-bearing **negative** guard: it proves the agent is
a *new destination for otherwise-rejected input*, not a re-router of the deterministic
surface (`repl/spec.md §17.9`, the "deterministic REPL untouched" invariant).

### 3.2 Request assembly / harvest (rungs 2–3)

This is how "agent knows the language" (rung 2 — primer) and "agent knows the
module/session" (rung 3 — harvest) are verified **deterministically**: given a constructed
session state + a user message, assert the assembled `CompletionRequest` (captured by the
stub, §1.1.2) contains the right content.

**Primer (rung 2):** assert the always-on language primer (`agent.md §7`) is present in
every request — core syntax/special-forms, the `:Type form` convention, the prelude
surface, the few-shot idioms (incl. the constrained-`(defn [Num a] …)` idiom the
acceptance walk-through needs, `agent.md §10`).

**Harvest selection (rung 3) — positive:**

| Test (behaviour) | Asserts |
|---|---|
| current-module pin | the current module's full source is always in the request (the §5.4 pin, never dropped) |
| mentioned symbols | a fn named in the message → its `/source` is harvested; a module named → its `module_preamble` + exports are harvested (`agent.md §5.2`) |
| `module_preamble` read | the harvested module slice carries the preamble text read from `SymbolTable.module_preamble` (FIXME 0428 field) |
| graceful degradation under budget | with a tiny budget, the push degrades per the §5.4 ladder — current-module-full-src survives at the floor, last-N-fns/modules drop first |

**Harvest selection — negative (+neg, the load-bearing precision guards):**

| Test (behaviour) | Asserts (ABSENCE) |
|---|---|
| irrelevant symbols excluded | a defined-but-unmentioned, low-`seq` symbol is **NOT** in the request (the ranker is selective, not a dump — `agent.md §5.1`) |
| aged-out symbols excluded | under budget pressure, an old (`seq`-stale) mention drops out of the window while a recent one stays (recency = max `seq`, `agent.md §5.2`) |
| no cross-module leakage | a symbol from a module never mentioned and not the current module is absent |

The negative harvest guards are the rung-3 equivalent of the `/list`-doesn't-show-primitives
discipline (`qa.md §"Negative coverage"`): "agent knows the module" is only proven if it
also provably does **not** carry irrelevant context. `[Tested]` without these is a gap.

### 3.3 Pull-as-visible-commands (rung 4)

The keystone (`agent.md §4`, `repl-embedded-agent.md §4.4`, `repl/spec.md §17.2`): the
stub returns a `ToolCalls` response → the agent synthesizes a REPL command string, runs it
through the **same** `process_commands` path a keystroke uses, renders it as-if-typed, and
feeds the result back into the next request.

| Test (behaviour) | Lane / mechanism | Asserts |
|---|---|---|
| pull renders as typed command | stub returns "source of `foo`" tool-call | transcript shows `/source foo` echoed as if typed, with the command's normal output following |
| pull dispatches through `process_commands` | a pull of a bad command | inherits cluster-atomic staging + normal command error (not an agent-internal one) |
| result re-enters context | stub: turn 1 pulls `/source foo`, turn 2 is `Done` | the captured turn-2 request contains the `/source foo` result fed back |
| **+neg: read-only allowlist enforced** | stub attempts a write (e.g. a `(defn …)` submission / `/sh`) | refused/unconstructable — renders "agent attempted a non-read command — refused", nothing enters the symbol table (`agent.md §4.2`, `repl/spec.md §17.3`) |

The allowlist-refuses-writes row is the consent boundary (`repl-embedded-agent.md §7.4`,
`repl/spec.md §17.3`): in read-only Advise mode the agent **cannot** synthesize a write
because the allowlist excludes them — proven negatively. This is also the rung-4 MVP
"proposed, not submitted" guard (`repl/spec.md §17.3.1`): a proposed `(defn …)` is **shown**
in the agent frame, not routed to `eval`.

### 3.4 Validator repair (rung 5, S89)

The pre-flight validator + silent-repair (U5 = silent-repair-anything, `agent.md §12`,
`repl-embedded-agent.md §6`). The stub returns **broken-then-fixed** code across turns;
the test asserts the stage→check→discard repair loop (built on Decision 44 cluster-atomic
staging — commit-on-Ok / discard-on-Err):

| Test (behaviour) | Asserts |
|---|---|
| broken generation repaired | stub turn 1 = code that fails frontend/typecheck on staging; the validator stages → checks → **discards** the broken stage and re-prompts; turn 2 = clean code that commits |
| only-clean-reaches-session | after the loop, only the clean form is in the session; the broken intermediate never committed |
| **+neg: user never sees a syntax error** | the broken intermediate is never rendered to the transcript — "the user structurally cannot see a syntax error" (the U5 silent-repair contract) |

Written in S89 (rung 5 is S89). Drafted here so the S89 `/dev` triad has the acceptance
criterion. The validator is typecheck-only dry-run, `pub(crate)`, int-internal, **no
facade/interface delta** (`agent.md §12`, the `/arch` Phase-2 ruling).

### 3.5 Preamble edit + round-trip (rungs 0 and 6)

**Rung 0 (S88 W1) — substrate:** module preambles round-trip byte-stably; 0423 green.
This is the deterministic substrate for "knows intent" and ties directly to
`spec/08-modules.md §8.16.5` (byte-stable round-trip) and the FIXME-0423 fix (the shared
regen pretty-printer path — `agent.md §5.2`, `spec/08-modules.md §8.16.5`):

| Test (behaviour) | Mode | Asserts | Spec |
|---|---|---|---|
| preamble read | `/doc <module>` | prints the module's preamble text | `spec/08-modules.md §8.16.4`, `repl/spec.md §17.5.1` |
| **+neg: absent preamble** | `/doc <module>` on a module with no preamble | clean "no preamble" message, NOT an error/empty crash | `repl/spec.md §17.5.1` |
| unchanged preamble byte-stable | regen a module whose preamble is unchanged | leading comment block byte-identical before/after (no reflow/re-wrap/re-mark) | `spec/08-modules.md §8.16.5` |
| 0423 lib-dir-relative write (rung-0 cousin) | `(mod test)` extraction | backing file at lib-dir-relative path; **+neg** no stray CWD-root file | `spec/08-modules.md §8.2.2` (the existing 0423 RED guard, `s88-test-plan.md` Stage A) |

**Rung 6 (S89) — Document mode:** the agent writes a module preamble; it round-trips; the
next session's harvester reads it back. Ties to `spec/08-modules.md §8.16` (the preamble
edit path) and the byte-stable round-trip (`§8.16.5`). The preamble write must also be
lib-dir-relative (the same 0423 fix surface — `s88-test-plan.md §"Module-preamble"`):

| Test (behaviour) | Asserts |
|---|---|
| preamble edit round-trips | the edit path writes the preamble; a subsequent `/doc <module>` reads it back; it persists across the module's backing-file regen |
| harvester reads edited preamble | after a Document-mode edit, a new turn's harvest carries the new preamble text (rung 6 → rung 3 feedback: "memory is the code") |

### 3.6 Reverse-query commands (rung-4 corollary, LLM-free — also Lane B)

`/refs` / `/tests-for` are **NOT gated** — LLM-free, default build (`agent.md §9`,
`repl/spec.md §17.6`). They grow the REPL for everyone, so they ALSO get **default-lane
(agent-free)** coverage (Lane B territory) — they are plain introspection commands. The
agent reaches for them as pull-tools, but they stand alone. (Detailed rows in
`s88-test-plan.md §"Reverse-query commands"`.) `/qa` may author these as soon as the
commands land — they are the one Stage-B sub-deliverable testable ahead of the rest of the
agent lane.

---

## 4. Lane B — feature-off guard (the default suite)

The one agent-named test family that belongs in the **agent-free default suite** because
it pins the feature-OFF contract. The default `cargo nextest run` builds **without** the
`agent` feature (no rig compiled, ~9s preserved — `agent.md §6.4`,
`repl-embedded-agent.md §7.2`). Lane B proves that with the feature off the binary is
**byte-identical to today** on every non-`/ask` input (`agent.md §2.2`, the `/arch`
byte-identical-by-construction claim).

| Test (behaviour) | Build | Asserts | Spec |
|---|---|---|---|
| `/ask` prints "not built in" | default | `/ask why` → "agent not built in (rebuild with --features agent)" | `repl/spec.md §17.1`, `repl/spec.md §0.6` (`--agent` accepted-not-error) |
| dispatch byte-identical | default | `(foo bar baz` (other parse error) → today's byte-identical parse-error display (the `Err(other)` fallback) | `repl/spec.md §17.9`, `repl/spec.md §17.1` |
| `--agent` flag accepted, ignored | default | `--agent` on a feature-off binary is accepted, not an error; session behaves exactly as today | `repl/spec.md §0.6` |
| `/refs` · `/tests-for` work agent-free | default | the reverse-query commands run in the default build (they are unconditional, `agent.md §9.3`) | `repl/spec.md §17.6` |

Lane B is also a **build guard**: it proves the default workspace compiles and the suite
passes *without rig as a dependency* — the dependency-discipline invariant
(`agent.md §6.4`). A regression that accidentally pulled `rig-core` into the default build
(e.g. a dev-dep enabling `agent`) breaks the ~9s budget and is caught here.

---

## 5. Lane C — model-quality eval (separate, NOT CI-blocking)

**Model quality is eval-lane, not unit-tested.** This is the deliberate boundary the stub
draws: the stub proves the *plumbing* (Lane A); a *real model* is the only thing that can
prove the *answer is good*, and a real model is non-deterministic, costs money/tokens, and
needs a key or a running Ollama. So model quality lives in a separate, manual/scheduled
lane that is **never in the default suite and never CI-blocking**.

- **Providers (`agent.md §6.3`):**
  - **Anthropic** — the default provider; needs an API key. (Per the `claude-api` /
    `/anthropic` discipline, the concrete model-id is a runtime-config value looked up
    against live Anthropic docs at run time, never hardcoded from memory.)
  - **Local Ollama** — the offline / free / no-key escape hatch. **This makes Lane C
    runnable offline, free, and deterministic-*enough* for a smoke lane** — a local model
    gives reproducible-enough grounding checks without a paid key or network. It is also
    the U6 privacy escape hatch and the `repl-embedded-agent.md §9` Phase-3 local-model
    goal, available *now* via rig's Ollama `CompletionModel` impl.
- **Gating:** behind `--features agent` AND a runtime presence check — the test is
  `#[ignore = "needs CRANELISP_AGENT_KEY (or local Ollama)"]` when no provider is reachable
  (the **one legitimate ignore** in the whole strategy — a backend-credential gate, not a
  spec gap — `s88-test-plan.md §"Dormant-without-key discipline"`). Run via
  `-- --ignored` on the eval-lane invocation.
- **Scored grounding assertions (not exact-match):**
  - the answer **cites the real symbol** harvested for the turn (e.g. `/ask "what does foo
    do?"` mentions the actual `foo` body / its real arity, not a hallucinated one — rung 3
    acceptance, `repl/spec.md §17`);
  - a proposed `(defn …)` **parses** (rung 2 acceptance) and, where applicable,
    **typechecks** against the session (rung 5/2 — the constrained-`Num` idiom);
  - grounding-regression for rung 7 (telemetry-driven curation must not regress grounding).

Lane C assertions are *scored* (substring/grounding checks with tolerance), never
exact-string, because model output varies run to run. A Lane C failure is a **quality
signal for human review**, not a red build.

---

## 6. Lane D — golden-transcript replay

The corollary of pull-as-visible-commands (`agent.md §4`, `repl/spec.md §17.2`, §15):
**because every agent action is a visible REPL line, every agent session is a legible,
replayable REPL script.** A recorded transcript + a stub replaying the same scripted
tool-calls = a full-session regression test. This is a Lane-A-family test (deterministic,
stub-driven, in the `--features agent` lane) but called out separately because it is a
*whole-session* guard rather than a single-seam one.

### 6.1 Record/replay shape

- **The script fixture** (the stub's input): an ordered list of scripted model responses
  (`Done` / `ToolCalls`, §1.1) — the model's half of a session. Stored as a fixture under
  `tests/fixtures/agent/` (a new agent fixtures dir; gitignored `.runs/` for outputs per
  `tests/CLAUDE.md`).
- **The golden transcript** (the expected output): the full rendered REPL transcript of a
  session — user turns + the agent's framed prose + the agent-issued commands echoed
  as-typed + their deterministic command output. Because the model half is scripted and the
  REPL half is deterministic, the *entire transcript is reproducible byte-for-byte* (modulo
  the agent prose, which is itself scripted in the stub).
- **The replay test:** drive the binary (`--features agent`, stub provider via the §1.1(a)
  config mechanism) with the recorded user inputs + the script fixture; capture the
  transcript; diff against the golden. Any drift in dispatch, pull-rendering, command
  output, or framing flips it red.

### 6.2 What it guards that the seam-tests don't

- **Pull/push interlock across turns** — a pull in turn 1 warms the harvest in turn 2
  (`agent.md §4.1`); a whole-session replay catches a regression in that interlock that a
  single-turn test misses.
- **Transcript legibility / replayability** — `repl/spec.md §17.2`/§15: the session must
  remain a script a human (or a re-run) can follow. The golden transcript IS that script;
  the test proves it stays legible.
- **Frame-vs-command rendering** — only prose is framed; commands + results use normal
  REPL roles (`agent.md §3.5`, `repl/spec.md §17.2`). The golden pins the exact framing.

---

## 7. Rung → lane mapping (cross-ref the SPRINT ladder)

This reconciles `sprints/SPRINT.md` §"Agentic capability ladder" (the "Test lane" column)
with the lanes defined here. Each rung's *primary* gating lane + any companion:

| Rung | Capability | Sprint | Gating lane(s) | This doc |
|---|---|---|---|---|
| **0** | Module preambles + clean regen (0423) | S88 W1 | **A** (deterministic round-trip) | §3.5 |
| **1** | Talk to an agent (prose→agent, round-trip, framed reply, `/ask`) | S88 W2–3 | **A** (classifier, no model) + **B** (feature-off) | §3.1, §4 |
| **2** | Agent knows the language (always-on primer [+R5 spec-grep]) | S88 W3 | **A** (primer-assembly) + **C** (answer quality) | §3.2, §5 |
| **3** | Agent knows the module/session (harvester) | S88 W3 | **A** (harvest selection **+neg**) + **C** | §3.2, §5 |
| **4** | Agent uses REPL commands as tools (pull, read-only) | S88 W3 *(end MVP)* | **A** (tool-call→command wiring) + **D** (golden transcript) | §3.3, §3.6, §6 |
| **5** | Agent submits forms (Build, confirm-gated, validator, U5 silent-repair) | **S89** | **A** (stage→check→discard repair loop) | §3.4 |
| **6** | Agent records understanding (Document mode preamble edits) | **S89** | **A** (edit + round-trip) | §3.5 |
| **7** | Self-tuning + reach (telemetry, semantic spec search, push-transparency, provider polish) | **S90** | **A** (telemetry capture) + **C** (grounding regression) | §3.2 (harvest evolution), §5 |

Lane B (feature-off) underwrites **every** rung implicitly — at every S88/S89/S90 close,
the default suite must stay agent-free and byte-identical. Lane B is the standing guard,
not tied to one rung.

---

## 8. Discipline — failing-not-ignored, spec-traced, durable

- **S88 agent tests are failing-not-ignored where they pin un-built behaviour.** Per
  `memory/feedback_failing_not_ignored.md` + `qa.md §"Failing-not-ignored discipline"`:
  Lane-A tests for rungs that have not yet been built (in the active sprint's scope) are
  written **failing, un-ignored** — including won't-compile failures when the
  `classify_for_agent` / `agent_turn` / `/refs` API doesn't exist yet. That is a valid,
  loud signal (standard TDD: write the test, watch it fail, `/dev` makes it pass). The
  **one legitimate `#[ignore]`** in the whole strategy is the Lane-C backend-credential
  gate (`#[ignore = "needs CRANELISP_AGENT_KEY (or local Ollama)"]`, §5) — a credential
  gate, not a spec gap.
- **Future-sprint rungs are PLAN rows, not written tests.** Rungs 5–6 (S89) and rung 7
  (S90) get rows in this strategy + `s88-test-plan.md`/`PLAN.md` with `[S89]`/`[S90]`; the
  tests themselves are authored in the sprint that builds them (per the
  `qa.md §"Failing-not-ignored"` table — "scheduled but not yet active → plan row, do not
  write the test yet").
- **`// spec:`-traced.** Every agent test carries a `// spec:` comment citing the normative
  section — `repl/spec.md §17` (and its subsections §17.1/§17.2/§17.3/§17.5/§17.6/§17.9 as
  appropriate) for the agent experience, and `spec/08-modules.md §8.16` (and §8.2.2 for the
  0423 write-location) for the module preamble. The spec-link linter
  (`tests/plan/spec_link_check.py`) verifies the cited anchors exist; run it before
  committing any agent-lane tests.
- **Repros join the suite for eternity.** Any defect a user-proxy (`/repl`, etc.) surfaces
  while exercising the agent gets a narrow `/qa`-authored repro in `tests/agent.rs`
  (Lane A) — failing, un-ignored, `// spec:`-traced, with a ledger row — per
  `qa.md §"Repros join the suite"`. A FIXME alone is not closure for an agent defect
  (`memory/feedback_no_fixme_with_failing_test.md`).
- **This strategy is the durable record Wave 3 / S89 / S90 build against.** The S88
  Lane-A/B tests are written in Wave 3 by `/qa` alongside the `/dev` build (not in this
  step). S89 (rungs 5–6) and S90 (rung 7) build their Lane-A tests against §3.4/§3.5/§5
  here. The plan asserts what SHOULD be tested; the test files are how it IS tested; drift
  between them is a defect resolved before phase exit (`qa.md §"Plan vs tests"`).

---

## 9. Open seams flagged to Wave 3 / `/int` / `/dev`

- **Stub-injection mechanism (§1.1).** Prefer (a) stub-provider-by-config so Lane A is
  genuine e2e. If request-content assertions (harvest selection +neg) cannot surface
  through the binary's I/O, that is a binary testability gap → file `target: /int`
  (a transcript / assembled-request echo hook) rather than bridging with an internal-API
  helper (`tests/CLAUDE.md §"Two tiers, no middle"`). The residual request-content unit
  tests are `/dev`-owned in `src/agent/`.
- **`tests/agent.rs` + `tests/fixtures/agent/`** are new test artefacts; the
  `--features agent` nextest lane + its `.runs/` gitignore entry are Wave-3 setup
  (`s88-test-plan.md §"Lane mechanics"`).
- **rig trait shape** (the stub's `impl rig::completion::CompletionModel`) is a Phase-5
  lookup against the pinned `rig-core` version (`agent.md §6.4`) — not pinned in this doc.
