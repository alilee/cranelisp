# REPL agent — assurance strategy

Owner: `qa`. Established by [test ownership](../CLAUDE.md) and reached from
[the test plan](PLAN.md#current-coverage-navigation). This document allocates
evidence for the embedded REPL agent: which conditions are observed, at which
layer, with what authority, and what each layer cannot show.

- **Required behaviour** is the [agent experience](../../repl/spec/17-embedded-agent.md),
  [language awareness](../../repl/spec/17a-agent-language-awareness.md) and
  [observability](../../repl/spec/17b-agent-observability.md) chapters, the agent
  flags in [CLI invocation](../../repl/spec/00-cli-invocation.md) §0.6, and the
  module preamble in [modules](../../spec/08-modules.md) §8.16.
- **Mechanism** is the [agent design](../../design/int/agent.md); boundary and
  feature rulings are [arch's](../../design/arch/repl-embedded-agent.md).
- Those documents govern. Where a condition here is stricter than they are, or
  contradicts them, repair the condition. A gap in one of them goes to its owner
  through `sprint`.
- Evidence policy, tiers, failing-test discipline, defect notation and
  traceability are stated once in [the test plan](PLAN.md) and
  [test conventions](../CLAUDE.md) and apply here unchanged.
- Section numbers are cited by source and test comments. Retired numbers are
  not reused.

## 1. The seam — a scripted `AgentModel`

`agent_turn` dispatches through the project-owned, object-safe `AgentModel`
membrane ([agent design](../../design/int/agent.md) §6.0, §11). Real providers
reach rig's `CompletionModel` below the membrane; the
[stub](../../src/agent/stub.rs) implements the membrane directly. A session
whose model is the stub runs classification, request assembly, harvest, pulls,
rendering, validation and the write gates with no network, no key and no
model variance.

That seam divides the evidence:

- agent **logic** is deterministic acceptance evidence (Lanes A, B and D);
- **model quality** is a diagnostic observation (Lane C) and gates nothing in
  the language or the REPL.

### 1.1 What the stub provides, and where it is reached

1. **Scripted responses.** An ordered script, one response consumed per model
   step: terminal prose, or tool calls that the agent synthesises into REPL
   commands and runs. A script can return broken code first and corrected code
   later, which is how the repair loop (§3.4) is driven.
2. **A record of each request received.** Conditions on what the agent *sent*
   are asserted over the assembled request, never over a model's answer.
3. **No latency and no provider stream.** The membrane's default
   `complete_streaming` delivers the stub's answer as one delta, so the
   streaming renderer ([agent design](../../design/int/agent.md) §14A.3) runs in
   Lane A. rig's delta stream (§6.2) is below the stub's reach.

Two layers reach the stub:

- **(a) Solution tier, preferred.** `CRANELISP_AGENT_PROVIDER=stub` with
  `CRANELISP_AGENT_STUB_SCRIPT=<path>` selects the stub in the real
  feature-enabled binary. `/context <path>` writes the same assembly the model
  receives ([agent design](../../design/int/agent.md) §3.3,
  [agent experience](../../repl/spec/17-embedded-agent.md) §17.11), so harvest
  *selection* is observable through the process.
- **(b) Module tier, `dev`-owned.** A request property that neither `/context`
  nor session output exposes is asserted beside the implementation in
  `src/agent/`, against the stub's captured request. `qa` names the conditions
  (§3.2, §3.3); `dev` writes the tests.

A request property that neither layer can observe is a testability gap for
`design` (int), not a reason for an internal-API helper in `tests/`
([two tiers](PLAN.md#strategy--two-tiers-no-middle)).

**Limits of the seam.**

- The stub does not enforce tool-use / tool-result pairing; the debug assertion
  in `assemble_request` is the guard ([agent design](../../design/int/agent.md)
  §3.2).
- The full-content trace fires only on the rig path (§28.2). A stub session
  cannot observe trace content; the activity log has no such constraint (§11).
- The rig wire path is module evidence in `src/agent/provider.rs` and
  `src/agent/request.rs`.

## 2. The lanes

| Lane | Observes | Build and execution | Authority |
|---|---|---|---|
| **A** | Deterministic agent logic (§3) | `--features agent` with the stub, through the [isolated launcher](../CLAUDE.md#the-agent-lane---features-agent--isolated-target-dir) | Acceptance |
| **B** | Feature-off behaviour and the default-build commands (§4) | default build, default suite | Acceptance |
| **C** | Live-model task completion (§5) | `--features agent` with a real provider, run by hand under an approved budget | Diagnostic observer; its harness self-check is a maintenance check |
| **D** | Composed session render (§6) | as Lane A | Acceptance |

- The default suite never compiles the agent feature; its time budget is
  stated in [root testing guidance](../../CLAUDE.md#testing).
- Feature-off cells are compiled only without the feature and feature-on cells
  only with it. Neither run observes the other's conditions, so agent
  acceptance needs the default suite **and** the launcher lane.
- The launcher runs [agent behaviour](../agent.rs) only. The feature-gated
  module tests in `src/agent/` run in neither the default suite nor the
  launcher; they need their own feature-enabled invocation against the isolated
  target directory.

## 3. Lane A — deterministic agent logic

Solution cells live in [agent behaviour](../agent.rs). Each traces to its
requirement by `// spec:`; this document does not list cell names.

### 3.1 Dispatch (rung 1)

The classifier routes on the parse result and never calls a model, so most of
these conditions need no script. The rule is
[agent experience](../../repl/spec/17-embedded-agent.md) §17.1: form count is the
discriminator and symbol resolution is never consulted
([agent design](../../design/int/agent.md) §2.2).

| Condition | Observation |
|---|---|
| Exactly one form stays in the REPL | a call, a literal and a vector evaluate normally |
| A slash command stays in the REPL | the ordinary command runs |
| **neg:** a lone symbol never reaches the agent | a known symbol self-documents; an unbound symbol and a fully qualified symbol take the ordinary unbound display or introspection ([agent experience](../../repl/spec/17-embedded-agent.md) §17.9) |
| An unclosed form continues | continuation prompt, no agent turn |
| Prose reaches the agent | multi-word prose, prose containing a contraction, mixed known and unknown words, and a non-bracket parse error all reach the agent arm |
| `/ask` forces the agent | a bare word that would otherwise self-document reaches the agent |
| No reachable provider | the dormant notice renders and no request is sent ([agent design](../../design/int/agent.md) §2.3) |

The lone-symbol negative is the load-bearing row: the agent is a destination
for input the REPL would otherwise reject, not a re-router of the deterministic
surface.

### 3.2 Request assembly and harvest (rungs 2–3)

"The agent knows the language" and "the agent knows the session" are conditions
on the assembled request.

**Primer.** Every request carries the primer, and the primer's idioms compile
([agent design](../../design/int/agent.md) §7). The primer names the `/syntax`
topics without their content (§22.4); symbols in scope reach the model through
the harvest, not the primer (§23).

**Harvest — positive.**

| Condition | Observation |
|---|---|
| Current-module pin | the pin ([agent design](../../design/int/agent.md) §5.2 block 1) is in every request and survives any budget (§5.4). The pin's admission set is an open `design` (int) question, so no condition fixes it |
| Mentions | a function named in the user text contributes its recorded source; a named module contributes its preamble and public binding names (§5.2 blocks 4–5). Mentions come from the user text only (§3.3) |
| In-scope block | every symbol in scope — current module, explicit imports, implicit prelude — appears at signature grain, fully qualified ([language awareness](../../repl/spec/17a-agent-language-awareness.md) §17.18.1) |
| Recent errored turn | the newest failed REPL turn, input and diagnostic, is in the request and survives any budget ([agent design](../../design/int/agent.md) §5.5) |
| Degradation | under a tight budget the blocks drop in the §5.4 order |

**Harvest — negative.**

| Condition | Observation (absence) |
|---|---|
| Unmentioned bodies | a defined, unmentioned function contributes no body through the mention arm. Its name and signature still appear when in scope, so absence from the whole request is **not** the condition |
| No cross-module leakage | a symbol from a module that is neither current, imported, prelude-provided nor mentioned is absent |
| Budget never elides a name | an in-scope symbol is reduced in grain, never dropped ([language awareness](../../repl/spec/17a-agent-language-awareness.md) §17.18.2) |

Without these negatives the positive rows prove only that the harvest is large.

**Nothing is allocated on mention age or on a pull entering the next harvest.**
The [architecture](../../design/arch/repl-embedded-agent.md) §4.4 withdraws the
pull-to-harvest interlock: pull results already re-enter through the transcript.
Its §4.3 retains recency as an optional int-owned heuristic. Neither warrants
an evidence allocation unless its owner adopts new behavior.

### 3.3 Pulls as private probes (rung 4)

A tool call becomes a REPL command run through the same `process_commands` path
a keystroke uses. A read pull is private
([agent experience](../../repl/spec/17-embedded-agent.md) §17.2.1,
[agent design](../../design/int/agent.md) §4.1): neither the command nor its
result scrolls the session, the result reaches the model through the transcript
with SGR stripped, and the pull is logged.

| Condition | Observation |
|---|---|
| **neg:** a probe is not echoed | no agent-input prompt and no command line for the probe appears in session output |
| Conclusions and definitions are still shown | framed prose and the definition echo appear; hiding probes hides nothing the user asked for |
| A pull is an ordinary command | a bad pull returns the ordinary command error to the model, and its log row carries the error class ([observability](../../repl/spec/17b-agent-observability.md) §17.20) |
| The result re-enters context | the next request carries the result on the transcript, paired after its tool-use turn (module tier) |
| **neg:** the read allowlist holds | a tool outside the allowlist is refused at synthesis, the refusal returns to the model, nothing executes and nothing enters the symbol table ([agent design](../../design/int/agent.md) §4.2, [agent experience](../../repl/spec/17-embedded-agent.md) §17.3) |

The allowlist is the read consent boundary. The three write tools are always
offered and route only to their gates
([agent design](../../design/int/agent.md) §15.1, §15.4, §17.2), so an
unconfirmed write never reaches eval. A definition the agent merely proposes is
shown as a definition echo and is not evaluated
([agent experience](../../repl/spec/17-embedded-agent.md) §17.3.1).

### 3.4 Validation, repair and the Build gate (rung 5)

The validator is a staging dry run that never commits: the model's text takes
the ordinary parse and expansion path, then `check_forms` against a staging
table that is always dropped, so a parse, expansion or type error is one `Err`
and any `Err` triggers repair ([agent design](../../design/int/agent.md) §16.1).
The §17.14 citations below are to the
[agent experience](../../repl/spec/17-embedded-agent.md).

| Condition | Observation |
|---|---|
| A broken generation is repaired | script: broken code, then clean code; only the clean form is in the session afterwards |
| **neg:** the user never sees the broken intermediate | it appears nowhere in session output (§17.14.3) |
| The cap ends in one give-up | an exhausted repair budget renders the give-up wording once and leaves the transcript wire-valid (§17.14.4; [agent design](../../design/int/agent.md) §16.3, §16.4) |
| **neg:** a declined submit changes nothing | the definition is absent after a decline (§17.14.2) |
| `--yes` answers consent only | under `--yes` a broken generation is still repaired before submission (§17.14.6; [agent design](../../design/int/agent.md) §20.3) |
| A malformed form does not crash the REPL | the session continues |

Consent is injected through a `ConsentReader`, so accept and decline are
scripted ([agent design](../../design/int/agent.md) §11).

### 3.5 Preamble edit + round-trip (rungs 0 and 6)

**Substrate (rung 0).** Requirements: [modules](../../spec/08-modules.md)
§8.16.4, §8.16.5 and §8.2.2.

| Condition | Observation |
|---|---|
| Preamble read | `/doc <module>` prints the module's preamble ([agent experience](../../repl/spec/17-embedded-agent.md) §17.5.1) |
| **neg:** absent preamble | `/doc <module>` on a module without one gives the no-preamble message, not an error |
| Unchanged preamble is byte-stable | regenerating a module leaves its leading comment block byte-identical |
| Inline-module extraction writes beside the library | backing file at the lib-dir-relative path, and no stray file at the working directory ([module conformance](../spec_08_modules.rs)) |

The two `/doc <module>` rows have no solution cell. They are carried as an
[unclassified lead](PLAN.md#active-allocation-and-unresolved-evidence) with
their band state; nothing further is allocated here.

**Document mode (rung 6).** The preamble and docstring write path is
[agent design](../../design/int/agent.md) §17; the experience is
[agent experience](../../repl/spec/17-embedded-agent.md) §17.15.

| Condition | Observation |
|---|---|
| A preamble edit round-trips | the accepted edit is written, reads back, and survives backing-file regeneration byte-stably |
| The harvest reads it back | a later turn's request carries the edited preamble |
| **neg:** a declined edit changes nothing | the file and the read-back are unchanged (§17.15.2) |
| `--yes` accepts the consultative gate | the edit lands without a prompt (§17.15.2a) |
| A docstring survives restart | a recorded docstring is present, once, in the next session (§17.15.3) |
| **neg:** no false "recorded" | a missing or non-function target is refused with its own reason and records nothing (§17.15.4) |

### 3.6 Default-build commands the agent pulls

`/refs`, `/tests-for`, `/syntax` and `/search` are LLM-free commands in every
build ([agent design](../../design/int/agent.md) §1). Their own requirements
carry their evidence in the default suite: reverse queries
([agent experience](../../repl/spec/17-embedded-agent.md) §17.6) in
[agent behaviour](../agent.rs), and search in [search](../search.rs).
Only their allowlist membership is an agent condition (§3.3).

### 3.7 Activity log and trace (rung 7)

Requirements: [observability](../../repl/spec/17b-agent-observability.md)
§17.20–§17.21.

| Condition | Observation |
|---|---|
| The log is silent | session output is byte-identical with and without the log configured |
| Records are stable JSONL | the documented keys, the turn correlation field joining a record to its exchange, the probe `question`, failure class, give-up cause and step accounting |
| **neg:** no content in the log | records carry no prompt, source or response content |
| An unwritable path degrades | the session continues and nothing leaks to stderr, for log and trace alike |
| **neg:** absent on the default build | the environment variables create no file |

Trace *content* is not observed in this lane (§1.1 limits). Log-driven tuning
and spec retrieval are not built ([agent design](../../design/int/agent.md)
§7), so nothing is allocated for them.

## 4. Lane B — feature-off behaviour

Feature-off is structural: `src/agent/` does not exist without the feature and
the dependencies are optional ([agent design](../../design/int/agent.md) §1,
§6.4). Lane B observes the resulting behaviour.

| Condition | Observation |
|---|---|
| `/ask` and `/context` answer "not built in" | one notice; no crash, file or evaluation ([agent experience](../../repl/spec/17-embedded-agent.md) §17.1, §17.11) |
| Dispatch is unchanged | a non-bracket parse error, a lone unbound symbol and multi-word prose each take the ordinary REPL outcome (§17.9) |
| `--agent` and `--yes` are hard errors | usage hint on stderr, exit 1, and never `unknown flag` ([CLI invocation](../../repl/spec/00-cli-invocation.md) §0.6.1, §0.6.2) |
| `--no-agent` is an accepted no-op | the session behaves as without it (§0.6.1) |
| Log and trace are absent | §3.7's last row |

Lane B does not measure build time or the dependency graph. Because its cells
compile only without the feature, a build that enabled the feature by accident
would drop them silently rather than fail them. No detector is allocated for
that; the control is the Cargo feature structure.

## 5. Lane C — live-model evaluation

A real model is the only evidence of answer quality, and it is non-deterministic,
costs money and needs a provider. It is therefore a diagnostic observer, never
part of an automated suite and never a language or REPL acceptance gate.

- Policy: [REPL-agent evaluation policy](agent-context-tuning.md).
- Current corpus, launch rules, graders, result classes and report contents:
  [runnable eval corpus and policy](s122-evidence-delta.md#runnable-eval-corpus-and-policy).
- Runner usage: [REPL-agent evals](../CLAUDE.md#repl-agent-evals).

The runner's stub self-check is evidence about the harness, not about a model.
A live run needs a separately approved model, disclosure and budget. An eval
result creates defect intake at most; a compiler or agent correction uses its
ordinary spec-traced evidence.

## 6. Lane D — composed session render

The model half of a session is scripted and the REPL half is deterministic, so
everything the user sees in an agent session is reproducible. What the user
sees is the outcome — framed prose, un-guttered pretty-printed code, and
proposed or landed definition echoes behind the agent-input prefix
([agent design](../../design/int/agent.md) §3.5, §14.2) — and never probe traffic.

One cell drives a probe step followed by a terminal answer and asserts the
render rules together. It is not a byte comparison against a stored transcript.
It guards what the seam cells cannot:

- **Composition.** Framed prose, an un-guttered fence, hidden probes and clean
  `--no-color` output hold in one session
  ([agent experience](../../repl/spec/17-embedded-agent.md) §17.2, §17.2.1,
  §17.13.3). Each rule can pass alone while the composition drifts.
- **Continuity across steps.** The probe result reaches the next step only
  through the transcript; it does not change the next harvest (§3.2).

The process harness reads output after exit, so it cannot show that a streamed
answer arrived incrementally ([harness limits](PLAN.md#strategy--two-tiers-no-middle));
that the streamed and single-shot bytes are equal is observable, and is.

## 7. Capability ladder — where each rung is evidenced

Test and source comments number agent capabilities by rung. This table is the
current definition of those numbers.

| Rung | Capability | Lanes | Section |
|---|---|---|---|
| 0 | Module preambles and clean regeneration | A | §3.5 |
| 1 | Talking to an agent: dispatch, framed reply, `/ask` | A, B | §3.1, §4 |
| 2 | The agent knows the language: primer | A, C | §3.2, §5 |
| 3 | The agent knows the session: harvest | A, C | §3.2, §5 |
| 4 | REPL commands as read tools | A, D | §3.3, §3.6, §6 |
| 5 | Submitting definitions: validator, repair, confirm gate, `--yes` | A | §3.4 |
| 6 | Recording understanding: preamble and docstring edits | A | §3.5 |
| 7 | Fluency and observability: `/syntax`, signature-grain harvest, `/search`, log and trace | A, B | §3.2, §3.6, §3.7 |

Lane B underwrites every rung: the default build stays agent-free whatever the
agent gains.
