# Embedded Agent and Importable-Symbol Search — int Design

Owner: `design` (int). Subordinate to the master, `design/int/int.md`. This
document states how the Binary/int context realises the embedded LLM advisor
(`src/agent/`), its dispatch classifier, the reverse-query and `/syntax`
commands, and the default-build `/search` index.

- **Required behaviour** is normative in `repl/spec/17-embedded-agent.md`,
  `repl/spec/17a-agent-language-awareness.md` and
  `repl/spec/17b-agent-observability.md`. This document designs the mechanism
  behind that experience and does not restate it.
- **Boundary and feature rulings** are `/arch`'s
  (`design/arch/repl-embedded-agent.md`). Where this document and that boundary
  or `design/arch/bounded-contexts.md` §6 disagree, they win.
- **Section numbers are pinned** by source, test, plan and design citations.
  Retired numbers are not reused, so gaps are deliberate.

**Eval harness.** The S122 eval harness is a test-owned client of the real
agent-enabled process over ordinary REPL stdin; no Binary/int production change
is selected for it (`design/int/s122-closure.md` §6). An approved live budget
that cannot admit the current per-request output ceiling (`AGENT_MAX_TOKENS`,
64,000 in `src/agent/provider.rs`) is the trigger for a configuration follow-up.
Project-level agent configuration and further providers are open under
`sprints/actions/ACT-0960-agent-configuration-and-model-comparison.md`.

---

## 1. Bounded-context fit

- **REPL-cadence consumer, not a new state window.** `agent_turn` runs on the
  eval thread holding the same `&mut CompilerSession` the read loop drives. It
  opens no cadence, spawns no thread, and reads session state only through the
  existing introspection and symbol-table accessors.
- **No cross-crate edge.** The agent lives entirely in the binary crate.
  `rig-core`, `tokio`, `serde_json` and `futures` are optional int-private
  dependencies behind the `agent` Cargo feature (§6.4); no other crate's
  `public-api.txt` depends on them.
- **Feature-off is structural.** All of `src/agent/` is
  `#[cfg(feature = "agent")]`. Without the feature the module, the classifier
  arm, `AgentState` and every recording call do not exist; the read loop is the
  ordinary REPL. `/ask` and `/context` keep their parser entries and answer
  "agent not built in" (§2.3).
- **Unconditional companions.** `/refs`, `/tests-for` (§9), `/syntax` (§22) and
  `/search` (§25) are LLM-free default-build commands. The agent reaches them
  through the ordinary pull allowlist (§4.2); only that allowlist row is gated.

## 2. Dispatch classifier and `/ask`

The classifier sits in the `src/main.rs` read loop after the paren-balance
continuation gate and before `process_commands`. It runs only when the agent is
active (`agent_is_active`: enabled and a reachable provider). A dormant or
feature-off session never diverts input.

### 2.2 The form-count rule

`classify_for_agent` (`src/agent/mod.rs`) consults the reader the REPL already
trusts, `cranelisp_frontend::parse`; `repl/spec/17-embedded-agent.md` §17.1 is
normative.

| Input | Route |
|---|---|
| Starts with `/`, blank, or comment-only | REPL (unchanged) |
| Parse error on an unbalanced buffer | continuation (defensive) |
| Any other parse error | agent (prose) |
| Exactly one form | REPL — evaluated or introspected, resolved or not |
| Zero or two-plus forms | agent (prose) |

- **Form count is the discriminator; symbol resolution is not consulted.**
  Routing on resolution sent a lone unbound or fully qualified symbol to the
  agent instead of the self-documentation surface, and made the same line
  route differently as the session grew. Routing every `Ok` parse to eval sent
  prose to eval, because a run of bare words parses as several symbols. Neither
  rule may return.
- A contraction such as `doesn't` parses as a quote reader-macro, so prose
  like `why doesn't that typecheck?` is two-plus forms and reaches the agent.
- With no active agent a multi-form line evaluates sequentially and abandons
  on the first error.

### 2.3 `/ask` and dormancy

- `ReplCommand::Ask` and its parser arm are unconditional, so `/ask` is always
  a known command. The dispatch body is feature-split: feature-off answers
  "agent not built in"; feature-on calls `agent_turn`.
- `/ask` is a slash command and never passes through the classifier; the two
  are independent entries to `agent_turn`.
- **Opt-in twice.** The agent acts only when compiled in and enabled with a
  reachable provider (§6.4). Otherwise `agent_turn` renders the dormant notice
  in the prose frame, naming the endpoint and that harvested source excerpts
  would be transmitted. The disclosure wording is
  `repl/spec/17-embedded-agent.md` §17.8.

## 3. `src/agent/` module and `agent_turn`

### 3.1 Module shape

| File | Responsibility |
|---|---|
| `src/agent/mod.rs` | `classify_for_agent`, `agent_turn`, `assemble_request`, `record_repl_turn`. |
| `src/agent/types.rs` | The provider-neutral turn vocabulary, the object-safe `AgentModel` membrane (§6.0), `AgentState` and the recent-turn ring. No rig type crosses it. |
| `src/agent/provider.rs` | Runtime provider selection, the rig-backed `AgentModel` implementation, dormancy reporting and the current-thread `block_on` bridge. The only holder of a concrete rig `CompletionModel`. |
| `src/agent/request.rs` | Translation between the neutral vocabulary and rig's request, message and tool-call types. |
| `src/agent/stub.rs` | The scripted, request-capturing `AgentModel` used by tests (§11). |
| `src/agent/harvest.rs` | Push-context assembly under budget (§5, §23). |
| `src/agent/primer.rs` | The always-on primer (§7), embedding `src/agent/primer.txt`. |
| `src/agent/pull.rs` | Pull synthesis, the read allowlist, and the gated write arms (§4, §15–§17, §20). |
| `src/agent/render.rs` | The streaming prose renderer and the agent-input prefix (§14). |
| `src/agent/log.rs`, `src/agent/trace.rs`, `src/agent/sink.rs` | The activity log, full-content trace and their shared append helper (§27–§28). |

### 3.2 `agent_turn` — the model and tool loop

```text
agent_turn(text):
  dormant? -> render dormant notice; return                         (§2.3)
  record user turn; reset per-turn give-up bookkeeping
  for step in 1..=MAX_TURN_ITERATIONS (8):
    state.current_turn = step                                        (§28.2)
    req = assemble_request(text)                                     (§3.3)
    log exchange
    resp = complete_streaming(req, sink -> StreamingRenderer)        (§6.0, §14A.3)
    Done(prose)      -> record assistant turn; return               (already rendered live)
    ToolCalls(calls) -> record tool_use turn; for each call run_pull (§4, §15–§17)
                        and record its result on the transcript
  budget exhausted -> give-up notice (a failed submit's notice when nothing committed)
```

- Tool results re-enter the model only through the transcript; there is no
  separate feedback channel.
- `assemble_request` asserts in debug builds that the transcript is wire-valid:
  every tool result follows the assistant turn carrying its tool call. The stub
  does not enforce this pairing, so this assertion is the guard.
- Interrupting a turn returns to the prompt. A read-only turn mutates nothing;
  a write commits only through the ordinary eval path (§15.3).

### 3.3 Request assembly

`assemble_request` builds one neutral `AgentRequest`: the primer (§7), the
harvest for mentions tokenised from the user text (§5), the whole session
transcript, the tool definitions (§4.2) and the user turn. It also carries the
correlation turn id (§28.2). The transcript is sent whole; the budget of §5.4
governs only the harvest. `/context <path>` writes the same assembly, so the
debug dump and the transmitted request cannot diverge
(`repl/spec/17-embedded-agent.md` §17.11).

### 3.4 Agent state

`CompilerSession.agent: Option<AgentState>` exists only with the feature and is
built by `enable_agent` at REPL start-up, before the read loop. `AgentState`
holds the transcript, the `Box<dyn AgentModel>` model handle (`None` when
dormant), the provider label, the recent-turn ring (§5.5), the `--yes`
consent bits (§20), per-turn give-up bookkeeping, the failed-probe error-class
tally for the log, and the current turn id. It is never serialised: durable
memory is the code, its docstrings and preambles (§17).

### 3.5 Output framing

- Read probes do not render at all (§4.1).
- Definitions the agent proposes or submits render unframed, as normal REPL
  definition echoes behind the agent-input prefix (§14.2).
- The agent's prose renders in the reserved gutter frame through the one
  styling seam (`design/int/terminal-styling.md`); `--no-color` and non-TTY
  output degrade byte-clean.

## 4. Pull-as-commands

### 4.1 Mechanism

- The model's tools are REPL commands. `synthesize_command` turns a tool call
  into a command string; `run_pull` runs it through `process_commands`, the
  path a keystroke uses. There is no private tool registry.
- **Probes are private.** Per `repl/spec/17-embedded-agent.md` §17.2.1, a read
  pull runs against a throwaway sink: neither the command nor its result
  scrolls the user session. Its output is stripped of SGR before reaching the
  model, and the pull is recorded in the log (§27) with the model's `question`
  and any failure class.
- The user sees the agent's conclusions (streamed prose) and its landed or
  proposed definitions.

### 4.2 The tool mapping and the read allowlist

- `ALLOWLIST` in `src/agent/pull.rs` is data: `source`, `sexp`, `info`, `sig`,
  `doc`, `type`, `imports`, `exports`, `list`, `refs`, `tests-for`, `syntax` and
  `search`. `tool_defs()` offers exactly these plus the three gated write tools
  (§15.1, §17.2).
- **The allowlist is the read consent boundary.** Any other name, including
  `sh`, `context` and unknown tools, is refused at synthesis and the refusal is
  fed back; nothing executes.
- A read can never reach eval: a `Compile` or `Quit` result from a pull fails
  closed.

## 5. Harvester

### 5.1 Push the shape, pull the bodies

`harvest_context` reads live tables and introspection every turn. It keeps no
index and no copy store, so there is nothing to invalidate. The budget is
`DEFAULT_TOKEN_BUDGET` (4,000) converted to characters; it is a tuning value,
not architecture.

### 5.2 The push blocks

1. **Current-module pin.** The module preamble, then each admitted binding's
   recorded authored source (`push_module_full_source`). Admitted bindings are
   callables, overload groups and macros that are not internal listing entries.
2. **Recent REPL turns** (§5.5).
3. **In-scope symbols** at signature grain (§23).
4. **Mentioned functions** — the recorded source of each mentioned function.
5. **Mentioned modules** — the preamble and the names of public bindings.

A mention is a token of the user text that names a module table or passes
`symbol_is_mentionable`. Mentions keep text order; there is no scoring pass.

**Open design questions** (recorded, not ruled):

- The pin is narrower than "full source": type, trait and impl definitions are
  not admitted, and a binding with no recorded source contributes nothing.
- The mentioned-module export list is `public_symbols()` names, not the
  `/exports` surface, which resolves public name candidates and filters
  internal entries.
- An import-graph neighbourhood signal is designed but not built.

### 5.4 The degradation ladder

Blocks consume the budget in push order, so an earlier block always outlives a
later one. Keep-priority, longest-kept first:

```text
current-module pin                  never dropped
most recent errored turn (§5.5)     never dropped
older errored turns                 newest first
green recent turns                  first recent-turn entries to drop
in-scope block (§23)                degrades grain per symbol; the list is never truncated
mentioned functions
mentioned modules                   preamble+exports -> exports only -> dropped
```

### 5.5 Recent-errored-turn feed

A failed definition never commits, so committed state cannot tell the agent
what just failed. The ring supplies that missing signal.

1. **Entry.** One per REPL eval turn (not slash commands, not agent turns): the
   submitted input and the exact string the user saw, either the rendered
   result or the `Error:` diagnostic. The ring holds `TURN_RING_CAP` (8)
   entries, enough for a failure to survive a few follow-up pokes before the
   question.
2. **Feed.** `record_repl_turn` is called once from the read loop's per-turn
   render site with the strings already produced for display. It is not a
   second transcript: rustyline history is input-only and TTY-only and must not
   be used.
3. **Harvest.** `push_recent_turns_block` emits errored turns first, then green
   turns, each newest first. The newest errored turn is pinned even past the
   budget; green turns are kept only to resolve deixis such as "that".
4. **Gating.** The ring lives on `AgentState`, which `enable_agent` installs
   at every feature-on REPL start-up, dormant or not, so recording starts with
   the first turn. With no state, `record_repl_turn` is a no-op. Feature-off,
   neither the ring nor the call exists.

## 6. LLM completion layer

### 6.0 The `AgentModel` membrane

- rig's `CompletionModel` (`rig_core::completion::CompletionModel`) is the
  provider wire boundary. It is dyn-incompatible (associated types, a `Clone`
  bound, async methods), so `Box<dyn CompletionModel>` does not compile. Do not
  try to simplify back to it.
- `agent_turn` dispatches through the object-safe `AgentModel` trait in
  `src/agent/types.rs`: `complete`, plus `complete_streaming`, whose default
  delegates to `complete` and emits the whole answer as one delta. The stub and
  any non-streaming provider therefore work unchanged.
- The membrane re-implements no protocol. It exists because runtime provider
  selection and the zero-network stub both need a boxed trait object.
- rig's higher-level `Agent`, RAG and tool-execution framework are deliberately
  unused: they would duplicate `agent_turn`, the harvester and the rule that the
  agent's capability surface is the REPL command set.

### 6.1 What `agent_turn` speaks

`src/agent/request.rs` maps the neutral request to rig's: primer to the
preamble, harvest to additional context, transcript to message history, tool
definitions to rig tool definitions, and the user turn to the prompt. Every
request carries `max_tokens = AGENT_MAX_TOKENS`: Anthropic rejects a request
without it. This output budget is distinct from the harvest input budget
(§5.4).

### 6.2 Streaming and tool use

- `RigModel::complete_streaming` drives rig's stream inside one `block_on` and
  forwards only text deltas to the sink. Tool-call and reasoning deltas
  accumulate into rig's aggregated choice, which the shared `lower_response`
  lowers exactly as `complete` does; a tool-call turn therefore streams no
  prose yet returns the correct response.
- Tool calls surface in the response and map one-to-one to REPL commands (§4).
  No executable tool is ever registered with rig.

### 6.3 Provider selection

`src/agent/provider.rs` builds the configured provider at session start from
environment configuration (`CRANELISP_AGENT_PROVIDER`, `CRANELISP_AGENT_MODEL`,
endpoint and key; `repl/spec/17-embedded-agent.md` §17.10):

- Anthropic is the default and requires a key; the model id is configuration,
  never a compiled-in constant.
- Ollama is the local, key-free provider, so zero-transmission operation is
  available.
- A deterministic stub serves tests.

A further rig provider is one construction arm in `provider.rs`, not an
`agent_turn` change.

### 6.4 Dependency discipline and opt-in twice

- `rig-core`, `tokio`, `serde_json` and `futures` are optional and enabled only
  by the `agent` feature, which is in no default set. Ordinary builds and the
  default suite never compile rig; agent tests run in their own feature lane.
- `rig-core` drops its default features and enables `reqwest` plus
  `native-tls`; rustls pulls a heavy C TLS backend and is rejected. rig
  providers are not individually feature-gated.
- `tokio` supplies a current-thread runtime only; each model step is one
  `block_on`.
- **Opt-in twice:** compiled in, and enabled with a reachable provider (an
  Anthropic key, or a reachable local Ollama). A published binary may include
  the feature and stays dormant until configured.

### 6.5 Coupling cost (accepted)

Only `request.rs` and `provider.rs` depend on rig's API. Replacing rig would
touch those two files, never `agent_turn`, and never a facade.

## 7. Always-on primer

- The model has no training data for Cranelisp, so a curated primer is always
  sent: core syntax and special forms, the `:Type` annotation convention, the
  prelude surface, and few-shot idioms.
- It is a version-controlled text asset, `src/agent/primer.txt`, embedded by
  `src/agent/primer.rs`, and curated by hand. Its few-shot idioms must compile.
- It names the `/syntax` topics but not their content (§22.4). Current prelude and
  library definitions reach the model through the harvest (§23); the primer
  describes a typical prelude surface.
- Spec retrieval (a `/spec` grep pull) is not built and is not in the
  allowlist; the primer and harvest carry grounding.

## 9. Reverse-query commands `/refs` and `/tests-for`

LLM-free, unconditional commands (`repl/spec/17-embedded-agent.md` §17.6):
`/refs <sym>` lists definitions whose bodies reference a symbol; `/tests-for`
restricts that to test functions.

### 9.2 Mechanism — on-demand, no maintained index

`handle_refs` and `handle_tests_for` (`src/repl/commands.rs`) share one
collector. It takes the deduplicated union of:

- **callee edges** — `ReverseIndex::build(...).callers_of(target)` over the
  serialised `callees` (skipped for `/tests-for`), which covers cache-restored
  modules with no introspection; and
- **a source token scan** — `scan_referers` (`src/repl/search.rs`) over each
  callable's recorded introspection source, which also finds non-callable
  referents such as type names in annotations.

Both feeds are recomputed per invocation from live state; there is no reverse
index to invalidate. Promote to an index only if measured scan latency
warrants it.

### 9.3 Wiring

`ReplCommand::Refs` and `ReplCommand::TestsFor` are unconditional parser and
dispatch arms in `src/repl/mod.rs`; both are allowlisted pulls (§4.2).

## 10. One turn, end to end

`/ask "how do I define a constrained function over Num?"`:

1. `/ask` dispatches to `agent_turn` (§2.3).
2. The request carries the primer's constrained-function idiom and the
   session's pinned module, recent turns and in-scope `Num` symbols (§3.3, §5).
3. The model may probe (`sig`, `info`) privately (§4.1); results return through
   the transcript.
4. The answer streams into the prose frame (§14A.3). A proposed definition is
   shown, or submitted only through the validated, consent-gated Build arm
   (§15–§16).

## 11. Testability seams

- **The membrane is the seam.** `src/agent/stub.rs` implements `AgentModel`
  with scripted responses and captures every `AgentRequest`, so the loop,
  pulls, repair and write gates run with no network and tests can assert what
  was sent.
- **Consent is injected.** The write gates read consent through a
  `ConsentReader`, so accept and decline paths are scripted.
- `classify_for_agent`, `validate_forms_dry_run`, `handle_syntax`, the search
  message functions (§25.10) and the renderer are pure or near-pure and test
  at their seams.
- The trace fires only on the rig path (§28.2), so a trace-file test needs a
  rig-backed or emitting model; the log fires from `agent_turn` and `pull.rs`
  and has no such constraint.
- The QA strategy and evidence allocation live in
  `tests/plan/agent-testing-strategy.md`.

## 12. Extension seams and open obligations

- **Mode offering.** `submit`, `set-preamble` and `set-doc` are always offered
  and always gated (§15.1). Turn-level mode selection would change the offer,
  not the gates.
- **Harvest** open questions are §5.2's.
- **Search completeness** is open: a full semantic index through the normal
  compiler, covering macros, replaces the interim design of §25
  (`sprints/actions/ACT-0952-complete-semantic-search-indexing.md`).
- **Configuration and providers** are open under ACT-0960 (see the header).

## 14. Agent output rendering (`src/agent/render.rs`)

All agent rendering lives in `render.rs`, inside the feature gate. It consumes
`src/pretty.rs` and the styling seam and never changes them.

### 14.1 Shape

- `StreamingRenderer` is the one render core (§14A.3).
- `render_agent_prose` is a test-only single-shot drive of that renderer: the
  comparand for the streaming invariant.
- `markdown_to_terminal` formats prose runs; `classify_fence_line` is the one
  fence classifier.

### 14.2 Agent-input prefix

`agent_input_prefix()` emits the `agent>` token (the agent-gutter role over
the prompt role) before every echoed Build or Document proposal. It is distinct
from the human prompt and from the prose gutter, and degrades to plain
`agent>` without colour.

### 14.3 Markdown inside the frame

A small, bounded formatter handles the markdown the model emits (headings,
lists, emphasis and inline code) using the existing style palette. The
formatted prose is then guttered, so formatting stays inside the frame.

### 14.4 Fence recognition

Fences with a `lisp` or `cranelisp` info-string are code runs; any other fence
stays prose and renders as a literal block.

### 14.5 Code fences reuse the pretty-printer

A lisp fence renders through `crate::pretty::pretty_print_str`, the printer
behind `/sexp` and `/source`, so layout fixes such as the aligned `let`/`match`
pairs (`design/int/terminal-styling.md` §3) apply to agent code with no
agent-side change.

### 14.6 Style once, at the leaf

Colour is one process-wide decision, `style::is_color_enabled()`, and styling
reaches SGR only through the styling seam. Each run is styled exactly once at
its leaf; the frame only prefixes gutters and never re-styles or re-escapes its
body. No colour-mode or writer-target parameter is added to any printer. Text
fed back to the model is stripped of SGR (`style::strip_ansi`).

### 14A.2 Code fences are un-guttered

Prose runs are guttered (`push_prose_run`); lisp runs are emitted without a
gutter (`push_lisp_block`). The code bytes on screen are the copyable bytes and
are byte-identical, colour-off, to `pretty_print_str` output
(`repl/spec/17-embedded-agent.md` §17.13.2). Empty or whitespace-only prose
runs emit nothing, so no stray gutter line appears.

### 14A.3 Streaming the terminal answer

- `StreamingRenderer` consumes raw markdown deltas. It is line-buffered: a
  complete prose line renders immediately; a lisp fence buffers until it closes
  and then flushes whole; `finish` flushes a partial line or an unterminated
  fence.
- **Byte-identity is structural.** Streaming and single-shot rendering use the
  same leaves and the same fence classifier, so the concatenated stream equals
  the single-shot render for any delta split
  (`repl/spec/17b-agent-observability.md` §17.22).
- Line granularity is what preserves that invariant; token-level flushing
  would break it for partially formatted spans.
- `agent_turn` creates one renderer per model step and never re-renders the
  `Done` prose after streaming it. The trace and log record the accumulated
  answer, not individual deltas.

## 15. Build mode — the confirm-gated write arm

### 15.1 One widening at the `run_pull` head

`run_pull` routes `submit` to `run_submit` and the Document tools to
`run_document_edit` (§17.2) before the read path. The read `ALLOWLIST` is
unchanged and still refuses everything else. `submit` is always offered but
always gated; the gate, not the offer, is the consent boundary.

### 15.2 The confirm gate

`run_submit` is the single code-write site:

1. validate and silently repair the proposed form (§16); on give-up, feed an
   honest not-submitted result back and render nothing broken;
2. render the clean form behind the agent-input prefix — always, even under
   `--yes`;
3. capture consent through the `ConsentReader`: a synchronous prompt at the
   REPL cadence, or the `--yes` auto-answer (§20.2);
4. on decline, feed "declined" back and leave the session unchanged; on accept,
   submit (§15.3).

Gate wording is `repl/spec/17-embedded-agent.md` §17.14.

### 15.3 Submission re-enters the ordinary eval path

On accept, `run_submit` drives `process_commands` and `eval` exactly as the
read loop does, then regenerates the backing file on a successful definition.
It inherits cluster-atomic staging (commit on `Ok`, discard on `Err`), error
recovery and persistence. There is no second eval entry or submit path.

### 15.4 Read-only by default

A write is reachable only past a gate. The read allowlist excludes writes; the
three write tools route only to their gates; an unconfirmed write never reaches
eval.

## 16. Pre-flight validator and silent repair

### 16.1 The dry run

`validate_forms_dry_run` (`src/worker.rs`) builds a fresh staging table, runs
`check_forms` through the containment helper (§24.2) against a cluster view,
and always drops staging. Its twin, `process_cluster_with_staging`, commits on
`Ok`; the validator omits the commit. `validate_one_form` (`src/agent/pull.rs`)
builds the model's text through the ordinary parse and expansion path, so a
parse, expansion or type error is one `Err`. There is no error-classification
branch: any `Err` triggers repair.

### 16.2 The repair loop

`validate_and_repair` runs inside `run_submit`, before the echo and the gate.
On `Err` it records a hidden repair exchange on the transcript, re-asks the
same `AgentModel` with the compiler error, and extracts the next proposal.
Nothing from a failed attempt is written to stdout; rendering happens only
after a clean form returns. The validation and the later real commit each
typecheck once; that duplication is the accepted cost of reusing the ordinary
commit path unchanged.

### 16.3 The cap

`MAX_REPAIR_ITERATIONS` is 3, a tuning value.

### 16.4 Give-up

On exhaustion the agent never submits broken code and never shows a raw
compiler error. The model receives an honest abort; at true turn-end, if no
submit committed, the user sees one give-up line
(`repl/spec/17-embedded-agent.md` §17.14.4).

### 16.5 Testability

A stub scripted broken-then-fixed drives the loop deterministically; see §11.

## 17. Document mode — preamble and docstring edits

### 17.1 The preamble write path

`save::apply_preamble_edit` sets the module's `module_preamble` field directly
and the session regenerates the backing file. Section 0 of the regenerated
source re-emits the field byte-stably (`design/int/session-persistence.md`
§1.3). The agent supplies stripped prose; `/doc <module>` reads the same field.

### 17.2 The consultative gate

`set-preamble <module> <text>` and `set-doc <symbol> <text>` route to
`run_document_edit`. It renders the exact canonical `;;` block or docstring it
proposes, asks the consultative question, and on accept applies the edit and
regenerates. `apply_docstring_edit` sets the live docstring, which regeneration
treats as authoritative (`design/int/session-persistence.md` §11.3a). The tool
name is the discriminator between the Build confirm gate and this gate; no
content sniffing is involved. A missing target is refused, not reported as
recorded (`repl/spec/17-embedded-agent.md` §17.15.4).

### 17.3 Read-back

A regenerated preamble or docstring round-trips through save and reload. The
next session's harvest reads the preamble from the same field (§5.2), so the
write needs no new harvest code.

## 20. `--yes` autonomous consent

`--yes` (`-y`) auto-answers the existing write gates. It relocates, widens and
removes nothing, and it never skips validation.

### 20.1 Flag and threading

`parse_args` accepts `--yes`/`-y` beside `--agent` in every build; without the
feature it is an accepted no-op. The resolved value is meaningful only with an
enabled agent in REPL mode. It is threaded into `enable_agent` and stored as
`AgentState.auto_accept`; it is never persisted.

### 20.2 Only the consent capture changes

`agent_auto_accept()` is read only at the consent step of `run_submit` and
`run_document_edit`. The proposed form or edit is always rendered, and the
accepted path is the same call either way. One flag covers both gates.

### 20.3 The validation floor

`auto_accept` is unreachable from `validate_and_repair` and
`validate_forms_dry_run`: they take no such parameter and read no such field.
Consent runs only after validation has returned a clean form. Threading the
flag into validation would let an autonomous agent submit unchecked code and
is a defect.

### 20.4 First-use notice

The first auto-accepted write of either kind in a session fires a one-time
notice (`fire_auto_accept_notice_once`, guarded by
`AgentState.auto_accept_notice_shown`) saying writes proceed without prompting
and the validator still gates correctness. Wording is
`repl/spec/17-embedded-agent.md` §17.16.

## 22. `/syntax` cheat-sheet

The cheat-sheet is a default-build command for humans and the agent. Content
is `/docs`-owned (`user/syntax-cheatsheet-plan.md`); the experience is
`repl/spec/17a-agent-language-awareness.md` §17.17.

### 22.1 Asset and parser

- The asset is `src/syntax/cheatsheet.txt`, embedded by `src/syntax.rs`. Both
  are unconditional.
- Topics are delimited by `=== topic: <name> ===` lines and keep authored
  order. The parsed sheet is a lazily built static.

### 22.2 Command

`handle_syntax` returns plain text with no style role: the bare form lists the
topic names; `/syntax <topic>` returns the topic as authored; an unknown topic
re-lists the index with a note. Topic content is not pretty-printed, because
its templates contain metavariables and do not parse. `/syntax` output is
deterministic REPL output, not agent prose.

### 22.3 Pull

`syntax` is one allowlist row (§4.2).

### 22.4 Primer topic names

The primer names the `/syntax` topics but not their content. The list is
maintained by hand and must match the asset's topics. Deriving it from the
parsed asset at build time would remove that obligation.

## 23. In-scope harvest at signature grain

### 23.1 The in-scope block

`push_in_scope_block` emits `== in scope ==` after the pin and the recent-turn
block. Each entry is the bare-symbol display a human gets by typing the name:
`format_def_entry` (`src/repl/format.rs`) rendered in the defining module,
with the docstring when present. Feeders apply in shadowing order, and a name
already emitted is skipped:

1. **Current-module definitions** — the current table's bindings, excluding
   internal listing entries and special forms.
2. **Explicit imports** — name candidates whose source module is elsewhere,
   resolved with `resolve_to_definition` and filtered in the same way. An
   import installs a candidate, not a binding, so feeder 1 never sees it.
3. **Implicit prelude** — `prelude_implicit_names()`, gated by the prelude
   fallback bit and resolved through prelude's public candidates, including
   re-exports.

Table guards are released before rendering.

### 23.2 Budget degrades grain, never presence

Under budget pressure each entry degrades from signature plus docstring, to
signature, to name only. The symbol list itself is never truncated, so the
agent never infers absence from elision
(`repl/spec/17a-agent-language-awareness.md` §17.18.2).

## 24. Containment of eval-thread typechecks

A monomorphiser assertion or other panic during an eval-thread typecheck would
otherwise unwind the REPL in the debug builds the agent uses.

### 24.2 One containment helper

`checked_check_forms` (`src/worker.rs`) wraps `check_forms` in `catch_unwind`
and converts a caught panic to an ordinary error, reusing `panic_message`.
`validate_forms_dry_run` calls it, so a panicking model proposal becomes a
repair attempt or give-up, never a crash. Pool workers keep their own catch;
the index worker has its own (§25.4).

## 25. `/search` — the importable-symbol index

`/search` finds symbols that are reachable but not yet imported. It is a
default-build session facility, not an agent capability. The experience is
`repl/spec/17a-agent-language-awareness.md` §17.19; the isolation contract is
`design/int/index-worker-isolation.md`.

**Current scope is interim.** Macro declarations are not index subjects
(`repl/spec/17a-agent-language-awareness.md` §17.19.2a), and source indexing
checks only a module's non-macro forms.
ACT-0952 owns the replacement: a full semantic index through the normal
compiler in an isolated realm. Until then this section describes what is built.

### 25.1 Execution home and per-module step

- The index is built by the nice workers from a separate `IndexModule`
  worklist (`src/session_v4/index_worker.rs`). It shares their threads but
  never the object-codegen worklist or the `.o` lifecycle, and it never
  registers a module.
- Discovery enumerates lib-path and project-root modules with the file rules
  `import` uses (`pipeline::resolve_module_file`).
- Each module takes exactly one branch:
  - **(a)** present in the scheduler registry: the real path owns it, so the
    index reads the loaded table's rows (or none) and never typechecks it;
  - **(b)** valid `.meta` (schema and build-id gates, plus
    [manifest validity](int.md#76-dependency-record-and-validity)): the table
    is deserialised and read, with no typecheck;
  - **(c)** no or stale `.meta`: the module is typechecked once against a
    private substrate (§25.2), inside the containment catch (§25.4).
- **Current branch-(c) cache write.** A clean branch (c) on a macro-free
  module writes a `.meta` (no `.o`) and, once its
  [dependency record](int.md#76-dependency-record-and-validity) settles, a
  manifest entry, so a later real import is a cache hit. `design/int/index-worker-isolation.md` §3.3 proposes
  retiring that write, and ACT-0952 forbids it for the future semantic index;
  its removal must be a coordinated design and test change, because
  `tests/search.rs` pins the current behaviour.

### 25.2 Private substrate

Branch (c) runs `check_forms` against a private snapshot of tables, aliases
and prelude fallback. The live `SharedState` maps are unchanged by
construction. The isolation contract and its evidence are
`design/int/index-worker-isolation.md`.

### 25.3 The index

`ImportableIndices` on `SharedState` is a derived, in-memory read cache. It is
not a symbol table, is never serialised, and needs no cache-schema change. It
holds one row per public symbol (name, scheme and docstring), the set of
processed modules, the worklist, and the lifecycle latch (§25.10). Clearing it
and re-reading `.meta` files reproduces the same results. The in-scope harvest
(§23) is separate: it reads live tables directly and shares no structure with
this index.

### 25.4 Containment

The branch-(c) typecheck is wrapped in `catch_unwind`. A caught panic or
typecheck error is a per-module skip: nothing is recorded, no `.meta` is
written, and the worker continues.

### 25.5 Trigger, priority and REPL-only arming

- `arm_burndown` enumerates the worklist once, at REPL start-up. `--run`,
  `--link` and release builds never arm it, so no index work or index-driven
  cache write can occur there.
- An idle nice worker takes object codegen first and index work only in the
  slack, so warming the index never delays loaded-module codegen.
- A search issued before the burn-down finishes serves partial results with
  the not-ready note (§25.10).

### 25.5b Flush and shutdown

Index work is best-effort warm-up. Link promotion drains only object codegen
and abandons the index worklist; shutdown is checked between index tasks.
`.meta` writes are atomic, so abandonment leaves unindexed modules, never a
corrupt artifact.

### 25.6 Command wiring and the result row

- `ReplCommand::Search` is an unconditional command; `search` is an allowlist
  row (§4.2).
- Each result row gives the name, the `:Type` rendered through
  `format_type_qualified`, the module, and the exact `(import …)` form.
- Ranking follows `repl/spec/17a-agent-language-awareness.md` §17.19.1a;
  messages follow §17.19.3. An empty query or no match returns no hits.

### 25.7 Match semantics

Name matches are exact or case-insensitive substring; docstring matches are
case-insensitive substring. Scheme matches call the typecheck-owned predicates
`signature_matches_exact` (alpha-equivalence) and `signature_matches_partial`
(structural containment, no unifier), exported by `cranelisp-typecheck`. The
index calls them and does not own type equivalence.

### 25.9 Seeded modules — a second, disjoint feed

- `primitives` and the synthetic `macros` module have no `.cl` file. They are
  read directly from their mounted tables and recorded with
  `record_preindexed`, with no typecheck or `.meta`.
- The seeded list comes from `bootstrap::seeded_importable_modules()`, not a
  name literal in the indexer; it excludes the root and `prelude`. Macro rows
  are still omitted (§25).
- `record_preindexed` counts a seeded module in both the enumerated total and
  the processed set, atomically and idempotently, so it is never pending.
- **The feeds are disjoint by construction.** Seeded names are removed from the
  file worklist before arming, so a user `primitives.cl` or `macros.cl` cannot
  be counted twice and wedge the pending count. The seeded module wins.

### 25.10 Lifecycle messages

- **Not-ready note.** While work is pending, `handle_search` appends the
  `indexing N module(s)…` note to partial results. On an empty result it serves
  that note instead of "no match": the two states call for opposite user
  actions. The pure functions `indexing_note_text` and `empty_result_message`
  own the text and its selection.
- **Completion notice.** `take_completion_notice()` is a one-shot
  check-and-set: armed, nothing pending, a not-ready note already shown, and
  not yet announced. The read loop polls it at the prompt boundary and prints
  `; search index complete.` only on an interactive TTY. Piped sessions never
  see it, which keeps scripted output deterministic.

## 27. Activity log (`src/agent/log.rs`)

The log is the silent, persistent, greppable index of agent activity; the
schema is `repl/spec/17b-agent-observability.md` §17.20.

### 27.1 Record sites

One `LogEvent` per existing event, with no new control flow: the model
exchange (`agent_turn`), a pull (`run_pull`), each repair iteration
(`validate_and_repair`), a committed submit, and a give-up. Each carries the
`turn` correlation key (§28.2) plus the explanatory fields §17.20.3a defines.

### 27.2 Gate

`CRANELISP_AGENT_LOG=<path>` enables it. Unset or empty means no file and no
cost. Write failures are discarded, and the session output is byte-identical
with or without the log.

### 27.3 Format

The log is JSONL with stable keys, serialised by `serde_json`. It records
metadata, not content.

### 27.4 Relationship to the trace

The log is the index and the trace (§28) is the content; the shared `turn`
joins them. Both are feature-gated, env-gated, silent development artifacts.

## 28. Full-content trace and correlation

### 28.1 Trace sink

`CRANELISP_AGENT_TRACE=<path>` appends each request and response, untruncated,
to a file. There is no stderr mode. `src/agent/trace.rs` formats through one
formatter with a `Grain`: `Full` for the persisted path, `Compact` for one-line
rendering.

### 28.2 The `turn` key

1. The key is the 1-based `agent_turn` loop step. `agent_turn` stores it on
   `AgentState.current_turn`; record sites read it from there;
   `assemble_request` copies it to `AgentRequest.turn`. The repair record
   keeps its own `iteration` alongside `turn`.
2. The trace is emitted by `RigModel` at the rig boundary, where it reads
   `request.turn`. The stub never emits a trace, so a trace-file test needs a
   rig-backed or emitting model (§11).

### 28.3 Shared append helper

`append_to_env_path` (`src/agent/sink.rs`) owns the environment-path gate, the
create-and-append and the discarded error. Each sink keeps its own variable
and content shape.

### 28.5 Evidence

Full-content survival, no stderr output, turn correlation, the silent-off
default and unwritable-path tolerance are the load-bearing properties; QA
allocates their evidence (§11).

### 28.6 Specification home

The environment-variable semantics and the `turn` key are specified in
`repl/spec/17b-agent-observability.md` §17.21.
