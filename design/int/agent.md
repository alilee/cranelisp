# Embedded Agent — int Design (`src/agent/` + dispatch classifier + reverse-query)

Owner: `/design` (int surface). Subordinate topic doc under `design/int/int.md` — the
master. This doc elaborates *within* the int bounded context (`design/arch/bounded-contexts.md`
§6) the implementation design for the **Sprint 88 agentic-REPL track**: the LLM-free
dispatch / reverse-query foundations (Stage B) and the read-only **Advisor MVP**
(Stage C, `repl-embedded-agent.md` §9 Phase 1).

**Provenance.** Refines `design/arch/repl-embedded-agent.md` (the `/arch` exploratory
design, now U1–U6 RATIFIED — `sprints/SPRINT.md` §"U1–U6 ratification gate") into an
implementable int-side plan. Scope + revisions R1–R6 are fixed by the Phase-2 `/arch`
verdict (APPROVE-WITH-REVISIONS). **This is DESIGN ONLY** — implementation is Phase 5.

**Authority order.** Where this doc and the bounded-context statement (BC §6) or the
ratified `repl-embedded-agent.md` drift, those win — file FIXME `target: /arch`.
The REPL *experience* (the `/ask` UX, the agent-output frame, the `--agent` row,
`/refs`/`/tests-for` UX, the U6 first-use disclosure wording) is `/repl`-owned in
`repl/spec.md`; this doc designs the int *mechanism* that backs it.

---

## 0. Scope summary — MVP-core vs R5-release-valve

The irreducible MVP (Stage C acceptance: `/ask "how do I define a constrained function
over Num?"` → spec-grounded, session-aware answer with a proposed `(defn …)` **shown,
not submitted**) is exactly five pieces:

| # | Piece | Tier |
|---|---|---|
| 1 | §5.3 dispatch classifier + `/ask` escape hatch (feature-OFF byte-identical) | **Stage B (LLM-free)** |
| 2 | Reverse-query commands `/refs` / `/tests-for` (LLM-free, default build) | **Stage B (LLM-free)** |
| 3 | `src/agent/` module + `agent` Cargo feature + `agent_turn` model↔tool loop | **Stage C MVP-core** |
| 4 | LLM completion layer via `rig-core`'s `CompletionModel` (R3-amended) — Anthropic + Ollama providers | **Stage C MVP-core** |
| 5 | Harvester + relevance ranker (§4.2/4.3 ladder) | **Stage C MVP-core** |
| 6 | Always-on language primer (§6.1) | **Stage C MVP-core** |
| 7 | Pull-as-visible-commands (§4.4 — synthesized REPL string through `process_commands`) | **Stage C MVP-core** |
| 8 | Read-only Advise mode (proposes code, does NOT submit) | **Stage C MVP-core** |
| 9 | **Spec-grep retrieval** (grep over embedded `spec/`) | **R5 — trail-into-S89 release valve** |
| 10 | **Telemetry skeleton** (log pulls/misses) | **R5 — trail-into-S89 release valve** |

R5 (the `/arch` verdict): pieces 9 + 10 are the cleanest to trail into S89 if Wave 2
runs hot. Spec-grep is a Phase-1 stopgap (→ semantic search in agentic-Phase-3);
telemetry has no Phase-1 consumer. Deferring them keeps the acceptance criterion
intact. This doc designs both but marks every seam `[R5]`.

**NOT this sprint (S89+ — seams noted, not foreclosed):** Build/Document write modes,
`submit_repl_input`, the pre-flight validator + silent-repair (U5 = silent-repair-anything,
S89-direction-only), module-preamble *editing* (the *reading* of the preamble is MVP —
§3.2). The staging-discard arm the validator will reuse already exists (Decision 44
discard-on-Err); this doc's only obligation is to **not foreclose** it. No new code for it.

---

## 1. Bounded-context fit (BC §6.3 — REPL-cadence consumer, not a new state window)

The agent is a **new consumer at three existing seams + one new sibling module** — the
`/arch` Phase-2 verdict's central claim, which this design honours structurally:

- **Zero new cross-crate edges.** The agent lives entirely in int. It reads int's own
  symbol tables / introspection and reuses int's *existing* inward calls to
  frontend/typecheck/backend (harvest, and — S89 — validate). No other crate's
  `public-api.txt` moves. (Principle 3 — dependency flows toward stability; the LLM
  client is an int-private optional dep, never a workspace edge.)
- **REPL-cadence consumer, NOT a new state window (BC §6.3).** `agent_turn` holds the
  REPL-cadence `&mut CompilerSession` handle — the *same* handle `main.rs`'s read loop
  drives, on the *same* eval thread. It does NOT open a fourth cadence, spawn a window,
  or take a second mutable claim on session state. Its model↔tool sub-loop is
  synchronous to the user's Enter (like a normal `eval`), and every state read goes
  through the **existing introspection surface** (`describe_symbol`, the `handle_*`,
  the symbol-table accessors) — never a bespoke state view. Cadence slot per §5.4.
- **`#[cfg(feature="agent")]` cuts AT the seams (4 of them), bolted on not woven through.**
  Feature-off ⇒ the binary is byte-identical to today (§4.4). The cuts:
  1. **Dispatch** (`src/main.rs` read loop): one classifier arm (§2).
  2. **Commands** (`src/repl.rs`): `/ask` + `/refs` + `/tests-for` `ReplCommand` variants
     (`/refs`/`/tests-for` are NOT gated — LLM-free, default build; `/ask` IS, see §2.3).
  3. **Module** (`src/agent/`): a new sibling in int's session decomposition, the
     `impl CompilerSession`-over-`pub(crate)`-fields pattern (`eval.rs`/`repl.rs`/
     `process_form.rs` — `src/CLAUDE.md §"Session/REPL module decomposition"`).
  4. **Validate/write** (S89, not this sprint): reuses the existing `eval`/staging path.

Quality attributes touched: **Simplicity** (Principle 6 — the agent adds no new
state-management complexity; it consumes existing surfaces), **Maintainability** (the
feature-gate cuts give bounded blast radius — feature-off is provably today's REPL),
**Observability** (telemetry skeleton §8 [R5]; pull-as-visible-commands makes every
agent action a transcript line), **Testability** (Principle 5 — `agent_turn` dispatches
through the object-safe `AgentModel` membrane §6, so the agent loop can be driven against a
stub `AgentModel` impl with zero network).

---

## 2. §5.3 dispatch classifier + `/ask`

### 2.1 The current seam (verified, current file:line)

The read loop is `src/main.rs:240-306` (verified — the `for line in stdin.lock().lines()`
loop). Today's completeness gate is `main.rs:251`:

```rust
if !buffer.trim_start().starts_with('/') && !s.parens_balanced(&buffer) {
    // continuation
}
```

On a complete buffer, `main.rs:260` calls `s.process_commands(&input, &mut stdout)`
(`src/repl.rs:381` — **note: the master doc's "`repl.rs:419`" now points at
`dispatch_command`; `process_commands` moved to `:381` in the S77 decomposition**).
`process_commands` sorts: blank/comment → `Nothing` (`:385`); slash → `dispatch_command`
(`:390`); bare special-form → `Final` (`:395`); else → `Compile(src)` (`:412`), which
`main.rs:266` feeds to `eval`. Bare atoms/literals reach `eval`'s introspection gate
`check_bare_symbol_introspection` (`src/eval.rs:447` — verified; the §4 self-documenting
behaviour). `describe_symbol` is `src/repl.rs:300` (verified).

### 2.2 The classifier shape — symbol-resolution-aware (refined, user-directed 2026-06-22)

The classifier is a routing decision made **one step earlier** than today, using the
reader the REPL already trusts (`cranelisp_frontend::parse`, `crates/cranelisp-frontend/
src/lib.rs:368`, called at `src/eval.rs:78`). It does NOT replace `process_commands`'s
internal sort — it sits *in front of it*, in the `main.rs` read loop, and diverts to the
agent the two cases `process_commands` would otherwise mishandle: a genuine parse error
(not Cranelisp), and a paren-balanced **bare-symbol** buffer whose symbols do not resolve.

**The design lesson (why the prior shape was wrong): parseability ≠ routing; resolution
is the discriminator.** The earlier draft of this section assumed prose fails to parse —
"two bare symbols = parse error per the reader" — and therefore routed any `Ok(forms)`
straight to `Repl`. That premise is **false about this reader.**
`cranelisp_frontend::parse("how do I define a function")` returns `Ok(N bare Symbol
forms)`, not `Err` — a run of bare words is a perfectly valid sequence of `Sexp::Symbol`
atoms. So a parse-success test alone routes a natural-language sentence to the REPL, never
the agent. **Parseability is insufficient; the classifier must resolve the symbols.** A
buffer of bare atoms is the §4 self-documentation surface **only if every atom is known**;
any unbound bare symbol (a typo, a bare word, a multi-word sentence) is for the agent. A
future reader MUST NOT reintroduce the "bare words don't parse → any `Ok` is REPL" premise.

```text
classify(buffer) ->                                   // main.rs read loop, on a complete buffer
  starts_with('/')                  -> Repl           // slash command — unchanged path (/ask, /refs, /tests-for)
  blank / comment-only              -> Repl           // unchanged (process_commands::Nothing)
  match cranelisp_frontend::parse(buffer):
    Err(unclosed '(' / '[')         -> Continuation   // (paren-balance guard) what parens_balanced gates today
    Err(other parse error)          -> Agent(buffer)  // not Cranelisp → natural language
    Ok(forms):
      ANY compound (List / Bracket)  -> Repl           // (+ 1 2), [1 2 3] — it is code, the §4 surface
      else (all forms are bare atoms — Symbol / Int / Float / Bool / Str):
        ALL known                    -> Repl           // §4 describe surface (bare-symbol introspection)
        ANY unbound / unknown symbol -> Agent(buffer)  // typo, bare word, multi-word prose
```

Atom resolution (the discriminator): a literal (`Int`/`Float`/`Bool`/`Str`) always counts
as known; a bare `Symbol` is known iff `symbol_is_known(name)` —

```rust
fn symbol_is_known(&self, name: &str) -> bool {                 // src/agent/mod.rs
    crate::session_v4::intrinsic_type_from_name(name).is_some() //   Int/Bool/Float/String (§4.1.3)
        || self.lookup_with_prelude_fallback(name).is_some()    //   src/repl.rs:562 — the canonical path
}
```

This reuses the **exact** resolution path `/sig` / `/info` / bare-symbol introspection /
`describe_symbol` use — `lookup_with_prelude_fallback` (`src/repl.rs:562`: current module
→ prelude outer scope → root, covering bound defs, special forms, types, traits,
operators, constructors), plus the `intrinsic_type_from_name` check those paths apply
ahead of the table lookup for the §4.1.3 names that live outside the symbol tables. **No
second resolver is hand-rolled** (Principle 7 — single source of truth): the `Some`/`None`
gate that decides "describe this symbol" vs "unknown symbol '…'" is the same gate that
decides Repl vs Agent here.

**Critical: the feature-OFF path is byte-identical.** The ENTIRE `agent` module — including
`classify_for_agent`, `symbol_is_known`, and the `Classify::Agent` variant — is
`#[cfg(feature = "agent")]` (declared in `lib.rs`), and `main.rs` calls `classify_for_agent`
only under the same cfg. Feature-off, the classifier and its `Agent` arm **do not exist**:
every input flows through `process_commands` / `eval` exactly as today. A bare unbound
symbol reaches today's `eval.rs` "unbound" introspection message; a genuine parse error
surfaces the same `eval` → `format_error` diagnostic. The feature-on `Agent` arms only fire
on input that today produces an unbound-symbol or parse-error diagnostic anyway, so there
is **no behaviour change for any input the reader accepts as known code.**

**Self-documentation preserved (the §5.2 tension, resolved).** A bare *known* atom (`+`,
`map`, `Int`, `42`) parses `Ok`, resolves, and routes `Repl` → reaches
`check_bare_symbol_introspection` (`eval.rs:447`) — the `repl/spec.md §4` contract is
untouched. A bare *unknown* word (`hello`, `lenght`, `why`) parses `Ok` as a lone
`Sexp::Symbol`, fails resolution, and routes to the agent — which is the right behaviour:
an unknown bare word is far more likely a question than a deliberate "describe this
unbound symbol" request. For a user who genuinely wants to introspect a not-yet-defined
name, or to ask a form-shaped question, the explicit escape hatch is `/ask` (§2.3).

### 2.3 `/ask <text>` — the escape hatch

A new `ReplCommand::Ask(&'a str)` variant (`src/repl.rs:37` enum) + a `"/ask"` arm in
`parse_slash_command` (`src/repl.rs:72`). It is the explicit "this is for the agent"
forcing function — works regardless of whether the text parses as a form, so the user
can ask `/ask why does + not work on strings` or `/ask "rewrite foo"`.

`/ask` dispatch in `dispatch_command` (`src/repl.rs:416`) is split by feature:

```rust
ReplCommand::Ask(text) => {
    #[cfg(feature = "agent")]
    { self.agent_turn(text, stdout); CommandResult::Nothing }   // §3; renders its own output
    #[cfg(not(feature = "agent"))]
    { CommandResult::Final("agent not built in (rebuild with --features agent)".into()) }
}
```

**The variant + the parse arm are unconditional** (the enum always carries `Ask`), but
the *dispatch body* is feature-split. This keeps the parser table identical in both
builds (so `/ask` is always recognised-not-unknown) while the capability is gated. With
the feature on but **no reachable provider configured** (U6 opt-in-twice — §6.4: no
Anthropic key AND no reachable local Ollama), the agent-on body short-circuits to a dormant
message: "agent feature built in but no provider configured; set an Anthropic key or point
at a local Ollama (transmits message + harvested source excerpts to `<endpoint>`)" — the U6
first-use disclosure naming **source excerpts** explicitly (the `/repl`-owned wording; this
is the int hook for it; the local-Ollama path discloses transmission to localhost).

### 2.4 Place in `main.rs`'s read loop

Minimal, gated. After the completeness gate (`main.rs:251`) and before
`process_commands` (`main.rs:260`):

```rust
// #[cfg(feature="agent")] only — feature-off this whole block is absent and
// the existing process_commands(&input, ...) path is byte-identical to today.
#[cfg(feature = "agent")]
if let Classify::Agent(text) = s.classify_for_agent(&input) {
    s.agent_turn(&text, &mut stdout);
    // re-prompt + watcher poll exactly as the normal-turn tail does
    continue;
}
// unchanged:
match s.process_commands(&input, &mut stdout) { … }
```

`classify_for_agent` is a `#[cfg(feature="agent")]` `pub(crate)` method on
`CompilerSession` (lives in `src/agent/`). It returns `Classify::Agent(text)` for the
`Err(other parse error)` case AND for an `Ok(all-bare-atoms)` buffer with any unbound
symbol (§2.2 — the resolution discriminator; it re-runs the cheap `parse` the loop would
run anyway, or — better — the loop threads the already-computed parse `Result` to avoid a
double parse; a Phase-5 micro-decision, noted). For every other case (slash, blank,
compound forms, all-known bare atoms) it returns `Classify::Repl` and the loop falls
through to `process_commands` unchanged. **`/ask`
does NOT go through `classify_for_agent`** — it is a slash command and flows through
`process_commands` → `dispatch_command` like any other (§2.3), so the classifier and the
escape hatch are two independent entry points to `agent_turn`.

Principle 11 (single pipeline; mode parameters) — the classifier is not a second
pipeline; it is a routing pre-filter that diverts exactly one otherwise-error case.

---

## 3. `src/agent/` module + `agent_turn`

### 3.1 Module shape

`src/agent/` — `pub(crate)`, fully `#[cfg(feature="agent")]`, a sibling to `repl.rs` /
`eval.rs` / `process_form.rs` in int's session decomposition (`src/CLAUDE.md`). Declared
in `lib.rs` as `#[cfg(feature = "agent")] pub(crate) mod agent;`. Suggested interior:

| File | Responsibility |
|---|---|
| `agent/mod.rs` | `impl CompilerSession { pub(crate) fn agent_turn(&mut self, text, stdout); fn classify_for_agent(&self, input) -> Classify; }` — the loop + classifier entry. |
| `agent/types.rs` | The provider-neutral turn vocabulary (`AgentRequest`/`ModelResponse`/`Turn`/`ToolDef`/`ToolCallRequest`/`ToolCallResult`) + the object-safe **`AgentModel`** membrane trait (§6.0) + `AgentState`. No rig type crosses this surface. |
| `agent/provider.rs` | Runtime provider selection (§6.4) — builds a `rig`-backed `AgentModel` (the `RigModel<M: CompletionModel>` membrane impl) for the configured provider (Anthropic default / Ollama local / stub), reads model-id + key/endpoint from runtime config, reports dormancy, and hosts the current-thread tokio `block_on` bridge. The ONE place holding a concrete rig `CompletionModel`. NO owned LLM-protocol code: rig owns the wire. |
| `agent/request.rs` | Translation between the agent's neutral turn vocabulary (primer/harvest/transcript/tool-defs, §3.3/§6.1) and rig's `CompletionRequest` + `Message`/tool-call types (via `serde_json` for the tool schema/args). The one place coupled to rig's request/response shapes. |
| `agent/stub.rs` | The deterministic test `AgentModel` (§6.0, §11) — a scripted-response model + an assertable capture of every `AgentRequest`. Implements `AgentModel`, the membrane, NOT rig's trait — the zero-network testability seam. |
| `agent/harvest.rs` | The harvester + relevance ranker (§5) — push-context assembly under token budget. |
| `agent/primer.rs` | The always-on language primer (§7) — a curated `const`/`include_str!` block + few-shot idioms. |
| `agent/pull.rs` | Pull-as-visible-commands (§4) — synthesize a REPL command string, run through `process_commands`, render as-typed. |
| `agent/spec_grep.rs` | `[R5]` Spec-grep retrieval over embedded `spec/`. |
| `agent/telemetry.rs` | `[R5]` Pull/miss logging skeleton. |

### 3.2 `agent_turn` — the model↔tool loop

`agent_turn(&mut self, text: &str, stdout: &mut impl Write)` is synchronous to the
user's Enter (it runs on the eval thread, holding the REPL-cadence `&mut CompilerSession`).
The loop:

```text
agent_turn(text):
  if no provider reachable (dormant) -> print U6 dormant notice, return    (§2.3, §6.4)
  req = assemble_request(text)                                              (§3.3)
  loop:
    resp = self.model.complete(&req)?         // AgentModel membrane (§6.0); the rig-backed impl
                                              //   block_on's rig's async CompletionModel one layer below;
                                              //   tool-calls surface here as ModelResponse::ToolCalls (§6)
    render agent prose in the reserved frame (style.rs, §3.5)
    match resp:
      Done(prose)                    -> render, break
      ToolCalls(calls):
        for call in calls:
          // every tool call IS a visible REPL command (§4 keystone)
          cmd_string = pull::synthesize_command(call)        // e.g. "/source foo"
          render cmd_string as-if-typed (normal REPL style)
          result = self.process_commands(&cmd_string, stdout) // SAME path a keystroke uses
          tool_results.push(result_text)
          telemetry::log_pull(call)                          // [R5]
        req = req.with_tool_results(tool_results)            // re-enter loop with results
    // budget guard: cap loop iterations (a tuning knob, not architecture)
```

Key properties:
- **Reads call the existing surface directly OR re-enter via `process_commands`.** Two
  read styles, both in-process: (a) the *harvest* (§5) reads symbol tables / introspection
  directly via the existing accessors (`describe_symbol`, `defined_symbols()`,
  `get_introspection`) — assembled into the request before the first `send`; (b) a *pull*
  (§4) re-enters through `process_commands`, so it is a visible REPL line. (a) is the
  ambient push (cheap, every turn); (b) is the enacted depth-on-demand.
- **No private tools (the §4.4 principle).** The agent's entire capability surface is the
  REPL command set. A pull synthesizes a command string; there is no separate tool
  registry. The model's "tools" map 1:1 onto REPL commands (§4.2).
- **Read-only this sprint.** No `submit`. If the model proposes a `(defn …)`, the agent
  *renders it as a proposal* (in its frame) — it does NOT route it to `eval`. The
  staging-write path (S89) is deliberately unreachable from `agent_turn` in the MVP.
- **Ctrl-C / interrupt** returns to the prompt (the existing read-loop interrupt). Because
  the MVP never mutates session state, an interrupt mid-turn leaves the session consistent
  by construction (no staging to discard).

### 3.3 Request assembly (the harvest + primer + transcript + turn)

`assemble_request(text)` composes the neutral turn vocabulary that `agent/request.rs`
translates into the rig `CompletionRequest` (§6.1):
1. **System primer** (§7) — always-on language essentials.
2. **Harvested context** (§5) — the push map under token budget.
3. **Transcript** — the prior agent turns this session (a `Vec` on the agent state; see
   §3.4). Bounded by budget; oldest turns drop first.
4. **Spec excerpts** `[R5]` — if spec-grep ran for this turn (§7.2).
5. **User turn** — `text`.

The assembled request is **provider-neutral** in the agent's own vocabulary (§3.3 fields);
`agent/request.rs` (§6) translates it to rig's `CompletionRequest`. rig itself is the
provider-agnostic boundary (R3-amended) — the same translated request drives Anthropic or
Ollama (or any rig provider) with no agent-loop change.

### 3.4 Agent state — minimal, transcript only

The only persistent agent state is the **conversation transcript** (the model turns +
tool results so far this session). It lives on a `pub(crate)` field added to
`CompilerSession` (or, cleaner, on a `#[cfg(feature="agent")] Option<AgentState>` field so
feature-off carries zero bytes):

```rust
#[cfg(feature = "agent")]
pub(crate) agent: Option<crate::agent::AgentState>,   // None until first /ask or agent route
```

`AgentState` = `{ transcript: Vec<Turn>, model: Option<Box<dyn AgentModel>>,
provider_label: String }` (the `model` is the object-safe **`AgentModel`** membrane handle
built by `agent/provider.rs` for the configured provider — §6; `None` ⇒ dormant). It is
**`Box<dyn AgentModel>`, NOT `Box<dyn rig::completion::CompletionModel>`** — rig's
`CompletionModel` is dyn-incompatible (associated types + a `Clone` bound + async methods),
so a `Box<dyn CompletionModel>` does not compile; `AgentModel` is the one-method object-safe
trait the stub and each rig-backed provider implement, with rig's `CompletionModel` the wire
boundary one layer below inside `provider.rs` (§6.1). See §6.0 for the full membrane rationale.
This is the **per-symbol-mutability / windowed-state discipline** (int.md §4) applied: the
agent adds ONE optional field, lazily constructed, not a parallel state machine. It is NOT
serialized (the MVP has no cross-session agent memory — the §3.2/§4.6 "memory is the
docstrings/preambles" model means the durable memory lives in the code, harvested fresh;
the sidecar is S89+). Feature-off ⇒ the field does not exist (`#[cfg]`-gated), so the
binary is byte-identical (§1).

### 3.5 Output framing (safety boundary §7.4)

The agent's **prose** renders in a distinct reserved visual frame (reuse `src/style.rs`
with its own role so `--no-color`/`NO_COLOR` degrade gracefully). Agent-issued commands +
their results render in **normal REPL style** (they ARE normal output — §4.4). Only the
prose is framed, so the deterministic `:Type value` format and the model's voice are
unmistakable. The exact frame glyphs/wording are `/repl`-owned (`repl/spec.md` agent
section); this doc fixes only that int routes prose through a distinct `style.rs` role.

---

## 4. Pull-as-visible-commands (§4.4 keystone)

### 4.1 Mechanism

A pull is the agent issuing a REPL command on the user's behalf. `pull::synthesize_command`
turns a model tool-call into a command **string** (e.g. `/source foo`, `/info bar`,
`/refs baz`, `/sig qux`), which `agent_turn` runs through `self.process_commands(&s, stdout)`
— the *same* path `main.rs:260` uses for a keystroke. The returned `CommandResult` text is
(a) rendered in the transcript as if the user typed the line, and (b) fed back to the model
as the tool result. Consequences (all from `repl-embedded-agent.md §4.4`):
- **No separate tool registry** — the pull-surface IS `dispatch_command`.
- **Visibility is uniform** — reads auto-run-and-show (writes are S89, confirm-gated).
- **Teaching surface** — the user watches the agent reach for `/source`/`/info`/`/refs`.
- **Pulls warm the push** — once pulled, `foo` is "mentioned" and enters the harvest
  window next turn (§5.3 recency). Push and pull interlock.

### 4.2 The tool → command mapping

The model is given (in the primer / tool definitions) a small set of "tools" that are
exactly REPL commands it may emit. MVP read-only set: `/source <sym>`, `/sexp <sym>`,
`/info <sym>`, `/sig <sym>`, `/doc <sym>`, `/type <expr>`, `/imports`, `/exports <mod>`,
`/list`, `/refs <sym>` (§9), `/tests-for <sym>` (§9), and `/spec <query>` `[R5]` (§7.2).
The mapping is data, not a registry — a table in `pull.rs` validating that a synthesized
command is in the **read-only allowlist** (no `/sh`, no `submit`, no write commands this
sprint — the consent boundary is enforced at synthesis, not trusted from the model).

**Safety: the allowlist is the consent gate.** `synthesize_command` rejects any command
not in the read-only set (renders "agent attempted a non-read command — refused" rather
than running it). This is how "auto-approve reads only" (§7.4) is structurally enforced
in the MVP — the agent *cannot* synthesize a write because the allowlist excludes them.

---

## 5. Harvester + relevance ranker (§4.2/4.3)

### 5.1 The push/pull principle

**Push the shape of everything; pull the bodies** (`repl-embedded-agent.md §4.3`). The
harvester assembles, every turn, a context map from **in-process free signals** — it reads
the same live structures the compiler just wrote (Principle 7 — the symbol table is the
single source of truth; the harvest is a read, never a copy-store). Token budget is the
governing constraint (§4.2): omniscient ≠ dump everything.

### 5.2 The push heuristics (tuning knobs, not architecture)

Default push, in priority order (the graceful-degradation ladder, §5.4):
1. **Current module — full source, pinned.** `current_module_path()` → iterate
   `symbol_table.defined_symbols()` → for each, `get_introspection(sym).source`
   (REPL evals) or the file-sliced source. Always included (the pin).
2. **Last ~6 modules mentioned — preamble + export surface.** For each mentioned module:
   - **preamble**: `symbol_table.module_preamble` (the field landed by FIXME 0428 —
     `crates/cranelisp-types/src/module.rs:130`, populated by the frontend reader from
     the leading `;;` comment block per spec §8.16). The harvester READS it (no edit —
     editing is S89 Document mode).
   - **exports**: the module's public `defined_symbols()` filtered to `is_public()`, name
     + scheme (the `/exports` surface, harvested directly).
3. **Last ~10 fns mentioned — full source.** For each mentioned fn FQ:
   `get_introspection(fq).source` (the `/source` surface, harvested directly).

"Mentioned" = appeared in the transcript or surfaced by a command this session, ordered
by the symbol table's `seq` (`crates/cranelisp-types/src/module.rs:157` `next_seq`;
per-entry `seq` records authorship recency — Decision 39). Recency = max `seq` among
mentions, so recently-defined / recently-touched entries win the window.

### 5.3 In-process free signals (the ranker inputs)

All free, all in-process (`repl-embedded-agent.md §4.2`):
- **Cursor module** — `current_module_path()` (pins #1).
- **Names in the message** — tokenize `text`, match against `defined_symbols()` keys.
- **Last error + implicated symbols** — int already formats errors with `ErrorLocation`
  (int.md §9); the implicated FQ symbols are a harvest signal. **This signal ranks
  *committed* symbols only** — it names which in-scope defns to prioritise. It does NOT
  carry the failed *form* itself (a failed `(defn …)` never commits, so it is in no symbol
  table), nor the diagnostic text the user read. That missing signal — the errored turn's
  own source + diagnostic — is a distinct harvest block, §5.5.
- **`seq`-ordered recency** — per-entry `seq` (above).
- **Import-graph neighborhood** — `module_aliases` + the per-symbol `Import` edges
  (`install_imports`, `src/imports.rs`) give callee/caller neighbors of in-window fns.
- **Transcript** — what's already been discussed this session.

The ranker is a scoring pass over `defined_symbols()` combining these signals; the
top-budget slice is pushed. **No maintained index** — recomputed each turn from live
state (no invalidation problem; §3.3 of the arch doc — the harvest is a pure cache).

### 5.4 Graceful-degradation ladder under token budget

When the assembled push exceeds the budget, drop the cheapest-value tail first. Budget is
consumed in **push order** (`harvest_context`), so the blocks below — listed
**highest-keep-priority first** (the pinned floor) to **lowest-keep-priority last** (the
first to drop) — degrade from the bottom up: an earlier block always wins the budget over a
later one. This is a keep-priority ladder, **not** an accretion list; read top-down as "kept
longest → dropped first":
```
current-module full-src            PINNED — never dropped (the floor)
most-recent errored turn (§5.5)    PINNED — never dropped (joins the floor: the uniquely-
                                   unrecoverable signal committed state cannot reconstruct)
older errored turns (§5.5)         newest-first (the oldest errored turn drops first)
green recent turns (§5.5)          deixis-only — the first recent-turn entry to drop
== in scope == block (§23)         degrades GRAIN per symbol (full → sig → name); the symbol
                                   LIST is never truncated
last-10 mentioned-fns full-src
last-6 mentioned-modules           preamble+exports → exports-only → dropped (cheapest tail —
                                   dropped first)
```
The floor always includes the current module (the pin) so the agent is never blind to the
user's cursor context, **and the single most-recent errored turn (§5.5)** — the missing
signal committed state cannot reconstruct, so it earns the pin next to the cursor module.
Older errored turns, green recent turns, the `== in scope ==` block, and the mentioned
fn/module surfaces all degrade above the floor, in the reverse of the keep-priority order
above (mentioned-module surfaces are the cheapest tail, dropped first). The budget number
is a runtime config knob (§6.4), not a constant.

### 5.5 Recent-errored-turn feed (E5 — the missing debug signal)

**The finding (S108 Inc3 E5, confirmed in code).** `harvest_context` (§5.1–5.4) assembles
context *entirely* from **committed** session state — mentioned symbols, in-scope defns,
module source. A failed `(defn …)` never commits: it is absent from every symbol table,
therefore absent from the harvest. So when a user types a form that fails to typecheck and
then asks *"why doesn't that typecheck?"*, the agent has zero visibility into the form or
its diagnostic — it hallucinates context and asks the user to paste the attempt. Debugging a
type error is the single highest-value in-REPL agent function, and the push side is blind to
it. The cure is a fourth harvest source: a bounded record of the recent REPL turns the user
actually saw, surfacing the **errored** ones — because a green turn's defn is already in the
symbol table (heuristics #1/#3 carry it), while a failed turn is the signal that lives
*nowhere else*.

**(1) What each ring entry captures.** One entry per REPL **eval turn** (the
`process_commands → CommandResult::Compile → eval` path — not slash commands, not `/ask`
turns, which are agent-conversation and already ride the §3.4 transcript):

- **`input`** — the exact source text the user submitted (`input_str` in the read loop —
  the buffer already trimmed and cleared for that turn).
- **`outcome`** — a two-arm record of *the string the user saw*: either the rendered result
  (`format_eval_result` output, green) **or** the compiler diagnostic verbatim (the
  `Error: {e}` line — the type error / parse error / warning surfaced). No re-derivation:
  the outcome is the identical string the display boundary already produced (see (2)).

The ring is **bounded, capacity N = 8 turns.** Justification: N must be large enough that
the most-recent *error* survives even when a few green or introspection turns follow it
before the user asks (a realistic debug micro-interaction — try a defn, it fails, poke at
`/sig` or a helper, then ask), and small enough to stay trivially inside the §5.4 budget.
Eight `(input, short-diagnostic)` pairs are at most a few hundred tokens, and the harvest
block is budget-gated like every other source (§5.4) so it degrades before it can crowd the
pinned module source. N is a tuning knob, not architecture (like the §5.2 push counts); 8 is
the starting value. The errored-turn *preference* (below) means the pin survives even if all
8 slots would otherwise fill with green turns — the ring is scanned for errors, not merely
truncated.

**(2) Where it is fed from — the ONE display boundary (Principle 7).** The ring is written
from the **single per-turn render site in the `main.rs` REPL read loop** — the same place
that computes `input_str` and emits the user-visible result (`s.pretty_print(&text, …)` on
the green arm) or diagnostic (`writeln!(stdout, "Error: {e}")` on the `Err(e)` arm). A small
`#[cfg(feature="agent")] pub(crate) fn record_repl_turn(&mut self, input: &str, outcome:
ReplTurnOutcome)` on `CompilerSession` is called once at that seam with **the identical
strings the user saw** — the read loop threads the already-rendered `text` / `format!("Error:
{e}")` into the one call at the turn tail (green and error arms feed the two `outcome`
variants). This is deliberately **not a second transcript store**: the feed reuses the strings
the display boundary already produced rather than re-capturing or re-rendering input. rustyline
history is **not** this seam — it is TTY-only, input-only (no results, no diagnostics), and
exists for line recall; using it would be a parallel transcript channel (Principle 7 forbids
it, per the E5 `/arch` coherence note). One boundary produces the user-visible strings; the
ring reads that one boundary.

**(3) How it enters the harvest — a new budget-gated block, errored turns preferentially.**
`harvest_context` gains a fourth source (`harvest.rs::push_recent_turns_block`, pushed
right after the current-module pin and before the `== in scope ==` block — alongside
current-module source, mentioned modules, mentioned fns): it reads the ring and emits a
labelled context block of recent turns, **ordered errored-first, newest-first** (the ring is
iterated newest→oldest — `push_back` newest, `.iter().rev()` — and partitioned into errored
then green, each partition newest-first), each rendered as its `input` form followed by its
diagnostic (or, for a green turn kept for deixis, its result). It is budget-gated exactly
like the other sources and sits high in the §5.4 ladder: the **single most-recent errored
turn is PINNED to the floor** — emitted unconditionally, even past the budget (it is the
uniquely-unrecoverable signal — committed state cannot reconstruct a form that never
committed); older errored turns degrade next (newest-first, budget-gated), and green turns
(kept only so the agent can resolve deixis like *"that"* / *"the last one"* against the
form immediately preceding the question) are the first to drop. This preference is why the
ring records green turns at all yet never lets them starve the error: a debug question almost
always refers to the most recent *failure*, which the pin guarantees is present.

**(4) Feature-gating + byte-identical-when-off.** The ring lives on `AgentState`
(`turn_ring: VecDeque<ReplTurn>`, cap N) — the state object already fully
`#[cfg(feature="agent")]` (§3.4), constructed at `enable_agent` (REPL startup, feature-on +
`--agent`), so it records from the very first turn and the E5 *fail-then-ask* sequence is
covered with no lazy-first-`/ask` gap (`enable_agent` runs before the read loop). Feature-off,
`AgentState`, `ReplTurn`, `ReplTurnOutcome`, `record_repl_turn`, and the read-loop call site
**do not exist** (all `#[cfg(feature="agent")]`), so the read loop is byte-identical to
today's — the recording call is absent, not a guarded no-op in the compiled binary. Feature-on
without `--agent` leaves `self.agent == None`; `record_repl_turn` guards on `if let Some(agent)
= &mut self.agent`, so it is an early-return no-op and nothing is recorded until the agent is
enabled. The block adds **no** new state window, no worker, no cross-crate edge, no
`cranelisp-types` change: it is one bounded field on an already-gated int-private struct, fed
from an existing display boundary — Simplicity (Principle 6) and the §1 byte-identical
guarantee both hold. **Landed (Wave A, `src/agent/`, `--features agent`):** the ring is
`AgentState.turn_ring: VecDeque<ReplTurn>` cap `TURN_RING_CAP = 8`
(`agent/types.rs`), fed by `record_repl_turn` (`agent/mod.rs`) from the two `main.rs`
per-turn render sites, and read by `harvest.rs::push_recent_turns_block`.

---

## 6. LLM completion layer — rig's `CompletionModel` behind a one-method `AgentModel` membrane (R3-amended — BINDING)

### 6.0 The decision (R3-amended, user 2026-06-21; membrane deviation accepted 2026-06-22)

R3's **intent** — a provider-agnostic boundary so `agent_turn` survives a local-model /
alternate-provider backend untouched — stands and is binding. Its **mechanism changed by
user direction (2026-06-21; `sprints/SPRINT.md` §"Architecture review" R3-amended):**

- **rig's `CompletionModel` is the provider WIRE boundary; a one-method object-safe
  `AgentModel` membrane is what `agent_turn` actually dispatches through.** We do NOT define
  a project-owned `LlmBackend` *adapter* trait (no protocol re-implementation, no
  `agent/anthropic.rs` hand-rolled provider), and rig's `CompletionModel` (verified path:
  **`rig_core::completion::CompletionModel`** — the lib name is `rig_core`, not `rig`;
  docs.rs/rig-core 0.39.0, the low-level completion interface every rig provider implements)
  **IS** the provider-agnostic wire boundary R3 required, consumed in `provider.rs`/`request.rs`.

  **Object-safety deviation (as-built, accepted by user 2026-06-22; FIXME 0427 resolved).**
  The original §6 mechanism named `agent_turn` holding `Box<dyn rig::completion::CompletionModel>`
  directly. **That does not compile.** rig's `CompletionModel` is **dyn-incompatible**: it
  carries associated types (`Response`, `StreamingResponse`, `Client`), a `Clone` supertrait
  bound, and async methods (`-> impl Future`: `completion`, `stream`). Any one of those makes
  a trait non-`dyn`-compatible; this trait has all three — `Box<dyn CompletionModel>` is
  rejected by the compiler. The as-built therefore introduces a **minimal one-method
  object-safe membrane** in `agent/types.rs`:

  ```rust
  pub trait AgentModel: Send {
      fn complete(&mut self, request: &AgentRequest) -> Result<ModelResponse, String>;
  }
  ```

  `AgentState.model` is `Option<Box<dyn AgentModel>>`. The stub and each rig-backed provider
  implement `AgentModel`; the rig-backed impl (`RigModel<M: CompletionModel>` in `provider.rs`)
  holds the concrete rig `CompletionModel` and `block_on`s its async `completion` internally,
  speaking only the neutral vocabulary (§3.3) across the boundary. **This is NOT a new adapter
  layer in the R3-rejected sense** — it re-implements no protocol, owns no wire detail (rig
  still owns all of that one layer below). It is the **structural consequence of
  dyn-incompatibility plus the requirement for runtime provider selection** (a `Box<dyn …>` is
  needed to hold "anthropic OR ollama OR stub, chosen at session construction" — §6.3) **plus
  the stub plug-in point** (§11 / `tests/plan/agent-testing-strategy.md`). The membrane *is*
  the testability seam: the stub implements `AgentModel`, so the whole agent loop runs against
  a deterministic canned model with zero network (Principle 5 — testability is structural).
  rig's `CompletionModel` membrane was always §6.1's named coupling point; the only change is
  that the dispatch shim over it is the project-owned object-safe `AgentModel`, not `dyn
  CompletionModel`. **A future reader MUST NOT "simplify" this back to
  `Box<dyn rig::CompletionModel>` — it will not compile.**
- **rig is used as the provider / completion layer ONLY — explicitly NOT rig's `Agent`
  struct, RAG, or tool-orchestration framework.** rig ships a higher-level `rig_core::agent::Agent`
  with its own tool registry, RAG context injection, and turn loop. We do **not** use it:
  it would collide head-on with our own `agent_turn` loop (§3.2), our harvester (§5), our
  **pull-as-visible-commands** mechanism (§4), and the keystone principle that **the agent
  has no private tools — its entire capability surface IS the REPL command set** (§4.4).
  We consume rig at the `CompletionModel`/`CompletionRequest` seam and own everything above
  it. *A future reader must not reach for `rig_core::agent::Agent` — that is a deliberate
  exclusion, not an omission.*

The discriminator (Principle 8 — no interim implementations) is unchanged: *will the loop
survive a local-model / alternate-provider backend without touching `agent_turn`?* — and is
now satisfied **by rig itself**: rig's `CompletionModel` is already implemented across
Anthropic, Ollama, OpenAI, Groq, and ~20 other providers, so provider swap is a
construction-time choice (§6.4), not an `agent_turn` edit.

### 6.1 What `agent_turn` speaks

`agent_turn`'s loop (§3.2) holds a `Box<dyn AgentModel>` (the object-safe membrane, §6.0;
the `model` field on `AgentState`, §3.4) and calls its one method `complete(&AgentRequest)`,
passing the agent's neutral turn vocabulary (§3.3). One layer below, inside the rig-backed
`AgentModel` impl (`RigModel` in `provider.rs`), `agent/request.rs` translates that neutral
request into a rig `CompletionRequest` and `block_on`s rig's async `completion` —
`rig_core::completion::CompletionModel` is the wire boundary there (NOT `agent_turn`'s
dispatch type; rig's trait is dyn-incompatible, §6.0). The neutral→rig field mapping:

- **System primer** (§7) → the request's preamble / system content.
- **Harvested context** (§5) + **spec excerpts** `[R5]` (§7.2) → additional system/context
  content (provider-neutral text the harvester assembled).
- **Transcript** (§3.4) → rig `Message` history (user / assistant / tool-result turns).
- **Tool defs** = the read-only command allowlist (§4.2) → rig tool definitions.
- **User turn** → the current user message.
- **Completion budget** → `max_tokens` — a **REQUIRED** field on every assembled request:
  Anthropic's Messages API rejects a request that omits it (every turn 400s before a token
  streams). Set on the single shared `build_request` builder (`src/agent/provider.rs`) as
  `AGENT_MAX_TOKENS = 65536` — a 64K streaming-scale default (full rationale on the
  constant's rustdoc). This is the **completion output budget** and is explicitly **distinct
  from the §5/§5.4 harvest token budget** (which bounds *input* context assembly and is a
  runtime config knob, §6.4); the two never interact.

The single coupling point is `agent/request.rs` (§3.1): the translation between the agent's
neutral vocabulary and rig's `CompletionRequest` / `Message` / tool-call types. The agent's
own `AgentRequest` / `ModelResponse` / `Turn` / `ToolDef` / `ToolCallRequest` /
`ToolCallResult` types remain provider-neutral (the vocabulary `AgentModel::complete` speaks)
so the harvester, primer, pull, and transcript machinery — and `agent_turn` itself — never see
a rig type; `request.rs` is the rig-coupling membrane and the `AgentModel` trait is the
object-safe dispatch shim above it.

### 6.2 Streaming + tool-use come from rig's completion layer

Both confirmed present at the `CompletionModel` layer (docs.rs/rig-core 0.39.0):

- **Streaming** — rig exposes streaming completions at the model layer (`RawStreamingChoice`
  / `StreamedAssistantContent` chunk enums carrying text deltas, tool-call deltas, and final
  usage). `agent_turn` renders prose live from the stream into the reserved frame (§3.5).
- **Tool-use** — rig's completion layer carries tool definitions and surfaces tool-call
  requests in the response (incremental tool-call deltas, collectable via the
  complete-tool-call path). Each surfaced tool call maps 1:1 to a synthesized REPL command
  (§4.2) — our pull mechanism, *not* rig's tool executor (we never register an executable
  tool with rig; we read the tool-call request and run it through `process_commands`).

So the agent does not hand-roll SSE framing, `anthropic-version` headers, or `tool_use`
block shapes — rig owns all provider wire detail. (This is the coupling tradeoff: §6.5.)

### 6.3 Provider selection — Anthropic default, Ollama local (multi-provider, U6 hatch)

`agent/provider.rs` (§3.1) builds the rig `CompletionModel` for the **runtime-configured**
provider, wraps it in a `RigModel<M>` (the rig-backed `AgentModel` impl, §6.0), and boxes it
as the `Box<dyn AgentModel>` membrane handle. Selection is runtime config
(`CRANELISP_AGENT_PROVIDER`), not a compile choice:

- **Anthropic = the default provider.** Built from `rig_core::providers::anthropic` (verified
  module path; the lib name is `rig_core`), with the **model-id taken from runtime config**
  (not hardcoded — per the `claude-api`/`/anthropic` discipline, the concrete current model-id
  is a Phase-5 config value looked up against live Anthropic docs, never baked from memory).
  Requires an API key → contributes to opt-in-twice (§6.4).
- **Ollama = the local / offline escape hatch.** Built from `rig_core::providers::ollama`
  (verified module path) against a **local endpoint with no API key**. This is what delivers
  the **U6 privacy escape hatch** *and* the `repl-embedded-agent.md §9` Phase-3
  **local-model goal — now**, in the MVP, because rig already implements `CompletionModel`
  for Ollama. A user wanting zero-transmission operation points the agent at a local Ollama
  and no source excerpt ever leaves the machine.

Provider + model-id + endpoint + key come from runtime config (env var / config file —
the §6.4 opt-in-twice surface). Adding a third rig provider later (OpenAI, Groq, …) is a
`provider.rs` construction arm, not an `agent_turn` change — the R3 intent, delivered.

### 6.4 Dependency discipline + feature gate + opt-in-twice (U6)

```toml
# Cargo.toml (the cranelisp binary crate) — AS-BUILT (Wave 3, accepted 2026-06-22)
[dependencies.rig-core]
version = "0.39.0"               # the Phase-5 pin
default-features = false         # drop rig's default derive/reqwest/rustls bundle
features = ["reqwest", "native-tls"]  # the smallest set that compiles the completion API
                                 #   + the anthropic/ollama providers; native-tls NOT rustls
optional = true

[dependencies.tokio]
version = "…"                    # current-thread runtime only — `agent_turn` block_on bridge
default-features = false
features = ["rt", "macros"]
optional = true

[dependencies.serde_json]        # tool schema + tool-call argument (de)serialization
version = "…"
optional = true

[features]
agent = ["dep:rig-core", "dep:tokio", "dep:serde_json"]  # OFF by default — in NO default set
```

- **`rig-core` (+ `tokio` + `serde_json`) are `optional = true`, enabled ONLY by the `agent`
  Cargo feature**, which is in **no crate's `default`**, enabled by no dev-dependency. `cargo
  build` / `cargo nextest run` therefore **never compile rig** → the default build + ~9s suite
  stay agent-free (`repl-embedded-agent.md §7.2`; mirrors `design/arch/release-llvm-backend.md
  §5`). All of `src/agent/` is `#[cfg(feature="agent")]`. Agent tests run in a separate
  `#[cfg(feature="agent")]` lane (`tests/agent.rs`, per the `/qa` Step-3.1 plan).
- **`features = ["reqwest", "native-tls"]` (as-built) — native-tls, deliberately NOT rustls.**
  rig's defaults (in 0.39.0: `derive`, `reqwest`, `rustls`) are dropped; the as-built opts back
  in `reqwest` + `native-tls` — the smallest set that compiles the completion API and the
  anthropic + ollama providers. **The rustls path was rejected:** it pulls `aws-lc-rs` (a heavy
  C TLS backend, ~30 MB of build artifacts + a C toolchain), which is prohibitive on the
  disk-tight VM (`memory/linux-vm-baseline.md`); `native-tls` links the system OpenSSL instead —
  a far lighter agent footprint. **Provider feature note (corrects the SPRINT R3 wording):** in
  `rig-core` 0.39.0 **providers are compiled into the core crate and are NOT individually
  feature-gated** — there is no `anthropic`/`ollama` Cargo feature (they live under
  `rig_core::providers::{anthropic,ollama}`, always present once `rig-core` is a dep). The SPRINT
  R3 phrasing "`+ only the anthropic + ollama providers`" reads as *intent* (compile only what
  those two need), not literal flags. If a later rig version gates providers, enable exactly the two.
- **`tokio` is a current-thread runtime only** (`rt` + `macros`) — `agent_turn` runs
  synchronous to the user's Enter, and the rig-backed `AgentModel::complete` (`RigModel`,
  §6.0) `block_on`s ONE async rig `completion` per loop step on a
  `Builder::new_current_thread()` runtime (no multi-thread executor, no spawned thread). This
  is the sync↔async bridge the membrane hides from `agent_turn`.
- **`serde_json`** carries the tool-definition schema and the tool-call argument
  (de)serialization at the `request.rs` membrane.
- **Opt-in twice (U6) — unchanged:** compiled-in (the `agent` flag) AND a runtime provider
  configured *and reachable* (Anthropic key present, OR a reachable local Ollama endpoint).
  Absent any reachable provider the agent is **dormant** and `/ask` says so, naming the
  endpoint + that **source excerpts** are transmitted (the U6 first-use disclosure — §2.3;
  the Ollama-local path transmits to localhost, which the disclosure states accurately). The
  published binary MAY ship `--features agent`; it stays dormant until a provider is
  configured.

### 6.5 Coupling tradeoff (accepted)

`agent/request.rs` + `agent/provider.rs` are **coupled to rig's API surface** — rig's
`CompletionModel` method shape, its `CompletionRequest` / `Message` / streaming-chunk /
tool-call types. The `AgentModel` membrane (§6.0) means `agent_turn` *itself* is **not**
coupled to a rig type (it dispatches through `Box<dyn AgentModel>` over the neutral
`AgentRequest`/`ModelResponse` vocabulary) — the rig coupling is confined to the two
membrane-implementing files. **Dropping rig later would touch the request membrane
(`request.rs`) and the rig-backed `AgentModel` impl (`provider.rs`)** — not `agent_turn`, and
not one isolated provider file per provider. This is the **accepted cost of the leaner
no-adapter choice** (user direction): we trade the prior design's owned `LlmBackend`
*protocol-adapter* layer — which would have re-implemented the wire — for not building and
maintaining that at all, and for getting ~20 providers (incl. local Ollama) for free *today*.
The `AgentModel` membrane is the small structural price the dyn-incompatibility of rig's trait
(§6.0) plus runtime provider selection plus the stub seam exact — it is a one-method dispatch
shim, NOT a protocol re-implementation, so it does not reintroduce the rejected adapter cost.
The blast radius of a hypothetical future rig replacement is bounded to `request.rs` +
`provider.rs` (and never `agent_turn`), all `#[cfg(feature="agent")]`, int-private — never a
cross-crate edge, never a facade. Recorded per Principle 6 (complexity has a budget): the cost
is real and named; the benefit (no protocol adapter, multi-provider + local now, plus a clean
zero-network testability seam at the membrane) was judged worth it.

---

## 7. Always-on language primer (§6.1)

A compact, curated **language primer + canonical few-shot idioms**, always in the request
(the system-primer content `agent/request.rs` puts into the rig `CompletionRequest` — §6.1).
Cranelisp is private — the model has **zero** of it in
training (`repl-embedded-agent.md §6`), so the primer is mandatory grounding, not optional.

### 7.1 Content (curated, distilled)

The distilled *always-needed* essentials (distinct from the large, retrieved spec):
- Core syntax + the special forms (`defn`, `deftype`, `match`, `let`, `if`, `fn`, …).
- The `:Type form` convention (the annotation reader-macro — binds the following form;
  `memory/annotation-reader-macro-binds-following-form.md`).
- The prelude surface (the implicit outer scope — traits/operators/types it provides).
- Canonical few-shot idioms: a `defn` with a docstring, a `deftype` (product + sum), a
  `match`, a trait impl, a module-with-preamble (the leading `;;` block per §8.16).

Stored as a `const`/`include_str!` block in `agent/primer.rs` (a `.txt`/`.md` companion
asset, version-controlled, human-curatable). It is curated by hand for the MVP; telemetry-
driven curation (which idioms the model fumbles) is agentic-Phase-3 (`repl-embedded-agent.md
§6.3`) — the telemetry skeleton (§8) logs the signal, no consumer yet `[R5]`.

### 7.2 `[R5]` Spec-grep retrieval

`agent/spec_grep.rs` — a `/spec <query>` pull-tool (§4.2) that greps the embedded `spec/`
(the curated `spec/*.md`, embedded via `include_str!`/`include_dir!`) for query terms and
returns the matching sections as spec-excerpt context (folded into the rig
`CompletionRequest` by `agent/request.rs`, §6.1). **Marked `[R5]` — the
within-Stage-C release valve.** It is a Phase-1 stopgap (→ semantic search in agentic-Phase-3,
`repl-embedded-agent.md §9`); the acceptance criterion ("spec-grounded answer") is met by the
primer (§7.1) + the harvest (§5) even without spec-grep, because the primer carries the
constrained-function-over-`Num` idiom and the harvest carries the session's `Num` impls.
Trail into S89 if Wave 2 runs hot — the MVP acceptance holds without it.

---

## 8. `[R5]` Telemetry skeleton (§4.5)

`agent/telemetry.rs` — log each pull (a "miss" — the push didn't carry what the agent
needed) with its category (compensatory vs legit-deep-dive, `repl-embedded-agent.md §4.5`).
**Marked `[R5]` — the within-Stage-C release valve.** It has **no Phase-1 consumer** —
the consumer (push/primer curation) is agentic-Phase-3. The skeleton is: a `Vec<PullLog>`
on `AgentState`, append-on-pull, with a future hook to dump/aggregate. Trail into S89 if
the wave runs hot. (Designing it now keeps the §4.5 instrument-compensation loop's seam
ready; building it now buys nothing this sprint.)

---

## 9. Reverse-query commands `/refs` / `/tests-for` (LLM-FREE — Stage B, default build)

These are **NOT gated** — LLM-free, in the **default (non-agent) build**, useful to humans
too (`repl-embedded-agent.md §4.4` corollary — "the agent grows the REPL for everyone").
The agent reaches for them as pull-tools (§4.2), but they stand alone.

### 9.1 Semantics

- **`/refs <sym>`** — list the symbols whose bodies reference `<sym>` (reverse of the
  forward name → source/sig/doc introspection). Scope: the in-memory modules.
- **`/tests-for <sym>`** — list `test-*` functions (the test-discovery shape: `test-`
  prefix + `(Fn [] (Option String))` signature, per `src/CLAUDE.md §"Test discovery"`)
  whose bodies reference `<sym>`. A specialization of `/refs` filtered to test fns.

### 9.2 Mechanism — on-demand scan, NO maintained index

Today's introspection is **forward** (name → sig/doc/source); these are **reverse**
queries int does not have (`repl-embedded-agent.md §4.4` impl note). In a REPL the full
ASTs / sources are already in memory, so the cheap MVP is an **on-demand scan** over the
in-memory bodies — **no maintained reverse index, no invalidation in a mutating session**.
Promote to an index only if scan latency bites (it won't at REPL scale).

The scan (new `handle_refs` / `handle_tests_for` in `src/repl.rs`, dispatched from
`dispatch_command`):
```text
handle_refs(target):
  for (module, st) in shared.symbol_tables:
    for (sym, entry) in st.defined_symbols():
      body = get_introspection(FQSymbol{module, sym}).source   // or entry.ast for batch modules
      if body references `target` (token/AST-node match):
        results.push(FQSymbol{module, sym})
  render results in the universal :Type-style list (or "no references found")
```

Reference detection: prefer an **AST walk** over `Introspection.ast` / the
`Def.ast`-stored expr (`src/session_v4/types.rs:230` `ast: Option<Defn>`) for precision
(matches a `Symbol` node, not a substring); fall back to a source token-scan
(`Introspection.source`) when no AST is available (cache-restored modules carry no
introspection — §"Cache-restore" in `src/CLAUDE.md`). This is a quality/precision knob;
the MVP may ship the token-scan and refine to AST-walk if false positives bite. Either
way the scan is read-only over live state, recomputed per invocation.

### 9.3 ReplCommand wiring

`ReplCommand::Refs(&'a str)` + `ReplCommand::TestsFor(&'a str)` (`src/repl.rs:37`), arms
in `parse_slash_command` (`"/refs"`, `"/tests-for"`), arms in `dispatch_command`
(`src/repl.rs:416`) → `CommandResult::Final(self.handle_refs(arg))` / `handle_tests_for(arg)`.
**Unconditional** (no `#[cfg]`) — default build carries them. `/qa` covers them in the
default lane (the Step-3.1 plan notes default-lane LLM-free coverage). The `/help` text
(`src/repl.rs:111`) gains two lines.

---

## 10. Acceptance walk-through

`/ask "how do I define a constrained function over Num?"`:
1. `/ask` → `dispatch_command` → `agent_turn(text)` (§2.3). Feature on + key present.
2. `assemble_request` (§3.3): primer (§7.1 — carries the `(defn [Num a] …)` constrained
   idiom + the `:Type` convention) + harvest (§5 — the session's current module, any `Num`
   impls / numeric fns mentioned, exports of a `num`-ish module if present) + the user turn.
   `[R5]` if spec-grep is in: `/spec Num constrained` excerpt; if trailed, the primer
   carries enough.
3. `model.complete` (the `AgentModel` membrane over rig's `CompletionModel`, §6) → the model
   may pull `/info Num` or `/sig some-numeric-fn` (§4) — each
   renders as a visible REPL line and feeds back. (Pulls warm the push — §4.1.)
4. The model returns prose + a proposed `(defn …)` over `Num`. The agent renders the prose
   in its frame (§3.5) and the `(defn …)` **as a proposal — SHOWN, not submitted** (§3.2,
   read-only Advise). The user can copy it to the prompt to define it.

Acceptance met: spec-grounded (primer + harvest), session-aware (harvest), proposed
`(defn …)` shown not submitted (read-only). All five MVP-core pieces exercised; R5 pieces
optional.

---

## 11. Testability notes (Principle 5 — for `/qa`, not authored here)

- **Classifier routing** — table tests over `classify_for_agent` (compound form → Repl,
  prose → Agent, unclosed → Continuation, **known** bare atom/literal → Repl/introspection,
  **unbound** bare symbol → Agent — the §2.2 resolution discriminator). Feature-off: assert
  `/ask` → "agent not built in" and the `Err(other)` / unbound-bare-symbol paths are
  today's diagnostics (byte-identical guard — the whole `agent` module, incl.
  `classify_for_agent`, is `#[cfg]`-gated away).
- **`agent_turn` against a stub `AgentModel`** — because `agent_turn` dispatches through the
  object-safe **`AgentModel`** membrane (§6.0, §6.1), the loop is tested by implementing
  *that one-method trait* with a stub that returns a canned `ModelResponse` (no network, no
  rig): assert a tool-call response synthesizes the right command, runs it through
  `process_commands`, and feeds the result back; assert a write-command synthesis is refused
  (allowlist §4.2). (The stub impls `AgentModel` — the project-owned object-safe membrane —
  NOT rig's `CompletionModel` directly; rig's trait is dyn-incompatible and sits one layer
  below in the rig-backed impl. The stub captures every `AgentRequest` so a unit test can also
  assert WHAT the agent sent — primer present, harvest slice correct, tools = the allowlist.)
- **Harvest** — assert the push map under a tiny budget degrades per the §5.4 ladder
  (current-module pinned at the floor).
- **`/refs` / `/tests-for`** — default-lane, LLM-free: define fns referencing a symbol,
  assert the reverse scan finds them; assert `/tests-for` filters to `test-*` fns.
- All agent-feature tests behind `#[cfg(feature="agent")]` in a separate lane; the default
  suite stays agent-free (`/qa` Step-3.1 plan).

Coverage gaps to flag to `/qa` (FIXME `target: /qa` if not in the Step-3.1 plan): the
feature-off byte-identical guard for the classifier; the allowlist-refuses-writes guard.

---

## 12. What this design does NOT foreclose (S89 seams)

- **Build/Document write modes + `submit_repl_input`** — `agent_turn`'s loop has a clean
  insertion point (the `ToolCalls` arm) for a write tool, confirmation-gated; the read-only
  allowlist (§4.2) is the one place to widen.
- **The pre-flight validator + silent-repair (U5 = silent-repair-anything, S89-direction).**
  The substrate exists: Decision 44 cluster-atomic staging (commit-on-Ok / discard-on-Err).
  The validator is a typecheck-only **dry-run** over that staging (stage → check → discard,
  silent), `pub(crate)`, int-internal, **no facade/interface delta** (the `/arch` Phase-2
  ruling). This design keeps the staging-discard arm reachable (the MVP simply never writes,
  so it never stages — but it does not remove or wall off the path).
- **Module-preamble editing (Document mode)** — the MVP READS `module_preamble` (§5.2); the
  edit path is S89. No coupling foreclosed.
- **Push-transparency header (U4 = ambient for MVP, prunable header Phase 3)** — the harvest
  (§5) is ambient/silent this sprint; the header is a Phase-3 add over the same harvest map.

---

## 13. Cross-skill handoffs / FIXMEs

Filed as `design/arch/fixmes/NNNN-*.md` per the protocol (not authored from this design
pass; `/sprint` schedules):
- **`/repl`** (in flight, Step 3.2) — the agent-output frame role, `/ask` UX, the
  `--agent`/`--no-agent` §0.6 row, `/refs`/`/tests-for` UX, the U6 first-use disclosure
  wording (names **source excerpts**). This doc fixes the int mechanism; `/repl` owns the
  experience normatively.
- **`/arch`** — no new cross-crate edge, no facade move (Phase-2 confirmed). The one
  anticipated `cranelisp-types` field (`module_preamble`) already landed (FIXME 0428). The
  `rig-core` dep (optional, `agent`-feature-gated, §6.4) is int-private (no workspace edge);
  if a workspace-dep declaration is wanted, file `target: /arch` at implementation time.
- **`/qa`** — agent lane (`#[cfg(feature="agent")]`), classifier/loop/harvest tests, the
  default-lane `/refs`/`/tests-for` tests, the feature-off byte-identical guard.

---

# S89 — Phase 2 (rungs 5–6) + Cluster A render

The sections below extend the S88 Advisor-MVP design above with the Sprint 89 scope:
**Cluster A** (agent output rendering — 3 improvements + 1 defect), **Cluster B**
(rung 5 — Build mode + pre-flight validator), **Cluster C** (rung 6 — Document mode).
The S88 sections §0–§13 are intact and unchanged; this is accretion (Principle 9).

**Authority.** Scope + the binding constraints R1–R4 are fixed by the Phase-2 `/arch`
verdict (`sprints/SPRINT.md §"Architecture review (Phase 2)"`, U5 ratified in
`design/arch/repl-embedded-agent.md §6.4`). Every seam rungs 5–6 need **already exists**
from S88 — Build/Document/validator are *consumer* extensions of the int bounded context,
not new machinery (the `/arch` central claim). The S89 work is `pub(crate)`, int-private,
fully `#[cfg(feature="agent")]`; **zero new cross-crate edge, zero `cranelisp-types`
change, no `CACHE_SCHEMA_VERSION` bump** (R4). Where this doc and BC §6 / the ratified
`repl-embedded-agent.md` drift, those win — file FIXME `target: /arch`.

---

## 14. Cluster A — agent output rendering (`src/agent/render.rs`, R1/R2)

Four items surfaced from live S88 use (`sprints/SPRINT.md §"Agent output rendering"`):
three experience improvements + one defect. **R1 (binding): all of it is agent-output-only
and fully `#[cfg(feature="agent")]`.** The render code lives in a **new submodule
`src/agent/render.rs`** that *consumes* `src/pretty.rs::pretty_print` and `src/style.rs`,
**never modifies them, and is never reachable from the default REPL render path.** The
normal REPL already pretty-prints (no default-build work); feature-off `render.rs` does not
exist and the binary stays byte-identical (§1).

### 14.0 Where the agent renders today (the seam being extended)

`agent_turn` renders the model's terminal prose at `src/agent/mod.rs:234-235`:

```rust
ModelResponse::Done(prose) => {
    let _ = write!(stdout, "{}", crate::style::agent_prose(&prose));  // ← raw prose
```

`style::agent_prose` (`src/style.rs:72`) gutters each line with `▌` and (when colour is on)
styles only the **gutter** bright-magenta — the body passes through **verbatim**. So today
the model's markdown renders raw and any ```lisp fence is emitted unformatted. Agent-issued
*commands* + their results render separately, unframed, in `run_pull` (`src/agent/pull.rs:113-136`)
— that path is correct (§17.2) and is **not** touched by Cluster A.

The Cluster-A change is a single new step between the model response and `agent_prose`:
`render::render_agent_prose(&prose)` produces the framed, markdown-formatted, fence-pretty-printed
block, which `agent_turn` then writes. The §3.5 framing contract is unchanged — only prose
is framed; commands stay in `run_pull`.

### 14.1 `render.rs` shape (the new submodule)

| Fn (`pub(crate)`) | Responsibility |
|---|---|
| `render_agent_prose(prose: &str) -> String` | The Cluster-A entry. Splits the model's markdown into prose runs and ```lisp/```` ``` ```` fenced runs (§14.4); formats prose runs as terminal markdown (§14.3); routes lisp fences through `crate::pretty::pretty_print_str` (§14.5, Principle-7 reuse); re-assembles and wraps the whole in the `▌` agent frame via `style::agent_prose`. Replaces the bare `agent_prose(&prose)` call at `mod.rs:235`. |
| `markdown_to_terminal(run: &str) -> String` (private) | §14.3 — headings/lists/emphasis/inline-code → SGR roles drawn from the existing `style::Style` palette. Degrades under `--no-color` (the `styled()` short-circuit). |
| `split_fences(prose: &str) -> Vec<Run>` (private) | §14.4 — partitions the prose into `Run::Prose(text)` / `Run::Lisp(code)` by ```` ``` ```` fences, recognising the `lisp`/`cranelisp` info-string. |

`Run` is a tiny private enum local to `render.rs`. No type crosses a module boundary — this
is all int-private behind the feature gate.

### 14.2 Improvement 1 — agent-input prompt (distinct prompt prefix)

**Problem (SPRINT item 1):** agent-issued pulls / echoed turns render with no prompt prefix,
so the transcript cannot tell who typed what. Today `run_pull` echoes the synthesized command
bare (`pull.rs:116`: `writeln!(stdout, "{cmd}")`).

**Design.** Give agent-originated input a **distinct prompt glyph** so a pulled command reads
honestly as agent-issued (vs. the human `user>` prompt). The int mechanism: a new
`render::agent_input_prefix() -> String` consulted at the **two** echo sites where the agent
"types" — the pull-command echo in `run_pull` (`pull.rs:116`) and (S89) the Build-write
echo (§15.4). It prepends the agent-input glyph (coordinated with `/repl` — the glyph is a
`/repl`-owned normative choice; this doc fixes only that int routes both agent-echo sites
through one prefix fn so they cannot diverge). The prefix degrades under `--no-color` to a
plain-text marker (same `styled()` short-circuit as `agent_prose`). The glyph is **distinct
from** the `▌` prose gutter (commands are not prose — §17.2) and distinct from the human
prompt. **Coordination point flagged to `/repl`** (§19).

This is the one Cluster-A item NOT inside `render_agent_prose` — it is a one-line prefix at
the command-echo sites, kept in `render.rs` so the whole agent-render surface is one module.

### 14.3 Improvement 2 — markdown formatting of prose (within the §10.3 frame)

**Problem (SPRINT item 2):** the model returns markdown; it renders raw. **Design.**
`markdown_to_terminal` formats the common inline/block markdown the model emits —
headings, bullet/numbered lists, `**bold**`/`*emphasis*`, and `` `inline code` `` — into
terminal SGR using the **existing** `style::Style` palette (`Bold`, `Italic`, etc.); it does
NOT introduce a new colour mode or writer target (R2 — see §14.6). It is a small, bounded
formatter (Principle 6 — complexity budget): it handles the markdown the model actually
produces, not a full CommonMark engine. The formatted prose then flows through
`style::agent_prose` so each line still carries the `▌` gutter — markdown formatting lives
**inside** the §10.3 agent-prose frame, not beside it. **Degrades under `--no-color`:**
every span goes through `style::styled`, which short-circuits to plain text when
`is_color_enabled()` is false (`style.rs:133`), so `--no-color` yields gutter + plain
markdown-stripped-to-text. **Coordination point flagged to `/repl`** (the markdown→frame
composition is a §17.2 experience detail — §19).

### 14.4 / 14.5 Improvement 3 — route ```lisp fences through `pretty_print` (Principle 7)

**Problem (SPRINT item 3):** a ```` ```lisp ```` block inside the model's markdown renders
as a raw fence. **Design.** `split_fences` partitions the prose by ```` ``` ```` fences;
each run whose info-string is `lisp` or `cranelisp` is a `Run::Lisp(code)`. Its body routes
through the **existing S24 S-expression pretty-printer** — `crate::pretty::pretty_print_str`
(`src/pretty.rs:33`, the string entry that parses then syntax-highlights + indents, with the
token-fallback for non-round-tripping display strings). This is **clean Principle-7 reuse**:
the same printer `/source`/`/sexp` already use (`repl.rs:966/982`), consumed not modified.
The pretty-printed block is re-wrapped in the prose frame (it is part of the agent's *answer*,
not a pulled command, so it lives inside `▌`) — distinguishing it from §17.2's unframed
agent-issued commands by **origin**: a fence in the model's prose is the agent *showing* code
(framed); a `run_pull` echo is the agent *running* a command (unframed). A non-lisp fence
(e.g. ```` ```sh ````) stays a `Run::Prose` and is markdown-formatted as a literal block.

### 14.6 The DEFECT — pretty-printer leaks raw ANSI escape codes on agent output (R2)

**Symptom (SPRINT item 4):** when the pretty-printer renders agent output, ANSI colour codes
appear as **literal text** (`\x1b[36m…`) instead of rendering. **Repro is `/qa`'s to author**
(a narrow failing-not-ignored Lane-A test — §17); this section is the int-internal root-cause
hypothesis + the fix shape, bounded by **R2: do NOT add a color-mode / writer-target parameter
to `pretty_print` or any `cranelisp-types` printer.** The bug is a wiring mismatch, not a
missing param — adding one would be Principle-8 interim machinery for a wiring bug.

**Root-cause hypothesis (the wiring mismatch).** Colour is a **global** decision owned by
`src/style.rs::is_color_enabled()` — a process-wide `OnceLock` set once at startup by
`init_color(no_color_flag)` (`style.rs:88-100`). `styled()` (`style.rs:133`) keys on it:
colour-on ⇒ wrap in SGR; colour-off ⇒ return the text **verbatim**. There is exactly one
colour gate and it is correct. So a *literal* `\x1b[…m` reaching the screen means **styled
text was produced for one writer target and then routed to a different one** — the classic
double-styling / mis-routing. Two concrete candidates, both wiring (the `/dev`+`/qa` repro
will distinguish which — likely (a)):

  (a) **Double-routing already-styled text through a second styler.** `pretty_print_str`
      returns SGR-bearing text when colour is on. If a Cluster-A path (or the existing
      `run_pull` result echo) takes that already-styled string and passes it through a
      *second* formatting pass that escapes or re-wraps it — e.g. a markdown formatter that
      treats `\x1b` as literal body text, or a fence-detector that does not route the lisp
      run to `pretty_print` and instead emits the raw styled-or-literal fence — the SGR
      bytes survive as visible text. **Fix:** style **once**, at the leaf. `render.rs` must
      produce each run's final styled text exactly once (markdown leaf OR `pretty_print`
      leaf), never re-style an already-styled run; the frame wrapper (`agent_prose`) only
      prefixes gutters and MUST NOT re-escape the body. This is the §14.1 contract made
      load-bearing: `render_agent_prose` is the single styling site for prose.

  (b) **Writer-target mismatch on the `OnceLock` in a test/sub-context.** If agent output
      is assembled in a context where `init_color` ran with a different value than the
      writer's actual TTY-ness (e.g. styled-for-TTY text captured into a pipe), literal SGR
      leaks. **Fix:** the agent render path consults the **same** `is_color_enabled()` gate
      as every other writer (it already must — `styled` is the only styler); the fix is to
      ensure no agent path *constructs* SGR through any route other than `style::styled`
      (so the global gate is always honoured). No new param — just funnel all agent styling
      through `style::styled`.

**The fix is `style.rs`/`pretty.rs` wiring + `render.rs` discipline, no signature change**
(R2). `pretty_print`/`pretty_print_str` keep their exact current signatures; `cranelisp-types`
printers are untouched; the correction is "style once at the leaf, honour the one global
gate, never re-style." **`/dev`'s mandatory unit test** pins the leaf-styling invariant at
the seam (a `render_agent_prose` output over a ```lisp fence contains no *literal* `\x1b`
substring when colour is off, and well-formed SGR when on); **`/qa`'s e2e repro** pins the
observable end-to-end symptom (no literal escape codes anywhere; `--no-color` clean).

---

## 14A. S107 render/streaming design (0554 / 0556 / 0555)

Three S107 findings extend Cluster A's render surface. All stay agent-output-only, fully
`#[cfg(feature="agent")]`, int-private (no `cranelisp-types` change — Phase-2 confirmed). The
normative contracts are `repl/spec.md` §3.11 (0554), §17.2 item 3 / §17.13.2 (0556), and
§17.22 (0555). **Sequencing is load-bearing (Phase-2): 0556 lands before 0555** — the streaming
renderer consumes the code-vs-prose framing split 0556 defines.

### 14A.1 — 0554: aligned `let`/`match` fences (reuse, no agent-side work)

The agent's ```lisp fences already route through `crate::pretty::pretty_print_str` (§14.5,
Principle-7 reuse — the same printer `/sexp`/`/source` use). The 0554 pair-aware layout is a
**structural change inside `pp` itself** (`src/pretty.rs`), designed in
`design/int/terminal-styling.md` §"Aligned `let`/`match` pair layout". Because the agent
consumes that printer unmodified, agent-emitted `let`/`match` fences inherit the aligned
columns with **zero `render.rs` change**. This is the whole point of the §14.5 reuse seam: fix
the printer once, every consumer (introspection *and* the agent) is fixed. The only S107
render.rs coupling is that a lisp fence must now emit **un-guttered** (§14A.2) so its bytes are
byte-identical to `pretty_print_str` output (the §3.11 / §17.13.2 MUST).

### 14A.2 — 0556: render-side gutter split (code fences copy-clean)

**Problem (`repl/spec.md` §17.2 item 3 / §17.13.2 [S107]).** Today `render_agent_prose` builds
one `body` string (prose runs markdown-formatted + lisp runs pretty-printed, concatenated),
then wraps the **whole** thing in `style::agent_prose`, which prefixes **every** line — prose
*and* code — with `▌ `. A multi-line copy of a ```lisp block therefore drags `▌ ` into the
clipboard on each line and the example cannot be re-run verbatim (FIXME 0556).

**Design — gutter per-run at the leaf, not once over the body.** The split lands in
`render_agent_prose`: instead of guttering the assembled body once, gutter **prose runs only**,
and append **lisp runs un-guttered**. `style::agent_prose` stays exactly as-is (it remains the
prose gutterer); it is simply no longer called over a body that contains code. This is the
Phase-2 **render-side structural split** — NOT the rejected "keep the gutter, expose an
un-guttered copy elsewhere" alternative (there is one render path; the code bytes on screen
*are* the copyable bytes).

Two shared leaf helpers make the emission a single source of truth (they are reused verbatim by
the streaming renderer §14A.3, which is how the differential invariant is guaranteed):

| Helper (`render.rs`, private) | Emits |
|---|---|
| `push_prose_run(out, text)` | `style::agent_prose(&markdown_to_terminal(text))` — every line guttered `▌ `, markdown-formatted (§14.3). |
| `push_lisp_block(out, code)` | `crate::pretty::pretty_print_str(code.trim_matches('\n'))` + a trailing `\n` — **no gutter on any line**, byte-identical (colour-off) to `/sexp`/`/source`. |

`render_agent_prose` becomes:

```
for run in split_fences(prose):
    Run::Prose(text) => push_prose_run(&mut out, &text)     // guttered
    Run::Lisp(code)  => push_lisp_block(&mut out, &code)    // UN-guttered — the 0556 fix
```

Notes for `/dev`:
- **Both `markdown_to_terminal` and `agent_prose` are line-independent** (each formats/gutters
  per `lines()`), so `push_prose_run` over a whole multi-line run equals concatenated
  per-line calls — the property the streaming path (§14A.3) relies on.
- **Empty-run hygiene.** `agent_prose` emits a lone gutter line for an *empty* body; guard so
  an empty prose run (e.g. a fence immediately at buffer start) contributes no stray `▌` line.
- The surrounding prose's gutter now marks the code block's boundary by its **absence** on the
  code lines (§17.2 item 3) — no caption line is emitted for the MVP (the spec permits, does
  not require, one).
- `/qa` re-baselines the non-TTY agent golden (§17.13.3) + the §14.6 leaf-styling guard —
  flagged, not authored here.

### 14A.3 — 0555: streaming the terminal answer (S1–S5)

The arch S1–S5 decomposition (`sprints/SPRINT.md` §"Streaming"), concretised. The whole feature
is agent-gated + int-internal; the only cross-cutting mechanism is the new `AgentModel` membrane
method (S1) — **not** a `cranelisp-types` type. Normative: `repl/spec.md` §17.22.

#### S1 — the neutral streaming membrane (`agent/types.rs`)

Add one method to the object-safe `AgentModel` trait, with a **default impl that delegates to
`complete`** (whole prose as one delta) so every non-streaming impl — the stub, Ollama, any
future provider — keeps working unchanged (bounds the blast radius; the Phase-2 fallback
constraint):

```rust
pub trait AgentModel: Send {
    fn complete(&mut self, request: &AgentRequest) -> Result<ModelResponse, String>;

    /// Stream the terminal answer's prose as neutral text deltas into `sink`,
    /// returning the SAME final `ModelResponse` `complete` would. Default: no real
    /// streaming — run `complete`, emit the whole `Done` prose as one delta.
    fn complete_streaming(
        &mut self,
        request: &AgentRequest,
        sink: &mut dyn FnMut(&str),
    ) -> Result<ModelResponse, String> {
        let resp = self.complete(request)?;
        if let ModelResponse::Done(prose) = &resp {
            sink(prose);            // one delta = the whole answer
        }
        Ok(resp)                    // ToolCalls: nothing streamed (tool-call turns not streamed)
    }
}
```

The sink carries **raw model text** (markdown), not rendered bytes — the renderer (S3) owns
formatting. `rig` types stay below the membrane. The default impl IS the "one-delta case"
that makes the differential invariant (§17.22) trivially hold for non-streaming providers.

#### S2 — provider streaming impl (`agent/provider.rs`)

`RigModel::complete_streaming` mirrors `complete` but drives `self.model.stream(rig_req)` in
one `block_on`, forwarding **text** deltas and reusing the existing `lower_response` to build
the final `ModelResponse` from the stream's aggregated `choice`:

```rust
fn complete_streaming(&mut self, request, sink) -> Result<ModelResponse, String> {
    crate::agent::trace::emit_request(request);
    let rig_req = /* identical build to `complete`: preamble + history + prompt + tools */;
    let choice = self.runtime.block_on(async {
        use futures::StreamExt;                                   // see dep note below
        let mut stream = self.model.stream(rig_req).await
            .map_err(|e| format!("stream failed: {e}"))?;
        while let Some(item) = stream.next().await {
            match item.map_err(|e| format!("stream error: {e}"))? {
                StreamedAssistantContent::Text(t) => sink(&t.text), // forward prose deltas live
                _ => {}                                             // tool-call / reasoning deltas: accumulated in stream.choice, NOT streamed
            }
        }
        Ok::<_, String>(stream.choice.clone())                    // aggregated at Poll::Ready(None)
    })?;
    let lowered = agent_request::lower_response(choice);          // SAME lowering as `complete`
    crate::agent::trace::emit_response(&lowered, request.turn);
    Ok(lowered)
}
```

- **Only `Text` deltas reach `sink`** — rig accumulates tool-call/reasoning items into
  `stream.choice` (verified: `rig_core::streaming` `poll_next` sets `choice` on stream-end),
  which `lower_response` turns into `ToolCalls` or `Done`. So a **tool-call turn streams no
  prose** (the §17.22 constraint) yet still returns the right `ModelResponse`; incidental
  narration text before a tool call renders through the same renderer (benign, in-contract —
  it is not the "streamed tool-call delta assembly" that is deferred).
- **Dependency note (the one Cargo edit `/dev` makes).** `.next()` needs `futures::StreamExt`
  in scope. `futures` is currently transitive-only (present in `Cargo.lock`); add it as a
  **direct, agent-gated optional dep** — `futures = { version = "…", optional = true }` and
  `agent = ["dep:rig-core", "dep:tokio", "dep:serde_json", "dep:futures"]`. This is int-internal
  and feature-gated — **no `cranelisp-types` / workspace-edge change** (Phase-2 invariant
  intact). (Alternatively `tokio-stream::StreamExt`, but `futures` is already downloaded.)
- **The `MockModel` real `stream` impl (`provider.rs` tests, ~L387).** Replace the
  `unimplemented!("…never streams…")` with a real impl so the rig-boundary loop test exercises
  streaming: return a `StreamingCompletionResponse::stream(inner)` whose `inner:
  StreamingResult<MockRaw>` is a boxed stream yielding one `RawStreamingChoice::Message(text)`
  per scripted text chunk followed by a `RawStreamingChoice::FinalResponse(MockRaw)` — so the
  aggregated `choice` lowers identically to the `completion` path. This makes the rig test
  assert both the streamed deltas AND the wire-valid continuation request.

#### S3 — the `StreamingRenderer` state machine (`agent/render.rs`)

A stateful renderer that consumes **raw markdown deltas** and emits rendered bytes
incrementally, matching `render_agent_prose`'s output when the full text is concatenated. It is
line-buffered (partial trailing line withheld until its newline — §17.22 line-granular) and
fence-aware (buffer within an open ```lisp fence, flush formatted at fence-close).

```rust
struct StreamingRenderer {
    line_buf: String,                 // partial trailing line, no newline yet
    fence: Option<(bool, String)>,    // Some(is_lisp, body) ⇒ inside a fence (state: inside-fence)
}
```

State machine (two states: **outside-fence** = `fence.is_none()`, **inside-fence** =
`fence.is_some()`):

```
push(delta, out):                                   // called per model delta
    line_buf += delta
    while let Some(nl) = line_buf.find('\n'):
        line = line_buf.drain(..=nl) minus '\n'
        process_line(line, out)                     // complete line only

process_line(line, out):
    if line.trim_start().strip_prefix("```") is Some(info):
        match fence.take():
            None            => fence = Some((info∈{lisp,cranelisp}, ""))   // OPEN — emit nothing
            Some((lisp,buf)) => if lisp { push_lisp_block(out, &buf) }      // CLOSE — un-guttered (§14A.2)
                                else     { push_prose_run(out, &buf) }      //   non-lisp fence = literal prose block
    else:
        match fence.as_mut():
            Some((_, buf)) => { buf += line; buf += "\n" }                  // INSIDE — buffer, no echo
            None           => push_prose_run(out, line)                     // OUTSIDE — gutter + format LIVE, per line

finish(out):                                        // end of the turn's stream
    if !line_buf.is_empty() { process_line(take(line_buf), out) }           // flush partial trailing line
    if let Some((lisp,buf)) = fence.take():                                 // unterminated fence at EOF
        if lisp { push_lisp_block(out, &buf) } else { push_prose_run(out, &buf) }
```

- **Byte-identity with `render_agent_prose` is structural, not hoped-for.** `process_line`
  reuses the **same** `push_prose_run` / `push_lisp_block` leaves (§14A.2) and the **same**
  fence-classification predicate as `split_fences`. Prose is line-independent (§14A.2 note), so
  per-line `push_prose_run` concatenates to the whole-run render; lisp is buffered and flushed
  whole through the identical `pretty_print_str`. **Recommended durable end-state (Principle 7 /
  Principle 18 — enforce the invariant by construction):** re-express `render_agent_prose(text)`
  as "drive one `StreamingRenderer` with `text` as a single delta into a `String` sink, then
  `finish`." Then there is literally one render path and the §17.22 differential invariant
  cannot drift. (0556 lands the run-based split first per sequencing; 0555 then unifies onto the
  renderer.) To keep `split_fences`' classifier single-source, factor its per-line
  `strip_prefix("```")` + info-string parse into a shared `classify_fence_line(line)` both call.
- **Line-granularity** is what preserves the invariant while streaming: sub-line/token flushing
  is explicitly *not* required (§17.22), and would break byte-identity for a partially-formatted
  markdown span.

#### S4 — `agent_turn` wiring (`agent/mod.rs`)

`agent_complete` (the model-call shim, `mod.rs:396`) grows a streaming sibling; the loop drives
S3 through the S1 sink:

```
// in the loop step, replacing the `agent_complete` call + the Done render:
let mut renderer = StreamingRenderer::new();
let resp = {
    let mut sink = |delta: &str| renderer.push(delta, stdout);
    self.agent_complete_streaming(&req, &mut sink)?   // borrows model like agent_complete
};
renderer.finish(stdout);                              // flush partial line / open fence
match resp {
    ModelResponse::Done(prose) => {
        // DO NOT call render_agent_prose again — the renderer already emitted it live.
        self.agent.as_mut().map(|s| s.record_assistant(&prose));   // unchanged: transcript + loop continuation
        return;
    }
    ModelResponse::ToolCalls(calls) => { /* unchanged pull path — renderer flushed any narration */ }
}
```

- **`agent_complete_streaming`** is the borrow-confining shim (mirrors `agent_complete`): take
  `self.agent.model` mutably for the call. The sink closure borrows `renderer` + `stdout`; the
  model borrow is disjoint (distinct field), so the existing take-the-handle-out discipline
  still applies.
- **The returned `ModelResponse` is unchanged** — `record_assistant`, the transcript wire-valid
  invariant, the tool-call/pull path, and the give-up/budget tail all keep working on the same
  value. Streaming changes *how the Done prose reached the screen*, nothing about the loop's
  control flow or state.
- **Trace/log fire on the accumulated text** — `RigModel::complete_streaming` calls the same
  `trace::emit_request`/`emit_response` (on the lowered final response, §S2) as `complete`, so
  the §17.21 trace + §17.20 log records are byte-for-byte what they are today (the accumulated
  answer, not per-delta) — the log↔trace `turn` join is unaffected.
- **The Done arm no longer calls `render_agent_prose`** — that is the one behavioural edit in
  the loop; forgetting it double-renders. The dormant/error/tool-call/budget paths are untouched
  (they never streamed).

#### S5 — the differential-invariant hook (for `/qa`)

The invariant (§17.22 MUST): streamed-concatenated output == `render_agent_prose` over the same
complete text (colour-off). The hook `/qa` asserts against:

- Feed a **multi-delta** answer through a `StreamingRenderer` into a `String` sink (splitting the
  same full text at arbitrary byte boundaries — mid-line, mid-fence, mid-span), `finish`, and
  compare to `render_agent_prose(full_text)`. Equal for every split ⇒ streaming changed only
  *when* bytes emit, never *which*.
- Because the recommended S3 end-state expresses `render_agent_prose` AS a one-delta drive of the
  same renderer, this test degenerates to "delta-splitting is invariant" — the exact property at
  risk (partial-line / partial-fence buffering bugs). The stub emits multiple `Done` deltas via
  the S1 default path's single delta OR (with a streaming-capable stub) several — either way the
  concatenation MUST match.
- **`/dev`'s mandatory unit tests** (per `src/CLAUDE.md`) pin, at the seam: (a) a fence split
  across two deltas still flushes one whole pretty-printed un-guttered block at close; (b) a
  prose line split across deltas emits exactly one guttered line; (c) colour-off output carries
  no literal `\x1b` (the §14.6 leaf guard, now over the streaming path too).

---

## 15. Cluster B — Build mode: the confirm-gated write arm (rung 5, R3)

The agent's **first write path**. **R3 (binding): the submitted form re-enters via the
existing `self.process_commands` / `self.eval` cluster-atomic staging path `main.rs` uses —
no new eval entry, no parallel submit path.** The §4.2 read-only allowlist is **widened in
one place** to admit the confirm-gated write while read-only-by-default stays the structural
floor.

### 15.1 The write arm is one widening of the §4.2 allowlist (R3)

Today the consent boundary is structural: `pull::synthesize_command` (`src/agent/pull.rs:72`)
rejects any tool not in the read-only `ALLOWLIST` (`pull.rs:29`), so a write is **unconstructable**
(§4.2). Build mode adds **exactly one** writing tool — `submit` (it carries a form string as
its argument, e.g. `(defn double [x] (* x 2))`) — and admits it through **one new arm**, not by
loosening the allowlist's read-only floor:

- The read-only `ALLOWLIST` is **unchanged** — reads stay auto-run (§17.3). `submit` is NOT
  added to it.
- `synthesize_command` keeps refusing everything not read-only **by default**. A new,
  separate gate recognises `submit` and routes it to the **confirm-gated write arm**
  (§15.2). A `submit` that does not pass the confirm-gate is refused exactly as a non-read
  command is today — so **a non-confirmed / disallowed write stays unconstructable** (the
  structural floor R3 requires).
- Concretely: `run_pull` (`pull.rs:96`) gains a pre-dispatch match — if `call.name == "submit"`,
  route to `run_submit` (§15.2, the confirm-gated arm); else fall through to the existing
  read-only `synthesize_command` path verbatim. The read path is byte-unchanged; the write
  path is the single new branch. This is "widen the allowlist in one place" — the one place
  is the `run_pull` head, and the floor (read-only-by-default refusal) is untouched.

`submit` is added to `tool_defs()` (`pull.rs:49`) **only when Build mode is active** for the
turn (so a read-only Advise turn never offers it). Whether Build is offered is a turn-level
flag (a future U-knob); for S89 the simplest correct shape is: `submit` is always in the
tool-defs but always confirm-gated — the gate, not the offer, is the consent boundary
(matching §17.3 "confirm each submission"). The +neg guard (a `submit` without confirm does
not reach `eval`) is what `/qa` pins.

### 15.2 The confirm gate (int mechanism; wording → `/repl`)

When the agent emits `submit <form>`, the int mechanism:

1. **Render the proposed form** as a normal definition echo (unframed, §17.2 / §17.3.1) —
   the exact line the user would approve, through the agent-input prefix (§14.2) so it reads
   as agent-issued.
2. **Capture consent.** The int-level mechanism is a **synchronous prompt at the eval thread**:
   `agent_turn` runs on the REPL-cadence `&mut CompilerSession`, synchronous to the user's
   Enter (§3.2), so the confirm read is an ordinary blocking line-read at the same cadence —
   the user types `y`/`n` (or equivalent) at the prompt. This holds BC §6.3 (REPL-cadence
   consumer, not a new state window): the confirm is a prompt boundary, not a second cadence.
   The **exact prompt wording** ("submit this definition? [y/N]") is deferred to `/repl` (the
   §17.3 confirm-and-show experience — §19). This doc fixes that int captures consent via a
   synchronous prompt at the existing cadence, not an async dialog or a new state window.
3. **On decline:** render nothing to the session; feed a "declined" tool-result back to the
   model (so it knows the form was not submitted) and continue the turn. Session state is
   unchanged — structurally identical to the §17.3.1 "proposed, not submitted" floor.
4. **On confirm:** route the form through `self.process_commands(&form, stdout)` (§15.3) —
   the **same** path a user keystroke uses.

`run_submit(&self, call, stdout)` is the new `pub(crate)` method in `pull.rs` (sibling to
`run_pull`), holding steps 1–4. It is the single confirm-gated write site.

### 15.3 Submission re-enters via `process_commands` / `eval` (R3 — no new eval entry)

On confirm, `run_submit` calls `self.process_commands(&form, stdout)` — for a `(defn …)`
this returns `CommandResult::Compile(src)`, which **the caller must drive through `eval`**
exactly as the `main.rs` read loop does (`main.rs:313-326`: `CommandResult::Compile(src) =>
s.eval(&src) …`). Two placement options, both reusing the existing path (R3):

- **(preferred) `run_submit` drives `eval` itself**, mirroring `main.rs:315`: on
  `Compile(src)` it calls `self.eval(&src)`, renders the result via `format_eval_result`
  (unframed — it is normal REPL output, §17.2), and on a successful def triggers
  `regenerate_backing_file()` (`main.rs:325`) so the new definition persists (§15 of the
  spec). This inherits **commit-on-Ok / discard-on-Err** cluster-atomic staging (Decision 44),
  error recovery, and backing-file regeneration **for free** — the agent's write is, at the
  staging layer, indistinguishable from a user keystroke.
- The tool-result fed back to the model is the `format_eval_result` text (the new symbol's
  `:Type name` echo) on success, or — **per the validator (§16) this should never be a raw
  compile error**, because the validator runs *first* and only clean code reaches `submit`.

**No new eval entry, no parallel submit path** (R3): `run_submit` is a *caller* of the
existing `process_commands`→`eval`→staging chain, structurally the same caller `main.rs` is.
The "one new internal seam" the master design names (`repl-embedded-agent.md §7.5`) is the
validator dry-run (§16), **not** a new submit path — submission is plain reuse.

### 15.4 Read-only-by-default stays the structural floor

The invariant R3 protects: **a write is reachable only past the confirm-gate.** Structurally:
the read `ALLOWLIST` excludes writes (unchanged); `submit` is the only writing tool and it is
unconditionally routed through `run_submit`'s confirm gate; an un-confirmed `submit` mutates
nothing (it never reaches `eval`). So "auto-approve reads only" (§7.4, §17.3) is preserved by
construction — the MVP's allowlist-exclusion floor is extended, not replaced, by a
confirm-gate floor for the one write tool. `/sh` and any other non-read, non-`submit` tool
stays refused at `synthesize_command` exactly as today.

---

## 16. Cluster B — pre-flight validator + silent-repair-anything (U5, R3)

Before generated code is shown or submitted, it is validated on staging and **silently
repaired on any failure** — the user structurally never sees an agent compile failure.
**R3 (binding): the stage→check→discard loop reuses the existing `check_forms`
discard-on-Err arm — `pub(crate)`, int-internal, no new public surface / facade delta (R3/R4).**
**U5 (binding): silent-repair *anything*** — on **any** `Err` (parse OR type), no
error-classification branch, feed the actual compiler error back to the model and retry.

### 16.1 The dry-run seam already exists: `process_cluster_with_staging` (R3)

The validator is the **typecheck-only dry-run** the master design names as "the one new
internal seam" (`repl-embedded-agent.md §7.5`). The substrate is the existing cluster-atomic
staging function `worker::process_cluster_with_staging` (`src/worker.rs:243-291`): it builds a
**fresh staging `SymbolTable`**, runs `cranelisp_typecheck::check_forms` over it via
`SymbolTableAccess::cluster`, and — crucially —

- on `Ok` it **commits** staging into live (`commit_staging_to_live`, `worker.rs:279`),
- on `Err` the staging table **drops** (atomic discard, live unchanged — `worker.rs:289`).

The validator needs the **discard arm without the commit** — a *check-only* run: stage →
`check_forms` → **always discard** (never commit), returning `Ok(())` / `Err(compiler_error)`.
The existing function's two halves (build-staging + `check_forms` over `SymbolTableAccess::cluster`,
`worker.rs:258-270`) are exactly the dry-run; the commit (`worker.rs:279`) is what the
validator omits. The cleanest int-internal shape (no signature change to the existing fn —
R4):

```rust
// src/worker.rs (pub(crate), #[cfg(feature="agent")]) — the typecheck-only dry-run.
// Reuses the EXACT build-staging + check_forms body of process_cluster_with_staging,
// minus commit_staging_to_live. Staging always drops (the discard arm, every path).
pub(crate) fn validate_forms_dry_run(
    symbol_tables: &DashMap<…>, module_aliases, prelude_fallback,
    module: &ModuleFullPath, working_program: &[TopLevel],
) -> Result<(), CranelispError> {
    // build fresh staging  (worker.rs:258-261)
    // check_forms over SymbolTableAccess::cluster  (worker.rs:264-270)
    // match: Ok(_) => Ok(()),  Err(Gap) => Err(...)?,  Err(e) => Err(...)   // NO commit
}
```

The frontend half (parse + macro-expand the model's code into `Vec<TopLevel>`) reuses the
existing `worker::build_program_compat` / the build-form boundary the REPL already uses
(`src/CLAUDE.md §"Cluster-Atomic Orchestration"`), so "parse OR type" failure (U5) surfaces
uniformly: a parse/expand error is an `Err` from the build half; a type error is an `Err`
from `check_forms`. **No error-classification branch** (U5): the validator does not
distinguish them — *any* `Err` triggers repair. This is exactly why silent-repair-anything
needs *less* machinery than the superseded "surface type errors" lean (`repl-embedded-agent.md
§6.4`): one `Result`, one discard, one re-prompt.

**No facade/interface delta (R3/R4):** `validate_forms_dry_run` is a `pub(crate)`
int-internal fn that reuses the same `check_forms` call and the same staging shape the live
path uses. `cranelisp-types` is untouched; no `public-api.txt` moves (int is a binary, no
baseline); no `CACHE_SCHEMA_VERSION` bump (the dry-run never persists).

### 16.2 The repair loop (silent, capped, in `agent_turn`'s write path)

The repair loop lives where the write originates — `run_submit` (§15.2), before the confirm
gate and before any echo:

```text
validate_and_repair(form, model):
  for _ in 0..MAX_REPAIR_ITERATIONS:                 // cap — §16.3
    parsed = build_program_compat(form)?or capture-as-Err
    match validate_forms_dry_run(parsed):            // §16.1 — stage→check→DISCARD
      Ok(())          -> return Ok(form)              // clean; proceeds to confirm+submit (§15)
      Err(compiler_error):
        // SILENT: nothing rendered to the transcript (the user never sees this).
        feedback = neutral-vocabulary message carrying compiler_error.to_string()
        record a HIDDEN repair turn on the transcript (NOT rendered to stdout)
        resp = model.complete(assemble_request_with(feedback))   // §3.2 membrane
        form = extract proposed code from resp (Done prose / a submit tool-call)
  return Err(give-up)                                // §16.4
```

Key properties:
- **Silent (U5, the load-bearing contract).** The broken intermediate is **never written to
  `stdout`** — neither the broken form nor the compiler error reaches the transcript. The
  repair model↔model exchange is internal: the feedback + the model's retry are recorded on
  the transcript *as agent state* (so the next real turn has context) but **not rendered**.
  Only the final clean form reaches the echo (§15.2 step 1) and the confirm gate. "The user
  structurally cannot see an agent compile failure" is enforced by *where the render call is*:
  rendering happens only after `validate_and_repair` returns `Ok(clean_form)`.
- **Reuses the membrane.** The retry `model.complete` is the same `AgentModel::complete`
  (§6.0) `agent_turn` already drives — so the repair loop is driven by a **stub `AgentModel`**
  in tests (§16.5, Lane A) with zero network.
- **Stage→check→discard only.** `validate_forms_dry_run` never commits, so a failed
  validation leaves live state untouched (no staging leak) — and a *successful* validation
  also discards (it is a *dry* run); the actual commit happens later, on confirm, through
  `process_commands`→`eval` (§15.3). The validator proves "this will at least parse/typecheck";
  the submit re-runs the real staged commit. (Running the check twice — once dry, once for
  real — is the accepted cost of reusing the existing commit path verbatim rather than
  threading a "validated" flag through `eval`; Principle 6 — the duplication is one extra
  typecheck at REPL cadence, cheap, and keeps R3's "no new eval entry" exact.)

### 16.3 The retry cap and 16.4 the give-up behaviour

- **Cap.** `MAX_REPAIR_ITERATIONS` — a `const` in `pull.rs`/`mod.rs`, sibling to the existing
  `MAX_TURN_ITERATIONS = 8` (`mod.rs:36`). Suggested **3** (a tuning knob, not architecture —
  the primer lowers the retry rate, the gate guarantees the floor; `repl-embedded-agent.md §6.2`).
- **Give-up.** When the cap is hit without a clean form, the agent does **not** submit broken
  code and does **not** show a compile error (U5). It renders, in the prose frame, a single
  honest notice ("I couldn't produce code that compiles cleanly here") and continues the turn
  read-only — i.e. it degrades to the §17.3.1 "proposed, not submitted" floor (the last
  attempt MAY be shown as a *proposal* the user can hand-fix, clearly marked not-submitted).
  The exact give-up wording is `/repl`-owned (§19); this doc fixes that give-up never submits
  and never surfaces a raw compiler error.

### 16.5 Testability hook (Lane A — `/qa`, R3 testability)

The repair loop is **drivable by a stub `AgentModel`** deterministically (Principle 5,
`tests/plan/agent-testing-strategy.md §3.4`): the stub is scripted **broken-then-fixed** —
turn 1 returns a `submit`/`Done` whose form fails `validate_forms_dry_run`; a later scripted
turn returns clean code that passes. The test (Lane A, `#[cfg(feature="agent")]`) asserts:
broken-generation-repaired (the loop stages→checks→discards then re-prompts), only-clean-
reaches-session (after the loop only the clean form is committed; the broken intermediate
never committed), and **+neg: the user never sees the broken intermediate** (the broken form
+ compiler error are absent from the rendered transcript — the U5 silent contract). The
testability seam is the *same* one S88 keeps open: `agent_turn`/`run_submit` dispatch through
the object-safe `AgentModel` membrane, so the stub drives the whole repair loop with zero
network. **Coordination flagged to `/qa`** (§19): the stub script DSL (`src/CLAUDE.md`
`tool:`/`done:` lines) gains a way to express a broken-then-fixed sequence.

---

## 17. Cluster C — Document mode: consultative preamble/docstring edits (rung 6, R4)

The agent records durable understanding by writing a module preamble (or docstring), reusing
the **S88 module-preamble substrate** — **R4 (binding): no `cranelisp-types` change, no cache
bump; reuse the S88 `module_preamble` field + cache v9.**

### 17.1 The write path already exists: `apply_module_preamble` + section-0 regen (R4)

The substrate landed S88 (U2; `repl-embedded-agent.md §3.4`):
- `SymbolTable.module_preamble: Option<String>` (the FIXME-0428 field, cache v9).
- `save::apply_module_preamble(symbol_tables, module, source)` (`src/save.rs:308`) captures a
  leading `;;` block off source text into the field.
- `save::generate_module_source` (`src/save.rs:96-101`) re-emits the field as the **byte-stable
  section-0 block** (`generate_preamble`, `save.rs:326`, the exact inverse of capture — §8.16.5
  byte-stable round-trip).
- `regenerate_backing_file()` (driven from `main.rs:325/333`) writes the regenerated source.

A Document-mode edit is therefore **a field set + a regen**, no new machinery:

```text
apply_preamble_edit(module, new_preamble_text):
  symbol_tables[module].module_preamble = Some(new_preamble_text)   // direct field set
  self.regenerate_backing_file()                                    // byte-stable section-0 regen
```

The direct field set is the durable, byte-stable write (vs. `apply_module_preamble` which
*captures from `;;`-marked source* — the agent supplies the **stripped prose**, so it sets the
field directly, exactly the form `/doc <module>` reads back, §17.5.1). The unmodified-rest-of-
file invariant (§8.16.5 — no reflow) holds by construction because only `module_preamble` is
touched and `generate_module_source` is byte-stable for the unchanged sections (the FIXME-0423
regen path). A `pub(crate) fn apply_preamble_edit` lives in `save.rs` next to
`apply_module_preamble`.

### 17.2 The consent gate distinguishes a preamble edit from a code write

A preamble edit is a **Document write** — **consultative**, not the Build confirm (§17.3): the
agent asks "shall I record that as `solver`'s preamble?" The int mechanism reuses the §15.2
synchronous-prompt-at-the-eval-thread consent capture, but the **gate is keyed by tool**, so
the two write classes are distinguished at the consent gate (the SPRINT-required distinction):

- The Build write tool is `submit <form>` (a code form) → **confirm gate** (§15.2),
  "submit this definition?".
- The Document write tool is `set-preamble <module> <text>` (or `set-doc <sym> <text>`) →
  **consultative gate**, "record this as <module>'s preamble?".

`run_pull`'s head (§15.1) routes `set-preamble`/`set-doc` to a `run_document_edit` arm (sibling
to `run_submit`), which renders the **exact new leading comment block** it proposes (§17.5.2 —
through `generate_preamble` so the user sees the canonical `;;` form), asks the consultative
question (wording → `/repl`, §19), and on confirm calls `apply_preamble_edit` (§17.1) then
echoes the edit as a normal REPL line (§17.2). The tool name **is** the discriminator — a
`submit` is code (confirm), a `set-preamble`/`set-doc` is documentation (consultative) — so the
consent gate branches on `call.name`, no content sniffing. Both are absent from the read-only
`ALLOWLIST` (so unconstructable without their gate — the §15.4 floor extends to Document writes
too).

### 17.3 Round-trip + harvester read-back (rung 6 → rung 3 feedback, R4)

The closing loop ("memory is the code", §3.1/§4.6): after `apply_preamble_edit` + regen, the
preamble (a) **round-trips byte-stably** through save/reload (it is the same field
`generate_module_source` emits and `capture_module_preamble` re-reads — §8.16.5), and (b) is
**read back by the harvester next session**. The harvester already reads `module_preamble` —
§5.2 step 2 ("preamble: `symbol_table.module_preamble` … The harvester READS it") — and the
S88 test `harvest_degrades_under_tight_budget_keeps_pin` (`mod.rs:620`) already asserts the
field is folded into the harvest. So rung 6 (the *write*) feeds rung 3 (the *read*) with **no
new harvest code**: a fresh session loads the regenerated `.cl`, `apply_module_preamble`
captures the section-0 block into the field on load, and the next `assemble_request` harvests
it. **No `cranelisp-types` change, no cache bump** (R4): cache v9 already serialises
`module_preamble`; a cache-restored module carries it through serde (`save.rs:301-303`).

### 17.4 Testability (Lane A — `/qa`)

Per `tests/plan/agent-testing-strategy.md §3.5` (rung 6): a Document-mode edit round-trips (the
edit writes the preamble; a subsequent `/doc <module>` reads it back; it persists across the
backing-file regen — byte-stable), and the harvester reads the edited preamble (after the edit,
a new turn's harvest carries the new preamble text). Drivable by a stub `AgentModel` scripting a
`set-preamble` tool-call + a confirm; the round-trip + harvest-read-back are deterministic.

---

## 18. What S89 does NOT change (the zero-movement gate — R4)

Pinned as a checkable Phase-5 gate (the `/arch` "zero baselines move" claim):
- **No `cranelisp-types` change.** Build reuses `process_commands`/`eval`/staging; the
  validator reuses `check_forms` + the existing staging shape; Document reuses the v9
  `module_preamble` field. If `/dev` finds in Phase 5 it needs a new boundary type or a
  cached-struct change, that is cross-crate → file `target: /arch` (none anticipated — R4).
- **No `CACHE_SCHEMA_VERSION` bump.** The validator dry-run never persists; Document reuses v9.
- **No `public-api.txt` movement.** `src/` is a binary (no baseline); all S89 additions
  (`render.rs`, `validate_forms_dry_run`, `run_submit`/`run_document_edit`/`apply_preamble_edit`,
  the `submit`/`set-preamble`/`set-doc` write arms) are `pub(crate)`, int-private,
  `#[cfg(feature="agent")]`. The agent never ships in `--link`/`--release` (NG4).
- **Feature-OFF byte-identical.** All Cluster-A render (`render.rs`) + rung-5/6 code rides the
  existing four `#[cfg(feature="agent")]` cuts (§1); feature-off the binary is byte-identical
  to today. Cluster A is the watch-item (R1): markdown/fence render lives **inside**
  `src/agent/`, never a default-build render path.

---

## 19. S89 coordination points (flag to `/sprint` at the Phase-3 exit gate)

Decisions this design couples to another skill's choice — `/sprint` reconciles at the gate:
- **`/repl`** (additive to `repl/spec.md §17`):
  - the **agent-input prompt glyph** (§14.2) — distinct from `▌` and from the human prompt; normative.
  - **markdown rendering** within the §10.3 agent-prose frame (§14.3) — the markdown→frame composition.
  - the **Build confirm-gate wording** ("submit this definition? [y/N]", §15.2) and the
    **Document consultative wording** ("record this as <module>'s preamble?", §17.2).
  - the **validator give-up wording** (§16.4) — never surfaces a raw compiler error (U5).
- **`/qa`** (testability hooks; `tests/plan/agent-testing-strategy.md §3.4/§3.5`):
  - the stub-script DSL extension for a **broken-then-fixed** repair sequence (§16.5, Lane A).
  - the Cluster-A **ANSI-leak narrow failing-not-ignored repro** (§14.6) — owed before closure.
  - the confirm-gated-write + allowlist-still-refuses-non-writes guard (§15.4) and the
    Document round-trip + harvest-read-back guard (§17.4).
- **`/arch`** — none anticipated (R4: zero cross-crate edge / type change). Only if Phase-5
  surfaces a boundary-type need → file `target: /arch`.

---

## 20. Scope item 3a — `--yes` autonomous-submit flag (policy knob, NOT a boundary change)

Extends §15 (Build write arm + `run_submit` confirm-gate) and §17 (Document consultative
gate) **additively** with the user-requested `--yes` flag (`sprints/SPRINT.md` §"3a";
`/arch` ruling `design/arch/repl-embedded-agent.md §7.4`, commit `93961e8`). `--yes`
auto-*answers* the existing write-consent gates — it does not relocate, widen, or remove
them.

**Binding constraints (`/arch` §7.4 — verbatim intent).** Policy knob, not a
structural-floor change. **Blanket** — one flag covers both write gates (Build `submit`
§15.2 + Document `set-preamble`/`set-doc` §17.2). **`--yes` touches ONLY the consent seam,
NEVER the validator** — `validate_forms_dry_run` (§16.1, stage→check→discard,
silent-repair-anything U5) runs unchanged. "Skip confirm" and "skip check" are **distinct
seams at distinct sites** (§20.3). Zero public-API / cross-crate impact; `pub(crate)`,
`#[cfg(feature="agent")]`-gated, no-op on default builds — exactly like `--agent` (§6.4,
§7.2). Feature-OFF byte-identity preserved by construction (§18).

### 20.1 Flag parse + threading (cite the real seam)

`--yes` is parsed in `parse_args` (`src/main.rs:413` arg loop) **alongside `--agent`**
(`main.rs:462`), with the identical accepted-no-op discipline: a binary built WITHOUT the
`agent` feature MUST recognise `--yes`/`-y` and treat them as no-ops (never "unknown
flag"), so a script written for an agent build runs in either build. The parse adds a
`yes` bool sibling to `agent_on`/`agent_off` (`main.rs:408-409`); the usage strings
(`main.rs:475`) gain `[--yes]`.

The resolved value rides the **same threading path as `agent_enabled`** (the cleanest
seam — no new plumbing): the resolved bool

```text
auto_accept = yes && agent_enabled        // §0.6.1: meaningful only with an active agent;
                                          //   off by default; REPL-only (agent_enabled is
                                          //   already gated to Action::Repl, main.rs:519)
```

is computed beside `agent_enabled` (`main.rs:519`), returned from `parse_args` as a fifth
field's companion, and threaded through `run` (`main.rs:188` param list) into the REPL
arm's `s.enable_agent(...)` call (`main.rs:260`). The `enable_agent` signature
(`src/session_v4/lifecycle.rs:133`) gains the bool — `enable_agent(&mut self, enabled:
bool, auto_accept: bool)` — and forwards it to `provider::build_agent_state`
(`src/agent/provider.rs:47`), which stores it on a **new `pub auto_accept: bool` field on
`AgentState`** (`src/agent/types.rs:132`, beside `model`/`provider_label`). Feature-OFF
`auto_accept` is dropped exactly as `agent_enabled` is (`main.rs:195-196` `let _ = …`).

**Why `AgentState`, not a session field.** The consent gates (`run_submit` §15.2,
`run_document_edit` §17.2) are `impl CompilerSession` methods that already read `self.agent`
(the `Option<AgentState>`); the auto-accept bit lives where the model handle and transcript
live (§3.4 — "the agent adds ONE optional state object, not a parallel state machine").
Feature-off the field does not exist (the whole `AgentState` is `#[cfg]`-gated), so the
binary is byte-identical (§1).

### 20.2 Consent-gate auto-answer — short-circuit the prompt-read, keep render + downstream identical

`--yes` changes **exactly one step** of each gate: the consent *capture*. The render of the
proposed form/edit and the entire downstream commit path are untouched.

**Build gate (§15.2 `run_submit`).** Step 1 (render the proposed form, §15.2.1) runs
**unchanged** — the user always sees the form the agent will submit, through the
agent-input prefix (§14.2). Step 2 (capture consent) is where `auto_accept` short-circuits:

```text
run_submit(call, stdout):
  form = validate_and_repair(call.arg, model)?            // §16 — RUNS UNCHANGED (see §20.3)
  render proposed form (echo via agent-input prefix)       // §15.2 step 1 — UNCHANGED, always shown
  consent =
    if self.agent_auto_accept() { true }                   // ← --yes: skip the [y/N] line-read
    else { prompt "[y/N]" + blocking line-read }            // §15.2 step 2 — the normal path
  if !consent { feed "declined" tool-result; continue }    // §15.2 step 3 — UNCHANGED
  self.process_commands(&form, stdout) → eval → regen      // §15.2 step 4 / §15.3 — IDENTICAL
```

`agent_auto_accept(&self) -> bool` is a one-line `pub(crate)` reader
(`self.agent.as_ref().map_or(false, |a| a.auto_accept)`) — dormant / feature-off ⇒ `false`.
The bool short-circuits **only** the prompt-emit + line-read; `consent` is `true` either
way on accept, so step 4 (`process_commands` → `eval` → `regenerate_backing_file`, §15.3)
is byte-for-byte the same call. The decline branch (step 3) is simply unreachable under
`--yes` (the gate always answers accept), not removed.

**Document gate (§17.2 `run_document_edit`).** Identical shape, the *consultative* prompt is
the short-circuit point: render the exact proposed `;;` block (§17.5.2, via
`generate_preamble`) — **always shown** — then `if agent_auto_accept() { accept } else {
ask "record this as <module>'s preamble?" + line-read }`; on accept, `apply_preamble_edit`
(§17.1) + regen run **identically**. Blanket per `/arch` §7.4(a): the same
`agent_auto_accept()` reader gates both `run_submit` and `run_document_edit` — one bool, one
mental model.

The render-always invariant is load-bearing for the §7.4 "the user sees it" requirement:
`--yes` is *trust*, not *silence* — every auto-accepted write still echoes the proposed
form/edit + (on Build) the `format_eval_result` `:Type name` confirmation (§15.3). Only the
`[y/N]`/consultative prompt line and its read disappear.

### 20.3 Validation-floor guard (CRITICAL — `/arch` §7.4 non-negotiable)

**`--yes` does NOT reach `validate_forms_dry_run` (§16.1).** The validator's
stage→check→discard, silent-repair-anything loop (`validate_and_repair`, §16.2) runs
**identically** with the flag on or off — only compiling code ever reaches the live session.
This is structural, not a convention to be remembered:

- **The bool lives in the consent branch, never the staging branch.** `auto_accept` is read
  **only** by `agent_auto_accept()`, called **only** at the §15.2-step-2 / §17.2-consultative
  prompt site — i.e. **after** `validate_and_repair` has already returned `Ok(clean_form)`
  (§15.2: the repair loop runs *before* the echo and the gate). `validate_forms_dry_run` and
  `validate_and_repair` take **no `auto_accept` parameter** and have **no read path** to the
  `AgentState.auto_accept` field. The validator cannot observe the flag, so it cannot be
  skipped by it.
- **"Skip confirm" and "skip check" are distinct seams (§7.4).** The confirm-gate is the
  **consent seam** (`run_submit` step 2 / the consultative prompt) — the only thing `--yes`
  answers. `validate_forms_dry_run`'s discard-on-Err arm is the **correctness seam** (§16.1)
  — untouched. The two are different functions at different call sites; conflating them would
  require threading `auto_accept` into the validator, which this design structurally forbids
  (the field is on `AgentState`, the validator takes only `symbol_tables`/`module`/
  `working_program`, §16.1).
- **The conflation risk, named.** An implementation that treated `--yes` as "skip the
  dry-run" (e.g. by branching the repair loop on `auto_accept`, or by passing the flag into
  `run_submit`'s validate call) would be a **defect** — a `--yes`-on agent could submit raw
  un-typechecked code. The design prevents it by *placement*: `auto_accept` is unreachable
  from the validation path, so the only way to introduce the bug is to add a new parameter,
  which review would catch.
- **Phase-5 `/dev` guard + `/qa` obligation.** A `--yes`-**on** Lane-A test (stub
  `AgentModel` scripted broken-then-fixed, §16.5) MUST prove a deliberately-broken generation
  is **still silently repaired** — staged → checked → discarded → re-prompted, never
  submitted raw — exactly as with `--yes` off. The auto-accept changes *which* gate answer is
  given; it changes **nothing** about the validator's behaviour. The test asserts: (a) the
  broken intermediate never reaches the session under `--yes`; (b) the user never sees the
  broken form (the U5 silent contract holds); (c) only the repaired clean form is committed —
  and is committed *without* a `[y/N]` prompt (the `--yes` distinction from the §16.5 base
  test). The `/dev` mandatory unit test pins `agent_auto_accept()` is read only at the consent
  site (not the validate site) — a structural guard at the seam.

### 20.4 First-use notice hook (mechanism; wording → `/repl §17`)

`--yes` is an autonomy escalation (the agent now writes without per-action assent), parallel
to the U6 opt-in-twice first-use disclosure (§2.3). Per `/arch` §7.4(b) a **one-time**
first-use notice on the **first auto-accepted write** is warranted — naming that the agent
will now submit/edit without prompting **and** that the pre-flight validator still gates
correctness. This doc fixes the **mechanism**; the wording is `/repl`-owned (`repl/spec.md
§17`, sibling to the U6 disclosure — §19).

**Mechanism — where the once-flag lives and fires.** A `pub auto_accept_notice_shown: bool`
field on `AgentState` (`types.rs:132`, default `false`, beside `auto_accept`). The notice
fires at the **single auto-accept short-circuit point** shared by both gates — immediately
**inside** the `if agent_auto_accept()` branch (§20.2), **before** the auto-accepted write
proceeds, guarded once:

```text
// in run_submit / run_document_edit, at the auto-accept branch (§20.2):
if self.agent_auto_accept() {
    self.fire_auto_accept_notice_once(stdout);   // ← once-only; sets the flag
    accept                                       // (no [y/N] read)
}
```

`fire_auto_accept_notice_once(&mut self, stdout)` (a `pub(crate)` method, `src/agent/mod.rs`
or `pull.rs`) checks-and-sets the flag: `if !state.auto_accept_notice_shown { render the
/repl-owned notice in the agent prose frame (§3.5 / §14.3); state.auto_accept_notice_shown =
true; }`. Because the flag is on `AgentState` (session-lived, not serialised — §3.4), the
notice fires **once per session** on the first auto-accepted write of **either** class
(Build or Document — blanket, §7.4(a)), never again. Feature-off / `--yes`-off the branch is
unreachable so the notice never fires (the flag costs zero bytes feature-off — `#[cfg]`-gated
with the rest of `AgentState`).

### 20.5 What §20 does NOT change (zero-movement, R4 / §18 extended)

- **No validator change** (§20.3) — `validate_forms_dry_run` / `validate_and_repair` take no
  new parameter, have no read path to `auto_accept`.
- **No new write path** — `--yes` answers the *existing* §15.2 / §17.2 gates; the
  `process_commands`→`eval`→staging commit (§15.3) and `apply_preamble_edit`+regen (§17.1) are
  the same calls. No parallel submit, no new eval entry (R3 preserved).
- **Read-only allowlist untouched** — reads were never gated; `--yes` answers only the gate
  that already guards writes (§15.4 / §17.2 floor intact).
- **Public-API / cross-crate: ZERO** — `--yes` is an int-internal `pub(crate)` CLI flag; the
  `auto_accept` + `auto_accept_notice_shown` bits live on the `#[cfg(feature="agent")]`
  `AgentState`. No `cranelisp-types` change, no facade delta, no `public-api.txt` movement, no
  `CACHE_SCHEMA_VERSION` bump (the flag never persists — it is a per-session runtime toggle).
- **Feature-OFF byte-identical** (§18) — `--yes`/`-y` parse as accepted no-ops in both builds;
  all consuming code is `#[cfg(feature="agent")]`.

### 20.6 Coordination points (add to §19)

- **`/repl`** — the **`--yes`/`-y` flag name** (§7.4(c): `/arch` defers naming to `/repl`,
  `repl/spec.md §0.6.1` alongside `--agent`/`--no-agent`) and the **first-use notice wording**
  (§20.4: names autonomy escalation + that the validator still gates — `repl/spec.md §17`).
- **`/qa`** — the `--yes`-**on** validation-floor guard (§20.3: deliberately-broken generation
  still silently repaired, never submitted raw; committed without a `[y/N]` prompt), Lane A,
  `#[cfg(feature="agent")]`, extending the §16.5 broken-then-fixed stub script.
- **`/arch`** — none anticipated (zero cross-crate edge / type change; the ruling is
  ratified, `repl-embedded-agent.md §7.4`). Only if Phase-5 surfaces a boundary need.

---

## 21. S90 fluency phase — overview (the four pillars, int-side)

**Provenance.** Refines `design/arch/repl-embedded-agent.md §11` (S90 Phase-2 `/arch` verdict,
APPROVE-WITH-REVISIONS, R1–R7, commit `ca9d5fb`) into the int-side implementation plan.
Honours the `/repl` experience contract (`repl/spec.md §17.17–§17.20`, commit `e112426`), the
`/docs` content contract (`user/syntax-cheatsheet-plan.md`, commit `e5a0119`), and the
`/typecheck` match-predicate seam (`design/typecheck/signature-match.md` +
`monomorphisation.md §9`, commit `2012dac`). **DESIGN ONLY** — implementation is Phase 5.

S90 delivers the "reach"/fluency half of rung 7 as four pillars, all REPL-cadence consumers of
the existing int surface (§1 / BC §6.3). **Ships fully this sprint:** Pillar 1 (`/syntax`),
Pillar 2 (harvest sig-grain), Pillar 4 (silent log), and the R2-layer-b containment floor
(`catch_unwind` on eval-thread typechecks). **Design-only this sprint (implemented next):**
Pillar 3 (nice-worker importable-symbol indexer + `/search`), gated on the 0432 typecheck root fix
+ the new nice-worker indexer `catch_unwind` (CF.2) (§11.5 / R1; re-pinned `/arch` `c699045`,
§11.1–§11.9).

The S88/S89 load-bearing invariants survive across all four (the §1 / §18 zero-movement gate):

- **Byte-identical feature-OFF — scoped to Pillars 1/2/4 (R9).** Those three S90 surfaces (except
  `/syntax`) are fully `#[cfg(feature="agent")]`. `/syntax` is the lone unconditional command (a
  static asset, like `/help`) — but its *agent pull* (the allowlist row) and its primer
  cross-reference are gated. **Pillar 3 is NOT covered** — it is a non-agent default-build session
  facility (`/search` + the nice-worker indexer run in every session); it carries a
  **default-build-behaviour-stable** invariant instead (the indexer must not perturb object-codegen
  behaviour or the default REPL contract — §25.8).
- **Zero new cross-crate edges, zero `public-api.txt` movement, zero `cranelisp-types` change,
  no `CACHE_SCHEMA_VERSION` bump (this sprint).** Confirmed by `/arch` (§11.8). Pillar 3's indices
  reuse the existing `check_forms` inward call + the existing `Type` scheme as their stored type.
  At Pillar-3 implementation time (next sprint) two additive `cranelisp-typecheck/public-api.txt`
  lines land (`signature_matches_exact` + `signature_matches_partial`, R8) — dispositioned then,
  not now. The one non-int behaviour obligation is the `/typecheck` 0432 root fix (a fix inside an
  existing crate).

Quality attributes touched (Principle citations): **Simplicity** (Principle 6 — Pillars 1/2/4
are a static asset + a grain change + a sibling sink; no new state machinery), **Observability**
(Pillar 4 is the durable insight log; the `catch_unwind` floor converts a silent crash into a
named failure), **Maintainability** (the feature-gate cuts keep blast radius bounded; Pillar 2
is a read enrichment of one existing harvest arm), **Concurrency-safety** (the containment floor
hardens the eval-thread typecheck path — §24), **Testability** (Principle 5 — Pillar 3's
zero-residue is structurally testable, mirroring `validate_dry_run_discards_does_not_commit`).

---

## 22. Pillar 1 — `/syntax` topic-indexed cheat-sheet (SHIPS S90)

A token-dense, verified-compiling, topic-keyed **core-language** syntax reference, surfaced as a
REPL command useful to **both** the human and the agent (the self-documenting-REPL principle).
Mechanically: a static `include_str!` asset + a delimiter parser + a new `ReplCommand::Syntax`
variant + a read-only allowlist row + the primer topic-name cross-reference. **No new
machinery.** UX is `/repl`-owned (`repl/spec.md §17.17`); content is `/docs`-owned
(`user/syntax-cheatsheet-plan.md`); this section designs the **int wiring** (R7).

### 22.1 The asset + the delimiter parser

- **Asset.** A single static file at **`src/syntax/cheatsheet.txt`** (`/docs`' content contract,
  `user/syntax-cheatsheet-plan.md`), embedded via `include_str!("../syntax/cheatsheet.txt")`.
  It is a **sibling of `src/agent/primer.txt`** in spirit but lives **outside** `src/agent/`
  and is **NOT feature-gated** (the `/syntax` *command* works in the default build; only the
  *agent pull* of it rides the `agent` feature). A new `src/syntax/` directory holds the asset;
  the parser lives in a new unconditional `src/syntax.rs` (declared `pub(crate) mod syntax;` in
  `lib.rs`, no `#[cfg]`).
- **Topic delimiter** (`/docs`' contract): each topic block is introduced by a line of the exact
  form **`=== topic: <name> ===`**. The parser splits the asset on these delimiter lines, keying
  each block by `<name>` (trimmed). It preserves the topic-name **order of appearance** (the
  asset's authored order = the bare-`/syntax` index order — deterministic, no sort).
- **Parser shape** (`src/syntax.rs`, pure, unit-testable):

  ```text
  parse_cheatsheet(&'static str) -> Vec<(name: &str, content: &str)>   // order-preserving
  topic_names(&self) -> Vec<&str>                                       // the bare-/syntax index
  topic_content(&self, name: &str) -> Option<&str>                      // /syntax <topic>
  ```

  Build it **once**, lazily, via a `std::sync::LazyLock<Cheatsheet>` over the `include_str!`
  constant (the parse is cheap and the asset never changes at runtime — a one-shot static cache,
  not a session structure). No state on `CompilerSession`.

### 22.2 `ReplCommand::Syntax` — the three forms (`repl/spec.md §17.17.1`)

A new **unconditional** `ReplCommand::Syntax(&'a str)` variant (`src/repl.rs:37` enum) + a
`"/syntax"` arm in `parse_slash_command` (`src/repl.rs:102`) + a `dispatch_command` arm
(`src/repl.rs:449`) → `CommandResult::Final(self.handle_syntax(arg))`. **No `#[cfg]`** — the
command is in the default build (like `/refs`/`/tests-for`, §9). The `/help` text
(`print_help`, `src/repl.rs:135`) gains one line. The handler (`handle_syntax`, a new method on
`CompilerSession` or a free fn over the `LazyLock` — free fn preferred, no session state read):

- **bare `/syntax`** (empty arg) → the **topic-name index**: the ordered list of topic names
  plus the one-line hint `Use /syntax <topic> for detail.` (`repl/spec.md §17.17.1`). Emitted as
  **deterministic plain text** — `;`-prefixed comment lines, carrying **no ANSI escapes** and **no
  style role**, so it is byte-identical with colour on or under `--no-color`. This design fixes
  that it lists `topic_names()` in authored order (`render_index`).
- **`/syntax <topic>`** → `topic_content(name)`: the topic's dense content, emitted **as
  authored** — deterministic plain text, trimmed of trailing whitespace, with **no second
  renderer**. The asset is the single source (Principle 7); `handle_syntax` returns the curated
  block verbatim. It **deliberately does NOT route through `crate::pretty`** (the S-expression
  pretty-printer): the cheat-sheet's `FORM` lines are **syntactic templates** —
  `(defn name ([params] body) ...)` with `...` and metavariables — that **do not parse**, so
  `crate::pretty` cannot render them, and reflowing the verified-compiling forms through a second
  renderer would buy no agent benefit while coupling the renderer to the cheat-sheet block format.
  Output is therefore identical with colour on or under `--no-color` (plain either way — no style
  role is involved). *(Future enhancement, out of scope: selectively syntax-highlight only the
  concrete `EXAMPLE` lines, which DO parse — deferred because it would couple the renderer to the
  block layout for modest gain.)*
- **unknown `/syntax <unknown>`** → re-print the bare index with a short "no such topic" note
  (`repl/spec.md §17.17.1` — self-documenting; never an opaque error). This is the `topic_content
  → None` arm.

**Output framing.** `/syntax` is deterministic REPL output, **not** agent prose — it is **not**
wrapped in the `▌` agent-prose frame (§3.5 / `repl/spec.md §17.17.2`). All three forms (index,
topic, unknown-topic re-list) return **plain text from `handle_syntax` with no second renderer
and no style role** — clean under `--no-color`, identical with colour on.

### 22.3 Read-only allowlist row (the agent pull-tool, gated)

`/syntax` joins the agent's **read-only pull allowlist** (`src/agent/pull.rs:61` `ALLOWLIST`) as
one new row — `("syntax", "Show core-language syntax: bare for topics, syntax <topic> for
detail")`. Consequences (all already in place — this is one data row):

- The agent emits `syntax <topic>` as a tool-call; `synthesize_command` (`pull.rs:125`) maps it
  to `/syntax <topic>`; `run_pull` runs it through `process_commands` like every other read
  (`pull.rs:195`) — rendered behind the `agent>` prompt (`repl/spec.md §17.17.3`), result fed
  back. **No special-casing** — `/syntax` is just another allowlisted read.
- The allowlist row is **inside** the `#[cfg(feature="agent")]` `pull.rs`, so the *pull surface*
  is gated even though the *command* is not (§21 invariant). The `tool_defs()` count test
  (`pull.rs:828` `tool_defs_are_read_only_plus_submit`) updates: `ALLOWLIST.len()` grows by 1.

### 22.4 Primer topic-name cross-reference (the gated primer edit)

The always-on primer (`src/agent/primer.txt`) gains a **compact line naming the `/syntax` topic
vocabulary** — the *names only*, not the content (`repl/spec.md §17.17.4` / R7). So the model
knows *which* topics exist and can pull detail on demand, without every topic's full content
bloating every turn. Division of labour the user experiences: **core syntax → primer summary +
`/syntax` depth; prelude/stdlib symbols → harvest (§23)** — honouring
`agent-prelude-awareness-via-harvest-not-primer` (the primer carries core-syntax topic *names*,
NOT prelude/stdlib idioms). The edit is to `primer.txt` (the `#[cfg(feature="agent")]` asset), so
it is gated. **Coupling note:** the topic-name list in the primer must stay in sync with the
asset's topics — a Phase-5 micro-decision (a doc comment pointing `/docs` + `/dev` at both files;
a future increment could derive the primer line from `topic_names()` at build, but the MVP hand-
maintains it with a sync note).

### 22.5 Primer `match`-shape contradiction (flag for Phase-5 verification)

`/docs` flagged (Phase-3a) a **primer/spec `match`-shape contradiction**: `src/agent/primer.txt`
(~lines 122–125) writes match arms **paren-grouped** — `((Circle r) (* …)) ((Rect w h) (* …))` —
but `spec/06-pattern-matching.md §6.1` (and `spec/04-expressions.md:485`) specify a **single flat
bracket** of alternating `pat body` pairs: `(match s [(Circle r) (* …) (Rect w h) (* …)])`. The
primer's shape is **wrong** (it would not compile). **Disposition:** this is a likely **primer
defect** → a `/dev` fix (correct the primer few-shot to the flat-bracket spec shape) **plus a
`/qa` repro** (a narrow test asserting the corrected `match` example compiles — the primer's
few-shot idioms are subject to the S89 verified-compiling discipline). Verify in Phase 5 against
the live REPL; the corrected shape is the spec's `[pat1 body1 pat2 body2 …]`. (This is noted
here, not actioned — `/design` does not edit source; it is a Phase-5 `/dev`+`/qa` handoff.)

---

## 23. Pillar 2 — harvest enrichment: in-scope symbols at signature grain (SHIPS S90)

The harvester (`src/agent/harvest.rs::harvest_context`, §5) already pushes the *shape* of the
session every turn. S90 **enriches the grain** of its export-surface arm so the agent has
**ambient awareness of what is in scope** — current-module defns + imported symbols + implicit
prelude — at **name + `:Type` signature + docstring** grain, every turn, without first spending a
turn on `/imports`/`/list`/`/exports` (`repl/spec.md §17.18`). This is the user-directed
"keep prelude plus imported symbols in context" delivered the user-owned way — **harvest, not
primer** (`agent-prelude-awareness-via-harvest-not-primer`). It is **ambient** — no command,
nothing extra in the human REPL (auditable offline via `/context`, §17.11).

### 23.1 The seam — enrich the existing export-surface arm, reuse the existing formatter

The change is confined to `harvest_context` (`harvest.rs:44`). Today its arms emit **names only**:

- the current-module arm (`harvest.rs:48–65`) pushes full source (already rich — unchanged);
- the mentioned-module arm (`harvest.rs:104–133`) pushes exports as **bare names** via
  `table.public_symbols().map(|(s,_)| s)` (`harvest.rs:112–116`) — **this is the arm to enrich**;
- a **new in-scope block** surfaces the current module's imports + implicit prelude at sig grain.

**Reuse the existing `:Type` formatter (Principle 7 — single source of truth).** The signature
rendering is **not re-implemented**: it is the **exact** path `/sig` and bare-symbol lookup use —
`crate::repl::format_entry_sig(entry, name)` (`src/repl.rs:220`), which dispatches per
`ModuleEntry`/`DefKind` (overloaded → one line per variant; constrained → inline constraints;
constructor; etc.) and itself delegates the type rendering to `crate::display::format_type_qualified`
(`src/display.rs:112`) — FQ primitive names, lettered vars, byte-identical to `/sig`. The
docstring is read from the same `entry`'s `docstring` field that `/doc`/`format_entry_sig` read
(`repl/spec.md §17.18.1` facet 3 — absent when none, no placeholder). So the harvested grain is
**exactly what a human gets by typing the name** — the design's stated equivalence.

**Per-symbol grain emission** (conceptual, the exact bytes `/dev`-owned per `§17.18.2`):

```text
== in scope ==
<name> :: <format_entry_sig(entry,name) signature>  ; <docstring if any>
...
```

The three feeders for the in-scope block (`repl/spec.md §17.18.1`):

1. **current-module own defns** — `current_symbol_table().defined_symbols()` (already iterated by
   the pinned-source arm; here read each entry's scheme+doc, not its source);
2. **explicit imports** — the current module's `ModuleEntry::Import` entries (the `/imports`
   surface), resolved through the import chain to the canonical entry for the signature (mirror
   `resolve_entry_for_display`, the path `/sig` uses for a re-exported name);
3. **implicit prelude** — `self.prelude_implicit_names()` (`src/repl.rs:1205`, the
   "Prelude (implicit)" surface, gated on the `prelude_fallback` bit) → for each name, the
   canonical prelude entry's `format_entry_sig`. This is the **harvest-sourced prelude awareness**
   the memory ruling demands — read live, never primer-baked.

### 23.2 Budget degrades GRAIN, not silently truncates (`repl/spec.md §17.18.2`)

Signature+docstring grain is heavier than bare names. The in-scope block rides the **same
`char_budget` graceful-degradation ladder** the harvester already enforces (`harvest.rs:45`,
`DEFAULT_TOKEN_BUDGET` × `CHARS_PER_TOKEN`). Under budget pressure the block degrades **grain**:

```
name :: signature  ; docstring        (full grain)
  → name :: signature                 (drop docstrings first — cheapest signal)
    → name                            (names-only floor — never absent)
```

The agent must **never** believe a symbol is *absent* merely because the budget elided its detail
(`§17.18.2`) — so the degradation drops detail-per-symbol, never truncates the symbol *list*. This
is a refinement of the existing §5.4 ladder applied to the new in-scope block; the current-module
full-source pin (§5.4 floor) is unchanged. **Acceptance (experiential):** a fresh agent session
references an in-scope symbol's actual signature without first having to `/list`/`/exports`.

### 23.3 Testability (Principle 5, for `/qa`)

- the in-scope block carries `name + signature + docstring` for a defined symbol (positive);
- the rendered signature is **byte-identical** to `/sig <name>` for the same symbol (the
  reuse-not-reimplement guard — assert `harvest contains format_entry_sig(entry,name)`);
- implicit-prelude symbols appear when the `prelude_fallback` bit is ON, absent when OFF (+neg,
  mirroring `prelude_implicit_names`'s own gate);
- under a tight budget the block degrades grain (docstring dropped) but the **symbol name is
  still present** (+neg — the "never silently absent" guarantee).

---

## 24. Containment floor (R2 layer b) — `catch_unwind` on eval-thread typechecks (SHIPS S90)

**The Pillar-3 robustness floor, landed THIS sprint** (it also retroactively hardens the S89
validator). The eval-thread typecheck path calls `check_forms` **directly, with no
`catch_unwind`** — so a 0432-shaped form (a multi-clause `defn` + unannotated self-call tripping
the monomorphiser `debug_assert!`, `monomorphise.rs:1016`) **unwinds the eval thread and crashes
the REPL** in a debug/agent build (the agent's only build). The pool-worker loop already guards
this (`worker.rs:1493`/`:1522` — `catch_unwind` → `notify_module_failed`); the eval-thread path
does not (§11.3, verified containment gap).

### 24.1 The wrap — mirror the pool-worker pattern at the eval-thread seam

Wrap the **typecheck call inside `validate_forms_dry_run`** (`src/worker.rs:308`, the §16.1
validator substrate, called from `validate_one_form`, `pull.rs:668`) in
`std::panic::catch_unwind(AssertUnwindSafe(...))`, converting a caught unwind to a clean
`Err(CranelispError)` — **exactly** the `worker.rs:1493` shape (reuse `panic_message`,
`worker.rs:1692`, for the payload string). The wrap goes around the `check_forms(...)` call
(`worker.rs:329`), not the whole function (the staging build is panic-free; only `check_forms` is
the hazard). On a caught panic: drop the throwaway staging (it drops on every path already —
§16.1) and return `Err` with a message like *"module/form failed to typecheck (compiler internal
error): {msg}"*. Because the validator already folds **any** `Err` into a repair re-prompt /
give-up (U5, §16.4 — no error-classification), a 0432-shaped model-proposed form now surfaces as
a graceful give-up **instead of a REPL crash** — the retroactive S89 hardening.

The **future Pillar-3 indexer** (§25) reuses this same `catch_unwind`-wrapped `check_forms` call
(it is a sibling of `validate_forms_dry_run` — §25.1), so a 0432-shaped *reachable library module*
hit at index time surfaces as a "could not index <module>" search-quality note, never a crash
(`repl/spec.md §17.19.4`). Designing the wrap on `validate_forms_dry_run`'s `check_forms` now
means the indexer inherits it free.

### 24.2 Why a shared helper, not two catch sites

To avoid two divergent catch sites (the validator's and the future indexer's), extract a small
`pub(crate)` helper in `worker.rs`:

```text
checked_check_forms(parsed, ctx, tables, aliases, fallback) -> Result<Vec<Warning>, CheckError>
  = catch_unwind(AssertUnwindSafe(|| check_forms(...)))
      .map_err(|p| CheckError::from(internal-panic(panic_message(&p))))
      .and_then(|r| r)
```

Both `validate_forms_dry_run` (now) and the indexer (next sprint) call **this** instead of
`check_forms` directly. One catch site, one `panic_message` reuse, mirroring `worker.rs:1493`.
This is the int-internal half of the two-layer containment (R2-b); the `/typecheck` 0432 root fix
(R2-a — the durable trigger removal) is the other half, owned by `/typecheck`.
**Both ship before any Pillar-3 implementation; layer (b) ships THIS sprint regardless** (it is
the S89-validator hardening).

### 24.3 Testability (Principle 5, for `/qa`)

- a 0432-shaped form fed to `validate_one_form` returns `Err` (a graceful give-up), **never
  panics the test process** (the containment guard — the unit-tier home for the §24 floor);
- the existing `validate_dry_run_discards_does_not_commit` (`pull.rs:1154`) still holds (the wrap
  does not change the discard semantics);
- (next sprint) the indexer over a 0432-shaped reachable module yields a "could not index" note +
  zero residue, never a crash (the §25 +neg / `repl/spec.md §17.19.4` floor).

---

## 25. Pillar 3 — nice-worker importable-symbol indexer + `/search` (DESIGN-ONLY S90, IMPLEMENTED NEXT)

**Status: DESIGN-PINNED, IMPLEMENTED NEXT** (R1/§11.5). **RE-PINNED 2026-06-23** (first redesign:
nice-worker home) then **REFINED 2026-06-25** (read-or-produce-`.meta` model; `/arch`
`design/arch/repl-embedded-agent.md §11.1/§11.1a/§11.1b/§11.2` + R13–R16). This section is the
int-side durable target for the **read-or-produce-`.meta`, one-artifact** indexer. It SUPERSEDES
both (i) the original eval-thread/lazy/one-shared-DTO/`agent`-gated `/lib-search` design (retracted
in full — RETRACTION note below) and (ii) the S90 "in-memory, typecheck-and-discard,
rebuild-every-triggered-session, writes-nothing" framing (superseded by the REFINEMENT note below).
Gated on the 0432 typecheck root fix (R2-a) + the **new** nice-worker indexer `catch_unwind`
(CF.2, R2-b). It pins the **execution home, the three-branch per-module step, the two indices, the
worklist↔claim coordination, the residue invariant, the `.meta` persistence, the trigger, the
containment catch, and the command wiring** so the implementation has a fixed target. The UX
contract is `repl/spec.md §17.19`; the match algorithm is `/typecheck`'s
(`design/typecheck/signature-match.md §6`).

> **IMPLEMENTED — S91 (core indexer §25.1–§25.8) + S108 (two additions below).** §25.1–§25.8 are the
> as-built target the S91 implementation turned green. **S108 (Increment 2)** added two mechanisms
> recorded in the new subsections: **§25.9 — the seeded direct-read feed** (`/search` now indexes the
> built-in `primitives`/`macros` modules by a direct symbol-table read, a SECOND feed disjoint from
> the `.cl` worklist) and **§25.10 — the lifecycle-message latch** (the "indexing N module(s)…"
> not-ready note + the async "; search index complete." completion notice). Both carry their own
> `Status: LANDED S108` note; the "design-only, nothing added to the default build" phrasing in the
> §25.8 close is historical S90 framing.

> **RETRACTION (what the first redesign removes).** The original §25 placed the indexer on the
> **eval thread** as a sibling of `validate_forms_dry_run`, built **lazily** one module per query,
> cached **one shared `ImportableSymbol` DTO** on `AgentState` fed by both Pillar 2 and Pillar 3,
> gated the command behind `#[cfg(feature="agent")]`, and matched **name + exact-shape only**. ALL
> of that is retracted. What CARRIES into the nice-worker model: 0432 is pulled in as a
> prerequisite, and Pillar 3 stays design-only this sprint.

> **REFINEMENT (2026-06-25 — read-or-produce-`.meta`; `/arch` §11.1 REFINEMENT BOX + R13–R16).**
> The S90 nice-worker model said the indexer **writes nothing**, typechecks-and-discards
> **in-memory**, and **re-typechecks lib-path ∪ project-root on every trigger**. A user design
> review surfaced two real problems: (1) a triggered first-`/search` re-typechecked the *entire*
> reachable world even when valid `.meta.json` caches already existed — a needless N-module
> typecheck; (2) a module the indexer typechecked-and-discarded, when later `/import`'d,
> **re-typechecked from scratch** (the index entry was a throwaway hint). Both dissolve once the
> indexer **reads from / produces the existing `.meta` cache** rather than an ephemeral discard.
> **What CHANGED:** the per-module step becomes **skip-if-claimed → read-`.meta`-if-valid → else
> typecheck-and-**write**-`.meta`** (§25.1); the two indices are **read-derived from `.meta` files**
> (rebuildable by a cheap `.meta`-scan), so cross-run persistence IS the existing `.meta` cache, not
> a per-session rebuild (R16, §25.3); the **residue invariant is relaxed** from "writes nothing"
> to **no session-state residue** — the +neg guard now asserts **no `SharedState` entry, NOT "no
> disk write"** (R13, §25.3); the `IndexModule` worklist coordinates with the real path by a
> **module-state check before claiming** — skip any module the real path owns (R15, §25.1b); and a
> found symbol later `/import`'d is now a **`.meta` cache-hit, no re-typecheck** (R13/§25.5 — problem
> 2 dissolved). **What CARRIES from S90:** nice-worker home (R4), eager-but-triggered (R9b, §25.5),
> two indices (R3), exact-OR-partial match (R6, §25.7), default-build facility (R9), CF.2 containment
> (R2-b, §25.4), and separate-worklist/no-`.o`-entanglement (§25.1).

### 25.1 Execution home — a background task of the NICE WORKERS; read-or-produce-`.meta` burn-down (R4, R13–R16)

Pillar 3 answers `/search <name>|<scheme>` over symbols **reachable but not yet imported**.
Reachable = **lib-search-path modules ∪ project-root modules** (R10). To know an importable
symbol's signature its defining module must have a typecheck result — which the refined model gets
either by **reading the module's `.meta` cache** or, on a cache-miss, by **typechecking it once and
writing the `.meta`** — but the module is **never imported** (never `register_module`'d).

**The indexer rides the nice workers, NOT the eval thread.** `src/session_v4/nice_worker.rs::nice_worker_loop`
(`nice_worker.rs:65`) is the pool of low-OS-priority threads that already drain background `.o`
codegen — it parks on `scheduler.take_object_codegen()` (`nice_worker.rs:79`), calls
`compile_module_object` (`nice_worker.rs:121`), and `notify_object_codegen_complete`
(`nice_worker.rs:101`). The indexer is a **second kind of work** drained by **the same threads
off a separate worklist** — it is NOT spliced into `compile_module_object`. Recommended shape: a
distinct **`IndexModule(path)` work variant** (peer to the existing object-codegen claim), with its
own scheduler claim/notify pair alongside `take_object_codegen`. Naming the variant + the claim is
this doc's detail; the architectural ruling (§11.1) is fixed: **separate worklist, shared threads,
no entanglement with the `.o` lifecycle.**

**The Phase-1 `.meta` writer the indexer reuses.** The real object-codegen path already writes a
module's `.meta` **decoupled from its `.o`** — `write_module_meta` (`nice_worker.rs:176`, the
typecheck-driven Phase-1 writer landed under FIXME 0387), which calls `cache::write_meta`. The
indexer reuses **the same `cache::write_meta` edge** (NOT the same call site — `write_module_meta`
stays the object path's; the indexer writes from its own `IndexModule` branch), producing a `.meta`
**byte-identical** to what the real path would write for the same module. The object path's
`take_object_codegen` claim and `compile_module_object` stay separate from the `IndexModule`
worklist — the indexer never enters that flow.

**NOT entangled with the `.o`-codegen lifecycle (the load-bearing separation).** The object-codegen
path operates on **`TypecheckDone`-registered** modules (`take_object_codegen`); the indexer
operates on **reachable-but-unregistered** modules. The `IndexModule` path therefore MUST NOT route
through `notify_typecheck_done` (`scheduler.rs:823`), `record_compiled` / `append_o_path`
(`cache.rs:144`/`:186`), `notify_object_codegen_complete` (`nice_worker.rs:101`), or
`register_module` (`scheduler.rs:376`). It **writes no `.o` and registers no module** — it writes
only the `.meta` via `cache::write_meta` on a cache-miss (branch c below), and reads `.meta` on a
cache-hit (branch b). The real path always wins for any module it owns (branch a; §25.1b).

**The flow — one of three branches per reachable module (R13–R16):**

```text
nice_worker_loop drains an IndexModule(path) task; take EXACTLY one branch:

 (a) path is present in the scheduler ModuleState registry in ANY pool state  (§25.1b, R15)
       -> SKIP. The real path owns it and writes its .meta; the indexer reads
          that .meta later (late .metas surface via .meta-scan / notify hook).
          No typecheck, no .meta write.

 (b) .meta present AND valid  (cache::load_meta schema+BUILD_ID gate  AND  int's
       is_cache_valid source-content gate)                                  (R16)
       -> deserialise the SymbolTable from the .meta (cache::load_meta /
          deserialise_meta), populate the TWO index entries from it (§25.3).
          NO typecheck.

 (c) no .meta, or stale .meta                                               (R13)
       -> typecheck once on the nice worker against throwaway staging
          (the validate_forms_dry_run discard substrate, §25.2):
            staging = SymbolTable::new_with_params(path)        // throwaway, locally owned
            ctx     = SymbolTableAccess::cluster(symbol_tables, &mut staging, path)
            catch_unwind(|| check_forms(parsed, &mut ctx, ...))  // CF.2 (§25.4)
              Ok(Ok(()))  -> cache::write_meta(path, &staging)   // benign .meta, NO .o, NO register
                             for each public entry: add TWO index entries (§25.3)
              Ok(Err(e))  -> logged per-module index-skip; module absent from results
              Err(panic)  -> logged per-module index-skip; continue; thread survives
            drop(staging)  // module is NEVER register_module'd
   then: mark path indexed; continue draining the IndexModule worklist
```

**Discovery (R10).** The reachable set is enumerated by walking **lib-search-path ∪ project-root**
using the **same file-resolution rules `import` uses** — `pipeline::resolve_module_file`
(`src/pipeline.rs:27`); **no new search semantics**. The enumerated set is the indexer's worklist.

**Why the nice workers (not the eval thread).** (a) The work is **exactly the nice workers' shape**
— low-priority background typecheck-and-record over a module worklist, the same threads already
burning down object codegen; (b) it is **off the eval thread**, so `/search` (human or agent pull)
is a non-blocking **index read**, never a synchronous typecheck stall on the user's Enter; (c) idle
nice workers absorb the cost (object codegen and indexing share the below-normal-priority thread
budget). The refinement **lowers** the burn-down's cost: it re-typechecks **only genuine
cache-misses** (branch c), reads hits straight off the existing `.meta` cache (branch b), and skips
modules the real path owns (branch a) — so a warm project pays a `.meta`-scan plus a few
miss-typechecks rather than an N-module re-typecheck (§25.5).

### 25.1b Worklist↔claim coordination — module-state check before claiming (R15, §11.1b)

The `IndexModule` worklist must never double-typecheck a module the real path owns, nor race the
priority/normal/object-codegen path on a module in flight. The coordination mechanism is a
**module-state check before claiming an `IndexModule` task**, grounded in the scheduler's existing
per-module registry — `ModuleState` (`scheduler.rs:52`), keyed by `ModuleFullPath`, carrying `pool`
(`scheduler.rs:53`) + the claim flags `object_working` (`scheduler.rs:81`) / `inmem_claimed`
(`scheduler.rs:75`) / `eval_owned` (`scheduler.rs:114`). The invariant (architectural; the exact
claim/notify naming is this doc's detail):

- **A module present in the registry in ANY pool state is owned by the real path → the indexer
  SKIPS it** (branch a). It is either in-scope (covered by Pillar 2's live-table harvest, §23) or
  it will be picked up later from the `.meta` the real path's typecheck-driven Phase-1 writer
  produces (`write_module_meta`, FIXME 0387 — a real-typechecked module always has a `.meta` to
  read, regardless of `.o` state). The real path always wins.
- **A reachable module ABSENT from the registry is the indexer's domain** — it reads the `.meta`
  if valid (branch b), else typechecks-and-writes-`.meta` (branch c), never registering it.
- **Late-arriving real `.meta`s** (a module typechecked-for-real but outside the indexer's in-scope
  set — e.g. a transitive dependency the real path loaded after the burn-down began) surface in
  `/search` because the indexer **reads them from their written `.meta`**: either via the
  trigger-time `.meta`-scan, or via a re-scan / a notify hook the implementation may add so a
  `.meta` written after the burn-down still surfaces. The mechanism (re-scan vs notify) is this
  doc's choice; the ruling is the invariant: **no module is both index-typechecked and
  real-typechecked concurrently — the real path always wins, and the indexer consumes the real
  path's `.meta` rather than duplicating its typecheck.**

### 25.2 The discard substrate it reuses (NOT the execution home)

The stage→check→discard mechanism is **`validate_forms_dry_run`** (`worker.rs:308`): build a
throwaway `staging` `SymbolTable`, a `SymbolTableAccess::cluster` view, run `check_forms`, drop
staging on every path. The indexer **reuses this substrate on branch (c) only** — the same staging
+ cluster-view + `check_forms` + drop — but **the execution home is the nice-worker loop, not the
eval thread**, and between the check and the drop it (i) writes the `.meta` via `cache::write_meta`
and (ii) reads public entries out of staging into the two indices. Branch (b) does **no** typecheck
— it deserialises the `SymbolTable` from the `.meta` and populates the indices from that; branch (a)
does neither. `validate_forms_dry_run` is the *eval-thread* validator (and is where CF.1, §24,
lands); the **indexer is a structurally-parallel pass on the nice workers** that reuses only the
discard *recipe* for its cache-miss branch. The eval-thread validator (CF.1) and the nice-worker
indexer (CF.2) are **two homes** for the same staging recipe; they do not share a call site.

### 25.3 Two purpose-built indices (R3, R16) — Pillar 2 is cleanly SEPARATE

**Pillar 3 builds TWO lookup indices** (user-specified, §11.2), populated by the nice-worker
burn-down — **read-derived from the `.meta` files** (branch b deserialises, branch c reads from
its own miss-typecheck's staging):

```rust
// int-private, pub(crate) — derived read-caches on SharedState, read-derived from .meta,
// NOT cranelisp-types boundary types, NOT symbol tables, NOT serialized.
struct ImportableIndices {
    // Index A — name lookup: /search <symbol>, exact OR partial (partial = substring).
    by_symbol: HashMap<Symbol, Vec<ModuleFullPath>>,
    // Index B — type lookup: /search <scheme>, exact OR partial (partial = structural-contains).
    by_scheme: Vec<(Type, Symbol, ModuleFullPath)>,   // scheme stored for the §25.7 predicates
    indexed: HashSet<ModuleFullPath>,                 // burn-down progress / skip-state guard
}
```

- **Index A: `symbol → modulepath`** — name lookup (`/search <symbol>`; exact or substring).
- **Index B: `scheme → (symbol, modulepath)`** — type lookup (`/search <scheme>`; exact or partial
  scheme via the §25.7 predicates). The stored `scheme` is the existing `cranelisp-types` `Type`
  — **no new boundary type**.

**Placement: `pub(crate)` on `SharedState` / the session** (the nice workers receive `&SharedState`
— `nice_worker_loop(shared: &SharedState)` — so the indices they populate must live where the
workers and `/search` both reach them; **NOT on `AgentState`** — the prior placement is retracted,
since `/search` is now a non-agent default-build command, R9).

**Cross-run persistence IS the `.meta` cache, not a serialized index (R16).** The two indices are
**derived read-caches** — never the source of truth; blow them away and they rebuild by a cheap
`.meta`-scan over the reachable modules. They are **NOT a symbol table**, **NOT serialized**, and
carry **NO `CACHE_SCHEMA_VERSION` bump**. The existing `.meta` cache is the cross-run persistence
layer; the indices are an in-memory projection over it. (This is the refinement: S90 rebuilt the
whole index by re-typechecking every triggered session; the refined model reads it from `.meta`.)

**No session-state residue — the `.meta` write is benign (R13).** The S90 "writes nothing" framing
is **superseded**. On branch (c) the indexer **MAY write a `.meta.json`** for a reachable-uncached
module it typechecks — a benign, content-hash-/build-id-invalidated cache artifact on the same
footing as any cache file (a later source edit makes it stale, caught by the existing `CacheStale`
/ `is_cache_valid` gates; a real recompile overwrites it byte-identically). The invariant that
**holds unchanged** is *session-state* isolation: the four `SharedState` maps — `symbol_tables`
(`session_v4.rs:193`), `module_aliases` (`:206`), `prelude_fallback` (`:220`), `introspection`
(`:291`) — **never gain an entry** for an indexed-but-unimported module (the indexer never calls
`register_module` / `notify_typecheck_done` / `record_compiled` / `append_o_path` /
`notify_object_codegen_complete`). **The +neg isolation test asserts the FOUR-`SharedState`-map
invariant** (mirroring `validate_dry_run_discards_does_not_commit`, `pull.rs:1154`) — assert **no
`SharedState` entry, NOT "no disk write"**: a produced `.meta` is expected and benign, and asserting
its absence would contradict the refined model. A found symbol, once `/import`'d, is a **`.meta`
cache-hit** (§25.5) — the live import path loads it from cache rather than re-typechecking from
scratch; the index entry was a search hint, the `.meta` is the durable typecheck result.

**Pillar 2 is cleanly SEPARATE (the retracted shared DTO).** The original "one DTO, two feeders"
coupling is **retracted**. Pillar 2 (in-scope harvest, §23) surfaces in-scope prelude+imports at
sig grain by reading the **live symbol tables directly into the harvest text block**
(`harvest_context`, `src/agent/harvest.rs`) — those symbols are already typechecked and already in
`symbol_tables`, so the harvester just reads name+sig+docstring off them each turn. **Pillar 2
needs no index at all.** So: **Pillar 2 = a live-table read into harvest text; Pillar 3 = two
in-memory lookup indices read-derived from the `.meta` cache over reachable modules.** They share
neither a structure nor a feeder. (If `/search` and the harvester both format a `{name, sig,
module}` line identically, that is a trivial shared *formatter*, not a shared index — an
implementation detail, not an architectural coupling.)

### 25.4 Containment — CF.2, a NEW nice-worker `catch_unwind` (R2, §11.3) — branch (c) only

**CF.2 is a new catch, NOT inherited.** The **priority**-worker loop wraps typecheck in
`catch_unwind` (`worker.rs:1493`/`:1522`), but `nice_worker_loop` runs **bare** — verified: zero
`catch_unwind` in `nice_worker.rs`. A panic on a nice worker today **silently kills that background
thread** (degrading object-codegen capacity invisibly). The indexer runs the **real typechecker**
(`check_forms` → monomorphiser) **only on branch (c)** (cache-miss) over **arbitrary reachable
lib-path ∪ project-root modules**, so a 0432-shaped module (a multi-clause `defn` + unannotated
self-call tripping the monomorphiser `debug_assert!`, `monomorphise.rs:1016`, live in the agent's
debug build) would otherwise **kill an indexer thread**. Branches (a) and (b) do **no** typecheck,
so CF.2's wrap scopes to the branch-(c) `check_forms` call.

**The wrap (mirror `worker.rs:1493`).** The branch-(c) path MUST wrap its `check_forms` in
`std::panic::catch_unwind(AssertUnwindSafe(…))`, reusing the existing `panic_message`
(`worker.rs:1692`) helper. On a caught unwind: convert it to a **logged per-module index-skip**
(record the module in `indexed` with no entries so it is not retried, **and write no `.meta`** —
the typecheck never completed), **drop the throwaway staging**, and **continue the burn-down** —
**never kill the worker thread**. This is **CF.2**, distinct from **CF.1** (the §24 eval-thread
validator catch that ships THIS sprint); CF.2 lands **with the Pillar-3 implementation** (next
sprint). Both mirror the same priority-worker pattern at two distinct seams; neither is inherited
from the other. Searching the library therefore **never crashes the REPL and never silently kills a
nice worker** — a 0432-shaped module is simply absent from results, with a `repl/spec.md §17.19.4`
search-quality note.

### 25.5 Trigger — eager-from-REPL-startup, REPL-only by construction; burn-down re-typechecks only cache-misses (R9b)

> **CORRECTION (2026-06-25 — eager-from-REPL-startup).** This supersedes the S90 §11.1a
> "eager-but-TRIGGERED on first `/search` OR first agent activation" model (and its Principle-6
> "a session that never searches should not pay" rationale). **New model: in REPL mode the
> `IndexModule` burn-down worklist is enqueued eagerly at REPL start-up; in `--run`/`--link`/
> `--release` it is NEVER enumerated.** Rationale (user): a real-site burn-down takes
> seconds-to-minutes, so trigger-on-first-`/search` makes the *first* search pay full
> latency — eager-from-startup instead warms the index during idle interactive time, so the
> first `/search` is fast. The cost-budget concern the old trigger answered is now answered by
> (i) REPL-only gating — batch/release pay nothing — and (ii) lower-than-object-codegen
> priority (below), so warming never delays loaded/prelude codegen.

**Single gate: REPL mode at startup.** When the binary starts in **REPL mode**, the indexer
enumerates the reachable set (§25.1, lib-path ∪ project-root via `pipeline::resolve_module_file`)
onto the `IndexModule` worklist **at start-up** and the nice workers **race ahead** — they do NOT
lazily index one module per query (the retracted lazy model). When the binary runs in
**`--run` / `--link` / `--release`** (batch/release — no REPL, no `/search`) the worklist is
**never enumerated**.

**REPL-only invariant — guaranteed by construction (R9).** Because the sole arming point is REPL
start-up, in batch/release **the indexer never arms → the two indices are never populated →
branch-(c) `cache::write_meta` index writes never fire.** This makes the REPL-only property of the
indexer (including its benign branch-(c) `.meta` writes, §25.3) a **structural guarantee, not an
emergent one**: no batch/release code path reaches the `IndexModule` enumeration, so no
index-driven side effect is possible there. (This composes with §25.8's default-build-stable
invariant: the indexer perturbs neither object-codegen behaviour nor any batch/release output.)

**Prioritization — eager but BEHIND object codegen.** The `IndexModule` worklist is drained
**yielding to the object-codegen worklist** on the shared nice workers: an idle nice worker takes
object-codegen work first (`take_object_codegen`) and only drains an `IndexModule` task when no
object-codegen work is pending. The index warm-up is therefore **eager but lower-priority** —
warming the search index **never delays object codegen of loaded/prelude modules** (preserving the
R9 default-build-behaviour-stable contract, §25.8). The exact yield mechanism (priority ordering on
the claim, or a separate condvar checked after `take_object_codegen` drains) is this doc's detail;
the ruling is the ordering invariant: **object codegen first, index warm-up in the slack.**

**Cost lowered by the refinement (unchanged from §25.1).** The burn-down **re-typechecks only
genuine `.meta` cache-misses** (branch c); modules with a valid `.meta` are **read off the existing
cache** (branch b — a deserialise, not a typecheck), and modules the real path owns are **skipped**
(branch a). So a warm project's start-up burn-down pays a `.meta`-scan plus a few miss-typechecks,
not an N-module re-typecheck. A `/search` that lands **before** the burn-down completes serves
**partial results from the indices-so-far + an "indexing N modules…" note** (a `/repl` UX detail,
`repl/spec.md §17.19`).

**Index → import is now a `.meta` cache-hit (improvement over the retracted S90 model).** Under S90,
a symbol the indexer found and the user then `/import`'d **re-typechecked from scratch** — the index
entry was a throwaway hint. Under the refined model, the miss-typecheck (branch c) already wrote the
module's `.meta` (or branch b read an existing valid one), so a later real `/import` of that module
is a **`.meta` cache-hit** on the live import path — no re-typecheck. The refinement keeps the
start-up warm-up cheap on warm projects (mostly `.meta`-reads, §25.5), taxes no batch/release run
(REPL-only, §25.5), and removes the double-typecheck on subsequent import.

### 25.5b Flush / shutdown — index work is abandon-on-flush, abandon-on-shutdown (R18)

The `IndexModule` burn-down is **best-effort warm-up, never a correctness obligation** — the index
only serves `/search`, which already tolerates partial results (the "indexing N modules…" note,
§25.5). Two consequences for the nice-worker lifecycle:

**Excluded from any correctness-gating flush.** The pre-`--link` hot-flush / priority-promotion
(`nice_worker.rs:70` — the `promote_nice_workers` check that bumps a nice worker to normal priority
before a link) exists to drain the **object-codegen** worklist to completion so the link/cache has
every `.o` it needs. The `IndexModule` worklist is **never part of that correctness-gating flush** —
it is **abandon-on-flush, never drained-to-completion** (the link/cache needs no index). A promoted
nice worker **prefers object-codegen and defers/abandons index work**: this is the §25.5
prioritization ruling (object codegen first, index warm-up in the slack) applied at flush time — a
flush is just the strongest form of "object codegen is pending," so the index worklist yields
entirely. A flush / `--link` path therefore **never blocks on index work**.

**Abandon-on-shutdown.** The burn-down loop checks the shutdown flag **between `IndexModule`
tasks** and **exits promptly** — it does NOT finish the whole burn-down first. Because every `.meta`
write is **atomic** (`cache::write_meta` → `atomic_write`, `cache/object.rs:237` — write-temp +
rename), an abandoned mid-burn shutdown leaves **some modules unindexed (their `.meta` simply
re-derived next session, §25.5 cache-miss branch c) and NEVER a corrupt or partial `.meta`**. There
is no flush-to-completion obligation on the index worklist at shutdown — the index is a derived
read-cache (§25.3), so an incomplete burn-down is a cheap next-session warm-up, not data loss.

### 25.6 `/search` command wiring + the result row (R12, R11, `repl/spec.md §17.19`)

- **A NORMAL default-build `ReplCommand`, NOT `#[cfg(feature="agent")]`-gated (R9a/R12).** A new
  `ReplCommand::Search(&'a str)` variant (`src/repl.rs`) + a `"/search"` arm in
  `parse_slash_command` + a `dispatch_command` arm — **renamed from `/lib-search`** (R12; the prior
  agent-gated `/lib-search` is retracted). It is a **session facility**: the nice-worker indexer
  runs in every session, so `/search` is an ordinary REPL command (like `/exports`/`/list`), not an
  agent capability. The `repl/spec.md §3.1` row tags it `[S90 — design only]`.
- **The agent reaches it via the ordinary pull (R11).** `/search` joins the read-only pull
  allowlist (`src/agent/pull.rs` `ALLOWLIST`) so the agent reaches it through the normal
  tools-as-visible-REPL-commands mechanism (§4.4), exactly like `/syntax`/`/list`/`/exports` — it
  is NOT a bespoke agent tool. (The allowlist row is added at implementation time.)
- **Result row** (`repl/spec.md §17.19.2`, four facets): name, `:Type` signature (via the same
  `format_entry_sig`/`format_type_qualified` Pillar 2 uses — identical grain), originating module,
  and the **exact `(import …)` form** to bring it into scope (e.g. `(import [solver.grid
  [grid-get]])` — synthesized from `module` + `name`). The import-form facet is the actionable
  payoff: the human copy-pastes it; the agent proposes-and-submits it through the Build gate (§15).
  Rendering is `/dev`-owned; this pins the facets + the formatter reuse.
- **How name-vs-scheme is distinguished** (`repl/spec.md §17.19.1`) is at implementation discretion
  (e.g. a leading `(Fn …` parses as a type-scheme query → Index B, else a name fragment → Index A),
  but **both** indices MUST be searchable. Empty / no-match → a "no importable symbols matched" note
  (self-documenting, never an opaque error).

### 25.7 Match semantics — exact OR partial in BOTH indices, calling `/typecheck` predicates (R6)

Match is **exact OR partial in both indices** (R6, §11.4, `design/typecheck/signature-match.md §6`):

- **Partial NAME (Index A)** — case-insensitive **substring** over the symbol name. Trivial,
  int-side, no typecheck involvement.
- **Exact SCHEME (Index B)** — the `/typecheck`-owned pure predicate
  `signature_matches_exact(&Type, &Type) -> bool` (alpha-equivalence, no `CheckState`).
- **Partial SCHEME (Index B)** — the new `/typecheck`-owned sibling
  `signature_matches_partial(&Type, &Type) -> bool`, **STRUCTURAL-CONTAINS** (the query type
  appears as a sub-tree of the candidate scheme, up to alpha-renaming of type vars; e.g. query
  `(Vec Int)` matches candidate `(Fn [(Vec Int)] Bool)`) — a **containment walk over the type tree,
  no unifier**. Full Hoogle subsumption (hole-instantiation + ranking) stays a later `/typecheck`
  upgrade.

The int indexer **calls** both predicates inside its Index-B search; it does **not** own them.

**Predicate sourcing — RESOLVED by `/arch` (R8, §11.8), no longer an open flag.** Both predicates
**export from `cranelisp-typecheck`** (Option A; type equivalence is typecheck's semantics —
**Principle 17** module locality + **Principle 7** single source of truth; inlining int-side would
hand-roll a divergent second judgment that must track `Type`'s representation in lockstep). Cost =
**two additive `cranelisp-typecheck/public-api.txt` lines** (`signature_matches_exact` +
`signature_matches_partial`), each a narrow `fn(&Type, &Type) -> bool` (**Principle 2**), no new
DTO (reuses the existing `Type` boundary), **dispositioned at Pillar-3 implementation time** (next
sprint) per the baseline-diff discipline. **No S90 baseline moves** (Pillar 3 is design-only).
The `_partial` MVP needs **no wildcard token** (the query is a plain type expression), so a `/spec`
consult is triggered only if a later sprint adds query-pattern holes (§11.4).

### 25.8 Implementation gate (clearly IMPLEMENTED-NEXT) + default-build-stable invariant

Pillar 3 implementation is **gated, both required**: (a) the `/typecheck` 0432 root fix (R2-a —
removes the trigger) **and** (b) **CF.2**, the new nice-worker indexer `catch_unwind` (R2-b, §25.4
— the safety net; lands **with** the Pillar-3 implementation, NOT this sprint). Note CF.1 (the
eval-thread validator catch, §24) ships S90 but does NOT cover the indexer — CF.2 is its own catch
at its own seam. Pillar 3 also requires the `IndexModule` worklist integration (§25.1), the
module-state-check coordination (§25.1b), the read-or-produce-`.meta` branch logic (§25.1), and the
two predicates (§25.7). If the 0432 fire lands early enough, implementation pulls forward in-sprint;
otherwise it is next sprint's first item, and **all of §25's design (nice-worker home + separate
worklist, three-branch read-or-produce-`.meta` step, skip-claimed coordination, two `.meta`-derived
indices, residue invariant, trigger, CF.2, command wiring) is the durable target.**

**Acceptance (what a future `/dev` wave must turn green):**

1. **Three-branch coverage.** A reachable module that is (a) registered in the scheduler is
   **skipped**, (b) has a valid `.meta` is **read with no typecheck** (assert `check_forms` is not
   called for it), (c) has no/stale `.meta` is **typechecked once and its `.meta` written** via
   `cache::write_meta`.
2. **Session-state residue +neg (R13).** After a burn-down, assert the four `SharedState` maps
   (`symbol_tables` / `module_aliases` / `prelude_fallback` / `introspection`) are **byte-unchanged**
   — mirroring `validate_dry_run_discards_does_not_commit` (`pull.rs:1154`). Assert **no
   `SharedState` entry, NOT "no disk write"** — a branch-(c) `.meta` is expected and benign.
3. **`.meta` cache-hit on import (R13/§25.5).** A symbol the indexer found (branch b or c) then
   `/import`'d loads its `.meta` from cache on the live import path — assert **no re-typecheck**
   (the improvement over the retracted S90 model).
4. **CF.2 containment.** A 0432-shaped reachable module → graceful per-module index-skip note, **no
   crash, no killed nice worker, no `.meta` written** for the failed module (§25.4).
5. **`.meta`-derived index rebuild (R16).** Clearing the in-memory indices and re-scanning `.meta`
   reproduces the same `/search` results — no `CACHE_SCHEMA_VERSION` bump, no new serialized index.
6. **Batch-mode-inert `_neg` (§25.5 REPL-only invariant).** A `--run` / `--link` invocation over a
   tree containing reachable-but-unimported modules produces **NO index and NO index-driven `.meta`
   writes** — the `IndexModule` worklist is never enumerated outside REPL mode (guaranteed by
   construction; the single arming gate is REPL start-up).
7. **Abandon-on-shutdown leaves no corrupt `.meta` (§25.5b).** Shutdown during an in-flight burn-down
   exits promptly (the loop checks the shutdown flag between `IndexModule` tasks); the resulting cache
   contains **no corrupt or partial `.meta`** (atomic write-temp+rename), and the **next session
   rebuilds the index cleanly** (unindexed modules re-derive via branch b/c).
8. **Flush / `--link` does not block on index work (§25.5b).** A flush / priority-promotion / `--link`
   path drains only the object-codegen worklist to completion and **abandons the `IndexModule`
   worklist** — assert the link path does not wait on any in-flight index task.

**Default-build-behaviour-stable invariant (R9, §11).** Because Pillar 3 is a **non-agent
default-build** facility, it does NOT carry the byte-identical-feature-OFF invariant (that scopes to
Pillars 1/2/4). It carries instead **two** structural guarantees: (i) **REPL-only by construction**
(§25.5) — the `IndexModule` worklist arms only at REPL start-up, so `--run`/`--link`/`--release`
enumerate no worklist, populate no index, and fire no branch-(c) `.meta` write (the batch-mode-inert
`_neg`, acceptance 6); and (ii) **the indexer must not perturb object-codegen behaviour or the REPL
contract** — satisfied structurally by the §25.1 separation (the `IndexModule` worklist is a
distinct claim, never entangled with `take_object_codegen` / the `.o` lifecycle) **and** by the
§25.5 prioritization ruling (index warm-up yields to object codegen, so warming the search index
never delays object codegen of loaded/prelude modules). (This sprint the invariant is **trivially
satisfied** — Pillar 3 is design-only, nothing is added to the default build; it becomes load-bearing
at implementation time.)

### 25.9 The seeded direct-read feed — a SECOND feed alongside the `.cl` worklist (E1, S108, `repl/spec.md §17.19`/§17.19.3)

**Status: LANDED S108 (Increment 2).** User testing surfaced that `/search vec-len` returned "no
importable symbols matched" although `primitives/vec-len` is a real importable primitive: the
built-in **seeded** modules (`primitives`, the synthetic `macros`) have **no `.cl` file**, so the
§25.1 file-enumeration worklist (`resolve_module_file` over lib-path ∪ project-root) never reached
them. The user ruled (2026-07-11) that `/search` scope SHALL include the seeded modules; `/arch`
approved the mechanism with **no `cranelisp-types` / cache-schema / public-API change**.

**Seeded modules are indexed by a DIRECT read of the live symbol table — NOT the three-branch file
dance (§25.1).** They are already typechecked-and-mounted by `mount_synthetic_modules`
(`bootstrap.rs`), so there is **nothing to stage, nothing to discard, and no `.meta` to write**: the
whole read-or-produce-`.meta` step (branches a/b/c, §25.1) is bypassed. `arm_burndown`
(`session_v4/index_worker.rs`) reads each seeded module's `SessionSymbolTable` straight out of
`SharedState.symbol_tables`, extracts its public entries (`public_entries_from_table`), and records
them via `record_preindexed`. This makes the indexer a **two-feed** producer over the ONE pair of
indices (§25.3): the `.cl` file worklist (typecheck-to-index, branches a/b/c) and the seeded
direct-read (no typecheck). Both land `{symbol, scheme, modulepath}` rows in Index A / Index B
identically — a seeded row and a file-derived row are indistinguishable at `/search` time.

**Single-source the seeded list — no name-literal in the indexer (Principle 19).** The list of which
modules are seeded-importable is `bootstrap::seeded_importable_modules()` — `primitives` + the
seeded `macros`, sourced from the module bootstrap actually mounts, NOT a `["primitives","macros"]`
literal inside `index_worker`. It deliberately **excludes** the root `""` module (special-forms-only
— `if`/`let`/… are always available and are not importable targets) and `prelude` (the implicit
outer scope — its symbols are re-exports, not an importable home, and the file enumerator already
skips it). This keeps "what bootstrap mounts" and "what `/search` treats as seeded-importable" from
drifting: bootstrap owns the fact, the indexer reads it (Principle 7 single-source-of-truth, Principle
19 no-module-privileged-by-name).

**`record_preindexed` counts a seeded module in BOTH tallies, atomically (the accounting invariant).**
`pending_count` — the signal that drives BOTH the "indexing N module(s)…" not-ready note (§25.10) and
the completion latch — is defined as `enumerated_total − indexed.len()` (the private `pending()`
helper on `IndicesInner`, the ONE place the subtraction lives). A seeded module is already fully
indexed the instant it is read, so `record_preindexed` increments **`enumerated_total` AND inserts
into `indexed`** under the one mutex. Counting it in `enumerated_total` as well is load-bearing: were
it added to `indexed` only, `pending_count` would **undercount** N and the not-ready note / completion
notice would fire early; were it added to `enumerated_total` only, it would be **perpetually
pending**. Because it lands in both, a seeded module is **never "pending"** — it never wedges the
burn-down and never inflates the note's N. `record_preindexed` is also idempotent (a re-add of an
already-`indexed` module neither double-counts `enumerated_total` nor re-inserts).

**The DISJOINT-FEEDS invariant — the seeded feed and the file feed must not overlap (Principle 18).**
A user file literally named `primitives.cl` / `macros.cl` on the project root or a lib-dir would
otherwise be enumerated onto the `.cl` worklist AND be counted a second time by the seeded
`record_preindexed` for the same `ModuleFullPath` — a double-count that (before the fix, review
finding I-1) left `pending_count ≥ 1` **forever**: `; search index complete.` never fired and every
`/search` showed a perpetual `indexing 1 module(s)…` note. `arm_burndown` closes this structurally:
it retains the seeded names **out** of the enumerated file `modules` list
(`modules.retain(|m| !seeded_modules.contains(m))`) **before** arming the worklist and **before** the
seeded direct-read — so the two feeds are disjoint by construction. **The seeded module WINS** on a
name collision: it is already typechecked-and-mounted, so the same-named user file is simply dropped
from the file set rather than the reverse. (Guarded deterministically —
`search_seeded_file_name_collision_does_not_wedge_pending_note` — not by a race.)

### 25.10 The lifecycle-message latch — not-ready note + completion notice (E2, S108, `repl/spec.md §17.19.3`)

**Status: LANDED S108 (Increment 2).** Two lifecycle messages make the background burn-down visible;
§17.19.3 defines them as **exclusive** states that MUST NOT be conflated. Both are driven off
`pending_count` and coordinated by a one-shot latch on `IndicesInner` (under the existing index
mutex), so no worker-side stdout and no `ExternalPrinter` TTY-fork is involved.

**The not-ready note — served inline by `handle_search`.** A `/search` issued before the burn-down
completes MUST say so rather than return a silent (or misleading "no match") result. `handle_search`
(`src/repl.rs`) reads `pending_count()`; when `> 0` it appends the note
`; indexing N module(s)… (results may be incomplete)` (N = the pending count) to whatever partial
results the indices-so-far hold, and — on the **empty** partial-result path — serves the note
**instead of** the `; no importable symbols matched '<q>'` note. This is the §17.19.3
non-conflation MUST (review finding I-2): "nothing matched yet, still building" (retry) and "nothing
matched a complete index" (rephrase) call for **opposite reader actions**, so while `pending > 0` the
empty path serves ONLY the not-ready note, and the no-match note is served ONLY at `pending == 0`.
The message selection is single-sourced in the **pure** free fns `indexing_note_text(pending)` and
`empty_result_message(query, pending)` (no `&self`, no side effects) so the two states are exclusive
by construction and unit-testable at the seam without driving a session; the not-ready-note text has
ONE source of truth that both the empty-result and the partial-result-append paths derive from.

**The completion notice — async, at the prompt boundary.** `; search index complete.` (lower-case,
trailing period, no count) announces the burn-down finished. It is emitted by the **`main.rs` read
loop** at the clean prompt boundary — polled BEFORE the prompt is written, so it lands only between a
completed prompt cycle and the next prompt (no mid-line interleave), written by the **sole writer**
(the read-loop thread; there is deliberately no worker-side stdout).

**The one-shot latch (`IndicesInner`).** Three booleans coordinate the pair: `note_shown` is set by
`mark_note_shown()` the first time `handle_search` serves a not-ready note; `announced` guards the
completion notice to fire at most once; and `take_completion_notice()` is a **check-and-set** that
returns `true` exactly once — when `armed && pending() == 0 && note_shown && !announced` — setting
`announced` on that firing call so every later call returns `false`. The `note_shown` gate is the
**timing-(b)** decision (USER-CONFIRMED 2026-07-11): the completion notice fires **only after** a
not-ready note was actually shown this session, so a session that never saw the index building sees
**neither** message — least noise, closes only a loop the user watched open, and (critically) keeps
every existing non-TTY golden untouched, since an unconditional notice would land at a
nondeterministic prompt and flake goldens.

**The `is_interactive()` gate — non-TTY sessions never emit it (the byte-identical contract).**
Gating on `note_shown` alone is **not sufficient** for determinism: a piped/non-TTY session CAN latch
`note_shown` (the inline not-ready note is synchronous `/search` output served on the non-TTY branch
too), so a piped run catching the burn-down mid-flight could emit the async completion line at a
timing-dependent boundary and break the §10.8 byte-identical scripted/piped contract (review finding
I-3). The `main.rs` poll therefore ALSO gates on `input.is_interactive()` (`src/repl_input.rs` —
`false` for `ReplInput::Piped`), making the completion path structurally unreachable on non-TTY. So
the notice requires BOTH a not-ready note shown this session AND an interactive TTY; every e2e golden
(all non-TTY) is guaranteed to never see it.

---

## 26. S90 cross-skill coordination (flag to `/sprint` at the Phase-3 exit gate)

- **`/docs`** — owns `src/syntax/cheatsheet.txt` content (topic taxonomy + verified-compiling
  examples, `=== topic: <name> ===` delimiter). The int parser (§22.1) depends on that exact
  delimiter and single-file shape — already contracted (`user/syntax-cheatsheet-plan.md`). Sync
  obligation: the primer topic-name line (§22.4) must match the asset's topics.
- **`/repl`** — owns the `/syntax`, harvest-sig-grain, `/search` (renamed from `/lib-search`, R12;
  + the session-facility framing + the "indexing N modules…" partial-result note, §25.5/§25.6), and
  `CRANELISP_AGENT_LOG` experience (`repl/spec.md §17.17–§17.20`). The int wiring honours those
  contracts; the exact rendered bytes are `/dev`-owned within them. **`CRANELISP_AGENT_LOG`** (the
  §27 log path env var) is the `/repl`-pinned name — int consumes it verbatim.
- **`/typecheck`** — owns the 0432 root fix (R2-a) and **both** §25.7 match predicates,
  `signature_matches_exact` (exact-shape, alpha-equivalence) AND `signature_matches_partial`
  (structural-contains). **RESOLVED (R8, §11.8):** both **export from `cranelisp-typecheck`**
  (Option A; Principles 17+7) — two additive `public-api.txt` lines dispositioned at Pillar-3
  implementation time (next sprint), no S90 baseline move. The int indexer calls them; the prior
  "export vs inline" open flag is closed.
- **`/qa`** — failing tests owed: the §24 (CF.1) containment guard (0432-shaped form → graceful
  `Err`, no panic on the eval thread), the Pillar-2 sig-grain harvest assertions (§23.3), the §22.5
  primer `match`-shape repro (corrected example compiles), and (next sprint) the §25 Pillar-3 tests
  — per §25.8 acceptance: the **three-branch coverage** (skip-claimed / read-`.meta` / typecheck-and-
  write-`.meta`), the **session-state residue +neg** (asserts the four `SharedState` maps unchanged,
  NOT "no disk write" — mirrors `validate_dry_run_discards_does_not_commit`, R13), the **`.meta`
  cache-hit on import** (no re-typecheck, R13/§25.5), the **CF.2 nice-worker containment**
  (0432-shaped reachable module → index-skip, no killed worker, no `.meta` written), the **`.meta`-
  derived index rebuild** (R16), and `signature_matches_exact`/`signature_matches_partial` unit
  suites.
- **`/arch`** — the §25.7 predicate-sourcing ruling is RESOLVED (R8 — export from
  `cranelisp-typecheck`). The read-or-produce-`.meta` refinement (R13–R16) adds **zero new
  cross-crate edge and zero backend baseline movement** (R14 — the `cranelisp_backend::cache`
  read/write/validate trio is already public; int already depends on it). No other cross-crate seam
  anticipated (§21).
- **`/dev` (src/)** — Phase 5: Pillars 1/2/4 + the §24 floor (serial, source-touching). The
  §22.5 primer `match` fix lands with Pillar 1.

---

## 27. Pillar 4 — silent greppable agent log (`src/agent/log.rs`, R5) (SHIPS S90)

A **silent, persistent, structured** log of the agent's activity — the *recording* half of
self-tuning, captured now so insight can be hand-extracted (`grep`/`jq`) and automated later. Per
the `/arch` ruling (R5/§11.6), it is a **new feature-gated sibling sink**, **NOT** a `trace.rs`
extension (`trace.rs` is ephemeral stderr wire-debug; this is persistent file-backed JSONL with
stable keys — different lifetime, sink, consumer). It takes the §8 `[R5]` reserved telemetry slot,
landed this sprint.

### 27.1 The module — `src/agent/log.rs`, a sibling sink

New file `src/agent/log.rs`, `pub(crate)`, fully `#[cfg(feature="agent")]` (declared
`pub mod log;` in `src/agent/mod.rs:21–29` alongside `harvest`/`pull`/`trace`). It **consumes the
event vocabulary the loop already produces** — it does not invent new events. The append points are
the existing record sites (no new control flow):

| Event | Where it already fires | Logged fields |
|---|---|---|
| model exchange | `agent_turn` loop, `mod.rs:241/245` (request/response) | `event=exchange`, turn index |
| pull | `run_pull`, `pull.rs:149` (a visible read command) | `event=pull`, `tool` (command), `symbol`/arg |
| validator-repair iteration | `validate_and_repair`, `pull.rs:586` loop (per iteration) | `event=repair`, `iteration`, `error_class` (the triggering compiler error), `symbol`, `module` |
| submit / commit | `submit_clean_form`, `pull.rs:359` (committed) | `event=submit`, `symbol`, `module` |
| give-up | `run_submit` give-up arm, `pull.rs:262`; turn-end give-up, `mod.rs:313` | `event=give_up`, `symbol`, `module` |

The log call is a **one-line append at each site**, guarded by the env gate (§27.2). The
**repair-iteration count + triggering error class** — the user's primary struggle signal — comes
free from the `validate_and_repair` loop (`pull.rs:586`), which already iterates and already holds
the compiler error string; the log records each iteration with its `error_class` and `iteration`.

### 27.2 Env-configured path, off by default, graceful (`repl/spec.md §17.20.2`)

The log is opt-in via **`CRANELISP_AGENT_LOG`** (the `/repl`-pinned name) — a **path**, sibling to
`CRANELISP_AGENT_TRACE`:

- **Set to a path** ⇒ each event **appends** one JSON object (one line) to that file (persistent
  across turns + the session). **Unset/empty** ⇒ **no log written**, no file created, **no cost
  paid** (`log_enabled()` returns false; the append points early-return — mirroring
  `trace::trace_enabled()`, `trace.rs:38`).
- **Graceful on an unwritable path** (`§17.20.2`): if the path cannot be opened/written, the log
  **degrades silently** — it does **not** crash the session and does **not** spew errors into the
  REPL (logging is a side channel; its failure never disturbs the session). The write is a
  best-effort `OpenOptions::new().create(true).append(true)` + `writeln!`, errors **discarded**
  (`let _ = ...`), exactly as `trace.rs` discards its `eprintln!` outcome.
- **Silent — nothing extra in the REPL** (`§17.20.1`): writing the log produces **no** banner, no
  "logging to …" line, no per-event echo. The human's session is **byte-identical** to the same
  session with logging off. It is a **dev-session artifact** (NG4) — never in a `--link`/`--release`
  artifact (feature-gated + REPL-only).

### 27.3 Format — persistent JSONL, stable greppable keys (`repl/spec.md §17.20.3`)

**JSONL** — one JSON object per line, one line per event — so `grep`/`jq` extract insight without a
query UI. Serialized via the existing `serde_json` dep (already pulled by the `agent` feature,
`Cargo.toml`). The **stable, greppable keys** (the `/repl` experience requirement; exact vocabulary
`/dev`-owned within it):

```json
{"event":"repair","symbol":"fib","module":"user","iteration":2,"error_class":"TypeError","ts":...}
{"event":"pull","tool":"source","symbol":"grid-get","ts":...}
{"event":"give_up","symbol":"fib","module":"user","ts":...}
```

At minimum, every record carries an **`event`** type (`exchange`/`pull`/`repair`/`submit`/
`give_up`); records that have one carry the **`symbol`**, the **`module`**, a repair's
**`error_class`** (the triggering compiler error class) + **`iteration`** count, and a pull's
**`tool`**. **Acceptance (operational):** a one-line `grep`/`jq` over the file extracts every
repair event with its triggering symbol/error and every exploration pull (`SPRINT.md §Pillar 4`).
A tiny serializable `LogEvent` struct (`#[derive(Serialize)]`, int-private) is the one new type;
**zero** `cranelisp-types`/public-API impact (§11.8).

### 27.4 Relationship to `trace.rs` (kept distinct, R5)

`trace.rs` (`CRANELISP_AGENT_TRACE`) is **ephemeral stderr** wire-debug (the rig message sequence,
for watching one session live). `log.rs` (`CRANELISP_AGENT_LOG`) is **persistent file JSONL** insight
(the struggle signal, for mining by hand later). Different lifetime, sink, consumer — **two sibling
sinks, not one overloaded module** (Principle 6 — keep concerns separate). Both env-gated, both
`#[cfg(feature="agent")]`, both silent-by-absence, both NG4 dev artifacts.

### 27.5 Testability (Principle 5, for `/qa`)

- with `CRANELISP_AGENT_LOG` set, a repair iteration appends a `{"event":"repair",...}` line
  carrying the symbol + error_class + iteration (positive);
- with it unset, **no** file is written and the session output is byte-identical (+neg — the
  silent-by-default guarantee);
- an unwritable path degrades silently — the session runs to completion, nothing in the REPL (+neg);
- feature-off, the log module does not exist (the byte-identical gate).

---

## 28. Persistent TRACE sink + log↔trace correlation (`turn`) (S90 addendum, SHIPS S90)

*User direction (2026-06-25).* Pillar 4's JSONL log (§27) is **metadata-only** — `event`, `symbol`,
`module`, `error_class`, `iteration`, `tool`, `ts`. That is the right shape for the **index** (a
`grep`/`jq` skim of *where* the agent struggled) but too thin to *read* what actually happened — the
full request the model saw, the full response it gave, the full compiler error text. That content
**already exists** in `trace.rs` (the `format_request_trace`/`format_response_trace` transcript), but
it is (a) **ephemeral** — `eprintln!` to stderr, gone when the terminal scrolls — and (b)
**truncated** — `TEXT_TRUNCATE = 80` + `compact()` collapse every form/error/prose to one short line.

The addendum makes the **trace the CONTENT record** the same env-path way the log is the **index**:
persist the trace to a file, **untruncated**, and **join the two by a shared `turn` id**. The log
stays compact (you grep it to find the interesting turn); the trace carries the full transcript for
that turn (you read it once the index pointed you there). This takes the §8 trace slot's
"persistent" upgrade with **no model, no public-API, no `cranelisp-types` movement** (§11.8) — it is
two int-private edits (`trace.rs`, `log.rs`) plus a one-field thread-through.

### 28.1 TRACE persistent sink — `CRANELISP_AGENT_TRACE=<path>`, full content, path-only

`CRANELISP_AGENT_TRACE` **changes meaning from a `=1` toggle to a PATH** (sibling-identical to
`CRANELISP_AGENT_LOG`, §27.2 / `log.rs:36–54`):

- **Set to a path** ⇒ each request/response trace is **appended** to that file (persistent across
  turns + session). The **stderr `eprintln!` sink is REMOVED** — the two `eprintln!` loops in
  `trace.rs::emit_request` / `emit_response` (`trace.rs:54–56` / `64–66`) are replaced by a
  best-effort file append. The persisted trace is **path-only**; there is no longer an ephemeral
  stderr mode. (This is the deliberate user-directed swap: the §27.4 "ephemeral stderr vs persistent
  file" distinction collapses — *both* sinks are now persistent file sinks, differentiated by
  **grain** — log = index, trace = content — not by lifetime.)
- **Unset/empty** ⇒ off, no file, no cost — the gate becomes `trace_path() -> Option<String>`
  (byte-for-byte the `log.rs::log_path()` shape, `log.rs:42–54`), replacing the truthy
  `trace_enabled() -> bool` (`trace.rs:38–46`). `emit_request`/`emit_response` early-return on `None`.
- **Graceful** — the append is `OpenOptions::new().create(true).append(true).open(path)` +
  `write_all`, the outcome **discarded** (`let _ = …`) — an unwritable path never crashes the
  session and never spews into the REPL. Identical to `log.rs::record` (`log.rs:131–148`).
- **Silent** — like the log, the trace file is the ONLY side effect; the REPL transcript is
  byte-identical with the trace off. NG4 dev-session artifact, `#[cfg(feature="agent")]`, REPL-only.

**FULL, UNTRUNCATED content (the core requirement).** The persisted lines must carry the **whole**
form/error/prose — not the `compact()`-collapsed 80-char head. The truncation must move **out of the
persisted path**:

- `TEXT_TRUNCATE` + `compact()` exist for **eyeball-on-one-line** rendering. With the stderr sink
  gone, the persisted path has no one-line constraint — a persisted trace is *read in a file*, where
  multi-line forms are an asset, not noise.
- **Recommendation: the formatters take a render mode rather than duplicating.** Add a private
  `Grain { Compact, Full }` (or a `bool full`) param threaded into `format_request_trace` /
  `format_response_trace` / `format_turn` / `format_call`, and have `compact()` become
  `render_text(text, grain)` — `Compact` keeps the existing newline-collapse + `TEXT_TRUNCATE` cut;
  `Full` returns the text verbatim (no collapse, no cut). `emit_request`/`emit_response` (the only
  persisted callers) pass `Full`. This keeps ONE formatter (Principle 7 — single-source-of-truth: no
  parallel "full" formatter mirroring the compact one) and preserves the existing unit tests, which
  exercise the `Compact` grain directly. The `…`-truncation / `⏎`-collapse tests stay as `Compact`
  assertions; one new `Full`-grain test asserts a >80-char form survives verbatim.
- (The line **prefix** — `[agent-trace] →request …` / `←response …` — stays; it is the per-turn
  delimiter a reader and the §28.2 correlation both key on. Only the *body* un-truncates.)

### 28.2 Shared `turn` correlation key — one id in BOTH sinks

A per-turn index joins an index record (log) to its content record (trace). The source is the
**`agent_turn` loop step** — `turn_step` (`mod.rs:241`), the `0..MAX_TURN_ITERATIONS` counter that
already drives one model exchange per iteration. The 1-based `turn_step + 1` is the correlation id.
The §27 `exchange` record already emits it — but on the **`iteration`** field (`mod.rs:248`,
`LogEvent::new("exchange").iteration(turn_step + 1)`), which is overloaded (a *repair* also uses
`iteration` for its own per-iteration count, §27.1). The addendum gives correlation its **own**
field so the two never collide:

- **`log.rs` — add a `turn: Option<usize>` field to `LogEvent`** (`log.rs:62–83`), a
  `skip_serializing_if = "Option::is_none"` `Option` like the other optionals, with a fluent
  `turn(usize)` setter (mirroring `iteration`, `log.rs:115–118`). It is the **only** new field; the
  log stays otherwise compact (§27.3 — no content fields; `turn` is an *index* key, not content).
- **`trace.rs` — a per-turn marker line.** `emit_request`/`emit_response` gain a `turn: usize` param
  and stamp it into the trace's header/marker (e.g. `[agent-trace] turn=3 →request …` /
  `turn=3 ←response …`) — the same id the log carries on its `turn` field. A reader (or a join
  script) lifts `turn=N` from the trace and `"turn":N` from the log; one grep over each file by the
  same N reconciles "the agent struggled on `fib` at turn 3" (log) with "here is the exact request
  the model saw and the exact response it gave at turn 3" (trace).

**Where the id is sourced + threaded.** `turn_step` is local to `agent_turn` (`mod.rs:241`). It must
reach **both** sinks:

- **Log side (already half-wired).** The `exchange` record at `mod.rs:247–249` switches from
  `.iteration(turn_step + 1)` to `.turn(turn_step + 1)`. Every OTHER record site that wants
  correlation (the §27.1 table — `pull` `pull.rs:228`, `repair` `pull.rs:631`, `submit`
  `pull.rs:404`, `give_up` `pull.rs:291` + the turn-end give-up `mod.rs`) gains `.turn(<current
  turn>)`. Those sites run **inside the `agent_turn` loop body** (directly, or one call deep in
  `run_pull`/`run_submit`/`validate_and_repair`), so the current `turn_step + 1` must be **threaded
  to them**. Recommendation (smallest seam): stash the current 1-based turn on `AgentState` —
  `current_turn: usize`, set once per loop iteration at the top of the `agent_turn` body
  (`state.current_turn = turn_step + 1`), read by the record sites via `self.agent` (every record
  site already holds `&mut self`/`&self`). This avoids threading a `turn` param down four call
  chains (`run_pull`/`run_submit`/`submit_clean_form`/`validate_and_repair`) — Principle 1
  (decoupling over convenience): the loop owns the turn, the sites read it off shared state, no
  signature churn. The repair record keeps BOTH `.turn(current)` (the correlation) AND
  `.iteration(iteration + 1)` (its own repair-loop count) — they are now distinct fields.
- **Trace side (the crux — the trace fires at a DIFFERENT seam from the log).** The trace
  `emit_request`/`emit_response` are called inside `RigModel::complete` at the **rig boundary**
  (`provider.rs:176` / `199`), one membrane layer below `agent_turn` — and `turn_step` is **not in
  scope there**. Two consequences the implementer must honour:
  1. The cleanest thread-through is to **carry the turn on `AgentRequest`** — add `pub turn: usize`
     to `AgentRequest` (`types.rs:115–127`), set by `assemble_request` (`mod.rs:346`) from the
     `current_turn` stashed on `AgentState` above (or pass it through). `RigModel::complete` then
     reads `request.turn` and passes it to `emit_request`; for the response it reuses the same
     `request.turn` (the response belongs to the request's turn). This keeps the rig membrane
     ignorant of the loop — it just forwards the request's own turn id. `AgentRequest` derives
     `Default` (`types.rs:115`), so the new `usize` defaults to `0` for the test-fixture
     constructions in `trace.rs`/`pull.rs` tests — harmless (turn 0 = "unstamped", never collides
     with the 1-based live ids).
  2. **The trace fires ONLY on the rig path, not the stub** (`provider.rs:170` `RigModel` is the
     sole `emit_*` caller; the deterministic `stub.rs` `AgentModel` never calls them). This is
     unchanged from today and correct — the persisted trace is a **live-provider** wire record; the
     stub path is covered by the `#[cfg(test)]` request-capture assertions (`agent/mod.rs`, the
     CLAUDE.md "stub captures every `AgentRequest`" lane), not by the trace file. Note for `/qa`:
     the §28 trace-file e2e therefore needs a **rig-backed** model or a stub that also emits — the
     §27 log e2e (which fires from `agent_turn`/`pull.rs`, provider-independent) does NOT have this
     constraint. Flag this asymmetry so a §28 trace test is not written against the bare stub
     expecting a file.

### 28.3 Share a small file-append helper (Principle 7) — RECOMMENDED

With the stderr sink gone, `trace.rs` and `log.rs` now perform the **identical** operation: read an
env var as a path (absence/empty = off), and best-effort-append text to it, errors discarded. That
is **one mechanism appearing twice** — exactly the Principle 7 (single-source-of-truth) / Principle 6
(complexity budget) smell. **Recommendation: extract a shared append helper.** A small free fn —
`fn append_to_env_path(var: &str, content: &str)` (home: a new tiny `src/agent/sink.rs`, or a
`pub(crate)` fn on `log.rs` that `trace.rs` calls) — owns the env-gate + `OpenOptions` create/append
+ `write_all` + `let _ =` discard ONE time. Then:

- `log.rs::record` serializes its `LogEvent` to a JSON line and calls
  `append_to_env_path(LOG_VAR, &line)`.
- `trace.rs::emit_request`/`emit_response` format their `Vec<String>` (joined by `\n`, trailing `\n`)
  and call `append_to_env_path(TRACE_VAR, &block)`.

Each module keeps its **own env var const** (`LOG_VAR`/`TRACE_VAR`) and its **own content shape**
(JSONL vs trace-text) — the helper owns only the **mechanism** (gate + append + swallow), which is
genuinely identical. This is the right cut: the differing concerns (what to write) stay separate; the
identical concern (how to append-to-an-env-path silently) is single-sourced. The alternative — each
module owning its own copy — re-introduces the very duplication the project's CLAUDE.md repeatedly
calls out (e.g. the retired `resolve_module_alias` byte-identical re-impl, S81 W-G 0303). **Recommend
the shared helper.** (If the implementer finds the two append shapes diverge — e.g. the trace wants a
different open-mode — fall back to per-module; but as specified they are identical.)

### 28.4 What §28 does NOT change (zero-movement)

- **No model/public-API/`cranelisp-types` movement** (§11.8). The three edits are int-private:
  `AgentRequest.turn` (int-private struct, `types.rs`), `LogEvent.turn` (int-private, §27.3), the
  `trace.rs` grain param + sink swap. No facade delta, no FIXME `target: /arch` anticipated.
- **The log stays compact** (§27.3) — `turn` is the ONLY field added; no content fields migrate into
  the log. Content lives in the trace; the log remains the greppable index.
- **`/repl` owns the env-var semantics wording.** `CRANELISP_AGENT_TRACE` changing from `=1` to a
  PATH is a user-facing config change recorded in `repl/spec.md §17.10` (the trace env row) +
  §17.20 (alongside `CRANELISP_AGENT_LOG`) — that file is `/repl`-owned, NOT edited here. Flag to
  `/repl` (§28.6).

### 28.5 Testability (Principle 5, for `/qa`)

- **Full content (positive):** with `CRANELISP_AGENT_TRACE=<path>` and a >80-char form in the
  transcript, the trace file carries the form **verbatim** (no `…`, no `⏎` collapse) — the
  un-truncation guard. (The existing `long_text_is_compacted_and_truncated` /
  `empty_id_renders_as_none` tests stay, re-pinned as **`Compact`-grain** unit tests of the
  formatter; one new **`Full`-grain** test asserts verbatim survival.)
- **Path-only / no stderr (+neg):** the stderr sink is gone — with the env set, **nothing** is
  written to stderr (a redirect-stderr assertion is empty); the content is in the file only.
- **Correlation (positive):** a turn that pulls then submits produces, for the SAME `turn=N`, a
  trace block at `turn=N` and log records carrying `"turn":N` — a join on N reconciles the two.
  Specifically: the `exchange` log line and the `submit`/`repair` log line for one turn share the
  same `turn`, and the trace block for that exchange carries the matching `turn=N`.
- **Off / unset (+neg):** unset/empty ⇒ no trace file, byte-identical session (the silent gate,
  mirroring §27.5).
- **Graceful (+neg):** an unwritable trace path degrades silently — session runs to completion,
  nothing in the REPL.
- **Shared helper (if extracted):** a single `append_to_env_path` test covers gate-off, append, and
  unwritable-path-swallow once; `log.rs`/`trace.rs` tests then assert only their content shape.

### 28.6 Coordination points (add to §26 / flag at the Phase-3 exit gate)

- **`/repl`** — `repl/spec.md §17.10` + §17.20: record `CRANELISP_AGENT_TRACE` as a **PATH** (no
  longer `=1`), persistent + silent + full-content, sibling to `CRANELISP_AGENT_LOG`; note the
  removal of the stderr trace mode and the `turn` correlation key the two share.
- **`/qa`** — the §28.5 tests, with the §28.2(2) caveat: the trace-file e2e needs a rig-backed (or
  emit-capable) model, since `emit_*` fires at the rig boundary, not from the stub path.
- **`/dev` (src/, narrow)** — implement against §28: the `trace.rs` sink swap + grain param
  (§28.1), the `turn` field on `LogEvent` + `AgentRequest` + the `AgentState.current_turn` stash and
  the record-site `.turn(…)` calls (§28.2), the shared `append_to_env_path` helper (§28.3). Serial
  with the other S90 `/dev` steps (broken worktree isolation). Keep feature-OFF byte-identical.
- **`/arch`** — none anticipated (zero cross-crate movement, §28.4).

---

## 13b. Cross-skill handoffs / FIXMEs (S89)

Per the protocol (filed as `design/arch/fixmes/NNNN-*.md` when `/sprint` schedules; not
authored from this design pass): the §19 + §20.6 coordination points are the S89 handoffs.
No new `cranelisp-types` field is anticipated (R4) — the one used (`module_preamble`) landed
S88 (FIXME 0428). The validator dry-run + write-arm allowlist widening + the `--yes` consent
auto-answer (§20) are int-internal, no facade delta (the Phase-2 ruling + the §7.4 `--yes`
ruling); no FIXME needed unless Phase-5 surfaces a cross-crate seam.

## Next skills

- `/repl` — settle the agent experience (frame, `/ask`, `--agent` row, reverse-query UX,
  U6 disclosure wording) against this mechanism; **S89**: agent-input prompt glyph, markdown
  frame, Build confirm + Document consultative wording, validator give-up wording (§19).
- `/dev` (int, narrow) — implement against this design once `/qa`'s failing tests land
  (Phase 5). Source-touching steps serialize (broken worktree isolation). **S89**: three
  clusters serial — Cluster A render (`src/agent/render.rs`, §14, R1/R2), Build write arm
  + validator (§15/§16, R3), Document edit (§17, R4); plus the `--yes` consent auto-answer
  (§20 — flag parse `main.rs:413/519`, `enable_agent`→`AgentState.auto_accept`, the
  `agent_auto_accept()` gate at §15.2/§17.2, the once-only first-use notice §20.4); the
  validation-floor guard (§20.3) is structural — `auto_accept` must never reach the
  validator. Keep feature-OFF byte-identical (§18).
- `/qa` — draft the failing tests (classifier routing, stub-`AgentModel` loop, harvest
  ladder, reverse-query scan) per §11. **S89**: stage→check→discard repair loop (Lane A,
  §16.5), confirm-gated-write + allowlist-refuses-non-writes (§15.4), Document round-trip +
  harvest read-back (§17.4), and the Cluster-A ANSI-leak narrow repro (§14.6).
- `/arch` — only if the `rig-core` dep wants a workspace-dep declaration, or if a
  cross-crate seam surfaces during implementation (none anticipated; R4 pins zero movement).

**S90 (fluency phase — §§21–27):**
- `/dev` (src/, narrow) — Phase 5, serial: Pillar 1 `/syntax` (`src/syntax.rs` parser +
  `ReplCommand::Syntax` + allowlist row + primer cross-ref, §22; incl. the §22.5 primer
  `match`-shape fix), Pillar 2 harvest sig-grain (§23 — enrich `harvest_context`, reuse
  `format_entry_sig`), the §24 `catch_unwind` containment floor (`checked_check_forms`), Pillar 4
  `src/agent/log.rs` (§27). Pillar 3 (§25) is design-only — implement next sprint (gated on 0432).
- `/qa` — S90 failing tests: §24 containment guard (0432-shaped → graceful `Err`, no panic),
  §23.3 sig-grain harvest assertions (sig byte-identical to `/sig`; prelude gate +neg; budget
  grain-degrade +neg), §22.5 primer `match`-shape repro, §27.5 log (event line on repair; silent
  +neg; unwritable-path +neg), and (next sprint) §25 zero-residue + containment tests.
- `/arch` — the §25.3 predicate-sourcing ruling owed (export `signature_matches_exact` from
  `cranelisp-typecheck` vs inline int-side). No other cross-crate seam anticipated (§21).
- `/typecheck` — 0432 root fix (R2-a) + `signature_matches_exact` (§25.3) — the Pillar-3 next-sprint
  prerequisites.
