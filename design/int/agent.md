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
agent action a transcript line), **Testability** (Principle 5 — `rig-core`'s
`CompletionModel` is a trait §6, so the agent loop can be driven against a stub
`CompletionModel` impl with zero network).

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
| `agent/provider.rs` | Runtime provider selection (§6.4) — builds a `rig`-backed `CompletionModel` for the configured provider (Anthropic default / Ollama local), reads model-id + key/endpoint from runtime config, and reports dormancy. NO owned LLM-protocol code: rig owns the wire. |
| `agent/request.rs` | Translation between the agent's neutral turn vocabulary (primer/harvest/transcript/tool-defs, §3.3/§6.1) and rig's `CompletionRequest` + `Message`/tool-call types. The one place coupled to rig's request/response shapes. |
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
    resp = self.model.completion(req).await?  // rig CompletionModel; streamed; tool-calls surface here (§6)
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

`AgentState` = `{ transcript: Vec<Turn>, model: Box<dyn rig::completion::CompletionModel>,
telemetry: Telemetry }` (the `model` is the rig-backed completion handle built by
`agent/provider.rs` for the configured provider — §6).
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
  (int.md §9); the implicated FQ symbols are a harvest signal.
- **`seq`-ordered recency** — per-entry `seq` (above).
- **Import-graph neighborhood** — `module_aliases` + the per-symbol `Import` edges
  (`install_imports`, `src/imports.rs`) give callee/caller neighbors of in-window fns.
- **Transcript** — what's already been discussed this session.

The ranker is a scoring pass over `defined_symbols()` combining these signals; the
top-budget slice is pushed. **No maintained index** — recomputed each turn from live
state (no invalidation problem; §3.3 of the arch doc — the harvest is a pure cache).

### 5.4 Graceful-degradation ladder under token budget

When the assembled push exceeds the budget, degrade in this order (drop the cheapest-value
tail first):
```
current-module full-src (PINNED)                    — never dropped
  → + last-10-fns full-src
    → + last-6-modules preamble+exports
      → + last-6-modules exports only (drop preambles)
        → current-module full-src + names-in-message only   (floor)
```
The floor always includes the current module (the pin) so the agent is never blind to the
user's cursor context. The budget number is a runtime config knob (§6.4), not a constant.

---

## 6. LLM completion layer — `rig-core`'s `CompletionModel`, used directly (R3-amended — BINDING)

### 6.0 The decision (R3-amended, user 2026-06-21)

R3's **intent** — a provider-agnostic boundary so `agent_turn` survives a local-model /
alternate-provider backend untouched — stands and is binding. Its **mechanism changed by
user direction (2026-06-21; `sprints/SPRINT.md` §"Architecture review" R3-amended):**

- **The boundary is `rig-core`'s `CompletionModel` trait, consumed directly.** We do NOT
  define a project-owned `LlmBackend` trait, and there is **no `agent/anthropic.rs`
  hand-rolled provider impl**. rig's `CompletionModel` (verified path:
  **`rig::completion::CompletionModel`** — docs.rs/rig-core 0.39.0, the low-level
  completion interface every rig provider implements) **IS** the provider-agnostic boundary
  R3 required. `agent_turn` calls it directly (§3.2). The user chose this leaner
  no-adapter option over an owned wrapper trait.
- **rig is used as the provider / completion layer ONLY — explicitly NOT rig's `Agent`
  struct, RAG, or tool-orchestration framework.** rig ships a higher-level `rig::agent::Agent`
  with its own tool registry, RAG context injection, and turn loop. We do **not** use it:
  it would collide head-on with our own `agent_turn` loop (§3.2), our harvester (§5), our
  **pull-as-visible-commands** mechanism (§4), and the keystone principle that **the agent
  has no private tools — its entire capability surface IS the REPL command set** (§4.4).
  We consume rig at the `CompletionModel`/`CompletionRequest` seam and own everything above
  it. *A future reader must not reach for `rig::agent::Agent` — that is a deliberate
  exclusion, not an omission.*

The discriminator (Principle 8 — no interim implementations) is unchanged: *will the loop
survive a local-model / alternate-provider backend without touching `agent_turn`?* — and is
now satisfied **by rig itself**: rig's `CompletionModel` is already implemented across
Anthropic, Ollama, OpenAI, Groq, and ~20 other providers, so provider swap is a
construction-time choice (§6.4), not an `agent_turn` edit.

### 6.1 What `agent_turn` speaks

`agent_turn`'s loop (§3.2) holds a `Box<dyn rig::completion::CompletionModel>` (the
`model` field on `AgentState`, §3.4) and calls its completion method directly, passing a
rig `CompletionRequest` built by `agent/request.rs` from the agent's neutral turn
vocabulary (§3.3):

- **System primer** (§7) → the request's preamble / system content.
- **Harvested context** (§5) + **spec excerpts** `[R5]` (§7.2) → additional system/context
  content (provider-neutral text the harvester assembled).
- **Transcript** (§3.4) → rig `Message` history (user / assistant / tool-result turns).
- **Tool defs** = the read-only command allowlist (§4.2) → rig tool definitions.
- **User turn** → the current user message.

The single coupling point is `agent/request.rs` (§3.1): the translation between the agent's
neutral vocabulary and rig's `CompletionRequest` / `Message` / tool-call types. The agent's
own `Turn` / `ToolDef` / `ToolCallRequest` / `ToolCallResult` types remain provider-neutral
(unchanged from the prior design's vocabulary) so the harvester, primer, pull, and transcript
machinery never see a rig type; `request.rs` is the membrane.

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

`agent/provider.rs` (§3.1) builds the `CompletionModel` for the **runtime-configured**
provider. Selection is runtime config, not a compile choice:

- **Anthropic = the default provider.** Built from `rig::providers::anthropic` (verified
  module path), with the **model-id taken from runtime config** (not hardcoded — per the
  `claude-api`/`/anthropic` discipline, the concrete current model-id is a Phase-5 config
  value looked up against live Anthropic docs, never baked from memory). Requires an API key
  → contributes to opt-in-twice (§6.4).
- **Ollama = the local / offline escape hatch.** Built from `rig::providers::ollama`
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
# Cargo.toml (the cranelisp binary crate)
[dependencies.rig-core]
version = "…"                    # Phase-5 pin; 0.39.0 is current at design time
default-features = false         # drop rig's default derive/reqwest/rustls bundle; opt back in
                                 # ONLY what the Anthropic + Ollama providers + completion API need
                                 # (the exact minimal feature set is a Phase-5 lookup — see note)
features = [ /* minimal: the TLS/http transport the two providers require */ ]
optional = true

[features]
agent = ["dep:rig-core"]         # OFF by default — in NO default feature set
```

- **`rig-core` is `optional = true`, enabled ONLY by the `agent` Cargo feature**, which is
  in **no crate's `default`**, enabled by no dev-dependency. `cargo build` / `cargo nextest
  run` therefore **never compile rig** → the default build + ~9s suite stay agent-free
  (`repl-embedded-agent.md §7.2`; mirrors `design/arch/release-llvm-backend.md §5`). All of
  `src/agent/` is `#[cfg(feature="agent")]`. Agent tests run in a separate
  `#[cfg(feature="agent")]` lane (`tests/agent.rs`, per the `/qa` Step-3.1 plan).
- **`default-features = false`** — rig's default features (in 0.39.0: `derive`, `reqwest`,
  `rustls`) are dropped; we opt back in only the transport features the two providers need.
  **Verification note (corrects the SPRINT R3 wording):** in current `rig-core` (0.39.0),
  **providers are compiled into the core crate and are NOT individually feature-gated** —
  there is no `anthropic` or `ollama` Cargo feature to enable (they live under
  `rig::providers::{anthropic,ollama}` and are always present once `rig-core` is a dep).
  The SPRINT R3 phrasing "`+ only the anthropic + ollama providers`" should be read as
  *intent* (compile only what those two providers need, via `default-features = false` + a
  minimal opt-in), not as literal provider feature flags. **The exact minimal `features`
  list is a Phase-5 lookup against the pinned rig-core version's `Cargo.toml`** — do not
  hardcode it here. If a later rig version does gate providers, enable exactly the two.
- **Opt-in twice (U6) — unchanged:** compiled-in (the `agent` flag) AND a runtime provider
  configured *and reachable* (Anthropic key present, OR a reachable local Ollama endpoint).
  Absent any reachable provider the agent is **dormant** and `/ask` says so, naming the
  endpoint + that **source excerpts** are transmitted (the U6 first-use disclosure — §2.3;
  the Ollama-local path transmits to localhost, which the disclosure states accurately). The
  published binary MAY ship `--features agent`; it stays dormant until a provider is
  configured.

### 6.5 Coupling tradeoff (accepted)

`agent_turn` and `agent/request.rs` are now **coupled to rig's API surface** — rig's
`CompletionModel` method shape, its `CompletionRequest` / `Message` / streaming-chunk /
tool-call types. **Dropping rig later would touch the loop** (`agent_turn`) and the request
membrane (`request.rs`), not just one isolated impl file. This is the **accepted cost of the
leaner no-adapter choice** (user direction): we trade the prior design's owned `LlmBackend`
insulation layer — which would have localized any provider-library swap to one impl — for
not building and maintaining that adapter at all, and for getting ~20 providers (incl. local
Ollama) for free *today*. The blast radius of a hypothetical future rig replacement is
bounded to `agent_turn` + `request.rs` + `provider.rs` (all `#[cfg(feature="agent")]`,
int-private) — never a cross-crate edge, never a facade. Recorded per Principle 6
(complexity has a budget): the cost is real and named; the benefit (no adapter, multi-provider
+ local now) was judged worth it.

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
3. `model.completion` (rig `CompletionModel`, §6) → the model may pull `/info Num` or
   `/sig some-numeric-fn` (§4) — each
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
- **`agent_turn` against a stub `CompletionModel`** — because the boundary is rig's
  `CompletionModel` *trait* (§6), the loop is tested by implementing it with a stub that
  returns a canned response (no network): assert a tool-call response synthesizes the right
  command, runs it through `process_commands`, and feeds the result back; assert a
  write-command synthesis is refused (allowlist §4.2). (The stub impls the same rig trait the
  real providers do — no project-owned trait to mock.)
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

## Next skills

- `/repl` — settle the agent experience (frame, `/ask`, `--agent` row, reverse-query UX,
  U6 disclosure wording) against this mechanism.
- `/dev` (int, narrow) — implement against this design once `/qa`'s failing tests land
  (Phase 5). Source-touching steps serialize (broken worktree isolation).
- `/qa` — draft the failing tests (classifier routing, stub-`CompletionModel` loop, harvest
  ladder, reverse-query scan) per §11.
- `/arch` — only if the `rig-core` dep wants a workspace-dep declaration, or if a
  cross-crate seam surfaces during implementation (none anticipated).
