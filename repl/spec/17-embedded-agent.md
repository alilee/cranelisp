> [REPL specification index](index.md)

## 17. Embedded Agent Experience [S88]

This section is **additive and behaviorally feature-gated.** It specifies the user-visible experience of the optional embedded LLM agent — a development partner that lives inside the live REPL session ([design/arch/repl-embedded-agent.md](../../design/arch/repl-embedded-agent.md)). **None of §1–§16 changes.** When the agent feature is compiled out, or built-in but dormant (§17.4), the REPL is byte-identical to the deterministic REPL §1–§16 describes — every requirement below that references the agent is gated on it being **both compiled-in and runtime-enabled**.

The agent extends the self-documentation principle (§4) into a conversational partner, but it does **not** replace, alter, or contend with the deterministic surface. Three invariants hold unconditionally:

- **The deterministic REPL is untouched.** Any **single form** (a bare atom, a fully-qualified symbol, or a compound form) and any slash command routes exactly as §1–§16 specify, whether or not the agent is enabled (§17.1) — a single symbol is always introspected (§4), never sent to the agent. The agent is a new destination for **multi-form / unparseable prose** (a line that parses to ≥2 forms, or a genuine parse error, §17.1) — and for the explicit `/ask` door — nothing more.
- **Everything the agent does is a visible REPL line.** The agent has no private capability surface: its reads, its proposed writes, and its shell proposals all appear as ordinary REPL commands and ordinary REPL output (§17.2). The session remains a legible, replayable script (§15).
- **Deterministic output and model output are unmistakable.** The agent's *prose* is rendered in a distinct reserved visual frame (§17.2); the deterministic `:Type value` format and the `;`-comment drawer remain exclusively the deterministic REPL's (§1, §4).

### 17.1 Agent Dispatch — The Classifier From the User's POV [S88]

When the agent is enabled, the REPL classifies each completed line of input into one of the existing deterministic destinations or the agent, **without regressing any §4 self-documentation behavior.** The classifier is a routing decision made one step earlier than evaluation; it does not change what any deterministic destination does.

**Form count is the discriminator, not symbol resolution (user ruling 2026-07-12).** The classifier decides by **how many forms the line parses to**, never by whether the forms' symbols resolve. The naive rules that predated this — "anything the reader accepts routes deterministically" or "resolve every bare atom and route unknowns to the agent" — both misjudged real input: multi-word natural-language prose parses cleanly as a *run of atoms*, and any prose containing an apostrophe (`doesn't`) parses to a **compound** form because `'` is the quote reader-macro (`'t` → `(quote t)`), so a compound-means-code rule misroutes a whole English sentence to eval (E6). The corrected rule is purely structural:

- **Exactly one form → the deterministic REPL.** A line that parses to **exactly one form** — a single bare atom (`map`, `42`), a single **fully-qualified** symbol (`primitives/vec-len`), or a single compound form (`(+ 1 2)`, `(defn …)`) — is evaluated/introspected exactly as §1/§4 specify. This decision does **NOT** depend on whether the symbol is known: a single **FQ** symbol **introspects** (§4), it never routes to the agent (this is the E6-candidate-B fix); a single bare unknown symbol shows the §4.1.10 unbound display. [S108]
- **Anything else → the agent if active, otherwise eval-sequentially-and-abandon.** A line that parses to **more than one form**, or that does not parse at all (unparseable prose, a genuine parse error), routes to the **agent when the agent is active**. When no agent is active, the line is evaluated **form by form in order and abandons on the first error, surfacing it** (§5.1) — never swallowing it into a fake result (the E7 fix). [S108]

A line is routed as follows (the first matching rule wins):

| Input shape | Routes to | Behavior |
|---|---|---|
| Starts with `/` (slash command) | Deterministic REPL | Unchanged (§3). `/ask` is the one slash command that forces the agent — see below. |
| `/ask <text>` | **Agent (always)** | The explicit door. Routes `<text>` to the agent unconditionally, bypassing the classifier (see below). |
| Blank or comment-only | Deterministic REPL | Unchanged — silent re-prompt (§2.3). |
| `parse(line)` → unclosed `(` or `[` (brackets not balanced) | Continuation | Unchanged — continuation prompt (§2.2). |
| `parse(line)` → **exactly one form** (a single bare atom, a single fully-qualified symbol, or a single compound `(…)`/`[…]`) | Deterministic REPL | Evaluated/introspected exactly as today (§1, §4). A single FQ symbol introspects — it does **not** route to the agent, regardless of whether it resolves. |
| **Anything else** — `parse(line)` → **more than one form**, OR a **genuine parse error** / unparseable prose | **Agent** if active; otherwise **eval sequentially, abandon on first error** | Multi-word prose (`why doesn't that typecheck?` — the `'` splits `doesn't` into `doesn` + `(quote t)`, ≥2 forms) reaches the agent. With no agent, `foo bar` evaluates `foo`, hits the undefined-variable error, and surfaces it (never a silent `:Int 0`). |

**Symbol resolution is NOT consulted.** The classifier's single-form → REPL decision is independent of `symbol_is_known`: a single form always routes deterministically, whether its symbols resolve or not. §4 self-documentation is therefore preserved unchanged for every single bare/FQ symbol — a bare known `map`, `+`, `42`, or `primitives/vec-len` is still **described** (§4), and a single bare unknown symbol shows the §4.1.10 unbound display — while multi-token prose (≥2 forms) reaches the agent. [S108]

**The reader is unchanged.** The `'`-in-contraction split (`doesn't` → `doesn` `(quote t)`) is language-normative and stays — the fix is entirely in the classifier rule, which now routes the resulting ≥2-form line to the agent (or sequential-eval) rather than treating "contains a compound form" as "is code." No reader change is made. [S108]

**The explicit `/ask` door always reaches the agent.** `/ask <text>` routes `<text>` to the agent **unconditionally**, bypassing the classifier. This is the canonical way to ask the agent about a *single known* symbol's usage in prose (e.g. `/ask how do I use map with a closure?` — where `map` alone would otherwise be described by §4), or to force any single-form line to the agent. [S88]

**Feature-off and dormant behavior:**

- The agent arm is **entirely feature-gated.** When the agent is **compiled out** or **dormant** (built-in but no runtime key, §17.4) the classifier's `Agent` arm does not exist:
  - A **single form** routes exactly as today — a bare unbound symbol → the §4.1.10 unbound display; a single known symbol → §4 introspection; a single compound form → evaluation (§1). Byte-identical to the deterministic REPL. [S108]
  - **More than one form** → **evaluate sequentially and abandon on the first error, surfacing it** (§5.1) — e.g. `foo bar` surfaces `undefined variable: foo` rather than swallowing it into a silent `:Int 0` (the E7 fix). A **genuine parse error** → today's parse-error display (§5.1). [S108]
  - `/ask <text>` MUST print a single, clear notice and re-prompt — `agent not built in` when compiled out, or `agent not enabled (no key configured)` when built-in but dormant — and MUST NOT crash, evaluate, or alter session state. [S88]

This fallback keeps the feature-off REPL deterministic: single forms and slash commands route exactly as §1–§16 specify; the only new live-agent behavior is the `Agent` arm for multi-form / unparseable input, and the only corrected deterministic behavior is that a multi-form line now surfaces its first per-form error instead of swallowing it (E7). [S108]

### 17.2 Agent Output Frame — Prose vs. Commands [S88]

When the agent takes a turn, its output has two kinds, rendered differently so the user can never confuse model output with deterministic output:

1. **Agent prose** — the model's natural-language explanation, reasoning, or proposal text. This MUST be rendered in a **distinct reserved visual frame** (§10.3 "Agent prose frame" role): a left gutter marker (`▌`) prefixing each prose line, with the gutter in bright magenta when colour is enabled. The frame MUST degrade gracefully: under `--no-color`, `NO_COLOR`, or a non-TTY (§10.1), the gutter marker MUST still be emitted as a plain-text prefix (so the prose remains visually distinguishable in piped output and the showcase), but with no SGR codes. The prose frame is the **only** place the agent's own words appear; it MUST NOT use the `:Type value` format or the `;`-comment drawer (those belong to the deterministic REPL). [S88]

2. **Agent-issued commands and their results** — when the agent reads (`/source foo`, `/info bar`, `/refs baz`) or proposes a write or shell command (§17.7), the command line and its output render in **NORMAL deterministic REPL style** (§1, §3, §10) — exactly as if the user had typed them. They ARE normal REPL output (`design/arch/repl-embedded-agent.md` §4.4). The command appears echoed as a REPL line (so the user watches the agent reach for the introspection vocabulary and learns it by observation), and its result uses the result's normal role (cyan type prefix, dim comment drawer, the `/list` layout, etc.). These MUST NOT be wrapped in the prose frame. [S88]

3. **Agent-emitted code — copy-clean, un-guttered (`▌`-free) [S107].** A pretty-printed ```lisp / ```cranelisp fenced form that the agent **shows as part of its answer** (§17.13.2 — the agent *displaying* code, distinct from an agent-issued `/source` pull) MUST render with **no per-line `▌` gutter on any code line**. This is the FIXME 0556 resolution: the gutter is emitted as literal line-leading text, so a multi-line selection over guttered code drags `▌ ` into the clipboard on every line and the example cannot be copied and re-run verbatim. Every code line a user would select MUST therefore be gutter-free. Concretely: the code block's bytes MUST be **exactly** what the deterministic pretty-printer produces for that form — byte-identical (colour-off) to `/sexp`/`/source` output for the same form (§3.11, §17.13.2) — with nothing prepended to any line. The surrounding **prose** lines keep their `▌` gutter (item 1), so the code block is set off from the conversation by the gutter boundary itself: the gutter's presence still marks "the agent is talking," and its **absence** marks "this is copyable code." The implementation MAY additionally caption the block with a single guttered marker line above it, but the code lines themselves MUST carry no gutter. The **"keep the gutter but expose an un-guttered copy elsewhere"** alternative is explicitly **rejected** (Phase-2 durability constraint) — this is a render-side structural split of code vs prose, not a second copy channel. [S107]

The contract: **the agent's prose is framed with the `▌` gutter; agent-emitted code and everything the agent does deterministically are un-guttered and byte-clean to copy.** This makes the deterministic-vs-model boundary unmistakable in every rendering mode while keeping every copyable line paste-ready. [S107]

A turn therefore reads on screen as an interleaving of framed prose, un-guttered pretty-printed code blocks, and unframed deterministic REPL lines — e.g. a prose sentence, then a gutter-free ```lisp block the agent is showing, then an echoed `/source` line and its normal output, then more prose, then a proposed `(defn …)` shown (not submitted) as a normal definition echo. The whole interleaving is part of the replayable transcript (§15). [S107]

**Guards this touches (for `/qa`).** Revising the code-line framing changes the bytes `render_agent_prose` emits for any fixture containing a ```lisp fence: the non-TTY byte-identical golden for agent output (the `--no-color` no-literal-escape transcript, §17.13.3) and the design-side §14.6 leaf-styling guard (`design/int/agent.md` §14.6) MUST be re-baselined to the un-guttered code shape when this lands. The change is agent-feature-gated (`#[cfg(feature = "agent")]`); the default REPL render path is untouched. [S107]

#### 17.2.1 The Probe Channel — The Agent's Self-Checks Are Private Reasoning, Not the User Session [S109]

§17.2 item 2 renders an agent-issued read as a normal echoed REPL line, on the premise that the
user learns the introspection vocabulary by watching the agent reach for it. In practice a
build-a-function turn issues **many** self-directed probes — *does `fn` take multi-arity?* (§17.17;
0575), *do multi-arity `defn` clauses share inference?* (0576), *what is this symbol's type?* — and
echoing each `agent> /type …` command and its result **line after line** floods the user's session
with the agent's private search, burying the one thing the user asked for (the finished function).
The observed session (the S109 agent-context observation, FIXME 0577, closed S113) scrolled
dozens of such probes and then hit the step budget without ever delivering the definition. This section carves the agent's **probe
traffic** off the user session. [S109]

**The probe set.** A **probe** is a read/introspection **pull** the agent issues to **check**
something before it writes — the syntax/type/introspection tools it uses to verify the language or
its own draft: `/type`, `/syntax`, `/sig`, `/info`, `/source`, `/doc`, `/exports`, `/list`,
`/search`, `/refs`, and the pre-flight validator's repair probes (§17.14.3). These are exactly the
pulls the §17.20.3a `question`/`error_class` fields instrument. (The precise tool membership is a
`/dev` detail; the default is the whole read/pull class above — a pull is the agent checking
itself, not answering the user. A tool that ever mutates session state is **not** a probe and stays
on its own consent path, §17.3.) [S109]

**Where probe traffic goes (MUST).** A probe MUST NOT scroll the user session as an
`agent> {command}` echo followed by its result. Probe traffic routes to the **private working
channel** — it is recorded in the §17.20 activity log (with the F1 `question` and F2 `error_class`
fields) and the §17.21 full-content trace, the tuning substrate — and is **not** rendered inline in
the transcript. This **revises §17.2 item 2 for the probe subclass**: the "watch every pull echo"
behaviour is replaced, because the flooding it caused defeated the very readability it was meant to
serve. The user learns the vocabulary from the agent's **conclusions**, not from watching it grind. [S109]

**What the user DOES see (MUST).** The user session carries the **outcome**, not the search for it:

1. the agent's **conclusions** — its framed prose (§17.2 item 1, the `▌` gutter), which MAY
   *summarise* what a probe established (*"`fn` is single-arity, so I used `defn`"*), and
2. the agent's **landed or proposed definitions** — the finished `(defn …)`/`(deftype …)` shown as
   a normal, un-guttered, copy-clean definition echo (§17.2 item 3) or submitted under the consent
   gate (§17.3.1, §17.14) — the thing the user actually asked for.

**Arch constraint — the probe channel is an E4 agent-gutter PRODUCER, not a bespoke renderer
(P2).** Where a probe's finding **does** surface to the user (a prose summary, per item 1 above), it
renders as **agent prose through the one styling seam** ([design/arch/repl-styling-seam.md](../../design/arch/repl-styling-seam.md)
— the `AgentGutter` producer, `10-terminal-styling.md` §10.3 R14), exactly like every other line of framed prose. There is **no
new probe-summary renderer**: a probe summary is prose, styled by the single formatter, degrading
`--no-color`/non-TTY byte-clean like all agent prose (§17.13.3). The private working channel itself
is not a screen surface at all — it is the log/trace sinks (§17.20/§17.21), which are already silent
(§17.20.1). [S109]

This is agent-feature-gated; feature-off there is no agent and no probe traffic. The change is a
render/experience change only — the agent still auto-runs its reads (§17.3 Reads row is unchanged:
reads need no consent); it just stops **echoing** its self-checks into the user's view. [S109]

### 17.3 Consent Model [S88]

The agent's actions are gated by **what they touch**, not by which "mode" the user selected. The S88 MVP is **read-only Advise**: it reads and shows, and it MAY *propose* code (shown, never submitted), but it performs no writes. The fuller consent model (Build and Document writes) is specified here as the **target** for the agentic-Phase-2 work (S89); the S88 MVP implements only the read-only row. **S89 realizes the Build and Document write rows** — the Build confirm-gate UX is §17.14, the Document consultative-edit UX is §17.15; both extend (never relax) the "auto-approve reads only" floor.

| Action class | Consent | S88 MVP | Notes |
|---|---|---|---|
| **Reads** (`/source`, `/info`, `/doc`, `/refs`, `/exports`, spec lookups, …) | **Auto-run-and-show** — no confirmation | **Yes** | The default is "auto-approve reads only." Reads are side-effect-free introspection; they run and their output appears as normal REPL lines (§17.2). |
| **Build writes** (submit a `defn`/`deftype` into the session) | **Confirm-and-show** — the exact line is shown and the user approves before it is submitted | **No (S89)** | In the MVP the agent **proposes** code: the `(defn …)` is *shown* as a normal definition echo but **not submitted** (§17.3.1). The confirm-each-submission flow lands in Phase 2. |
| **Document writes** (set/replace a docstring or a module preamble, §17.5) | **Consultative** — the agent asks ("shall I record that as `solver`'s preamble?") before writing | **No (S89)** | The read of a preamble is an auto-run read (above); *writing* one is consultative and is Phase 2. |
| **Shell** (`/sh …`) | **Confirm-and-show** — the agent proposes the exact command; the user approves | **No (S89)** | The agent has no direct shell tool; shell is reachable only by proposing a `/sh` line the user must approve (§17.7). |

**The default is "auto-approve reads only."** No write of any kind — code, documentation, or shell — happens without an explicit user action in the turn. [S88]

#### 17.3.1 The MVP "proposed, not submitted" Read-Out [S88]

In the S88 read-only MVP, when the agent answers a request that warrants code, it MUST present the proposed code as a **normal definition echo** (the same rendering a user-typed `(defn …)` produces visually) inside the turn, and MUST make clear in its framed prose that the code is a **proposal the user can submit**, not something already in the session. The session symbol table MUST be unchanged by the proposal — typing the proposed name afterward MUST still report it as unbound (§4.1.10) until the user actually submits it. [S88]

This satisfies the Stage C acceptance shape: `/ask "how do I define a constrained function over Num?"` → a spec-grounded, session-aware answer with a proposed `(defn …)` **shown, not submitted.** [S88]

### 17.4 Opt-In-Twice and Dormancy [S88]

The agent requires **two** independent opt-ins to be live, and is **dormant** unless both hold (`design/arch/repl-embedded-agent.md` §7.3/§7.4):

1. **Compiled in** — the binary was built with the agent feature. A default build has no LLM client in it at all; `--agent` is a no-op (§0.6.1).
2. **Runtime-enabled with a key** — the session was started with the agent on (§0.6.1) AND a backend key/config is present.

Absent either, the agent is dormant: `/ask` reports the dormant case (§17.1) and prose falls back to the parse-error display. This is the user-facing expression of "off by default; the REPL works fully without it." A dormant or absent agent MUST never transmit anything anywhere. [S88]

### 17.5 `/doc <module>` and the Module-Preamble Edit UX [S88]

A **module preamble** (`spec/08-modules.md §8.16`) is module-level documentation — the leading `;;` comment block at the head of a module file, the module analogue of a `defn` docstring. The REPL surfaces it on the same introspection family as docstrings.

#### 17.5.1 Reading a Module Preamble — `/doc <module>` [S88]

`/doc` is overloaded by what its argument resolves to:

- `/doc <name>` — when the argument is a **definition** (function, type, trait, macro, …), reads that definition's **docstring** (the existing behavior, §3.1, §11.2.4). Unchanged.
- `/doc <module>` — when the argument resolves to a **module**, reads that module's **preamble** text (`spec/08-modules.md §8.16.4`). [S88]

The module-preamble read MUST:

- Print the preamble text. The text is presented as documentation prose, not as source comments — the stored form (§8.16.2) has the `;;` markers already stripped — so the user sees the documentation content directly, consistent with how `/doc <name>` shows a docstring's content (not its surrounding quotes). [S88]
- Indicate clearly when the module has **no preamble** — the module-level analogue of a definition with no docstring (§8.16.4). The no-preamble indication MUST be distinguishable from "module not found" (a resolution error per §3.5) and from an empty-but-present preamble. A module with no leading comment block is the common, valid case (§8.16.1) and MUST NOT be reported as an error. [S88]
- Resolve the module argument using the same logic as `/exports <module>` (§3.5) — submodule paths, root modules, stdlib modules; load-on-demand if not yet loaded; `Module '<name>' not found` if unresolvable. [S88]

Suggested shape (illustrative; the exact framing is at implementation discretion within these requirements):

```
user> /doc solver
; module solver
Sudoku solver: constraint propagation +
backtracking over a Vec-backed grid.

user> /doc util
; module util — no preamble
```

The `; module <name>` header and the no-preamble line are comment-drawer lines (`;`-prefixed, dim per §10.3), consistent with the self-documentation comment convention (§1.5). The preamble body is plain prose. [S88]

**Ambiguity note.** When a name could denote both a definition and a module (rare), `/doc` SHOULD prefer the definition reading and offer the module reading via the fully-qualified module path, OR clearly indicate which it resolved. The implementation MUST NOT silently pick one with no signal to the user. [S88]

#### 17.5.2 Module-Preamble Edit UX (read now; consultative edit in S89) [S88]

The preamble is **editable in-session** (`spec/08-modules.md §8.16.5`): setting or replacing a module's preamble rewrites the leading comment block in the module's backing file, and the change MUST round-trip byte-stably through source regeneration (§8.16.5; coordinated with the FIXME 0423 regen fix). The S88 work specs the **read** (§17.5.1) and the **shape** of the edit UX; the edit flow itself is the agent's **Document mode**, which is **consultative** and lands in S89 (§17.3).

The edit UX shape (normative on the experience when implemented in S89; specified now so the read and the edit are designed together):

- A preamble edit is a **Document write** — consultative (§17.3). The agent (or a user-facing edit command) MUST present the **exact new leading comment block** it proposes and ask for confirmation ("shall I record that as `solver`'s preamble?") before writing. [S88]
- On confirmation, the new preamble is rendered as the canonical leading `;;` comment block (§8.16.1) at the head of the module file; the rest of the file MUST remain byte-stable (§8.16.5). Setting a preamble on a module that had none inserts the block; clearing one removes it. [S88]
- An unmodified preamble MUST NOT be reflowed, re-wrapped, or re-marked on any regeneration (§8.16.5) — the user MUST be able to trust that source regeneration after an unrelated change leaves their hand-written preamble verbatim. [S88]
- The edit is shown as a normal REPL line (§17.2) and becomes part of the replayable transcript (§15). [S88]

Because the preamble is also the agent's primary durable memory (`design/arch/repl-embedded-agent.md` §3.1), improving a module's documentation and growing the agent's memory are the **same activity** — the user benefits from every preamble the agent helps write. [S88]

### 17.6 Reverse-Query Commands — `/refs` and `/tests-for` [S88]

These commands answer **reverse** questions (which sites reference X?) that the existing introspection family — all **forward** (name → sig/doc/source) — cannot. They are **LLM-free**, available in the **default build** (no agent feature required), and useful to humans directly. They exist because the agent needs them and "the agent's needs are also a human's" (`design/arch/repl-embedded-agent.md` §4.4 corollary) — the agent is a forcing function that grows the REPL's introspection vocabulary for everyone. [S88]

Both are an **on-demand scan over the in-memory bodies** of the live session — no maintained reverse index, no cache to invalidate in a mutating session. (The implementation strategy is `/int`-owned; the spec pins the user-visible result + format.) [S88]

#### 17.6.1 `/refs <sym>` [S88]

`/refs <sym>` lists the **definitions in scope whose body references `<sym>`** — the call/use sites of a symbol. [S88]

- The argument is required. `/refs` with no argument MUST print a usage hint: `Usage: /refs <symbol-name>`. [S88]
- The output lists the referencing definitions by their fully-qualified name, using the **same normative layout algorithm** as `/list` (§3.3 rules L0–L4) — names only — so `/refs` output is consistent with the rest of the introspection family and stays byte-identical to `/list` for the same name set. [S88]
- If no definition in scope references `<sym>`, print a clear no-results line (e.g. `; no references to <sym>`), distinguishable from an unknown-symbol error. [S88]
- If `<sym>` is itself an unbound name in the session, `/refs` SHOULD report `unbound symbol '<sym>'` (consistent with §4.1.10) rather than silently reporting no references — distinguishing a typo from a genuinely-unreferenced symbol. [S88]

```
user> /refs grid-get
; references to grid-get
solver/solve solver/propagate
user> /refs unused-helper
; no references to unused-helper
```

#### 17.6.2 `/tests-for <sym>` [S88]

`/tests-for <sym>` lists the **test functions whose body references `<sym>`** — "what tests exercise this?" A test function is one recognized by the test convention (the `test-` prefix and the test signature, §16.1). [S88]

- The argument is required. `/tests-for` with no argument MUST print a usage hint: `Usage: /tests-for <symbol-name>`. [S88]
- The output lists matching test functions by fully-qualified name, using the `/list` layout (§3.3 L0–L4), byte-identical for the same name set. [S88]
- If no test references `<sym>`, print a clear no-results line (e.g. `; no tests reference <sym>`), distinguishable from an unknown-symbol error. This is itself useful signal — an un-tested symbol. [S88]

```
user> /tests-for solve
; tests referencing solve
solver/test-solve-easy solver/test-solve-hard
```

Both commands MUST appear in `/help` (§3.2) and MUST NOT crash or alter session state on any input (§5.2). [S88]

### 17.7 Shell Proposals [S88]

The agent has **no direct shell tool.** When the agent would run a shell command, it MUST do so by **proposing a `/sh <cmd>` line** (§13) that the user approves — confirm-and-show (§17.3). The agent proposes the exact command (shown as a normal REPL line, §17.2); the user runs it. This is **S89** (a write-class action); the S88 read-only MVP issues no shell proposals. [S88]

### 17.8 Privacy and First-Use Disclosure [S88]

The agent's view is bounded by the introspection surface and the embedded spec — **not** the host filesystem (no raw file-read tool; §17.6's scans are over in-memory session structures, not files). When the agent is enabled and a turn would transmit data to the backend, the REPL MUST satisfy the **opt-in-twice** discipline (§17.4) and the **first-use disclosure** below.

#### 17.8.1 First-Use Disclosure — Normative Wording [S88]

The **first time** in a session that the agent would transmit anything to the configured backend, the REPL MUST present a one-time disclosure **before** the transmission, stating plainly **what is sent** and **to where**. The disclosure is normative in content (the exact phrasing is at implementation discretion, but it MUST convey all of the following):

- **What is sent** — the disclosure MUST state that the following leave the session and are sent to the backend:
  1. **The user's message** (the `/ask` text or the prose that routed to the agent).
  2. **Harvested source excerpts** — explicitly **source excerpts, not merely signatures.** The disclosure MUST use language that makes clear the *bodies* of code are transmitted, not only type signatures. Per the agent's context model (`design/arch/repl-embedded-agent.md` §4.3), the harvested context includes the **full source of the current module** and the **full source of recently-mentioned functions** (the last ~10), plus module preambles and export surfaces. The wording MUST NOT understate this as "signatures" or "metadata" — it MUST say source excerpts / code bodies. [S88]
- **To where** — the disclosure MUST name the **configured endpoint** (the backend the session is configured to use) so the user knows the destination of the transmitted data. [S88]

Illustrative wording (an implementation MAY reword, but MUST cover every element above):

```
▌ Heads up — the embedded agent is about to contact an external model.
▌ What is sent: your message, plus source excerpts harvested from your
▌ session — including the full source of the current module and of the
▌ functions you have recently referenced (their code bodies, not just
▌ their type signatures), and module documentation.
▌ To where: <configured-endpoint>.
▌ (The agent is dev-session only and never runs in --run or --link.
▌  To keep the agent off, restart without --agent, or start with --no-agent.)
```

The disclosure MUST appear in the agent prose frame (§17.2) so it is unmistakably the agent's own notice. It is shown **once per session** before the first transmission; subsequent turns do not repeat it. An implementation MAY additionally require an explicit per-session acknowledgement before the first transmission; if it does, declining MUST keep the agent dormant for the session with no transmission. [S88]

The disclosure's honesty about **source excerpts** is the user's only signal that their code bodies — not just abstract type information — are leaving the machine. Understating it would be a conformance failure, not a wording nicety. [S88]

### 17.9 Relationship to the Deterministic Spec [S88]

This section is the **complete** set of additive agent requirements on the REPL experience. The deterministic contract (§1–§16) is unchanged; the only deterministic-surface additions are:

- the `/ask`, `/refs`, `/tests-for` command rows and the `/doc <module>` overload (§3.1);
- the `--agent` / `--no-agent` flags (§0.6.1) and (S89) the `--yes` / `-y` flag (§0.6.2);
- the "Agent prose frame" style role and (S89) the "Agent-input prompt" style role (§10.3);
- (S90) the `/syntax` command row (§3.1, §17.17) and the `/search` command row (§3.1, §17.19, *design-pinned re-pin*) — both reusing existing §10.3 roles, **no new style role**.

The **S90** additions (§17.17–§17.21 — the fluency pillars) introduce **no new style role**. Two of the four are **non-agent, default-build** surfaces (the command rows above) and two stay *inside* the agent surface: `/syntax` (§17.17) is an LLM-free static-asset command that also serves as an agent pull-tool; the signature-grain harvest (§17.18) is ambient agent context with **no command and nothing extra in the REPL**; `/search` (§17.19) is a **non-agent-gated default-build session facility** (re-pinned 2026-06-23 — its background index is built by the nice workers, which run regardless of the `agent` feature; the agent merely reaches it through the ordinary pull) and is **design-pinned-now / implemented-later** (gated on the FIXME-0432 fix + the nice-worker `catch_unwind` floor per §11.3); and the silent agent log (§17.20) is an env-opt-in (`CRANELISP_AGENT_LOG`), feature-gated, off-by-default file sink that produces **nothing extra in the REPL**. Its **companion**, the persistent full-content trace (§17.21, `CRANELISP_AGENT_TRACE=<path>` — re-purposed from S89's ephemeral stderr trace, whose stderr sink is **removed**), is a sibling env-opt-in, feature-gated, off-by-default file sink with the **identical silent/graceful contract**; the two are joined by a shared `turn` key. The **byte-identical-feature-OFF** invariant therefore scopes to the agent-gated surfaces (the harvest, the log, and the trace all require the agent); `/syntax` and `/search` are present and functional in the default build. [S90 re-pin]

The **S89** additions (§17.12–§17.16) are all *inside* the agent surface — the agent-input prompt (§17.12) and markdown/fenced-Lisp rendering (§17.13) only ever affect agent-issued/agent-turn output, and the Build confirm-gate (§17.14), Document consultative edit (§17.15), and the `--yes` auto-accept (§17.14.5 / §17.15.2a) + autonomous-submit first-use notice (§17.16) only fire when the live agent proposes a write. `--yes` (§0.6.2) is, like `--agent`, a no-op on default builds and when no agent is active. None alters the deterministic REPL: feature-off or dormant, no agent line is issued, no agent prose is rendered, and no write gate exists, so §1–§16 stay byte-identical. [S89]

Of these, `/refs`, `/tests-for`, and `/doc <module>` are **LLM-free** and live in the default build; `/ask`, the agent frame, and the agent flags are **feature-gated** and inert (or accepted-but-no-op) when the agent is compiled out. The form-count dispatch classifier (§17.1) — which routes a **single form** to the deterministic REPL and **multi-form / unparseable prose** to the agent — is itself **entirely feature-gated**: feature-off, a single unbound bare symbol still lands on today's §4.1.10 unbound display, a genuine parse error on the §5 display, and a multi-form line evaluates sequentially and surfaces its first error (§5), so §1–§16 stay deterministic. [S88]

### 17.10 Enabling & Configuring the Agent [S88]

This subsection is **normative** on how a user turns the agent on and points it at a backend. It pins the as-built scheme: the agent is a **compile-time feature** plus **environment-based runtime configuration** — and it is **explicitly NOT configured via `Cranelisp.toml`** (see the rationale below).

#### 17.10.1 Enabling — the `agent` Cargo feature [S88]

The embedded agent is compiled **only** when the binary is built with the `agent` Cargo feature, which is **off by default**:

- A **default build** (`cargo build`, `cargo nextest run`) contains no LLM client at all — the entire `src/agent/` module is absent. `/ask` reports `agent not built in` (§17.1) and `--agent` is an accepted no-op (§0.6.1). This is the first of the two opt-ins (§17.4).
- An **agent build** (`cargo build --features agent`) compiles the agent in. Whether it is *live* in a given session still depends on the runtime configuration below — being compiled in is necessary but not sufficient (opt-in-twice, §17.4). [S88]

#### 17.10.2 Configuring — the environment, NOT `Cranelisp.toml` [S88]

The agent is configured **entirely through environment variables**, read once at session construction. The agent **MUST NOT** read `Cranelisp.toml` (the project config file) for provider, model, or key. [S88]

**Rationale (normative intent).** The provider, model-id, and API key are **per-developer secrets and preferences**, not version-controlled project configuration. `Cranelisp.toml` is checked into the project and shared across every developer and CI run; an API key there would be a leaked secret, and a hard-coded provider/model there would impose one developer's backend choice on the whole team. Keeping agent configuration in the environment keeps secrets out of source control and lets each developer (and each shell session) choose their own backend independently. The agent therefore **never** consults `Cranelisp.toml`. [S88]

The environment surface (matching the as-built `src/agent/provider.rs`):

| Variable | Meaning | Default |
|---|---|---|
| `CRANELISP_AGENT_PROVIDER` | Selects the backend: `anthropic`, `ollama`, or `stub`. | `anthropic` [S88] |
| `CRANELISP_AGENT_MODEL` | The model-id (provider-specific). **Required** for any live provider — a live provider with no model-id stays dormant. | — [S88] |
| `ANTHROPIC_API_KEY` *or* `CRANELISP_AGENT_KEY` | The Anthropic API key. Its **presence** (non-empty) is the reachability gate for the Anthropic provider; either variable supplies it. | — [S88] |
| `OLLAMA_API_BASE_URL` | The Ollama endpoint. Ollama needs **no key** — it is the local / offline escape hatch (the U6 privacy path, §17.8). | `http://localhost:11434` [S88] |
| `CRANELISP_AGENT_STUB_SCRIPT` | **Test-only.** Path to a scripted-response fixture for the deterministic `stub` provider. This selects a canned, offline test double — it is **not** an end-user configuration knob. | — [S88] |

#### 17.10.3 Dormancy — the reachability gate [S88]

With the feature compiled in (§17.10.1) but **no provider configured or reachable**, the agent is **dormant** (§17.4) — it never transmits anything (§17.8). This is the **second** opt-in: the agent is live only when it is *both* compiled in *and* backed by a configured, reachable provider. [S88]

When the agent is dormant for want of configuration, `/ask` MUST report what to set, naming the missing variables for the selected provider — for example:

- Anthropic (the default provider) with no key or no model-id → a notice to set `ANTHROPIC_API_KEY` (or `CRANELISP_AGENT_KEY`) **and** `CRANELISP_AGENT_MODEL`. [S88]
- Ollama with no model-id → a notice to set `CRANELISP_AGENT_MODEL` (no key is needed for Ollama). [S88]

The reachability gates are, per provider: **Anthropic** — a non-empty key *and* a non-empty model-id; **Ollama** — a non-empty model-id (the endpoint defaults to localhost, no key); **stub** — a loadable fixture from `CRANELISP_AGENT_STUB_SCRIPT`. Absent its gate, each provider yields a dormant agent rather than an error, and `/ask` renders the dormant notice (§17.1) naming what to set. [S88]

#### 17.10.4 Cross-reference — the first-use disclosure [S88]

Configuration determines **where** data goes, so it is bound to the privacy disclosure (§17.8). The **first** time a live agent would transmit in a session, the REPL presents the first-use disclosure (§17.8.1) naming the **configured endpoint** — i.e. the backend selected by `CRANELISP_AGENT_PROVIDER` and its endpoint. Because **Ollama is local** (`OLLAMA_API_BASE_URL` defaults to `http://localhost:11434`), a turn against an Ollama backend transmits to the local host and **nothing leaves the machine** — the offline escape hatch (§17.8). A turn against the Anthropic provider transmits source excerpts to the external Anthropic endpoint, which is exactly what the §17.8.1 disclosure exists to surface. [S88]

### 17.11 Debugging the agent context — `/context` [Tested+Neg tests/agent.rs::context_feature_off_prints_not_built_in, tests/agent.rs::agent_on_context_dumps_request_to_file_dormant] [S88]

`/context <path>` is a **debug command** for inspecting *what the agent would send the model* — not for invoking it. It writes the agent's **fully assembled next-turn request** — byte-for-byte the grounding, context, and turn structure that an `agent_turn` would transmit on the next turn — to the file at `<path>` as readable text, and **does not call the model**. Its purpose is to let a developer audit the agent's grounding, harvested context, and system primer **offline**, before (or without) ever spending a transmission. [S88]

**What it dumps.** The file contains the assembled request rendered as labelled sections, in **send-order** — the order in which the material is presented to the model: [S88]

```
=== BUDGET (approx) ===
=== SYSTEM PRIMER ===
=== HARVESTED CONTEXT ===
=== TOOLS (read-only) ===
=== TRANSCRIPT ===
=== CURRENT USER TURN ===
```

- `=== BUDGET (approx) ===` — the approximate token/size budget for the turn. [S88]
- `=== SYSTEM PRIMER ===` — the agent's system grounding (its role, the introspection vocabulary, the consent model). [S88]
- `=== HARVESTED CONTEXT ===` — the context the agent harvested from the live session (the in-memory introspection surface and embedded spec excerpts, §17.8) for this turn. [S88]
- `=== TOOLS (read-only) ===` — the tool surface offered to the model. In the S88 read-only MVP this is the read-only pull allowlist (§17.3); `/context` itself is **not** in it (see below). [S88]
- `=== TRANSCRIPT ===` — the conversation so far this session. [S88]
- `=== CURRENT USER TURN ===` — the pending user turn that would be sent next. [S88]

**Works dormant/offline — no model call, no key.** Because `/context` dumps the *assembled* request rather than transmitting it, it functions regardless of provider, reachability, or dormancy (§17.4, §17.10.3): it requires **no API key and contacts no backend**, and a **dormant** agent (built-in but unconfigured) MUST still produce the full dump. This is the entire point — the developer can inspect grounding, harvest, and primer **without** opting in to a transmission. A dormant agent dumping its context does **not** violate "a dormant or absent agent MUST never transmit anything" (§17.4): writing a local file is not a transmission. [S88]

**Human-only debug command — never an agent tool.** `/context` is invoked **only by the human** at the prompt. It is **NOT** in the agent's pull allowlist (§17.3) and the agent **cannot** issue it — `/context` writes a file, which is outside the agent's read-only capability surface (§17.2, §17.8). It does not appear in the `=== TOOLS (read-only) ===` section it dumps. [S88]

**Success and error reporting.** On success the REPL prints a confirmation line naming the path and the number of characters written — e.g. `wrote agent context to <path> (<N> chars)`. If `<path>` cannot be written (e.g. an unwritable directory), the REPL reports a graceful error rather than crashing or panicking. [S88]

**Feature-OFF behavior.** When the binary is built **without** the `agent` feature (§17.10.1), `/context` prints `agent not built in` — identical to `/ask`'s feature-off behavior (§17.1) — and writes nothing. [S88]

### 17.12 Agent-Input Prompt — Who Typed What [S89]

§17.2 establishes that an agent turn interleaves **framed prose** (`▌` gutter) with **unframed deterministic REPL lines** (the agent's reads, proposals, and — in S89 — its writes, all rendered as if the user had typed them). That unframed-equals-keystroke contract created an honesty gap surfaced in live S88 use: when the agent **issues a line itself** — a pulled read command (`/source foo`), or (S89) a submitted form — the line renders with **no prompt prefix at all**, so a reader scanning the replayable transcript (§15) cannot tell whether the agent typed it or the user did. This subsection closes that gap with a distinct **agent-input prompt**. [S89]

**The agent-input prompt glyph.** Every line the agent "types" — i.e. a line the *agent originated* and the REPL is echoing as an issued command — MUST be prefixed with a distinct **agent-input prompt**: the token `agent>` (the agent analogue of the human `user>` prompt, §2.1). The prompt:

- is **distinct from the human prompt** (`user>` / the timing+module prompt of §2.1) — the reader can tell agent-issued input from user-typed input at a glance; [S89]
- is **distinct from the `▌` prose gutter** (§17.2) — a pulled command is the agent *acting*, not the agent *speaking*; the `agent>` prompt marks issued input, the `▌` gutter marks prose. The two never share a glyph. [S89]
- is styled per the new §10.3 "Agent-input prompt" role (dim, with the `agent` token in bright magenta to tie it visually to the agent's magenta prose frame), and **degrades under `--no-color`, `NO_COLOR`, or a non-TTY** (§10.1) to the **plain-text token `agent>`** with no SGR codes — so piped output and the showcase still read honestly. [S89]

**Where the agent-input prompt appears (the two agent-echo sites).** The `agent>` prompt prefixes exactly the lines the agent issues as input:

1. **Pulled read commands** (§17.2) — when the agent reaches for `/source`, `/info`, `/refs`, `/sig`, … the echoed command line carries `agent>`; its **result** below it renders in normal deterministic style (cyan type prefix, dim drawer, the `/list` layout — §1, §3) exactly as today, *unprefixed and unframed*. Only the issued command line gets the `agent>` prompt; the result is the REPL's own output. [S89]
2. **Build-submit echoes** (§17.14) — when the agent submits a form past the confirm-gate, the submitted definition line is echoed with `agent>` so the transcript shows the agent issued it (then the normal `:Type name` definition result follows, unprefixed). [S89]

Illustratively (colour elided):

```
user> /ask how does grid-get work?
▌ Let me look at its definition.
agent> /source grid-get
:(Fn [primitives/Vec primitives/Int] primitives/Int) solver/grid-get  ; defn - Read a cell
▌ It indexes the flat grid vector by row-major offset. ...
```

The `agent>` line is agent-issued input; the `:(Fn …)` line beneath it is the deterministic REPL's normal `/source` output; the `▌` lines are the agent's prose. Three visually-distinct origins, each honestly marked. [S89]

**Feature-off / dormant.** The agent-input prompt exists only when the agent is live (it only ever prefixes agent-issued lines, which only exist when the agent takes a turn). Feature-off or dormant, no agent line is ever issued, so the prompt never appears — the deterministic REPL is byte-identical (§17.1, §17.9). [S89]

### 17.13 Markdown Rendering Within the Agent-Prose Frame [S89]

The agent returns **markdown** prose. S88 rendered it raw inside the `▌` frame (§17.2) — headings, lists, emphasis, and fenced code all passed through verbatim, and (the live-use defect, §17.13.3) raw ANSI escape codes could leak as literal text. S89 specifies that the model's markdown is **formatted for the terminal inside the §17.2 prose frame**, that fenced Lisp renders through the deterministic pretty-printer, and — normatively — that **no raw ANSI escape code ever appears as literal text** in any rendering mode. [S89]

#### 17.13.1 Markdown Formatting (inside the `▌` frame) [S89]

The agent's prose MUST be formatted as terminal text — not emitted as raw markdown source — **within** the §17.2 agent-prose frame (every formatted prose line still carries the `▌` gutter; the markdown formatting lives *inside* the frame, not beside it). The formatter MUST handle the common markdown the model actually produces:

- **Headings** (`#`, `##`, …) — rendered as a visually-distinct heading line (e.g. bold), not as a literal `## ` prefix. [S89]
- **Bullet and numbered lists** — rendered as aligned list items with a bullet/number marker, not as literal `- `/`1. ` source. [S89]
- **Emphasis** — `**bold**` and `*emphasis*` rendered with the corresponding terminal weight/style (bold, italic), with the surrounding `*`/`**` markers consumed (not shown literally). [S89]
- **Inline code** — `` `code` `` rendered as a distinguishable inline span (e.g. via the existing palette), with the backticks consumed. [S89]

This is a **bounded** terminal formatter for the markdown the model emits — not a full CommonMark engine; constructs it does not handle MUST degrade to readable plain text (the marker shown or stripped), never to a crash or to garbled output. The formatting uses the **existing §10.3 palette roles** (bold, dim, etc.) — it introduces **no new colour and no new style role** beyond the agent-prose frame role already in §10.3. [S89]

**Degrades cleanly under `--no-color`.** Under `--no-color`, `NO_COLOR`, or a non-TTY (§10.1), the markdown formatting MUST degrade to **plain text with the `▌` gutter still present** (per §17.2's frame-degradation rule) and **no SGR codes** — headings/lists read as plain text lines, emphasis markers are stripped to their words, inline code shows its text. The prose stays legible and frame-marked in piped output and the showcase, exactly as the bare prose did in S88. [S89]

#### 17.13.2 Fenced Lisp Renders via the Pretty-Printer [S89]

When the model's prose contains a fenced code block whose info-string is `lisp` (or `cranelisp`) — `` ```lisp … ``` `` — the block's body MUST be rendered through the **deterministic S-expression pretty-printer** (the same printer `/source` and `/sexp` use, §3.1, §3.11, §10) — syntax-highlighted, indented, and (for `let`/`match`) pair-aligned per §3.11 — **not** emitted as a raw fence. It is part of the agent's *answer* — the agent *showing* code — distinct from an agent-issued `/source` pull, which is the agent *running a command* and renders unframed with the `agent>` prompt (§17.12). A fence with a **non-Lisp** info-string (e.g. `` ```sh ``) is left as a literal block (markdown-formatted, not pretty-printed). [S89]

**Copy-clean, un-guttered [S107].** Per §17.2 item 3 (FIXME 0556), the pretty-printed code block MUST render with **no per-line `▌` gutter** — the surrounding prose stays guttered, but every code line the user might select-and-copy is gutter-free, and the block's bytes are **byte-identical (colour-off) to `pretty_print_str` / `/sexp` output for the same form**. (Before S107 this block was routed through the prose frame and carried the gutter on every line, polluting copy-paste — the defect 0556 fixes.) The pretty-printed fence MUST honour the colour mode: syntax-highlighted when colour is enabled, plain indented text under `--no-color`/non-TTY — degrading via the **same** global colour gate as every other styled output (§10.1, §10.7), never a separate one. [S89] [S107]

#### 17.13.3 No Raw ANSI Escape Codes — Normative (the S88 defect) [S89]

In live S88 use, agent output sometimes emitted ANSI colour codes as **literal text** (e.g. a visible `\033[36m…` in the rendered prose or a fenced block) instead of rendering as colour. This is a **conformance failure**, not a cosmetic nicety. Normatively:

- In **every** rendering mode, an agent turn's output (framed prose, formatted markdown, and pretty-printed fenced Lisp) MUST contain **no ANSI escape code as literal visible text**. Colour codes either take effect as styling (colour enabled) or are absent entirely (colour disabled) — they are never shown as characters. [S89]
- Under `--no-color`, `NO_COLOR`, or a non-TTY (§10.1), agent output MUST be **completely free of SGR/escape sequences** — the `--no-color` transcript is clean plain text (gutter + plain prose + plain-indented Lisp). [S89]
- This is the **user-visible acceptance** for the defect's fix: an `/ask` answer containing prose **plus** a `` ```lisp `` block renders with formatted prose and a pretty-printed, correctly-coloured form, with **no literal escape codes anywhere**, and stays clean under `--no-color`. [S89]

(The root cause is an int-internal render-path wiring issue — style-once-at-the-leaf, the global colour gate honoured uniformly — not a missing colour-mode parameter; that is `/int`/`/dev`-owned mechanism. This spec pins only the user-visible contract: no literal escapes, clean `--no-color`. A `/qa` narrow failing-not-ignored repro is owed before closure, per `CLAUDE.md §Testing`.) [S89]

### 17.14 Build Mode — The Confirm-Gated Submit UX [S89]

S88's read-only MVP **proposed** code — shown, never submitted (§17.3.1). S89 promotes the agent to **propose-then-submit-on-confirm**: the agent MAY submit a form into the live session, but **only past a confirm-gate the user controls**. This realizes the §17.3 "Build writes → confirm-and-show" row, which S88 specified as the target and left unimplemented. The read-only-by-default floor (§17.3) is **extended, not replaced**: a write is reachable **only** past the confirm-gate; reads stay auto-run-and-show; non-read, non-submit tools (e.g. `/sh`, §17.7) stay refused. [S89]

#### 17.14.1 The Confirm-Gate Experience [S89]

When the agent wants to submit a form, the user sees, in order:

1. **The proposed form, shown pretty-printed.** The exact `(defn …)`/`(deftype …)` the agent proposes is rendered as a normal definition echo (the same visual a user-typed definition produces, §1.3) — pretty-printed (§17.13.2) so the user reads exactly what would be submitted. It is echoed with the **`agent>` agent-input prompt** (§17.12) so it reads honestly as agent-issued. [S89]
2. **A confirm prompt.** The REPL MUST then present a clear, single-line confirm prompt that names the action as a **code submission** and offers an explicit accept/decline choice — e.g. `submit this definition? [y/N]`. The prompt MUST make the **default-decline** posture visible (the capitalized `N`): pressing Enter, or any non-affirmative response, declines. The exact wording is at implementation discretion but MUST convey (a) that a **definition is being submitted into the session**, and (b) an explicit yes/no with **decline as the safe default**. [S89]

The consent interaction is a **synchronous prompt at the REPL prompt** — the user types `y`/`n` (or equivalent) on the next line, the same way they answer any prompt; it is not a background dialog or a mode switch. [S89]

#### 17.14.2 Accept and Decline [S89]

- **On accept** (`y`): the form is submitted — it goes through the *same* path a user keystroke uses, so it is type-checked, defined, and persisted exactly as if the user had typed it, and its normal `:Type name` definition result (§1.3) renders **unframed** below the echo (it is now real session state). Typing the new name afterward reports it as bound (§4). The submission is part of the replayable transcript (§15). [S89]
- **On decline** (Enter / `n` / anything non-affirmative): **nothing is written to the session.** The proposal is discarded; the session symbol table is **unchanged** — typing the proposed name afterward MUST still report it unbound (§4.1.10), structurally identical to the S88 "proposed, not submitted" floor (§17.3.1). The agent is told the user declined (so it does not assume the code is live) and the turn continues. A decline MUST never partially apply, crash, or leave the session in an inconsistent state. [S89]

#### 17.14.3 The Pre-Flight Validator — The User Never Sees an Agent Compile Error [S89]

Before a proposed form reaches the confirm-gate (§17.14.1), the REPL **silently validates** it (a behind-the-scenes type-check on a throwaway staging copy) and, on **any** failure — a parse error or a type error, no distinction — **silently repairs** it (asks the model to fix it and re-validates), up to a bounded number of attempts. The user-visible contract (the U5 ratified decision, `design/arch/repl-embedded-agent.md §6.4`):

- **The user NEVER sees a raw agent compiler error.** A broken intermediate the agent generated — the broken form *and* the compiler diagnostic it produced — MUST NOT appear in the transcript at all. Only a form that **at least parses and type-checks** ever reaches the confirm-gate echo. The whole stage→check→discard→repair exchange is invisible. [S89]
- **No stack of compiler diagnostics, ever.** The user is never shown a sequence of failed attempts, error messages, or internal retry chatter. The validator's work is silent by construction. [S89]

#### 17.14.4 The Validator Give-Up Wording [S89]

If silent-repair exhausts its attempt cap without producing a form that validates, the agent **gives up gracefully** — it does **not** submit broken code, and it does **not** dump a compiler error. Instead it renders, in its prose frame (§17.2), a **single honest, polite notice** that it could not produce valid code here — e.g. *"I wasn't able to produce code that compiles cleanly for this — here's my best attempt, which you may need to adjust."* Normatively, the give-up:

- MUST be a **graceful, plain-language notice** in the agent prose frame — never a raw compiler diagnostic, a stack trace, or a stack of failed attempts. [S89]
- MUST NOT submit anything to the session (it degrades to the §17.3.1 read-only "proposed, not submitted" floor). [S89]
- MAY show its **last attempt clearly marked as an un-submitted proposal** the user can copy and hand-fix — pretty-printed (§17.13.2), with no confirm-gate (there is nothing valid to submit), and with prose that makes unmistakable it is **not** in the session. [S89]

The exact phrasing is at implementation discretion but MUST convey: it could not produce valid code, nothing was submitted, and (if shown) the remaining code is an unverified suggestion. The user's experience of an agent that cannot get the code right is a **calm apology and a suggestion**, never a wall of diagnostics. [S89]

#### 17.14.5 Autonomous Submit Under `--yes` — Auto-Accept the Confirm-Gate [S89]

When the session is started with `--yes` (§0.6.2), the Build confirm-gate (§17.14.1) **auto-accepts**: the agent submits its proposed form **without prompting** for `[y/N]`. Normatively:

- **The proposed form is still shown.** The pretty-printed `agent>`-prefixed definition echo (§17.14.1 step 1) MUST still render before submission — the user always sees exactly what the agent submitted. `--yes` removes the **question**, not the **visibility**. [S89]
- **The confirm prompt is suppressed; submission proceeds as on accept.** In place of the `submit this definition? [y/N]` prompt (§17.14.1 step 2), the form goes straight through the **accept path** (§17.14.2) — type-checked, defined, persisted, with its normal `:Type name` result rendered unframed below the echo, and added to the replayable transcript (§15). The behaviour is exactly as if the user had answered `y`. [S89]
- **The decline path is unreachable while `--yes` is on, by design.** There is no opportunity to decline an individual Build submit under `--yes`; that is the flag's purpose. (To regain per-action control, restart without `--yes`.) [S89]

#### 17.14.6 The Validation Floor Holds Under `--yes` — Never Submit Raw [S89]

`--yes` auto-answers **consent, not validation** (`/arch` ruling, `design/arch/repl-embedded-agent.md §7.4`). The pre-flight validator (§17.14.3) and its give-up path (§17.14.4) are **invariant under the flag** — `--yes` changes nothing about them:

- Every form the agent submits under `--yes` is **still silently validated and silently repaired** exactly as with `--yes` off (§17.14.3). Only a form that at least parses and type-checks is ever auto-submitted; a deliberately-broken generation is **silently repaired, never submitted raw.** The user never sees broken code reach the session, with or without `--yes`. [S89]
- If silent-repair exhausts its attempt cap, the agent **gives up gracefully** under `--yes` exactly as in §17.14.4 — it does **not** auto-submit broken code, and it does **not** dump a compiler diagnostic. `--yes` cannot force an un-validating form into the session; the give-up degrades to the read-only "proposed, not submitted" floor (§17.3.1), shown as an un-submitted suggestion. [S89]

`--yes` removes the prompt, not the correctness floor. An implementation that treated `--yes` as "skip the dry-run" would be a conformance defect (the `/arch` validation-floor invariant). [S89]

### 17.15 Document Mode — The Consultative Preamble/Docstring Edit UX [S89]

S88 specified **reading** a module preamble (`/doc <module>`, §17.5.1) and the **shape** of the edit UX, deferring the edit itself to S89 (§17.5.2). S89 specifies the **edit experience**: the agent records its understanding durably — as a module preamble or a definition docstring — through a **consultative** gate that is deliberately distinct, in wording and posture, from the Build code-submit confirm (§17.14). This realizes the §17.3 "Document writes → consultative" row. [S89]

#### 17.15.1 The Consultative Gate — Distinct From the Build Confirm [S89]

A Document write (set/replace a module preamble or a definition docstring) is **consultative**, not a terse code-submit confirm. The two write classes are distinguished **by the question the user is asked**, so the user always knows whether the agent is changing **code** or changing **documentation**:

- **Build (code) — confirm posture** (§17.14): `submit this definition? [y/N]` — a terse, default-decline confirm for a code change. [S89]
- **Document (documentation) — consultative posture**: the agent **proposes recording its understanding** and asks a consultative question naming the target — e.g. *"record this as `solver`'s preamble?"* (for a module preamble) or *"record this as `grid-get`'s docstring?"* (for a definition docstring). The wording is a **consultation** ("shall I record this as …?"), distinct from the Build "submit this definition?" — the user is being asked to endorse a piece of *documentation*, not to approve *code*. [S89]

Before asking, the agent MUST **show exactly what it proposes to record** — the proposed preamble/docstring text, rendered as it would be stored (for a module preamble, the canonical leading `;;` comment block, §17.5.2; for a docstring, the docstring text) — so the user endorses the exact wording. The proposal echo carries the `agent>` agent-input prompt (§17.12). [S89]

#### 17.15.2 Accept and Decline [S89]

- **On accept**: the preamble/docstring is written durably into the code — for a module preamble, as the canonical leading `;;` block at the head of the module's backing file (§17.5.2); for a docstring, into the definition. The edit is shown as a normal REPL line (§17.2) and becomes part of the replayable transcript (§15). The **rest of the file MUST remain byte-stable** (§8.16.5) — an unrelated regeneration MUST leave the hand-written text verbatim (the §17.5.2 no-reflow guarantee). [S89]
- **On decline**: nothing is written; the existing preamble/docstring (or its absence) is unchanged; the agent is told the user declined and the turn continues. [S89]

#### 17.15.2a Autonomous Edit Under `--yes` — Auto-Accept the Consultative Gate [S89]

`--yes` (§0.6.2) is **blanket** — it auto-accepts the Document consultative gate (§17.15.1) as well as the Build confirm-gate (§17.14.5). When `--yes` is active:

- **The proposed text is still shown.** The agent MUST still render exactly what it proposes to record — the preamble `;;` block or the docstring, as it would be stored, carrying the `agent>` prompt (§17.15.1) — before writing. The user always sees the documentation the agent recorded. [S89]
- **The consultative question is suppressed; the edit proceeds as on accept.** In place of the *"record this as `solver`'s preamble?"* consultation (§17.15.1), the edit goes straight through the **accept path** (§17.15.2) — written durably into the code with the rest of the file byte-stable (§8.16.5), shown as a normal REPL line, added to the transcript. The behaviour is exactly as if the user had endorsed it. [S89]
- **The decline path is unreachable while `--yes` is on, by design.** No per-edit decline opportunity exists under `--yes`. (Restart without `--yes` to regain per-edit consultation.) [S89]

The byte-stable round-trip (§8.16.5) and the durable-memory promise (§17.15.3) hold unchanged under `--yes` — the flag removes the question, not the correctness or persistence guarantees.

#### 17.15.3 The Durable-Memory Promise — "Next Session It Remembers" [S89]

A Document edit is **durable**: it round-trips byte-stably through source regeneration (§17.5.2, §8.16.5) — the recorded text persists in the code exactly as endorsed. Because the agent's harvested context reads module preambles and docstrings back from the live session (§17.8, the agent's durable memory is the code, `design/arch/repl-embedded-agent.md §3.1`), a preamble the agent helps write **this** session is read back by the agent **next** session. The experience-level promise the user can rely on: **what the agent records, it remembers** — and because the record lives in the code as ordinary, readable documentation, improving a module's docs and growing the agent's memory are the **same activity** (§17.5.2). The user never maintains a separate agent memory; the documentation *is* the memory, and it is durable across sessions. [S89]

#### 17.15.4 Honest Failure — No False "Recorded" [Tested+Neg tests/agent.rs::set_doc_missing_target_e2e_refused_no_false_recorded_neg, tests/agent.rs::set_doc_non_function_target_e2e_refused_not_recorded_neg (agent-feature lane: cargo nextest run --features agent --test agent)]

The durable-memory promise (§17.15.3) only holds for a target the edit **can** record durably. When the proposed docstring target is **not durably recordable**, the Document edit MUST **fail honestly**: the agent surfaces a clear error naming why, MUST NOT claim it "recorded" anything, and MUST leave the live state unchanged (no ephemeral in-session write that vanishes on restart). The honesty contract has two faces, both of which are refusals — not silent no-ops:

- **Missing target ⇒ "no such definition".** A docstring edit names a symbol that has **no local definition** in the current module — including a never-defined name, a qualified `mod/sym`, or a name that is only a re-exported **import** (not a local `Def`) — is refused with a not-found error (e.g. `no such definition: <symbol>`). The agent does not guess and does not fabricate a target. [S94]
- **Non-recordable kind ⇒ refused, naming "function".** A docstring edit names a symbol that **does** resolve locally but is **not a user-defined function** (a primitive extern, an ADT constructor, a type — any kind whose docstring would display in-session but **not survive source regeneration**, §17.5.2) is refused with a message making clear that only a function's docstring can be recorded. Surfacing an in-session-only docstring that silently disappears on the next session would break the §17.15.3 promise, so it is refused rather than half-applied. [S94]

In both cases the failure reaches the user as the agent's own honest report (the U5 "never a raw compiler error" posture, §16.4); the consultative gate's success line (*"recorded …"*) MUST NOT appear, and a subsequent session's `/doc <symbol>` MUST show no spuriously-recorded docstring. This is the negative face of the durable-memory promise: the agent records what it **can** durably remember, and is honest about what it cannot. [S94]

### 17.16 Autonomous-Submit First-Use Notice — `--yes` Escalation Disclosure [S89]

`--yes` (§0.6.2) is an **autonomy escalation**: the agent now writes — submits Build forms (§17.14) and records Document edits (§17.15) — **without asking** the per-action `[y/N]`/consultative question. Parallel in spirit to the S88 transmit first-use disclosure (§17.8.1), this escalation warrants its own **one-time** notice (per the `/arch` ruling, `design/arch/repl-embedded-agent.md §7.4 (b)`; wording owned here).

The **first time** in a session that `--yes` is active and the agent **would write** (the first Build submit or Document edit), the REPL MUST present a one-time disclosure **before** the write, in the agent prose frame (§17.2) so it is unmistakably the agent's own notice. It is shown **once per session** — subsequent autonomous writes do not repeat it. The disclosure is **normative in content** (exact phrasing at implementation discretion, but it MUST convey all of the following):

- It MUST state that, because the session was started with `--yes`, the agent will **submit definitions and record documentation edits without asking** — the per-action confirm/consultative prompt is being **auto-accepted** on the user's behalf. [S89]
- It MUST state that the user **still sees every form and every edit** the agent makes (they are shown as agent-issued lines, §17.12) — autonomy removes the prompt, **not** the visibility. [S89]
- It MUST state that the **pre-flight validator still gates correctness** (§17.14.3): only code that compiles is ever submitted — `--yes` skips the question, **not** the correctness check; the agent never submits broken code. [S89]
- It SHOULD state how to regain per-action control: **restart without `--yes`.** [S89]

Illustrative wording (an implementation MAY reword, but MUST cover every element above):

```
▌ Autonomous mode (--yes) — the agent will submit definitions and record
▌ documentation edits WITHOUT asking you each time. You still see every
▌ form and edit it makes (shown as agent> lines). Only code that compiles
▌ is ever submitted — the pre-flight check still runs; --yes skips the
▌ prompt, not the correctness check.
▌ (To approve each write yourself, restart without --yes.)
```

An implementation MAY additionally require an explicit per-session acknowledgement before the first autonomous write; if it does, declining MUST fall back to the per-action confirm/consultative gates (§17.14.1 / §17.15.1) for the rest of the session (i.e. behave as if `--yes` were off). This disclosure is **distinct from** the §17.8.1 transmit disclosure — that one names *what leaves the machine*; this one names *that the agent acts without asking*. Both may fire in the same session (transmit first, then autonomous-write). [S89]
