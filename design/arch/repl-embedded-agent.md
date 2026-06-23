# Embedding an LLM Agent in the REPL — Exploratory Architectural Design

**Status:** RATIFIED (U1–U6, user 2026-06-21 — §10) + IN DELIVERY. **Phase 1 (Advisor MVP, rungs 0–4) SHIPPED + live-validated S88** (`sprints/archive/sprint-88.md`). **Phase 2 (Build + Document + pre-flight validator, rungs 5–6) SHIPPED + live-validated S89** (`sprints/archive/sprint-89.md`). **S90 (fluency — reach half of rung 7: `/syntax` cheat-sheet, sig-grain harvest, importable-symbol search, silent greppable log) is APPROVE-WITH-REVISIONS — see §11** (the durable record of the S90 Phase-2 `/arch` review; verdict transcribed into `sprints/SPRINT.md` by `/sprint`). The implementable int-side plan is `design/int/agent.md`; the REPL experience is `repl/spec.md §17`; the module-preamble form is spec §8.16. This doc remains the master architectural reference; §§ below describe the full target, with phasing in §9 and the S90 fluency-phase review in §11.
**Owner:** `/arch` (crate/feature boundary). Cross-skill: `/repl` (experience), `/int` (dispatch + session wiring), `/spec` (spec-retrieval + module-preamble packaging).
**Provenance:** Authored by `/arch` (S86) against the user's vision and refined through an `/arch`↔user design conversation. Greenfield — no prior LLM-as-feature design exists; the only adjacent concept is `/learn` (FIXME 0052), a scripted tutorial, not an LLM. First-principles + this codebase; the sketch has no REPL-agent precedent.

---

## §1. Vision, goals, non-goals

### 1.1 Vision
The REPL is already self-documenting: every symbol/expression/special-form typed at the prompt yields useful `:Type value` feedback (root `CLAUDE.md` §"Design Principles"; `repl/spec.md` §4). The embedded agent extends that principle into a **development partner** that lives inside the live session.

The agent's range spans from whiteboard reasoning to compilable code in one breath — illustrated by the kinds of things a user asks it: *"how can I decompose this requirement into modules?"* (architecture advice) … *"write a data structure with an O(1) lookup for a cache of this record"* (concrete, typed code synthesis). It must be fluent across that whole span, always grounded.

### 1.2 Goals — two tiers
- **Tier 1 — the grounded advisor (core starting point).** Super-powered over four substrates: **errors** (type/runtime/link → explanation + fix), **platforms** (what's available, their effects/schema), and **modules** — both **stdlib** and **project** (exports, sigs, docs). Retrieval + grounding; the MVP, and it stands alone.
- **Tier 2 — the development partner (the actual product).** Help the user **architect → design → build → test** *their* vision. This is the same skill decomposition this compiler project runs on itself (`/arch`, `/design`, `/dev`, `/qa`) — the embedded agent gives the Cranelisp user's project that same skilled-collaborator lifecycle. **Put this at the top of the goals: the agent brings the project's own development discipline inside the user's REPL.**
- **G-ground** Grounded, not hallucinated. Cranelisp is a *private* language — the model has zero prior knowledge of it (§6), so grounding (project state + spec + an always-on language primer) is mandatory, not optional.
- **G-legible** Every action the agent takes is a visible REPL command/input, echoed as if typed (§4.4) — the session stays a legible, replayable script.
- **G-light** Feature-gated, off by default; the REPL works fully without it (§7). Cf. the optional-prelude principle.

### 1.3 Non-goals
- **NG1** Not a replacement for the deterministic REPL. `(…)`/`[…]`/`/…` always route to the existing machinery, untouched (§5). Additive only.
- **NG2** Not required for the language to work. An LLM-free build is a first-class default.
- **NG3** Not a silent autopilot. Code writes are confirmation-gated; understanding writes are consultative (§2, §7).
- **NG4** Not part of the release tier. Orthogonal to `--release` (Phase H); a *dev-session* capability (like introspection — see the "Introspection is REPL-only" memory) that never ships in a `--link`/`--release` artifact.
- **NG5** Not a normative change to the deterministic REPL spec, beyond one additive dispatch section + the module-preamble prerequisite (§3.4, §10).

---

## §2. The three modes

The agent is not a waterfall of lifecycle phases the user switches between. The modes that earn their keep are cut by **what the agent touches and the consent that touch requires** — the agent slides between them fluidly inside one conversation (Build and Document usually pair):

| Mode | Touches | Consent | Notes |
|---|---|---|---|
| **Advise** | reads only (errors, platforms, modules, spec, the project's own docs) | autonomous, no confirmation | most turns live here |
| **Build** | writes *code* — defns/types via `submit_repl_input` | **confirm each submission** | the "build my vision" hands |
| **Document** | writes *understanding* — docstrings + module preambles | **consultative** ("shall I record that as `solver`'s preamble?") | how accumulated intent becomes durable (§3) |

"Architect" and "design" are *Advise* turns that happen to produce structure and signatures; they become durable only when promoted into code (Build) and docs (Document). There is no separate "architect subsystem" — there is reasoning (Advise) that lands in the two write modes.

---

## §3. Memory architecture

The agent's persistent memory is **mostly the project's own docstrings and module preambles** — not a private store. The self-documenting principle, turned inward on the agent.

### 3.1 Primary store — docstrings + module preambles (in the `.cl` code)
Authoritative, version-controlled, human-readable, *shared* (humans edit them too), and already retrievable through the existing `/doc`/`/info`/exports surface the agent uses as tools. The agent's understanding can't bit-rot in a hidden place because it lives where humans look. The agent maintains it in **Document** mode (consultative). Virtuous loop: the agent reads its memory via the same introspection it advises with, and grows its memory by improving the docs — so memory-maintenance and documentation are the *same* activity, and the human benefits directly.

### 3.2 Secondary store — a small persistent sidecar (the residual)
Cross-cutting intent that has no natural docstring home: the overall vision, "why X over Y," open questions. **Small by design.** (Exactly the `memory/` + design-doc split this compiler project runs on; the user's project gets the same.) The only part that needs explicit serialization + reconciliation across sessions.

**The line** (keep the sidecar tiny): *anything that describes a specific named thing goes on that thing (docstring/preamble); only genuinely cross-cutting, no-single-home intent goes to the sidecar.* This pushes the agent to attach understanding to the code it's about.

### 3.3 Derived index — a pure cache, not a store
A reconstructible read-index over the docstrings/preambles + symbol tables for fast retrieval. **Never the source of truth** — blow it away and it rebuilds from the files/session. Because the read path harvests fresh from live structures each turn (§4.1), this index is an *optimization*, not a necessity, and it has **no cache-invalidation problem**: the symbol table is the truth.

### 3.4 Prerequisite: module preambles must be first-class
Docstrings already are (`PrimitiveDef.docstring`, `/doc`, defn docstrings). Module-level documentation — a preamble block the agent can read and rewrite — may not be a first-class, addressable, editable concept today. **Making it one is load-bearing** for this memory model: a normative module-preamble form + `/doc <module>` to read it + an edit path. A small `/spec` + `/repl` item to confirm/build before the rest leans on it.

---

## §4. Context — harvest, don't fetch

### 4.1 The embedded advantage
An external assistant peers through a keyhole (grep/LSP/file reads) and pays a round-trip per fact. This agent is **in-process**: the symbol tables and the introspection dictionary are live structures in the same address space. Baseline context is therefore **harvested** — assembled fresh from live memory every turn at ~zero cost — not retrieved. That's where the "omniscient" feel comes from: the agent is never ignorant of, or stale about, the user's own code, because it reads the same tables the compiler just wrote. (Docstrings/preambles live on those same entries, so one harvest pass surfaces both current state *and* accumulated understanding.)

### 4.2 The problem flips: from retrieval to selection under budget
Omniscient ≠ dump everything. A real project has thousands of symbols; you can't prepend the table, and irrelevant entries dilute attention as badly as missing ones. **Token budget is the governing design principle.** So the centerpiece module is a continuous, in-process **context harvester + relevance ranker**; the omniscient feel is engineered by always selecting the *right* slice, cheaply, from signals that are also in-process and free (cursor module, symbols named/referenced in the message, the last error + its implicated symbols, recently-defined entries via the symbol table's `seq`, the import-graph neighborhood, the transcript).

### 4.3 The push/pull balance
**Push the shape of everything; pull the bodies.**

- **Push (harvested map, every turn, ambient).** Default heuristics (tuning knobs, not architecture):
  - module **preambles + export surface** for the **last ~6 modules mentioned**,
  - **full src of the last ~10 fns mentioned**,
  - **full src of the current module** (pinned).
  Recency ("mentioned") = appeared in the transcript or surfaced by a command, ordered by the symbol table's `seq`. The budget enforces a **graceful-degradation ladder**: current-module full-src → preamble+exports+mentioned-fns → preamble+exports only.
- **Pull (depth on demand, enacted).** Full source, full docstring, a spec section, CLIF/disasm — for the few things a reasoning step actually bites on.

### 4.4 Tool calls ARE visible REPL commands (the keystone)
A pull is the agent **issuing a REPL command on the user's behalf**: ask for source → answered by `/source foo` → rendered in the transcript *as if the user typed it*. Consequences:
- **No separate tool registry** — the agent's pull-surface *is* `dispatch_command`; a pull synthesizes a command string and runs it through the same `process_commands` path a keystroke uses.
- **Visibility is uniform; only consent differs** — reads auto-run-and-show; writes (submit a defn, `/sh`) confirm-and-show. Everything the agent does is on screen as a REPL line.
- **It's a teaching surface** — the user *watches* the agent reach for `/source`/`/info`/`/refs` and learns the vocabulary by observation.
- **Pulls warm the push** — once pulled, `foo` is "mentioned" and enters the harvest window next turn. Push and pull interlock.

**Principle: the agent has no private tools — its entire capability surface is the REPL command set.**

**Corollary — the agent grows the REPL for everyone.** When the agent needs something the command set lacks (e.g. "find the tests that reference this symbol"), that need is also a human's: it becomes a command (`/refs <sym>`, `/tests-for <sym>`, `/callers <fn>`, `/uses <type>`) serving both. The agent is a **forcing function for the REPL's introspection vocabulary.** *Implementation note:* today's introspection is **forward** (name → sig/doc/source); these are **reverse** queries we don't have. In a REPL the full ASTs are already in memory, so the cheap MVP is an **on-demand scan** over the in-memory bodies — no maintained reverse index, no invalidation in a mutating session; promote to an index only if scan latency bites.

### 4.5 Self-tuning telemetry
Treat the push as a **cache**; the goal is **max hit-rate under the token budget**; every pull is a miss. Log misses, and **split** them:
- **Compensatory pull** — the target was *close* to scope (same module; a direct callee/caller of an in-window fn; a symbol that aged out). The heuristic should have included it. **This is the tuning signal** — its distribution names which categories to promote into the push defaults.
- **Legit deep-dive** — something the push could never anticipate. The healthy push/pull split working; not a miss to fix.

The same "instrument compensation" loop applies to generation (§6.3). Measure compensation → curate what's pushed → fewer compensations.

### 4.6 Honest bound
The agent is omniscient about **code + docs + spec** — not about *unstated* intent. The only intent it has is what's been captured (docstrings/preambles/sidecar). State this plainly; it's the engine of the loop: every **Document** edit converts mind→harvestable-substrate, so omniscience *grows as you work*.

### 4.7 Open: push transparency
Pull is enacted-and-visible; push is ambient-and-silent. Should the push be *partially surfaced* — a collapsed, expandable header like `⊙ in scope: solver (full), grid·html (api), +10 fns` — so the user can see/audit/**prune/extend** what the agent reasons over? Costs screen space; buys legible, steerable omniscience. **RATIFIED (U4, §10): ambient for the MVP, prunable header in Phase 3** — the harvest stays silent through Phase 1–2; the header rides Phase 3 once telemetry informs what to surface (§9 Phase 3).

---

## §5. The dispatch model

### 5.1 The current seam
The read loop (`src/main.rs:240-306`): accumulate lines; a line is **complete** when it starts with `/` (slash, single-line — `main.rs:251`) OR `parens_balanced(&buffer)`; else continuation. On complete, `process_commands` (`src/repl.rs:419`) sorts: blank/comment → `Nothing`; slash → dispatch; bare special-form → `Final`; else → `Compile` → `eval`. Bare atoms/literals (`3`, `+`, `foo`) flow to `eval`'s bare-symbol introspection gate (`eval.rs:447`) — the §4 self-documenting behavior.

### 5.2 The bare-atom tension
The naive "slash + bracket → REPL, else → agent" rule **breaks self-documentation**: `+`, `foo`, `42` match neither slash nor bracket and would route to the agent, regressing the heavily-tested `repl/spec.md` §4 contract.

### 5.3 Recommendation — route by "parses as a complete form, or a slash command"
```
classify(line, buffer_state):
  starts with '/'                 -> ReplSlash      (unchanged)
  blank / comment-only            -> ReplNothing    (unchanged)
  try parse(buffer):
    Ok(complete sexp(s))          -> ReplForm        (atoms, literals, lists, vectors — the §4 surface)
    Err(unclosed '(' or '[')      -> Continuation    (unchanged: parens_balanced gate)
    Err(other parse error)        -> Agent           (not Cranelisp -> natural language)
  feature off                     -> Err(other) falls back to today's parse-error display
  agent dormant / --agent OFF     -> Agent arms fall back to today's deterministic display  (§7.4 invariant)
```
**Zero regression** (anything the reader accepts routes deterministically); the brackets rule is a strict subset of "parses as a form." The discriminator is the reader the REPL already trusts (`cranelisp_frontend::parse`, `eval.rs:78`), called one step earlier to *decide routing*.

**The active ⇒ route / dormant ⇒ today's-display invariant (S89 ruling, `/arch` 2026-06-22).** The `Classify::Agent` arms — bare-unbound and `Err(other parse error)` — fire only when the agent is **runtime-active** (compiled `--features agent` AND `--agent` not OFF AND a provider is reachable). When the agent is compiled-in but **dormant** (`self.agent == None`: no model/key, or `--agent` OFF / `--no-agent`), the `Classify::Agent` arms fall back to *today's deterministic display* — the bare-unbound case reaches `eval.rs`'s unbound-symbol introspection; the parse-error case surfaces the `format_error` diagnostic — i.e. the dormant feature-ON build behaves byte-identically to the feature-OFF build for these two inputs. **This is a refinement WITHIN the ratified U1 contract, not a reversal.** U1's whole purpose is routing to a *working* agent; routing to a dormant one that can only print the U6 "not configured" notice is strictly worse UX than the parse-error / undefined-name diagnostic the user gets today. The S88 ratification already pins feature-OFF as byte-identical (§7.5); extending byte-identity to *dormant* feature-ON is the conservative reading of "route only to a live agent." The guard belongs on the **route decision** (gate `Classify::Agent` on agent-active in `main.rs`, alongside the existing `#[cfg(feature="agent")]`), NOT solely inside `agent_turn` — a dormant `agent_turn` that prints the U6 notice on a *classifier-diverted* input is the defect; the U6 dormant notice remains correct only for the **explicit** `/ask` door (§5.3), where the user has named the agent deliberately. Invariant: **agent ACTIVE ⇒ route per U1; agent dormant/off ⇒ today's deterministic display; `/ask` when dormant ⇒ U6 notice (explicit door, unchanged).**

**The one ambiguity** — a bare single word ("hello", "why") parses as a symbol and would route to introspection. Resolve with a minimal escape hatch: **`/ask <text>`** (and/or a reserved leading `\`) forces agent routing. Multi-word prose is never a single valid sexp (two bare symbols = parse error), so real sentences route to the agent with no sigil. With the feature off, `/ask` prints "agent not built in."

### 5.4 Cadence
The agent turn slots inside the existing REPL cadence (`overview.md`) as a new branch: it may spin a model↔tool sub-loop (synchronous to the user's Enter, like a normal eval); its `submit`/pull re-enter the compilation cadence through the same `eval`/`process_commands` handoff a keystroke would; the watcher polls at prompt boundaries (after the turn resolves). Ctrl-C interrupts back to the prompt; because mutation is confirmation-gated and staged (§6.2), an interrupt leaves the session consistent.

---

## §6. Novel-language correctness — primer + validator

Cranelisp is private; the model has **zero** of it in training. Without supplementation it will emit code with syntax errors — and an error *from the assistant* breaks flow worse than one from the user. Two layers, the second of which the embedded setting makes nearly free:

### 6.1 Layer 1 — supplement the prior (push, always)
A compact, curated **language primer + canonical few-shot idioms** (a defn, a deftype, a match, a trait impl, a module-with-preamble) is **always in context** — syntax, special forms, the `:Type` convention, the prelude surface. Distinct from the (large, retrieved) spec: the primer is the distilled *always-needed* essentials, because every generation needs syntax. Curate it; tune it from §6.3.

### 6.2 Layer 2 — the validator role (the embedded killer move)
The in-process compiler is also the agent's **pre-flight validator**. Before generated code is shown as the answer, run it through the **real frontend + typechecker**; on failure, feed the *actual compiler error* back and retry — **silently, invisible to the user.** This is not new machinery: it is the existing **cluster-atomic staging** (commit-on-Ok / discard-on-Err). The agent stages; only clean code reaches the live session and the screen. The user **structurally cannot** see a syntax error from the agent — the primer lowers the retry rate, the gate guarantees the floor.

**So the in-process compiler has three roles for the agent: read (harvest, §4), write (commands/submit, §4.4), and validate (pre-flight).** The validator role is what an external assistant can't cheaply have, and it turns "novel language" from a flow-breaker into a non-event.

### 6.3 Telemetry closes the loop
Pre-submission failure categories are the tuning signal for the primer, exactly as compensatory pulls tune the harvest (§4.5). One discipline: **instrument every place the agent had to compensate (a pull, or a fail-and-retry), and let the distribution drive what's curated into the push.**

### 6.4 Validator policy — RATIFIED: silent-repair anything (U5)
Syntax has a clean answer — **always silent-repair, never break flow.** Type errors are ambiguous: some are the agent fumbling a signature (hide + repair); others are a real design signal the user should see. The fork was: silent-repair *anything* that doesn't compile, or **parse errors only** + **surface type errors as a collaboration moment** (the original lean).

**RATIFIED (user, 2026-06-21; `sprints/archive/sprint-88.md` §"U1–U6 ratification gate"): SILENT-REPAIR ANYTHING.** The user OVERRODE the original "surface type errors" lean: **both** parse AND type failures are hidden-and-repaired; the user **structurally cannot** see an agent compile failure (max flow over collaboration-on-type-errors). This decides the validator's policy for the Phase-2 implementation (§9 Phase 2). **No interface consequence:** the validator is a typecheck-only dry-run over the existing staging (stage → check → discard, silent — §7.5), and silent-repair-anything means it simply discards on *any* `Err` (parse or type) and re-prompts the model with the captured compiler error — which is exactly what the existing `check_forms` discard-on-Err arm already does (Decision 44). "Repair anything" needs *less* machinery than "surface type errors" would have (no error-classification branch, no surfacing path). `pub(crate)`, int-internal, no facade/`cranelisp-types` delta.

---

## §7. Architecture, backend, safety

### 7.1 Where it plugs in
A feature-gated **`src/agent/`** module, `pub(crate)`, sibling to `repl.rs`/`eval.rs`. The §5.3 classifier gains an `Agent(text)` arm calling `session.agent_turn(...)`. `agent_turn` runs the model↔tool loop; reads call the existing `handle_*` directly; writes + pulls go back through `self.process_commands`/`self.eval` — the *same* path `main.rs` uses, inheriting cluster-atomic staging, error recovery (`repl/spec.md` §5.2), and backing-file regeneration. The agent holds the REPL-cadence `&mut CompilerSession` handle, not a new state window; it reads live state through the existing introspection surface (`describe_symbol` `repl.rs:300`, the `handle_*`, the symbol-table accessors).

### 7.2 Feature gating (mirror the release-backend precedent)
```toml
# src/ binary crate Cargo.toml
[dependencies]
<llm-client> = { version = "...", optional = true }
[features]
agent = ["dep:<llm-client>"]   # OFF by default
```
`agent` in no crate's `default`; no dev-dependency enables it; `cargo build`/`cargo nextest run` never compile the client → the default build + ~9s suite stay agent-free. The published binary MAY ship `--features agent`; agent tests run in a separate lane behind `#[cfg(feature="agent")]`.

### 7.3 LLM backend
Default to an **API backend** (best capability/latency), configurable, behind a **pluggable backend trait** so a local-model/alternate-provider backend drops in without touching the agent loop. **Opt-in twice** — compiled in (flag) AND enabled at runtime (config/key present); absent a key the agent is dormant and `/ask` says so. The artifact carries only a small HTTP client (the service is hit at runtime), not a build-time toolchain.

### 7.4 Safety & boundaries

**Dormant ⇒ today's deterministic display (S89 ruling, `/arch` 2026-06-22 — the classifier active-state guard).** "Opt-in twice" (§7.3) means the agent is **dormant** when compiled-in but lacking a runtime provider/key, or with `--agent` OFF. Dormancy MUST gate the §5.3 classifier's `Classify::Agent` route, not just the body of `agent_turn`: when the agent is dormant or `--agent` is OFF, the classifier's two divert arms (bare-unbound symbol; non-paren parse error) **fall back to today's deterministic diagnostic** (the same display the feature-OFF build produces — §7.5), rather than diverting to a dormant `agent_turn` that can only print the U6 "not configured" notice. The U6 dormant notice is correct **only** for the *explicit* `/ask` door (the user named the agent deliberately); it is a regression on the *classifier-diverted* path, where today's undefined-name / parse-error diagnostic is strictly better UX. Invariant: **agent ACTIVE ⇒ route per U1; agent dormant/off ⇒ today's deterministic display; explicit `/ask` while dormant ⇒ U6 notice.** This is a refinement within the ratified U1 contract (route only to a *live* agent), not a U1-semantics change — `/dev` implements directly (the guard is the agent-active condition added to the `Classify::Agent` route gate in `main.rs`, beside the existing `#[cfg(feature="agent")]`); `pub(crate)`, int-internal, zero public-API / cross-crate impact. See §5.3 for the classifier pseudocode carrying this arm.

- **Deterministic vs. model output unmistakable.** The deterministic REPL owns the `:Type value` format and `;`-drawer; the agent uses a distinct reserved visual frame (reusing `src/style.rs` with its own role so `--no-color`/`NO_COLOR` degrade). Agent-issued commands + their results render in normal REPL style (they *are* normal output, §4.4); only the agent's prose is framed.
- **Consent.** Reads auto-run-and-show; **Build** writes confirm-and-show (exact line shown); **Document** writes are consultative. Default "auto-approve reads only."
- **Transcript transparency.** Everything the agent does is a visible REPL line → the session stays a legible, replayable script (preserves the §15 persistence model + reproducibility).
- **Privacy / offline.** Opt-in twice; a one-time first-use notice (what is sent: the message, harvested signatures/excerpts; to where: the configured endpoint); a local-model escape hatch. The agent's view is bounded by the introspection surface + spec, not the host filesystem (no raw file-read tool; spec is the embedded curated `spec/`).
- **`/sh`.** No direct shell tool. Shell is reachable only via `submit_repl_input("/sh …")` — confirmation-gated, so the agent *proposes* and the user approves the exact command.

#### `--yes` autonomous-submit flag (S89, scope item 3a) — RULING: policy knob, not a boundary change

A REPL-only CLI flag `--yes` (companion to `--agent`/`--no-agent`, `repl/spec.md §0.6.1`) makes the agent's write-consent gates **auto-accept** — the Build-mode form-submit confirm and the Document-mode consultative preamble/docstring edit — so the agent acts without the per-action `[y/N]` prompt.

**It is a policy knob (human-in-the-loop → trust mode), NOT a structural-floor change.** It auto-*answers* the gate; it does not relocate, widen, or remove it. The R3 structural floor — *read-only-by-default is the floor; the write arm is reachable only past the confirm-gate, re-entering through the same `process_commands`/`eval` cluster-atomic staging path (commit-on-Ok / discard-on-Err)* — is unchanged. Writes remain structurally unconstructable except through that one gated path; `--yes` only sets the gate's answer to "accept" instead of prompting. The read-only pull allowlist is untouched (`--yes` answers only the gate that already guards writes; reads were never gated). No new write path, no parallel submit, no new state window.

**Validation-floor invariant (non-negotiable).** `--yes` bypasses **consent, not validation.** The pre-flight validator (the typecheck-only dry-run over staging, stage→check→discard, silent-repair-anything — U5, §6.2/§6.4) still runs on every submission; only compiling code ever reaches the live session. "Skip confirm" and "skip check" are **distinct concerns at distinct seams** — the confirm-gate is the consent seam; `validate_forms_dry_run`'s discard-on-Err arm is the correctness seam — and `--yes` touches only the former. An implementation that conflated them (treating `--yes` as "skip the dry-run") would be a defect; this is called out as a **Phase-5 `/dev` guard + `/qa` test obligation**: a `--yes`-on test must prove a deliberately-broken generation is still silently repaired (never submitted raw), exactly as with `--yes` off — the validator's behaviour is invariant under the flag.

**Design-point recommendations** (scope item 3a a/b/c):
- **(a) Blanket vs Build-only — RECOMMEND blanket.** One `--yes` covers all agent write-consent gates (Build submit + Document edits), per the universal `-y` convention. Both gates are the same consent seam answered the same way; splitting them adds surface for no boundary-meaningful distinction (Document writes are *consultative* but still gated, and are no more dangerous than Build — both pass the validator / round-trip byte-stably). One flag, one mental model.
- **(b) First-use notice — RECOMMEND yes, one-time.** `--yes` is an autonomy escalation (the agent now writes without per-action assent), parallel to the S88 U6 opt-in-twice + first-use disclosure. A one-time first-use notice on the first auto-accepted write — naming that the agent will now submit/edit without prompting, and that the pre-flight validator still gates correctness — is warranted. **Wording is `/repl`-owned** (`repl/spec.md §17`, the agent-experience home; sibling to the U6 disclosure). `/arch` rules only that the escalation *warrants* a notice; `/repl` authors the text.
- **(c) Naming — `/arch` defers to `/repl`.** `--yes` (with `-y` short form) follows the universal convention and is the recommended default, but the user-facing flag name is an experience surface — `/repl` owns it in `repl/spec.md §0.6.1` alongside `--agent`/`--no-agent`.

**Public-API / boundary impact: ZERO.** `--yes` is an int-internal `pub(crate)` CLI flag parsed in `src/`, threaded as a bool into the existing consent-gate decision. No `cranelisp-types` change, no facade delta (int's library facade is retired; its contract is the CLI `//!` narrative + `repl/spec.md` + the e2e suite), no `public-api.txt` movement, no new cross-crate edge. It is `#[cfg(feature="agent")]`-gated and a no-op on default builds, exactly like `--agent` (§7.2). Feature-off byte-identity is preserved by construction.

### 7.5 Grafting & facade impact
int's *library* facade was retired (`facades/int.md` → BC §6; a binary has no `public-api.txt` boundary — its conformance gate is the e2e suite). int's contract is therefore the **CLI narrative** (`src/main.rs` `//!`), the **REPL experience** (`repl/spec.md`), and the **e2e suite**. "Without breaking the facade" = don't disturb that deterministic contract.

The graft is neat because the agent is a new **consumer** at three existing seams + one new sibling module — nothing rewired:
- **Dispatch** (`src/main.rs`): one new `Agent(text)` classifier arm (§5.3); existing arms untouched.
- **Commands** (`src/repl.rs`): one new `/ask` `ReplCommand` variant; pulls reuse `dispatch_command` + the existing `String`-returning `handle_*` unchanged — the agent *consumes* the command surface, doesn't modify it.
- **Eval/validate** (`src/eval.rs`): writes + the pre-flight validator reuse the existing `eval`/cluster-atomic staging; no new eval entry.
- **Module:** `src/agent/` is another sibling in int's established session decomposition (the `eval.rs`/`repl.rs`/`process_form.rs` `impl CompilerSession`-over-`pub(crate)`-fields pattern). Fits exactly.

All four cuts are `#[cfg(feature="agent")]`. **Feature-off ⇒ the binary is byte-identical to today** — no LLM dep in the build graph; the dispatch path unchanged (the `Err(other parse error)` case falls back to today's diagnostic) — so the REPL/CLI contract and the e2e suite are preserved **by construction** (same discipline as §7.2: `agent` in no `default`, no dev-dep enables it).

**Zero new cross-crate edges.** The agent is fully contained in the int bounded context: it reads int's own symbol tables/introspection and reuses int's *existing* inward calls to frontend/typecheck/backend (harvest, validate). No other crate's `public-api.txt`/facade moves.

Where it is *not* free (the honest list):
- **`repl/spec.md` gains an additive agent section** (+ `/ask`, the agent-output frame, the `--agent` row) — the only deterministic-contract change, additive + behaviorally gated.
- **Module preambles first-class** (§3.4) — the one genuinely new language/REPL concept, not just plumbing (the prerequisite; `/spec`+`/repl`).
- **One new internal seam:** a *typecheck-only dry-run* over the existing staging (stage→check→discard, silent, no commit/print) for the validator's repair loop — distinct from the existing stage→check→commit→print. `pub(crate)`, internal to int; not a facade change.
- **Additive surface:** the reverse-query commands (`/refs`/`/tests-for`) + modest `pub(crate)` field widening per the existing sibling-module pattern.

The rule that keeps it neat: **the `#[cfg(feature="agent")]` cuts live AT the seams (three of them) — bolted on, not woven through.** Feature-off is provably the original REPL.

---

## §8. Relationship to existing concepts
- **`/learn` (FIXME 0052)** — a *scripted* tutorial; the agent complements and could eventually subsume it (a conversational tutor grounded in the spec is a strictly more flexible `/learn`). Keep separate initially (the tutorial is deterministic + offline; the agent is neither). No coupling in the MVP.
- **Self-documenting surface** — the agent *leans on* it (harvest, tools) rather than duplicating it; and via **Document** mode it *feeds* it.
- **Spec impact** — `repl/spec.md` §1–§16 unchanged except (1) a new agent-dispatch section (+ `/ask` + the agent-output frame + an `--agent`/`--no-agent` §0.6 row), and (2) the **module-preamble** first-class concept (§3.4). Both additive; `/repl`-owned, with a `/spec` consult for the preamble form.

---

## §9. Phasing
- **Phase 1 — Advisor MVP.** Feature-gated `src/agent/`; §5.3 classifier + `/ask`; API backend (opt-in twice); harvested push (§4.3 heuristics) + pull-as-visible-commands (§4.4); **Advise** mode (read-only) + the always-on **language primer** (§6.1); spec retrieval (grep over embedded `spec/`); telemetry skeleton (§4.5). No writes yet (proposes code, doesn't submit). Acceptance: ask "how do I define a constrained function over Num?" → a spec-grounded, session-aware answer with a proposed `(defn …)` shown.
- **Phase 2 — Build + Document + validator (S89, rungs 5–6).** The agent's first **write** path. Build mode: the read-only pull allowlist (§4.2/Phase-1) is **extended with a confirm-gated write arm** — a submitted form goes back through `process_commands`/`eval` (the *same* cluster-atomic staging path `main.rs` uses, commit-on-Ok / discard-on-Err, §7.1), **no new eval entry** (§7.5); writes remain structurally unconstructable without passing the gate (consent is the allowlist + the confirm, exactly as Phase-1 read-only was structural by allowlist-exclusion). The **pre-flight validator + silent-repair-anything** (§6.2, U5 ratified §6.4): before generated code is shown or submitted, run it through the real frontend + typechecker on staging via the **typecheck-only dry-run seam** (stage → check → discard, silent — §7.5; `pub(crate)`, int-internal, no facade delta), repairing on *any* failure. **Document** mode: consultative docstring/preamble edits, reusing the S88 first-class module-preamble substrate (`SymbolTable.module_preamble` + `capture_module_preamble` + the byte-stable regen path — no new `cranelisp-types` change; cache schema already v9). Acceptance: the agent defines a user-approved function that *always at least parses*, a deliberately-broken generation is silently repaired and never shown, and a preamble the agent writes round-trips byte-stably and is read back by next session's harvester. **Zero new cross-crate edges; zero `public-api.txt` baselines move** (agent additions stay `pub(crate)`, int-private, behind `#[cfg(feature="agent")]`).
- **Phase 3 — Self-tuning + reach.** Compensation telemetry drives push/primer curation (§4.5/§6.3); reverse-query commands (`/refs`/`/tests-for`); semantic spec search (precompute-and-ship index); pluggable local-model backend; optional push-transparency header (§4.7). 

**Scheduling.** Its own track — **not gated by and not gating Phase H**. A dev-session feature; never ships in `--link`/`--release` (NG4). `/sprint` schedules it independently.

---

## §10. Sign-off — U1–U6 RATIFIED (user, 2026-06-21)

All six sign-offs are ratified; the durable record is `sprints/archive/sprint-88.md` §"U1–U6 ratification gate". Summary:

- **U1 — Dispatch.** **ADOPT + REFINED** — `/ask` is the explicit door; else parse → unclosed = continuation, parse-error = agent, `Ok` compound = REPL, bare atoms resolve (all-known → REPL §4; any unbound → agent). Symbol-resolution-aware (the bare-prose-parses-Ok reality gap), not the literal bracket rule. Feature-off byte-identical. (§5.3; `design/int/agent.md §2.2`.)
- **U2 — Module preambles first-class** (§3.4). **ADOPT** — landed S88: additive `SymbolTable.module_preamble: Option<String>` field (FIXME 0428, BC §7), `CACHE_SCHEMA_VERSION` 8→9, the `;;`-leading-comment-block form (spec §8.16), `capture_module_preamble` + byte-stable regen. Phase-2 Document mode reuses this substrate with **no further interface change**.
- **U3 — Memory line** (§3.2). **ADOPT** — named-thing → on the thing; only no-home intent → tiny sidecar (sidecar is Phase-3+).
- **U4 — Push transparency** (§4.7). **AMBIENT for MVP; prunable header in Phase 3** — the harvest is ambient/silent in Phase 1–2; the header rides Phase 3 over the same harvest map (§9 Phase 3).
- **U5 — Validator policy** (§6.4). **SILENT-REPAIR ANYTHING** (user override of the original "surface type errors" lean) — parse AND type failures hidden-and-repaired; the user structurally cannot see an agent compile failure. Lands in Phase 2 (S89). No interface consequence (§6.4, §7.5).
- **U6 — Backend + privacy** (§7.3/§7.4). **OPT-IN-TWICE + first-use notice** — dormant unless built `--features agent` AND a reachable provider; one-time disclosure names **source excerpts** (not just signatures) + endpoint.

### Cross-skill handoffs / Next skills
*(Filed as `design/arch/fixmes/NNNN-*.md` when scheduled by `/sprint`. The Phase-1 MVP handoffs landed in S88; the Phase-2 design-lock handoffs (write-allowlist arm, validator dry-run seam) are S89.)*
- **`/repl`** — the experience: agent-dispatch section + `/ask` + agent-output frame + `--agent` row; **module-preamble** form + `/doc <module>` (§3.4); the reverse-query commands (§4.4).
- **`/int`** — dispatch + session wiring: the §5.3 classifier, `src/agent/` + feature gate (§7.1/§7.2), the `agent_turn` loop, the validator-on-staging path (§6.2), the harvester/relevance-ranker (§4.2/§4.3), telemetry (§4.5).
- **`/spec`** — the module-preamble normative form (§3.4); spec-retrieval/embedding packaging if it touches `spec/` layout.
- **`/arch`** — the `agent` feature boundary/discipline; the ruling that the agent is a REPL-cadence consumer of the existing surface (not a new state window); the three-roles-of-the-in-process-compiler framing (read/write/validate).
- **`/qa`** — agent-feature tests behind `#[cfg(feature="agent")]` (separate lane): classifier routing, pull-as-command wiring, the validator repair loop, echo-as-typed reproducibility. Default suite stays agent-free.

---

## §11. S90 Phase-2 review — the fluency phase (reach half of rung 7)

**Status:** APPROVE-WITH-REVISIONS (`/arch` Phase-2, 2026-06-23). Verdict transcribed
into `sprints/SPRINT.md` by `/sprint`; this section is the durable architectural record.

S90 delivers the **"reach"/fluency half of rung 7** as four pillars on the existing
`agent` feature gate. All four are **REPL-cadence consumers of the existing int surface**
(§7.1 / BC §6.3) — no pillar opens a new state window, and the **byte-identical-feature-OFF**
(§7.5) + **zero-new-cross-crate-edge** (§7.5) invariants hold for all four. The pillars:

1. **`/syntax` topic cheat-sheet** — a curated, verified-compiling, topic-keyed
   core-language reference; a REPL command (human) that is also an agent pull-tool; the
   primer cross-references the topic *names*. This is the primer-appropriate kind of
   grounding (core syntax, derived from spec); prelude/stdlib idioms stay harvest-sourced
   per the `agent-prelude-awareness-via-harvest-not-primer` ruling. Mechanically it is a
   new read-only `/syntax` command (additive to the §4.2 allowlist) + a static asset; no
   new machinery.
2. **Harvest at signature grain** — the harvester (§4.1/§5) surfaces in-scope prelude +
   imported symbols at **name + type signature + docstring** grain each turn. This is the
   user-directed way to keep prelude+imports in context (harvest, NOT primer). It reads the
   same live symbol tables `harvest_context` already reads (`src/agent/harvest.rs`); the
   only change is the *grain* (add signature + docstring to the export-surface arm). Pure
   read enrichment of an existing harvest arm — Principle 7 (the symbol table is the
   source of truth), no copy-store.

### §11.1 Pillar 3 — importable-symbol search: the typecheck-to-index-then-discard seam

Pillar 3 searches symbols **reachable on the lib search path but not yet imported**, by
name and/or type signature. To know an importable symbol's signature its defining module
must be typechecked — but it must **not** be imported into the session. The mechanism is
**typecheck-to-index-then-discard**: typecheck a reachable module against throwaway
staging, index its public symbols (name + signature + docstring + originating module),
**discard the typecheck state**, and serve searches from the index.

**Ruling — the seam lives in int and reuses the S88/S89 validator dry-run substrate;
ZERO new cross-crate edges.** The discard seam already exists: `worker::validate_forms_dry_run`
(`src/worker.rs:308`) builds a **throwaway `SessionSymbolTable` staging** + a
`SymbolTableAccess::cluster(...)` view, runs `cranelisp_typecheck::check_forms`, and
**drops the staging on every path — never commits** (the §16.1 discard arm; the structural
"zero residue" guarantee). Pillar 3's indexer is a **sibling of this function**, not a new
seam: it runs the same stage→check pass over a *reachable but unregistered* module's parsed
forms, but instead of discarding the *result* it **reads the public entries out of the
staging table** (name + scheme + docstring + module) into an int-side index, *then* drops
the staging. The typecheck is `check_forms` — the **existing** int→typecheck inward call —
so no crate's `public-api.txt` moves and `cranelisp-types` is untouched (Principle 3).

**Why zero residue is structural, not disciplinary.** Residue would mean a session
`DashMap` (`SharedState.symbol_tables` / `module_aliases` / `prelude_fallback` /
`introspection`) gaining an entry for the indexed module. It cannot, by construction:
the indexer typechecks into a **locally-owned `staging` value** (not `symbol_tables`),
exactly as `validate_forms_dry_run` does — the indexed module is **never `register_module`'d**,
so the scheduler/`ModuleState`/alias/fallback maps never learn it exists. The index itself
is a **derived read-cache** (§3.3 — "never the source of truth; blow it away and it
rebuilds"), an int-private `pub(crate)` structure on `SharedState` (or on `AgentState`),
**not** a symbol table and **not** serialized. The +neg isolation test the acceptance
demands asserts exactly this: after an index pass, `symbol_tables`/`module_aliases`/
`prelude_fallback` are unchanged (the same shape as the §16.1 validator-discard guard
`validate_dry_run_discards_does_not_commit`, `src/agent/pull.rs:1088`).

**Index lifetime / invalidation.** Because the index is a pure cache over files on the
search path, invalidation is coarse and cheap: rebuild on search-path change or on a
miss; an indexed entry going stale (a module edited on disk) is a *quality* concern, not
a *correctness* one (the entry is only a search hint — importing it then re-typechecks
for real through the live path). MVP: build lazily on first search, hold for the session,
offer a cheap rebuild. No fine-grained invalidation machinery (Principle 6 — complexity
has a budget; the index is reconstructible).

### §11.2 One index or two (Pillars 2 + 3)

**Ruling — ONE indexing *value shape*, TWO population paths.** The unit both pillars serve
is the same: `{ name, signature, docstring, module }` (the searchable/displayable record).
Pillar 2 (in-scope) populates it from **already-typechecked live tables** — a direct read,
cheap, every turn, ambient. Pillar 3 (importable) populates it from the
**typecheck-to-index-then-discard** pass — expensive, lazy, cached. **Share the record
type and the search/format code; keep the two population paths distinct** — they have
different cost, lifetime, and trigger, and conflating them would force Pillar 2's cheap
per-turn read through Pillar 3's typecheck-and-cache lifecycle (a Principle-8 interim
smell — building heavier machinery than the in-scope case needs). One DTO, one search
function, two feeders. This is the "derived index is a pure cache" model (§3.3) applied
twice with different inputs.

### §11.3 Pillar 3 robustness blocker — FIXME 0432 (the index-time typecheck PANIC)

**Ruling — 0432 IS pulled into S90 as a Pillar-3 prerequisite; Pillar 3 MUST NOT ship
without containment.** The reasoning:

- Pillar 3 runs the **real typechecker** (`check_forms` → monomorphiser) over **arbitrary
  reachable modules at index time**. FIXME 0432 Face B is a monomorphiser `debug_assert!`
  (`crates/cranelisp-typecheck/src/traits/monomorphise.rs:1016`) that fires on a
  multi-clause `defn` + self-call whose params are unannotated — a **common, valid-looking
  shape** (a public 1-arg entry variant delegating to a private accumulator variant). A
  library on the search path can easily contain it.
- The agent's validator (S89) typechecks **one staged user form** on the eval thread. The
  Pillar-3 indexer typechecks **whole third-party modules** — a strictly *broader* trigger
  surface for 0432.
- **Containment gap (verified):** the pool-worker typecheck loop wraps `handle_typecheck_work_shared`
  in `catch_unwind` (`src/worker.rs:1483` — panic → `notify_module_failed`). But the agent
  validator and (as designed) the Pillar-3 indexer call `check_forms` **directly on the eval
  thread with NO `catch_unwind`** (`validate_one_form` → `validate_forms_dry_run`,
  `src/agent/pull.rs:668` / `src/worker.rs:308`; `s.agent_turn(...)` is called bare from the
  `main.rs` read loop). A debug-build session (the agent's only build — `cargo run`/`nextest`
  are debug, so `debug_assert!` is **live**) would therefore **unwind the eval thread and
  crash the REPL** when the indexer hits a 0432-shaped module. The agent can crash the REPL
  by *searching the library* — a robustness defect that defeats the whole feature.

**Two-layer containment, both required:**

1. **Fix 0432 Face B at root (`/typecheck`, the priority face per the FIXME).** The
   monomorphiser must surface the unannotated-self-call ambiguity as a **clean type error**
   (the §3.11 concrete-types-ambiguity ruling — a residual `Var` reaching the mangler is a
   type error, never a `debug_assert!` panic), not a non-concrete-param tripwire. This is
   the durable fix and aligns the mangler with `s84-concrete-types-ambiguity-ruling`. `/qa`
   already owns the repro obligation (0432 `target: /qa → typecheck`).
2. **Defence-in-depth: the index-time AND validator typecheck on the eval thread MUST run
   inside a `catch_unwind`** (`pub(crate)`, int-internal, mirroring the `src/worker.rs:1483`
   pool-worker pattern — convert a caught unwind to a clean `Err`, drop the throwaway
   staging, surface "module failed to index/validate" rather than crashing the REPL). This
   is independently warranted: a typechecker `debug_assert!`/`unreachable!` over *arbitrary
   third-party library source* is exactly the "panic on input the author did not control"
   case the eval-thread path currently does not guard. It also retroactively hardens the
   S89 validator (a model-proposed 0432 form panic-crashing the REPL — the exact hazard the
   FIXME flags). The catch is the **agent-robustness floor**; the root fix removes the
   trigger. Ship both.

**Sizing consequence:** because Pillar 3 cannot ship without (2), and is materially safer
with (1), Pillar 3's full delivery in S90 is gated on the typecheck fire. See §11.5.

### §11.4 Type-signature match semantics (Pillar 3 search)

**Interface is `/arch`'s; the algorithm is `/typecheck`'s.** The index stores each symbol's
type as its `cranelisp-types` scheme (the existing boundary type — no new DTO). The *match
predicate* — exact-shape vs. unification/subsumption (Hoogle-style) — is a `/typecheck`
design detail (it owns inference + unification). **MVP recommendation:** ship **name-fragment
match + exact-structural-shape match** first (cheap, no unifier invocation — compare the
query's parsed type-shape against indexed shapes up to alpha-renaming of type vars), and
record **unification/subsumption match as a `/typecheck`-owned follow-up** (a query
`(Fn [Int] ?)` subsuming `(Fn [Int] Bool)` needs the real unifier and a ranking model).
Exact-shape clears the acceptance criterion ("search by type signature, get name + sig +
module"); Hoogle-style subsumption is a precision upgrade, not an MVP gate. Flagged: whether
the query *syntax* for a type pattern (holes/wildcards) touches spec is a `/spec` consult,
not an `/arch` call — name it in the Phase-3 handoffs.

### §11.5 Pillar 3 sizing — DESIGN-THIS-SPRINT, IMPLEMENT-NEXT (the split)

**Ruling (the user-delegated sizing call): SPLIT — Pillars 1, 2, 4 ship fully in S90;
Pillar 3 is designed this sprint and implemented next, UNLESS the 0432 typecheck fire lands
early enough to pull its implementation forward in-sprint.** Rationale:

- Pillars 1/2/4 are high-value, low-risk, and self-contained (a static asset + a command; a
  harvest-arm grain change; a log sink). They ship regardless (Principle 6 — they fit the
  budget cleanly).
- Pillar 3 is **gated on a cross-skill typecheck fix** (0432 root fix) **plus** the
  eval-thread `catch_unwind` hardening (§11.3), **plus** a new index lifecycle, **plus** the
  match-semantics interface (§11.4). That is materially more surface than 1/2/4 combined, and
  shipping it half-hardened (indexer without containment) would be a Principle-8 interim
  implementation that can crash the REPL. The **design** (this §11.1–§11.4) lands in S90 so
  the seam, the DTO, the discard guarantee, and the containment obligation are pinned; the
  **implementation** lands once 0432's root fix is in (same sprint if the typecheck fire
  completes before Pillar-3 implementation is reached; otherwise next sprint). This keeps
  S90's shippable surface clean and de-risks the one design-risk pillar without discarding
  its design work.

### §11.6 Pillar 4 — silent greppable agent log

**Ruling — a SIBLING sink to `trace.rs`, not an extension of it; zero public-API /
`cranelisp-types` impact.** `src/agent/trace.rs` is an **ephemeral stdout/stderr** wire-debug
trace (env-gated, `eprintln!`, formatting-only, no persistence — verified `src/agent/trace.rs`).
Pillar 4 is a **persistent, structured, file-backed JSONL** insight log with stable keys
(event type, symbol, error class, repair-iteration count, module). The two have different
lifetime, sink, and consumer; folding the persistent log into the ephemeral trace would
overload one module with two unrelated contracts (Principle 6 — keep concerns separate).
Add `src/agent/log.rs` (or `telemetry.rs` — the §8 [R5] skeleton slot the int doc already
reserves) as a new feature-gated sibling that *consumes* the same in-memory event vocabulary
the agent loop already produces (the repair iterations + triggering errors already flow
through `pull.rs`; the pulls through `run_pull`; submits/give-ups through `run_submit`). It
appends one JSON object per event. **Impact: ZERO** — `pub(crate)`, int-private, fully
`#[cfg(feature="agent")]`, off the default build path (byte-identical feature-OFF), no
facade/`cranelisp-types`/`public-api.txt` movement, no cache bump. **Log file location** is
a `/repl`-owned experience detail (env-configurable path, sibling to `CRANELISP_AGENT_TRACE`
in `repl/spec.md §17.10`); `/arch` rules only that it is a dev-session artifact (NG4 — never
in a `--link`/`--release` artifact) and writes silently (nothing extra in the REPL).

### §11.7 `/syntax` ownership split

- **Content** (the cheat-sheet topics + verified-compiling examples) — authored by `/docs`
  (the verified-compiling discipline + token-dense curation is `/docs`' craft), **validated
  by `/spec`** for accuracy against the normative spec (no normative *change* expected — it
  is a *projection* of spec, not new language surface). The asset is a static
  `include_str!` companion in `src/agent/` (sibling to `primer.txt`).
- **Command UX** (`/syntax` bare = list topics; `/syntax <topic>` = dense content; the
  agent-pull rendering) — `/repl` (`repl/spec.md §17`).
- **Tool-wiring** (the `/syntax` `ReplCommand` variant + dispatch + the §4.2 allowlist row +
  the primer topic-name cross-reference) — `/dev (src/)`.

### §11.8 Public-API / `cranelisp-types` impact (all four pillars)

**Confirmed ZERO across all four pillars.** No baseline moves, no `cranelisp-types` change,
no `CACHE_SCHEMA_VERSION` bump. Every pillar is `pub(crate)`, int-private, fully
`#[cfg(feature="agent")]`, byte-identical feature-OFF. Pillar 3's index reuses the existing
`check_forms` inward call and the existing `cranelisp-types` scheme as its stored type — it
needs **no new boundary type** (the index record is an int-private struct). The only
non-int obligation is the **`/typecheck` 0432 root fix** (§11.3), which is a behaviour fix
inside an existing crate, not an edge change. (If a future Hoogle-style match — §11.4 —
wants a query-pattern type that does not already have a `cranelisp-types` home, that is a
`target: /arch` filing at *that* implementation time, not now.)

**Pillar-3 exact-shape match predicate — export ruling (`/arch`, S90 Phase-3, 2026-06-23).**
The exact-shape match (R6 MVP) is `pub fn signature_matches_exact(&Type, &Type) -> bool` — pure
alpha-equivalence, no `CheckState` (`design/typecheck/signature-match.md §6`). **Ruling: export it
from `cranelisp-typecheck` (the design's Option A), NOT inline it int-side (Option B).** Type
equivalence is typecheck's semantics — even pure alpha-equivalence over `Type` — so its home is the
type-owning crate (Principle 17 module locality + Principle 7 single source of truth). Inlining
int-side would hand-roll a second equivalence judgment that must track typecheck's `Type`
representation and var-binding rules in lockstep; a future `Type` variant would silently diverge it
with no compile error. The cost is **one additive `public-api.txt` line in `cranelisp-typecheck`** —
a narrow `fn(&Type, &Type) -> bool` (Principle 2 narrow interfaces), the narrowest possible export,
no new DTO (reuses the existing `Type` boundary). **This is a legitimate edge evolution at Pillar-3
*implementation* time** (next sprint), named + dispositioned in the same change-set per the
baseline-diff discipline. **It does NOT contradict §11.8's "zero across all four pillars" claim,
which is scoped to S90 — where Pillar 3 is design-only and nothing implements.** This is the §11.4 /
R6 anticipated case ("a future match predicate is a `target: /arch` filing at that implementation
time"), pre-approved here so `/design (cranelisp-typecheck)` can pin Option A now in
`signature-match.md §6`. Pillars 1, 2, 4 remain zero-impact unconditionally. (Recorded as R8 below.)

### §11.9 Revisions to scope (R1..Rn)

- **R1 (binding):** Pillar 3 ships **split — design-this-sprint, implement-next** unless the
  0432 typecheck fire completes in time to pull implementation forward in-sprint (§11.5).
  Pillars 1, 2, 4 ship fully in S90 regardless.
- **R2 (binding):** **FIXME 0432 is pulled into S90** as a Pillar-3 prerequisite. Two-layer
  containment, both required: (a) `/typecheck` root-fixes Face B to a clean type error
  (§3.11 / `s84-concrete-types-ambiguity-ruling`); (b) the **eval-thread index-time AND
  validator typecheck are wrapped in `catch_unwind`** (`pub(crate)`, int-internal, mirroring
  `src/worker.rs:1483`) — the agent-robustness floor. The catch lands with Pillar 3's
  implementation (it is also a retroactive S89-validator hardening); the root fix is the
  `/typecheck` fire. Pillar 3 does not ship without (b).
- **R3 (binding):** **One index DTO `{ name, signature, docstring, module }`, two population
  paths** (Pillar 2 live-read; Pillar 3 typecheck-and-discard). Share the record + search +
  format; keep the feeders distinct (§11.2).
- **R4 (binding):** Pillar 3's indexer is a **sibling of `validate_forms_dry_run`** — same
  throwaway-`staging` discard substrate, never `register_module`. Zero residue is structural
  (the indexed module never enters any `SharedState` map); the +neg isolation test mirrors
  `validate_dry_run_discards_does_not_commit` (§11.1).
- **R5 (binding):** Pillar 4 is a **new `#[cfg(feature="agent")]` sibling sink** (`log.rs` /
  the reserved `telemetry.rs` slot), NOT an extension of `trace.rs` (§11.6).
- **R6 (binding):** Type-signature match — **MVP = name-fragment + exact-structural-shape**;
  unification/subsumption (Hoogle-style) is a `/typecheck`-owned follow-up; the query-pattern
  *syntax* (holes/wildcards) is a `/spec` consult (§11.4).
- **R7 (binding):** `/syntax` content = `/docs` (`/spec` validates), UX = `/repl`, wiring =
  `/dev (src/)`; the cheat-sheet is a static `include_str!` asset, NOT primer-baked idioms;
  prelude/stdlib stays harvest-sourced (§11.7, honouring `agent-prelude-awareness-via-harvest-not-primer`).
- **R8 (binding):** Pillar-3 exact-shape match predicate `signature_matches_exact(&Type, &Type) -> bool`
  **exports from `cranelisp-typecheck` (Option A)**, not inlined int-side — type equivalence is
  typecheck's semantics (Principle 17 + 7). One additive `cranelisp-typecheck/public-api.txt` line at
  Pillar-3 *implementation* time (next sprint), per the baseline-diff discipline; does NOT move §11.8's
  S90 "zero impact" claim (Pillar 3 is design-only in S90). See §11.8 end (the export ruling).

---

### Key file/line citations
- Dispatch seam: `src/main.rs:240-306`; `src/repl.rs:419/428/433/450`.
- **Validator dry-run / discard substrate (Pillar-3 indexer reuses):** `src/worker.rs:308`
  (`validate_forms_dry_run` — throwaway staging, never commits); `src/agent/pull.rs:668`
  (`validate_one_form`, eval-thread, no `catch_unwind`); `src/agent/pull.rs:1088`
  (`validate_dry_run_discards_does_not_commit` — the zero-residue guard shape).
- **0432 panic site + containment:** `crates/cranelisp-typecheck/src/traits/monomorphise.rs:1016`
  (`debug_assert!` — live in debug/agent builds); `src/worker.rs:1483` (the pool-worker
  `catch_unwind` pattern the eval-thread path must mirror).
- **Harvest sig-grain (Pillar 2):** `src/agent/harvest.rs` (`harvest_context`, the export-surface arm).
- **Pillar-4 sibling-sink reference:** `src/agent/trace.rs` (ephemeral, env-gated — the contrast).
- Tools-as-strings (pull surface): `src/repl.rs` `handle_*` (all return `String`); `describe_symbol` `:300`.
- Eval/validate re-entry: `src/eval.rs:72/78`; `:447` (the bare-atom self-documentation gate §5.3 must preserve); cluster-atomic staging (commit-on-Ok/discard-on-Err) — the validator substrate (§6.2).
- Self-documentation contract not to regress: `repl/spec.md` §4.
- Feature-gating precedent: `design/arch/release-llvm-backend.md` §5.
- Cadence/window model: `design/arch/overview.md`.
- `/learn`: `design/arch/fixmes/0052-*.md`.
