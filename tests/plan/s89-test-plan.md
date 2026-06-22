# Sprint 89 — `/qa` Failing-Test Plan (Phase 3 Design)

Owned by `/qa`. Authored Phase 3 (Design). **PLAN ONLY** — the `.rs` test files
land Phase 5 Stage 1 (serially; source-editing is one-agent-at-a-time on this
project). This doc asserts what Phase 5 writes; it does not write it.

**Scope.** S89 delivers rungs 5–6 of the agentic-REPL ladder behind the default-off
`agent` feature, plus a live-use agent-output-rendering cluster. Three clusters
(`sprints/SPRINT.md`): **A** — agent output rendering (incl. one DEFECT); **B** —
Rung 5 Build mode + pre-flight validator; **C** — Rung 6 Document mode. Carries:
**0429** (close + delete, `target: /qa`), **0423** (delete, `target: /int`).

**Provenance.**
- `sprints/SPRINT.md` §"Agent output rendering", §"Rung 5 — Build mode", §"Rung 6 —
  Document mode", the Phase-2 /arch review (R1–R4), and the transcribed `/design (src/)`
  plan + `[Phase-5 verify]` acceptance.
- `design/int/agent.md §14` (Cluster A render + §14.6 the ANSI-leak DEFECT), §15 (Build
  write arm, §15.4 read-only floor +neg), §16 (validator + §16.5 broken-then-fixed
  stub), §17 (Document mode, §17.3 round-trip / §17.4 harvester read-back), §18 (the
  zero-movement gate), §19 (testability seams owed from `/dev`).
- `tests/plan/agent-testing-strategy.md` — the **durable** 4-lane strategy + the
  deterministic stub `AgentModel`. This S89 plan slots its rows into Lanes A/B/D
  defined there; §3.4 (validator), §3.5 (preamble round-trip), §6 (golden transcript).
- `repl/spec.md §17` (agent experience), `spec/08-modules.md §8.16` (module preamble).

**Authority order.** Where this `/qa` plan drifts from `repl-embedded-agent.md`, the
/arch Phase-2 verdict, or `design/int/agent.md`, those win — file FIXME `target: /arch`
(cross-crate) or `target: /design` (per-crate gap). None anticipated (R4: zero baseline
movement, zero `cranelisp-types` change, no cache bump).

**Baseline at S89 open (SPRINT.md).** default `cargo nextest run` **1516/1516, 0
intentional reds**; `--features agent` **33/33 lib + 23/23 e2e**; default build provably
agent-free (no rig/tokio in the dep tree). A genuine regression is any RED beyond the
named guards this plan adds. The **byte-identical-when-feature-OFF** invariant is
load-bearing and must survive this sprint (Lane B, §4 below).

---

## Lane mechanics (recap from `agent-testing-strategy.md §2`)

- **Lane A** — deterministic plumbing, `--features agent` + stub `AgentModel`, in a
  SEPARATE `--features agent` nextest invocation (not the ~9s default). Tests live in
  `tests/agent.rs`, gated `#![cfg(feature = "agent")]` at the top so the whole file
  compiles out by default. E2e where behaviour surfaces through the binary's I/O; the
  residual request-content assertions are `/dev`-owned unit tests in `src/agent/` (§1.1).
- **Lane B** — feature-OFF byte-identical guard, default build (no `agent` feature),
  in the default ~9s suite. The whole agent lane stays out of it.
- **Lane D** — golden-transcript replay, Lane-A-family (`--features agent` + stub).
- Stub injection: prefer (a) **stub-provider-by-config** (`CRANELISP_AGENT_STUB_SCRIPT=<fixture>`,
  the line DSL `tool: <name> <arg>` / `done: <prose>` per `src/CLAUDE.md`), so Lane A is
  genuine e2e. Request-content assertions that cannot surface through the binary's I/O are
  the legitimate `/dev`-owned unit-tier cases (§1.1(b)).
- Every agent test carries `// spec: repl/spec.md §17…` and/or `spec/08-modules.md §8.16`.
  Run `python3 tests/plan/spec_link_check.py --scope agent.rs` before committing.

---

## Cluster A — agent output rendering (§14)

`repl/spec.md §17` (agent frame). All Lane A (`--features agent`) except where a Lane-D
golden pins the rendered shape. Render lives **inside** `src/agent/render.rs`, fully
`#[cfg(feature="agent")]` (R1) — never a default-build render path.

### A.1 The ANSI-escape-leak DEFECT — narrow failing-not-ignored repro (§14.6) — RED-FIRST

**This is the owed defect repro (CLAUDE.md §Testing — failing-not-ignored before closure).**
Today the pretty-printer, when rendering agent output, leaks ANSI colour codes as **literal
text** (`\x1b[36m…`) instead of rendering. Root cause (hypothesis §14.6(a)): styled text
produced once is re-routed through a second formatting pass — the classic double-styling /
mis-routing; the fix is "style once at the leaf, honour the one global `is_color_enabled()`
gate, never re-style" (R2: **no** color-mode / writer-target param on `pretty_print` or any
`cranelisp-types` printer — adding one is Principle-8 interim machinery for a wiring bug).

| Test (behaviour) | Lane | Asserts (RED-first → green on fix) | Spec |
|---|---|---|---|
| `agent_output_no_literal_ansi_escape_when_color_off_neg` | A | drive an `/ask` whose scripted `done:` prose contains a ```` ```lisp ```` fence; with colour OFF (`--no-color`) the rendered transcript contains **NO** literal `\x1b[`-style escape substring anywhere (the +neg absence guard) | `repl/spec.md §17`, §10.3 |
| `agent_output_lisp_fence_pretty_printed_styled` | A | the fenced ```` ```lisp ```` form is routed through the existing S24 `pretty::pretty_print_str` and rendered as a correctly-styled, indented Lisp form (positive: the form is pretty-printed, not emitted as a raw fence) — with colour ON the SGR is **well-formed** (no orphan/literal `\x1b` bytes) | `repl/spec.md §17`, §14.5 |

The first row is the load-bearing **failing-not-ignored** defect guard — it is RED on
HEAD (literal escape codes leak) and flips green when `/dev` lands the leaf-styling fix in
the SAME change-set with its mandatory unit test (`render_agent_prose` output over a
```lisp fence contains no literal `\x1b` when colour off / well-formed SGR when on, §14.6).
Keep the repro narrow: a single `/ask` turn, one scripted `done:` prose carrying one
```lisp fence, no harvest setup beyond the minimum.

### A.2 Rendering improvements (positive — RED-first, green when §14 lands)

| Test (behaviour) | Lane | Asserts | Spec |
|---|---|---|---|
| `agent_issued_pull_shows_agent_prompt` | A | when the agent issues a pull (a command rendered as if typed), the line carries the **agent-input prompt glyph** (§14.2 — distinct from `▌` prose gutter and from the human prompt) marking it agent-issued | `repl/spec.md §17.2` |
| `agent_prose_markdown_formatted_for_terminal` | A | the agent's markdown prose (heading / list / emphasis / inline-code) renders **formatted** for the terminal within the §10.3 agent-prose frame, NOT raw markdown source | `repl/spec.md §17`, §10.3 |
| `agent_prose_markdown_no_color_clean_neg` | A | under `--no-color` the same markdown degrades cleanly — formatted layout without SGR, and **no** literal escape codes (the `styled()` short-circuit; ties A.1's absence guard to the markdown leaf) | `repl/spec.md §10.3` |
| `agent_session_render_golden_transcript` | D | a full `/ask` session (scripted prose + a ```lisp fence + an agent-issued pull) replays byte-for-byte against a golden transcript: agent prose framed in `▌`, the pull echoed unframed with the agent prompt glyph, the fence pretty-printed — pins the whole rendered shape | `repl/spec.md §17.2`, §15 |

The Lane-D golden is the whole-session render guard (frame-vs-command rendering, the agent
prompt glyph, fence pretty-print) — a single drift in any of them flips it red. Fixture under
`tests/fixtures/agent/`; `.runs/` gitignored.

---

## Cluster B — Build mode + pre-flight validator (§15/§16)

`repl/spec.md §17.3`. Lane A (`--features agent` + stub `AgentModel`). The submitted form
re-enters via the existing `process_commands`/`eval` cluster-atomic staging path (R3 — no
new eval entry); the validator reuses the `check_forms` discard-on-Err arm (§16.1).

### B.1 The stage→check→discard repair loop — broken-then-fixed (§16.5) — Lane A

The keystone Build test. A stub `AgentModel` is scripted **broken-then-fixed**: turn 1
returns a `submit`/`done` whose form fails `validate_forms_dry_run` (parse OR type — U5
silent-repair-anything, no error-classification branch); a later scripted turn returns clean
code that passes. The validator stages → checks → **discards** the broken stage (never
commits), feeds the actual compiler error back to the model silently, and re-prompts; the
second completion compiles and (on confirm) submits.

| Test (behaviour) | Asserts | As-authored status |
|---|---|---|
| `agent_build_broken_then_fixed_repaired_silently` | the loop stages→checks→**discards** the turn-1 broken form, re-prompts; the turn-2 clean form reaches the confirm gate (answered `y`) + submits — only the clean form's `(defn …)` lands: (i) **no compiler error** reaches the transcript (U5 silent), (ii) the fixed form **binds** — `(double 5)` evals to `10`, (iii) `double` is not reported unbound after the write | **RED** (write arm + validator absent; `submit` currently refused) |
| `agent_build_broken_intermediate_never_shown_neg` | **+neg (U5 silent contract):** the broken form's compiler diagnostic (`parse error`/`unbalanced`/`unexpected`) is **absent** from the rendered transcript — "the user structurally cannot see an agent compile failure" (rendering happens only after `validate_and_repair` returns `Ok(clean_form)`); the agent's terminal prose still frames | **PASS today** (standing +neg floor guard — broken form never echoed while `submit` is refused; must **continue** holding once the write arm lands) |

These are RED-first / standing-floor (the §15/§16 write arm + validator do not exist yet —
`submit` is refused at `synthesize_command` today, so the keystone is RED and the silent
+neg passes by the floor). They flip-and-hold when `/dev` lands rung 5.
`// spec: repl/spec.md §17.14.3` (silent validator), `§17.14.2` (accept/decline).

**The broken-then-fixed stub-script DSL — the contract `/dev` 2d MUST implement (verbatim).**
The existing stub-script DSL is one scripted MODEL turn-response per line, consumed in order,
one per `AgentModel::complete()` call (`tool: <name> <arg>` / `done: <prose>` / `prose:
<cont>`). Cluster B extends it with **exactly one new tool name — `submit`** (the Build write
tool, §15.1), in the SAME `tool:` form:

```text
tool: submit <FORM>   → a `submit` ToolCalls response carrying <FORM> (rest of the
                        line, verbatim) as the form string to validate→confirm→submit.
```

A **broken-then-fixed** repair sequence is expressed as **TWO consecutive `tool: submit`
lines — NO new keyword.** The repair loop (§16.2) consumes scripted responses in sequence
exactly as the model↔tool loop does: the FIRST `tool: submit` carries code that FAILS
`validate_forms_dry_run` (parse OR type — U5); the validator stages→checks→**discards** it,
feeds the compiler error back silently, re-prompts; the stub's NEXT scripted response (the
SECOND `tool: submit`) carries CLEAN code. The Nth `tool: submit` is the Nth repair attempt;
the first that validates clean reaches the confirm gate.

Canonical broken-then-fixed script (verbatim — the `BROKEN_THEN_FIXED_SUBMIT` const in
`tests/agent.rs`):

```text
tool: submit (defn double [x] (add-i64 x x)
tool: submit (defn double [x] (add-i64 x x))
done: defined double for you
```

Line 1 is parse-broken (unbalanced paren → repair). Line 2 is the clean repaired form
(reaches the confirm gate → submits). Line 3 is the terminal prose after the write. Minimal +
consistent with the existing `tool:`/`done:` DSL — `submit` is just a tool name; the
broken-then-fixed sequence is just two scripted turn-responses in order. **`/dev` 2d must
implement EXACTLY this format** (the stub parses `tool: submit <FORM>` into a `submit`
tool-call, and consecutive `tool: submit` lines feed the repair loop in order).

### B.2 Read-only floor +neg — unconfirmed / non-read tool never reaches `eval` (§15.4) — Lane A

The consent boundary (R3 structural floor). Two negative guards:

| Test (behaviour) | Asserts (ABSENCE) | As-authored status |
|---|---|---|
| `agent_build_declined_submit_no_change_neg` | a `submit` whose confirm-gate is **declined** (`n`) mutates nothing — the proposed name (`declinee`) stays unbound (`(declinee 1)` → unbound), structurally identical to the §17.3.1 "proposed, not submitted" floor | **PASS today** (standing floor — `submit` refused, so `declinee` never binds; must continue holding once the write arm + decline path land) |
| `agent_build_non_read_tool_still_refused_neg` | a non-read, non-`submit` tool (`/sh`) is **refused at `synthesize_command`** exactly as in the S88 read-only MVP — the read `ALLOWLIST` floor is unchanged, the write is structurally unconstructable WITHOUT any confirm gate (`pwned` never executes) | **PASS today** (the S88 structural floor — the rung-5 write arm must NOT regress it) |

The second row proves the floor was **extended, not loosened** (§15.4): the only new write
path is the confirm-gated `submit`; everything else still hits the read-only refusal. Both
are the rung-5 equivalent of the S88 `agent_pull_read_only_in_advise_mode_neg` guard —
standing floor guards that hold today and MUST continue holding when the write arm lands.
`// spec: repl/spec.md §17.14.2` (decline), `§17.14` (floor §15.4).

### B.3 0429 close — rig wire-path rig-trait-level mock (Lane A)

0429's step-1 deliverable (the rig wire-path BELOW the `AgentModel` membrane has no automated
test). Implement `rig_core::completion::CompletionModel` with canned response + canned
tool-call, inject as the provider, assert deterministically (no network): `request.rs` builds
the rig request from an `AgentRequest` (primer + harvest + transcript + user turn present);
`provider.rs` maps rig response → `ModelResponse::Done` and tool-calls → `ModelResponse::ToolCalls`;
the `block_on` bridge returns without nested-runtime panic.

| Test (behaviour) | Lane | Asserts |
|---|---|---|
| `rig_model_maps_done_response` | A | rig canned text response → `ModelResponse::Done(prose)`; the `block_on` bridge returns cleanly |
| `rig_model_maps_tool_calls_response` | A | rig canned tool-call response → `ModelResponse::ToolCalls(…)` mapped correctly |
| `rig_request_built_from_agent_request` | A (likely `/dev`-owned unit-tier §1.1(b)) | the rig `CompletionRequest` carries the system primer + harvested context + transcript + user turn (request-content assertion — may not surface e2e; if not, `/dev` unit test in `src/agent/`) |

These are the **rig-trait-level** mock (distinct from the `AgentModel` stub) — they test the
membrane's underside. Per the 0429 §1 correction now applied to `agent-testing-strategy.md §1`.
On these landing green, **0429 is fully met → `/qa` deletes `design/arch/fixmes/0429-*.md`**
with a commit naming the resolution (deletion owed this sprint).

### B.4 `--yes` validation-floor (CRITICAL — `/arch §7.4` / `agent.md §20.3`) — Lane A

The safety-critical `--yes` guard: `--yes` skips **consent**, NEVER **validation**. With
`--yes` ON, the broken-then-fixed sequence (the `BROKEN_THEN_FIXED_SUBMIT` script + the
`--yes` flag) MUST still silently repair — only the clean form commits — AND **no `[y/N]`
prompt** fires (auto-accepted). A `--yes` that skipped the validator would submit the raw
broken form and `double` would never bind (the conflation defect §20.3 names). Note: NO `y`
line is piped — `--yes` auto-accepts, so the binding is asserted via `(double 5)`.

| Test (behaviour) | Asserts | As-authored status |
|---|---|---|
| `agent_build_yes_validation_floor_still_repairs` | (a) the broken intermediate is STILL silently repaired under `--yes` — **no compiler error** surfaces; (b) only the CLEAN form commits — `(double 5)` evals to `10` (a raw-broken submit would leave `double` unbound); (c) **no `[y/N]` prompt** — consent auto-accepted (§17.14.5) | **RED** (`--yes` threading + §20.3 placement absent) |

`// spec: repl/spec.md §17.14.6` (validation floor under `--yes`), `§17.14.5` (auto-accept),
`§0.6.2`.

### B.5 `--yes` accepted-no-op — default build / `--no-agent` (3a)

`--yes`/`-y` is an **accepted no-op** when no agent is active: never `unknown flag`, the
session evals exactly as today (§20.1, identical to `--agent`). The **default-build half is a
DEFAULT-lane test** (NOT `#[cfg(feature="agent")]`); the `--no-agent` half is agent-lane.

| Test (behaviour) | Lane | Asserts | As-authored status |
|---|---|---|---|
| `yes_flag_accepted_no_op_default_build` | **DEFAULT** | `--yes` on a default (non-`agent`) build → accepted (no `unknown flag`), session evals `3` | **RED** (default build errors `unknown flag: --yes` today) |
| `y_short_flag_accepted_no_op_default_build` | **DEFAULT** | `-y` (short form) on a default build → parsed as a **FLAG**, not swallowed as the REPL target (no `-y>` target prompt) — the +neg guard against today's `_ =>` arm capturing `-y` as a target | **RED** (today `-y` is swallowed as the REPL target → `-y>` prompt) |
| `agent_yes_with_no_agent_is_accepted_no_op` | A | `--no-agent --yes` (agent build, agent disabled) → `--yes` accepted/inert, session evals `3` | **RED** (`--yes` unknown even in the agent build today) |

`// spec: repl/spec.md §0.6.2`. The `-y`-not-swallowed-as-target row is the load-bearing
+neg: a flag that parses as `unknown flag`-free but lands as a target is a **false-green** the
naïve assertion would miss — pinned via the `-y>` target-prompt absence.

---

## Cluster C — Document mode (§17)

`spec/08-modules.md §8.16` (module preamble) + `repl/spec.md §17.5`. Lane A. Reuses the S88
`module_preamble` substrate + byte-stable regen (R4: no `cranelisp-types` change, no cache bump).

### C.1 Write → save → reload → harvester-read-back round-trip (§17.3/§17.4) — Lane A

The closing memory loop ("memory is the code"). A stub `AgentModel` scripts a `set-preamble`
tool-call + a confirm; the agent writes a module preamble; it round-trips byte-identically;
a fresh session's harvester reads it back into context.

| Test (behaviour) | Asserts |
|---|---|
| `agent_document_preamble_edit_round_trips_byte_stable` | the Document edit (`apply_preamble_edit` + section-0 regen) writes the preamble; a subsequent `/doc <module>` reads it back; it persists **byte-identically** across the module's backing-file regen (the §8.16.5 byte-stable round-trip — leading comment block identical before/after, no reflow) |
| `agent_document_harvester_reads_edited_preamble_back` | after the Document-mode edit, a **fresh session** loads the regenerated `.cl`, `apply_module_preamble` captures the section-0 block, and the next turn's harvest carries the new preamble text into the request (rung 6 write → rung 3 read, no new harvest code) |

RED-first (rung 6 edit arm does not exist yet). `// spec: spec/08-modules.md §8.16`,
`§8.16.5`; `repl/spec.md §17.5`.

---

## Cluster B/C consent +neg — confirm-gate declines path

The confirm/consultative gate's decline path makes no change. (B.2's `agent_build_unconfirmed_submit_never_evals_neg`
covers the Build decline; this is the Document twin.)

| Test (behaviour) | Lane | Asserts |
|---|---|---|
| `agent_document_declined_preamble_edit_no_change_neg` | A | a `set-preamble` edit whose **consultative** gate is declined writes nothing — the module's preamble (and its backing file) are byte-identical to the pre-edit state, no regen fires | `repl/spec.md §17.5`, §17.2 |

The Build confirm and the Document consultative gate are discriminated by **tool name** (§17.2);
both decline paths are no-ops on session state.

---

## Lane B — feature-OFF / byte-identical guard (the default suite)

The standing guard: with the `agent` feature OFF the binary is **byte-identical to today** on
every non-`/ask` input, the workspace compiles **without rig in the dep tree**, and the ~9s
budget is preserved (§18, the /arch zero-movement gate). These run in the DEFAULT
`cargo nextest run`. The S88 Lane-B family already exists; S89 adds no new feature surface that
changes feature-OFF behaviour, so the guard is **re-affirmed**, not re-authored — verify at
close that:

| Test (behaviour) | Build | Asserts |
|---|---|---|
| `agent_off_ask_prints_not_built_in` (S88, re-verify) | default | `/ask why` → "agent not built in (rebuild with --features agent)"; non-`/ask` input byte-identical to today |
| `agent_off_dispatch_byte_identical` (S88, re-verify) | default | `(foo bar baz` (other parse error) → today's byte-identical parse-error display (the `Err(other)` fallback) |
| default suite stays agent-free (build guard) | default | the default workspace compiles + the ~9s suite passes **without rig/tokio** as a dependency — a regression that pulled `rig-core` into the default build (e.g. a dev-dep enabling `agent`) breaks the budget and is caught here |

**S89 watch-item (R1):** the new Cluster-A render (`render.rs`) + rung-5/6 code MUST ride the
existing four `#[cfg(feature="agent")]` cuts. If any of it leaks into a default-build render
path, Lane B (and the ~9s budget) catches it. The whole agent lane stays behind
`#[cfg(feature="agent")]` — `tests/agent.rs` compiles out by default.

---

## Carries

- **0429 — close + delete (`target: /qa`).** Substantially met in S88 (the rig-trait
  continuation-pairing test landed). S89 residual, all owed **this sprint**:
  1. ✅ **DONE this phase** — the one-line `tests/plan/agent-testing-strategy.md §1`
     correction (the stub implements **`AgentModel`**, not rig's `CompletionModel` directly).
     Applied Phase 3.
  2. The rig-trait-level mock tests (B.3 above) land Phase 5.
  3. On B.3 green, **`/qa` deletes `design/arch/fixmes/0429-qa-rig-wire-path-untested-add-rig-trait-mock.md`**
     with a commit naming the resolution. (The user-owed one-time Lane-C smoke is eval-lane,
     not CI — not a `/qa` blocker.)
- **0423 — delete (`target: /int`).** Fixed S88 W1b; the fix + green test
  (`spec_08_modules.rs::inline_mod_test_extraction_writes_lib_dir_relative_not_cwd`, now green)
  are the durable record. **`/int` deletes the FIXME file** — bookkeeping only, NOT a `/qa`
  action. Noted here for visibility.

---

## Phase-5 exit condition (RED-first → green)

Phase 5 Stage 1 writes the `.rs` tests below RED-first; the per-cluster `/dev` (int, narrow)
work flips each green in the same change-set with its mandatory unit test.

- **RED-first then green** (won't-compile / wrong-result until rung 5/6 + render land):
  all Cluster A (A.1 + A.2), Cluster B (B.1 + B.2 + B.3), Cluster C (C.1), the B/C
  decline-path +neg.
- **The ANSI-leak repro (`agent_output_no_literal_ansi_escape_when_color_off_neg`, A.1) is
  failing-not-ignored** — RED on HEAD against today's leaking render, flips green with the
  §14.6 leaf-styling fix. This is the owed defect guard (CLAUDE.md §Testing: a defect is not
  closed until `/qa` has a narrow failing-not-ignored repro).
- **Lane B re-verified green** in the default suite at close (feature-OFF byte-identical, no
  rig in the dep tree, ~9s budget intact) — the §18 zero-movement gate.
- **Gate (§18 checkable):** zero `public-api.txt` movement, no `cranelisp-types` change, no
  `CACHE_SCHEMA_VERSION` bump. If Phase 5 surfaces a boundary-type need → file `target: /arch`
  (none anticipated, R4).

---

## Testability seams required from `/dev` (§19)

Lane A cannot be authored deterministically without these int-internal hooks. Flagged to
`/sprint` at the Phase-3 exit gate (`agent.md §19`); `/dev` exposes them in Phase 5:

1. **Broken-then-fixed stub-script DSL extension (§16.5).** The stub `AgentModel` script DSL
   (`CRANELISP_AGENT_STUB_SCRIPT` line DSL — `tool: <name> <arg>` / `done: <prose>`, `src/CLAUDE.md`)
   must express a **broken-then-fixed** sequence: turn-1 `submit`/`done` whose form fails
   `validate_forms_dry_run`, a later turn returning clean code. Without this the repair-loop
   tests (B.1) cannot be driven deterministically.
2. **A hook to drive the validator repair loop observably.** The stage→check→discard loop +
   silent-repair must be drivable by the stub through `run_submit`/`agent_turn` via the
   `AgentModel` membrane (zero network), AND the test must be able to assert the broken
   intermediate is **absent** from the rendered transcript (B.1 +neg). If the silent
   repair-turn record cannot be distinguished from the rendered transcript through the binary's
   I/O, that is a testability gap → file `target: /int` (a transcript / assembled-request echo
   hook) per `tests/CLAUDE.md §"Two tiers, no middle"`, NOT an internal-API bridge.
3. **Stub-provider-by-config for Lane A e2e (§1.1(a)).** Prefer the `CRANELISP_AGENT_STUB_SCRIPT`
   config path so Lane A is genuine e2e. Request-content assertions (B.3 `rig_request_built…`,
   harvest selection) that genuinely cannot surface through the binary's I/O are the legitimate
   `/dev`-owned unit-tier cases in `src/agent/`.
4. **`tests/agent.rs` + `tests/fixtures/agent/`** + the `--features agent` nextest lane (and its
   `.runs/` gitignore entry) — Wave-setup carried from S88; extended for the broken-then-fixed
   and golden-transcript fixtures.

---

## Ledger note (for `/qa` to fold into `ledger.md` at close)

- Cluster A: ANSI-leak narrow failing-not-ignored repro
  (`agent_output_no_literal_ansi_escape_when_color_off_neg`) — RED-first, owner `/dev` (int,
  §14.6 leaf-styling wiring), target S89.
- Cluster B: stage→check→discard repair loop (B.1) + read-only floor +neg (B.2) + 0429
  rig-trait mock (B.3) — RED-first, owner `/dev` (int, rung 5 + rig wire-path), target S89.
- Cluster C: Document round-trip + harvester read-back (C.1) + decline +neg — RED-first,
  owner `/dev` (int, rung 6), target S89.
- 0429: closed when B.3 green; `/qa` deletes the FIXME file. 0423: `/int` deletes (bookkeeping).
- Lane B re-verified green at close (feature-OFF byte-identical; no rig in default dep tree).
