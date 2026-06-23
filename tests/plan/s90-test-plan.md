# Sprint 90 — `/qa` Failing-Test Plan (Phase 3 Design)

Owned by `/qa`. Authored Phase 3 (DESIGN). **PLAN ONLY** — the `.rs` test files
land Phase 5 (serially; source-editing is one-agent-at-a-time on this project).
This doc asserts what Phase 5 writes; it does not write it.

**Scope.** S90 delivers the **fluency / "reach" half of rung 7** behind the
default-off `agent` feature, plus a passive telemetry log. Four pillars
(`sprints/SPRINT.md §Scope`): **P1** `/syntax` cheat-sheet command, **P2**
harvest at signature grain, **P3** importable-symbol search (DESIGN-ONLY this
sprint — R1), **P4** silent greppable agent log. Plus **0432** (pulled in, R2) —
the multi-clause-`defn`-self-call defect, with a two-layer containment floor.

Each row below is marked **SHIPS-THIS-SPRINT** (RED-first → `/dev` flips green in
the same change-set) vs **DESIGN-PINNED** (plan now; the `.rs` test is authored at
Pillar-3 implementation, this sprint only if 0432's root fix + the `catch_unwind`
floor land early enough to pull P3 forward — §11.5).

**Provenance.**
- `sprints/SPRINT.md` §Scope (four pillars), §"Architecture review (Phase 2)"
  (verdict + R1–R7), §"FIXME debt" (0432 pulled in).
- `design/arch/repl-embedded-agent.md §11` (commit `ca9d5fb`/`ca9d5fb`-line) —
  §11.1 Pillar-3 seam (sibling of `validate_forms_dry_run`, structural zero
  residue), §11.2 one-DTO-two-feeders, §11.3 two-layer containment (0432 root fix
  + eval-thread `catch_unwind`), §11.4 match semantics, §11.5 split sizing, §11.6
  Pillar-4 sibling sink, §11.7 `/syntax` ownership, §11.8 zero public-API impact.
- `repl/spec.md §17.17` (`/syntax`), §17.18 (harvest sig-grain), §17.19
  (`/lib-search` — design-pinned), §17.20 (`CRANELISP_AGENT_LOG`).
- `user/syntax-cheatsheet-plan.md` (cheat-sheet asset `src/syntax/cheatsheet.txt`,
  the `=== topic: <name> ===` delimiter, verified-compiling discipline, the
  flagged primer/spec `match`-shape contradiction §4).
- `design/typecheck/monomorphisation.md §9` (0432 Face-B root fix — the
  `monomorphise_call` P1 concreteness gate, panic→clean-error) +
  `design/typecheck/signature-match.md` (the exact-shape / alpha-equivalence match
  predicate).
- `design/arch/fixmes/0432-multi-clause-defn-self-call-codegen.md` (the defect,
  two faces).
- `tests/plan/agent-testing-strategy.md` — the durable 4-lane strategy + the
  deterministic stub `AgentModel`; `tests/agent.rs` — the existing lane + DSL.

**Authority order.** Where this `/qa` plan drifts from `repl-embedded-agent.md §11`,
the /arch Phase-2 verdict, `design/typecheck/{monomorphisation,signature-match}.md`,
or `repl/spec.md §17`, those win — file FIXME `target: /arch` (cross-crate) or
`target: /design` (per-crate gap). None anticipated (R-set: zero baseline movement,
zero `cranelisp-types` change, no cache bump — §11.8).

**Baseline at S90 open (SPRINT.md).** default `cargo nextest run` **1520/1520, 0
intentional reds**; `--features agent` **82 lib + 42 e2e**; default build provably
agent-free (no rig/tokio in the dep tree). A genuine regression is any RED beyond
the named guards this plan adds. The **byte-identical-when-feature-OFF** invariant
is load-bearing and must survive (Lane B, §"Pillar 4" below + §"Feature-OFF").

---

## Lane mechanics (recap from `agent-testing-strategy.md §2`)

- **Lane A** — deterministic plumbing, `--features agent` + stub `AgentModel`, in a
  SEPARATE `--features agent` nextest invocation (not the ~9s default). Tests live
  in `tests/agent.rs`, gated `#![cfg(feature = "agent")]` at the top so the file
  compiles out by default. E2e where behaviour surfaces through the binary's I/O.
- **Lane B** — feature-OFF byte-identical guard, default build (no `agent`
  feature), in the default ~9s suite. The agent surface stays out of it.
- **Lane C** — model-quality eval, real provider, NOT CI (out of S90 plan scope
  except the grounding-regression note in §"Pillar 2").
- **Lane D** — golden-transcript replay, Lane-A-family (`--features agent` + stub).
- **Stub injection** — the §1.1(a) **stub-provider-by-config** mechanism, already
  in `tests/agent.rs`: `stub_repl(script, prelude, stdin)` writes a script fixture,
  sets `CRANELISP_AGENT_PROVIDER=stub` + `CRANELISP_AGENT_STUB_SCRIPT=<path>`, adds
  `--agent`, drives the real binary. Script DSL (one scripted turn-response/line):
  - `tool: <name> <arg>` → a `ToolCalls` response → the agent synthesizes
    `/<name> <arg>` and runs it through `process_commands` (the same path a
    keystroke uses), renders it as-typed (`agent>` glyph), feeds the result back.
  - `done: <prose>` → a terminal `Done(prose)` the agent renders framed (`▌`).
  - For S90 the **new pull tools** are `syntax` and `lib-search` — same `tool:`
    form, new tool names in the read-only allowlist (§"Testability seams").
- Every agent test carries `// spec: repl/spec.md §17…` (and/or
  `spec/05-definitions.md §5.1.2` for 0432). Run
  `python3 tests/plan/spec_link_check.py --scope agent.rs` before committing.

---

## Pillar 1 — `/syntax` cheat-sheet command (SHIPS THIS SPRINT)

`repl/spec.md §17.17`; `user/syntax-cheatsheet-plan.md`. `/syntax` is **NOT
feature-gated** — it is a normal deterministic REPL command (a static asset read
off disk, the §17.17.2 `/help`/`/list` family) usable by the human on the
**default build**, AND an agent pull-tool when the agent is live (§17.17.3). The
content is `/docs`-owned (`src/syntax/cheatsheet.txt`); `/qa` guards the
**mechanism** (the command behaviour + the asset's machine contract), not the
prose accuracy (that is `/docs` verified-compiling + `/spec` validation).

**File:** `tests/repl_introspection.rs` (the deterministic-command home) for the
default-build command rows; `tests/agent.rs` (Lane A) for the agent-pull row.

| # | Test (behaviour) | Lane / build | Asserts | Spec |
|---|---|---|---|---|
| P1.1 | `syntax_bare_lists_topics` | default (no `agent`) | bare `/syntax` prints a scannable list of topic names AND a drill-in hint (`/syntax <topic>` …); not framed (`▌` absent) | §17.17.1 |
| P1.2 | `syntax_topic_returns_content` | default | `/syntax <topic>` (a known topic) prints that topic's dense block (a known marker from the block — e.g. the topic header / a `SPEC` cross-link line); content present, no opaque error | §17.17.1 |
| P1.3 | `syntax_unknown_topic_relists_no_dead_end_neg` | default | `/syntax <nonsense>` MUST NOT error opaquely — it re-prints the topic list with a "not one of them" note; the **+neg** is *no* opaque `unknown` error and *no* empty/dead-end output (the self-documenting floor) | §17.17.1 |
| P1.4 | `syntax_works_on_default_build_not_feature_gated` | default | `/syntax match` on a plain (non-`agent`) binary returns content — proves the command is NOT behind the `agent` feature (Lane-B-family build guard) | §17.17.3 |
| P1.5 | `syntax_degrades_clean_under_no_color_neg` | default | `/syntax hkt --no-color` (piped/non-TTY) carries NO literal `\x1b[` SGR escapes AND the block reads as plain-indented Lisp (mirrors the S89 §17.13.3 ANSI-leak floor) | §17.17.2 |
| P1.6 | `agent_pulls_syntax_renders_as_command` | Lane A (`--features agent`) | stub `tool: syntax hkt` → the agent synthesizes `/syntax hkt`, it renders with the `agent>` glyph and the topic content beneath, unframed; then a `done:` prose answer is framed | §17.17.3 |
| P1.7 | `cheatsheet_asset_parses_by_delimiter` | default (asset-mechanism guard) | a guard that the shipped `src/syntax/cheatsheet.txt` parses: every topic block opens with the `=== topic: <name> ===` delimiter; bare `/syntax` lists exactly the delimiter-named topics (the index never drifts from content) | §17.17.1; cheatsheet-plan §5 |
| P1.8 | `cheatsheet_sampled_example_compiles` | default | a **sampled** example pulled from one `/syntax <topic>` block evals/typechecks at the REPL without error (guards the *mechanism* that examples are compiling Lisp; full verified-compiling coverage is `/docs`' discipline, §"Match-shape verification" below) | §17.17.1; cheatsheet-plan §4 |

Notes:
- P1.7/P1.8 guard the **mechanism**, not the content: P1.7 asserts the delimiter
  contract `/dev`'s parser and `/docs`' authoring share (`=== topic: <name> ===`);
  P1.8 asserts at least one block's example is live Lisp. Exhaustive
  every-example-compiles is the `/docs` Phase-5 gate (cheatsheet-plan §4), not a
  per-example `/qa` row.
- P1.5 is the deterministic-degradation floor — `/syntax` reuses existing §10.3
  roles and introduces no new style role (§17.17.2), so the no-color clean-output
  guard reuses the S89 ANSI-leak assertion shape.

---

## Pillar 2 — harvest at signature grain (SHIPS THIS SPRINT)

`repl/spec.md §17.18`. The harvester surfaces in-scope symbols — current module's
own defns + explicit imports + implicit prelude — at **name + `:Type` signature +
docstring** grain, ambiently every turn, **without** the agent first spending a
turn on `/list`/`/imports`. This is ambient (no command, nothing extra in the
human REPL); it is observable via the `/context <path>` harvest dump (§17.11,
`=== HARVESTED CONTEXT ===`), the established observable read-back seam.

**File:** `tests/agent.rs` (Lane A). Observed through the `/context` dump in a
stub-driven session (the same mechanism C.1's read-back used in S89).

| # | Test (behaviour) | Lane / build | Asserts | Spec |
|---|---|---|---|---|
| P2.1 | `harvest_in_scope_shows_name_sig_docstring` | Lane A | a fresh session defines a docstring'd fn + imports a prelude symbol; the `/context` dump's in-scope block carries, per symbol, name + its `:Type` signature (FQ type names) + its docstring — for an own defn, a prelude symbol, and an imported symbol | §17.18.1 |
| P2.2 | `harvest_sig_is_fully_qualified_neg` | Lane A | the harvested signature uses FQ type names (e.g. `primitives/Int`) — the **+neg** is that a bare `Int` does NOT appear in a type position in the in-scope block (the §4.1 FQ-display discipline, the same negative shape as `/sig`) | §17.18.1 |
| P2.3 | `harvest_budget_degrades_grain_not_truncates_neg` | Lane A | under a tiny harvest budget the in-scope block degrades grain (sig-without-docstring, then names-only) but does NOT silently drop a symbol to a misleadingly-short list — the **+neg** is that the in-scope symbol's *name* still appears even when its detail is elided (the agent must never believe a symbol is absent) | §17.18.2 |
| P2.4 | `harvest_references_actual_sig_no_relist_needed` | Lane A | acceptance: a stub session whose first turn references an in-scope symbol's signature succeeds **without** an intervening `/list`/`/exports` pull in the transcript — the ambient grain made the pre-flight unnecessary | §17.18.2 |

Notes:
- P2.3 is the load-bearing **+neg precision guard** (mirrors the rung-3 harvest
  negative discipline, `agent-testing-strategy.md §3.2`): "ambient awareness" is
  only proven if budget pressure degrades *grain*, not *membership*. A truncated
  list that drops a symbol's name entirely is the failure this guards against.
- The budget knob (P2.3) needs an observable lever — see §"Testability seams"
  (a way to drive the harvest at a tiny `char_budget` from an e2e). If absent →
  file `target: /int`.
- Grounding-regression (Lane C, non-CI) — sig-grain harvest must not *regress*
  the real-model grounding the S89 Lane-C eval checks. Noted, not authored
  (`agent-testing-strategy.md §5`).

---

## Pillar 4 — silent greppable agent log (SHIPS THIS SPRINT)

`repl/spec.md §17.20`; `repl-embedded-agent.md §11.6` (R5). With
`CRANELISP_AGENT_LOG=<path>` set, an agent session appends one structured JSONL
record per event to that file, **silently** (nothing extra in the REPL), with
**stable greppable keys**. The log is `#[cfg(feature="agent")]`, off the default
build, and feature-OFF stays byte-identical.

**File:** `tests/agent.rs` (Lane A) for the log-content rows; the default-build
absence row is a Lane-B-family default-suite row.

| # | Test (behaviour) | Lane / build | Asserts | Spec |
|---|---|---|---|---|
| P4.1 | `agent_log_writes_jsonl_with_stable_keys` | Lane A | with `CRANELISP_AGENT_LOG=<tmp path>`, a stub session that does a pull + a `done:` writes a file; each line parses as JSON and carries the stable keys (event type; symbol when present; for a repair: error class + repair-iteration count; module) — a `grep`/`jq` one-liner shape extracts the events | §17.20.3 |
| P4.2 | `agent_log_is_silent_transcript_unchanged_neg` | Lane A | the REPL transcript with `CRANELISP_AGENT_LOG` set is **byte-identical** to the same stub session with it unset — the **+neg** is no "logging to …" banner, no per-event echo, nothing extra in stdout (the §17.20.1 silent contract; compare two `stub_repl` runs) | §17.20.1 |
| P4.3 | `agent_log_absent_on_default_build_neg` | default (no `agent`) | `CRANELISP_AGENT_LOG=<path>` on a plain (non-`agent`) binary writes **NO file** (the var is inert; the log only exists in an `--features agent` build) — the **+neg** absence guard | §17.20.2 |
| P4.4 | `agent_log_graceful_on_unwritable_path_neg` | Lane A | `CRANELISP_AGENT_LOG` set to an unwritable path (e.g. a dir, or a path under a nonexistent parent) — the session does NOT crash and spews NO error into the REPL (logging is a side channel; its failure never disturbs the session) | §17.20.2 |
| P4.5 | feature-OFF byte-identical re-verify | Lane B (default suite) | the default `cargo nextest run` stays agent-free + byte-identical with the log code added; the standing Lane-B floor (`agent-testing-strategy.md §4`) re-confirmed at S90 close | §17.9 |

Notes:
- P4.2 is the keystone silent guard: it diffs two real stub transcripts (log-on /
  log-off). The golden-transcript family (Lane D) already pins the transcript
  shape; P4.2 proves the log perturbs it by zero bytes.
- P4.1's "stable keys" assertion is the experience requirement (§17.20.3) — the
  exact key vocabulary is `/dev`-owned; the test pins that a one-line `jq`/`grep`
  reliably extracts repair events + their triggering symbol/error. Needs an
  observable repair event in the script (a broken-then-fixed `submit` from the
  S89 DSL) so a repair-class record exists to grep — see §"Testability seams".

---

## 0432 — multi-clause `defn` self-call narrow repro (PULLED IN, R2 — SHIPS THIS SPRINT)

`design/arch/fixmes/0432-multi-clause-defn-self-call-codegen.md`;
`design/typecheck/monomorphisation.md §9`; `s84-concrete-types-ambiguity-ruling`.
Per CLAUDE.md this is **mandatory** and the durable record. A multi-clause
(multi-signature) `defn` whose body cross-variant self-calls, **with params
unannotated** (Face B), today:

- **REPL path** → the monomorphiser `debug_assert!` at `monomorphise.rs:1016`
  fires *inside Pass 4* (debug build → live), the unwind escapes the eval thread →
  **PANIC** / crash.
- **`--run` path** → the `debug_assert!` is compiled out; the §4 ambiguity
  backstop catches the residual var at finalisation → a **clean ambiguous-type
  error**.

The fix (`/typecheck`, §9.3) is an early concreteness gate at `monomorphise_call`
P1, before `build_mangled_name`, returning `Err(TypeError{ "ambiguous type …" })`
so **both builds converge on the clean error** and the mangler is never reached
with a non-concrete param.

**The repro shape (the minimal Face-B form, from the FIXME / §9.1, no prelude —
primitives only so it is free-standing):**

```lisp
(defn sum-to ([n] (sum-to n 0))
             ([n acc] (if (primitives/eq-i64 n 0) acc
                          (sum-to (primitives/sub-i64 n 1) (primitives/add-i64 acc n)))))
```

Capture **BOTH faces** of the divergence, RED-first, flipping green when §9's root
fix lands (clean ambiguous-type error, REPL == `--run`, no panic):

| # | Test (behaviour) | Tier / file | Asserts (CORRECT post-fix outcome → RED today) | Spec |
|---|---|---|---|---|
| 0432.U | `multi_clause_self_call_unannotated_clean_type_error` | **unit, `crates/cranelisp-typecheck`** (`/dev`-authored; `/qa` specifies it) | the Face-B form through `check_forms`/`pass4_monomorphise` returns `Err(TypeError{ msg contains "ambiguous type" })` — **NOT a panic**. Debug-built (the panic only fires in debug), so it directly guards the divergence | §9.6; spec/05 §5.1.2 |
| 0432.E1 | `multi_clause_defn_self_call_repl_clean_error_not_panic` | e2e, `tests/spec_05_definitions.rs` (`PreludeVariant::None`) | the Face-B form via the **REPL** (`repl_capture`) prints a clean `ambiguous type … add an annotation …` error AND the session **does not crash** (no panic banner, exit clean, a following form still evals) — RED today (REPL panics) | spec/05 §5.1.2; §9.4 |
| 0432.E2 | `multi_clause_defn_self_call_run_clean_error` | e2e, `tests/spec_05_definitions.rs` (`--run`, `PreludeVariant::None`) | the same form via `--run` prints the clean ambiguous-type error (this face is GREEN-today on `--run` — it pins the convergence target the REPL face must match) | spec/05 §5.1.2; §9.4 |
| 0432.E3 | `multi_clause_defn_self_call_repl_equals_run_neg` | e2e, `tests/spec_05_definitions.rs` | **REPL and `--run` produce the IDENTICAL ambiguous-type diagnostic** (the cross-mode convergence the FIXME demands — the **+neg** is no REPL/`--run` *divergence*, neither panic nor differing message) — RED today (divergence) | §9.4 |

Notes:
- **0432.U** is the mandatory unit-per-fix guard at the exact seam (per
  CLAUDE.md). `/qa` specifies it here; `/dev (cranelisp-typecheck)` authors it in
  the crate alongside the §9.3 fix (it is a `crates/*/src` unit test, NOT
  `/qa`-owned per `tests/CLAUDE.md §"Two tiers, no middle"`). Named in this plan so
  the obligation is visible; the row is owned at write-time by `/dev`.
- The e2e rows (0432.E1–E3) ARE `/qa`-owned — they cross REPL/`--run` modes
  (the mode-divergence that warrants e2e per `tests/CLAUDE.md §"Unit-test-per-fix"`).
  They convert the existing failing-repro obligation (0432 `target: /qa →
  /typecheck`) into committed RED guards.
- **Face A is explicitly OUT of this row set** (annotated params → codegen
  `undefined function`, a backend/codegen lowering defect, §9.5). S90's pulled-in
  scope is Face B only (the panic is the robustness blocker for Pillar 3). Face A
  carries forward as a separate defect — if a Face-A repro is cheap to capture
  during reduction, it lands as its own RED row pointing `/dev (backend)`, but it
  is **not** gated to S90 close.

---

## Containment floor (R2 layer b — SHIPS THIS SPRINT)

`repl-embedded-agent.md §11.3` layer (b). The agent's eval-thread typechecks
(the S89 validator AND, when it lands, the Pillar-3 indexer) call `check_forms`
**directly on the eval thread with NO `catch_unwind`** today
(`src/agent/pull.rs:668` → `src/worker.rs:308`). A 0432-shaped (or otherwise
panic-inducing) form fed through that path unwinds the eval thread and **crashes
the REPL**. Layer (b) wraps those eval-thread typechecks in `catch_unwind`
(`pub(crate)`, int-internal, mirroring `src/worker.rs:1483`) — convert a caught
unwind to a clean `Err`, drop the throwaway staging, surface "module failed to
validate/index" rather than crashing.

This floor is **independent of the 0432 root fix** — it hardens the agent against
*any* typechecker panic over uncontrolled input, and retroactively hardens the
S89 validator. It is RED on HEAD's un-caught eval-thread typecheck and green on the
floor.

**File:** `tests/agent.rs` (Lane A).

| # | Test (behaviour) | Lane / build | Asserts | Spec |
|---|---|---|---|---|
| CF.1 | `agent_validator_malformed_form_does_not_crash_repl` | Lane A | a stub `tool: submit <0432-Face-B-shaped form>` (a model-proposed multi-clause self-call) fed through the S89 Build validator does **NOT** crash the REPL — the session surfaces a clean "could not validate" / silent-repair outcome and stays alive (a following input still evals). RED on HEAD (eval-thread typecheck panic unwinds, no catch); green on the §11.3(b) `catch_unwind` floor | §17.14.3; §11.3 |

Notes:
- CF.1 is the **floor** — it proves the catch, not the root fix. Pre-0432-root-fix
  the validator typecheck of the Face-B form panics; the catch converts that to a
  clean Err and the REPL survives. Post-root-fix the same form yields a clean type
  error *without even reaching the panic* — but the catch must still be present
  (defence-in-depth for the *next* uncontrolled-input panic, e.g. a Face-A or
  future shape). Both 0432.U/E and CF.1 land; they guard different seams
  (root-cause vs. floor) — §9.6 "containment interaction".
- CF.1 uses the S89 `tool: submit` DSL (the broken-then-fixed write tool); here the
  "broken" form is the panic-inducing 0432 shape rather than a parse error. Needs
  the validator-repair-loop observable through the transcript (it already is, per
  S89 §16.5) — and ideally a hook to observe the catch fired (a "could not
  validate" surfacing) — see §"Testability seams".

---

## Pillar 3 — importable-symbol search + `/lib-search` + match (DESIGN-PINNED)

`repl/spec.md §17.19`; `repl-embedded-agent.md §11.1–§11.4`;
`design/typecheck/signature-match.md`. **DESIGN-ONLY this sprint** (R1). These
rows are PLANNED now and the `.rs` tests are **authored at Pillar-3
implementation** — this sprint only if 0432's root fix + the CF.1 `catch_unwind`
floor land early enough to pull P3 forward (§11.5); otherwise next sprint. They
carry the `[S90 — design only]` / authored-at-implementation marker and are NOT
written failing this phase (per `qa.md §"Failing-not-ignored"`: scheduled-but-not-
yet-active → plan row, do not write the test yet).

**File (at implementation):** `tests/agent.rs` (Lane A) for the agent-pull +
zero-residue rows; `tests/repl_introspection.rs` for the human-command rows; the
match-predicate unit rows are `/dev`-owned in `crates/cranelisp-typecheck`.

| # | Test (behaviour) | Tier / when | Asserts | Spec |
|---|---|---|---|---|
| P3.1 | `lib_search_name_fragment_lists_import_form` | e2e, at-impl | `/lib-search grid` over a fixture with reachable-but-unimported `grid-get`/`grid-set` lists each: name + `:Type` sig (FQ) + originating module + the exact `(import …)` form | §17.19.1, §17.19.2 |
| P3.2 | `lib_search_exact_shape_signature_matches` | e2e, at-impl | `/lib-search (Fn [Int Int] Int)` returns symbols of exactly that shape (up to alpha-renaming) and their import forms | §17.19.1; signature-match §2 |
| P3.3 | `lib_search_no_match_reprompts_no_dead_end_neg` | e2e, at-impl | an empty/no-match query re-prompts with a short "no importable symbols matched" note — **+neg** no opaque error | §17.19.1 |
| P3.4 | `lib_search_index_zero_residue_neg` | e2e, at-impl | **the keystone +neg (R4)** — after a `/lib-search` over a reachable module, the session's `symbol_tables` / `module_aliases` / `prelude_fallback` / introspection are **unchanged** (the indexed module was never `register_module`'d): a subsequent reference to the searched module's symbol is still **unbound**, and `/list`/`/imports` do NOT show it. Mirrors the existing `validate_dry_run_discards_does_not_commit` guard (§11.1) | §11.1; §11.8 |
| P3.5 | `lib_search_agent_pull_renders_as_command` | Lane A, at-impl | stub `tool: lib-search grid` → the agent synthesizes `/lib-search grid` (the `agent>` glyph) and the result renders unframed; the agent can then propose the import via Build (§17.14) | §17.19.3 |
| P3.6 | `lib_search_0432_shaped_module_does_not_crash_neg` | e2e, at-impl | **the containment +neg (§17.19.4)** — a 0432-shaped (or otherwise un-typecheckable) module on the search path, when searched, surfaces a graceful "could not index <module>" search-quality note and is simply absent from results — never an unwound eval thread, panic, or lost session. This is CF.1's floor exercised through the indexer (the broader trigger surface §11.3 flags) | §17.19.4; §11.3 |
| P3.7 | `signature_matches_exact_alpha_equiv` | **unit, `cranelisp-typecheck`** (`/dev`), at-impl | the match predicate: `(Fn [a] a)` matches `(Fn [b] b)` (alpha-equiv); `(Fn [a a] a)` does **NOT** match `(Fn [a b] a)` (bijective renaming); same-name-different-module ADTs do **NOT** match (FQ head equality); arity is structural (different param/arg counts never match) | signature-match §2 |

Notes:
- P3.4 + P3.6 are the two containment/isolation keystones the §11 acceptance
  demands (zero-residue + does-not-crash). They mirror existing guard shapes
  (`validate_dry_run_discards_does_not_commit` for residue; CF.1 for crash).
- P3.7 is the match-predicate unit suite; it is `/dev`-owned in
  `cranelisp-typecheck` (per `signature-match.md §2`'s worked equivalences),
  specified here so the alpha-equivalence / bijective-renaming / FQ-head /
  arity-structural cases are pinned as acceptance.
- One indexing abstraction, two feeders (R3) — P2 (in-scope, live read) and P3
  (importable, typecheck-and-discard) share the `{ name, signature, docstring,
  module }` DTO + search/format; the feeders differ. P2's rows already exercise
  the live-read feeder; P3.1–P3.4 exercise the discard feeder — no separate
  "shared DTO" test is warranted (the shape is int-private, §11.8).

---

## Match-shape verification (Phase-5 step — primer/spec contradiction)

`user/syntax-cheatsheet-plan.md §4` flagged a **primer/spec `match`-shape
contradiction**: the always-on primer (`src/agent/primer.txt`, lines ~122–125)
shows `match`/sum-ctor examples with **paren-grouped arms** `((Circle r) (* …))`,
while the spec's authoritative grammar (`spec/06-pattern-matching.md §6.1`) is
**flat bracket pairs** `[(Circle r) (* …) (Rect w h) (* w h)]`. The cheat-sheet
will use the spec (bracket) shape; the two shapes must be reconciled against the
**live REPL** in Phase 5.

**Phase-5 verification step (not a row authored this phase):**
1. During Phase 5, run **both** `match` shapes (paren-grouped and flat-bracket)
   through the live REPL.
2. **If the flat-bracket spec shape compiles and the primer's paren-grouped shape
   does NOT** → the primer is a **defect**: file to `/dev (src/)` to correct
   `primer.txt`, AND `/qa` authors a narrow failing repro
   (`tests/spec_06_pattern_matching.rs`) pinning that the spec's flat-bracket
   `match` shape compiles (RED-first if it does not, green on the as-built
   compiler; or a guard that the paren-grouped shape is rejected if that is the
   correct behaviour).
3. **If the spec example itself fails to compile** → escalate to `/spec` + `/qa`
   (a spec-vs-implementation divergence, not a primer matter).
4. Do not ship two contradictory shapes — conform the primer and cheat-sheet to
   whatever the live REPL accepts.

This is a Phase-5 *verification + conditional repro* step. It produces a committed
`/qa` test only if a real shape-divergence defect surfaces; otherwise it is a
verified-no-defect note (the cheat-sheet conforms to spec, the primer is corrected
by `/dev` if it diverged). Recorded here so the obligation is not lost.

---

## Feature-OFF byte-identical (Lane B — standing floor)

The S90 surface adds: P1's `/syntax` command + asset (default-build, NOT gated —
so it must work feature-OFF, P1.4); P2's harvest grain (agent-gated); P4's log
(agent-gated); the eval-thread `catch_unwind` (agent-gated). The standing Lane-B
floor (`agent-testing-strategy.md §4`) re-verifies at S90 close:

- the default `cargo nextest run` stays **agent-free** (no rig/tokio in the dep
  tree) and byte-identical on every non-agent input;
- `/syntax` (the one LLM-free addition) works on the default build (P1.4) WITHOUT
  pulling the `agent` feature into the default dep tree;
- `CRANELISP_AGENT_LOG` is inert on the default build (P4.3).

No new dedicated Lane-B row beyond P1.4 + P4.3 + P4.5 above; the existing Lane-B
family (`tests/agent.rs` feature-off rows + the default-suite green count) is the
guard.

---

## Testability seams owed by `/dev` (flagged, NOT bridged with internal helpers)

Per `tests/CLAUDE.md §"Two tiers, no middle"`, a behaviour that cannot surface
through the binary's I/O is a **binary testability gap** → file `target: /int`,
do not bridge with an internal-API helper. The S90 seams `/dev` must provide for
the rows above to be e2e:

1. **New pull-tool names in the stub DSL allowlist** — `syntax` and `lib-search`
   (at P3 impl) must be synthesizable via `tool: syntax <topic>` /
   `tool: lib-search <query>` (the read-only allowlist gains these rows, §11.7 /
   §17.19.3). P1.6 / P3.5 depend on this. (Already the established `tool:` pattern;
   just two new allowlisted names.)
2. **A harvest-budget lever observable from an e2e** — P2.3 needs to drive the
   harvest at a tiny `char_budget` so degradation-not-truncation is observable
   through the `/context` dump. If no env/flag knob exists to force a small budget,
   that is a gap → `target: /int` (a `CRANELISP_AGENT_HARVEST_BUDGET`-style test
   lever, sibling to the existing agent env surface §17.10).
3. **An observable "could not validate/index" surfacing for the catch floor** —
   CF.1 (and P3.6) assert the eval-thread `catch_unwind` converts a panic to a
   clean outcome. The test observes "session survives + clean note"; if the catch
   fires *silently* with nothing observable in the transcript, the test can only
   assert survival (the following-input-evals proxy). A surfaced "could not
   validate <…>" / search-quality note (§17.19.4) makes the catch *directly*
   observable — flag `target: /int` if the surfacing is absent and only the
   survival proxy is available.
4. **`CRANELISP_AGENT_LOG` honored in test subprocesses** — P4.1/P4.2/P4.4 set the
   env on the spawned binary (the `Cranelisp` builder's `.env(...)` already does
   this). No new seam; noted so the log path is a per-test tmpdir file (fresh-tmp
   discipline, `tests/CLAUDE.md`).

None of these requires a Rust-API bridge; all are env/allowlist/surfacing knobs
on the binary. File the FIXME `target: /int` only if a knob is genuinely absent at
Phase 5.

---

## Summary — row inventory

**SHIPS THIS SPRINT (RED-first → `/dev` flips green in change-set):**

- **P1 `/syntax`** — 8 rows (P1.1–P1.8): bare-list, topic-content,
  unknown-relist-+neg, default-build-not-gated, no-color-degrade-+neg, agent-pull,
  asset-delimiter-parse, sampled-example-compiles. `tests/repl_introspection.rs`
  (default) + `tests/agent.rs` (Lane A).
- **P2 harvest sig-grain** — 4 rows (P2.1–P2.4): name+sig+docstring, FQ-+neg,
  budget-degrades-grain-not-truncate-+neg, no-relist-acceptance. `tests/agent.rs`.
- **P4 silent log** — 5 rows (P4.1–P4.5): jsonl-stable-keys, silent-+neg,
  absent-on-default-+neg, graceful-unwritable-+neg, feature-OFF-re-verify.
  `tests/agent.rs` + default suite.
- **0432 repro (R2)** — 4 rows: 0432.U (unit, `/dev`-authored in
  `cranelisp-typecheck`) + 0432.E1/E2/E3 (e2e, `/qa`, REPL panic-vs-clean +
  `--run` clean + REPL==`--run` convergence-+neg). `tests/spec_05_definitions.rs`.
- **Containment floor (R2 layer b)** — 1 row: CF.1 (malformed form through the
  agent validator does not crash the REPL — RED on un-caught eval-thread
  typecheck, green on the `catch_unwind` floor). `tests/agent.rs`.

**DESIGN-PINNED (authored at Pillar-3 implementation):**

- **P3 indexer + `/lib-search` + match** — 7 rows (P3.1–P3.7): name-fragment,
  exact-shape, no-match-reprompt-+neg, **zero-residue-+neg (R4 keystone)**,
  agent-pull, **0432-shaped-module-does-not-crash-+neg (§17.19.4 keystone)**, and
  the `signature_matches` alpha-equiv/bijective/FQ-head/arity unit suite
  (`/dev`-owned).

**Phase-5 verification step (conditional repro):**

- Match-shape primer/spec contradiction — run both shapes through the live REPL;
  if the primer's paren-grouped shape doesn't compile → primer defect → `/dev` fix
  + a `/qa` repro in `tests/spec_06_pattern_matching.rs`.

**0432 repro shape (the durable record):** unannotated multi-clause `defn` +
cross-variant self-call (`(defn sum-to ([n] (sum-to n 0)) ([n acc] …))`), no
prelude — captures BOTH faces (REPL panic / `--run` clean) → both converge on the
clean ambiguous-type error when §9's `monomorphise_call` P1 concreteness gate
lands.

**Testability seams `/dev` owes:** (1) `syntax`/`lib-search` pull-tool allowlist
names; (2) a harvest-budget test lever; (3) an observable "could not
validate/index" surfacing for the catch floor; (4) `CRANELISP_AGENT_LOG` honored
in the test subprocess (already provided by the builder).

---

## Execution note — Phase 5 Wave 1 step 1q (`/qa`, 2026-06-23)

Pillar-1 (§P1) tests + the two Wave-1 primer-shape repros authored RED-first.
The `.rs` files landed; `/dev` step 1d flips them green.

**P1 rows authored (8/8):**

- **`tests/repl_introspection.rs`** (default build, NOT agent-gated — the §17.17.3
  "works feature-off" contract): `syntax_bare_lists_topics` (P1.1),
  `syntax_topic_returns_content` (P1.2),
  `syntax_unknown_topic_relists_no_dead_end_neg` (P1.3),
  `syntax_works_on_default_build_not_feature_gated` (P1.4),
  `syntax_degrades_clean_under_no_color_neg` (P1.5),
  `cheatsheet_asset_parses_by_delimiter` (P1.7),
  `cheatsheet_sampled_example_compiles` (P1.8).
- **`tests/agent.rs`** (Lane A, `--features agent`): `agent_pulls_syntax_renders_as_command`
  (P1.6).

**Primer-shape repros (Wave-1 fold-in, in `tests/agent.rs`, unconditional —
they read `src/agent/primer.txt` straight off disk so they run in BOTH lanes):**

- `primer_match_uses_flat_bracket_arms_not_paren_grouped` — +neg the paren-grouped
  `((Circle r) …)` arms (verified non-compiling live), pin the spec flat-bracket
  shape (`spec/06 §6.1`). RED on HEAD (primer.txt:124–125 carry the wrong shape).
- `primer_deftrait_uses_direct_children_not_outer_bracket` — +neg the outer-bracket
  `(deftrait Show [(show …)])` (verified non-compiling live: "expected list"), pin
  the spec direct-children shape (`spec/07 §7.1`). RED on HEAD (primer.txt:46,128).
- `primer_match_flat_bracket_shape_compiles_e2e` — companion convergence-target
  e2e: the spec flat-bracket shape `(match (Some 7) [None 0 (Some x) x])` → `7`.
  GREEN on HEAD (the spec shape already compiles); pins the target the corrected
  primer must match.

**Confirmed RED count.** Default `cargo nextest run`: **1530 tests, 8 RED**
(prior 1520 baseline + P1.8 green + the primer-compile e2e green = 1522 passed) —
the 8 are exactly the intended new guards (6 `/syntax` default rows + 2
primer-content guards); no pre-existing test regressed. Agent lane
(`cargo nextest run --features agent --test agent`): **3 new RED**
(`agent_pulls_syntax_renders_as_command` + the 2 primer guards; +
`primer_match_flat_bracket_shape_compiles_e2e` green). P1.8 + the primer-compile
e2e are intentionally GREEN-on-HEAD (verified-compiling-mechanism / convergence
targets, independent of `/syntax` wiring — same pattern as 0432.E2).

**Testability seam owed by 1d (CONFIRMED at authoring).** The `agent_pulls_syntax`
RED output is precisely `agent attempted a non-read command 'syntax' — refused
(read-only Advise mode)` — i.e. **`syntax` must be added to the read-only pull-tool
allowlist** (§17.17.3 / §11.7, seam #1 above) so `tool: syntax <topic>` synthesizes
a rendered `/syntax <topic>`. Without the allowlist row P1.6 cannot go green even
once the command is wired. (`lib-search` allowlisting stays design-pinned, P3.)

**Pre-existing, NOT a regression:** `agent_on_no_provider_is_dormant` (S88) fails
on this host because a real `ANTHROPIC_API_KEY` is present in the environment, so
the "no provider ⇒ dormant" precondition does not hold (the agent answers instead).
Environment-dependent; untouched by this step.

No plan-row shifts (the 8 P1 rows landed exactly as planned); the primer-shape
repros are the SPRINT.md-Notes Wave-1 fold-in (not a new §P1 row). No FIXME filed
(seam #1 is already named in §"Testability seams" and re-confirmed above).

---

## Execution note — Phase 5 Wave 2 step 2q (`/qa`, 2026-06-23)

Pillar-2 (§P2) tests authored RED-first in `tests/agent.rs` (Lane A,
`--features agent`). The `.rs` rows landed; `/dev` step 2d enriches
`harvest_context` (`src/agent/harvest.rs`) to flip them green.

**P2 rows authored (4/4), all observed via the `/context` dump's new
`== in scope ==` block:**

- `harvest_in_scope_shows_name_sig_docstring` (P2.1) — own defn (`inc-doc`,
  docstring'd) + implicit-prelude symbol (`add-i64`) each carry name + FQ `:Type`
  signature + docstring in the `== in scope ==` block. The `add-i64` signature
  is the discriminating assertion (it is NOT in the current-module source pin, so
  its presence proves the export-surface arm is enriched, not the §5.4 source
  floor).
- `harvest_sig_is_fully_qualified_neg` (P2.2, +neg) — the in-scope signature uses
  the FQ `primitives/Int` form; the +neg strips every `primitives/Int` and asserts
  no bare `Int` survives in a type position (the `/sig`-grain FQ-display +neg).
- `harvest_budget_degrades_grain_not_truncates_neg` (P2.3, +neg) — under a tight
  budget the `== in scope ==` block keeps every symbol NAME (`inc-doc`, `add-i64`)
  while eliding the docstring DETAIL (grain degrades sig→names, never silent
  membership truncation).
- `harvest_references_actual_sig_no_relist_needed` (P2.4) — a stub session whose
  model answers directly (no `tool: list`/`exports`) asserts the transcript carries
  NO `/list`/`/exports`/`/imports` pre-flight pull AND the ambient `== in scope ==`
  harvest carries `inc-doc`'s actual signature (so the no-pull answer is grounded).

All four scope their grain assertions to the new `== in scope ==` block header
(`repl/spec.md §17.18.2` / design/int/agent.md §23.1) — deliberately NOT the
whole `=== HARVESTED CONTEXT ===` (which always carries the current-module
full-source pin and would satisfy the own-defn assertions trivially). RED on HEAD
because the `== in scope ==` block does not exist (harvest is name-only): the
`split("== in scope ==").nth(1)` yields nothing, so every grain + name assertion
fails.

**Confirmed RED count.** `cargo nextest run --features agent --test agent`
(`--no-fail-fast`, agent env unset so the dormant precondition holds — see the
Wave-1 note re `agent_on_no_provider_is_dormant`): **50 tests run, 46 passed, 4
failed** — the 4 failures are exactly the new P2 rows above; no pre-existing
agent-lane test regressed. Default `cargo nextest run`: **1539/1539, 0 failures**
— the P2 rows are `#[cfg(feature = "agent")]` and compile out of the default
build, so the Wave-1 default count (1539/0) is undisturbed.
`python3 tests/plan/spec_link_check.py --scope agent.rs` clean (55/55 OK, every P2
row cites `repl/spec.md §17.18`).

**Testability seam owed by 2d (CONFIRMED at authoring — test plan §"Testability
seams" #2 / design/int/agent.md §23.2).** P2.3 sets
`CRANELISP_AGENT_HARVEST_BUDGET=200` to force a small in-process `char_budget` so
budget-degrades-GRAIN-not-membership is observable through the `/context` dump.
**This env lever does not exist on HEAD** — P2.3 is RED partly because the lever is
absent (and partly because there is no in-scope block to degrade). 2d must add the
lever (a sibling to the §17.10 agent env surface) alongside the sig-grain
enrichment, or P2.3 cannot go green even once the in-scope block exists. The other
three P2 rows need only the §23.1 in-scope-block enrichment (the existing
`/context` dump seam already surfaces it — no new lever). No FIXME filed (the seam
is already named in §"Testability seams" #2 and re-confirmed here; file
`target: /int` only if 2d finds the lever genuinely cannot be wired).

No plan-row shifts (the 4 P2 rows landed exactly as planned); no ledger entry
(ship-this-sprint RED-first guards are tracked here, not in the carry-forward
failure ledger).

---

## Execution note — Phase 5 Wave 3 step 3q (`/qa`, 2026-06-23)

Pillar-4 (§P4) tests authored in `tests/agent.rs` (Lane A log-content rows +
the default-lane absence/byte-identical rows). The `.rs` rows landed; `/dev`
step 3d builds `src/agent/log.rs` (the §27 silent sibling sink) to flip the
RED row green.

**P4 rows authored (5/5):**

- **`agent_log_writes_jsonl_with_stable_keys` (P4.1, Lane A, `--features agent`)**
  — `CRANELISP_AGENT_LOG=<fresh tmp path>` set on the spawned binary; a stub
  session that PULLS (`/source`) + REPAIRS (broken-then-fixed `submit`) +
  SUBMITS writes a JSONL file. Asserts the file exists, every line is a JSON
  object (`{...}`) carrying `"event"`, and the broken-then-fixed submit produces
  a `{"event":"repair",...}` record carrying the stable greppable keys
  (`symbol`/`module`/`error_class`/`iteration`) with `symbol=helper`. The JSONL
  shape is checked by a `grep`-style structural assertion (the §17.20.3
  acceptance is operational `grep`/`jq`-ability; the test crate has no
  `serde_json` dev-dep, so a substring/`{...}` check IS the spec acceptance —
  no `Cargo.toml` change). **The load-bearing RED-first row.**
- **`agent_log_is_silent_transcript_unchanged_neg` (P4.2, +neg, Lane A)** — two
  stub transcripts (log-ON vs log-OFF), byte-identical AFTER masking the
  per-prompt wall-clock counter (`N+Mms; <mod>> ` — independent jitter every
  REPL run differs on, NOT a log perturbation; masked with the `regex` dev-dep).
  Plus a +neg that no "logging to …" banner appears. **Green-on-HEAD** (the var
  is inert today ⇒ zero perturbation) — the standing silent-floor guard the sink
  must not regress (per §27.5 byte-identical guarantee).
- **`agent_log_graceful_on_unwritable_path_neg` (P4.4, +neg, Lane A)** —
  `CRANELISP_AGENT_LOG` under a NONEXISTENT parent dir; the session exits clean
  (no crash/panic), the agent turn still renders (`▌`), NO log-error chatter
  reaches the REPL, and no file is forced into being. **Green-on-HEAD** (inert
  var ⇒ no write attempt) — the standing graceful-degradation floor.
- **`agent_log_absent_on_default_build_neg` (P4.3, +neg, DEFAULT lane,
  `#[cfg(not(feature = "agent"))]`)** — on a default (non-`agent`) build,
  `CRANELISP_AGENT_LOG` set ⇒ NO log file written (the var is inert; the sink
  lives only in an `--features agent` build, §17.20.2). **Green-on-HEAD** —
  the Lane-B absence floor.
- **`agent_log_feature_off_byte_identical_reverify` (P4.5, DEFAULT lane)** —
  the same non-agent input on the default build is byte-identical with
  `CRANELISP_AGENT_LOG` set vs unset (modulo the masked prompt counter) — the
  agent-gated log code adds nothing to the default suite (§17.9). **Green-on-HEAD**
  — the standing Lane-B floor re-confirmed for Pillar 4.

**Confirmed RED count.** Agent lane
(`env -u ANTHROPIC_API_KEY -u CRANELISP_AGENT_PROVIDER -u CRANELISP_AGENT_STUB_SCRIPT
cargo nextest run --features agent --test agent --no-fail-fast`): **53 tests run,
52 passed, 1 failed** — the single RED is `agent_log_writes_jsonl_with_stable_keys`
(no log sink exists ⇒ no file written), the load-bearing positive guard. P4.2 /
P4.4 (Lane A) and P4.3 / P4.5 (default lane) are intentionally **green-on-HEAD**:
they are +neg silence/absence/graceful/byte-identical FLOORS (the var is inert
today ⇒ trivially no perturbation), exactly the standing-guard pattern of
`agent_build_non_read_tool_still_refused_neg` (S89) and the Wave-1 P1.8 /
primer-compile convergence targets — they pin behaviour the sink must NOT
regress, per design §27.5's byte-identical guarantee. No pre-existing agent-lane
test regressed. Default `cargo nextest run`: **1541/1541, 0 failures** (up from
the Wave-2 1539: the two default-lane P4.3 + P4.5 rows are green-on-HEAD absence
guards; the Lane-A rows are `#[cfg(feature = "agent")]` and compile out).
`python3 tests/plan/spec_link_check.py --scope agent.rs` clean (60/60 OK; every
P4 row cites `repl/spec.md §17.20` / §17.9).

**Testability seam owed by 3d.** Per the test plan §"Testability seams" #4:
`CRANELISP_AGENT_LOG` must be honored on the spawned binary — **already provided**
by the `Cranelisp` builder's `.env(...)` (no new seam). The single substantive
obligation is the §27 sink itself (`src/agent/log.rs`): one-line env-gated
appends at the existing record sites (`pull.rs` repairs/pulls, `run_pull`,
`run_submit` submits/give-ups), JSONL via `serde_json`, best-effort-discarded
write — so P4.1's file appears with the stable keys. No in-process log-path
observation lever is needed beyond the env var (the test reads the file off the
per-test tmpdir). No FIXME filed.

No plan-row shifts (the 5 P4 rows landed exactly as planned); no ledger entry
(ship-this-sprint RED-first guards are tracked here, not in the carry-forward
failure ledger).
