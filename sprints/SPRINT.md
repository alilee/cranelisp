# Sprint 88: Clean-and-Green Close-out → Agentic-REPL Phase 1 (Advisor MVP)

**Status**: PHASE 5 LANGUAGE (ACTIVE) — Wave 1

**Goal**: Clear the last genuinely-clearable defects on the green base (the exemplar-gating `conj` heap-ADT corruption + the CWD-relative regen write), then open the **agentic-REPL track** — ratify the embedded-agent design (U1–U6), build its LLM-free foundations (module preambles first-class + the dispatch classifier + reverse-query commands), and land the **Phase-1 read-only "grounded advisor" MVP** behind a default-off `agent` feature.

## Scope

S88 is the **first sprint of the agentic-REPL track** — the track you sequenced to run *before* effect-concurrency and *before* Phase H (ROADMAP Forward Plan; `design/arch/effect-concurrency.md` §Sequencing). It runs in three stages: get the green base **fully clear of clearable defects** (gates the rest), build the **LLM-free agentic-REPL foundations**, then land the **Phase-1 Advisor MVP**.

Entry baseline: S87 closed `--workspace` **2870/0/0, zero intentional reds**. Any red is a true regression.

### Stage A — Green & clear (gates Stage B/C)

Two real defects + a FIXME-store triage. Both defects get a `/qa` failing-not-ignored repro first; the owning skill flips it green in the same change-set with its mandatory unit test (CLAUDE.md §Testing).

1. **DEF-2 — curated `conj` corrupts heap-ADT Vec elements (exemplar-gating; user-flagged).** The exemplar hand-uses bare `vec-push` everywhere it accumulates a `Vec` of heap ADTs because the curated wrapper `(defn conj [v x] (vec-push v x))` mis-manages the refcount of a heap-ADT element passed through its call frame (wrapper-RC / consuming-calling-convention). A `Vec` of `Cell`/`Box` built via `conj` in an accumulator loop comes out **corrupted** → the solver reports spurious "No solution found." (`exemplar/CLAUDE.md` §Known-Issues DEF-2.)
   - **Repro recipe (exact shape matters — S87's repro pass claimed "simple conj doesn't reproduce"; the live shape is heap-ADT-through-the-wrapper):** accumulate a `(Vec Box)` (ADT element) via `conj` vs via `vec-push` in a ~30-iteration loop; compare element sums — they differ. Int-valued `conj` is unaffected; `count`/`get`/`assoc` are unaffected.
   - **RESOLVED — does not reproduce (Step 3.1, `/qa`, 2026-06-21).** Driving the exact heap-ADT-through-wrapper shape (+ borrowed-source re-read, shared-element copy, multi-variant `Cell`, RC-trace, 200× sustained) shows `conj` is **RC-identical to `vec-push`** — `CRANELISP_RC_TRACE` balanced, no premature element free. **DEF-2 was collaterally fixed by S87's FIXME 0417** (the vec-set/vec-push heap-element consuming-inc alignment); the "wrapper-RC mis-count" hypothesis is not present in current codegen. **Decisive:** swapping *every* `vec-push`→`conj` in a copy of the exemplar solves the full 9×9, tests 39/39, 200× sustained correct. **No owner triage; no fix work.** A fixed defect earns a GREEN guard, not a RED: `tests/spec_12_runtime.rs::{conj_wrapper_heap_adt_element_matches_vec_push_repl, conj_wrapper_heap_adt_element_sum_run, conj_wrapper_multivariant_cell_vec_built_correctly_run}`.
   - **Closure:** Stage-A DEF-2 exit gate **met by green guards.** **Stage D / Phase-6b G2 swap is UNBLOCKED** (no fix to wait on) — `/port` retires the `exemplar/CLAUDE.md` DEF-2 carve-out by swapping `vec-push`→`conj`.

2. **0423 — source-regen / `(mod …)` extraction writes backing files CWD-relative, not lib-dir-relative (`/int`).** Running the in-language stdlib self-test runner from the repo root caused the extractor to emit `(mod test)` backing files to `./collections/…`, `./num/…` etc. at the repo root (currently band-aided by a `.gitignore` guard). The "D-regen" class the S87 repro pass dismissed as a test-isolation artifact — the root cruft is concrete evidence it happens.
   - **Repro DONE (Step 3.1, `/qa`) — RED guard, owner `/int`.** `tests/spec_08_modules.rs::inline_mod_test_extraction_writes_lib_dir_relative_not_cwd` (failing-not-ignored, `// spec: §8.2.2`): with CWD = tmpdir root ≠ lib-dir, the inline `(mod test)` backing file writes to `<cwd>/accum/test.cl` instead of `<lib-dir>/accum/test.cl`. **Secondary symptom confirmed:** parenthesized-type annotations regen with a spurious space (`[: (Option String) x]` vs `:(Option String)`); bare `:Int` fine.
   - **Fix (Phase 5, `/int`):** resolve extraction output against the lib-dir / source module's own directory, never the process CWD; prefer recognizing an existing extraction-stable backing file over re-emitting; fix the regen annotation spacing (`: Type` → `:Type`, per the `:Type`-binds-following-form reader-macro semantics).

3. **FIXME-store triage.** Every open FIXME gets an explicit disposition. Confirm-deferred (NOT actioned — they belong to later tracks you already sequenced):
   - **Phase H:** 0050 (display protocol), 0052 (`/learn`), 0365 (Type.member), 0407 (Model-B closure-callback), 0419 (shared HostCallbacks builder).
   - **Effect-concurrency track** (runs after agentic-repl): 0424 (spark apply-args / par-map), 0425 (compiler-internal dependency-service extraction), 0426 (D0030 mutual-import deadlock revisit-trigger), 0408 (Sudoku parallel-search showcase).
   - **Ruling-gated / covered:** 0410 (Cranelisp.toml scaffold — needs `/spec §8.11.4` ruling; deferred), 0416 (bitwise intrinsics — `stdlib num.bits` covers; deferred to a perf-driven decision).
   - **Housekeeping:** the concurrency-track sequencing FIXME (referenced as **0427** in `effect-concurrency.md`) was never filed — `/sprint` records the sequencing in ROADMAP at close rather than filing a FIXME-to-self.
   - **Exit gate (A → B/C):** `cargo nextest run --workspace` green (both new repros flipped); FIXME store fully triaged.

### Stage B — Agentic-REPL foundations (LLM-free)

Builds on the green base. Everything here is independently valuable and ships with **no LLM dependency** — it keeps the default build + ~9s suite LLM-free.

1. **U1–U6 ratification gate (`/sprint` + user; `/arch` advises).** `design/arch/repl-embedded-agent.md` is EXPLORATORY/pre-ratification. The six sign-offs (U1 dispatch rule; U2 module-preambles-first-class prerequisite; U3 memory line; U4 push transparency; U5 validator policy; U6 backend + privacy) must be ratified before the foundations & MVP lock. The doc carries leans for U4/U5. **Held at the top of Phase 2/3** — the design phase cannot finalize until these are answered.

2. **Module preambles first-class (U2 prerequisite — `/spec` + `/repl`).** Load-bearing for the agent's memory model (§3.4) and independently useful: a normative module-preamble form + `/doc <module>` to read it + an edit path. `/spec` owns the normative form; `/repl` owns the experience; `/qa` covers it. **(R2)** The form + experience are `/spec`+`/repl`-local, but the *storage* is an additive `module_preamble` field on the per-module `SymbolTable` — a `cranelisp-types` change + `CACHE_SCHEMA_VERSION` bump. Lock the form first, then file `target: /arch` for the field (do NOT model it as a synthetic `ModuleEntry`).

3. **Dispatch classifier + `/ask` + reverse-query commands (`/int` + `/repl`).** The §5.3 "parses-as-form-or-slash → REPL; else → agent" classifier with the `/ask <text>` escape hatch (feature-off ⇒ `/ask` prints "agent not built in", `Err(other)` falls back to today's parse-error display — byte-identical to today). Plus the reverse-query commands the agent (and humans) need — `/refs <sym>`, `/tests-for <sym>` (on-demand scan over in-memory bodies, no maintained index) — which **grow the REPL for everyone** (§4.4 corollary).

### Stage C — Phase-1 Advisor MVP (LLM, feature-gated OFF by default)

The read-only **grounded advisor** (`repl-embedded-agent.md` §9 Phase 1). Introduces the external LLM dependency, fully `#[cfg(feature="agent")]`-gated — `agent` in no crate's `default`, no dev-dep enables it, default `cargo build` / `cargo nextest run` never compile the client.

- **Feature-gated `src/agent/` module** (sibling to `repl.rs`/`eval.rs`, `pub(crate)`), `agent_turn` model↔tool loop; the §5.3 classifier's `Agent(text)` arm.
- **Pluggable LLM backend trait + an API backend** (opt-in twice: compiled-in AND runtime key present; absent a key the agent is dormant and `/ask` says so). *Provider/client choice is a Phase-2/3 design decision* — natural default is the Anthropic Claude API (latest models) given this project's context; `/arch` rules the boundary, `/int` wires it.
- **Harvested push + relevance ranker** (§4.2/4.3 heuristics: current-module full src pinned; preambles+exports for last ~6 modules mentioned; full src of last ~10 fns mentioned; graceful-degradation ladder under token budget).
- **Always-on language primer** (§6.1 — distilled syntax/special-forms/`:Type`-convention/prelude few-shot idioms; the model has zero Cranelisp in training).
- **Pull-as-visible-commands** (§4.4 — a pull synthesizes a REPL command run through the same `process_commands` path, rendered as if typed); **read-only Advise mode** only (no writes this sprint).
- **Spec retrieval** (grep over embedded `spec/`) + **telemetry skeleton** (§4.5 — log pulls/misses for later push-tuning). **(R5 — within-Stage-C release valve):** these two are the cleanest to **trail into S89 if the wave runs hot** — spec-grep is a Phase-1 stopgap (→ semantic search in Phase 3) and telemetry has no Phase-1 consumer. Deferring them keeps the acceptance criterion intact and does not touch the Stage B/C fault line. The irreducible MVP is client + harvester + primer + pull-as-visible-commands.
- **Acceptance:** `/ask "how do I define a constrained function over Num?"` → a spec-grounded, session-aware answer with a proposed `(defn …)` **shown, not submitted**.
- **(R3 — amended):** the LLM backend is **`rig-core`'s `CompletionModel`** directly (provider/completion layer only, NOT rig's Agent framework). Multi-provider incl. **local Ollama** (U6 escape hatch + Phase-3 local goal now). `rig-core` 0.39.0: providers built into the core (no per-provider features); `optional=true` + `default-features=false` + minimal transport opt-in (Phase-5 lookup), behind `#[cfg(feature="agent")]`. Default provider = Anthropic Claude (model-id from runtime config); Ollama = local/offline.

### Stage D — Exemplar adequacy adoption refresh (Phase 6b — `/port`)

The S87 stdlib-adequacy review (`exemplar/notes-stdlib-adequacy-s87.md §FULL`; `stdlib/plan-stdlib.md §26.4`) **completed all stdlib *authoring*** (G3 `range`, G4 `char-to-digit`/`digit-to-char`, G5 `replace-at`/`str-assoc`, G1 `num.bits` module). What it parked on `/port` is the **exemplar adoption** — sites where the verb now exists but the exemplar hand-rolls. S88 closes them in Phase 6b (the natural user-facing-action home), most gated on Stage A:

- **G2 — `vec-push` → `conj`** (~5 heap-ADT accumulator sites; `grid.cl`/`solver.cl`/`html.cl`) — **gated on the Stage A DEF-2 fix.** Retires the DEF-2 carve-out in `exemplar/CLAUDE.md`. The correct closure of the defect (retire the workaround it forced).
- **G1-adoption — `grid.cl` bit layer (~55 lines) → `num.bits/*`** (the module landed S87).
- **G6 — `digit-string` (10-arm `if`) → `int-to-string` / `digit-to-char`**; **G8 — `make-dots` → `repeat-str`**; **G10 — dedup `user.cl`'s `rem`/`row-of`/`col-of`**.
- **DO NOT FORCE (flag only):** **G7** (`rem-i64` inline alias) and **G9** (`str` macro) — `exemplar/CLAUDE.md` deliberately rationalizes both; leave as-is.
- **No new stdlib authoring expected.** If the Phase-6a assessment (or the agent MVP exercising the language) surfaces *new* adequacy gaps, they follow the user-proxy protocol → `/qa` repro (defects) or FIXME (capability gaps), not in-sprint stdlib authoring.
- All prior demos + the exemplar replay green after the swaps (regression guard).

### Out of scope (deferred, with rationale)

- **Agentic-REPL Phase 2** (Build + Document modes + the pre-flight validator/silent-repair on staging) — needs the preamble prerequisite settled and the Advisor MVP proven first; **target S89** on this base.
- **Agentic-REPL Phase 3** (compensation-telemetry-driven curation, semantic spec search, local-model backend, push-transparency header) — target S90+.
- **Effect-concurrency track** (0424/0425/0426/0408) — your sequencing: *after* agentic-repl. The compiler-internal concurrency debt (0425/0426) explicitly must NOT be actioned standalone (Principle 6) — it rides the coordination-layer redesign of that track.
- **Phase H** (0050/0052/0365/0407/0419 + the `--release` efficiency tier) — gated behind both tracks.

## FIXME debt

| FIXME | Target | Status | S88 disposition |
|---|---|---|---|
| 0050 | /int | deferred | Phase-H carry (display protocol) — confirm deferred |
| 0052 | /repl | open | Phase-H carry (`/learn`) — confirm deferred (agent may subsume later; no coupling in MVP) |
| 0365 | /spec | open | Phase-H carry (Type.member) — confirm deferred |
| 0407 | /arch | open | Phase-H carry (Model-B closure-callback) — confirm deferred |
| 0408 | /port | open | Concurrency-track carry (Sudoku parallel-search) — confirm deferred |
| 0410 | /repl | open | Ruling-gated (`/spec §8.11.4`) — confirm deferred |
| 0416 | /arch | open | `stdlib num.bits` covers — confirm deferred |
| 0419 | /arch | open | Phase-H carry (HostCallbacks builder) — confirm deferred |
| 0423 | /int | open | **Stage A — action** (CWD-relative regen write) |
| 0424 | /arch | open | Concurrency-track carry (par-map/spark) — confirm deferred |
| 0425 | /arch | open | Concurrency-track carry (dependency-service extraction) — confirm deferred |
| 0426 | /arch | open | Concurrency-track carry (D0030 deadlock revisit-trigger) — confirm deferred |
| DEF-2 | — | **RESOLVED** | Does not reproduce (Step 3.1) — collaterally fixed by S87 FIXME 0417; 3 green guards added. No fix work. Stage D G2 swap unblocked. |
| 0423 | /int | open | **Stage A — action**; repro RED-guarded (Step 3.1); fix Phase 5 (`/int`) |
| 0428 | /arch | open | **Stage B / Step 3.2** — filed by `/spec` (Step 3.1): additive `SymbolTable.module_preamble` field + `CACHE_SCHEMA_VERSION` bump (R2 storage for U2) |
| (new) | /repl,/int | to file | Further agentic-REPL handoffs filed as Stage B/C design locks (per `repl-embedded-agent.md` §10 "Next skills") |

## Architecture review (Phase 2)

**Verdict (/arch, 2026-06-21): APPROVE-WITH-REVISIONS.** Scope is technically coherent; the embedded-agent design's central claims hold. **No `cranelisp-types`/`design/arch` edit made or needed this phase** (one additive field is anticipated but Phase-3-gated — R2). Confirmed: **zero new cross-crate edges** (the agent lives entirely in the int BC §6, reuses int's existing inward calls); the agent is a **REPL-cadence consumer, not a new state window** (holds `&mut CompilerSession` at cadence, reaches state only through the existing introspection surface — satisfies BC §6.3); the four-cut `#[cfg(feature="agent")]` graft is **sound** (cuts at 3 seams + 1 sibling module; feature-OFF ⇒ byte-identical binary *by construction* via the `Err(other parse error)`→today's-diagnostic fallback); the one new internal seam (typecheck-only dry-run on staging) is **`pub(crate)`, int-internal, no facade/interface delta** (it's int discarding a successful staging frame — already what int does on `Err` per Decision 44).

**Revisions (applied to scope):**
- **R1 — DEF-2: minimal-repro gates owner assignment.** `/backend` is *candidate*, not confirmed (S87 mis-framed 2 of 3 defect owners). The `/qa` heap-ADT-through-the-wrapper repro MUST be reduced to a minimal failing test **before** `/sprint` dispatches a `/backend` triage; the handoff names the repro, not the symptom. Could be backend consuming-convention **or** typecheck monomorphisation-of-the-wrapper **or** RC-fusion — the repro disambiguates. Inspect at CLIF level (`/clif conj` / `CRANELISP_CODEGEN_TRACE=1`).
- **R2 — module-preamble storage is an additive `cranelisp-types` field, Phase-3-gated.** Form + experience are `/spec`+`/repl`-local; the *storage* (a `module_preamble: Option<…>` field on the per-module `SymbolTable`, parallel to the per-entry `docstring`, BC §7) is an additive `cranelisp-types` change + `CACHE_SCHEMA_VERSION` bump. `/spec`/`/repl` lock the normative form first, then file `target: /arch`; /arch adds the field + regenerates the baseline in that change-set. (The §3.4 "no interface delta" framing was slightly optimistic on storage.)
- **R3 — provider-agnostic LLM backend. AMENDED (user, 2026-06-21): use `rig-core`'s `CompletionModel` directly as the boundary.** Original R3 wanted our own trait + hand-rolled Anthropic impl; superseded — `rig-core` (the modular provider/completion layer ONLY, NOT its Agent/RAG framework, which would collide with our `agent_turn`/harvester/pull-as-command + "no private tools" principle) IS the provider-agnostic boundary R3's intent required. `agent_turn` speaks `rig::completion::CompletionModel` directly (user chose the leaner option over an owned adapter trait). **Multi-provider incl. LOCAL (Ollama, no-key) — delivers the U6 privacy escape hatch + the §9 Phase-3 local-model goal now.** Dep discipline (verified vs `rig-core` **0.39.0**): providers (`rig::providers::{anthropic,ollama}`) are compiled into the core crate — there are **no per-provider Cargo features** (the "only anthropic+ollama" is *intent*, compile-minimal, not literal flags). `rig-core` declared `optional = true`, `default-features = false` (drops `derive`/`reqwest`/`rustls` defaults) + the minimal transport feature opt-in (exact set = Phase-5 lookup against the pinned 0.39.0 `Cargo.toml`), enabled only by the `agent` Cargo feature → entirely behind `#[cfg(feature="agent")]` (default build + ~9s suite never compile it). Default provider = Anthropic Claude (latest models, model-id from runtime config); Ollama is the local/offline escape hatch. **Tradeoff accepted:** `agent_turn` is coupled to rig's API surface (dropping rig later touches the loop) — chosen for the leaner build.
- **R4 — Stage B/C fault line confirmed; no re-cut.** Stage B (LLM-free foundations) is independently valuable and a clean fallback if Stage C slips. Recommend no re-cut.
- **R5 — within-Stage-C release valve.** Client + harvester + primer + pull-as-visible-commands are the irreducible MVP (the acceptance criterion needs all three). **Spec-retrieval (grep over embedded `spec/`) + telemetry skeleton are the cleanest to trail into S89** if the wave runs hot — spec-grep is a Phase-1 stopgap (→ semantic search in Phase 3); telemetry has no Phase-1 consumer. Deferring them keeps MVP *acceptance* intact without touching the B/C fault line.
- **R6 — track sequencing CONFIRMED** (agentic-repl before effect-concurrency before Phase H, per `effect-concurrency.md` §Sequencing). 0424/0425/0426/0408 deferral consistent; **0425/0426 must NOT be actioned standalone** (Principle 6). **Bookkeeping:** `effect-concurrency.md` claims the sequencing FIXME "filed to /sprint as 0427" but it was never filed — `/sprint` reconciles at close (record sequencing in ROADMAP + strike the inaccurate line).

**Public-API impact:** **zero `public-api.txt` baselines move this phase.** `src/` is a binary (no baseline); `cranelisp-exe-bundle` untouched (agent never ships in `--link`/`--release`, NG4); agent additions are `pub(crate)`. Two anticipated-but-deferred edge moves: DEF-2 fix (expected internal-only, no boundary delta — watch-item) and the R2 preamble field (one additive `cranelisp-types` line, Phase-3-gated behind the U2 form lock).

**Phase-3 advisories** (carried to design skills): `/int` — build the classifier with the feature-OFF fallback as the byte-identical path; the LLM trait (R3) is the *only* provider-touching seam; keep the staging-discard arm reachable. `/spec`+`/repl` — settle the preamble form, file `target: /arch` for storage (R2), don't model it as a synthetic `ModuleEntry`. `/qa` — agent lane fully behind `#[cfg(feature="agent")]`; DEF-2 minimal repro (R1) gates triage. `/port` — G2 swap gated on DEF-2 green; G7/G9 left-as-deliberate is correct.

### U1–U6 ratification gate — RATIFIED (user, 2026-06-21)

| # | Sign-off | Ratified decision |
|---|---|---|
| **U1** | Dispatch (§5.3) | **ADOPT** (as /arch rec) — "parses-as-form-or-slash → REPL; else → agent" + `/ask` escape hatch. Zero regression of `repl/spec.md §4`. |
| **U2** | Module preambles first-class | **ADOPT** (as /arch rec) — with the R2 storage caveat: additive `SymbolTable` field + `CACHE_SCHEMA_VERSION` bump, filed `target: /arch` once the form locks. |
| **U3** | Memory line (§3.2) | **ADOPT** (as /arch rec) — named-thing→on-the-thing; only no-home intent→tiny sidecar. |
| **U4** | Push transparency (§4.7) | **AMBIENT for MVP; prunable header in Phase 3** (as /arch rec) — bless the direction, build it Phase 3 once telemetry informs it. |
| **U5** | Validator policy (§6.4) | **SILENT-REPAIR ANYTHING** (user OVERRODE /arch's "surface type errors" lean) — parse AND type failures are hidden-and-repaired; the user never sees an agent compile failure. Max flow over collaboration-on-type-errors. **Sets S89 direction only** (the validator lands agentic-Phase-2; the S88 read-only MVP has none). |
| **U6** | Backend + privacy (§7.3/§7.4) | **OPT-IN-TWICE + first-use notice** (as /arch rec) — dormant unless built `--features agent` AND key present; one-time disclosure must explicitly state **source excerpts** (not just signatures) may be transmitted, and to which endpoint. |

## Skill plans (Phase 3)

**Dispatch discipline:** each design agent edits only its OWN owned doc tree and **returns its SPRINT.md skill-plan as text** for `/sprint` to transcribe (S87 parallel-doc-clobber lesson). Source/test-touching steps serialize (broken worktree isolation). Sequenced by dependency:

**Step 3.1 — gating — DONE (2026-06-21):**
- **`/qa`** ✅ — `tests/plan/s88-test-plan.md` authored. **DEF-2 RESOLVED** (does not reproduce — collaterally fixed by S87 0417; 3 green guards; Stage D G2 unblocked). **0423** repro RED-guarded (`spec_08_modules.rs::inline_mod_test_extraction_writes_lib_dir_relative_not_cwd`) + secondary annotation-spacing symptom. Agent-feature test plan authored (separate `tests/agent.rs` lane behind `#[cfg(feature="agent")]`; `/refs`·`/tests-for` get default-lane LLM-free coverage too). Suite: 2874 run, 2873 passed, **1 intentional RED** (the 0423 guard).
- **`/spec`** ✅ (then revised) — authored `spec/08-modules.md §8.16` + cross-refs (§8.14, `05-definitions §5.12`, `01-lexical §1.3.4`), all `[S88]`-tagged. **Filed FIXME 0428** (`target: /arch`) for the additive `SymbolTable.module_preamble: Option<String>` field + `CACHE_SCHEMA_VERSION` bump (field shape unchanged by the model below). **MODEL DECISION (user, 2026-06-21):** preamble = **leading comment block** (file-header `;;` block), NOT the bare string literal `/spec` first chose. **§8.16 REVISED (DONE):** boundary = contiguous leading line-comment block from file line 1 up to the first form, **blank-line-terminated** (natural position above `(mod …)`); comments after the first form are never preamble; at-most-one. Stored text = `;;`-marker + one-space stripped, newline-joined → `SymbolTable.module_preamble: Option<String>` (field shape **unchanged**). New §8.16.6 asymmetry rationale (a module has no binding form to carry a leading string; file-header comments are where module docs live). Byte-stable regen round-trip **explicitly coordinated with the 0423 fix** (shared source-regen path). **Ripple:** needs the **frontend reader to capture + associate the leading comment block** (`Sexp::Comment`, S24, substrate) → new `/design (cranelisp-frontend)` item in Step 3.2.

**Step 3.2 — after 3.1 (the form + repro feed these):**
- **`/arch`** ✅ **DONE** — landed FIXME 0428: `SymbolTable.module_preamble: Option<String>` added (`#[serde(default)]`, `None` at all sites), **`CACHE_SCHEMA_VERSION` 8→9**, `cranelisp-types/public-api.txt` regenerated (one additive line), BC §7 updated, 0428 resolved+deleted, `cargo check -p cranelisp-types`/`-p cranelisp` clean. Field is *populated later* by the frontend reader (the comment-capture mechanism — `/design (cranelisp-frontend)` below).
- **`/design` (src/)** ✅ **DONE** → `design/int/agent.md`. Classifier = routing pre-filter in `main.rs` read loop one step ahead of `process_commands`; `Err(other parse error)`→`Agent(text)` **only under `#[cfg(feature="agent")]`** (feature-OFF byte-identical by construction); `/ask` an always-recognized `ReplCommand` (parser table identical both builds, body feature-split). **Backend SUPERSEDED (user, 2026-06-21):** the doc's own `LlmBackend` trait + `agent/anthropic.rs` impl is replaced by **`rig-core::CompletionModel` directly** (R3-amended — see Phase-2 review). `design/int/agent.md` re-tasked to revise the backend section: `agent_turn` speaks rig's `CompletionModel`; providers anthropic + ollama (local); rig `default-features=false`, behind the `agent` feature. Harvester reads `module_preamble`, ranks by `seq`, current-module-pin floor. Pull-as-visible-commands via `process_commands` (read-only allowlist = structural consent gate; writes unconstructable this sprint). **MVP-core** = classifier + `agent_turn` + trait + harvester + primer + pull + Advise + LLM-free `/refs`·`/tests-for`; **`[R5]` spec-grep + telemetry = trail-into-S89**. S89 seams (Build/Document/validator-dry-run/U4-header) kept open. Seam-citation correction: `process_commands` is `repl.rs:381` (master doc's `:419` now points at `dispatch_command` post-S77).
- **`/repl`** ✅ **DONE** → `repl/spec.md` (additive; `[S88]`-tagged). New **§17 Embedded Agent Experience** (dispatch classifier user-POV; output frame — only agent *prose* framed, commands render normal-style; §17.3 read-only Advise = propose-not-submit; opt-in-twice; §17.5 `/doc <module>` + preamble edit UX; §17.6 `/refs`·`/tests-for` LLM-free default-build; §17.8 **normative first-use disclosure** — must say **source excerpts** (code bodies, not "signatures") + endpoint, understating = conformance failure). §0.6.1 `--agent`/`--no-agent` (REPL-only; **accepted no-op on default builds**; off-by-default even with key). §3.1 inventory rows; §10.3 agent-prose style role (degrades `--no-color`).
- **`/design` (cranelisp-frontend)** ✅ **DONE** → `design/frontend/module-preamble.md`. New pure fn **`capture_module_preamble(&str) -> Option<String>`** (Shape A — line-oriented scan over raw source head, NOT the `Sexp::Comment` stream, because `skip_ws_collect_comments` swallows blank lines so the sexp stream can't see the blank-line break). Marker-strip (`;;`/`;` + one space) + `\n`-join. **Wiring:** frontend returns the `Option<String>`; **int** calls it at the 4 module-load sites + assigns `SymbolTable.module_preamble` (orthogonal to `extract_module_declarations`). **0423 coordination contract:** frontend captures, **int re-emits in `src/save.rs::generate_module_source`** (the SAME regen path 0423 corrects) as a leading "section-0" block — reconciled on the one path, no parallel helper; **inverse-pair byte-stability invariant** (capture-strip ∘ emit-remark = identity on canonical form). One boundary ambiguity flagged (leading blank line *before* the comment run → defaults to `None`). → **Phase-5 /int wiring + regen re-emit is a wave item** (coordinated with the 0423 fix); no FIXME (in-sprint scheduled work is the record).
- ~~**`/design` ({DEF-2 owner crate})** — DEF-2 root-cause design~~ **CANCELLED** — DEF-2 does not reproduce (Step 3.1); no fix work, no owner.

**Step 3.3 — exit gate ✅ MET:** interface set complete (`SymbolTable.module_preamble` landed, `cranelisp-types` baseline regenerated, 0428 resolved); `/qa` test plan authored + Stage-A repros in place (0423 RED, DEF-2 green); design docs current (`design/int/agent.md`, `design/frontend/module-preamble.md`, `spec/08-modules.md §8.16`, `repl/spec.md §17`). **Phase 3 COMPLETE → Phase 4 (wave org).**

*(`/stdlib` no authoring — S87 completed G3/G4/G5/num.bits; Phase-6a assessment only. `/port` Stage D — both Phase-6 surfaces; plans in Scope §Stage D.)*

## Waves (Phase 4)

**ALL `/dev` work is `src/` + `cranelisp-frontend` source → STRICTLY SERIAL** (single source-editor at a time; broken worktree isolation). Each `/dev` step is followed by `/review` (Phase-5 D/D/R cycle). `/qa` Stage-1 (sprint-wide failing tests) is largely satisfied (Stage-A repros in place); remaining `/qa` rides each wave. Phase-5 entry baseline: 2874 run, 1 intentional RED (0423 guard).

### Wave 1 — Stage A defect + Stage B preamble (frontend → src/, serial)

The 0423 fix and the preamble regen re-emit share `src/save.rs::generate_module_source` → **same change-set** (no parallel helper; inverse-pair byte-stability).

| Step | Skill | Crate | Task |
|---|---|---|---|
| 1a | /dev | cranelisp-frontend | ✅ **DONE** — `capture_module_preamble` in `src/preamble.rs` (Shape A); 17 `// spec:`-traced tests (boundary +neg); public-api +3 lines (mod+qualified+root re-export); frontend 310/310, workspace green except pre-existing 0423 RED |
| 1b | /dev | src/ | ✅ **DONE** — 0423 path fix (`resolve_module_file`, prefer-existing-backing-file) + annotation-spacing fix (regen-local colon-binding renderer `render_decl_sexp`; `Sexp` untouched) + preamble wiring (`apply_module_preamble` at 4 load sites) + regen section-0 re-emit (inverse-pair invariant). **0423 RED→GREEN; full suite green** (S81 repros 0337–0344 resolved earlier). +11 tests (e2e 0423, 2 process_form, 7 save.rs round-trip/spacing) |
| 1c | /qa→/dev | tests | **FOLDED into 1a/1b** — §8.16 boundary +neg covered by 1a's 17 frontend tests; byte-stable regen round-trip + 0423 green covered by 1b's e2e tests |
| 1R | /review | all | ✅ **DONE — GATE-READY, 0 Blocker/0 Important.** Root-cause confirmed (0423 path + nested-parent §8.2.5); boundary clean (no `Sexp`/`cranelisp-types` edit from 1b); inverse-pair invariant holds; test coverage +neg complete; 1501/1501 green. 3 advisory Suggestions (below). |

**Wave 1 CLOSED.** Suggestions (non-blocking, carried): (S1 →/arch future) evaluate moving colon-binding into `cranelisp-types::Sexp` so regen + future emitters share one renderer (avoids a second regen-local copy); (S2 →/dev, cheap fold-in on next `src/` touch) cross-ref comment between `render_decl_sexp_indented` and `Sexp::format_indented` (duplicated 60-col fit logic); (S3 →/design, nit) `module-preamble.md` says "one new public-api line" but as-built is 3 (mod+fn+re-export).

### Wave 2 — Stage B dispatch + reverse-query (src/, serial)

| Step | Skill | Crate | Task |
|---|---|---|---|
| 2a | /dev | src/ | §5.3 classifier (`Err(other)`→Agent under `cfg`, **feature-OFF byte-identical**) + `/ask` `ReplCommand` + reverse-query `/refs`·`/tests-for` (**default build**, on-demand AST scan) + agent-prose style role (§10.3) + unit tests |
| 2R | /review | all | feature-OFF-byte-identical verification; §4 self-doc gate intact |

### Wave 3 — Stage C Advisor MVP (src/, serial, `#[cfg(feature="agent")]`)

| Step | Skill | Crate | Task |
|---|---|---|---|
| 3a | /dev | src/ | `src/agent/` module + `agent` feature gate (off by default) + `agent_turn` loop over **`rig::completion::CompletionModel`** (R3-amended; rig-core 0.39.0 `optional`+`default-features=false`+minimal transport; providers `rig::providers::{anthropic,ollama}` built-in; Anthropic default, Ollama local) + harvester/ranker + language primer + pull-as-visible-commands + read-only Advise mode; agent-feature tests in a separate `tests/agent.rs` lane |
| 3b | /dev | src/ | **[R5 release valve]** spec-grep retrieval + telemetry skeleton — trail into S89 if Wave 3 runs hot (MVP acceptance holds without them) |
| 3R | /review | all | default build + ~9s suite stay agent-free; acceptance: `/ask "constrained fn over Num?"` → grounded answer + proposed `(defn …)` shown-not-submitted |

**Wave-3 testability seam (`/qa` input):** `/dev (src/)` must expose a **stub-provider-by-config path** (a test `CompletionModel` selected by runtime config under `--features agent`) + an assembled-request echo hook, so Lane A (deterministic plumbing) is genuine e2e rather than unit-only. Build it into 3a. Full strategy: `tests/plan/agent-testing-strategy.md`.

### Wave 4 — Stage D + user-facing (Phase 6)

| Step | Skill | Task |
|---|---|---|
| 4a (6b) | /port | Exemplar adoption: G2 `vec-push`→`conj` (unblocked — DEF-2 resolved) + G1 `num.bits/*` + G6/G8/G10; retire the DEF-2 carve-out; exemplar replays green |
| 4b (6a) | /repl, /stdlib, /docs, /port | User-facing assessment of what shipped; gap FIXMEs for next sprint; prior demos replay green |

## Agentic capability ladder (track delivery sequence)

The fine-grained capability sequence for the whole agentic-REPL track (refines the coarse 3-phase `repl-embedded-agent.md §9`). **Rungs 0–4 = the S88 read-only Advisor MVP; rungs 5–6 = S89 (agentic Phase 2); rung 7 = S90 (Phase 3).** Each rung names its acceptance/demo + the test lane that covers it (see the testing strategy doc, `tests/plan/agent-testing-strategy.md`).

| Rung | Capability | Acceptance (demo) | Sprint / wave | Test lane |
|---|---|---|---|---|
| **0** | Module preambles + clean regen (substrate for "knows intent") | preamble round-trips byte-stably; 0423 green | S88 W1 | A (deterministic) |
| **1** | **Talk to an agent** — prose → agent, model round-trip, framed reply; `/ask` | `/ask "hi"` → framed reply; `(+ 1 2)` still evals; `+` still introspects | S88 W2–3 | A (classifier, no model) + B (feature-off) |
| **2** | **Agent knows the language** — always-on primer (+ [R5] spec-grep) | `/ask "constrained fn over Num?"` → grounded answer + a `(defn …)` that **parses** | S88 W3 | A (primer-assembly) + C (answer quality, eval) |
| **3** | **Agent knows the module/session** — harvester pushes current module + mentioned symbols (reads `module_preamble`) | define `foo`, `/ask "what does foo do?"` → answer cites the real `foo` | S88 W3 | A (harvest selection +neg) + C |
| **4** | **Agent uses REPL commands as tools** — pull synthesizes `/source`·`/info` through `process_commands`, result re-enters context (read-only) | a prompt needing a pull → transcript shows the agent-issued command + output, then the answer | S88 W3 *(end of MVP)* | A (tool-call→command wiring) + D (golden transcript) |
| **5** | **Agent submits forms** — Build mode, confirm-gated, + pre-flight validator (real frontend+typecheck on staging; **U5 silent-repair-anything**) | agent defines an approved fn that always ≥ parses; broken generations silently repaired, never shown | **S89** | A (stage→check→discard repair loop) |
| **6** | **Agent records understanding** — Document mode: consultative docstring/preamble edits become durable in the code | agent writes a module preamble; round-trips; next session harvester reads it back | **S89** | A (edit + round-trip) |
| **7** | **Self-tuning + reach** — compensation telemetry → push/primer curation; semantic spec search; push-transparency header (U4); provider/local polish | telemetry drives what's pushed; offline via Ollama | **S90** | A (telemetry capture) + C (grounding regression) |

**Testing-strategy linchpin (full doc: `tests/plan/agent-testing-strategy.md`, authored by `/qa`):** because `agent_turn` speaks rig's `CompletionModel` *trait*, a **deterministic stub `CompletionModel`** splits testing — **Lane A** deterministic plumbing (CI, the bulk: classifier, request-assembly/harvest, pull-wiring, validator repair — stub backend, no network/key), **Lane B** feature-off byte-identical guard (default ~9s suite stays agent-free), **Lane C** model-quality eval (real provider incl. local Ollama; scored; not CI-blocking), **Lane D** golden-transcript replay (pull-as-visible-commands ⇒ every session is a replayable script).

## Notes

- 2026-06-21: S87 closed (`--workspace` 2870/0/0, 0 intentional reds). S88 opened.
- Scope shape (user, 2026-06-21 via /sprint Phase-1 question): **Foundations + Phase-1 LLM Advisor MVP** (the full read-only advisor, not foundations-only). Debt clearance: clear the **exemplar-gating defect** (DEF-2, user-flagged) + 0423; confirm-defer the Phase-H/concurrency FIXMEs per the established track sequencing.
- The agentic-REPL track is sequenced **before** effect-concurrency and **before** Phase H (user direction, `effect-concurrency.md` §Sequencing). S88 = agentic-REPL Phase 1.
- **Phase 1 scope APPROVED** by user (2026-06-21) → Phase 2.
- **Phase 2 /arch verdict** (2026-06-21): APPROVE-WITH-REVISIONS; R1–R6 applied to scope; no `cranelisp-types`/`design/arch` edit needed this phase; zero `public-api.txt` baselines move.
- **U1–U6 RATIFIED** by user (2026-06-21): U1/U2/U3/U4/U6 as /arch recommended; **U5 overridden → silent-repair-anything** (max flow; S89-direction only). → advanced to Phase 3 DESIGN.
- **Phase 3 Step 3.1 DONE** (2026-06-21): `/qa` + `/spec` (disjoint trees, `/qa` owned the test run). **Key finding:** the user-flagged exemplar-gating defect **DEF-2 does not reproduce** — collaterally fixed by S87 FIXME 0417; verified by swapping every `vec-push`→`conj` in the exemplar (9×9 solves, 39/39 tests, 200× sustained). Stage A's only real defect is **0423** (`/int`, RED-guarded). Stage A is lighter than scoped. Stage D's G2 swap is **unblocked** (no fix to wait on). `/spec` chose leading-bare-string-literal preambles (§8.16) + filed 0428. → Step 3.2.
- **Phase 5 Wave 1 COMPLETE** (2026-06-22): 1a `/dev`(frontend) `capture_module_preamble` (17 tests) → 1b `/dev`(src/) 0423 fix + preamble wiring + regen re-emit (**0423 RED→GREEN**, +11 tests) → 1R `/review` GATE-READY (0 Blocker). Suite **1501/1501 green, 0 intentional reds** (S81 repros 0337–0344 resolved in intervening sprints). Serial-source discipline held (1a→1b→1R, one source-agent at a time). **Whole sprint still uncommitted working-tree state** — checkpoint commit advisable at a wave boundary (pending user; no commit without request). → Wave 2 ready.
- **Pre-Phase-5 artifacts pinned (user-requested, 2026-06-22):** (1) **agentic capability ladder** (rungs 0–7, S88→S90) recorded in SPRINT.md (§"Agentic capability ladder") + `ROADMAP.md` (§"Agentic-REPL track"); (2) **track-wide testing strategy** authored by `/qa` → `tests/plan/agent-testing-strategy.md` (4 lanes; linchpin = deterministic stub `rig::completion::CompletionModel`; default suite stays agent-free; Lane C eval = local-Ollama-capable, non-CI). Wave-3 testability seam (stub-provider-by-config + request-echo hook) folded into 3a.
- **LLM backend decided (user, 2026-06-21):** use **`rig-core`** as the multi-provider/local completion layer (R3 amended). Researched the Rust landscape (rig modular core, `CompletionModel` across Anthropic/Ollama/OpenAI/Groq, Ollama = local no-key, streaming+tools at completion layer). `agent_turn` speaks rig's `CompletionModel` **directly** (user chose leaner over an owned adapter trait). rig = provider layer ONLY (not its Agent/RAG framework — would collide with our agent loop). `default-features=false` + anthropic+ollama, behind `#[cfg(feature="agent")]`. Local Ollama satisfies U6 + the Phase-3 local goal now. `design/int/agent.md` backend section re-tasked to revise.
- **Phase 3 Step 3.2 DONE + Phase 4 organized** (2026-06-21): `/arch` landed the `module_preamble` field (0428, cache 8→9); `/design (src/)` → `design/int/agent.md`; `/repl` → `repl/spec.md §17`; `/design (frontend)` → `design/frontend/module-preamble.md` (Shape-A line-scan capture + the 0423-shared regen contract). Phase 3 COMPLETE. Phase-4 waves organized (4 waves, all `/dev` serial). **Phase 5 (the implementation build) is teed up, pending user go-ahead.**
- **0427 reconciliation (R6, deferred to close):** `effect-concurrency.md` claims a sequencing FIXME 0427 was "filed to /sprint" — it never was. At close, /sprint records the track sequencing in ROADMAP and (owning `/arch`) strikes the inaccurate line, OR files 0427 as the durable record. Bookkeeping only.

## Outcome (Phase 7)

*To be authored at close.*
