# Sprint 108: Testing-driven defect-fix umbrella (successive mini-increments)

**Status**: **CLOSED 2026-07-12 (user approval).** Three increments delivered:
Inc1 (`f2bfd8a5` — 2 REPL introspection display bugs + agent request + ledger
retirement), Inc2 (`f6036d49` — `/search` seeded-primitives + lifecycle + conformance
fixes), Inc3 (this commit — the prelude≡import resolution convergence + full E-set +
`/search` visibility + governance/methodology; Phase 6a `/repl` CONFORMS + `/audit`
typecheck assessment). Suite 4370/4367, 3 known carries; agent e2e 73/73. Outcome
below; S109 carries recorded. Superseded ACTIVE status: umbrella held successive
testing-driven defect-fix increments across user testing sessions.

**Goal**: An umbrella sprint holding successive small defect-fix increments as the
user surfaces issues through REPL/language testing. Each increment runs a
lightweight scope → `/arch` sanity → D/D/R cycle and lands its own committed
guards. Increment 1 fixed two REPL introspection display bugs + the agent request
+ settled the failure-ledger question. A running **stdlib-request backlog** (see
§Stdlib request backlog) collects "missing library function" findings for a future
`/stdlib` increment — distinct from defects and language usability findings.

**Audit**: `cranelisp-typecheck` (S108 Inc3 close; escalation-trigger-6 pull — the prelude≡import resolution convergence is a major arc completing in typecheck+types; highest-signal target this sprint). Phase-6a `/audit` dispatch DONE → `audits/cranelisp-typecheck-s108.md` (disposition next-sprint Phase 1).

## Increment 3 — OUTCOME (awaiting user close approval)

**Delivered:**
- **Prelude ≡ import resolution convergence** — coverage matrix (8 RED acceptance rows) → one `ResolutionScope` (fallback intrinsic; fallback-less resolver unrepresentable) + one §8.6.4 seam; 12 divergent `_or_prelude` variants collapsed; `/review` CLEAR; `/audit` confirms class structurally closed. Public-API change (baseline regen); new correct §8.6.4 rejections (deftrait/defmacro/method over prelude), blast-radius scouted clean.
- **E-set**: E3/E8/0558 scope-enumeration; **E4 one-formatter styling** (styled::render sole authority; SGR-into-saved-.cl bug fixed; 0561 closed); E5–E7 agent/eval; E9 impl-trait hop; E10 `(vec-len [])` ambiguity (user-ruled, re-baselined).
- **/search + introspection private-name visibility** (I-1, user-caught) — `is_public()` gate; also correctly tightened §8.8.1 prelude visibility (private prelude imports no longer leak).
- **Governance/methodology**: /qa direct coverage-annotation authority (no FIXME cycle); three-altitude duplication lens (/review 0565 cue, /qa coverage-by-definition-variants category, /audit 0564 Duplication-attribute 4-facet+spec extension).
- **Phase 6a**: /repl CONFORMS (styling/search/errors vs repl/spec.md); /audit typecheck assessment landed.

**Deferred / carried (evidence-gated):**
- **Dotted-ctor `Type.Ctor` value-position (§8.5.2)** — committed failing guard; /qa-confirmed typecheck registration-model fix (not small) → **S109**. `/audit` R-3 offers an ALTERNATIVE: simplify the spec (drop the never-worked dotted-ctor form) — **USER decision at S109 Phase 1**.
- **Next-increment gap FIXMEs**: 0567 (/arch resolve terminal-vs-head filter, latent), 0568 (/dev __expr-leak in ambiguity msg), 0569 (/dev+/qa /search macro-row bogus Int type).
- **/audit S109 Phase-1 proposals**: R-1 traits.md rewrite + doc sprawl, R-2 doc/naming sweep (stale S78 block, "outer scope" rustdoc ×9, `resolve_entry_in_current_module` rename), R-4 program.rs split, R-5 S87 residue disposition.

**Suite:** 4370 tests / 4367 pass / 3 known carries (ownership_reuse 0528, deftype_ctor_trailing S107, dotted-ctor S109). Agent e2e 73/73. 0 warnings.

**Final trivia (pre-commit):** delete FIXME 0560 (/dev-intr, Wave-E fix verified); /qa PLAN provenance-note. Frontmatter-vs-§II.3 audit: governance edits (qa/spec/repl/audit defs) changed no model/effort rows — table intact.

## Increments

| # | Focus | Status |
|---|---|---|
| 1 | REPL introspection display (D1 §4.1.3, D2 §4.1.2) + agent `max_tokens` (D3) + coverage repair (C1) + ledger retirement (M1) | COMPLETE — committed f2bfd8a5; 0 regressions |
| 2 | `/search` indexes seeded primitives (E1) + indexing lifecycle messages (E2) + 3 review-found conformance fixes + coverage-process lesson | COMPLETE — suite 4274 pass / 0 regressions; review CLEAR; fail-on-revert proven; committed 65a1f54a |
| 3 | `/search` + REPL introspection findings — full batch (E3–E9 + B + 0558–0561) | ACTIVE — Stage-2: Wave A CLOSED. /arch E8 extension DONE (view-walk union via `impls_for_type_in_view`); **E9 = typecheck-local → new Wave F** (checker prelude-hop; /qa repro → /dev typecheck). Wave B CLOSED + **0562 FIXED** (failure-path arm + on_module_failed hook + predicate extracted; deleted). **Wave C FIXED** (E7 `return Err(e)`; 3 REDs green, fail-on-revert). Unmasked false-green `spec_11_stdlib::macro_vec_empty` (`(vec-len (vec))` genuinely ambiguous — HEAD passed only via the swallow) → E10 **USER RULED 2026-07-12: `(vec-len [])` IS ambiguous and MUST error → re-baseline test to assert the ambiguity error, NO compiler change** (/testing). Wave-C review FOLDED into /review D (proportional — 1-line verified fix). **Wave D LANDED** (E4 one formatter: `src/styled.rs` new — `Role`/`StyledDoc`/`role_style`/`render`; `style_tokens` DELETED; two highlighters collapsed to one Sexp-tree walk; all semantic formatters emit role-spans; colour-off byte-identical, 86 colour-ON fixtures; RED set = exactly the 3 known carries; 0561 italic→dim fixed). **/review D DONE → NEEDS REWORK** (seam architecture CONFIRMED sound: one render/role_style/walk, style_tokens gone, colour-off byte-identical; Wave-C E7 CLEAR). Both dev scope-calls ACCEPTED (round-trip is source-only relayout, not formatter-output reparse; /expand deferral OK). Rework scope (**Wave D2**, one /dev src dispatch): **I1** serializer-SGR-injection at 4 persistence sites (pretty_print → plain `.text()`; colour-ON writes SGR into saved .cl → reload parse-fail; real bug, unit-test-first); **B1** route named §10.3 colour-ON producers through render (cascade report R6, watcher notes, 11 slash-cmd `Error:` R8/R9, agent> composite R14; prompt R13 = documented rustyline deferral); **I2** add K2/K7/K9 colour-ON pins; **I3b** add src/CLAUDE.md one-styling-seam rule. RECORD CORRECTION: colour-ON fixtures = **17**, not 86 (12 K-series + role-table pin + invariants). **Wave D2 LANDED** (I1 `pretty_print_plain` at 4 persistence sites — real colour-ON SGR-injection-into-saved-.cl bug fixed, unit-test-first; B1 cascade report/watcher notes/11 slash-cmd `Error:` R8/R9 via shared `error_line`/agent> R14 composite routed through render; prompt R13 = documented rustyline deferral — SGR would inflate continuation-align width, untestable surface; I2 K2/K7/K9 pins added; I3b src/CLAUDE.md seam rule). Colour-OFF byte-identical (62/62 goldens + 139/139 unit). Dev flagged residual: `broken_status_line` (redefine.rs:1475) still raw R6 → **D2 tail running** (fold-in via render + full-suite gate). Follow-ups (cleanup batch/FIXME): I3a int design-doc stale (/design int), I4 envelope 3-homes (/design), scope-call-2 format_sexp is live format_flat mirror + latent string-escape bug (FIXME → /dev+/qa), S1–S4, seam-doc §5 wording (/arch), 0561 gate-close (/repl). **D2 tail LANDED** (broken_status_line R6 via render; full gate GREEN — 4326/4329, 3 known carries, 0 regressions, 0 warnings). **Wave E LANDED** (0560 reactor overlap pinned via strand-interleave high-water-mark — peak≥2 parked reads, serialized-impl peaks at 1 & still fails; 263×3 green; FIXME 0560 ready-delete). **Wave F LANDED** (E9 = real typecheck bug not normative; fix at impl-site via dedicated `lookup_trait_decl_or_prelude` fallback variant reusing the S78 chokepoint — deliberately NOT the shared `lookup_trait_decl_with_state` because its deftrait-dup-check caller must stay current-module-only for prelude SHADOWING; unit seam test + e2e flip; 661 typecheck green). **/review F CLEAR** (all correctness links verified incl. shadowing) but found latent **7th site** (Imp1: `impl_check.rs:70` HKT arity gate `lookup_type_def_with_state` current-module-only — wrong-arity prelude-globbed HKT target silently skips friendly rejection; same class, same fn, contained) + S1 (`resolve_trait` rustdoc "No fallback" misleading — recurrence vector). **Wave F2 RUNNING** (Imp1 hop + S1 rustdoc + S2 resolve-home-once, unit-test-first). Class then honored on check path. Cleanup carries: Imp2 design/typecheck/traits.md stale (/design tc), S3 negatives (/qa), design/typecheck step1 (/design tc). Then cleanup batch + FIXME closes → Phase 6/7. |
| 4+ | Testing-driven — filled as the user surfaces issues | pending |

The detailed record below (Scope, Arch review, Waves, Outcome) is **Increment 1**.
Increment 2+ append their own Scope/Waves subsections as they open.

## Increment 2 — `/search` indexes seeded primitives + indexing lifecycle messages

**Surfaced by:** user testing — `/search vec-len` returned "no importable symbols
matched 'vec-len'" although `primitives/vec-len` is a real, importable primitive
(`(primitives/vec-len [1 2 3])` → `3`). (Also confirmed live: Increment-1 D3 agent
`max_tokens` fix works — the embedded agent responded fully in the same session.)

**Root cause (confirmed):** `src/session_v4/index_worker.rs` (the Pillar-3
importable-symbol indexer, S91) enumerates the reachable set as **every `.cl`
module on the lib search path ∪ project root** (`resolve_module_file`, ~L288-292).
The built-in `primitives` module is **bootstrap-seeded — no `.cl` file** — so it is
never enumerated → every primitive (`vec-len`, `str-len`, `add-i64`, `vec-get`, …)
is invisible to `/search`.

**User ruling (2026-07-11):** `/search` scope SHALL include the built-in seeded
modules (`primitives`, `macros`) — not just `.cl` files. (Spec §17.19 R10 defined
scope by file-resolution and never addressed seeded modules; the intent — "is
there already a function that does this?" — clearly wants primitives discoverable.)

### E1 — `/search` indexes the seeded modules
- `/repl` scribes the `repl/spec.md` §17.19 R10 clarification: reachable scope =
  lib-path ∪ project-root `.cl` modules **∪ the built-in seeded modules**
  (`primitives`, `macros`). The seeded tables are live in the symbol table already,
  so they need no typecheck-to-index-then-discard dance — index them directly.
- `/dev` (src/) extends `index_worker` to also record the seeded modules' public
  symbols into the index.
- `/testing` repro: `/search vec-len` finds `primitives/vec-len` and offers
  `(import [primitives [vec-len]])`; an already-in-scope exact match is
  marked-but-shown (R13). Owner: `/dev` (src/, int).

### E2 — indexing lifecycle messages
User-directed: make the indexing lifecycle visible. Two messages must exist and
fire:
- **"indexing N modules…"** — the not-ready / partial-results note (already
  required by spec §17.19.3): a `/search` issued before the burn-down completes
  MUST say so, not return a silent empty result. Confirm it is implemented and
  fires.
- **"search index complete."** — a completion message when the background
  burn-down finishes. NEW — `/repl` defines the exact wording + WHEN it fires
  (always, or only after a prior not-ready note was shown?) in `repl/spec.md`
  §17.19.3, bringing that timing sub-question to the user if genuinely open.
- `/dev` (src/) implements/verifies both; `/testing` pins them.

**Design/ownership:** REPL-experience contract → `/repl` owns `repl/spec.md`
§17.19; mechanism (indexing seeded tables, completion signal from the nice-worker
burn-down to the REPL) → int/`src/`, `/dev`. `/arch` light sanity on the mechanism
(no `cranelisp-types` change expected).

### Design outcome (Phase 2/3, 2026-07-11)

**/arch (mechanism, read-only) — APPROVED, no `cranelisp-types`/schema/public-API
change, no Principle-8 risk:**
- E1: index seeded modules by DIRECT read of the live symbol table (bypass the
  typecheck-to-index-then-discard file dance — seeded modules are already
  typechecked-and-mounted). Add `record_preindexed` that counts seeded modules in
  BOTH `enumerated_total` and `indexed` atomically at arm time (else `pending_count`
  undercounts → the not-ready note AND completion fire early). Source the seeded
  list from a new `bootstrap::seeded_importable_modules()` (`primitives` + `macros`;
  exclude root `""` = special-forms-only, and `prelude` = already skipped) — NOT a
  name-literal in `index_worker` (Principle 19). No `.meta` write for seeded rows.
- E2 completion: int-local one-shot latch on `IndicesInner` (`announced` +
  `take_completion_notice()`, check-and-set under the existing mutex), POLLED by the
  `main.rs` read loop at the prompt boundary (single-writer; no worker-side stdout,
  no `ExternalPrinter` TTY-fork). Fire only after a not-ready note was shown this
  session (a `note_shown` latch) — protects the `non_tty` byte-identical goldens AND
  is the semantically right default.

**/repl (contract) — `repl/spec.md` §17.19 scribed:** R10 scope = `.cl` modules ∪
seeded modules; §17.19.3 "indexing N modules…" tightened (N = pending count; MUST
serve the note even on empty partial results; distinct from "no match"); "search
index complete." added (lower-case, trailing period, no count) with async
constraints (no mid-line interleave; global colour gate; non-TTY byte-identical).

**OPEN DECISION FOR THE USER — completion-message timing.** When does
`search index complete.` fire? (a) always/every session; (b) only after a prior
"indexing N modules…" note was shown this session; (c) on-demand (next `/search`).
**BOTH /repl and /arch independently recommend (b)** — least noise, closes only a
loop the user actually saw open, and keeps every existing non-TTY golden untouched
(an unconditional notice lands at a nondeterministic prompt → flakes goldens).
Scribed as (b), PROVISIONAL. `/dev` held on the completion-message timing until the
user confirms. (E1 + the "indexing N…" note don't depend on this.)

**Minor spec reconciliation (→ /repl, same touch):** §17.19.3 opening still says the
index is "armed on first `/search` / first agent activation," but the impl arms
eagerly at REPL startup (main.rs R17). Align in the finalize pass.

**USER DECISION (2026-07-11): completion-message timing = (b)** — `search index
complete.` fires only after a "indexing N modules…" not-ready note was shown this
session. `/repl`'s provisional (b) is now final; `/dev` proceeds.

### Increment 2 waves

| Skill | Crate | Task | Status |
|---|---|---|---|
| /testing | tests/ | QA-first repros | done — E1 primary RED-for-right-reason + R13 guard GREEN; E2 deferred to /dev unit tests (async, not e2e-deterministic — burn-down beats first /search even @30 modules; documented, no racy test). Flagged: `class=prelude-scope-miss` imprecise → /qa vocab note |
| /dev | src/ | E1 + E2 implementation | done — `seeded_importable_modules()`+`record_preindexed`+direct-read; latch (`note_shown`+`announced`+`take_completion_notice()`) polled in main.rs; E1 repros GREEN, 5 unit tests GREEN, non_tty golden GREEN; suite 4268 pass / 0 regressions |
| /review | src/ | Review E1+E2 | done — E1 solid; E2 NEEDS REWORK (small): I-1 seeded-name collision double-count wedges pending; I-2 empty-partial conflates "no match"+note (§17.19.3); I-3 completion not suppressed on non-TTY (byte-identical violation); I-4 agent.md §25 stale; M-1 wording/SGR. No Blockers. |
| /dev | src/ | REWORK: I-1/I-2/I-3/S-1 | done — I-1 disjoint-feed filter (+test); I-2 not-ready note replaces "no match" (repl.rs); I-3 `is_interactive()` gate (+test); S-1 private `pending()` helper. Suite 4270 pass / 0 regressions |
| /dev | src/ | GUARD-CLOSURE (process finding) | done — I-2 selection extracted to pure fns + 3 non-conflation tests; **fail-on-revert CONFIRMED for I-1/I-2/I-3** (each goes RED when its fix is reverted). 35/35 affected + 16/16 index_worker GREEN |
| /review | src/ | Re-check | done — **CLEAR, Increment 2 code done.** 3 findings genuinely closed, no new mirror, fail-on-revert credible. Suggestion #1: retain-filter (I-1 prod path) untested but DETERMINISTIC → guard it (lesson). Suggestion #2: dim-vs-italic + main.rs comment nit → M-1. |

**Increment 2 — remaining FINALIZE items (code done; these are traceability/doc/conformance closure):**

| Skill | Surface | Task | Status |
|---|---|---|---|
| /testing | tests/ | Suggestion #1 (lesson): deterministic retain-filter guard | done — `search_seeded_file_name_collision_does_not_wedge_pending_note` GREEN (deterministic via SUT `wait_for_index_settled`, not a race); fail-on-revert reasoned (wedge → 5s timeout + note). 0 regressions |
| /repl | repl/spec.md | M-1 wording | done — canonical: `; search index complete.` (impl correct), `indexing N module(s)… (results may be incomplete)`, italic classification-comment role, armed-at-startup; de-provisionalized timing (b). Surfaced broader §10.3 dim-vs-italic divergence → FIXME 0561. |
| /dev | src/ | main.rs L408 comment `Dim`→`Italic` | SUBSUMED into FIXME 0561 (same dim/italic issue; fixed when §10.3 reconciled) |
| /design | design/int | I-4: agent.md §25 | done — §25.9 (seeded direct-read feed) + §25.10 (lifecycle latch) added + currency pointer. Noted §25 header still says "DESIGN-ONLY S90" (larger status-prose carry, not blocking) |
| /qa | tests/plan/ + repl/spec.md + tests/CLAUDE.md | Finalize | done — annotations `[Tested]` (honest: unit-pinned cited as unit, completion-wording left pending); PLAN rows + E2 unit-deferral table; `class=enumeration-miss` defined; process-lesson note in tests/CLAUDE.md §"QA-first targeting and deferral discipline". Reconcile clean 646/0 |
| /testing | tests/ | Micro-pass: `class=` → `enumeration-miss` + drop resolved FIXME(/qa) blocks | done — both repros relabelled; 0 remaining `prelude-scope-miss`/`FIXME(/qa)` in search.rs; 30/30 green |

## Increment 3 — `/search` + REPL introspection findings (ACCUMULATING; NOT STARTED)

**Status:** MS1 (E4 styling unification) in PHASE 1 SCOPE (below). Findings E3, E5,
E6, E7 remain recorded for MS2+. Repro recipes recorded so `/testing` authors the
failing guards directly (QA-first), covering the negatives too (S108-Inc2 lesson).

### Increment 3 execution plan — ALL known issues, waved by relatedness — PHASE 1 SCOPE DRAFT

**PHASE 2 arch — SIGNED OFF (2026-07-12).** Design docs: `design/arch/repl-styling-seam.md`
(E4) + `design/arch/resolve-home-enumeration.md` (E3+0558). No `cranelisp-types`/public-API/
cache change in the base (one contingency: if the user ratifies dimming `module/` inside
`:module/Type`, an additive `render_type_spans` in `cranelisp-types` is the honest seam).
E5/E6/E7 confirmed int-local. **E4 recalibration:** §10.3 roles are largely SPEC'd-but-
UNIMPLEMENTED (semantic formatters emit plain strings) → Wave D = "implement §10.3 via the
one seam", not just dedup. E6: the reader-side "don't split `'` in contractions" option is
language-normative → rejected unless the user rules; classifier-side refinement is the
int-local default.

Resolve the whole known-issue set this increment (user, 2026-07-12): E3, E4, E5, E6,
E7 + candidate B + FIXMEs 0558/0559/0560/0561. Decomposed into waves that BUNDLE
related changes (NOT deferred for size — `feedback_no_defer_for_size_decompose`;
drain findings — `feedback_close_fixmes_each_sprint`). Terminal caps CONFIRMED (all
roles incl. italic+dim available). OUT of scope (unchanged since Inc1 — feature work,
not defects): FIXMEs 0050/0052/0463/0553.

**Design phases (Phase 2/3) — the two design-heavy items + spec/normative work:**
| Skill | Task |
|---|---|
| /arch (P2) | (a) E4 styling seam + element→style role model (actors+functions first); (b) E3+0558 scope/enumeration UNIFICATION (the recurring `enumeration-miss`/`wrong-scope-lookup` class → one "resolve-home-then-enumerate over all importable sources" helper). Confirm E5/E6/E7 int-local; public-API/cache impact (expect none). |
| /repl (P3) | E4 styling spec — the ONE byte-reproducible token→style contract, consolidating §1/§1.5/§3.11/§4.1/§10.3/§10.4; resolve 0561. E6 §17.1 classifier-rule refinement. |
| /spec+USER (P3) | E7 multi-form-line semantics (normative sub-question); E6 classifier intent if language-facing. |
| /design int (P3) | E5 harvest §5 contract (design/int/agent.md); 0559 agent.md §6 max_tokens. |
| /qa (P3) | whole-increment test plan (PLAN rows for every E# repro + the E4 byte-identity guards). |

**Phase 5 Stage 1 — QA-first (/testing, sprint-wide):** failing repros for E3
(loaded-module search), E6 (`classify_for_agent("why doesn't…")`→Repl), E7 (`foo bar`
→`:Int 0`), 0558 (prelude-globbed trait sections), + E4 byte-identity guards per
output kind; E5 as feasible. Negatives too (S108-Inc2 lesson).

**Phase 5 Stage 2 — implementation waves (bundled by surface; /dev serial, /review each):**
| Wave | Surface | Bundles | 
|---|---|---|
| A — Agent | src/agent/ | E5 (harvest errored turns) + E6 (classifier misroute, +B FQ-symbol) + `/design`: 0559 doc |
| B — Scope/enumeration | src/ (index_worker, format_trait_display) | E3 + 0558 — both the recurring scope/enumeration class, on /arch's unified helper |
| C — Eval correctness | src/ (eval/cluster/process_form) | E7 multi-form error-swallow → silent `:Int 0` |
| D — Styling | src/ (display/pretty/style) | E4 — the ONE formatter; route all callers; delete parallels; collapse `style_tokens`+`pp`; close 0561 (LARGEST — sequence last) |
| E — Hygiene | crates/cranelisp-intrinsics | 0560 reactor load-sensitive test → deterministic |

**Exit:** all E#/candidate-B/FIXME-0558-0561 resolved with fail-on-revert guards;
0559/0560 closed; suite green (0 regressions); E4 = one formatter+one spec, parallels
deleted; `/arch` scope/enumeration helper backs E3+0558 (class can't recur a 4th time).

---

### Wave G — Prelude ≡ import resolution CONVERGENCE (user pivot, 2026-07-12)

**The reframe (user, correcting my walkthrough of the E9 fix).** Spec §8.6.4/§8.8.1:
the prelude is *just* `(import [prelude [*]])`; a prelude-provided name is in scope
**identically to an explicit import**; whether it's materialised into the module
symbol table or consulted-on-miss is an **implementation detail with ZERO semantic
weight** — **there is no "outer scope" as a language concept.** ⇒ there must be **ONE
lookup that consults the table and transparently falls back to the prelude**, used at
every site. The E3/E8/0558/E9/HKT class is the SYMPTOM of not having it: the codebase
grew **6** fallback-bolted variants (`resolve_with_fallback`, `resolve_terminal_entry_or_prelude`,
`resolve_terminal_fq_or_prelude`, `resolve_current_or_prelude`, `probe_current_or_prelude`,
`lookup_trait_decl_or_prelude`) + a `prelude_fallback` bit through ~93 sites, so each
new site can FORGET the hop. My E9 "shadowing" rationale was **spec-inverted**:
def-over-prelude-name is a §8.6.4 **conflict (compile-time error)**, NOT a shadow (only
`let`/`fn`/`match` shadow, §8.6.3).

**Root cause is a QA coverage gap (user):** "with good tests, needing these variants
would have failed." No positive+negative matrix pinned "prelude name ≡ explicit import
at EVERY resolution site." **Fix coverage FIRST.**

**`/qa` matrix (DONE — PLAN.md §"Prelude ≡ explicit import — resolution-site × polarity
matrix", 21 sites S1–S21):** def-over-prelude IS enforced for `defn`/`defn-`/`deftype`
(one good seam `reject_def_over_binding`, 33/33 green) but **bypassed by `deftrait`,
trait-method names, `defmacro`** (silent accepts). **RED set = acceptance spec for the
convergence:** R1 HKT-arity gate skips validation for prelude target; R2/R3 deftrait-
over-prelude silent register (the inversion, mode-uniform); R4/R5 defmacro-over-in-scope
silent both arms; R6/R7 trait-method-over-in-scope silent both arms; R8 symmetric
import-over-local. GREEN parity rows G1–G8. **Structural acceptance:** no `_or_prelude`
variant NEEDED — fallback intrinsic to one lookup; exactly TWO ops (resolve-a-reference /
may-this-name-be-defined), both prelude-consulting; every def form through the one
§8.6.4 seam; 93-site threading collapsed; `/review` grep guard. FIXME 0558 DELETED (qa).

**Sequence:** (1) `/qa` matrix ✓ → (2) **`/testing` matrix ✓** — 18 tests, **8 RED =
acceptance spec** (R1 HKT arity gate `impl_check.rs`; R2/R3/R6/R7 deftrait+trait-method
bypass `reject_def_over_binding` in `traits/registry.rs`; R4/R5/R8-macro `src/expander.rs`
macro reg misses §8.6.4 seam) + 10 GREEN + §V upkeep (33 tests de-ledgered). Recon: R8-
deftrait GREEN (trait-registry dup-check catches import-over-local, NOT def-over-implicit-
prelude — seam half-fires); R1 anchor miscite → FIXME 0566 (/qa). → (3) **`/arch` RULED** (`design/arch/prelude-import-convergence.md`): ONE lookup =
`ResolutionScope` in cranelisp-types, **fallback intrinsic at scope construction — no
fallback-less public entry point EXISTS** (forgetting the hop becomes unrepresentable,
Principles 18/20). Census grew 6→**12** on scout (3 more hand-rolled copies + int macro
retry) → all collapse to `scope.resolve` projections; `lookup_type_def_with_state` (R1)
+ `lookup_trait_decl_with_state` (R2) DELETE. ONE def seam = `reject_def_over_binding`
relocated to cranelisp-types; typecheck Pass-1 AND int defmacro both call it; routes
deftrait/method (R2/R3/R6/R7) + defmacro (R4/R5) + import-over-local (R8). **Blast radius
SMALL / S108-completable**: stdlib zero self-collision (every def-bearing module already
`(import [prelude []])`-suppresses; prelude.cl is a re-export shell), examples/exemplar
clean, no GREEN test relies on the silent accepts → NO stdlib FIXME, no user escalation,
no design tension; compiler still builds its own prelude. **Public-API**: +`ResolutionScope`
+`reject_def_over_binding` −free `resolve`/`resolve_with_fallback`/`resolve_macro_head`
(land WITH collapse + baseline regen, 1 change-set); **cache no impact, no schema bump**.
Reframed resolve-home-enumeration.md/interfaces.md/bounded-contexts.md/Principles 17&19;
spec-inverted typecheck CLAUDE.md note flagged for /dev deletion. **USER APPROVED ruling
("proceed", 2026-07-12).** → (4a) **`/dev` CS1 (types+typecheck) LANDED**: 12 census fns
collapsed to `ResolutionScope`/`scope_resolve` projections; `lookup_type_def_with_state`
+ `lookup_trait_decl_with_state` + E9's `lookup_trait_decl_or_prelude` DELETED (confirmed);
`reject_def_over_binding` relocated to types, routes defn/deftype/deftrait+methods; R1/R2/
R3/R6/R7 GREEN, R4/R5/R8 still RED (CS2), no other regression (4353p/6f = 3 CS2 REDs + 3
carries); public-api.txt regen; §4.3 CLAUDE.md correction landed; 28 resolve unit tests.
Sensible deviation: free `resolve_with_fallback` kept as thin shim (src/expander still
calls it; removing in CS1 breaks build) → CS2 removes it + 2nd public-api regen. → (4b)
**`/dev` CS2 (src/int) LANDED**: defmacro gate (`reject_defmacro_over_binding`) + recognize_
macro_head over ResolutionScope + imports TraitDecl arm → R4/R5/R8 GREEN; shim
`resolve_with_fallback` REMOVED + 2nd public-api regen (single-line diff); src/CLAUDE.md
retitled off "outer scope". **ALL 8 REDs GREEN; full suite 4363/3f = only the 3 carries;
S20/S21 byte-identity held; full-tree grep `_or_prelude`=0, `resolve_with_fallback`=0-in-
code, `prelude_fallback`=enumerated-set.** Class now STRUCTURALLY impossible. Step-4
repl.rs display-tier alignment deliberately NOT done (ResolutionScope chain-follows to
terminal; display gate needs raw-head/non-chain-followed lookup → would break S20/S21;
documented deviation — display tier keeps its own tiered read, a §3.4 non-resolution
reader). 2 stale `resolve_with_fallback` doc refs flagged: cranelisp-types/CLAUDE.md:83
(/arch), cranelisp-typecheck/CLAUDE.md:169 (/dev-tc). → (5) **`/review` CLEAR** — structural criterion HELD (no fallback-less entry survives; grep 0/0/enumerated),
one seam HELD, step-4 deviation LEGITIMATE, **CLASS CLOSED** (fallback-less resolver
unrepresentable). Non-blocking residuals: **(F1 Imp, /dev-tc)** spec-inverted comment
re-seeded in `impl_check/tests.rs:127` ("may legitimately SHADOW") — landmine, reword;
**(F2 Imp, /arch)** ruling-doc amendments (§3.3 row-12 alignment impossible→record step-4
end-state; §3.4 enumerate find_trait_method_decl + eval.rs hop + 2nd writer ensure_prelude_bit;
+ RULE the display-vs-resolution I-1 divergence: display/`/search`-in-scope-mark/harvest take
prelude head WITHOUT the private filter → a PRIVATE prelude binding shows in-scope while
ResolutionScope rejects it, pre-existing) + stale ref types/CLAUDE.md:83; **(F3 Sugg, /dev-int)**
`eval.rs:560` byte-equiv MIRROR of the display hop (P7 — the 0564/0565 category, live);
**(F4 Sugg, /dev-tc)** checker.rs scope-glue triplication (`with_scope` helper) + stale ref
typecheck/CLAUDE.md:169. Convergence DONE + reviewed CLEAR; residuals are polish/hygiene. The landed E9 fix STAYS (green) but folds into the convergence;
its wrong `crates/cranelisp-typecheck/CLAUDE.md` "reference-hops-binding-doesn't" note
gets corrected in the same change-set. Wave F2 (HKT `_or_prelude` bolt-on) SUPERSEDED by
this — do NOT add a 7th variant; the HKT gate (R1) is fixed by the convergence.

**Separate defect (NOT this class), for triage:** dotted ctor access `Type.Ctor` in
value position → `undefined variable` in EVERY provenance incl. same-module (§8.5.2
violation; zero coverage). Own repro + row needed.

**STANDING coverage-audit CATEGORY (user, 2026-07-12): "coverage by definition
variants."** This prelude case is one instance of a category risk `/qa` must audit
coverage against on a rolling basis — an operation that must behave UNIFORMLY across
a variant family (def forms defn/deftype/deftrait/defmacro/def; resolution sites;
import shapes specific/renamed/member/glob/re-export; provenance explicit-vs-prelude;
output kinds) needs a **variant × {positive,negative} matrix**; its absence lets each
variant grow its own **codepath** — the duplication the project fights hardest (P7/P8
mirrors, E4 one-formatter, resolve-home unification). The matrix is the LEVER that
forces ONE codepath (RED wherever a variant diverges). **`/qa` deliverable (next
dispatch, after /testing):** formalize "coverage-by-definition-variants" as a standing
category in the coverage-process doc (`tests/CLAUDE.md` / `tests/plan/`) — the audit
question + the def-form/import-shape/output-kind families to sweep — so it becomes a
rolling lens, not a one-off. Ties to `/audit`'s whole-context duplication sweep.

---

### Increment 3 — CLOSE-DRIVE tracker (user "proceed" 2026-07-12; drain all to Phase 6/7)

Convergence (Wave G) DONE + /review CLEAR. Remaining drain, driven serially:

- [x] **/arch close batch** — F2 ruling amendments (§3.3 row-12 alignment RETIRED as settled; §3.4 writers/readers corrected); **A.3 RULED a BUG** (spec §8.8.1: prelude = public names only; private-prelude-shown-in-scope is false — named /dev fix); stale ref types/CLAUDE.md:83; **FIXME 0563 actioned+deleted**; seam-doc §5 amended. New minor **FIXME 0567** (/arch, latent — resolution's own terminal-vs-head I-1 filter; /arch does at next types change-set).
- [x] **/dev(src/int) LANDED** — A.3 `is_public()` gate on `lookup_with_prelude_fallback_opt` (single seam; describe_symbol/resolve_entry_arg/is_already_in_scope/**exact_in_scope_hit**/symbol_is_bound/harvest all inherit) + F3 collapse `eval.rs:566` mirror (27 lines→1 call, byte-equiv, goldens+S20/S21 green) + Wave-A mod.rs comment. **USER concern (searching non-public names) PINNED**: e2e asserts `/search <private-prelude>` → NO result row (not just unmarked); fail-on-revert = private `secret` appears as marked row. Bonus: leak also hit bare-symbol introspection (private prelude fn showed bound). 3 unit + 2 e2e; e2e in tests/search.rs flagged for /qa-/testing rehome (fix+test one change-set, METHOD §2.2).
- [x] **/dev(typecheck) LANDED** — F1 comment de-inverted (idempotency-vs-name-freedom framing; no assertion changed) + F4 `with_scope` helper (3 sites single-sourced, behaviour-identical, 661 green) + stale ref typecheck/CLAUDE.md:169 fixed. Minors: +1 ambient `result_large_err` (left unsuppressed to match ~102 peers); **NEW minor** stale "outer scope" doc-comment on `scope_resolve` (checker.rs ~918-953) — fold into later doc pass.
- [x] **/testing LANDED** — E10 re-baselined to 2 tests (neg-ambiguity `macro_vec_empty_neg_ambiguous_element_type` + `macro_vec_empty_pinned_ok`, §3.11.1, clean spec-conformant error, no compiler change; minor: `__expr` binder leak in msg — cosmetic). Dotted-ctor: committed RED `spec_08_modules::dotted_constructor_in_value_position_resolves` (12 lines; §8.5.2; `class=enumeration-miss`; dotted resolver has field-accessors but OMITS constructors; primary attribution typecheck) — **fix pending /qa attribution confirm → /dev; carry as known-defect guard if non-trivial**.
- [ ] **/design(int)** — §5.5(4) harvest doc (agent.md); I3a `design/int/terminal-styling.md` stale (Wave-D); I4 envelope 3-homes drift.
- [x] **/qa LANDED** — standing category in tests/CLAUDE.md; 0566 corrected+deleted (+R1–R8 all-green verified); **dotted-ctor attribution CONFIRMED typecheck** (`resolve_dotted_field_accessor` — field accessors keyed, constructors never `Type.Ctor`-keyed) → **CARRY early-S109** (evidence-gated: needs adt.rs registration-model + resolver arm + codegen-key ripple, not small; committed guard = record; PLAN §VI); search e2e ACCEPTED in place; **FIXME 0568 filed (/spec)** [S102]→[Tested+Neg]. Corrections routed to /testing (dotted-ctor locus format, I-1 past-tense — fold into §V sweep).
- [ ] **FIXME drains** — 0560 (/dev-intrinsics delete, Wave E done); 0561 (/repl delete, Wave D2 done); 0564 (/audit action Duplication-attribute extension); 0565 (/review action checklist cue).
- [~] **/design(int) RUNNING** — §5.5(4) harvest contract; I3a terminal-styling.md stale (teaches forbidden pattern) → styled::render seam; I4 envelope 3-homes (a: document intentional split / b: FIXME→/dev).
- [x] **METHOD CHANGE LANDED (user 2026-07-12): /qa maintains coverage ANNOTATION band directly — no FIXME cycle.** Edited `.claude/commands/qa.md` (boundary exception + two-sided-traceability bullet) + root CLAUDE.md §Traceability + cross-ref notes in `.claude/commands/spec.md` & `repl.md` (annotation band is a shared /qa-maintained band; prose stays owner-gated). **0568 = first case of new path** (/qa applies §8.6.4 [Tested+Neg] tags directly + deletes 0568).
- [x] **0568 CLOSED via new direct path** (/qa applied 3 §8.6.4 [Tested+Neg] tags, verified GREEN, deleted FIXME, reconcilers clean; +spec/CLAUDE.md carve-out added).
- [x] **FIXME drains (methodology/notation)** — 0565 (/review cue) DONE; /testing 2 comment corrections DONE (locus grep-clean; 2 I-1 tests past-tensed, 0543/E3 guards untouched).
- [ ] **Remaining trivia (2 micro-/dev)** — 0560 (/dev-intrinsics FIXME delete, Wave E fix verified); scope_resolve stale "outer scope" doc-comment (/dev-tc). Fold into Phase-6-adjacent or final micro-touch.
- [x] **Phase-6a /repl DONE** — CONFORMS (styling/`/search`/§8.6.4-errors all conform to repl/spec.md); **0561 reconciled+deleted** (2 stale "italic"→dim prose); demos replay green. 2 gap FIXMEs (next-incr, /dev low-sev): 0568 `__expr`-leak in ambiguity msg, **0569 /search macro rows show bogus `:primitives/Int`** (+/qa /testing repro, §17.19.2 spec pin owed by /repl).
- [~] **Phase-6a /audit RUNNING** — cranelisp-typecheck rotation assessment (convergence major-arc) + action 0564 (Duplication-attribute 3-facet+spec extension).
- [ ] **Final trivia + /qa note** — 0560 (/dev-intr FIXME delete); scope_resolve stale doc-comment (/dev-tc); /qa PLAN note (in-scope-via-prelude control ← public re-export, provenance slip).
- [~] **GATE FINDING (full-suite run 2026-07-12, 4370t/4366p/4f):** RED set = 3 known (ownership_reuse 0528, deftype_ctor_trailing S107, dotted-ctor S109 new carry) + **1 surfaced-by-I-1**: `search::search_loaded_module_in_scope_exact_match_still_marked_not_imported_neg`. NOT an I-1 regression — the fix correctly stops the prelude's PRIVATE imports from leaking downstream (§8.8.1: prelude provides PUBLIC names only). The Wave-B control's fixture relied on that leak: prelude `(import [foo [other]])` (private) made `other` falsely in-scope. **Re-baselined (/testing): fixture prelude `import`→`export [foo [other]]`** (§8.8.1/§8.4.0/§8.9.1 cited + empirically confirmed bare `other` unbound under private import; 35/35 search green). macro_vec_empty carry CLEARED (E10 GREEN). **GATE CLEAN: full suite 4370t/4367p/3f = exactly the 3 known carries (ownership_reuse 0528, deftype_ctor_trailing S107, dotted-ctor S109-carry); agent e2e 73/73.** /testing flagged /qa PLAN note: "in-scope-via-prelude control must derive scope from a PUBLIC re-export, not private import" (provenance slip, coverage-by-definition-variants lens).
- [ ] **Phase 6/7** — user-facing assessment (/repl,/port,/stdlib,/examples,/docs) + /audit rotation dispatch (rotation TBD — pick at 6a) + close (USER approval; nothing commits until then).

**USER-REVIEW GATE — CLEARED (user signed off 2026-07-12, "looks good - happy to
proceed").** The E4 styling spec (`repl/spec.md` §10.3, 15-role byte-reproducible
table; 0561 resolved) is the LOCKED contract. Wave D unblocked. (Gate: spec was
presented for review before lock-in, per the hard requirement.)

**Open decisions (gate their waves, not the whole plan):**
- **W-C (user) — RULED 2026-07-12:** multi-form line → agent (if active) else
  sequential-eval-abandon-on-first-error; single form (incl FQ) → eval. See E6/E7.
- **W-D/W2 (user) — Q1 REFRAMED (user: "why does cranelisp-types know rendering?"):**
  types must NOT know styles. So type-annotation `module/`-dim is EITHER (a) types
  exposes a role-NEUTRAL STRUCTURAL decomposition (`ModulePrefix`/`TypeName`/punct
  spans — structure, not colour) + int maps structure→style (module-dim works inside
  `:module/Type`; types stays rendering-agnostic; single walk, Principle 7), OR (b)
  type annotations WHOLLY CYAN + module-dim only on bare FQ names (int holds
  `FQSymbol`; ZERO types change). `/sprint` recommends (b) — simplest, fully respects
  the objection, module paths still dimmed where they most appear (search rows,
  symbol display); (a) only if full consistency inside type annotations is wanted.
  **RULED 2026-07-12: (b)** — type annotation is a SINGLE cyan construct (no internal
  decomposition); module-dim on bare FQ names only; ZERO `cranelisp-types` change.
- **Candidate hygiene (user opt-in):** the 2 pre-existing cross-crate RED guards
  (`deftype_ctor_trailing_form…` /frontend-S107; `chaining_toggle_off…` 0528
  /typecheck-S103) — fold in as an extra wave, or leave to their owners? (Off-theme;
  default = leave.)

### E3 — CONFIRMED DEFECT: `/search` drops already-loaded modules' not-in-scope symbols

**Surfaced by:** user testing — `/search count` returned every substring match
(`test-count`, `bit-count`, `popcount`) but NOT the exact `count`
(`collections.vec/count`), which `/exports collections.vec` confirms exists and is
importable.

**Root cause (confirmed in code):** `src/session_v4/index_worker.rs:548` — branch
(a): `if shared.scheduler.is_registered(module) { mark_skipped(module) }` records
ZERO entries for an already-loaded/registered module. The comment claims "its
`.meta` is read later," but nothing ever reads it later (`mark_skipped` adds it to
the `indexed` set; never revisited). So every loaded module contributes NO symbols
to the importable index; its importable-but-not-in-scope symbols are unreachable via
`/search` (only the R13 live-table path surfaces them, and only when in scope). In
the user's session `collections.vec` was loaded (prelude uses its fns), so `count`
(importable, not bare-imported) was invisible; the UNloaded `collections.vec.test`
indexed normally (hence `test-count` showed).

**Spec backing:** §17.19 R10 — importable-but-not-in-scope symbols MUST be surfaced.
`foo/count` (foo loaded via another import, count not imported) is importable → MUST
appear. Violated.

**Minimal repro (deterministic — recorded for QA-first):**
```
foo.cl:      (export [primitives [*]]) (defn count [x] x) (defn other [x] x)
prelude.cl:  (export [primitives [*]]) (import [foo [other]])   ; loads foo, count NOT in scope
/search count   → "no importable symbols matched 'count'"   [BUG: should surface foo/count + import]
/search other   → found "already in scope"                  [control: in-scope path works]
```
Negatives to also pin (lesson): loaded-not-in-scope symbol IS found after fix; the
in-scope exact match still marked-but-shown (R13 not regressed); an UNloaded
module still indexes.

**Fix direction:** branch (a) should DIRECT-READ the registered module's public
symbols from the live symbol table into the index (the Increment-2 seeded pattern,
extended) instead of `mark_skipped`-empty. **`class=enumeration-miss` — SECOND
instance of this class in the `/search` indexer** (Inc2 = seeded modules; E3 =
loaded modules). Recurrence → `/arch` glance at unifying "enumerate ALL importable
sources" (seeded ∪ file ∪ loaded) so it cannot recur a third time. Owner: `/dev`
(src/, int).

### E5 — CONFIRMED: agent harvest omits recent failed/errored turns (can't debug type errors)

**Surfaced by:** user testing — typed `(defn rotations …)` which failed
(`type error at 34..35: ambiguous type; add an annotation…`), then asked the agent
"why doesn't that typecheck?" The agent had NO visibility into the failed form or
its error — it hallucinated context (scouting for `rem`/`mod`) and said "I haven't
seen an attempt from you… paste the attempt." Debugging a type error is the single
most valuable in-REPL agent function, and the agent is blind to it.

**Root cause (confirmed in code):** `src/agent/harvest.rs::harvest_context`
assembles context ENTIRELY from committed session state — mentioned symbols,
in-scope defns (`push_in_scope_block`), full module source. Grep for
`error|failed|transcript|history|diagnostic|errored` → nothing: NO recent-turn /
errored-form / compiler-diagnostic inclusion. A failed defn never commits → absent
from the symbol table → absent from the harvest.

**Fix direction:** include the recent errored turn(s) in the agent's turn context —
the failed form's source text + its compiler diagnostic (design/int/agent.md §5
harvest, or the turn-assembly in `agent/request.rs`). Consider a bounded ring of
the last N REPL turns (input + result/error), surfacing the errored ones. Owner:
`/dev` (src/agent/, `--features agent`); `/design`(int) for the §5 harvest contract.
Aligns with the standing principle: agent awareness lives in harvest/context.

### E6 — CONFIRMED DEFECT: agent classifier misroutes prose to the REPL (should route to the agent)

**Surfaced by:** user testing (user: "that sentence should have been routed to the
agent"). With the agent ACTIVE, `why doesn't that typecheck?` was evaluated by the
REPL (yielding a garbage `:primitives/Int 0`) instead of being routed to the agent;
the user had to fall back to explicit `/ask`.

**Root cause (confirmed end-to-end):** `src/agent/mod.rs::classify_for_agent`
(spec §17.1, the designed auto-router) routes any buffer with a COMPOUND form
(`Sexp::List`/`Bracket`) to the REPL as "code" (mod.rs:134-139). But the apostrophe
is the quote reader-macro: `reader.rs:870` `read_quote` desugars `'x` →
`Sexp::List([quote, x])`. So `doesn't` → `doesn` + `(quote t)` — a `List` — and
`any_compound → Repl` fires, misrouting the whole prose sentence to eval. (Plain
prose of unknown words routes to the agent correctly — unit-tested:
`"how do I define a function"` → `Agent`. The trap is specifically a **reader-macro
char inside an English word**: `'` (contraction → quote), `` ` ``, `~`, and `:` in
`was:` — the second transcript sentence hit `:` + `'` both.)

**Spec backing:** §17.1 — the classifier routes prose/unknowns to the agent when
active; this sentence is prose and should have routed. DEFECT.

**USER RULING (2026-07-12) — unifies E6 + candidate B + E7 into ONE rule, replacing
the `any_compound` heuristic entirely:**
- **Exactly ONE form (bare OR fully-qualified) → REPL eval/introspect.** (Fixes B: a
  single FQ symbol introspects, never routes to the agent — so the classifier's
  single-form Repl decision must NOT depend on `symbol_is_known`.)
- **Anything else (>1 form, or unparseable prose) → the AGENT if active; if no agent,
  eval sequentially and ABANDON on the first error** (surface it — no swallow, no
  silent `:Int 0`). (Fixes E6: prose is multi-token → Agent. Fixes E7's no-agent path.)
Owner E6/B: `/dev` (src/agent/mod.rs `classify_for_agent` — the rule is now "one form
→ Repl, else → Agent", no `any_compound`, no reader change). **Repro:** unit-test
`classify_for_agent("why doesn't that typecheck?")` → `Agent`; `classify_for_agent`
of a single FQ symbol → `Repl` (deterministic, no model). The reader-side
`'`-in-contraction split is NOT touched (arch: language-normative — rejected).

### E7 — CONFIRMED DEFECT: multi-form REPL line swallows per-form errors → silent `:Int 0`

**Surfaced by:** isolating E6 — the misrouted sentence produced `:Int 0` rather than
a visible error. That masking is a SEPARATE, general REPL defect (NOT agent-related;
reproduces in the default build):

| Input | Result | Problem |
|---|---|---|
| `foo` | `Error: undefined variable: foo` | ✓ correct (single form) |
| `foo 2` | `:primitives/Int 2` | `foo`'s error SWALLOWED; shows last form |
| `2 foo` | `:primitives/Int 0` | undefined `foo` → silent `0` |
| `1 2 3` | `:primitives/Int 3` | multi-form line shows only last value |
| `foo bar` | `:primitives/Int 0` | both undefined → bogus `0` |

**Mechanism (corrected by /arch P2 — NOT a typecheck bypass):** `src/eval.rs::eval`
(~L185-208) DOES raise the per-form error, but the multi-form arm wraps it as a
fake `EvalResult::Val { value: 0, ty: Int }` carrying the error as a WARNING (an
explicit `// TODO`), and then L207 (`*r.warnings_mut() = all_warnings`) CLOBBERS that
warning because the `Err` branch never extends `all_warnings`. So the line surfaces
only the last form's value (or fake `0`) and the per-form error is dropped. Two
small int-side sub-defects, both in `eval()`; either user ruling lands entirely there.

**Spec backing:** Design Principle "Self-documenting REPL — No valid language
construct should produce an opaque error" + `src/CLAUDE.md` §Error Handling
(undefined variable MUST surface). Open normative sub-question for the USER: what
should a multi-form REPL line DO — reject as one-form-only (cluster model: "a
non-`(begin)` REPL input = one-form cluster"), or evaluate all + show last but
SURFACE every per-form error? Either way the swallow + silent `:Int 0` is a defect.
Owner: `/dev` (src/, int — `eval.rs` L185-208). **USER RULING (2026-07-12):** part of
the E6 unified rule — a multi-form line reaches `eval` ONLY on the no-agent path
(agent-active multi-form → agent). There, eval SEQUENTIALLY and ABANDON on the first
error (surface it; no fake `Val{0}`, no warning-clobber at L207). Single form
(incl FQ) never hits this path (→ direct eval). **Repro (default/no-agent build):**
`foo bar` → must surface `undefined variable: foo`, not `:Int 0`.

### E8 — CONFIRMED DEFECT (Stage-1): type-side `; impl:` view drops prelude-globbed trait impls

Bare `Int` (test-standard prelude) → `:primitives/Int ; type` with NO `; impl:`
section; §4.1.3 requires `; impl: Display Eq Num Ord` (all prelude-globbed). The
Decision-45 Pattern-B view-walk enumerates candidate traits from the ASKING scope
and misses the prelude outer-scope hop. Committed RED:
`repl_introspection::type_impl_section_includes_prelude_globbed_trait_impls_probe`.
`class=prelude-scope-miss`, locus `src/repl.rs::format_builtin_type_display`. SAME
family as E3/0558/Inc1-D1 but a DISTINCT locus — `/arch` scoped Pattern-B out of the
0558 home-rooting fix, so E8 needs a small `/arch` design extension (does the
`; impl:` view-walk get a prelude hop? §4.1.3 says it MUST) BEFORE its /dev fix.
**Folded into Wave B** (scope/enumeration) with a `/arch` design touch first.

### E9 — SUSPECTED (Stage-1 observation, needs repro): `impl` of a prelude-globbed trait fails to resolve

`(impl <prelude-globbed-trait> <local-type>)` fails check-time: `unknown trait:
Display` from `user` scope — the `impl`-form's trait resolution misses the prelude
outer-scope hop (a possible THIRD face of the class, this one on the CHECK path, not
display). NOT e2e-reproduced yet. → `/qa`/`/testing` produce a minimal repro; if
confirmed, fold into Wave B (or its own wave) as `class=prelude-scope-miss`; if it
turns out language-normative (impl trait-resolution scope), route to user/`/spec`.

### Candidate bundle items (to firm up as findings accumulate)

- **B — bare qualified symbol routes to the agent, not direct introspection.** In
  two transcripts a bare FQ symbol (`primitives/vec-len`, `collections.vec/count`)
  triggered `agent> /sig …` rather than the REPL printing its `:Type … ; defn`
  directly (§4.1 self-documenting gap?). Agent-session only; needs isolation before
  it's firm. (The NL-→-`:Int 0` half of this cluster graduated to E6 above.)
- **Diagnostics visibility — DECIDED: keep as-is** (user, 2026-07-12). Leave the 5s
  settle-wait; the indexing diagnostics stay a rare-case affordance (only surface
  when indexing genuinely exceeds the settle window). No change. NOT in scope.
- **FIXME 0561 (dim-vs-italic §10.3).** REPL-experience ratification; could bundle
  if Increment 3 touches REPL display (E4 makes this likely), else stays its own FIXME.

### E4 — Pretty-printing / presentation-path consolidation (user, 2026-07-12)

**Surfaced by:** user observation that different REPL commands use different
presentation formats — a possible duplicated-code-path smell (same class as
Inc1 D2's two-envelope constructor display).

**Survey (read-only, done at triage — NOT a full map):**
- **Already unified (no action):** the names-only grouped-symbol lists — `/list`,
  `/imports`, `/exports` all render through the shared `append_name_category`
  (§3.3 L0–L4 layout), guarded by cross-command byte-identity tests
  (`prelude_group_and_category_share_layout_body`). So this family is NOT the
  duplication.
- **Suspect family — the `:Type name [; metadata]` renderers.** Multiple entry
  points format the "typed symbol" line with divergent trailing metadata:
  `format_def_entry` (bare symbol / `/sig` / `/info`, `src/repl.rs`),
  `render_search_row` (`/search`, repl.rs:1251), `handle_doc` (repl.rs:769),
  `format_scheme_display`/`format_type_qualified` (`src/display.rs`),
  `format_related_section`/`format_trait_related_sections` (the `; match:`/`; impl:`
  /`; defn:` sections). Concrete drift from the transcripts: the DOCSTRING renders
  `; defn - <doc>` (`/sig`) vs `<name>: "<doc>"` (`/doc`) vs absent (`/search` rows);
  the `:Type name` envelope's trailing structure differs per command.

**In-scope surfaces (user, 2026-07-12): result values, `/sig`, `/info`, `/sexp`.**
These map to THREE presentation subsystems:
1. **`format_eval_result` / `format_eval_result_body`** (repl.rs:2429/2457) — result
   VALUES (`:Type value`) + the bare-symbol Def echo → `format_value` /
   `format_scheme_display` (display.rs).
2. **`format_def_entry`** (repl.rs) — the `:Type name ; class` introspection line;
   **already shared by `/sig` (repl.rs:756) AND `/info` (repl.rs:1547)**.
3. **`crate::pretty::pretty_print`** (the `pp_*` code-printer, pretty.rs) — `/sexp`
   (repl.rs:1461) and `/source`.

**Already single-sourced (confirm, don't re-do):** `/sig`+`/info` → `format_def_entry`;
the Type→string atom → `render_type` (cranelisp-types, the single walk, FIXME 0420);
`/sexp`+`/source` → `pretty_print`.

**Prime suspect (the D2-class drift):** subsystem 1 (`format_eval_result`, values +
Def echo) vs subsystem 2 (`format_def_entry`, sig/info) — TWO renderers of the
`:Type <thing> [; metadata]` envelope. repl.rs:747 already carries a "the two
surfaces" comment acknowledging the coupling. Determine whether the envelope /
`; class` / docstring rendering is duplicated-with-drift (→ unify onto one core, the
D2 lesson: one formatter per concept) or legitimately different, and how `/sexp`'s
code-form presentation should relate.

**GOVERNING PRINCIPLE (user, 2026-07-12) — the north star for E4:** ONE formatter
conforming to ONE styling spec, for all **token-styled** REPL output — output with
per-element syntax roles: values, introspection (`/sig`/`/info`/bare symbol), code
(`/sexp`/`/source`), search rows, errors/warnings. Every such line routes through a
single formatting/styling core so a role is defined once, applied once, and cannot
drift. Subsumes E4a (the styling contract), FIXME 0561, the two-highlighter
duplication, and the fragmented display specs.

**EXPLICIT SCOPE BOUNDARY (user, 2026-07-12):** the **pure symbol lists** — `/list`,
`/imports`, `/exports` — are NOT in the styling-formatter scope. They are a distinct
**uniform-layout + line-break** concern (every name rendered identically: bold header
+ default-weight names, §10.3; grouped/column-wrapped), already unified via
`append_name_category`. No per-token styling applies to them. Leave them alone —
they are the LAYOUT concern, not the STYLING concern. (`/search` rows DO carry token
roles — `:Type` cyan, module-path, import form — so search is IN the styling scope.)

**What it replaces (the current fragmentation, styling scope only):**
- **Formatters (many):** `format_value`/`format_result_value`/`format_scheme_display`/
  `format_ctor_display`/`format_adt_value` (display.rs), `format_def_entry`/
  `format_overloaded_variants`/`format_related_section`/`format_eval_result`/
  `render_search_row` (repl.rs), `style_tokens` + `pp`/`style_atom` (pretty.rs — two
  code highlighters). Each applies styles semi-independently. (`append_name_category`
  is EXCLUDED — the separate list-layout concern above.)
- **Specs (fragmented):** §1/§1.5 (values), §4.1 (introspection), §3.11 (code layout
  only), §10.3 (REPL-output style roles), §10.4 (styled universal output) — no single
  normative styling contract; the code-highlighter token roles are unspec'd (impl-only).

**The real task (execution-time, `/arch`-led — this is a foundational consolidation,
likely the LARGEST Increment-3 item; may warrant its own increment/careful waving):**
1. `/arch` designs the single formatter seam (one styling/render core all output
   routes through) + the element→style role model. Actors-and-functions first
   (per the standing principle): what emits styled output, what the role vocabulary
   is, one application point.
2. `/repl`(+`/spec` if language-facing) scribes the ONE styling spec — the normative,
   byte-reproducible token/element→style contract (the E4a role table: head=bold,
   literals=coloured, source-comments=italic, REPL-metadata=dim, FQ-module-prefix=dim,
   type-annotation=cyan(+enhancement), …), consolidating §1/§1.5/§3.11/§4.1/§10.3/§10.4
   into (or cross-referencing) one authority.
3. `/dev` (src/, int) implements the single formatter; deletes the parallel
   formatters/highlighters, routing all callers through it; closes 0561.
4. `/qa`/`/testing`: byte-identity guards across output kinds (the discipline §3.11
   already models for layout, extended to styling).
`class=presentation-drift`. Do NOT pre-judge which current divergences are legitimate
vs drift until the `/arch` map — but the TARGET is one seam, one spec.

**E4a — the code-highlighter styling contract (user, 2026-07-12): "this should be
well-specified."** Currently the code pretty-printer's token→style mapping is
IMPLEMENTED but NOT normatively specified — §3.11 pins only `let`/`match` LAYOUT
(and just says "colour on adds SGR spans"), and §10.3 specifies REPL-OUTPUT roles
(prompt/result-type/classification-comment/headers/errors), NOT the code
highlighter's per-token roles. So the highlighter's colour contract lives only in
`pretty.rs` — and in TWO copies (`style_tokens` char-scanner vs `pp`/`style_atom`
tree printer). E4 must (1) SPEC the token→style contract normatively (new §10
subsection or §3.11 extension), (2) UNIFY onto ONE highlighter (prefer the
structural `Sexp`-tree path — string-scanning is fragile), (3) resolve FIXME 0561.

**Desired styling roles (user contract — to be scribed + made byte-reproducible):**
| Token | Style | Current state |
|---|---|---|
| Head of apply form (1st symbol) | **bold** | EXISTS (both paths bold `in_head`) |
| Literals (int/float/bool) | coloured (yellow) | EXISTS |
| Literals (string) | coloured (green) | EXISTS |
| Type annotations (`:Type`, `:module/Type`) | special highlight | EXISTS (cyan); user wants it well-specified + possibly enhanced |
| Comments | **italic** | IMPL italic; §10.3 says DIM → FIXME 0561 |
| **Module-path prefix in FQ names** (`primitives/` in `primitives/vec-len`) | **diminutive (dim)** | NEW — no role today |

**FIXME 0561 refinement (comment-type distinction):** §10.3's DIM is for REPL
STRUCTURED-METADATA `;` lines (`; defn`, `; match:`, `; impl:`) — "not comments in
the source-code sense." The user's ITALIC is for SOURCE-CODE comments in the code
printer (`/sexp`/`/source`). These are DIFFERENT comment types → likely resolve as:
source comments = italic; REPL classification/metadata = dim (§10.3 stands). The
0561 drift is the impl over-applying italic to the metadata role. Confirm at scribe
time. **`class=presentation-drift`** (the two-highlighter mirror + spec gap).
OPEN sub-question for the user (parked): what "special" highlighting for type
annotations beyond the current cyan — e.g. dim the `module/` prefix inside
`:module/Type` too (composing with the FQ-module-path role)?

## Stdlib request backlog

STOOD UP (Increment 1): `stdlib/BACKLOG.md`, `/stdlib`-owned. Columns: function |
Clojure analog + signature | use-case that surfaced it | priority (P1/P2/P3) |
status (`requested → in-increment → landed`). Landed rows kept in a provenance
section; pointer added to `stdlib/CLAUDE.md`.

**Capture flow (a):** as testing surfaces "missing library function" requests,
`/sprint` batches them and dispatches `/stdlib` to append + groom (only `/stdlib`
edits `stdlib/`). `/sprint` pulls high-priority `requested` rows into scope when a
stdlib increment is planned. **Routing dividing line** (from the file): writable in
Cranelisp from existing primitives + special forms → backlog; needs a new
primitive / special form / language change → a usability FIXME in
`design/arch/fixmes/`; wrong output / crash / spec violation → a committed failing
test, not the backlog.

## Scope

A small, coherent defect-fix increment. All three code defects live in the `src/`
binary/int surface; each is spec- or API-anchored and carries a committed guard
(or a specified one). Delivers:

**D1 — Seeded ADTs drop the `; match:` section (spec §4.1.3).**
`Option`/`Result`/`IO` (primitives-seeded ADTs) introspect with the primary line
only, omitting the `; match:` constructor section that a user `deftype` shows.
Root cause: `src/repl.rs::format_type_display` looks up constructors via
`lookup_type_def_chain` from `current_module_path()` (the user module) and that
chain-follow takes no `prelude_fallback` — so it never reaches the type's resolved
home (`primitives`). Guard (RED, committed):
`tests/repl_introspection.rs::seeded_option_bare_lookup_includes_match_section`.
Owner: `/dev` (src/).

**D2 — Nullary constructors drop the module qualifier and `; deftype` (spec §4.1.2),
via a DUPLICATE code path.** A bare nullary ctor (`None`, user `Red`) renders
`:user/Color Color.Red` instead of `:user/Color user/Color.Red ; deftype`. Root
cause: `src/eval.rs` (~L628) special-cases `field_count == 0` and routes nullary
ctors to runtime evaluation + the value-display envelope (`src/display.rs`
~L371/527: `:{type} {ctor}`) instead of the introspection envelope
(`src/repl.rs` ~L2560 `format_def_entry` Constructor arm:
`:{type} {module}/{ctor} ; deftype`). **The fix is to COLLAPSE the duplication**
(route bare nullary lookup through the same `format_def_entry` arm as applied
ctors), not to patch the value path — per the user's directive that the divergence
is a duplicate-code-path smell we do not want. The `display.rs` value path stays
for genuine runtime values (§1.5, e.g. `(Some 42)`). Guard (RED, committed):
`tests/repl_introspection.rs::nullary_constructor_bare_lookup_shows_deftype_and_qualified_home`.
Owner: `/dev` (src/). `/review` verifies no new mirror is introduced.

**D3 — Embedded agent: every Anthropic request fails (missing `max_tokens`).**
`src/agent/provider.rs::build_request` assembles the rig `CompletionRequest`
without `.max_tokens(...)`, which Anthropic requires — both `complete` and
`complete_streaming` are dead against Anthropic. Fix: add `.max_tokens(<named
constant>)` to the single builder. **NOT e2e-reproducible** (the stub provider
bypasses `build_request`; CI can't call the live API) — the guard is a
`#[cfg(test)]` unit test in `src/agent/provider.rs` asserting
`build_request(...).max_tokens.is_some()`, authored WITH the fix. Tracked by
FIXME 0554. Owner: `/dev` (src/, `--features agent`).

**C1 — Coverage-process repair (the root cause D2 slipped through).**
`nullary_constructor_bare_lookup_dot_notation` under-asserts (only
`.contains("Color.Red")`, passes on the buggy output) and §4.1.2's `[Tested]`
annotation over-claims (the cited test validates only §1.5's dot-notation).
Re-point the §4.1.2 annotation onto the new §4.1.2 guard once green; assess the
sibling applied-ctor test for the same under-assertion. Tracked by FIXME 0557.
Owner: `/qa`.

**M1 — Failure-ledger disposition (methodology decision).**
`tests/plan/ledger.md` has grown to ~4400 lines of append-only per-sprint RED
narrative — most describing tests long since GREEN. The ledger has two functions;
both move onto the **permanent test corpus**, which is a strictly better substrate
(the ledger by its own discipline holds only *currently-failing* tests, whereas
reproduced defects live in the suite forever — GREEN or RED):

1. **Regression triage** (expected-RED vs new-breakage) → the inline
   defect-comment + open-FIXME convention, already stated in root `CLAUDE.md`
   §Testing ("a genuine regression is any RED that does not trace to a known open
   defect"). No separate file needed.
2. **Frequency / locus / recurrence analysis** → a structured `// defect:`
   notation on repro tests (beside the existing `// spec:`), e.g.
   `// defect: class=<class> locus=<file:line> found=S<NN> owner=/<skill>`.
   Enables `grep class= | uniq -c` (recurring-class → `/arch`-escalation signal),
   `grep locus=` (hotspot seams), and per-sprint defect trend — over the FULL
   history, not just current REDs. The one design task: `/qa` owns a short
   **controlled vocabulary** for `class=` (free-text fragments and defeats
   `uniq -c`); `/testing` applies the notation at repro time.

**Proposed:** retire the narrative ledger; land the `// defect:` notation +
`/qa`-owned class vocabulary; migrate the ledger's anti-pattern discipline text
(no "flaky"/"pre-existing"/"timing-sensitive" — user directive 2026-04-21) into
`tests/CLAUDE.md` or `sprints/METHOD.md`; update root `CLAUDE.md`'s ledger
pointer. Owner: `/qa` (owns the file + coverage process + class vocabulary) +
`/testing` (applies notation, retro-tags existing repros opportunistically).
**Decision is the user's** — see §Notes.

### Out of scope (deferred, unrelated to this defect increment)

- FIXME 0050 (`/int` — List/Seq pretty-printer, aspirational), 0052 (`/repl`),
  0463 (`/examples`), 0553 (`/typecheck` — instantiate-at-types entry point).
  None are defect fixes; carried, not actioned here. Target: a future feature
  sprint.

## FIXME debt

| FIXME | Target skill | Status | Notes |
|---|---|---|---|
| 0554 | /dev | RESOLVED (W2, deleted) | D3 landed: `AGENT_MAX_TOKENS=65536` + unit guard. |
| 0559 | /design | open (filed W2) | agent.md §6 doesn't state the `max_tokens` request contract the D3 test cites; doc-side, non-blocking. |
| 0560 | /dev | open (filed W3) | `reactor::two_async_reads_overlap_max_not_sum_one_thread` load-sensitive (passes isolated, fails contended) — pin deterministically. Pre-existing, not S108; carried. |
| 0557 | /qa | open | C1 — nullary-ctor lookup test under-asserts + §4.1.2 annotation mis-pointed. |
| 0558 | /qa | open (filed W1) | Sibling wrong-scope class in `format_trait_display` (repl.rs:2748) — prelude-globbed traits may drop `; defn:`/`; impl:`. Arch-scoped-OUT of S108; repro+fix next sprint. |
| 0050 | /int | open (out of scope) | Aspirational; not this sprint. |
| 0052 | /repl | open (out of scope) | Not this sprint. |
| 0463 | /examples | open (out of scope) | Not this sprint. |
| 0553 | /typecheck | open (out of scope) | Feature work; not this sprint. |

## Architecture review (Phase 2) — SIGNED OFF, Phase 3+ may proceed

`/arch` verdict (2026-07-11). No `cranelisp-types` public-API or cache-schema
change for any item; no Principle-8 risk (all corrections toward specified target
using existing mechanisms).

- **D1 — APPROVED, int-side only.** Reject the `prelude_fallback`-parameter option
  on `cranelisp-types` (widens the edge + second-resolves an already-resolved fact,
  Principles 2/7). Fix = **root the constructor chain-lookup at the resolved home
  `module` the function already holds**, not `current_module_path()`. At the home
  the TypeDef is local (chain terminates depth 0), so the prelude question never
  arises. **TWO sites** carry the same scope-rooted bug — fix both in one change-set:
  `format_type_display` (repl.rs ~L2678) AND the `format_def_entry`
  `DefKind::Constructor` arm (repl.rs ~L2550-2554, the FIXME-0321 mis-qualify class).
  Leave the `; impl:` lookup scope-rooted (Decision-45 Pattern B — different
  semantics; a prelude-trait-enumeration sibling gap exists but is out of scope →
  note to /qa).
- **D2 — APPROVED WITH REQUIRED REFINEMENT: discriminate by concreteness.** An
  UNCONDITIONAL collapse is a §1.5.1 violation: bare `None` (result-only-polymorphic)
  MUST keep the value display `:(prelude/Option a) Option.None` with NO `; deftype`
  — pinned GREEN by `prelude_option_none_value_display_neg_definition_metadata`. The
  defect is **concrete nullary ctors only** (user `Red`), NOT the seeded `None` (its
  display is as-specified). Fix in `check_bare_symbol_introspection` (eval.rs
  ~L625-638): nullary AND non-concrete scheme (`!Type::is_concrete()`, types.rs:92)
  → keep `None` (falls to §1.5.1 value display, already green); nullary AND concrete
  → introspection `EvalResult::Def`. Post-collapse seam ownership (for /review's
  mirror guard): `format_def_entry` Constructor arm = the ONE ctor-**definition**
  formatter; `display.rs` value envelope = the ONE ctor-**value** formatter;
  `format_ctor_display` = shared atom. **Correct the sprint/repro-comment claim that
  `None` is an instance — it is not.**
- **D3 — APPROVED as specified.** `.max_tokens(AGENT_MAX_TOKENS)` named constant +
  `#[cfg(test)]` unit test asserting `max_tokens.is_some()`, same change-set. Arch
  calibration note: the agent loop drives `stream` (S107) → use the streaming-scale
  default (~64K), not a lowball; exact value /dev's per FIXME 0554.
- **Collateral the change-set MUST carry (→ C1):** `tests/display_exact.rs::display_exact_nullary_and_single_level_adt_value_lines`
  pins `:user/Color Color.Red` but elicits it via a **bare** `Red` lookup (same
  under-assertion class as 0557) — D2's fix flips it RED. Remedy = **re-elicit via a
  genuine runtime expression** (e.g. `(defn f [] Red)` + `(f)` / a `match`), not
  weaken. Owner /qa (C1), executed by /testing alongside the /dev change-set.

## Skill plans (Phase 3)

{Pending scope approval. Anticipated: /dev(src/) for D1+D2 (one change-set,
collapse the duplicate path) then D3 (feature-gated); /review(src/) against
design intent + the no-new-mirror check; /qa for C1 annotation re-point + M1
ledger disposition; /testing to confirm/tighten the two committed repros and add
the current-REDs index if M1 lands that way.}

## Waves (Phase 4)

Source-touching agents run SERIALLY (worktree isolation broken); waves sequence
edits, not parallelise them. `/review` is read-only and follows each fix.

### Wave 1 — D1 + D2 (REPL introspection display)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | src/ | D1 (root ctor lookup at home `module`, both sites) + D2 (concreteness-discriminated collapse) + src unit tests; flip both RED repros GREEN; keep §1.5.1 Neg green | done |
| /testing | tests/ | Re-elicit `display_exact` nullary row via runtime expr; correct D2 repro comment (None not an instance); confirm suite green | done |
| /review | src/ | Review D1+D2 vs design intent + no-new-mirror (the two ctor-format seams) | done |

**W1 result:** full suite 4264 run / 4262 pass / 2 fail. Both fails pre-existing
intentional guards (`deftype_ctor_trailing_form_after_field_bracket_rejected_neg`
— /dev-frontend, S107; `chaining_toggle_off_allocates_intermediate` — FIXME 0528,
/typecheck, S103); zero S108 regressions. D1+D2 target repros + §1.5.1 Neg +
`display_exact` re-elicitation all GREEN.

**W1 /review verdict — CLEAR, no Blockers.** No-new-mirror clean (D2 collapsed,
not copied); both D1 sites re-homed; discriminator correct. Findings:
- IMPORTANT → Wave 3 /testing: the two now-GREEN repros still carry present-tense
  "DEFECT (open, owner /dev)" comments; under ledger retirement these would let a
  future regression pose as a known guard. Fix while retagging with `// defect:`.
- MINOR → Wave 2 /dev: stale rustdoc on `check_bare_symbol_introspection`
  (eval.rs:~525, "nullary ctors" unqualified).
- ROUTING → FIXME 0558 (filed): the wrong-scope display class RECURS in
  `format_trait_display` (repl.rs:2748) — prelude-globbed traits may drop
  `; defn:`/`; impl:`. Arch-scoped-out of S108; FIXME preserves it.
- SUGGESTION (no action): duplicated test session-ctor (`d2_session` vs
  `fq_arg_tests::session`) + `TempDir::keep()` artifact leak — below extraction
  threshold (2 sites); extract on 3rd occurrence.

### Wave 2 — D3 (agent request)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | src/ | D3 `.max_tokens(AGENT_MAX_TOKENS)` + `#[cfg(test)]` guard (`--features agent`); delete FIXME 0554; + MINOR rustdoc fix eval.rs:~525 | done (max_tokens=65536; test green; 0554 deleted) |
| /review | src/ | Review D3 change-set | done (CLEAR; FIXME 0559 filed, non-blocking) |

### Wave 3 — C1 + M1 (coverage process + ledger retirement)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /qa | tests/plan/ | C1 re-point §4.1.2 [Tested]; M1 retire ledger, design `// defect:` notation + `class=` vocabulary, migrate discipline text to tests/CLAUDE.md, update root CLAUDE.md pointer; delete FIXME 0557 | done (also fixed S86 7-row clobber; root CLAUDE.md edited; scripts pass) |
| /testing | tests/ | Apply `// defect:` notation to the S108 repros AND fix the IMPORTANT /review finding — strip the stale present-tense "DEFECT (open)" framing from the two now-GREEN repros (repl_introspection.rs ~L1086, ~L1818) so triage isn't polluted | done (notation applied; stale framing 0; orphaned test deleted) |
| /qa | tests/plan/ | Cleanup: re-point/drop the `spec_coverage_reconcile.py:596-598` mapping to the deleted `nullary_constructor_bare_lookup_dot_notation` + audit-note refs | done (re-pointed to §4.1.2 guard; verifiers clean 639/0 dead, link-check 1644 OK) |

## Dispatch log

All shim dispatches, default tier per `artefacts.md` §II.3 — no model/effort
overrides used this sprint.

| Wave | Agent | Surface | Model | Effort | Non-default reason |
|---|---|---|---|---|---|
| P2 | /arch | src/ D1/D2/D3 review | default | default | — |
| W1 | /dev | src/ (D1+D2) | default | default | — |
| W1 | /testing | tests/ (display_exact re-elicit + comment) | default | default | — |
| W1 | /review | src/ (D1+D2) | default | default | — |
| W2 | /dev | src/ (D3 + rustdoc) | default | default | — |
| W2 | /review | src/ (D3) | default | default | — |
| W3 | /qa | tests/plan/ + tests/CLAUDE.md + root CLAUDE.md + repl/spec.md annot (C1+M1) | default | default | — |
| W3 | /testing | tests/ (notation + orphan delete) | default | default | — |
| W3 | /qa | tests/plan/ (reconcile residue cleanup) | default | default | — |

## Notes

- Defects surfaced by user REPL testing (this session). D1/D2 isolated and
  reduced by `/testing` with committed RED repros; D3 root-caused to a one-line
  omission and filed as FIXME 0554 (not e2e-reproducible → FIXME + unit-test guard).
- **Open decision for the user (M1):** retire the heavyweight failure ledger,
  moving BOTH its functions onto the permanent test corpus — triage via the
  inline defect-comment/FIXME convention, and frequency/locus/recurrence analysis
  via a structured `// defect: class= locus= found= owner=` notation on repro
  tests (with a `/qa`-owned controlled `class=` vocabulary)? Or keep/slim the
  ledger? `/sprint` recommends retire + adopt the notation. The `class=`
  vocabulary is the only genuine design task and is `/qa`'s.

## Outcome (Phase 7)

### Delivered
- **D1** (spec §4.1.3): seeded ADTs (`Option`/`Result`/`IO`) now surface `; match:`.
  Fix rooted the constructor chain-lookup at the type's resolved home at BOTH
  scope-rooted sites (`format_type_display`, `format_def_entry` Constructor arm);
  no `cranelisp-types` edge/cache change. Guard GREEN:
  `repl_introspection::seeded_option_bare_lookup_includes_match_section`.
- **D2** (spec §4.1.2): concrete nullary constructors now show
  `:{type} {module}/{Type.Ctor} ; deftype`. The duplicate display path was
  COLLAPSED (concreteness-discriminated) — bare result-only-polymorphic ctors
  (`None`) keep their §1.5.1 value display. Guard GREEN:
  `repl_introspection::nullary_constructor_bare_lookup_shows_deftype_and_qualified_home`;
  §1.5.1 Neg guard stays GREEN.
- **D3** (Anthropic API contract): embedded agent sets `max_tokens` (=65536) on the
  shared request builder — both `complete`/`complete_streaming` repaired. Unit
  guard GREEN under `--features agent`. FIXME 0554 resolved + deleted.
- **C1** (FIXME 0557): §4.1.2 `[Tested]` re-pointed at the real guard; `/qa` also
  found + fixed an S86 clobber (7 §1.5 rows mis-cited at one under-asserting test);
  reconcile scripts clean (639 citations / 0 dead). FIXME 0557 deleted. Orphaned
  `nullary_constructor_bare_lookup_dot_notation` deleted (subsumed).
- **M1** (user-approved): failure ledger retired → tombstone. Both functions moved
  onto the permanent test corpus: triage via the inline-defect/FIXME convention;
  frequency/locus/recurrence analysis via a new `// defect: class= locus= found=
  owner=` notation on repro tests, backed by a `/qa`-owned 9-class vocabulary
  (`tests/CLAUDE.md`). Ledger discipline text migrated. Root `CLAUDE.md` §Testing
  pointer + /testing skills-row updated (**user-visible edit to the canonical
  instruction file**). S108 repros carry `// defect:` lines; stale "DEFECT (open)"
  framing stripped from now-GREEN repros (W1 /review IMPORTANT finding).

**Suite:** full `nextest` 4260 pass / 2 pre-existing intentional guards RED / 0
S108 regressions.

### Deferred (with rationale)
- **Phase 6 user-proxy fan-out + rotating `/audit`** — skipped as disproportionate
  for a 3-defect mini-sprint with no new user-facing surface (behaviour verified by
  e2e + unit guards). User consulted at close.
- **FIXME 0558** (/qa) — wrong-scope class recurs in `format_trait_display`;
  arch-scoped-out of S108, repro+fix next sprint.
- **FIXME 0559** (/design) — `agent.md §6` should state the `max_tokens` contract;
  doc-side, non-blocking.
- **FIXME 0560** (/dev) — pre-existing load-sensitive reactor test; carried (not
  S108-caused).

### Findings
- **PROCESS (user, Increment 2): a `/review`-caught correctness defect is a
  QA-first + unit-test MISS, not a review win.** `/review` found I-1/I-2/I-3 as
  correctness defects, but all three were knowable before review — `/arch`
  pre-flagged I-1's collision; §17.19.3 stated I-2's non-conflation as a MUST;
  I-3's byte-identical piped contract is a standing invariant. Root cause: the
  QA-first deferral ("E2 latch will be `/dev` unit-pinned") never ENUMERATED the
  boundaries, so `/dev` pinned the happy path and the negatives/spec-MUSTs fell
  through. Correction: guard-closure wave (deterministic I-2 guard + fail-on-revert
  check on all three); durable lesson saved to memory + a coverage-process note
  (spec-MUSTs + arch-pre-flagged boundaries are the highest-signal QA-first
  targets; deferred-e2e must enumerate the unit cases). This is the first real
  exercise of the ledger-retirement bet: review is the LAST line, tests the first.
- The wrong-scope display-lookup is a recurring CLASS (D1 type display, D2 routing,
  0558 trait display) — `/arch` noted a candidate "resolve home, then enumerate"
  single helper to back all introspection section-lookups so it cannot recur a
  4th time. Seeded as `class=wrong-scope-lookup` in the new notation vocabulary.
- Coverage-annotation clobbering (S86 7-row, plus 0557) is invisible to the
  reconcile script (citations resolve, just to the wrong test) — the script guards
  existence, not intent. Worth a `/qa` process note.
- The new `// defect:` notation is the durable replacement for the ledger's
  analytical function and, unlike the ledger, spans GREEN repros — its first real
  test is whether `grep class= | uniq -c` surfaces the wrong-scope recurrence next
  time it appears.
