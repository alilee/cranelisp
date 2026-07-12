# Sprint 108: Testing-driven defect-fix umbrella (successive mini-increments)

**Status**: ACTIVE — Increment 1 COMPLETE (not closed); awaiting Increment 2
(next testing-driven batch). Sprint stays open across user testing sessions;
closes when the user calls it (Phase 6 fan-out + `/audit` deferred to close).

**Goal**: An umbrella sprint holding successive small defect-fix increments as the
user surfaces issues through REPL/language testing. Each increment runs a
lightweight scope → `/arch` sanity → D/D/R cycle and lands its own committed
guards. Increment 1 fixed two REPL introspection display bugs + the agent request
+ settled the failure-ledger question. A running **stdlib-request backlog** (see
§Stdlib request backlog) collects "missing library function" findings for a future
`/stdlib` increment — distinct from defects and language usability findings.

**Audit**: {deferred to sprint close — rotation TBD, METHOD §2.6}

## Increments

| # | Focus | Status |
|---|---|---|
| 1 | REPL introspection display (D1 §4.1.3, D2 §4.1.2) + agent `max_tokens` (D3) + coverage repair (C1) + ledger retirement (M1) | COMPLETE — committed f2bfd8a5; 0 regressions |
| 2 | `/search` indexes seeded primitives (E1) + indexing lifecycle messages (E2) + 3 review-found conformance fixes + coverage-process lesson | COMPLETE — suite 4274 pass / 0 regressions; review CLEAR; fail-on-revert proven; committed 65a1f54a |
| 3+ | Testing-driven — filled as the user surfaces issues | pending |

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
