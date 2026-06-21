# Sprint 87: Green-and-Clear → Deep Per-Crate Audit

**Status**: PHASE 4 WAVE ORG (complete) — ready for PHASE 5 LANGUAGE (ACTIVE)

**Goal**: First return the suite to fully green and triage the FIXME store; then run a fresh-view per-crate audit of the 6 crate-shaped surfaces against their prior-audit baselines, producing a prioritized pre-Phase-H consolidation/simplification backlog and a scope-decision gate; and roll out the de-risked stdlib self-test + bare-verb promotion, informed by an exemplar-driven stdlib-adequacy review.

## Scope

S87 is the second leg of the pre-Phase-H consolidation arc (ROADMAP Forward Plan). Per user direction (2026-06-20), it runs in **three stages**: get to green-and-clear *before* the audit (so the fresh-view passes read settled, defect-free code), the deep per-crate audit, and a stdlib stream (adequacy review + rollout) that runs on the green base in parallel with the audit.

### Stage A — Green & Clear (gates the audit)

A FIXME + tests round to clear all known reds and the named-resolver carries before any audit wave.

0. **Stage-A entry check (R3).** Run the `tests/plan/ledger.md` §Close-time Verification protocol *at Stage-A entry* (not only at sprint close) and confirm the live `cargo nextest run --workspace` red set is **exactly** the 4 named guards below and nothing else. The whole premise of Stage A is "0 intentional reds before audit," so the gate is mis-calibrated if the live red set ≠ 4. (S86 fixed D3/D4/DEF-1/D5b in-campaign; this check confirms none re-surfaced.)
1. **Clear the 4 intentional failing-not-ignored guards** (defects with committed repros + named resolvers, per `tests/plan/ledger.md`):
   - `/int` — `disasm_command_shows_native_code_for_compiled_fn`: `/disasm` reads a never-populated `intr.disasm` field instead of calling `cranelisp_backend::produce_disasm` (D41 on-demand re-derivation). Wire the handler.
   - `/repl` — `info_multi_clause_macro_shows_clause_count`: `/info` on a multi-clause macro omits the `N clauses` count.
   - `/typecheck` — `type_error_names_expected_type_fully_qualified` + `..._actual_..`: error renderer names types bare not FQ; root cause `crates/cranelisp-typecheck/src/unify.rs:117` (value-display qualifies, error renderer doesn't).
   - Each fix lands with its mandatory unit test (assess e2e need before fixing; the guards are the e2e record). Suite returns to **0 intentional reds**.
2. **FIXME store hygiene** — triage every open FIXME in `design/arch/fixmes/`:
   - Delete already-resolved files whose owning skill has not yet removed them: **0414** (/qa — spec→test linter, RESOLVED S86), **0405** (/platform — web showcase, RESOLVED by S86 Wave E). (Only the owning skill deletes.)
   - Close the **0412 / 0413** residual judgment work (/spec, /repl): confirm the `[Gap(S86)]` clauses, triage the 75-row `--mode stale` report not bulk-flipped in S86.
   - Every remaining open FIXME gets an explicit disposition: action-if-cheap, or `status: deferred` + rationale + target sprint (set by the owning skill). Carries that are Phase-H-gated (0050, 0052, 0365) or demo/forward-flow (0408, 0409, 0410, 0415) are confirmed-deferred, not actioned.
3. **Exit gate (Stage A → Stage B):** `cargo nextest run --workspace` green (0 intentional failing guards remaining); FIXME store fully triaged; close-time ledger re-verification protocol satisfied for any entry touched.

### Stage B — Deep per-crate audit

Fresh-view audit of the **physical workspace crates** for **simplicity, maintainability, and duplicated code paths**. `/review` + `/arch` driven. **Design/review only — no implementation** unless emergent-mandatory per METHOD §Phase 5.

**Surfaces to audit (R1 — /arch Phase-2 correction).** The "6 crate-shaped surfaces" is the *triad-deployment* abstraction (METHOD §1.3, where runtime is "paired with backend"); an audit must enumerate the **real physical crates**. There is no `cranelisp-runtime` — Decision 43 (S65) split it into `cranelisp-primitives` + `cranelisp-intrinsics`. The eight audit passes:

| Crate / surface | Prior-audit baseline to reconcile (R5) |
|---|---|
| `cranelisp-typecheck` | `audits/typecheck-20260531.md` (latest of three generations) |
| `cranelisp-backend` | `audits/backend-20260423.md` + `.mmd` |
| `src/` (binary; folds in the 65-line `cranelisp-exe-bundle` per binary-surface composition) | `audits/src-20260423.md` + `.mmd` |
| `cranelisp-frontend` | `audits/frontend-20260423.md` + `.mmd` |
| `cranelisp-intrinsics` (7.1k — would have been skipped under the old list; the `vec_set_copy` RC-asymmetry seed already implies it is in scope) | `audits/intrinsics-2026-06-14.md` (no diagram) |
| `cranelisp-primitives` | `audits/primitives-2026-06-14.md` (no diagram) |
| `cranelisp-platform` | `audits/platform-2026-06-14.md` (no diagram) |
| `cranelisp-types` | `design/arch/facades/types-audit-s69.md` |

"No prior baseline" ≠ skip — it means a from-zero pass, flagged as such.

**Quantitative pre-pass (opens Stage B, feeds every crate pass).** Before the qualitative passes, produce a `tokei`-driven LOC table — **per crate and per module** — ranking modules by size. Large modules are prioritized for deeper scrutiny: excessive size is a leading indicator of duplication / inefficiency / mixed concerns. File-level tools can't split inline `#[cfg(test)]` modules from production code, so the table carries **three columns (R5c)**: non-test LOC / inline-test LOC estimate (`grep -c '#\[test\]\|#\[cfg(test)\]'` per module) / `tests/`-dir LOC — with the size ranking driven by the **corrected non-test** figure, *before* it sets scrutiny priority (several large typecheck/backend modules carry heavy inline test blocks; uncorrected LOC mis-ranks them). The rough baseline already flags the targets — `cranelisp-typecheck` (~31k), `src/` (~32k), `cranelisp-backend` (~27k) dwarf the rest. The LOC table is a durable audit artefact (`audits/loc-s87.md`).

**One pass per crate** (user-confirmed depth). Depth on a single pass is assured by four mechanisms:

1. **Prior-audit baseline first, same instrument.** Each pass opens by reading that crate's named baseline (table above) and reconciling every prior finding: still-open / regressed / resolved. The S87 pass is a **delta + currency check** on the deep baseline, not a from-zero look. *Same-instrument requirement (R5a):* the lens checklist must map onto the prior audit's finding taxonomy so "still-open/regressed/resolved" is a true diff, not a re-categorization.
2. **Fixed lens checklist per pass** — every pass covers all of: (i) duplicated code paths / `mirror` comments; (ii) dead paths (e.g. the `produce_disasm` zero-call-site class); (iii) function-budget overruns; (iv) RC-symmetry (consuming-inc uniformity, Decision 24); (v) resolution-seam consolidation; (vi) interim-architecture residue (Principle 8); **(vii) cross-crate-boundary / host-callback hygiene (R5b)** — does this crate hand-roll something a sibling crate also hand-rolls across the FFI/host-callback boundary? This is the class the interior lens misses and the one that bit S86 hardest (DEF-4/5/6 composite + the JIT-vs-`--link` host-callback divergence; FIXME 0407 is the same family).
3. **File:line evidence per finding.** Every finding cites concrete `file:line` evidence and a severity, not a vague smell — keeps the backlog actionable and verifiable.
4. **/arch cross-cutting synthesis pass.** One /arch pass over all 6 crate findings catches patterns no single-crate pass can see — chief among them the **single-resolution-seam question** (DEF-1 recurrence, inherently cross-crate).

**S86 hot-spot seeds** (feed into the relevant crate passes):
- DEF-1 recurrence → is there *one* resolution seam that should consult the prelude fallback, vs. N chokepoints each wired separately? (/arch synthesis — cf. `memory/feedback_review_root_cause_and_duplication`)
- DEF-2/DEF-3 → sweep all primitive-arg-forwarding sites for consuming-inc symmetry (`cranelisp-backend`).
- `vec_set_copy` runtime/backend RC asymmetry — RC-model alignment candidate (`cranelisp-backend` / `cranelisp-intrinsics`).
- Audit all wall-clock timing witnesses for best-of-N robustness under the saturated `--workspace` run (`/qa` lens).
- Hot spots flagged by the S86 defect cluster: typecheck module/submodule resolution; backend codegen RC; int codegen-batch derivation + cache/link.

**Audit artefacts (durable by-products, written to `audits/`).** The audit produces, not just a backlog, a refreshed picture of each crate:
- `audits/loc-s87.md` — the quantitative LOC table (per crate + per module, test/non-test, size-ranked).
- Per-crate **current-state mermaid diagrams** (`audits/{crate}-s87-current-state.mmd`) — module structure + data flow, extending the 2026-04-23 precedent (which covered only backend/frontend/src/typecheck) to all eight crates. Diagrams show *the approach* — how a form moves through the crate, where the seams are — making duplication and tangled data flow visible at a glance. Each S87 `.mmd` carries a one-line header note citing the predecessor it refreshes (the 04-23 files are *superseded* but per the never-delete-archived rule stay in place). `.mmd` source committed; SVG rendering optional (no `mmdc` on host — render later or leave as source).
- `audits/s87-findings.md` — the consolidated, severity-ranked findings + /arch cross-cutting synthesis.

**Output:** a prioritized consolidation/simplification backlog (the pre-Phase-H technical-work scope), plus the artefact set above.

**Scope-decision gate (Stage B exit, /sprint + user):** with the backlog in hand, decide what — if anything — must land before Phase H opens (Phase H currently gates on display protocol `0050`, `/learn` `0052`, `Type.member` `0365`, plus whatever the backlog surfaces as must-fix-first). The two exploratory design tracks' sign-offs (`--release` LLVM tier U1–U4; embedded REPL agent U1–U6) are surfaced at this gate for user decision but are not S87 implementation.

### Stage C — Stdlib adequacy & rollout

Runs on the green base (after Stage A), in parallel with the Stage B audit (distinct files). Two parts: an exemplar-driven **adequacy review** (assessment) that informs the **rollout** (authoring).

1. **Exemplar-driven stdlib-adequacy review (`/port`).** `/port` re-reads the Sudoku exemplar (`exemplar/`) through the lens: *where is the code awkward to express because the stdlib lacks an obvious feature?* Output a **collated, prioritized gap list** — each entry naming the exemplar site (`file:line`), what was awkward (workaround written inline, primitive used where a verb should exist, missing combinator/collection op, etc.), and the proposed stdlib feature that would express it cleanly. Distinguish:
   - **Pure stdlib gaps** (a missing function/macro composable from existing primitives) → candidates for Stage C.2 in-sprint authoring.
   - **Compiler/language gaps** (the feature needs typecheck/codegen/spec support) → feed the Stage B audit backlog / FIXME store, not in-sprint stdlib work.
   Written to `stdlib/plan-stdlib.md` (the managed-surface plan) and surfaced as a Notes entry.
2. **Stdlib rollout (`/stdlib`)** — the de-risked S86 follow-up (its compiler blockers D3/D4/DEF-1 are fixed):
   - Author `(mod test)` self-test submodules across stdlib modules (self-test rollout).
   - Bare-promote the curated collection verbs (`count`/`get`/`conj`/`assoc`, `first`/`rest`) — un-comment the `(export …)` now that DEF-1 is fixed. **Sequencing (R4): 0402 (/spec curated-overload naming reservation) resolves in Stage A first; C.2's bare-promotion set MUST NOT overlap 0402's reserved set in a way that pre-binds a Phase-H trait-dispatched name.** Promote as module-qualified / via the de-risked re-export, not as the reserved Phase-H trait names.
   - Action the **pure stdlib gaps** from C.1 that are cheap + obviously correct; defer the rest into `plan-stdlib.md` with rationale.
   - Free-standing discipline preserved (tests/examples stay zero-stdlib-dependency per CLAUDE.md §Stdlib separation); rollout lands with stdlib's own self-tests green and prior demos/exemplar replaying green.

### Out of scope (deferred, with rationale)

- **Acting on the audit backlog** — S87 produces the backlog; implementation is the *next* sprint(s), decided at the scope-decision gate. (Emergent-mandatory refactors — third duplicate, over-budget function, `mirror` — may still land in-sprint per METHOD §Phase 5.)
- **Compiler/language gaps surfaced by the C.1 adequacy review** — anything needing typecheck/codegen/spec support is fed to the Stage B backlog / FIXME store, not authored in-sprint (S87 stdlib authoring is pure-stdlib-composable features only).
- **Phase-H feature work** (0050 display protocol, 0052 `/learn`, 0365 Type.member) — gated behind this arc's scope decision.
- **Demo/forward-flow FIXMEs** (0408 Sudoku parallel-search, 0409 demo numbering, 0410 Cranelisp.toml scaffold, 0415 symbol-layout) — Phase 6 forward-flow, not audit-sprint scope.

## FIXME debt

| FIXME | Target | Status | S87 disposition |
|---|---|---|---|
| 0050 | /int | deferred | Phase-H carry (display protocol) — confirm deferred |
| 0052 | /repl | open | Phase-H carry (/learn) — confirm deferred |
| 0365 | /spec | open | Phase-H carry (Type.member) — confirm deferred |
| 0402 | /spec | open | Stage A — action (curated-overload naming reservation) |
| 0405 | /platform | open | Stage A — delete (RESOLVED S86 Wave E) |
| 0406 | /int | open | Confirm deferred (friendly link rejection — /arch ruling stands) |
| 0407 | /arch | open | Stage B synthesis CITES it (host-callback-divergence evidence, lens vii) — stays `open`, NOT resolved/actioned in-sprint; future `/dev platform + intrinsics + /arch ABI` task (R2) |
| 0408 | /port | open | Out of scope — demo pass |
| 0409 | /repl | open | Out of scope — forward-flow |
| 0410 | /repl | open | Out of scope — needs /spec first |
| 0412 | /spec | open | Stage A — close residual judgment work |
| 0413 | /repl | open | Stage A — close residual judgment work |
| 0414 | /qa | open | Stage A — delete (RESOLVED S86) |
| 0415 | /repl | open | Out of scope — forward-flow |

## Architecture review (Phase 2)

**Verdict (/arch, 2026-06-20): APPROVE-WITH-REVISIONS.** Three-stage shape sound; green-before-audit ordering correct; **no interface delta** (the /int disasm fix wires the already-public `cranelisp_backend::produce_disasm`; the /typecheck fix changes `TypeError.message` content only, not the `cranelisp-types` boundary shape; bare-verb promotion is stdlib-local bare-name curation, MUST NOT touch reachability); **no interim-architecture trap** (the audit yields a backlog, the input that *prevents* speculative work); **no canonical `design/arch/` archive/fold triggered** (audit by-products live in `audits/`, outside the canonical set). No `cranelisp-types` edit made or needed.

Revisions applied to this plan:
- **R1 (was blocking)** — crate enumeration corrected: `cranelisp-runtime` does not exist (Decision 43/S65 → `cranelisp-primitives` + `cranelisp-intrinsics`); the audit now enumerates the **8 physical crates** (table in Stage B), so intrinsics (7.1k), types, and exe-bundle are no longer skipped.
- **R2** — FIXME 0407 is *cited* by the synthesis (host-callback-divergence evidence), stays `open`, not actioned in-sprint.
- **R3** — Stage-A entry check added: run ledger §Close-time Verification at entry; live red set must equal exactly the 4 named guards.
- **R4** — 0402 resolves (Stage A) before C.2 authoring; C.2 promotion set must not pre-bind a reserved Phase-H trait name.
- **R5** — named per-pass baseline (table); same-instrument reconciliation (a); 7th lens item cross-crate/host-callback hygiene (b); mechanical inline-test-split LOC column (c).
- **R6** — Phase-H/forward-flow deferrals confirmed; 0405/0414 deletes are owning-skill (/platform, /qa) actions.

**Phase-3 advisory (carried to /design typecheck):** the FQ-naming fix must target the Display path used by the *error renderer* (`crates/cranelisp-typecheck/src/unify.rs:117`), NOT the value-display path that already qualifies — do not unify the two in a way that changes REPL value-display output (separate spec contract).

**Phase-4 note:** C.1 (adequacy review) feeds the Wave-2 /arch synthesis, so C.1 must be *gated into* Wave 2, not run alongside it.

## Skill plans (Phase 3)

### /spec

**Task (Stage A — FIXME 0402, ACTIONED this phase):** Record the curated-overload naming reservation that keeps S86's bare-name curation forward-compatible with the Phase-H trait-dispatched collection abstraction, and unblock Stage C.2 (R4) by pinning which bare names MUST NOT be pre-bound now.

- **Actioned now (Phase 3), not deferred to Phase 5.** The ruling is pure non-normative stdlib-author guidance — no language-semantics change, consistent with /arch's S86 sign-off ("bare-name-curation only; no compiler/`cranelisp-types`/spec-semantics change") — so it lands as spec text immediately and 0402 is resolved + deleted.
- **The ruling:** Reserve `map`/`filter`/`reduce`/`count`/`get`/`conj`/`assoc` and `first`/`rest` as future trait-dispatched (Functor/Foldable/collection-trait) bare names. The distinction binding on /stdlib for Stage C.2: **module-qualified curation is allowed for any reserved name** (e.g. `collections.vec/count`, reachable module-qualified or via explicit import); **bare-promotion to the prelude pointing at one concrete family is what is deferred** for the reserved verbs, because that pre-binds a name the future trait must own. `first`/`rest` stay unbound in the prelude (list `first` and pair `first` are distinct terminal sources — re-exporting both bare poisons the name under §8.6.4); both reachable FQ. The already-trait-dispatched operators (`+ - * / = < > <= >=`, `show`) are unaffected — they are the model the reserved verbs anticipate.
- **Stage C.2 guidance (R4):** /stdlib MAY bare-promote / re-export only names NOT in the reserved set, and MAY curate the reserved verbs module-qualified. Un-commenting `(export …)` to bare-promote `count`/`get`/`conj`/`assoc`/`first`/`rest` to the prelude as a concrete family is OUT (it would pre-bind a reserved Phase-H trait name); promote those as module-qualified / explicit-import-on-demand instead.

**Design refs (spec sections):**
- `spec/11-stdlib.md §11.4a` (NEW — Curated Collection-Verb Naming Reservation; §11.4a.1 first/rest coexistence; §11.4a.2 non-restrictions) — the canonical home of the ruling.
- `spec/07-traits.md §7.12.2` (future-extensions table — new row cross-referencing §11.4a) — the trait-side discoverability anchor.
- Consistency anchors (no edit): §8.6.4 terminal-source collision rule; §8.6.5 ambiguity poisoning; §8.8.1 optional-prelude; §8.9.1/§8.11.4/§3.1 FQ-reachability guarantee; §7.5 trait-dispatched operators; §7.7.5 Functor.

**Acceptance criteria:**
- 0402 ruling recorded in §11.4a, naming each reserved verb + the bare-promotion-vs-module-qualified distinction; resolved + `design/arch/fixmes/0402-*.md` deleted (this phase).
- §7.12.2 cross-references §11.4a so a trait-side reader finds the reservation.
- The reservation is internally consistent with the §8.6.4/§8.6.5/§8.8.1/§8.9.1 invariants it cites (no new language semantics introduced).
- Stage C.2's bare-promotion set does not overlap the reserved set in a way that pre-binds a Phase-H trait name (verified by /stdlib at C.2 against §11.4a).

**Carried /spec FIXMEs (not actioned this phase):**
- **0412** (Stage A — close residual judgment work): confirm the `[Gap(S86)]` clauses + triage the 75-row `--mode stale` report not bulk-flipped in S86. Disposition this sprint per Stage-A plan; not part of 0402.
- **0365** (Phase-H carry — `Type.member` / associated types): confirm deferred (FIXME-debt table). No action this sprint.

### /port — Stage C.1 exemplar-driven stdlib-adequacy review

**Task.** Re-read the Sudoku exemplar (`grid`/`solver`/`html`/`form`/`user`) through the lens *"where is the code awkward because the stdlib lacks an obvious feature?"* Produce a **collated, prioritized gap list** — each entry: exemplar site (`file:line`), the awkward thing (inline workaround / raw primitive where a verb should exist / hand-rolled combinator / contorted data flow), the proposed stdlib feature, and a **class**: **[STDLIB]** (pure fn/macro composable from primitives → Stage C.2 `/stdlib` authoring) vs **[COMPILER]** (needs typecheck/codegen/spec → Stage B backlog / FIXME store, NOT in-sprint). Also flag **authoring gaps** (verb missing) vs **adoption gaps** (verb already in stdlib, exemplar hand-rolls). Gated into **Wave 2** so [COMPILER] gaps feed the /arch synthesis before it closes (Phase-4 gating note). Read-only on source; parallel with the Stage B audit. Hands the collated list to `/stdlib` for `stdlib/plan-stdlib.md` intake (/stdlib owns that file's authoring).

**Design refs.** `exemplar/notes-stdlib-adequacy-s87.md` (this skill's working notes — lens, method, output format, first-recon list C1–C10); `exemplar/CLAUDE.md` §Known-Issues/§Design-Decisions (DEF-2 + no-bitwise + no-rem context); current stdlib surface (`collections/vec.cl`, `seq.cl`, `num/int.cl`, `text/string.cl`) for authoring-vs-adoption checks. Coordinate with /spec §11.4a reservation (above): proposed [STDLIB] verbs must respect the reserved-name rule (no bare-promotion of a reserved Phase-H trait name).

**Recon findings (validated this phase).** Modules already fairly clean post-S86 idiom pass; awkwardness clusters in: (a) C3 — bitwise ops simulated via `/ * - pow2` (**[COMPILER]** language gap: no `bit-*` intrinsics — biggest contortion, gates Stage B not C.2); (b) C5/C7 — manual index-recursion accumulators wanting a `range` verb (**[STDLIB]** authoring, highest leverage, many sites); (c) adoption gaps where the verb already exists (`int-to-string` C1, `num.int/rem` C4, `repeat-str` C6, `str` macro C9). The DEF-2 `vec-push` cluster is a **compiler defect masquerading as a stdlib gap** (`conj` exists but corrupts heap-ADT elements) → routes to the DEF-2 repro, not C.2; not double-counted.

**Acceptance.** (1) Collated list complete: every qualifying site has `file:line` + awkwardness + proposed verb + [STDLIB]/[COMPILER] class + authoring/adoption flag, prioritized. (2) [STDLIB] authoring candidates checked against current stdlib surface (no "propose a verb that already exists") and against /spec §11.4a reserved names. (3) [COMPILER] entries handed to the Stage B backlog / filed as FIXME before Wave-2 synthesis closes. (4) [STDLIB] entries handed to `/stdlib` for `plan-stdlib.md` intake. (5) Surfaced as a Notes entry. Read-only on source (no `.cl`/`.rs` edits); honest "already clean" coverage noted where true.

### /design (src/) — two Stage-A REPL-handler fixes

Two Stage-A failing guards, both REPL handlers on the `src/` binary surface.
One src/ surface, two distinct resolver skills (`/int` for disasm, `/repl` for
the macro card). Design refs authored this phase: `design/int/int.md` §4.3
(disasm-on-demand correction — the master doc was STALE, claiming backend writes
`disasm` eagerly; corrected to the Decision 41 on-demand model), §8.2.1
(`/disasm` on-demand wiring), §8.2.2 (`/info` macro clause-count).

| # | Task | Crate | Design refs | Acceptance |
|---|---|---|---|---|
| 1 | **`/disasm` on-demand wiring (→/int).** `src/repl.rs::handle_disasm` reads the never-populated `intr.disasm` field → always "no disassembly available". Rewire to **re-derive on demand** (Decision 41): resolve `fq` (current module, same as `/clif`'s `get_introspection`), read `code_size` from the introspection record, call the **already-public** `cranelisp_backend::produce_disasm(&fq, code_size, &shared.symbol_tables)`, format `; disasm for <name>\n{text}` on `Ok`, graceful "no disassembly available" on missing `code_size`/`Err`. **Re-derives** (does NOT populate a field) — no `disasm` field is or should be written; the field + `symbol_disasm()` accessor (`session_v4.rs:1244`) are vestigial, remove or mark dead. | `src/` | `int.md` §4.3, §8.2.1; backend `produce_disasm` (`crates/cranelisp-backend/public-api.txt`, def `lib.rs`) | e2e guard `tests/repl_introspection.rs::disasm_command_shows_native_code_for_compiled_fn` flips green; **mandatory `src/` unit test** asserting `handle_disasm` on a compiled fn returns the `; disasm for` header + a `0x` line, NOT the dead path. No backend/types surface change (no interface delta). |
| 2 | **`/info` macro clause-count line (→/repl).** `src/repl.rs::format_macro_display` omits the `N clauses` summary line for multi-clause macros (spec `repl/spec.md §11.2.2`). Append `  N clauses` (two spaces, no `;`) as the final line, **gated on `clauses.len() > 1`** (single-clause `/info when` shows no count per the spec worked example). Count from the `clauses` slice already iterated; no new data. | `src/` | `int.md` §8.2.2; `repl/spec.md §11.2.2` | e2e guard `tests/repl_introspection.rs::info_multi_clause_macro_shows_clause_count` flips green; **mandatory `src/` unit test** asserting `format_macro_display` (or `handle_info`) on a 2-clause macro contains `2 clauses` and on a 1-clause macro does NOT. Existing macro-display guards (`defmacro_display_*`, `bare_macro_lookup`, `/sig`-path via `format_entry_sig`) stay green — all `contains`-based, `/sig` uses a different renderer. No interface delta. |

**Unit-test loci & e2e sufficiency.** Each fix carries a **mandatory `src/` unit
test** (CLAUDE.md §Testing — assess e2e need BEFORE the fix; the named ledger
guards ARE the e2e record, so no NEW e2e is owed). #1 pins the `handle_disasm`
wiring seam (the bug was a dead-field read); #2 pins the `format_macro_display`
rendering seam incl. the negative single-clause case. Both failing-not-ignored
e2e guards are already authored + un-ignored → they suffice for the end-to-end
contract.

**Phase-4 wave note — one `/dev` invocation or two?** Both fixes touch the SAME
file (`src/repl.rs`), are tiny, and are **independent** (disjoint functions:
`handle_disasm` vs `format_macro_display`; no shared edit region). Nominally two
resolver skills (`/int`, `/repl`) but **recommend a SINGLE `/dev (src/)`
invocation** doing both: concurrent `/dev` on one file races the index/linter
(CLAUDE.md §Testing "single agent at a time"; worktree isolation broken), and
splitting a 2-edit one-file change into two serial invocations only doubles
build/test cost for no isolation benefit. One agent edits `src/repl.rs` (both
functions + two unit tests; optionally removes the vestigial `disasm`
field/accessor in `session_v4.rs`), runs the suite once, lands both guards green
in one change-set. If `/sprint` wants resolver-attribution granularity, two
**serial** invocations are acceptable — NOT parallel.

### /design (cranelisp-typecheck) — FQ type names in type-error messages

- **Task:** Fix the type-error renderer so expected/actual type names are fully qualified (`primitives/Int`, not bare `Int`) per `repl/spec.md §5.3`. Add a **crate-private** `format_type_fq(ty: &Type) -> String` in `unify.rs` (maps the 4 primitive variants to `primitives/Int|Bool|String|Float`, renders `Type::ADT` via `FQTypeName`'s already-qualified Display, recurses on Fn/args); call it at `unify.rs:117` in place of the two `{t1}`/`{t2}` `Display` interpolations.
- **Crate:** `cranelisp-typecheck` (self-contained, `/dev`-deployable).
- **Boundary decision (binding):** typecheck-local helper, **NOT** promoted to `cranelisp-types` — (a) `cranelisp-types` is /arch-owned, promotion would serialize the fix behind an /arch FIXME; (b) honours the /arch Phase-2 advisory (keep error-renderer and value-display paths entirely separate functions in separate crates, converging only on the FQ output convention, never a shared call). Cannot regress value-display (touches neither `Type::Display`, `cranelisp-types::format_type_display`, nor `src/display.rs::format_type_qualified_inner`).
- **Design refs:** `design/typecheck/typecheck.md §8.3` (authored this phase); root cause `crates/cranelisp-typecheck/src/unify.rs:117`; bare-primitive arms `crates/cranelisp-types/src/types.rs:190-193`.
- **Acceptance:** (a) new `cranelisp-typecheck` unit test in `unify.rs #[cfg(test)]` asserting the `unify(Int, String)` `Err` message contains `primitives/Int` + `primitives/String`, same change-set; (b) both e2e guards `tests/repl_negative.rs::type_error_names_{expected,actual}_type_fully_qualified` flip green; (c) a `cranelisp-types` unit test asserting value-display is UNCHANGED (negative guard against unifying the paths); (d) no public-surface delta.
- **Adjacent instances (lens — NOT Stage-A scope, flagged for Stage B):** `unify.rs:135` (occurs-check message — trivially covered by the same swap, emergent-mandatory if /dev does it in-pass); `traits.rs:1157`+`:1804` ("no impl" via `concrete_type_name` strips module — deeper reconstruction, audit backlog).

### /qa — sprint-wide test plan

- **Task:** Author the failing-test plan for all implementation stages; persisted at `tests/plan/s87-test-plan.md`.
- **Stage-A entry verification (R3) — DONE this phase:** ran one read-only `cargo nextest run --workspace --no-fail-fast` (SHA `2fd7300`) → live red set is **exactly** the 4 named guards: `disasm_command_shows_native_code_for_compiled_fn` (`tests/repl_introspection.rs:1599`, →/int), `info_multi_clause_macro_shows_clause_count` (`tests/repl_introspection.rs:1119`, →/repl), `type_error_names_{expected,actual}_type_fully_qualified` (`tests/repl_negative.rs:125`/`:101`, →/typecheck). All `#[test]`, un-ignored, asserting the correct outcome. **Gate calibrated.** (Note: the macro-count guard's resolver is /repl but the test lives in `repl_introspection.rs`, not a `/repl`-named file.)
- **Per-fix plan (Stage A):** the 4 guards ARE the e2e record; each fix adds a mandatory **unit** test in its owning crate (typecheck renderer at `unify.rs`; src/ disasm-wiring seam; src/ macro-card renderer incl. single-clause negative). No additional e2e owed.
- **Stage-C plan:** (a) bare-verb promotion — positive e2e (each verb resolves bare via a **QA-owned re-export fixture**, run through all modes) + negative coverage (FQ `primitives/<name>` still works; empty prelude still valid + bare verb undefined there; no raw-primitive bare leak); R4-respecting (post-0402, no reserved-name pre-bind); all `tests/` stay zero-stdlib-dependency. (b) self-test rollout — REPL-session e2e via `CRANELISP_LIB`→`stdlib/` running the in-language runner over the `(mod test)` modules (`discover-tests` is dev-session-only → REPL not `--run`/`--link`); any NEW defect a self-test surfaces → narrow stdlib-free failing repro in `tests/`.
- **Stage-B (audit):** no new tests; /qa lens contribution = sweep all wall-clock timing witnesses for best-of-N robustness under the saturated run (single-shot positive timing assertions are latent close-gate flakes) → findings to `audits/s87-findings.md`.
- **Design refs:** `tests/plan/s87-test-plan.md`; `tests/plan/ledger.md §Close-time Verification`; `tests/CLAUDE.md`.
- **Acceptance:** Stage-A entry red set == exactly 4 (met); Stage-A exit 4 guards green + each fix carries its unit test + ledger Resolved-removal; Stage-C positive+negative bare-verb e2e + self-test runner guard (0402-respecting, zero-stdlib-dep harness); all new tests `// spec:`-traced + ledger/PLAN rows + `spec_link_check` clean + 30 s cap.

### /stdlib — Stage C.2 rollout

- **Task:** Roll out stdlib self-tests + bare-verb promotion (de-risked S86 follow-up); design in `stdlib/plan-stdlib.md §26`.
- **Self-test rollout (§26.1):** `(mod test …)` submodules per module (DISTINCT from `tests/`; preserves free-standing discipline), template = the green `testing/runner.cl` `(mod test)` (`super`-import + `assert-*`). 5 bootstrap-ordered waves: assertions keystone → trait bedrock (`compare/eq`·`ord`, `num`, `text/display` — the now-fixed D3/D4 modules) → core types → collections+helpers → fn/default/derive. Run via in-language runner in a live REPL.
- **Bare-verb promotion (§26.2) — conditioned on 0402 (R4):** under the §11.4a reservation, the conservative forward-compatible decision is **bare-promote only `conj`** (not reserved, no Phase-H collision); `assoc` conditional pending /spec; the four reserved verbs (`count`/`get`/`first`/`rest`, + `map`/`filter`/`reduce`) stay module-qualified. One-line `(export [collections.vec [conj]])` un-comment; DEF-1's fix is what de-risks it.
- **Adequacy-gap intake (§26.3):** decision rule — compiler/language gaps ROUTE OUT (Stage B backlog / FIXME, never stdlib-worked-around, so audit input isn't masked); pure-stdlib gaps action in-sprint only if cheap AND obviously-correct (≤~15 LOC, existing module/pattern, ships with a self-test), else DEFER (§26.4) with rationale; borderline → DEFER; every name cross-checked against §11.4a. (C.1 gates into Wave 2, so the gap list arrives then; `range` is the flagged highest-leverage pure-stdlib candidate.)
- **Design refs:** `stdlib/plan-stdlib.md §26`; `spec/11-stdlib.md §11.4a` (the 0402 reservation); the `/port` C.1 gap list (intake).
- **Acceptance:** self-tests green via the in-language runner; `conj` bare-promoted + DEF-1-guarded; the 3 constitutional invariants intact (FQ `primitives/<name>` reachable, empty prelude valid, reachability unchanged); free-standing discipline preserved; prior demos/exemplar replay green.

## Waves (Phase 4)

Organized from the Phase-3 plans. **Source-touching serialization rule (CLAUDE.md §Testing — worktree isolation broken):** any agent that edits `.rs`/`.cl` source runs **serially**, one at a time, and owns the single test run; read-only agents (audit passes, C.1 review) fan out in parallel. The Phase-3 SPRINT.md clobber (3 of 6 parallel design agents' edits survived) is the same hazard at the doc layer — **Phase-5 source agents return diffs/results; /sprint does not run two source-editors at once.**

### Wave 0 — Stage A green-and-clear (gates everything)

QA-first is already satisfied (the 4 guards exist + entry red-set verified == exactly 4). Source-editing `/dev` agents run **serially**:

| Step | Skill / agent | Crate | Task | Status |
|---|---|---|---|---|
| 0 | /qa | tests | Stage-A entry check — **DONE Phase 3** (red set == 4) | done |
| 1 | /dev | cranelisp-typecheck | FQ type-error renderer (`format_type_fq` @ `unify.rs`) + occurs-check renderer (in-pass) + unit test → 2 guards green | **done** |
| 1b | /qa | tests | collateral: 3 `spec_08_modules` assertions bare→FQ (spec-correct §5.3); 0416 (transient /dev FIXME) resolved+removed | **done** |
| 2 | /dev | src/ | **single invocation** both REPL fixes: `/disasm` on-demand re-derivation + `/info` clause-count + 3 unit tests → 2 guards green | **done** |
| R | /review | all | Wave-0 change-set review — **gate-ready, 0 Blocker/0 Important**; surfaced PIF/dead-accessor coupling → 0418 | **done** |
| 0418 | /arch → /qa → /dev | facades, tests, src/ | **RESOLVED by removal** (user-directed): dead `Introspection.disasm` field + `symbol_disasm()` accessor + PIF row entry deleted; on-demand `/disasm` intact; suite green | **done** |
| 3 | owning skills | fixmes | FIXME hygiene: /qa deleted 0414 ✓; /platform deleted 0405 ✓ (web showcase confirmed shipped); /spec resolved 0412 ✓ (19 flipped, 7 kept w/ rationale, `--mode check` 0); /repl resolved 0413 ✓ (gap clauses green, 20 flipped, `--mode check` 0); rest confirmed-deferred | **done** |
| gate | /sprint | — | `cargo nextest run --workspace` green (**2833/0/0 ✓**); ledger Resolved-removals (**4 guards removed, 0 intentional guards remain ✓**); FIXME store triaged (**✓ all tail closed**) | **✅ MET — Stage A CLOSED** |

_Steps 1+2 ran serially. 0418 resolved by removal (above). Stage-A tail closed 2026-06-20: 0405/0412/0413 all resolved+deleted; no source touched so suite stays 2833/0/0. **Stage A fully closed.**_

### Wave 1 — two threads on the green base (parallel across threads, serial within source-edits)

**Audit thread (read-only — fans out in parallel):**

| Step | Skill | Surface | Task | Status |
|---|---|---|---|---|
| 1a | /review | all | LOC pre-pass → `audits/loc-s87.md` (3-column test-split, size-ranked) — **DONE**; rerank src/>backend>typecheck (R5c paid off) | **done** |
| 1b | /review (×8, parallel) | the 8 crates (R1 table) | per-crate fresh-view pass: reconcile named baseline + 7-lens checklist + file:line evidence; refresh current-state `.mmd` | **done** (8 `audits/{crate}-s87.md` + `.mmd`; 0 Blockers) |

**Stdlib thread (C.1 read-only ∥; C.2 source-editing serial):**

| Step | Skill | Surface | Task | Status |
|---|---|---|---|---|
| 1c | /port | exemplar (read-only) | C.1 adequacy review → collated gap list — **DONE** (G1–G10: 2 [COMPILER], 8 [STDLIB]; G3 `range` highest-leverage; filed 0416→/arch) | **done** |
| 1d | /stdlib | stdlib/ (source) | C.2 rollout — **DONE**: 97 self-tests green (14 modules, backing-file form to survive source-regen); `conj` promotion **HELD** (§11.4a reserves it — net 0 bare-promotion); G3 `range`(half-open)/G4 `char-to-digit`/G5 `replace-at` landed; suite 2833/0/0; **4 new defects surfaced** → repro pass | **done** |

_C.2 (1d) is source-editing — it must not run concurrently with Wave-0 `/dev` steps or with itself. C.1 (1c) is read-only and runs parallel with the audit. C.1's **[COMPILER]** gaps must reach Wave 2 before synthesis closes._

### Wave 2 — synthesis + gate

| Step | Skill | Task | Status |
|---|---|---|---|
| 2a | /arch | cross-cutting synthesis over all 8 crate findings + C.1 [COMPILER] gaps → `audits/s87-findings.md` (severity-ranked backlog); resolution-seam + host-callback-divergence (cite 0407) lenses | **done** |

**Wave-1b audit results (2026-06-20) — 8 crates, 0 Blockers, ~80 findings; the cross-cutting themes the synthesis must rank:**
- **T1 — FQ-rendering / `Type`-walk duplication (HIGH leverage).** `cranelisp-types` audit: the `Type`-enum walk is now copy-pasted **5×** across 3 crates (bare `Type::Display` + 2 dead exports in types; `format_type_fq` in typecheck (Wave-0 add); 2 FQ renderers in `src/display.rs`). Wave-0 was correct-but-symptom and *deepened* it. **Recommendation: consolidate into one parameterized walk in `cranelisp-types`** (conventions as config — preserves the /arch keep-distinct advisory at the output level). The type-rendering analogue of the DEF-1 single-seam question.
- **T2 — `vec_set_copy` RC asymmetry (paired, cross-crate).** Confirmed from BOTH sides: backend F3 (`vec_codegen.rs:404` compensation dance) + intrinsics NEW-2 (`vec_runtime.rs:220` unconditional inc). Sibling `vec_push_copy` is the symmetric model. Fix = stop the runtime inc + delete the backend compensation **as one paired change** (one side alone re-opens FIXME 0296 UAF). Primitives MED-2 (`str_split/join` hand-roll Vec writes) is a third witness.
- **T3 — Host-callback / JIT-vs-`--link` divergence (DEF-6 root enabler; 0407 prerequisite).** Confirmed structural from src/ F-B + platform F2: `HostCallbacks` is **hand-constructed at 2 production sites in 2 crates with no shared builder** (`src/platform.rs:253` + `cranelisp-exe-bundle/src/lib.rs:131`); agree only via a comment. Backend confirmed CLEAN (identical CLIF both modes — divergence is at the platform/intrinsics ABI boundary). **Fix = one shared consumer-side `HostCallbacks` builder — and it is the prerequisite for safely landing 0407.**
- **T4 — DEF-1 codegen-batch seam (the residual).** typecheck: the resolution seam is ONE, correctly wired (mono-collection chokepoint now routed). BUT src/ F-A: `derive_codegen_batch` (`worker.rs:599`) never consults `prelude_fallback` → codegen-scope and typecheck-scope disagree about reachability; that disagreement IS DEF-1's residual. + F-G: prelude-fallback re-inlined at 2 off-canonical src/ sites.
- **T5 — Dead-path / dead-export class (the 0418/produce_disasm class).** backend F2 (`Jit::compile_defn`/`build_compile_context`/`CompileArtifacts.disasm` dead-in-prod); types F2 (2 dead public exports); typecheck F6 (`lookup_constructor_type` "user"-default); intrinsics NEW-4 (`is_runtime` unused).
- **T6 — Persistent duplication families.** backend F1 (two `build_isa`) + F5 (`emit_extern_call_1..4` ladder); frontend F2 (two synthetic-Sexp DSLs); primitives MED-1 (three-edit registration seam — the `neq-string` defect-class seam, still no omission guard); src/ F-G/F-L.
- **T7 — Over-budget functions** (typecheck `monomorphise_call` ~307L; backend `compile_resolved_call` grew to 271L; src/ `try_cache_hit_load` ~254L, `CompilerSession::new` ~216L) and **T8 — interim-arch residue** (types F3: SymbolTable DashMap concurrency migration in limbo 3 sprints).
- **Unsafe audits PASS** (intrinsics: 1 missing `// SAFETY:` on `call_continuation` io.rs:407; platform: exemplary). **Per-crate baseline reconciliation: strongly positive** — most prior HIGH findings resolved; the durable misses are the duplication families (T1/T6) — the recurring-class signal per `feedback_review_root_cause_and_duplication`.
| gate | /sprint + user | **scope-decision gate**: with the backlog in hand, decide what must land before Phase H opens; surface release-tier U1–U4 + agent U1–U6 sign-offs | **AWAITING USER** |

**C.2 /stdlib rollout DONE (2026-06-20).** 97 self-tests green across 14 modules — authored as **separate backing files** (`<module>/test.cl` + bare `(mod test)`) because inline `(mod test)` bodies are silently stripped by source-regen extraction (spec §8.2.5) when the lib dir is the in-place `stdlib/` (D-regen defect — a full nextest run corrupted the tree on the inline form; backing-file form is byte-stable, md5-verified). **`conj` HELD** — the actual /spec 0402 §11.4a ruling RESERVES `conj` (the C.2 plan's proposed §26.2 wrongly assumed it was free); deferred to spec → net **0 bare-promotion** this sprint; capability stays module-qualified-reachable. **G3 `range`** (half-open `[lo,hi)` Clojure semantics), **G4 `char-to-digit`/`digit-to-char`** (shipped `-to-` not `->` — D-name defect: `->` in a defn name parses as threading head), **G5 `replace-at`+`str-assoc`** landed with self-tests. Suite 2833/0/0; exemplar+demos replay green; free-standing preserved. **4 defects surfaced → repro pass** (`stdlib/plan-stdlib.md §26.6`): D-either (discover-tests SIGBUS on `(Either String Int)`→/backend), D-name (→/frontend), D-default (nullary return-type-poly trait method codegen→/typecheck), D-regen (source-regen strips inline `(mod test)`→/int+/qa).

**User-directed verification pass (2026-06-20):** user is skeptical of the audit findings — directed (a) render the 8 `.mmd`→`.svg` for review, (b) **repro the issues** (separate real defects from audit over-claims), (c) scope **clearing ALL non-Phase-H FIXMEs** ("don't want to carry anything"). Launched: /qa repro pass (the 4 C.2 defects + audit latent claims B1/DEF-2-conj/T2/host-callback — failing-not-ignored for what reproduces, explicit "does-not-reproduce" for over-claims) + read-only clear-all-FIXMEs cost assessment (`audits/s87-clear-all-fixmes.md`). SVG: user chose **view `.mmd` directly** (committed sources; no render — no renderer installed + disk 88%). No SVG artefacts generated.

**Clear-all-FIXMEs assessment DONE (`audits/s87-clear-all-fixmes.md`).** The 10 non-Phase-H FIXMEs clear by THREE different mechanisms — the decisive framing for "don't carry anything":
- **Kind A — debt-closure (6, safe to force-clear):** 0406, 0409, 0415, 0417, 0419, 0420 (consolidate already-correct code / write a missing test+doc; S/M, low-med risk).
- **Kind B — design-ruling-gated (2):** 0410 (needs /spec §8.11.4 — `lib-dirs=[]` footgun), 0416 (needs /spec shift-semantics; a new permanent primitive surface).
- **Kind C — feature-build dressed as a FIXME (2):** 0407 (Model-B closure-callback, **ABI v3→v4**, L, high-risk) + 0408 (Sudoku parallel-search rework, L). Clearing these = BUILDING features, not closing debt.
- **Hard orderings:** 0419→0407 (prereq); **0417 paired-or-UAF** (backend+intrinsics one change-set, co-fix DEF-2 `conj`); 0410 after §8.11.4 ruling; 0408 soft-deps 0416 + Phase-H Tier-2.
- **Bottom line:** zero *debt* carries ≈ **1 sprint** (6 kind-A + 0410 post-ruling, serialized by the single-source-agent constraint). Zero *FIXME* carries additionally needs **building or retracting 2–3 features** — honest disposition for 0407 if literal-zero is required = **retract Model B** (Model A already serves the showcase), fold 0408 into the Phase-H arc.

**HYGIENE EXECUTION LOG (2026-06-21):**
- **Wave 3 — defects: COMPLETE (3/3, suite 2846/0/0 full green).** (1) **heap-vec SIGSEGV** → root cause was NOT the audit's vec RC-asymmetry but a **last-use-analysis soundness bug** (`backend/heap.rs compute_last_uses` used textual pre-order as a liveness proxy — wrong for a var re-passed in a self-recursive tail call → COW mutate-in-place freed a still-live var); fix records direct-Var occurrences after nested subexprs (backend-only). (2) **D-default** → owner was **typecheck not backend** (repro had guessed /backend): `try_resolve_trait_method` bailed `Ok(None)` for nullary methods; now dispatches on recorded return type when `Self` is in return position. (3) **D-name** → reader symbol-char set excluded interior operator chars; `char->digit` split; fix absorbs interior operator-runs into symbols, preserves standalone `->`. **FIXME 0421 filed (→/spec)** to reconcile `spec/01-lexical.md §1.4.1` grammar. Each fix landed with a mandatory unit test. *Takeaway: the audit's defect framing was wrong on 2 of 3 root causes — the repro+fix discipline corrected visible-vs-true owner each time.*
- **Wave 4 — test extraction: COMPLETE (all 8 crates, ~32,500 test LOC → sibling files, uniform convention).** backend ~10,650 (`lib.rs` −78%), src/ ~5,850, intrinsics ~4,199, frontend ~4,126 (`ast_builder` −57%), typecheck ~3,150, types ~2,228, platform ~1,249, primitives ~1,106. Every crate's test count unchanged; suite green (2846/0/0) throughout; no production code displaced (diff-verified per file); `public-api.txt` untouched. The maintainability pass under-scoped (headlined only 4 crates) — all 8 done for uniformity.
- **Wave 5 — decomposition: APPROVED FULL (user, 2026-06-21) — "coherent and cohesive modules of manageable size", design-first, staged into sub-waves.** Each sub-wave = /design (module boundaries) → /dev (execute, behavior-preserving, suite-green gate) → /review (coherence + no-regression). SERIAL throughout.
  - **5a** backend `control_flow.rs` (1463) → let_if / lambda / par_bind / fn_as_value / drop_glue (+ dedup 4-site capture-RC-inc)
  - **5b** backend `compiler/mod.rs` (1279) → resolution / context / fn_compiler / rc_emission (+ 4-site import-chain walk → one `resolve_chain`; + 3-site `emit_extern_call_*` dedup)
  - **5c** src `process_form.rs` (1765) → macro_resolution / macro_clause / form_dispatch / cluster / cache_restore (+ src-side prelude-fallback dedup)
  - **5d** src `session_v4.rs` (1428) → types / shared_state / lifecycle / nice_worker / test_runner
  - **5e** typecheck `traits.rs` (1718) — L/HIGH-RISK, deep /design first → trait-method resolution / impl-storage / monomorphise / dispatch (`monomorphise_call` ~307L) (+ tc-side prelude-fallback dedup)
  - **5a DONE** (`design/backend/s87-decomposition.md` §5a): `control_flow.rs` 1463→47-line hub + 7 submodules; capture-RC-inc dedup 5→2 helpers; `compile_par_bind_continuation` split; backend 243/243, workspace 2846/0/0, public-api byte-identical.
  - **5b DONE** (§5b): `compiler/mod.rs` 1281→33-line hub + 4 submodules (`resolution`/`context`/`fn_compiler`/`rc_emission`); import-chain 4-driver dedup→`resolve_chain`/`resolve_driven` (~120 LOC, equivalence-verified); `compile_body` split; `CompileContext` `pub use`; public-api byte-identical. **`emit_extern_call_*` ladder dedup deferred** (it's in vec_codegen/control_flow, separate S-task — backlog).
  - **5c DONE** (`design/int/s87-decomposition.md` §5c): `process_form.rs` 1765→360-line parent + 6 submodules; `try_cache_hit_load` 254L→44-line orchestrator; `dependency.rs` kept cohesive; src 1468/1468, workspace 2846/0/0.
  - **5d DONE** (§5d): `session_v4.rs` 3139→531-line parent + 5 submodules; `compile_module_object` + `CompilerSession::new` split; `set_tc_modules` setter; `re_register_module` kept on parent (PIF row_45 guard); Wave-0 disasm removal intact; 1468/1468, 2846/0/0.
  - **5e DONE** (`design/typecheck/s87-traits-decomposition.md`, HIGH-RISK): `traits.rs` 2824→63-line hub + 5 submodules; `monomorphise_call`→8 phases (P4 subst isolation preserved, 0344 guard intact); bulk-scan dedup (`find_trait_method_decl<R>`, HKT-vs-bool distinction preserved); D-default helpers kept with resolver; typecheck 435/435, workspace 2846/0/0, **public-api byte-identical**, `mod traits` still private.
  - **WAVE 5 COMPLETE** — all 5 modules decomposed, behavior-preserving, suite green throughout. Deferred: `emit_extern_call_*` ladder dedup (vec_codegen/control_flow, separate S-task); src-side prelude-fallback dedup (repl.rs 2 sites, with the root-tier `root:bool` subtlety).
  - **/review of Wave-5 decompositions: batched to close** (each /dev self-verified green + public-api-identical + equivalence-checked; consolidated coherence review pending).
- **Remaining hygiene:** emit_extern_call dedup; src-side prelude-fallback dedup; consolidation FIXMEs 0417 (vec RC — latent) + 0420 (FQ-walk → types); cheap kind-A FIXMEs 0406/0409/0415; consolidated Wave-5 /review.
- **⚠ LARGE UNCOMMITTED TREE:** entire sprint (defects + ~32.5k LOC test extraction across 8 crates + 5 module decompositions) is uncommitted working-tree state. Suite green (2846/0/0) + per-crate public-api byte-identical. Checkpoint commit advisable (pending user — no commit without request).

**SCOPE EXPANSION → FULL HYGIENE SPRINT (user, 2026-06-21).** "This is a hygiene sprint so we now want to address all those points." S87 expands from audit-only to **execute the maintainability backlog in-sprint**:
- **IN scope (execute now):** the 3 real defects (D-name /frontend, D-default /backend, heap-vec SIGSEGV /backend); **test→sibling-file extraction** (all crates, `backend/lib.rs` first); **oversized-module decomposition** (the 5 + cheap dedups `emit_extern_call_*`, prelude-fallback walk); **non-host-callback consolidation** 0417 (vec RC alignment) + 0420 (FQ Type-rendering walk); the cheap kind-A FIXMEs (0406, 0409, 0415).
- **DEFERRED to Phase H (user):** **host-callback builder 0419 + Model-B 0407** — "definitely Phase H (if we even go that way)"; the **concurrency direction (B vs C) is a Phase-H decision**, not S87. 0408 (Sudoku parallel-search) follows the concurrency call → Phase-H-arc. 0416 (bitwise) + 0410 (Cranelisp.toml) are /spec-ruling-gated features — confirm separately.
- **Execution discipline:** ALL source-editing, so strictly SERIAL (single source-agent; worktree isolation broken). Order: defects → test extraction → decomposition → consolidation (extraction precedes decomposition so splits are legible; defects first for safety; control_flow.rs touched by both a defect-area and a decomposition → defect first).
- **SVG render BLOCKED (env):** aarch64 VM + no system Chromium + Google ships no arm64-Linux Chrome-for-Testing → puppeteer auto-download 404s, mmdc can't render. `.mmd` committed + viewable elsewhere; to render here needs `sudo apt install chromium-browser` then point mmdc at it.

**REPRO VERDICT (2026-06-20) — user-directed; the audit was PARTLY over-claimed.** /qa repro'd 7 candidates across REPL/`--run`/`--link`. Suite now **2838 run / 2834 passed / 4 RED** (4 new failing-not-ignored guards; ledger updated).
- **REAL defects (3 — failing tests are the record, no FIXMEs):**
  - **D-name** (`->` in a `defn` name fails to parse — read as threading head) → **/frontend**. `tests/spec_05_definitions.rs::defn_name_with_arrow_in_symbol_parses` (RED) + green control.
  - **D-default** (nullary return-type-poly trait method → `undefined function` at **codegen**, not typecheck) → **/backend**. `tests/spec_07_traits.rs::nullary_return_poly_trait_method_dispatches_at_codegen` (RED).
  - **Heap-element-vec borrowed-recursive RC UAF** (the genuinely serious one — **SIGSEGV 10/10 at depth 2**, REPL + `--run`; Int analog fine) → **/backend**. `tests/spec_12_runtime.rs::vec_push_heap_element_borrowed_recursive_source_no_uaf` (REPL) + `_run`. This is the deterministic root cause behind the intermittent C.2 **D-either** discover-tests SIGBUS (the stdlib runner copies a heap-element `(Vec (Pair…))`).
- **OVER-CLAIMS / masked / latent (4 — do NOT reproduce; S86 fixes hold):**
  - **B1 / DEF-1 codegen-batch seam — DOES NOT REPRODUCE** (the synthesis's "#1 must-fix, only one with a committed red repro" was WRONG). Prelude-glob `defn` incl. `count` wrapping `vec-len` in a consuming dep runs correctly under `--run` AND `--link`; existing `def1_…batch` test passes. **Downgrade from must-fix to latent/theoretical.**
  - **B2 / simple `conj` corruption — DOES NOT REPRODUCE** (sound across all modes incl. 500× sustained + COW). Only the borrowed-recursive vec-**push** shape (above) is live.
  - **T2 / `vec_set_copy` uniformity — correct as shipped, latent only** (audit itself conceded "correct, suite green"). The real vec-RC bug is the borrowed-recursive **push** UAF, not the set-copy symmetry.
  - **D-regen — DOES NOT REPRODUCE** (inline `(mod test)` extraction is byte-stable; the S86 corruption was a test-isolation artifact under parallel nextest, already mitigated). Hygiene, not a compiler defect.
- **Gate impact:** the must-fix-before-Phase-H list is RESHAPED — **drop B1** (doesn't repro); the real must-fix is the **memory-safety SIGSEGV** (heap-vec borrowed-recursive RC) + D-name + D-default. The FQ-walk/host-callback/vec-set *consolidation* items (0417/0419/0420) stand as latent-hygiene, not active bugs.

**MAINTAINABILITY DEEP-PASS (2026-06-20) — `audits/s87-maintainability.md`; the part the per-crate audits under-delivered (user-flagged).** The defect-skewed passes missed the chartered simplicity/maintainability focus; this pass produces it:
- **Test→sibling-file extraction** (convention ALREADY in use by typecheck: `#[cfg(test)] mod tests;` → sibling `foo/tests.rs`): **all S-effort, zero-risk, ~12–20k LOC out of production files.** Headline `backend/lib.rs` (~4,200 of 6,785 lines inline test → ~79% smaller); also `frontend/ast_builder.rs` (~1,830), src/ cluster (`worker.rs`/`session_v4.rs`/`observability.rs`/`scheduler.rs`/`process_form.rs` ~3,300), `frontend/reader.rs`, intrinsics. **Recommended FIRST move** (makes on-disk sizes match corrected LOC + makes decomposition legible).
- **Oversized-module decomposition (top 5):** `src/process_form.rs`(1765)→5 mods (`try_cache_hit_load` ~254L); `src/session_v4.rs`(1428)→5 mods (`compile_module_object` ~309L); `backend/compiler/mod.rs`(1279)→4 mods (+4-site import-chain walk→one `resolve_chain`); `backend/compiler/control_flow.rs`(1463)→5 mods (+dedup 4-site capture-RC-inc); `typecheck/traits.rs`(1718)→L/high-risk, needs /design first (`monomorphise_call` ~307L). Cheap dedups: 3-site `emit_extern_call_*`, 6+-site prelude-fallback walk.
- **Honesty check (same skepticism as the repro pass):** verified-and-REJECTED two per-crate over-claims — the session_v4↔repl handler "byte-identical duplication" is FALSE (handlers only in repl.rs); the "552-line `fresh_instantiation_subst` god function" is FALSE (~16 lines).

**Wave-2 synthesis results (2026-06-20) — `audits/s87-findings.md`.** /arch reranked /sprint's draft: **T2 (RC labor-split) #1, T4 (DEF-1 seam) #3 ahead of T1 (FQ-walk #4)**. Must-fix-before-Phase-H shortlist:
- **B1 / DEF-1 codegen-batch (T4) — MUST.** Only theme with a committed red repro; codegen-scope ≠ typecheck-scope reachability; Phase H would ship it. Additive, low-risk (thread `prelude_fallback` into `derive_codegen_batch` `worker.rs:599`).
- **B2 / vec RC-model alignment (T2) — LEAN MUST, paired with the DEF-2 `conj` defect** (same root: Vec-element RC discipline across backend+intrinsics). Paired-change-or-UAF.
- **B3 / shared HostCallbacks builder (T3) — MAYBE, conditional**: gate-in iff 0407 (Model-B) is on the near roadmap; else defer (it is the 0407 prerequisite — do not widen HostCallbacks ×3 fields ×2 sites before one builder exists).
- **B8 / SymbolTable concurrency target — owed /arch DECISION (not impl):** rule before Phase H whether the DashMap-inner+atomic target is still live or has converged on the simpler `&mut self` model (3 sprints stale).
- Phase H still gates on 0050/0052/0365; S87 adds B1/B2 (+B3 conditional) + the B8 decision. Release-tier U1–U4 / agent U1–U6 = user decisions at the gate, not /arch ranking.

**Chartered answers:** (a) `derive_codegen_batch` IS the one remaining codegen-side seam that must consult the prelude fallback — the unification is "codegen-scope asks the same reachability question typecheck does," via B1, NOT a resolution-engine merge. (b) YES — the shared consumer-side HostCallbacks builder is the right fix AND truly the 0407 prerequisite (gate-in only if 0407 scheduled).

**Recurrence escalations:** T1 (FQ-walk ×5 — Wave-0 deepened it) + T6 (duplication families) → process note: a duplicate family seen in 2+ consecutive audits is past-threshold, flag Important not Suggestion. **FIXMEs filed:** 0417 (→/arch, vec RC alignment), 0419 (→/arch, HostCallbacks builder), 0420 (→/arch, FQ Type-rendering consolidation). B17/DEF-2 `conj` = failing-test record, no FIXME. Per-crate `/dev` items (B5–B15) owned by each crate's triad in the per-crate audits.

## Notes

- 2026-06-20: S86 closed (`--workspace` 2829 run / 2825 passed / 4 intentional guards / 0 skipped). S87 opened.
- Scope shape (user, 2026-06-20): green-and-clear FIRST, then audit; one pass per crate; refer to prior audit findings first; depth assured by baseline-reconciliation + fixed-lens checklist + file:line evidence + /arch cross-cutting synthesis.
- LOC measurement folded in (user, 2026-06-20): `tokei` per-crate/per-module test-vs-non-test, size-ranked, large modules → deeper scrutiny. Audit produces durable artefacts (LOC table, refreshed per-crate current-state `.mmd`, consolidated findings).
- Stage C added (user, 2026-06-20): stdlib self-test rollout + bare-verb promotion back IN-scope, plus a `/port` exemplar-driven stdlib-adequacy review → collated gap list (awkward-to-express sites where the stdlib lacks an obvious feature); pure-stdlib gaps actioned in-sprint, compiler/language gaps fed to the audit backlog.
- 0402 (/spec curated-overload naming) pulled into Stage A action (user direction toward inclusiveness).
- Phase 1 scope APPROVED by user (2026-06-20) → advanced to Phase 2 arch review.
- Phase 2 /arch verdict (2026-06-20): APPROVE-WITH-REVISIONS; R1–R6 applied above. Forward obligation recorded: if the synthesis confirms the **JIT-vs-`--link` host-callback divergence** (DEF-6 + 0407 two faces) as a real cross-crate pattern, it becomes a backlog item feeding the scope-decision gate and, if scheduled, a future `bounded-contexts.md` §3/§5/§6 edit — NOT an S87 edit.
- **Phase 3 DONE (2026-06-20):** 6 design agents (/spec, /qa, /design typecheck, /design src/, /stdlib, /port). Outputs — 0402 RESOLVED+deleted (spec/11-stdlib §11.4a + 07-traits §7.12.2); test plan `tests/plan/s87-test-plan.md` + entry red-set verified == 4; `design/typecheck/typecheck.md §8.3`; `design/int/int.md §4.3/§8.2.1/§8.2.2` (corrected a STALE doc claiming eager disasm); `stdlib/plan-stdlib.md §26`; `exemplar/notes-stdlib-adequacy-s87.md` (recon C1–C10). Exit gate met: no interface delta, /qa ready to draft tests, design docs current.
- **Methodology finding (Phase 3):** 6 design agents dispatched in parallel; 3 edited SPRINT.md concurrently and the index race left only 3 of 6 plans (the other 3 returned text, transcribed by /sprint). **Lesson:** Phase-3/5 agents must return their plan/diff as text for /sprint to transcribe, NOT edit SPRINT.md directly — the §Testing serial-source rule extends to the shared plan doc. Applied to the Wave plan.
- **Phase 4 DONE (2026-06-20):** waves organized (above); source-editing steps serialized (Wave-0 step1 then step2; C.2 not concurrent). Ready for Phase 5 (ACTIVE) pending user go-ahead — Phase 5 is the first phase that edits compiler source.
- **Phase 5 Wave 0 — core DONE (2026-06-20):** all 4 Stage-A guards green; `cargo nextest run --workspace` = **2833 passed / 0 failed / 0 skipped**. Serial source-edits held (typecheck → /qa collateral → src/). /review verdict gate-ready (0 Blocker/0 Important). Ledger: 4 guards Resolved-removed, **canonical run now 0 intentional guards** (any RED is now a regression). FIXMEs: 0402 (Phase 3) + 0414 + transient 0416 deleted; **0418 filed (→/arch)** — PIF row freezes the now-dead `symbol_disasm`/`Introspection.disasm` (Stage-B backlog seed, fold into Wave-2 synthesis). Wave-0 tail (non-blocking): 0405 delete (/platform), 0412/0413 residual (/spec, /repl).
- **Emergent in-pass fix (METHOD §Phase 5):** the typecheck FQ fix also covered the occurs-check renderer (`unify.rs:135` class) in-pass; the deeper `traits.rs:1157/:1804` no-impl renderers (bare via `concrete_type_name`, need name reconstruction) were correctly left to the Stage-B backlog.
- **Stage A CLOSED + Wave 1 opened (2026-06-20):** tail cleared in parallel (0405 /platform delete; 0412 /spec resolve — 19 flipped/7 kept, `--mode check` 0; 0413 /repl resolve — gap clauses green/20 flipped, `--mode check` 0), no source touched → suite stays 2833/0/0. **Wave 1a LOC pre-pass** (`audits/loc-s87.md`): R5c test-split rerank = **src/ 13.6k > backend 9.5k > typecheck 6.9k** (raw 31k typecheck was 68% test — would've over-allocated 3×); deep-scrutiny top: `typecheck/{program,traits,checker,infer}.rs`, `src/{process_form,repl,session_v4}.rs`, `backend/compiler/{control_flow,mod,vec_codegen}.rs`. **C.1 /port** complete: G1–G10 (2 [COMPILER]: G1 bitwise intrinsics→FIXME 0416, G2 DEF-2 conj RC; 8 [STDLIB]: G3 `range` top win, G4 `char->digit`, G5 `str-assoc` authoring + 5 adoption). Now dispatching Wave 1b (8-crate audit fan-out) + 1d (/stdlib C.2). Note: /port reused number 0416 for the bitwise FIXME (prior 0416 was deleted; no collision but history-confusing) — left as-is; next FIXME = 0417.
- **0418 RESOLVED by removal (user-directed, 2026-06-20) — not deferred to Stage B.** User chose option (a): delete the dead disasm machinery now (disasm is on-demand). Serial 3-agent vertical, suite green at each step: **/arch** dropped `symbol_disasm` from the canonical accessor enumeration (`d1-introspection-repl-only.md` §"Reader handling" — the S81-retired `facades/int.md` the FIXME cited; corrected) + `bounded-contexts.md §6` + `sequences/exec-flow-compilation.mmd`, deleted 0418; **/qa** relaxed PIF `row_42` (8→7 accessors); **/dev** removed `Introspection.disasm` field (`session_v4.rs:301`) + `symbol_disasm()` accessor + `worker.rs:1764` None-assertion + 3 stale doc-comments. Final: `--workspace` **2833/0/0**, `cargo check -p cranelisp` 0 warnings (−1). Live `/disasm` on-demand path + e2e guard intact. (Ops: disk hit 100% mid-run; agent cleared `target/debug/incremental` — safe rebuild cache — to finish.)

## Outcome (Phase 7)

_Pending close._
