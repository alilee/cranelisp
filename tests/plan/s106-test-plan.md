# S106 test plan — FIXME burn-down (REPL/agent usability + aging-item drain)

**Author:** `/qa` · **Date:** 2026-07-09 · **Status:** Phase 3 (design) deliverable —
planning only; test authoring is Phase 5 Stage 1. Consumed by `/sprint` for wave planning
(`sprints/SPRINT.md` §"Skill plans (Phase 3) → /qa").

**Inputs:** `sprints/SPRINT.md` (the FIXME-debt workstream tables A–J + §"Architecture review
(Phase 2)" rulings 1–5 + the coherence pass); the in-scope FIXME files
`design/arch/fixmes/{0538,0539,0540,0541,0542,0543,0545,0546,0548,0549,0550,0551,0365,0416,0496,0498,0499,0544}-*.md`;
`tests/CLAUDE.md` (two-tier strategy; unit-test-per-fix; failing-not-ignored; fresh-tmpdir;
`--link` prereq script); `tests/plan/coverage-audit-s101.md` §2.4 (L-S1 lane definition) / §2.5
(4 standing drafting rules); `tests/plan/s103-test-plan.md` §1.6 + §9 (the S103 L-S1 partial
landing this plan generalizes); `repl/spec.md` §0.2.1/§0.6.1/§0.6.2/§3.3/§4.1.4/§10.1/§15.4/§17.19/§18.8;
`spec/appendix-a-builtins.md` §A.3; `spec/08-modules.md` §8.5.2; `spec/05-definitions.md` §5.2.6.

**Discipline pinned (binding on every S106 drafted test):**
- **Two tiers, no middle.** Every `/qa` deliverable below is **e2e** (`tests/*.rs`, subprocess
  `Cranelisp` builder). Where a fix needs a **unit test** (mandatory per the per-fix rule), the
  owning **`/dev` (crate)** authors it in the crate's `#[cfg(test)]` module — those are **named
  here as `/dev` obligations, NOT authored by `/qa`.** `/qa` never writes `crates/*/src` unit
  tests nor `src/` unit tests.
- **Failing-not-ignored.** Every new e2e for a confirmed defect or a behaviour-change lands
  **RED, un-ignored**, with a `// spec:` anchor and a ledger row; it flips GREEN in the owning
  skill's fix change-set. `/qa` observes the flip, annotates the ledger row in place, never
  deletes/weakens.
- **Exact-output over substring** (S101 drafting rule 2) for every shape-pinning MUST: exact
  line(s) via `assert_stdout_eq` / `assert_golden` / `assert_golden_masked`, not
  `assert_stdout_contains`. Error-shape and diagnostic assertions keep substring per
  `tests/CLAUDE.md` §Test Standards.
- **Positive AND negative** for every MUST that constrains what appears (`_neg_`/`_not_` naming).
- **The 22 intentional failing-not-ignored guards are untouched.** Every S106 RED below is
  ADDITIONAL. Root-`CLAUDE.md` §Testing itemizes the 22; none are in this plan's edit set.

**WS-A / read-loop serialization honoured in test SEQUENCING (not in authorship).** The Phase-2
coherence pass co-schedules the `save.rs`/Pass-0-peel fixes (**0538, 0548, 0549**) in one
`/dev (src/)` serial slot and the `src/main.rs` read-loop fixes (**0544, 0551**) in another.
The tests for each cluster are **independently authored** (one repro per FIXME, separately
runnable) but are **grouped in this plan by cluster** so `/sprint` can gate each cluster's REDs
against its single serial `/dev` slot. No test depends on another test in its cluster.

---

## §0 Scope map — every in-scope item to its `/qa` deliverable

| FIXME | Owner (fix) | `/qa` e2e deliverable | Category | RED/GREEN at draft |
|---|---|---|---|---|
| 0541 | /dev(src) | `tests/agent.rs` — multi-tool-call batch e2e (feature-gated) | RED-first defect | RED (panics today) |
| 0542 | /dev(src) | `tests/repl_introspection.rs` — user-module trait bare-lookup | RED-first defect | RED |
| 0546 | /dev(src) | `tests/repl_introspection.rs` — `/imports` prelude group layout | RED-first defect | RED |
| 0548 | /dev(src) | `tests/repl_persist.rs` — failed-import-not-persisted (+ `--run` e2e) | RED-first defect | RED |
| 0551 | /dev(platforms+src) | `tests/repl_lifecycle.rs` — piped read-line reachable seams | RED-first defect | RED |
| 0539 | /repl→/int | `tests/agent.rs` — flip no-op→error guards | behaviour-change guard | RED |
| 0540 | /repl→/int | `tests/search.rs` — docstring axis + ranking | behaviour-change guard | RED |
| 0543 | /repl→/int | `tests/search.rs` — exact-in-scope surfacing + ranking | behaviour-change guard | RED |
| 0545 | /repl→/int | `tests/repl_introspection.rs` — L3 packing reconcile | behaviour-change guard | RED-or-rebaseline |
| 0549 | /dev(src) | `tests/repl_persist.rs` — `__expr` not persisted (+ `--run`) | behaviour-change guard | RED |
| 0550 | /dev(src) | `tests/link.rs` — `--link` output name/collision | behaviour-change guard | RED |
| 0538 | /dev(src) | `tests/repl_persist.rs` — trait/type regen fidelity e2e | behaviour-change guard | RED |
| 0365 | /spec,/dev | `tests/spec_field_accessor.rs` — `Type.member` field accessor | behaviour-change guard | RED (gated on impl) |
| 0416 | /spec,/dev | `tests/spec_appendix_a_bitwise.rs` — verify/extend existing | behaviour-change guard | RED (gated on /spec) |
| 0496 | /dev(src) | **none** — /dev unit-tier; `/qa` verifies + names residual | n/a | — |
| 0498 | /dev(types) | **none** — /dev unit-tier; `/qa` names the drift-guard | n/a | — |
| 0499 L-S1 | /qa | `tests/repl_introspection.rs` + `tests/repl_redefinition.rs` — preamble grid generalization | robustness guard | GREEN |
| 0544 | /repl→/int | `tests/repl_lifecycle.rs` — non-TTY byte-identical | behaviour-change guard | GREEN (byte-identical) |

Counts at plan close: **§10**.

---

## §1 Workstream A — backing-file & read-loop cluster

### Cluster A1 — `save.rs` / Pass-0-peel (serial `/dev (src/)` slot): 0548, 0549, 0538

#### 0548 — a failed structural form (import/export/mod/platform) MUST NOT persist

Root cause (pinned): Pass-0 peel calls `record_*_on_symbol_table` BEFORE `handle_*`, so a
failed `import` is already on `symbol_table.imports` when a **later successful form** triggers
regeneration. Trigger is a subsequent successful form (bad-import-then-`/quit` does NOT persist).

| Test | File | Tier | `// spec:` | Observable (exact) | Pos/Neg | Cat |
|---|---|---|---|---|---|---|
| `persist_failed_import_not_written_to_backing_neg` | `repl_persist.rs` | e2e | `repl/spec.md §15.4` | Project seeded `user.cl`=`(defn seed [] 1)`; REPL: failing `(import [platforms.stdio [*]])` → good `(defn g [x] (mul-i64 x 2))` → `/quit`. Regenerated `user.cl` read via `read_tmp` **does NOT contain** `platforms.stdio` / the failed import line; **DOES contain** `defn g` and `defn seed`. | Neg (absence of phantom) + Pos (real defns present) | RED-first |
| `persist_bad_import_then_run_succeeds_e2e` | `repl_persist.rs` | e2e | `repl/spec.md §15.4` | Same session, then `Cranelisp::new().run(<project>)` / `run_again` on the regenerated project: exit 0 (or at least NOT the module-not-found error) — the end-to-end integrity guard crossing REPL-persist → `--run`. | Pos (clean run) + Neg (no `module ... not found`) | RED-first |
| `persist_failed_export_not_written_to_backing_neg` | `repl_persist.rs` | e2e | `repl/spec.md §15.4` | The shared-fix sibling: a failing `export`/`mod` (pick the one reachable through the REPL surface) then a good defn then `/quit`; regenerated file excludes the failed structural form. Pins the fix is applied uniformly, not import-only. | Neg | RED-first |

`/dev (src/)` **unit obligation (named, not `/qa`-authored):** a `src/process_form` seam unit
test that `record_imports_on_symbol_table` (and the export/mod/platform siblings) leaves NO
entry on `symbol_table.imports` when the paired `handle_*` returns `Err` — the record-after-
success ordering pinned at its seam.

#### 0549 — non-defining `__expr` forms MUST NOT persist to the backing file

Phase-2 ruling 3: `save.rs::generate_fns_and_macros` filters synthetic `__expr*`-named `UserFn`
entries from regen, symmetric with the `$`-mangled filter. The in-session symbol-table entry
still exists — only the source emission is suppressed.

| Test | File | Tier | `// spec:` | Observable (exact) | Pos/Neg | Cat |
|---|---|---|---|---|---|---|
| `persist_bare_expr_not_written_to_backing_neg` | `repl_persist.rs` | e2e | `repl/spec.md §15.4` | Project `user.cl`=`(defn seed [] 1)`; REPL: `(add-i64 1 2)` → `:primitives/Int 3` (**in-session eval still worked** — assert the result appeared) → `(defn g [x] (mul-i64 x 2))` → `/quit`. Regenerated `user.cl`: **no** top-level `(add-i64 1 2)` (nor any bare-expression form); **does** contain `defn g`/`defn seed`. | Neg (no expr form) + Pos (eval happened; defns present) | behaviour-change guard, RED |
| `persist_bare_expr_then_run_module_clean_e2e` | `repl_persist.rs` | e2e | `repl/spec.md §18.8` | Persist as above then `--run` / reload the project: the module loads with no re-materialised dead top-level expression (no double-eval side effect, no error). | Pos + Neg | guard, RED |

`/dev (src/)` **unit obligation:** `save.rs::generate_fns_and_macros` excludes `__expr*` names
(round-trip: an `__expr` symbol-table entry is present in the live table but absent from the
regenerated source string).

#### 0538 — source-first regen fidelity for `save.rs` §5–7 (traits/types)

`generate_traits`/`generate_types` render from stored sexp via `render_decl_sexp` (reformats
whitespace + desugars reader shorthand); section 8 already prefers the consistency-gated
verbatim source slice. Extend that discipline to §5–7.

| Test | File | Tier | `// spec:` | Observable (exact) | Pos/Neg | Cat |
|---|---|---|---|---|---|---|
| `persist_trait_decl_regen_preserves_source_formatting` | `repl_persist.rs` | e2e | `repl/spec.md §15.4` | Seed a `deftrait` with non-canonical formatting + reader shorthand in a module that ALSO has a fn triggering T1 reload; after a reload/regen the trait declaration in the regenerated file is **byte-identical** to the authored source (verbatim slice), not the pretty-printed reformat. | Pos | guard, RED |
| `persist_type_decl_regen_falls_back_to_pretty_on_mismatch` | `repl_persist.rs` | e2e | `repl/spec.md §15.4` | A `deftype` whose stored source does NOT re-parse to the recorded sexp falls back to `render_decl_sexp` (structurally faithful) — the fallback path is exercised, not silently dropped. | Neg (fallback fires) | guard, RED |

`/dev (src/)` **unit obligation (this is the primary tier for 0538 — the FIXME explicitly asks
for round-trip UNIT tests):** `save.rs` §5–7 verbatim-slice-when-sexp-matches / pretty-print-on-
mismatch, at the `introspection_sexp_and_source` + `verbatim_slice` seam. The e2e rows above are
the observable envelope; the unit round-trip is the seam guard.

**Sequencing note:** the three A1 clusters' REDs (7 e2e) all gate against the single serial
`save.rs`/Pass-0 `/dev` slot. They are independently runnable; `/sprint` may land 0548/0549
before 0538 (0538 is fidelity polish, non-blocking) within the one slot.

### Cluster A2 — `src/main.rs` read loop (serial `/dev (src/)` slot): 0551, 0544

#### 0551 — `read-line` leaves stdin `O_NONBLOCK`; REPL exits (BOTH seams)

Phase-2 §coherence ruling: fix at BOTH seams — **(A)** platform poll leaf
(`platforms/stdio/src/lib.rs::set_stdin_nonblocking`) restores fd-0 flags on terminal;
**(B)** host (`src/main.rs`) stops treating `WouldBlock`/`EINTR` as EOF (`Err(_) => break` →
distinguish genuine EOF from retryable). **(C)** split-brain `STDIN_BUF` is a pinned residual,
NOT redesigned in S106.

**Testability constraint (load-bearing):** the interactive-TTY exit only manifests on a real
TTY; the piped-stdin `Cranelisp` harness has **no PTY**. So the durable `/qa` e2e guards are the
**reachable piped-mode** behaviours (0551's piped-vs-interactive note), and the fd-flag-restore
and WouldBlock-≠-EOF seams get **`/dev` unit tests** (named below). A true PTY e2e is a
harness gap (see §6).

| Test | File | Tier | `// spec:` | Observable | Pos/Neg | Cat |
|---|---|---|---|---|---|---|
| `piped_read_line_does_not_leak_next_line_as_undefined_var_neg` | `repl_lifecycle.rs` | e2e | `repl/spec.md §10.1` | Piped REPL: a `main` calling `read-line`, then a following expression line piped after it. The next piped line MUST be consumed as intended input, NOT leak to the REPL reader as an `undefined variable` error. Assert: no `undefined variable` in stdout/stderr; the subsequent expression evaluates. | Neg (no leak) + Pos (next form evals) | RED-first |
| `piped_read_line_session_continues_after_eval` | `repl_lifecycle.rs` | e2e | `repl/spec.md §10.1` | Piped REPL: read-line `main` then a plain `(add-i64 4 5)` form; the second form's result (`9`) appears — the session did not terminate early after the read-line turn. | Pos | RED-first |

`/dev` **unit obligations (both seams — the FIXME's step-3 pins both):**
- **Platform (`/dev` platforms/stdio):** a fd-flags seam unit test asserting fd-0's `O_NONBLOCK`
  is **unchanged** (restored) after a `read-line` poll turn — seam (A).
- **Host (`/dev` src/):** the read-loop seam distinguishes `WouldBlock`/`EINTR` from EOF — a
  retryable error does NOT break the loop — seam (B).

The e2e piped guards + the two unit tests together satisfy the "assert BOTH seams" mandate at
the tiers each seam is reachable from.

#### 0544 — line editor / history (rustyline, TTY-gated)

Phase-2 ruling 1: rustyline, default-build, constructed ONLY on the interactive-TTY branch
(`std::io::IsTerminal`); the non-TTY path stays the **exact** `stdin.lock().lines()` code and is
**byte-identical**. Consent-line reader goes through the same single input abstraction (no
split-brain BufReader).

**Testability:** arrow-key/history behaviour is TTY-only, not drivable through piped stdin. The
durable `/qa` guard is the **non-TTY byte-identical** assertion (Phase-2's `/qa` obligation).

| Test | File | Tier | `// spec:` | Observable (exact) | Pos/Neg | Cat |
|---|---|---|---|---|---|---|
| `non_tty_repl_output_byte_identical_line_editor_off` | `repl_lifecycle.rs` | e2e | `repl/spec.md §10.1` | A fixed piped-stdin script (mixed defns + evals + a slash command) run through the REPL: capture stdout as a golden (`assert_golden`). This golden is captured on S106 HEAD **before** the 0544 change and MUST remain byte-identical **after** — the guard that rustyline never engages on the non-TTY branch. | Pos (identical) | guard, GREEN (byte-identical pre/post) |
| `non_tty_consent_line_read_unchanged` | `repl_lifecycle.rs` (or `agent.rs` if consent-gated) | e2e | `repl/spec.md §10.1` | If reachable non-agent: pipe a scripted session that exercises the next-line read path the consent seam uses; assert the piped line is consumed identically pre/post. If only reachable under `--features agent`, gate accordingly and note. | Pos | guard, GREEN |

**Explicit coverage gap (recorded, not hidden):** interactive up/down-arrow history recall,
inline editing, and cross-session history persistence are **TTY-only** and **not e2e-covered** —
flagged as manually-verified in the `/repl` demo. `/dev` **unit obligation:** if rustyline's
history buffer API is unit-drivable, a scripted history add/recall unit test in `src/`; else the
TTY surface is a documented manual-verification item.

---

## §2 Workstream B — symbol-enumeration display

### 0546 — `/imports` "Prelude (implicit)" group bypasses the shared layout

Root cause (pinned): the prelude group does its own one-symbol-per-line loop instead of routing
through `append_name_category`/`format_symbol_layout` (the L0–L4 formatter). §3.3 requires the
layout be shared verbatim by `/list`/`/imports`/`/exports`.

| Test | File | Tier | `// spec:` | Observable (exact) | Pos/Neg | Cat |
|---|---|---|---|---|---|---|
| `imports_prelude_group_uses_shared_layout` | `repl_introspection.rs` | e2e | `repl/spec.md §3.3` | `/imports` on a module with prelude fallback ON: the `Prelude (implicit):` names render multi-column (operators first, ≤6/line, letter-grouped) — assert the exact block is **byte-identical** to what `format_symbol_layout` produces for the same name set (not one-per-line). Use `assert_golden`/exact block compare. | Pos | RED-first |
| `imports_prelude_group_preserves_header_suffix_comment` | `repl_introspection.rs` | e2e | `repl/spec.md §3.4` | The `Prelude (implicit):  ; available via the prelude outer scope, …` header **suffix comment** is preserved AND the layout is applied — both, in one output. | Pos (annotation) + Neg (NOT one-per-line: assert no ≥N consecutive single-name lines) | RED-first |

`/dev (src/)` **unit obligation:** `handle_imports` routes the prelude names through
`append_name_category` while emitting the header suffix comment.

### 0545 — §3.3 L3 letter-group packing reconcile (spec example vs rule text)

The §3.3 L3 rule text says "append group if `current_count + group_size ≤ 6`, else flush"; the
illustrative example encodes the more-eager new-line-per-letter behaviour (`abs add ceil concat`
= 4, then `double drop` on a fresh row even though 4+2=6). `/repl` reconciles which is
normative; `/qa` audits whether the existing tests pin the disputed `4+2=6` boundary and
re-baselines the golden if the example was wrong.

| Test | File | Tier | `// spec:` | Observable (exact) | Pos/Neg | Cat |
|---|---|---|---|---|---|---|
| `list_layout_l3_pack_to_six_across_letter_groups` | `repl_introspection.rs` | e2e | `repl/spec.md §3.3` | The missing boundary case the existing `list_layout_l3_letter_group_early_break` does NOT pin: a name set where `current_count(4) + next_group_size(2) == 6`. Assert the reconciled packing — per Phase-2 route-to-`/repl`, if the L3 **rule text** wins, the two groups share the row (`… concat double drop`); if the **example** wins, `double drop` flushes to a fresh row. **Exact golden**, re-baselined in the fix change-set to the `/repl`-reconciled rule. | Pos | guard, RED-or-rebaseline |
| `list_layout_l3_neg_boundary_no_straddle` | `repl_introspection.rs` | e2e | `repl/spec.md §3.3` | Negative companion: a group that would push `current_count + group_size` to 7 MUST flush first (never straddle). Guards the reconciled rule's upper edge. | Neg | guard |

**`/qa` audit note:** the existing `list_layout_l3_*` goldens and
`layout_cross_command_list_exports_byte_identical` may encode the pre-reconcile behaviour. If
`/repl` rules the example wrong, these goldens **re-baseline in the same change-set as the fix**
(not silently — the re-baseline is the visible record of the behaviour change). The four
shared-formatter commands stay byte-identical post-fix.

---

## §3 Workstream C — `/search` discovery (both `/repl`-owned; co-scheduled)

The `/search` index seam is shared; 0540 (docstring axis) and 0543 (exact-in-scope + ranking)
land coherently. Existing coverage lives in `tests/search.rs` (`search_by_name_*`,
`search_by_scheme_*`, `search_neg_already_imported_not_relisted`).

### 0540 — `/search` also matches docstrings (new axis + ranking)

| Test | File | Tier | `// spec:` | Observable (exact) | Pos/Neg | Cat |
|---|---|---|---|---|---|---|
| `search_matches_docstring_only_hit` | `search.rs` | e2e | `repl/spec.md §17.19.1` | A query that appears in a symbol's **docstring** but NOT its name or scheme surfaces that symbol. Assert the symbol's result row appears. | Pos | guard, RED |
| `search_docstring_hit_ranked_below_name_scheme_neg` | `search.rs` | e2e | `repl/spec.md §17.19.1` | For a query matching one symbol by name/scheme and another only by docstring, the name/scheme hit is ranked **above** the docstring-only hit (per the `/repl` ranking ruling). Assert output ORDER (name/scheme row precedes docstring row). | Pos (ordering) + Neg (docstring hit NOT above name hit) | guard, RED |
| `search_docstring_no_false_hit_neg` | `search.rs` | e2e | `repl/spec.md §17.19.1` | A query matching NO name, NO scheme, NO docstring returns the self-documenting no-match note (existing `search_neg_no_match` shape) — the docstring axis does not manufacture spurious hits. | Neg | guard, RED |

If `/repl` pins §17.19.2 to show a docstring-match **excerpt**, add
`search_docstring_hit_shows_why_excerpt` asserting the snippet around the matched substring.

### 0543 — `/search` surfaces exact in-scope match + exact-above-partial ranking

`handle_search` filters every hit through `is_already_in_scope`, so an exact in-scope match
(`show`, prelude-reachable) is dropped while four partial out-of-scope matches (`trace-show*`)
survive; results sort alphabetically, so exact never precedes partial.

| Test | File | Tier | `// spec:` | Observable (exact) | Pos/Neg | Cat |
|---|---|---|---|---|---|---|
| `search_exact_in_scope_match_surfaced_marked` | `search.rs` | e2e | `repl/spec.md §17.19` | Per the `/repl` ruling: `/search` for a query with an exact in-scope match + partial out-of-scope matches surfaces the exact match, **marked** (e.g. "already in scope — no import needed") rather than omitted. Assert the exact-name row appears with the marking. | Pos | guard, RED |
| `search_exact_ranked_above_partial` | `search.rs` | e2e | `repl/spec.md §17.19.1` | A query with an exact out-of-scope match + partial substring matches ranks exact-name **before** partial (and exact-scheme before structural-contains). Assert output ORDER: exact row first. | Pos (ordering) | guard, RED |
| `search_exact_in_scope_not_offered_import_form_neg` | `search.rs` | e2e | `repl/spec.md §17.19` | The marked exact in-scope row does NOT offer an `(import …)` form (it's already available) — preserves the §17.19 not-yet-imported intent while not hiding the strongest match. | Neg | guard, RED |

**Existing-test reconcile:** `search_neg_already_imported_not_relisted` asserts the CURRENT
"in-scope match excluded" behaviour. Under the 0543 ruling it either flips (now surfaced-marked)
or gets a flip-note; reconcile in the fix change-set, do not silently delete.

---

## §4 Workstream D — agent / CLI surface

### 0541 — multi-tool-call turn panics the binary (transcript pairing)

Root cause (pinned): `record_pull_result` checks only `transcript.last()`; after the first
`ToolResult` is pushed, subsequent calls in the same `≥2`-call batch fail the `.last()` check
and demote to `User`, leaving tool_use ids uncovered → `assert_transcript_wire_valid`
`debug_assert!` panic in `assemble_request`.

**Precondition (BLOCKING, flag to `/sprint`):** the `--features agent` test lane does NOT
COMPILE on `main` — `src/agent/{harvest.rs:393,pull.rs:1470}` are missing the `mode_summary`
field on `UserFnState::Concrete` (S102 carrier drift). `/dev (src/)` must fix this as **step 0**
so `/qa` gets a **failing** (not erroring-to-compile) repro. Recorded here; no separate FIXME.

| Test | File | Tier | `// spec:` | Observable | Pos/Neg | Cat |
|---|---|---|---|---|---|---|
| `agent_multi_tool_call_batch_all_results_covered` | `agent.rs` (`#[cfg(feature = "agent")]`) | e2e | `design/int/agent.md` (transcript wire-validity invariant; confirm exact §anchor at authoring — else free-form `// spec: (invariant on types.rs::assert_transcript_wire_valid) — …`) | Extend a stub fixture to emit a **≥3-tool-call batch** in one `ModelResponse::ToolCalls` (if the stub DSL can express >1 call/turn); drive a turn; assert the session **does not panic** (exit not a debug-assert abort) and all N tool_use ids close as `ToolResult` (the next assembled request is wire-valid). | Pos (all covered) + Neg (no panic / no uncovered-id abort) | RED-first (panics today) |

**Stub-DSL contingency:** if the deterministic stub cannot express a multi-call batch, `/qa`
records that limitation and the durable regression guard is the **`/dev` unit test on
`AgentState`** (the FIXME's "natural grain"): record one `AssistantToolCalls` batch of ≥3, then
`record_pull_result` once per call in order, assert all N close as `ToolResult` and
`assert_transcript_wire_valid` passes. That unit test is **`/dev (src/)`-authored** and is the
minimum durable record; the e2e above is added when the stub can batch. Either way the defect
gets a failing test.

### 0539 — `--agent`/`--yes` hard-error on a non-agent build (flip existing no-ops)

User ruling: `--agent` and `--yes`/`-y` on a binary built **without** the agent feature MUST
ERROR (usage hint to stderr, exit 1), not be accepted as a no-op. `--no-agent` is **unaffected**
(stays accepted no-op). This flips existing `tests/agent.rs` accepted-no-op guards — `/qa` owns
`tests/`, so `/qa` edits these e2e tests.

| Existing test | Disposition |
|---|---|
| `agent_flag_accepted_not_unknown` (~138, not cfg-gated) | **Split by feature.** On `#[cfg(not(feature="agent"))]`: assert `--agent` ERRORS (stderr usage hint + exit 1). On `#[cfg(feature="agent")]`: keep accepted-valid. |
| `yes_flag_accepted_no_op_default_build` (~161) | **Flip** to `yes_flag_errors_on_default_build` — assert exit 1 + stderr usage hint on the non-agent build. |
| `y_short_flag_accepted_no_op_default_build` (~189) | **Flip** to error-path (`-y` same as `--yes`). |
| `agent_log_absent_on_default_build_neg` (~2643) | Uses `--agent` as a no-op **precondition**. Rework: remove `--agent` from the invocation (it now errors) — the log-absence assertion stands on a plain default-build session. |
| `agent_trace_absent_on_default_build_neg` (~3145) | Same rework — drop the `--agent` precondition; keep the trace-absence assertion. |
| `no_agent_flag_accepted_not_unknown` (~218) | **UNCHANGED** — `--no-agent` stays accepted no-op. Add an explicit assertion it does NOT error, as the negative anchor of this ruling. |
| `agent_yes_with_no_agent_is_accepted_no_op` (~1535) | Inspect feature gating: if it exercises `--yes` on a non-agent build it flips to error; if it is the agent-capable-but-dormant-provider case, it is UNAFFECTED (the ruling is scoped to feature-not-compiled-in). `/qa` determines at authoring. |

| New test | File | Tier | `// spec:` | Observable | Pos/Neg | Cat |
|---|---|---|---|---|---|---|
| `agent_flag_errors_on_non_agent_build` | `agent.rs` (`cfg(not(agent))`) | e2e | `repl/spec.md §0.6.1` | `--agent` on default build → exit 1, stderr contains usage hint (substring, matching `--no-cache`+`--link` style), session does NOT start. | Pos (errors) | guard, RED |
| `yes_flag_errors_on_non_agent_build` | `agent.rs` (`cfg(not(agent))`) | e2e | `repl/spec.md §0.6.2` | `--yes` and `-y` on default build → exit 1 + stderr usage hint. | Pos | guard, RED |
| `no_agent_flag_still_accepted_no_op_neg` | `agent.rs` | e2e | `repl/spec.md §0.6.1` | `--no-agent` on default build → NOT `unknown flag`, NOT an error, session evals normally. The negative guard that the ruling is scoped and did not over-reach. | Neg | guard, GREEN |

**Sequencing:** the flips depend on `/repl` scribing §0.6.1/§0.6.2 first (spec wording), then
`/int` flipping the `main.rs` parse arms. `/qa` authors the flipped tests RED against the new
spec wording.

---

## §5 Workstream H — language / spec features

### 0365 — `Type.member` accessor qualification resolves a poisoned bare field

S83 ruling exists; needs impl (frontend resolution + typecheck). `Type.member` currently
resolves constructors + trait methods; extend to field accessors so `Box.v`/`Cup.v`
disambiguate a same-module poisoned bare `v`. Existing `tests/spec_field_accessor.rs` already
has `Box.v`/`Cup.v` cross-module + same-module cases — `/qa` audits which assert the **poisoned
same-module** disambiguation and fills the gap.

| Test | File | Tier | `// spec:` | Observable (exact) | Pos/Neg | Cat |
|---|---|---|---|---|---|---|
| `type_member_field_accessor_disambiguates_poisoned_same_module` | `spec_field_accessor.rs` | e2e | `spec/08-modules.md §8.5.2` | Same module: `(deftype Box [:Int v])` + `(deftype Cup [:Int v])` (bare `v` poisoned/ambiguous). `Box.v` on a `Box` value resolves to the `Box` accessor and `Cup.v` on a `Cup` value to the `Cup` accessor — assert both yield the correct field values through all modes. | Pos | guard, RED (unimplemented) |
| `type_member_field_accessor_typed_as_fn_neg_bare_still_ambiguous` | `spec_field_accessor.rs` | e2e | `spec/05-definitions.md §5.2.6` | Negative anchor: bare `v` STILL errors ambiguous (compile-time, lists alternatives) — the qualification escape does not silently un-poison the bare name; `Box.v` types as `(Fn [Box] Int)`. | Neg | guard, RED |

`/dev` unit obligations: `/dev (frontend)` — `Type.member` resolution learns the accessor case;
`/dev (typecheck)` — resolves to `(Fn [Type] FieldType)`. `/qa` audit records which existing
`spec_field_accessor.rs` cases already cover the cross-module axis (they do — `cross_module_*`)
vs the same-module-poisoned axis (the gap this fills).

### 0416 — bitwise primitives (verify/extend the existing RED file; GATED ON /spec)

Phase-2 ruling 5: these are **inline-lowered primitives** (`DefKind::Primitive` +
backend CLIF arms `band/bor/bxor/bnot/ishl/ushr|sshr/popcnt`), NOT extern intrinsics. Backend
lowering is **gated on `/spec`** deciding Int width, `bit-not` two's-complement width, and
**signed-vs-logical shift** (`shr` → `sshr` or `ushr`), added to `spec/appendix-a-builtins.md`
§A.3.

**`tests/spec_appendix_a_bitwise.rs` ALREADY EXISTS** (9 RED-first tests, S91 Thread C):
`bit_and_basic_and_edge` etc., `PrimitivesOnly` prelude, decimal-literal bit patterns. Its
header already assumes signed 64-bit two's-complement, `shr` arithmetic, shift-count mod 64.

| Action | File | Detail |
|---|---|---|
| **Verify** the existing 9 tests' asserted semantics **against the `/spec` §A.3 ruling once it lands.** | `spec_appendix_a_bitwise.rs` | If `/spec` rules `shr` **logical** (`ushr`) rather than arithmetic, the existing `shr`/`bit-not` goldens (sign-extension, all-64-bit complement) **must be corrected to match the ruling** before they can be the acceptance oracle — the S106 spec ruling governs, not the S91 header's assumption. RED-first: they fail today (primitives unregistered) and flip when the primitives + lowering land. |
| **Extend** with the `+neg` / signedness boundary the ruling pins. | `spec_appendix_a_bitwise.rs` | e.g. `shr_sign_behaviour_matches_spec_ruling` (arith vs logical on a negative operand), `bit_not_width_matches_spec` (complement width), `popcount_all_64_bits`. Each `// spec: spec/appendix-a-builtins.md §A.3`, exact integer results. |

**Blocking note to `/sprint`:** do NOT finalize these goldens until `/spec` §A.3 rules width +
shift signedness. Draft them RED against the header's current assumption; re-baseline in the
`/spec`+`/dev` change-set if the ruling differs. `/dev (primitives)` seeds the rows;
`/dev (backend)` adds the lowering arms.

---

## §6 Workstream G — aging test-hygiene (0496, 0498, 0499 L-S1)

### 0496 — src/ unit-tier residual (VERIFY drained + name residual) — NO `/qa` e2e owed

Per the FIXME's S103 update, the `lifecycle.rs` headline is drained (`degraded_startup_tests`
module + `redefine.rs` seams). `/qa`'s S106 role is **verification + naming the residual**, not
authoring (these are `/dev (src/)` unit tests):

**Named residual (kept open for a future wave / opened when a fix next touches the seam):**
1. `src/process_form/cache_restore.rs` (0 tests — the D3 cache-restore axis).
2. `src/process_form/macro_resolution.rs` (0 tests).
3. `src/eval.rs` (2 tests — Matrix-E recording seam only).
4. `src/display.rs` `format_adt_value`/`format_adt_heap_value` ADT-value rendering module (rides
   the 0493 fix wave — not in S106 scope unless a display fix opens it).
5. `src/repl.rs` handler tests through the facade (`handle_sig`/`handle_mod`/`handle_source`).

**`/qa` disposition:** no e2e is owed for 0496 (it is the unit-tier half). `/qa` confirms the
drained modules against the crate's `#[cfg(test)]` inventory and records the residual list above
so the FIXME can be narrowed/closed by `/sprint`. If any S106 fix (0541/0546/0548/0549/0538)
touches one of these modules, its per-fix `/dev` unit test drains that cell as a side effect —
note the coincidence, do not double-author.

### 0498 — types marshal byte-sync drift-guard + zero-test module cover — NO `/qa` e2e owed

Unit-tier, `/dev (types)`-owned. `/qa` names the obligations (these are `crates/cranelisp-types`
`#[cfg(test)]` tests, NOT `/qa`'s to author):
1. **Drift-guard** asserting `cranelisp-types/src/marshal.rs` and
   `cranelisp-primitives/src/marshal.rs` tables/tags are identical (shared-constant or
   table-equality/checksum test — whichever the crate topology permits without a new production
   dep edge); + the `builtins.rs` ctor-order sync arm if mechanically assertable.
2. Minimal complexity/negative cover for `check.rs`, `newtype.rs`; negative arms for `got.rs`,
   `scheduling.rs`.

Natural carrier: any S106 types-touching change-set (there is none forced by S106 scope per the
Phase-2 "no `cranelisp-types` edit" finding — so this rides the next types touch or is a
standalone `/dev (types)` slot). `/qa` records the obligation; no e2e.

### 0499 L-S1 — session-history preamble grid (generalize beyond the 6a-burned cells)

**Status reconcile:** S103 authored a **partial** L-S1 grid (`assert_preamble_invariant` helper
in `repl_introspection.rs` ~3440 + `repl_redefinition.rs` ~1202; 7 GREEN robustness tests). The
S106 task is to **generalize the helper beyond the 6a-burned cells** so all 7 lanes genuinely
exist, then `/qa` deletes 0499 at close (L-M1 retires to WS-J per SPRINT.md — not `/qa`'s to
grow).

The L-S1 lane (coverage-audit §2.4): for each introspection/report surface, re-run the core
assertion under the preamble grid `{∅, bare lookup of the symbol, expression turn calling it,
prior failed turn, /reset}`, via a helper that prepends preambles to stdin. The audit says
"start with the surfaces 6a burned: `/info`/`/source` (0486), cascade report (0491),
shadow-resolution order (0484)" — the **generalization** is to the surfaces 6a did NOT burn.

| Test group | File | Tier | `// spec:` | Observable | Pos/Neg | Cat |
|---|---|---|---|---|---|---|
| Preamble-grid generalization: `/info`/`/source` (0486 surface) | `repl_introspection.rs` | e2e | `repl/spec.md §18.4` | `/info` and `/source` for a symbol produce the SAME correct output under every preamble (esp. `bare lookup` preamble — the 0486 corruption trigger). Extend the existing helper's `body`/`needle` invariants to `/source` exact output, not just `/info`. | Pos (invariant holds) | robustness, GREEN |
| Preamble-grid generalization: bare-lookup type display + `/list`/`/imports` layout | `repl_introspection.rs` | e2e | `repl/spec.md §3.3` | Layout enumerators + bare type-display produce identical output under the preamble grid — generalizes L-S1 to the enumeration surfaces (couples with 0545/0546 goldens). | Pos | robustness, GREEN |
| Preamble-grid generalization: redefinition report (0491 cascade + §18.1.1) | `repl_redefinition.rs` | e2e | `repl/spec.md §18.1.1` | Extend the redefinition-surface grid to the cascade/downgrade report shape under `{prior failed turn, /reset}` preambles. | Pos + Neg (no `__expr` noise in report) | robustness, GREEN |

**Deletion condition (record for `/sprint`):** L-S1 helper generalized (above) AND L-M1
migrated to WS-J's `design/arch/backlog/performance.md` §5 by `/arch` → all 7 lanes exist or are
explicitly re-homed → `/qa` deletes `0499` at S106 close with a commit naming the resolution.
`/qa` confirms the per-lane audit (L-U1/L-S2/L-S3/L-N1/L-N2 already EXIST per the 0499 status
table) before deleting.

---

## §7 Workstream E — line editor (0544)

Covered in **Cluster A2** (§1) — co-scheduled with 0551 on the `src/main.rs` read loop.

---

## §8 Guard-flip & ledger bookkeeping

- **New RED-first defect repros (5 FIXMEs):** 0541, 0542, 0546, 0548, 0551. Each RED at draft,
  flips in the owning `/dev` change-set.
- **New behaviour-change guards RED at draft (9 FIXMEs):** 0539 (flips), 0540, 0543, 0545
  (RED-or-rebaseline), 0549, 0550, 0538, 0365, 0416 (gated on /spec).
- **GREEN robustness / byte-identical (2):** 0544 (non-TTY byte-identical) + 0499 L-S1
  generalization.
- **No `/qa` test (2):** 0496, 0498 — `/dev` unit-tier; `/qa` names obligations + residual.
- **ONE drafting-batch ledger entry** per the S101 §6.1 precedent ("S106 Phase-5 Stage-1 FIXME-
  burn-down RED set", six fields); any RED carried at close gets a full entry and joins the
  root-`CLAUDE.md` intentional-failing count.
- **The 22 existing intentional guards are NOT edited.** The only existing tests this plan
  MODIFIES are the 0539 `tests/agent.rs` no-op flips (§4) and the 0545/0543 existing-golden /
  existing-test reconciles (§2/§3) — each modification is a documented behaviour-change, not a
  weakening, and lands in the fix change-set.
- **Flip protocol:** fix + `/dev` unit test land together; `/qa` observes the e2e flip,
  annotates the ledger row in place with sprint + SHA, updates the test-file "RED on HEAD" note.
  Tests never deleted or weakened.

---

## §9 Harness readiness + named gaps

**Exists and ready:** the `Cranelisp` e2e builder (`repl()`/`run()`/`link()`/`link_then_run()`,
`.file()`/`.user()`/`.stdin()`/`.cli_flag()`/`.env()`, `read_tmp`/`tmp_exists`/`tmpdir_path`,
`assert_golden`/`assert_golden_masked`/`assert_stdout_eq`, `assert_no_internal_artifacts`);
`PreludeVariant::{None,PrimitivesOnly,TestStandard}`; the `--link` prereq nextest setup script;
the L-S1 `assert_preamble_invariant` helper (S103, to be generalized).

**Gaps (named, with owners) — do not block Phase-5 drafting; each dependent test drafts RED-
until-its-mechanism/ruling lands:**

| # | Gap | Needed by | Owner / when |
|---|---|---|---|
| G-1 | **PTY-driven e2e** — the harness has no pseudo-terminal, so 0551's interactive-TTY exit and 0544's arrow-key/history are NOT e2e-reachable. Reachable guards (piped-mode 0551, non-TTY-byte-identical 0544) + named `/dev` unit tests cover the seams; the TTY-interactive surface is a documented manual-verification item. If PTY e2e is later wanted, file `/int`/`/arch` for a harness `pty_capture` primitive. | 0551 interactive exit, 0544 history recall | harness gap — NOT filed as FIXME this sprint (piped + unit coverage is sufficient; manual `/repl` demo verifies TTY) |
| G-2 | **`--features agent` lane does not compile** (`mode_summary` drift, `harvest.rs:393`/`pull.rs:1470`). Blocks a **failing** (vs erroring) 0541 repro. | 0541 e2e | `/dev (src/)` step-0 fix, flagged to `/sprint` |
| G-3 | **Stub-DSL multi-call batch** — whether the deterministic agent stub can emit >1 tool call per turn. If not, 0541's durable guard is the `/dev` `AgentState` unit test (the FIXME's natural grain); the e2e is added when the stub can batch. | 0541 e2e vs unit | `/dev (src/)` — confirm stub capability at authoring |
| G-4 | **`/repl` spec rulings pending** — 0539 (§0.6.1/§0.6.2 error wording), 0540/0543 (§17.19 docstring-axis + ranking + in-scope marking), 0545 (§3.3 L3 rule-vs-example reconcile), 0550 (§0.2.1 `--link` output name/location contract), 0544 (§10 history requirement). Each test drafts to the ruled contract; where the ruling is still open, draft to the FIXME's proposed resolution and re-baseline if `/repl` diverges. | 0539/0540/0543/0545/0550/0544 | `/repl` — Phase-5 spec scribe precedes/co-lands the `/dev` fix |
| G-5 | **`/spec` §A.3 semantics** — Int width, `bit-not` width, `shr` signedness — gate the 0416 goldens. | 0416 | `/spec` first, then `/dev (primitives)` → `/dev (backend)` |

**Exit-gate readiness — READY for Phase 5.** Every in-scope item has a concrete `/qa` e2e
deliverable (or a documented "no e2e owed, unit-tier" disposition + named `/dev` obligation).
The gaps above are landing/ruling dependencies on named owners, not planning holes — each
dependent test drafts RED-until-its-mechanism-or-ruling, which is the QA-first discipline.

---

## §10 Registration

- Registered in `tests/CLAUDE.md` §Plan documents (this pass).
- Peer of `tests/plan/s103-test-plan.md` (predecessor; L-S1 generalized here) and
  `tests/plan/coverage-audit-s101.md` (the 7-lane source).
- Ledger rows for all new tests land with the drafting commits (Phase 5), not this plan.

### Count summary

**RED-first defect repros: 5** (0541, 0542, 0546, 0548, 0551) → ~11 e2e tests.
**Behaviour-change guards: 9** (0539, 0540, 0543, 0545, 0549, 0550, 0538, 0365, 0416) →
~22 e2e tests (incl. the 0539 flips + 0416 verify/extend).
**GREEN robustness: 2** (0544 non-TTY byte-identical, 0499 L-S1 generalization) → ~6 e2e tests.
**No `/qa` e2e (unit-tier, obligations named): 2** (0496, 0498).
</content>
</invoke>
