# Sprint 107: REPL & agent output rendering ergonomics

**Status**: COMPLETE

**Goal**: Fix the REPL/agent output-rendering findings surfaced during S106 close-out testing — code pretty-print column alignment, agent-output copy-paste cleanliness, agent-response streaming — plus the one correctness defect found alongside them (deftype nameless-field silent acceptance).

## Scope

Four findings from S106 testing. Items 2–4 share one surface (REPL/agent output rendering, `/repl`-spec + `src/`-impl); item 1 is a small independent frontend correctness fix folded in because it was found in the same session and already carries a RED guard.

1. **deftype nameless constructor-field rejection** (correctness). The frontend
   silently accepts `(deftype Rotation (L :Int) (R :Int))` — it reads `:Int` as
   a type annotation on the constructor and DROPS the field, collapsing L/R to
   nullary constructors (a silent enum). Spec §5.2 already mandates a bracketed
   `[:Type name]` field list, so this is impl-conformance, **no spec change**.
   - Owner: `/dev(cranelisp-frontend)`. Guard: existing RED e2e
     `tests/spec_05_definitions.rs::deftype_ctor_nameless_type_field_rejected_neg`.

2. **FIXME 0554 — `/sexp` & `/source` column alignment.** The pretty-printer is
   pair-unaware for `let` bindings and `match` arms, smearing pairs across lines.
   Render one pair per line with aligned left (names/patterns) + right
   (values/bodies) columns.
   - Owner: `/repl` (normative layout in `repl/spec.md`) + `/dev(src)`
     (`src/pretty.rs`) + `/qa` (e2e pinning a fixed `let`/`match` fixture).

3. **FIXME 0556 — agent `▌` gutter breaks copy-paste.** The per-line gutter
   (`style::agent_prose`) lands in the clipboard, polluting multi-line copy of
   pretty-printed `lisp` fences. Make agent-emitted code copy-clean.
   - Owner: `/repl` (revise the §10.3 gutter spec) + `/dev(src)`
     (`src/style.rs` + `src/agent/render.rs`). Agent-feature-gated.

4. **FIXME 0555 — agent response not streamed.** `agent_turn` `block_on`s one
   full completion then renders all at once; stream incrementally instead.
   - Owner: `/repl` (spec streaming behaviour) + `/dev(src)`
     (`src/agent/provider.rs` + `render.rs`). Agent-feature-gated.
   - **Effort/design risk (flag for Phase 2):** needs a streaming-aware renderer
     (the current `split_fences`/markdown path needs complete text), rig's
     streaming completion API, and the tokio bridge — an `/arch` touch. Not
     pre-deferred (per `memory/feedback_no_defer_for_size_decompose_evidence_gated`);
     to be decomposed into waves and sequenced after the contained items 1–3.

**Cross-cutting constraint (affects Phase 4 waves):** items 1–4 all touch `src/`
(and 2–4 the REPL render layer specifically). Per the single-agent-per-source
rule (worktree isolation broken), `/dev(src)` implementation is **serial**, not
parallel. Only the `/repl` spec decisions and the `/dev(cranelisp-frontend)` fix
(item 1) can run alongside `src/` render work.

**Out of scope** (no language-semantics changes; no new features). The
type-directed value pretty-printer (FIXME 0050) is a *different* mechanism
(value display vs. source-code formatting) and stays deferred.

## FIXME debt

| FIXME | Target skill | Status | In scope? | Notes |
|---|---|---|---|---|
| — (deftype nameless field) | /dev(frontend) | RED test, no FIXME | **yes** | Tracked by `deftype_ctor_nameless_type_field_rejected_neg`; the test is the record (per `feedback_no_fixme_with_failing_test`). |
| 0554 | /repl | open | **yes** | `/sexp`/`/source` let/match column alignment. |
| 0555 | /repl | open | **yes** | Agent streaming — higher effort, Phase-2 arch input. |
| 0556 | /repl | open | **yes** | Agent gutter copy-paste. |
| 0050 | /int→/dev(src) | deferred | no | Type-directed List/Seq *value* pretty-printer; blocked on display protocol. Different mechanism from 0554. |
| 0052 | /repl | open | no (flag) | `/learn` REPL feature; open since S64 — **long carry, flag for user** (METHOD §2.4). Large feature, off-theme. |
| 0463 | /examples | deferred | no | Poll-shape network example; blocked on platform net-leaf infra. |
| 0553 | /typecheck | open | no | "Instantiate at types" entry point; explicitly future work, co-lands with the ModeSummary sprint. |

## Architecture review (Phase 2)

**Verdict: SIGN-OFF-WITH-REVISIONS** (2026-07-10, `/arch`). Coherent as one
increment. No blocker. Revisions are streaming decomposition + Principle-8
durability constraints; no items added or removed.

**Public-API / cross-crate: NONE — no `cranelisp-types` edit.**
- Item 1 (deftype) is frontend-internal AST-build rejection. Root cause pinned:
  `crates/cranelisp-frontend/src/ast_builder.rs::build_constructor_def`
  (~L604–612) — for `(L :Int)`, the trailing `:Int` is not a `Sexp::Bracket`, so
  the `else { vec![] }` arm silently drops the field and collapses `L` to nullary.
  Fix = reject a trailing non-bracket, non-docstring form there. `FieldDef`/
  `ConstructorDef` already exist in `cranelisp-types`; no boundary-type change.
- Items 2–4 live entirely in the `src/` binary crate (`pretty.rs`, `style.rs`,
  `src/agent/`). No `crates/` code consumes `pretty_print`/`agent_prose`/
  `render_agent_prose`; `AgentModel` is int-internal. The binary crate has no
  `cargo-public-api` gate (its conformance gate is the e2e suite), so even `pub`
  signature changes here need no baseline/facade update.

**Streaming (0555): FITS S107, no architecture change.** The current-thread
tokio runtime + `block_on` bridge is sufficient — stream via
`block_on(async { while let Some(chunk) = stream.next().await { sink(delta) } })`
over `self.model.stream(...)`; synchronous stdout writes inside the async block
are fine (single-threaded, `agent_turn` owns stdout for the turn). No thread
spawn, no multi-thread executor, no new tokio feature. The only new interface is
the **int-internal** `AgentModel::complete_streaming` membrane in
`src/agent/types.rs` (NOT a `cranelisp-types` type). Decomposed:

- **S1 — Neutral streaming membrane.** Add `complete_streaming(&mut self, req,
  sink: &mut dyn FnMut(&str)) -> Result<ModelResponse, String>` to `AgentModel`,
  emitting neutral text deltas + returning the final `ModelResponse`. **Default
  impl falls back to `complete`** (whole prose as one delta) so stub/Ollama/
  non-streaming paths keep working — bounds the blast radius. rig types stay
  below the membrane.
- **S2 — Provider streaming impl.** `RigModel::complete_streaming` consumes
  `self.model.stream(rig_req)` in one `block_on`, forwarding deltas + accumulating
  full text. Replace the `MockModel` `unimplemented!` stub (provider.rs:387) with
  a minimal real impl.
- **S3 — Streaming-aware renderer.** Stateful `StreamingRenderer` in `render.rs`:
  render prose deltas line-by-line through `markdown_to_terminal` live, **buffer
  only within an open ``` fence** and flush through `pretty_print_str` on the
  closing fence, applying the 0556 gutter policy. (Durable buffer-within-fence
  strategy — NOT the raw-then-reformat half-measure.)
- **S4 — `agent_turn` wiring.** Drive S3 via the S1 sink during `agent_complete`;
  keep the returned `ModelResponse` for `record_assistant` + loop continuation;
  trace/log fire on the accumulated text.
- **S5 — `/qa` `--features agent` coverage.** Stub emits multiple deltas → assert
  incremental emission; unit-test fence-buffering (partial fence held, flushed
  formatted on close).

**Streaming de-risk constraints (Phase-3/5 binding):**
1. **Stream only the terminal `Done` prose this sprint; tool-call turns stay
   non-streamed** (the dead-prompt pause is the terminal answer; rig streamed
   tool-call delta assembly is the fiddly part). Explicit non-goal seam, not
   foreclosed (Principle-8-clean).
2. **`/qa` differential invariant:** streamed-concatenated output MUST byte-equal
   `render_agent_prose` over the same complete text (colour-off) — protects the
   non-TTY goldens + §14.6 leaf-styling guards.
3. Default-fallback membrane (S1) ⇒ a non-streaming provider degrades to today's
   behaviour rather than breaking.

**Principle-8 durability constraints (binding on `/dev`):**
- **0554** — pair-awareness implemented **structurally on the `Sexp` tree**
  (recognise the let/match binding `Sexp::Bracket` as a pair sequence inside
  `pp`), NOT by string post-processing.
- **0556** — **render-side structural fix** (gutter prose lines; frame code
  fences without a per-line `▌`). The "keep gutter + expose un-guttered copy
  elsewhere" alternative is a hack — rejected. §14 normative note (`/repl`):
  prose streams live; a ```lisp fence renders formatted at fence-close (it cannot
  stream token-by-token — `pretty_print` needs the whole form).
- **0555** — go straight to the S3 fence-buffering renderer; the raw-then-reformat
  option is a Principle-8 interim and is rejected.

**Sequencing (load-bearing, not cosmetic): 0556 must land before 0555** — it
defines the code/prose framing split the streaming renderer consumes.

## Skill plans (Phase 3)

**Dispatch order (dependency-driven):** `/repl` authors the normative
rendering/streaming spec FIRST (input to the rest); then `/design(src)` + `/qa`
build against it. `/spec` not invoked (no language-semantics change — deftype is
§5.2 conformance; rendering is display). `/arch` interface set already confirmed
complete in Phase 2 (NONE cross-crate; int-internal `AgentModel::complete_streaming`).

### /design(cranelisp-frontend) — SKIPPED (design complete in Phase 2)

- The deftype nameless-field fix was fully designed by `/arch`: root cause at
  `crates/cranelisp-frontend/src/ast_builder.rs::build_constructor_def` (~L604–612,
  the `else { vec![] }` field-drop), fix = reject a trailing non-bracket,
  non-docstring form. No design-doc refinement needed; goes straight to `/qa`
  (RED test exists) + Phase-5 `/dev(cranelisp-frontend)`.

### /repl — normative rendering/streaming spec — DELIVERED

- **0554 → new `repl/spec.md` §3.11.** Structural pair-awareness on the `Sexp`
  tree for `let` (first `[...]`) + `match` (post-scrutinee `[...]`). Rules P0–P5:
  ≥2 pairs ⇒ aligned layout (forces multi-line); one pair/line; left col at `[`+1;
  right col at `leftStart + W + 1` (`W` = max flat left-term width per vector);
  multi-line right terms indent under the right col; odd-count graceful fallback.
  Byte-reproducible (colour-off). Worked `rotate` output is byte-exact in §3.11
  (the `/qa` fixture).
- **0556 → revised §17.2 (new item 3), §17.13.2, §10.3.** Agent PROSE keeps the
  `▌` gutter; agent-emitted CODE fences render with NO per-line gutter,
  byte-identical (colour-off) to `pretty_print_str`. Re-baselines the non-TTY
  agent golden (§17.13.3) + the §14.6 leaf-styling guard (noted for `/qa`).
- **0555 → new §17.22.** Terminal prose streams live line-by-line; ```lisp fences
  buffer + emit formatted un-guttered at fence-close; tool-call turns NOT streamed
  (explicit seam). **Differential invariant (MUST):** streamed-concatenated ==
  `render_agent_prose` over the same text (colour-off); non-streaming degrades as
  the one-delta case.
- **Acceptance met**: three testable MUSTs, all `[S107]`-annotated, no
  language-semantics change. Input ready for `/design(src)` + `/qa`.

### /design(src) — render/streaming implementation design — DELIVERED

- **Docs**: `design/int/terminal-styling.md` (new "Aligned `let`/`match` pair
  layout"), `design/int/agent.md` new **§14A** (0554 reuse / 0556 split / 0555 S1–S5).
- **0554 seam**: new `try_pp_pair_form` dispatch at the top of `pp_list` (before
  `FLAT_THRESHOLD`); helpers `pair_vector_layout(pairs, left_col)` (~40 lines:
  `W` from unstyled `format_flat().len()`, `right_col = left_col+W+1`, recurse
  `pp(right, right_col, false)` for P4) + `as_pairs()` even-count splitter (odd →
  `None` → P5 fallback). `let` `[`-col `indent+5`; `match` keeps arm vector on the
  head line. Benefits `/sexp`, `/source`, agent fences at once.
- **0556 seam** (before 0555): restructure `render_agent_prose` to gutter
  per-run at the leaf — `push_prose_run` (guttered) + `push_lisp_block`
  (un-guttered, byte-identical to `/sexp`). `style::agent_prose` unchanged.
- **0555 seams (S1→S5)**: S1 `AgentModel::complete_streaming(&mut self, req,
  sink: &mut dyn FnMut(&str)) -> Result<ModelResponse,String>` default-delegates
  to `complete`; S2 `RigModel::complete_streaming` over `self.model.stream` in one
  `block_on` (+ real `MockModel::stream`; **one Cargo edit — `futures` as
  agent-gated optional dep in the binary crate, int-internal**); S3
  `StreamingRenderer { line_buf, fence }` reusing the 0556 leaves; S4
  `agent_complete_streaming` shim — the `Done` arm stops calling
  `render_agent_prose` (the one behavioural edit, else double-render); S5 the
  differential-invariant hook. Recommended: re-express `render_agent_prose` as a
  one-delta drive of the renderer (invariant by construction, Principle 7/18).
- **Acceptance met**: no `cranelisp-types` change; all Phase-2 durability
  constraints honoured (structural-on-tree / render-side split / fence-buffering /
  0556→0555 sequencing).

### /qa — sprint-wide failing-test plan — DELIVERED

- **Plan**: `tests/plan/s107-test-plan.md`. Two-tier — `/qa` owns e2e; the
  load-bearing unit tier is named as `/dev` obligations.
- **Item 1** (`spec_05_definitions.rs`): existing RED `deftype_ctor_nameless_type_field_rejected_neg`
  + ADD positive `deftype_sum_bracketed_field_still_constructs` + tighter negative
  `deftype_ctor_nameless_field_not_nullary_neg`; `/dev(frontend)` unit on
  `build_constructor_def` returning `Err`.
- **Item 2** (`display_exact.rs`, byte-exact): `sexp_rotate_aligned_let_match_byte_exact`,
  `source_rotate_aligned_matches_sexp_byte_exact` (parity), P0/P5 edges
  (two-arm-forces-multiline, single-pair-flat-fallback, odd-count-no-crash,
  empty-let-no-crash); `/dev(src)` unit on `pp` P0–P5.
- **Item 3** (`agent.rs`, `--features agent`): `agent_lisp_fence_code_lines_ungutter_neg`,
  `agent_lisp_fence_bytes_equal_sexp_output`, `agent_prose_lines_keep_gutter`.
- **Item 4** (`agent.rs`, `--features agent`): `agent_terminal_answer_streams_incrementally`,
  `agent_streaming_bytes_equal_single_shot` (differential-invariant e2e proxy),
  `agent_streaming_fence_emitted_whole_at_close_neg`, `agent_tool_call_turn_not_streamed`,
  `agent_non_streaming_provider_degrades`; `/dev(src)` unit (load-bearing): pure
  differential invariant vs `render_agent_prose`, `StreamingRenderer` fence-buffering,
  S1 default-fallback.
- **0556 re-baseline set** (else Phase 5 misses them): tighten `tests/agent.rs`
  `agent_output_no_literal_ansi_escape_when_color_off_neg`,
  `agent_output_lisp_fence_pretty_printed_styled`, and the §17.13.3 golden
  `agent_session_render_golden_transcript` to the un-guttered code shape;
  `/dev(src)` re-baselines the §14.6 leaf-styling units in the same change-set.
- **Harness gaps** (Phase-5 prerequisites): **G-1 (blocks item 4 e2e)** — the stub
  can't script multiple deltas; `/dev(src)` must add the `complete_streaming`
  membrane + a stub delta channel (incl. a boundary inside a ```lisp fence). G-2 —
  incrementality isn't observable post-exit; e2e pins rendered result + byte-parity,
  timing is a unit concern. G-3 — assert the pretty block as a byte-exact SUBSTRING
  (non-TTY `user> ` prompt interleaves). G-4 (pre-existing) — no `--color=force`;
  colour-ON invariant lives in `/dev` units via the `ColorGuard` seam.
- **Acceptance met**: enough to draft failing tests in Phase 5 Stage 1.

## Waves (Phase 4)

**Execution is SERIAL** — worktree isolation is broken on this project
(`src/CLAUDE.md`), so only ONE source-editing agent runs at a time. The
methodology's "parallel across crates" does not apply; the D/D/R design step is
already complete (Phase 3), so Stage 2 is `/dev → /review` per item. Design docs
are current, so no per-item `/design` re-invocation.

### Phase 5 Stage 1 — QA-first (one `/qa` pass)

Write the failing tests that do NOT depend on the streaming harness gap (G-1):
- Item 1: `deftype_sum_bracketed_field_still_constructs`, `deftype_ctor_nameless_field_not_nullary_neg` (RED `…_rejected_neg` already exists).
- Item 2: `sexp_rotate_aligned_let_match_byte_exact` + `source_…parity` + P0/P5 edges.
- Item 3: gutter-shape tests + **re-baseline** the 3 existing goldens to the un-guttered code shape (they go RED until item-3 dev lands).
- Item 4 (partial): `agent_non_streaming_provider_degrades`. The **multi-delta streaming e2e is deferred to mid-Stage-2** (blocked on G-1 — the stub delta channel is built in item-4 S1/S2).
All failing-not-ignored.

### Phase 5 Stage 2 — serial `/dev → /review` per item

| Order | Skill | Crate | Task | Flips green |
|---|---|---|---|---|
| 1 | /dev → /review | cranelisp-frontend | Item 1 — reject nameless ctor field at `build_constructor_def` + unit | item-1 e2e (3) |
| 2 | /dev → /review | src/ | Item 2 — `pp` pair-awareness (0554) + `pp` P0–P5 units | item-2 layout e2e |
| 3 | /dev → /review | src/ | Item 3 — render-side gutter split (0556) + re-baseline §14.6 units | item-3 gutter e2e + re-baselined goldens |
| 4a | /dev | src/ | Item 4 S1+S2 — `complete_streaming` membrane (default fallback) + stub delta channel (**unblocks G-1**) + `futures` dep | — |
| 4b | /qa | tests/ | Item 4 — write the multi-delta streaming e2e (now possible) | (RED) |
| 4c | /dev → /review | src/ | Item 4 S3+S4+S5 — `StreamingRenderer` + `agent_turn` wiring + differential-invariant hook + units | item-4 streaming e2e + differential invariant |

**Load-bearing order:** items 1 & 2 independent; **item 3 (0556) before item 4
(0555)** — the gutter split feeds the streaming renderer. Item 4 has an internal
QA re-entry (4b) after the stub delta channel exists.

**Wave-gate note:** in-scope FIXMEs 0554/0555/0556 (`target: /repl`) are being
actioned this sprint, not blocking it; they are deleted when the behaviour lands
(Phase 5 / close). No other open FIXME targets a Phase-5 skill in a blocking way.

## Notes

- 2026-07-10: Scope drafted from S106 close-out testing findings (`/sexp` layout, agent streaming, agent copy-paste, deftype nameless-field). User approved scope (streaming kept in) and advanced to Phase 2 (arch review). `/arch` dispatched.
- 2026-07-10: `/arch` returned SIGN-OFF-WITH-REVISIONS. No `cranelisp-types`/cross-crate change (all `src/` binary + `cranelisp-frontend`-internal). Streaming FITS with no arch change (S1–S5 decomposition + de-risk constraints). Principle-8 durability constraints recorded (Sexp-tree pair-awareness; render-side gutter fix; fence-buffering renderer). Sequencing: 0556 before 0555. Reflected into Phase-2 + Waves sections. Ready for Phase 3 pending user go.
- 2026-07-10: Phase 5 STARTED (user go). Stage 1 dispatched — `/qa` writes the failing-not-ignored tests (items 1/2/3 + item-4 partial; multi-delta streaming e2e deferred per G-1). Serial: `/qa` owns the tree this stage.
- 2026-07-10: **Stage 1 DONE.** RED set landed (spec-link clean; ledger updated, SHA 52389dfa). Item1: `deftype_ctor_nameless_field_not_nullary_neg` RED + `deftype_sum_bracketed_field_still_constructs` GREEN. Item2: `sexp_rotate_aligned_let_match_byte_exact` + `source_…parity` + `sexp_two_arm_match_forces_multiline_neg` RED; 3 P0/P5 guards GREEN. Item3: `agent_lisp_fence_code_lines_ungutter_neg` + `agent_lisp_fence_bytes_equal_sexp_output` RED + 3 re-baselined goldens RED; `agent_prose_lines_keep_gutter` GREEN. Item4: ALL deferred (no `complete_streaming`/delta channel on HEAD — G-1). No surprises.
- 2026-07-10: Stage 2 item 1 dispatched — `/dev(cranelisp-frontend)`.
- 2026-07-10: **Item 1 /dev DONE.** `build_constructor_def` (`ast_builder.rs` ~L604) now returns `Err(span)` on a trailing non-bracket, non-docstring ctor form (was silent `else { vec![] }`). Narrow: accepted grammar (bracketed/nullary/docstring variants) untouched. +2 frontend unit tests. `deftype_ctor_nameless_type_field_rejected_neg` + `deftype_ctor_nameless_field_not_nullary_neg` GREEN; positive companion + all deftype tests stay GREEN. 339/339 crate + 51/51 e2e; check/clippy clean. `/review(frontend)` dispatched.
- 2026-07-10: **Item 1 /review CLEAN** — correct/narrow/root-cause; no mirror of the silent-drop pattern (only sibling field path routes through the fixed fn). Item 1 COMPLETE. Finding for Phase 7 (Minor, pre-existing, out of mandate): `(L [:Int n] junk)` still silently drops trailing junk AFTER a valid field bracket — a separate silent-acceptance, not fixed here.
- 2026-07-10: Stage 2 item 2 dispatched — `/dev(src)` (0554 `pp` pair-awareness).
- 2026-07-10: **Item 2 /dev DONE.** `src/pretty.rs`: `try_pp_pair_form` dispatch atop `pp_list` (before FLAT_THRESHOLD) + `try_pp_let`/`try_pp_match`/`as_pairs`/`pair_vector_layout` (`W`=max unstyled left width, `right_col=left_col+W+1`, recurse `pp(right,right_col)` for P4; odd→P5 fallback). `/sexp rotate` BYTE-IDENTICAL to §3.11. 3 targets RED→GREEN, 3 guards held; display_exact 27/27, repl_introspection 165/165 (no regression); +7 pp unit tests; clippy clean. Dev note to review: a ≥2-pair let/match embedded in a FLAT-rendered parent aligns rel to indent=0 (cosmetic). `/review(src)` dispatched.
- 2026-07-10: **Item 2 /review — BLOCKER + IMPORTANT (not clean).** BLOCKER: the flat-parent embedding is a P2/P3 misalignment for a COMMON shape — a ≥2-pair `let`/`match` inside a parent whose flat width ≤ FLAT_THRESHOLD(40) renders the parent flat (`pp_list_flat` is pair-unaware, `crates/cranelisp-types/src/sexp.rs:42`), so the nested pair-form aligns to indent=0. Empirically `(defn g [x] (let [a 1 bb 2] a))` misaligns `bb`/body by ~10 cols. `rotate` escapes only because it's big enough to force the `defn` multiline. Core algorithm + byte-exact `rotate` are correct; P0-trigger scope tight, structural-on-tree confirmed. IMPORTANT: `sexp_two_arm_match_forces_multiline_neg` is a FALSE-GREEN (asserts arms-not-shared-line, not column alignment) — masks the Blocker. Root of the Blocker = P0's force-multiline does not propagate to ancestors. **HELD for user decision on P0 propagation vs relaxation (A/B) before dispatching the fix.**
- 2026-07-10: **USER DECISION — honor §3.11 P0 as written** (force-multiline always; propagate to enclosing forms). Small forms wrapping a ≥2-pair let/match now render multiline+aligned. No spec change (propagation is the correct reading of the existing P0). Dispatching item-2 Blocker fix: `/dev(src)` ancestor-gate; then `/qa` strengthens the false-green guard + adds the flat-parent aligned test + re-baselines any goldens that legitimately became multiline; then `/review(src)` re-review.
- 2026-07-10: **Item 2 Blocker fix DONE.** `src/pretty.rs`: flat-path in `pp_list` + `pp_bracket` gated on `!subtree_contains_pair_form` (+ `is_forced_pair_form` single-sourcing the P0 decision). Both repros render aligned; perf bounded (scan only inside ≤40-char flat branch, short-circuits). +6 pp unit tests (byte-exact + column-equality). **ZERO pretty-print golden churn** (display_exact+repl_introspection 192/192). Full-suite REDs = 2, both unrelated: pre-existing FIXME-0528 guard; and `agent::primer_deftrait_uses_direct_children_not_outer_bracket` — RED from THIS session's pre-sprint primer edit (renamed the deftrait example Show→Describe to avoid the prelude-`show` collision per the primer's own guidance); test over-specified on the literal `Show`/`show`. Routing both remaining item-2 items to `/qa`: (A) strengthen `sexp_two_arm_match_forces_multiline_neg` to assert column alignment + add flat-parent aligned e2e (close the review IMPORTANT); (B) update the primer_deftrait assertion to the current `Describe`/`describe` example. `/qa` dispatched.
- 2026-07-10: **Item 2 /qa finalization DONE + Item 2 COMPLETE.** `sexp_two_arm_match_forces_multiline_neg` now byte-exact alignment; `sexp_flat_parent_two_pair_let_forces_multiline_aligned` added (display_exact 28/28). `primer_deftrait_uses_direct_children_not_outer_bracket` updated to `Describe`/`describe`, outer-bracket guard intact (GREEN, --features agent). The 5 remaining agent REDs are the INTENDED item-3 guards (0556). Mirror-check (`/sprint`): flat-path sites are `pp_list` + `pp_bracket` (both gated) + `pp_type_annotation_list` (L561) — the last renders content via `format_flat` on both paths (type annotation = one flat cyan span), so the gate is moot there; no actionable third mirror. Item 2 (0554 + Blocker + guards) COMPLETE.
- 2026-07-10: Stage 2 item 3 dispatched — `/dev(src)` (0556 render-side gutter split).
- 2026-07-10: **Item 3 /dev DONE.** `src/agent/render.rs`: `render_agent_prose` restructured to per-run leaves — `push_prose_run` (guttered `▌` + markdown, empty-run guarded) + `push_lisp_block` (un-guttered, byte-identical to `pretty_print_str`); whole-body `agent_prose` call removed; `style::agent_prose` untouched; default path untouched (feature-gated). 5 item-3 e2e targets GREEN; `agent_prose_lines_keep_gutter` GREEN; full `--test agent` 66/0; +4 render units (11 render / 110 agent lib). No §14.6 re-baseline needed (those didn't assert guttered-code). clippy clean. `/review(src)` dispatched (item 4 streaming reuses these leaves).
- 2026-07-10: **Item 3 /review CLEAN — item 3 COMPLETE.** Interleavings sound; copy-clean (§17.2) + style-once (§14.6) invariants hold; leaves are thin reuse wrappers (no mirror). 2 Minor: (1) empty-run guard trims only `\n` not general whitespace (fold `trim().is_empty()` into item-4 dev); (2) item-4 guidance — `split_fences` is whole-string, so the StreamingRenderer needs its OWN incremental fence-state (buffer to line boundaries for prose, buffer whole fences for code) — CONFIRMS the S3 design.
- 2026-07-10: Stage 2 item 4 dispatched — `/dev(src)` S1–S5 (streaming impl + stub delta channel + differential-invariant unit test). Then `/qa` e2e, then `/review`.
- 2026-07-10: **Item 4 /dev S1–S5 DONE.** S1 `AgentModel::complete_streaming` (default→`complete` fallback). S2 `RigModel::complete_streaming` over `model.stream` in one `block_on` + real `MockModel::stream` + `futures` agent-gated dep + `build_request` factored. S3 `StreamingRenderer` (own incremental fence-state, `classify_fence_line`; removed `split_fences`+`Run`; folded Minor #1 `trim().is_empty()`). S4 `Done` arm drives the renderer, removed `render_agent_prose` call (one behavioural edit). S5 `render_agent_prose` re-expressed as one-delta drive → **differential invariant holds BY CONSTRUCTION** (now `#[cfg(test)]` oracle). Stub DSL: `<|delta|>` marker (`stub.rs`), scripts multi-deltas incl. mid-fence — G-1 CLOSED. Differential unit test checks EVERY byte-split ≡ `render_agent_prose`: GREEN; 117/117 agent lib units; item-3 e2e 66/66 (no regression); clippy clean; no `cranelisp-types` change. `/qa` (e2e) dispatched.
- 2026-07-10: **Item 4 /qa e2e DONE.** 5 `--features agent` e2e in `tests/agent.rs` (§17.22): `agent_streaming_bytes_equal_single_shot` (differential proxy — single vs multi-delta incl. mid-fence boundary BYTE-IDENTICAL), `agent_streaming_fence_emitted_whole_at_close_neg`, `agent_terminal_answer_streams_incrementally`, `agent_tool_call_turn_not_streamed`, `agent_non_streaming_provider_degrades`. `--test agent` 71/0; spec-link 82 OK; ledger updated (item 4 landed). No differential mismatch. `/review(src)` dispatched (final review, S1–S5).
- 2026-07-10: **Item 4 /review CLEAN — item 4 COMPLETE.** Differential invariant STRUCTURALLY guaranteed (production Done-arm + the `#[cfg(test)]` `render_agent_prose` oracle drive the SAME `StreamingRenderer`/leaves; byte-equality invariant to delta boundaries). All adversarial state-machine checks pass (boundary at `\n`/fence-marker/mid-fence, unterminated fence, empty/whitespace deltas, CRLF); rig drain-to-`None`-before-`choice` correct; MockModel aggregates identically; S4 no double-render, repair loop stays non-streaming; no unwrap/panic in pipeline; `futures` agent-gated; no `cranelisp-types` change. 2 advisory (2-site flush below extraction threshold; real-provider tool-call incidental-Text narration is §14A.3-blessed but not deterministically tested → Phase-7 note).
- 2026-07-10: **Phase 6 DONE (`/repl`).** No spec-vs-delivery gap; `repl/demos/code-formatting.demo` added (green); all demos replay green (11 active + 26 archive); FIXMEs 0554/0555/0556 retired (were untracked).
- 2026-07-10: **Phase 7 CLOSE (user-approved).** Close conditioned on the trailing-junk `/qa` repro (landed, RED, FIXME /frontend). FIXME 0052 SCHEDULED to Phase H (user directive — stop per-sprint re-litigation). Committing to `main` (one S107 commit incl. session fixes; excluding `.clj-kondo/`,`.lsp/`,`agent_trace.txt`). Archived → `sprints/archive/sprint-107.md`; ROADMAP updated.
- 2026-07-10: **PHASE 5 EXIT GATE MET.** Full release-gate `cargo nextest run --no-fail-fast`: **4257 passed, 1 failed, 1 skipped** — the sole RED is the pre-existing known-defect guard `ownership_reuse::chaining_toggle_off_allocates_intermediate` (FIXME 0528, `/typecheck`+`/backend`; fails on baseline HEAD, not ours). Agent lane `--features agent`: `--test agent` **71/0**, agent lib **117/117**. All in-scope RED tests flipped GREEN; no `#[ignore]` added; all `/review` Blocker+Important resolved; no public-API/`cranelisp-types` change (arch-confirmed); design docs current (`repl/spec.md` §3.11/§17.2/§17.22, `design/int/agent.md §14A`, `terminal-styling.md`). All 4 items COMPLETE.
- 2026-07-10: User advanced to Phase 3. Dispatched `/repl` (normative spec) → then `/design(src)` + `/qa` (parallel). All three delivered: `/repl` (repl/spec.md §3.11/§17.2/§17.22), `/design(src)` (design/int/terminal-styling.md + agent.md §14A), `/qa` (tests/plan/s107-test-plan.md). `/design(cranelisp-frontend)` skipped (design complete in Phase 2). **Phase 3 exit gate MET**: interface set complete (arch, NONE cross-crate); `/qa` plan sufficient for Stage 1; design docs current. Phase 4 waves authored — serial pipeline (worktree isolation broken). Awaiting user go to begin Phase 5.

## Outcome (Phase 7)

### Delivered
- **Item 1 — deftype nameless-field rejection** (`cranelisp-frontend`). `build_constructor_def` now returns `Err(span)` on a trailing non-bracket, non-docstring constructor form (was a silent `else { vec![] }` field-drop → nullary enum). +2 frontend unit tests; `/review` clean (no mirror).
- **Item 2 — `/sexp` & `/source` `let`/`match` column alignment** (`src/pretty.rs`, FIXME 0554, `repl/spec.md §3.11`). Structural Sexp-tree pair-awareness (`try_pp_pair_form`/`pair_vector_layout`); byte-identical to §3.11. `/review` found a **Blocker** (flat-parent misalignment for the common small case) → fixed via the ancestor-gate (`subtree_contains_pair_form`) honoring §3.11 P0 propagation (**user decision**); false-green guard strengthened + flat-parent regression test added. +13 unit tests.
- **Item 3 — agent gutter code-vs-prose split** (`src/agent/render.rs`, FIXME 0556, `§17.2`). `render_agent_prose` gutters per-run at the leaf: code fences un-guttered (copy-paste clean, byte-identical to `/sexp`), prose keeps `▌`. `/review` clean. +4 unit tests.
- **Item 4 — agent response streaming** (`src/agent/{types,provider,render,mod,stub}.rs` + agent-gated `futures` dep, FIXME 0555, `§17.22`). `AgentModel::complete_streaming` membrane (default fallback), `RigModel` stream drive, stateful `StreamingRenderer` (fence-buffered), `agent_turn` wiring. **Differential invariant (streamed ≡ single-shot) holds by construction** (single render core; `/review`-confirmed structural). Terminal prose streams live; fences render at close; tool-call turns non-streamed. +6 unit tests + 5 e2e.
- **Regression demo**: `repl/demos/code-formatting.demo` (green); all prior demos replay green.

### Deferred (with rationale)
- Nothing from S107 scope deferred — all 4 items shipped.
- Out-of-scope carries: **0052** `/learn` REPL feature — **SCHEDULED (user directive) to Phase H (release-prep / tutorial track)**, `status: deferred` set to stop per-sprint re-litigation (past the §2.4 line, explicit sign-off); **0050** type-directed value pretty-printer (blocked on display protocol); **0463** poll-shape network example (blocked on platform net-leaf); **0553** "instantiate at types" entry point (future, co-lands with ModeSummary sprint).

### Findings (record in FIXMEs if not already)
- **Trailing-junk silent-drop (pre-existing, `cranelisp-frontend`)**: `(L [:Int n] junk)` still silently drops a form AFTER a valid field bracket — a separate silent-acceptance from the item-1 fix, out of its mandate. **Captured at close (user directive)**: `/qa` repro `tests/spec_05_definitions.rs::deftype_ctor_trailing_form_after_field_bracket_rejected_neg` — RED (HEAD silently accepts `(deftype Box (Box [:Int n] extra))`), `// FIXME(/frontend)`, ledger-recorded. Resolver: `/dev(cranelisp-frontend)`, future sprint.
- **Real-provider tool-call narration (agent)**: with a real `RigModel`, incidental `Text` deltas before a tool call now stream to screen (design-blessed, `design/int/agent.md §14A.3 S2`, "benign/in-contract"); the deterministic stub streams nothing on `ToolCalls`, so this display path is invisible to the automated suite. Awareness only.
- **Methodology — assertion strength**: item-2's `/review` caught that a "not on the same line" e2e guard was a **false-green** masking a column-misalignment Blocker. Weak-assertion guards mask defects; strengthened to byte-exact alignment.
- **Collateral — feature-gated primer tests**: a pre-sprint `primer.txt` edit (Show→Describe, to avoid the prelude-`show` recursion) broke a `--features agent` primer test over-specified on the `Show`/`show` literal; surfaced only by item-2's full-suite run. Primer-content edits need a `--features agent` run.
- **Arch principles served well**: the Phase-2 Principle-8 durability constraints (structural-on-tree, render-side split, fence-buffering — not string-hackery/dual-copy/raw-then-reformat) and Principle-7 single-source (differential invariant by construction) held through implementation and prevented the interim shortcuts. No principle friction.

### Exit metrics
- Release-gate `cargo nextest run --no-fail-fast`: 4257 passed / 1 failed (pre-existing FIXME-0528 guard only) / 1 skipped. Agent lane: `--test agent` 71/0; agent lib 117/117.
- FIXMEs retired: 0554, 0555, 0556 (behaviour shipped). No new gap FIXME (Phase-6 assessment found no spec-vs-delivery gap).
