# cranelisp-frontend — Deep Per-Crate Audit (Sprint 87, Stage B)

> **Predecessor.** This pass refreshes `audits/frontend-20260423.md` (+ its
> `-current-state.mmd` / `-target-state.mmd`). Per the never-delete-archived
> rule the 04-23 files stay in place; this S87 pass is a **delta + currency
> check** on that deep baseline, not a from-zero look.
>
> **Method.** 7-lens checklist (i)–(vii) per `sprints/SPRINT.md` Stage B, same
> instrument as the 04-23 finding taxonomy so "still-open / regressed /
> resolved" is a true diff. LOC priorities from `audits/loc-s87.md`:
> deepest production modules `ast_builder.rs` (1211 corrected), `reader.rs`
> (1109). READ-ONLY on code — findings only.
>
> **Suite state at audit:** Stage-A close left `cargo nextest run --workspace`
> green (2833/0/0). This is a *settled* surface — no intentional reds, no
> in-flight defect campaign in this crate.

---

## 0. Baseline reconciliation

The 04-23 audit had **6 main findings** + **5 named agent traps**. Reconciled
against the as-built crate (`reader.rs`, `ast_builder.rs`, `module_extract.rs`,
`quasiquote.rs`, `defmacro.rs`, `lib.rs`):

| # | 04-23 finding | S87 status | Evidence |
|---|---|---|---|
| 1 | `ast_builder.rs` too large / dominant complexity sink (~2915 LOC, ~142 fns) | **IMPROVED, partially open** | Corrected prod LOC now 1211 (raw 3041, 60% test). Still the crate's largest prod file, but no god function survives — largest is `build_method_sig` ~75 lines. The "parallel mini-parsers" risk is contained; the file was NOT split per rec #1. See F1. |
| 2 | Top-level dispatch duplicated between batch & REPL (`build_top_level` vs `build_repl_input`) | **RESOLVED** | The dual entry pair is gone. There is now ONE per-form dispatcher `build_form` (`ast_builder.rs:180`) + one sequence boundary `build_forms` (`:287`); the orchestrator owns begin/structural/expr peeling. Baseline rec #2 ("single top-level classifier") substantially delivered. |
| 3 | Syntax recognition vs lowering split/scattered; implicit cross-file pipeline contracts | **IMPROVED (documented), structurally same** | Contracts are now *documented* (caller-contract doc-comments on `build_form`:162-176 / `build_forms`:274-286; `module_extract.rs:18-21` `super` boundary; `ast_builder.rs:144` header). The coupling is unchanged but no longer *implicit*. See F4 (lens v). |
| 4 | Synthetic-Sexp construction repetitive / multiple local DSLs | **STILL OPEN** | `quasiquote.rs` has `make_sexp_{sym,int,float,bool,str,container}`, `make_slist`, `make_sconcat` (`:75-172`); `defmacro.rs` has `make_scons_match`, `make_match_sexp{,_exhaustive}`, `make_var_pattern` (`:537-606`). Two separate emit-synthetic-Sexp DSLs persist. Span allocation WAS centralized (see trap #2). See F2. |
| 5 | Documentation drift (peg vs hand-written; stale `ast_builder.rs` header) | **PARTIALLY RESOLVED** | `ast_builder.rs` header now accurate (`:1-20`). `design/frontend/reader.md:17,65` now correctly says hand-written. BUT `crates/cranelisp-frontend/plan-frontend.md` (§1, lines 5-32) AND `design/frontend/CLAUDE.md:16` still name PEG. `frontend.md` tracks this as HIGH-5 staleness register. See F3. |
| 6 | Test bulk obscures production structure | **STILL OPEN (by design)** | `ast_builder.rs` 60% inline test, `reader.rs` 35%. Baseline itself recommended keeping tests local; the readability cost remains but is accepted. Low severity. See F8. |

| Trap | 04-23 agent trap | S87 status |
|---|---|---|
| T1 | macro-expansion-before-AST invariant | **HELD + documented** — `build_form` doc-comment `:174-176` warns explicitly. |
| T2 | ad-hoc synthetic spans | **RESOLVED structurally** — single allocator `next_synthetic_span()` (`quasiquote.rs:27-40`), shared by defmacro via `crate::quasiquote::next_synthetic_span` (`defmacro.rs:22`). Trap can no longer be tripped accidentally. |
| T3 | literal `super` downstream of `module_extract` | **HELD + documented** — `module_extract.rs:18-21,227-242` (BC invariant #3). |
| T4 | add top-level form in only one entry path | **RESOLVED** — single `build_form` path eliminates the trap (see #2). |
| T5 | trust `plan-frontend.md` as truth | **STILL LIVE** — `plan-frontend.md` is still the stale doc (see F3). |

**Counts:** Resolved 3 (F#2, F#4-trap-class, baseline-traps T2/T4) · Partially
resolved / improved 3 (F#1, F#3, F#5) · Still open 2 (F#4 synth-DSL, F#6
test-bulk) · Traps held-or-resolved 5/5 (only T5 still live, = F3).
**No regressions.** **No new HIGH-severity structural debt introduced.**

---

## 1. S87 findings (severity-ranked)

### F1 — `ast_builder.rs` not split; still the single accretion point — Important
**`crates/cranelisp-frontend/src/ast_builder.rs`** (prod 1–1767).
Baseline rec #1 (split by subsystem: `ast/top_level.rs`, `ast/expr.rs`,
`ast/types.rs`, `ast/patterns.rs`, `ast/common.rs`) was **not actioned**. The
file improved on the metrics that matter most — no god function (largest
`build_method_sig` `:811-885` ~75 lines, `build_impl_target` `:941-1010` ~70,
`parse_deftype` `:497-559` ~63, `desugar_type_def` `:664-726` ~63), and the
public surface narrowed to `build_form`/`build_forms`/`build_expr`. But it still
mixes top-level dispatch, expr lowering, trait/impl lowering, type-expr parsing,
annotation/param parsing, and pattern builders in one 1211-LOC prod module, and
remains where new syntax lands first. **Not emergent-mandatory** (no over-budget
function, no third-duplicate trigger) → audit backlog, not in-sprint.
*Lens iii (function-budget) clean; lens i (mixed-concern accretion) is the live risk.*
**Proposed consolidation:** carry baseline rec #1 forward as a scoped
`/dev (cranelisp-frontend)` refactor — extract `ast/types.rs` (type-expr +
annotation parsing: `parse_type_expr`, `build_annotated_params`,
`annotation_run_carrier`, `desugar_type_def`) first, the most self-contained
seam. Defer the rest behind a measured second-need.

### F2 — Two parallel synthetic-Sexp DSLs (quasiquote vs defmacro) — Important
**`crates/cranelisp-frontend/src/quasiquote.rs:75-172`** and
**`crates/cranelisp-frontend/src/defmacro.rs:537-606`**.
Baseline #4 unresolved. `quasiquote.rs` emits `(macros/Sexp* …)` constructor
forms via `make_sexp_sym`/`make_sexp_int`/`make_sexp_float`/`make_sexp_bool`/
`make_sexp_str`/`make_sexp_container`/`make_slist`/`make_sconcat`; `defmacro.rs`
emits match/cons forms via `make_scons_match`/`make_match_sexp`/
`make_match_sexp_exhaustive`/`make_var_pattern`. Both hand-build raw
`Sexp::List`/`Sexp::Symbol` trees whose correctness depends on matching
`ast_builder.rs`'s reading EXACTLY — a hidden-contract surface (baseline #3).
The span half of this concern was already fixed (single `next_synthetic_span`).
*Lens i (duplication), lens vi (Principle 7 — single source of truth for "what a
canonical synthetic Sexp looks like").*
**Proposed consolidation:** extract a crate-internal `synth.rs` (or `sexp_kit`)
with the canonical primitive constructors (`sym`, `int`, `str`, `list`,
`bracket`, `cons`/`nil`) that both modules call; keep module-specific composite
builders (`make_scons_match`, `make_sexp_container`) layered on top. This is the
04-23 target diagram's `SexpKit` node. Two call-site families = past the
two-not-three threshold; appropriate as backlog, not forced in-sprint.

### F3 — `plan-frontend.md` + `design/frontend/CLAUDE.md` still name PEG — Important
**`crates/cranelisp-frontend/plan-frontend.md`** §1 (lines 5-32, "Decision: `peg`
0.8") and **`design/frontend/CLAUDE.md:16`** ("PEG grammar structure").
The reader is hand-written recursive descent (`reader.rs`, `Reader` cursor
struct). Baseline HIGH-5 is *partially* closed: `ast_builder.rs` header is now
accurate and `design/frontend/reader.md:17,65` correctly documents the
hand-written choice and the rejected-PEG rationale; `frontend.md` carries an
explicit HIGH-5 staleness register. But the two docs above still assert PEG —
the exact false-mental-model trap (baseline trap T5) that invites an agent to
"port the PEG grammar." `plan-frontend.md:303,410` even instruct porting
`reader.rs` as "PEG grammar."
*Lens ii is about dead CODE; this is the doc-currency arm of lens vi (interim/
stale-architecture residue).*
**Proposed consolidation:** FIXME `target: /design` (or `/frontend`) — refresh
`plan-frontend.md` §1 + the porting steps to "hand-written recursive descent,"
and fix `design/frontend/CLAUDE.md:16` "PEG grammar structure" →
"recursive-descent grammar structure." Cheap, high-leverage; carries baseline
rec #5.

### F4 — Test/prod mirror: `is_top_level_form` + `parsed_entry_to_top_level` duplicated in the test module — Suggestion(→Important if it drifts)
**`ast_builder.rs:328` `is_top_level_form_sexp` (prod)** vs
**`ast_builder.rs:1835` `is_top_level_form` (test)** — *verbatim* duplicate of
the head-set `defn|defn-|deftype|deftype-|deftrait|deftrait-|impl|defmacro|
defmacro-`. And **`ast_builder.rs:346` `parsed_entry_to_top_level` (prod,
returns `Option`, drops Macro/Constructor)** vs **`:1782` same-named test adapter
(returns `TopLevel`, `unreachable!`s on Macro/Constructor)**. The test re-creates
production logic instead of calling it, so a change to the prod head-set or the
entry→TopLevel disposition will silently NOT be reflected in the test's view —
the classic Principle-7 mirror the `feedback_review_root_cause_and_duplication`
memory flags. *Lens i (mirror), lens vi (Principle 7).*
**Proposed consolidation:** FIXME `target: /dev` — have the test adapter call the
production `is_top_level_form_sexp` / `parsed_entry_to_top_level` (handling the
`None` arm explicitly) rather than re-deriving. Low effort; removes the drift
surface. Note the head-set ALSO appears as the `build_form` dispatch
(`:227-245`) and `parse_def_visibility` (`:131-141`) — a third occurrence of the
form-name vocabulary, so this edges toward the three-site extraction threshold
(a `const TOP_LEVEL_HEADS` or shared classifier).

### F5 — Duplicated dotted-module-path parsing in the reader — Suggestion
**`reader.rs:593-618`** (in `read_symbol_or_keyword`) and
**`reader.rs:692-714`** (in `read_qualified_tail`). Two near-identical loops
consume dotted segments (`while peek == b'.'`, same backtrack via `dot_pos`,
same `is_symbol_start`/`consume_symbol_chars`, same `module.push('.')`
accumulation, same trailing-`/` detection). Two sites = below the
three-to-extract threshold, but they are *structurally identical* and parse the
same grammar fragment, so drift between them = a qualified-name parse bug.
*Lens i (duplication).*
**Proposed consolidation:** factor `consume_dotted_module_path(r) -> String`
called by both. Suggestion-severity (two sites); promote if a third dotted-path
reader appears.

### F6 — `unreachable!`/`expect` in production paths (justified, but audit them) — Suggestion
Three production-path partial functions, each with a documented invariant:
- `ast_builder.rs:243` `unreachable!("invariant: parse_def_visibility returns known base")` — guarded by the exhaustive `parse_def_visibility` match immediately above; sound.
- `ast_builder.rs:1651` `.expect("run of length 1 has one element")` in `annotation_run_carrier` — reached only on a known-non-empty run; sound but an `.expect` in prod.
- `reader.rs:357` `unreachable!("invariant: caller checked non-empty via peek()")` in `read_utf8_char` — caller (`read_string` `:346`) checks via `peek()`; sound.
None are spec-violation panics on user input, and all carry SAFETY-style
justification strings (not the audit-prohibited "trust me"). *Lens ii-adjacent
(panic-in-prod vigilance per `sketch/audits/codegen.md`).* No action required;
recorded so the next pass can confirm they stay invariant-guarded. If
`annotation_run_carrier` is touched, prefer returning a structured parse error
over `.expect`.

### F7 — `is_top_level_form_sexp` head-set ≠ `build_form` accepted-head-set (latent skew) — Suggestion
`build_forms` (`:310`) uses `is_top_level_form_sexp` (`:328`) to *route* a sexp
to `build_form`; `build_form` (`:210-250`) then independently re-decides which
heads it accepts (rejecting `begin`/`mod`/`import`/…, dispatching
`defmacro`/`impl`/`parse_def_visibility`). The routing predicate and the
dispatcher's accepted set are maintained separately. They agree today, but a new
top-level head added to `build_form` and not to `is_top_level_form_sexp` (or vice
versa) routes the form to `build_expr` instead — a silent mis-parse, not an
error. This is the *residual* of baseline #2: the dual entry pair is gone, but
the "what is a top-level form" knowledge is still expressed twice.
*Lens v (resolution-seam / single-classifier), lens vi (Principle 7).*
**Proposed consolidation:** drive both the routing predicate and `build_form`'s
accepted-head dispatch from one source (e.g. a single `classify_head(head) ->
HeadKind` enum). Folds naturally into the F4 shared-classifier extraction.

### F8 — Inline-test bulk in the two deep modules — Suggestion
`ast_builder.rs` 1768→4077 is test (60% of file); `reader.rs` 961→1781 is test
(35%). Baseline #6 / rec #6. The baseline explicitly recommended KEEPING tests
local; the only cost is scroll/readability. Lowest priority; if the F1 split
happens, the tests move with their subsystems naturally. No standalone action.

---

## 2. Lens coverage summary

| Lens | Result |
|---|---|
| (i) duplicated code paths / mirrors | F2 (synth DSLs), F4 (test/prod mirror), F5 (dotted-path), F7 (head-set skew) — the crate's dominant theme |
| (ii) dead paths (e.g. `produce_disasm` zero-call class) | **CLEAN.** S43 MacroExpander removal left NO frontend residue — the trait now lives in `cranelisp_types::MacroExpander` (referenced only in `lib.rs:12,269` doc comments). No vestigial dispatch, no `#[allow(dead_code)]`, no zero-call-site pub fns found. |
| (iii) function-budget overruns | **CLEAN.** No production function >100 lines in either deep module (vs baseline's "multiple 40–90 line functions" — improved). |
| (iv) RC-symmetry (Decision 24) | **N/A** — frontend does no RC/codegen; no consuming-inc sites. |
| (v) resolution-seam consolidation | **MOSTLY CLEAN.** Frontend correctly defers NAME resolution to int/typecheck (only constructs `SymbolRef::new(None, …)` / `ModuleFullPath` splits, `ast_builder.rs:1411,1441,1511,1674`). The two frontend-owned resolution acts — `super` rewrite (`module_extract.rs:227-242`) and qualifier splitting — are single-seam and documented (BC invariant #3). The one skew is F7 (top-level-head classification expressed twice). |
| (vi) interim-architecture residue (Principle 8) | F3 (stale PEG docs), F2/F4/F7 (Principle-7 single-source gaps). No interim *code* path — `build_repl_input`/`build_top_level` dual pipeline (the old interim shape) is fully retired. |
| (vii) cross-crate / host-callback hygiene (R5b) | **CLEAN for frontend.** Frontend has no FFI/host-callback surface (it is text→Sexp→AST, all in-process). It emits `cranelisp_types` DTOs (`ParsedEntry`, `TopLevel`, `Expr`, `Sexp`) across the crate boundary via the documented facade (`lib.rs` re-exports, `public-api.txt`). No hand-rolled boundary marshalling that a sibling also hand-rolls; the S86 host-callback-divergence family (0407) does not touch this crate. |

---

## 3. Disposition

No Blocker. No emergent-mandatory refactor (no over-budget function, no
third-duplicate that crosses the in-sprint trigger — F4/F7 are *two*-site mirrors
that *edge* toward three with the form-head vocabulary, the strongest backlog
candidate). All findings → S87 consolidation backlog (`audits/s87-findings.md`)
for the scope-decision gate. Recommended pre-Phase-H priority order if any
frontend work is funded: **F3** (cheap doc fix, carries baseline rec #5) →
**F4+F7** (shared head classifier, removes two mirrors at once) → **F2**
(synth-Sexp kit) → **F1** (ast_builder split, largest, defer behind measured
need). F5/F6/F8 are opportunistic.
