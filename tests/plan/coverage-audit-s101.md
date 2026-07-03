# S101 Special Risk Review + Coverage Audit

**Author:** `/qa` · **Date:** 2026-07-03 · **Status:** user-mandated pre-close deliverable
(`sprints/SPRINT.md` §Phase 6b, Notes 2026-07-03). Successor and widener of
`tests/plan/s101-coverage-postmortem.md` (Wave 1 — which covered only the three
Phase-3 finds; this audit covers the full 6a/6b defect set and audits the Wave-1
post-mortem's own narrowness). **This document is the S102 Phase-1 scoping input.**

**The question the user asked:** despite QA-first (20 sprint-wide guards drafted
failing-first), 5 D/D/R cycles each with review, and a ~3,480-test suite, the Phase
6a/6b user-proxy exercise found **12 real defect items** (all now guarded — ledger
§"Sprint 101 Phase 6a/6b defect set"). Why did the machinery miss them, and what
structural changes prevent the category?

**One-paragraph answer.** The 12 misses are not random: they fall into five
mechanical patterns, and each pattern maps to a structural property of how the suite
is built. (1) The assertion vocabulary is ~99% substring/presence
(1,817 presence-style call sites vs 13 exact-output assertions suite-wide), so any
defect that *adds noise or garbles shape without deleting the needle* passes — four
defects sailed through assertions that existed and ran. (2) QA-first tests drive
**canonical minimal scripts** derived from spec+design; defects that need an
*organic session history* (a bare lookup, an expression turn, an import used before
a shadow) are structurally unreachable from those scripts. (3) The suite's
restart/persistence lane existed but only over *simple healthy* states; every
compound persisted state (macro-defining-macro artifacts, broken backing files,
hand-authored files, cache-restored + redefine) was a first-visit in 6a. (4)
Strategy-implied matrices (instantiation count, rc branch, displacement shape,
genericity × reference position) had only the design-named cell pinned — the
adjacent cell crashed. (5) The at-scale **default path** (unannotated fns →
generalization → T1 downgrade) is nearly unrepresented: redefinition fixtures are
essentially all concretely annotated because that is what makes the machinery fire.
Patterns (1)–(3) are `/qa`-curable with lanes (proposed §2.4); pattern (4) is the
now-binding METHOD §2.2 discipline plus per-crate drains (§3, FIXMEs filed);
pattern (5) is a sequencing fact for S102 (§4, T1 at the top).

---

## §1 Axis 1 — Miss post-mortem, per defect

### 1.1 Miss-pattern taxonomy

| # | Pattern | Mechanism of the miss |
|---|---|---|
| **P1** | **Assertion-too-weak** | The surface WAS exercised and the test PASSED over wrong output — substring/presence needles tolerate prefix noise, garbled structure, internal-name leakage, unqualified names. |
| **P2** | **Canonical-script blindness** | The surface was exercised, but always via one minimal fixed turn sequence; the defect requires a specific *session-history preamble* (bare lookup, expression turn, use-before-shadow) that was never a test dimension. |
| **P3** | **Never-exercised state combination** | The defect lives in a compound state no lane visits: restart × broken file, persistence × macro-defining-macro, cache-restored × file-backed × redefine, dirty-cwd adoption. Individual axes were covered; the product was not. |
| **P4** | **Strategy-implied matrix, single cell pinned** | The implementation strategy creates a matrix (instantiation count, rc branch, genericity × reference position); only the design-named cell got a test; the neighbouring cell crashes/leaks. (= METHOD §2.2's target class.) |
| **P5** | **Design-blessed behavior** | The test faithfully pinned what the design said — and the design was the defect (or the designed floor is user-hostile). QA-first cannot catch what spec+design bless; only proxy/user exercise can. |
| **P6** | **Diagnostic-surface exemption** | The project standard "error tests use substring matching" (tests/CLAUDE.md §Test Standards) institutionalizes P1 for the *entire error/diagnostic surface* — internal spans, Debug reprs, phantom module names all pass. |

### 1.2 Per-defect classification

Seventeen items classified: the 12 ledger-guarded defect items, plus the carried
0474, the T1 finding, and the three instructive usability findings (0485, 0487,
0490) per the audit brief.

| Defect (guard set) | Primary | Secondary | Precise miss mechanism |
|---|---|---|---|
| **0483** vec-op-as-value at ≥2 instantiations → SIGBUS | P4 | — | Instantiation-*count* was never a matrix axis. The Wave-1 cat-3 sweep enumerated use-*positions* per builtin family but every probe used ONE instantiation of the receiving HOF; the wrapper-per-instantiation strategy (fn_as_value) makes count the load-bearing axis. The sweep audited the wrong (well, one of two) dimensions — an audit-of-the-audit finding. |
| **0484** import-shadow order-dependent resolution | P2 | P4 | Shadowing matrix: builtin-vs-user cell pinned in-sprint (0475); import-vs-user cell never pinned. And *history-dependence* (name used before shadowing defn vs not) was never a dimension — all resolution tests run one canonical order. |
| **0485** macro clause-exhaustion diagnostic (internal span, Debug FQSymbol, recursion-bottom grain) | P6 | — | Error assertions are substring-by-standard; nothing bans `1000056..`, `FQSymbol {`, or asserts the reported arity matches the user's call. Usability finding, but the *class* (internal-artifact leakage in diagnostics) is mechanically testable and untested. |
| **0486** bare lookup corrupts /info//source | P2 | — | `/info`/`/source` well tested (repl_introspection.rs, 153 tests) — but always defn→inspect. A bare-lookup turn between them was never a preamble. A "read-only" operation mutating introspection state is exactly what canonical scripts cannot find. |
| **0487** `/mod M` env ≠ module-file env | P3 | P5 | `/mod` appears in only 4 test files, always with prelude-free bodies. The invariant "module-namespace turn compiles in the module-file's environment" was never stated in a testable form, so no parity test existed. Partly P5: nothing in repl/spec.md pinned it either. |
| **0488** generic-fn FQ-call / imported-value-use missing mono (3 signatures) | P4 | — | Genericity-of-referent was not an axis in the cat-3 sweep (builtin families only). Matrix: {concrete, generic} × {bare call, FQ call, value same-module, value imported}: only the two ✓-diagonal cells were covered by incident tests. Typecheck's edge-recording is unit-tested (0470/0472 work); the *consuming turn's codegen-batch derivation* — where the defect lives — has no unit tier at all (it is src/-side; §3). |
| **0489** restart with broken backing file exits(1) | P5 | P3 | L-R5 deliberately asserted "the fire's designed floor" (load-time compile error) per the Phase-3 gate note — the designed floor IS the lockout. QA pinned design-as-specified; only /repl's user-lens assessment recognized the floor as a defect and authored the §18.8 restart-MUST-reach-prompt MUST [S102]. |
| **0491** `__expr` leaks into cascade `broken:` | P2 | P1 | L-R3's exact-set negative needles named specific *user* fns that must be absent — but every QA redefinition fixture was defn-turns-only. No expression turn ever preceded the breaking redefinition, so the wrapper never joined a transaction in any test session. |
| **trap-format** wrapper prefix (§18.5 MUST; guard-is-the-record) | P1 | — | L-R1 guards asserted `contains("is broken by the redefinition of")` — TRUE even with the `Error: codegen error at 0..0: runtime error: runtime panic:` triple-wrapper prefix. Spec pins an exact format; the assertion pinned a substring. |
| **0492** `/sig` primary line not FQ | P1 | — | The pre-existing pin `sig_shows_type_signature` asserts `contains("Fn")` — the textbook case. §18.4's "same primary line as bare lookup" MUST was drafted this sprint and its guard pinned the provenance line, not the primary line. |
| **0493** nested parameterized-ADT display garbled | P1 | — | A guard existed (`display_user_list_value_shows_elements_and_nil`) and PASSED over `(List.Cons 1 primitives/Int) (List.Cons 2 …))` — element-presence needles survive garbling and unbalanced parens. Regression window unknowable *because* the assertion was weak. 25 `display_*` tests in repl_introspection.rs share the style. |
| **D1** macro-defining-macro use poisons directory | P3 | P4 | Persistence round-trip lane exists (repl_persist.rs, 21 tests, 15 `run_again`) but its grammar covered defn/deftype/import/macro-*usage*. Macro-*defining*-macro was a first-visit. The regeneration strategy (persist expansion artifact + original form) had zero unit scenarios in save.rs. `(def x 1)` + `/quit` is a first-session user path. |
| **D2** cwd `user.cl` adoption rewrites hand-authored source | P3 | — | The fresh-tmpdir isolation discipline (tests/CLAUDE.md) structurally *excludes* the dirty-world precondition: no test ever starts in a directory containing a hand-authored `user.cl`. The isolation rule that protects tests from each other also hid the adoption/authorship-fidelity (§15.4.7) surface completely. |
| **D3** file-backed dependent recompile false-BREAKS after cache restore | P3 | — | Cache-restore lane exists (cache.rs, 31 `run_again`) and redefinition lane exists (new, S101) — their *product* (cache-restored session × file-backed module × transaction) had zero tests until the 6b guard. All L-R lanes used REPL-defined user-module symbols in fresh sessions. |
| **T1 silent split-world** (/port; not a guard — designed stage-M residue, `session-transaction.md` §10) | P5 | (default-path) | The T1 downgrade was an in-sprint design fork, reviewed and upheld; its coherent-stale shape is pinned GREEN (2 tests, flip-notes). What no lane represents: **unannotated fns are the at-scale default** (they generalize → downgrade → no report). Redefinition fixtures carry 39 concrete `:Type` annotation sites across the two redefine files vs ~2 polymorphic-target tests — the fixture idiom is the *opposite* of user code. |
| **0474** COW copy-branch leak (carried, 3 REDs) | P4 | — | rc>1-copy vs rc==1-mutate is a strategy branch matrix; all S101 wrapper guards used temporary rc==1 vecs (mutate branch). The rc>1 copy branch of the COW cores is not distinctly unit-tested at codegen level either (§3, backend). Found by /review reading RC polarity, not by any test. |
| **0490** phantom `user.primitives` module error | P6 | — | Same class as 0485: qualified-name error path exercised, but substring standard tolerates the misleading re-anchored module name, the `'...'` placeholder leak, and the `0..0` span. |

### 1.3 Pattern counts (primary classification, 17 items)

| Pattern | Count | Items |
|---|---|---|
| P1 assertion-too-weak | 3 | trap-format, 0492, 0493 |
| P2 canonical-script blindness | 3 | 0484, 0486, 0491 |
| P3 never-exercised combination | 4 | 0487, D1, D2, D3 |
| P4 strategy-matrix single cell | 3 | 0483, 0488, 0474 |
| P5 design-blessed behavior | 2 | 0489, T1 |
| P6 diagnostic-surface exemption | 2 | 0485, 0490 |

Secondary tags add: P1 +1 (0491), P3 +2 (0489, D1-adjacent), P4 +2 (0484, D1), P5 +1 (0487).

**Reading.** No pattern dominates — this was not one hole but five. But they
polarize into two families: **P1/P2/P3/P6 (12 of 17 with secondaries) are
e2e-suite-construction properties** that `/qa` can cure with assertion policy +
lane structure (§2.4); **P4 is the unit-tier discipline** now binding in METHOD
§2.2 and needing the per-crate drains (§3). **P5 is not a testing failure at
all** — it is the reason Phase 6a exists, and it argues for keeping proxy
assessment mandatory even in machinery sprints (both P5 items were found by
proxies exercising *judgment*, not scripts).

### 1.4 Audit of the Wave-1 post-mortem's narrowness

The Wave-1 post-mortem (`s101-coverage-postmortem.md`) was correct but under-scoped
on its own axis: its cat-3 sweep enumerated use-*positions* per *builtin* family and
explicitly recorded its not-probed list — but two axes that mattered were not
conceived as axes: **instantiation count** (0483 — one step past every probe) and
**genericity of the referent** (0488 — user/stdlib generic fns are not a "builtin
family", so the sweep never looked). Its §3.3 standing rule ("new registration
kinds get a value-use row") keys on registration kind; 0488 shows the failure axis
is broader: *anything whose codegen artifact is minted per-consumer* (mono
instances, wrappers) needs the value-use × instantiation-count row. Superseding
standing rule in §2.5 below.

---

## §2 Axis 2 — Coverage-model audit (e2e suite)

Evidence gathered by direct inspection of `tests/*.rs` (69 files, 1,476 `#[test]`
fns; the remaining ~2,000 of the 3,480-run suite are crate unit tiers, §3).

### 2.1 Assertion vocabulary — confirmed, quantified

| Assertion style | Call sites | Share |
|---|---|---|
| Presence: raw `.contains(` | 1,309 | — |
| Presence: `assert_stdout_contains{,_all}` / `assert_stderr_contains` | 508 | — |
| **Presence total** | **1,817** | **~99.3%** |
| Absence: `does_not_contain` | 55 | — |
| **Exact output**: `assert_stdout_eq` (2) + `assert_output_eq` (11) | **13** | **~0.7%** |
| Regex: `assert_stdout_matches` | 0 | (helper exists, unused) |
| Golden: `assert_golden{,_masked}` | 0 | (helper exists, unused) |

The spec pins exact display formats in many places (`repl/spec.md` §1.4 FQ types,
§1.5 value rendering incl. the recursive ADT form, §5.1 error format, §18.3 cascade
report layout, §18.5 trap format) — and the suite has effectively **no exact-output
lane**. Four S101 defects (0492, 0493, trap-format, 0491-secondary) passed through
existing assertions. The `assert_golden` and `assert_stdout_matches` helpers were
built and never adopted.

**Nuance kept:** substring matching is the RIGHT default for *error* resilience
(tests/CLAUDE.md standard) — the cure is not "make everything exact" but (a) exact
assertions where the spec pins exact *display* output, and (b) a universal
*negative* vocabulary banning internal artifacts (§2.4 L-N1/L-N2).

### 2.2 Negative coverage distribution

Per-file `_neg_`/`_not_` counts: 15 files with ≥10 tests carry **zero**
negative-named tests, including `spec_11_stdlib.rs` (57 tests), `cache.rs` (34),
`spec_06_pattern_matching.rs` (25), `build_confidence.rs` (18). High performers:
`repl_negative.rs` (18/51), `spec_08_modules.rs` (16/68), `repl_introspection.rs`
(29/153). Whole-suite `does_not_contain` = 55 sites across 1,476 tests — the
"verify wrong things absent" convention is real but thin, and concentrated where
past sprints forced it. **cache.rs at 0 negatives** is the standout given D3/D1
both live on the cache/persistence surface.

### 2.3 Lifecycle/state-space coverage — the confirmed structural gaps

| Suspected gap | Verdict | Evidence |
|---|---|---|
| (c) Single-session-only REPL testing | **PARTLY confirmed** | Multi-session exists: `run_again` has 67 call sites in 10 files (cache.rs 31, repl_persist.rs 15). But pre-6b, restarts covered only *simple healthy* persisted states. Compound states — broken backing file (0489), macro-defining-macro artifact (D1), hand-authored file (D2), hybrid batch/REPL meta (D2 residue, UNREDUCED) — were all first-visits. The lane is a *line*, not a *grid*. |
| (d) No file-backed-module + `/mod` lane | **Confirmed** | `.file(` fixtures are dense in spec_08 (117 sites) for load/import semantics, but `/mod` appears in only 4 files and never with prelude-dependent bodies (0487) nor combined with redefinition before the 6b D3 guard. |
| (e) Cache-restored vs fresh-session paths | **Confirmed for interaction surfaces** | cache.rs covers hit/consistency/invalidation; no pre-6b test drove an *interactive mutation* (redefine, `/mod` turn) in a cache-restored session. D3's cell (restored × file-backed × redefine) was empty; its fresh-session control passes — the divergence is exactly the untested axis. |
| (f) Unannotated default path | **Confirmed** | 39 concrete-annotation sites across repl_redefinition.rs + repl_persist_redefine.rs; ~2 polymorphic-target tests (coherent-stale pins). Every transaction-fires test uses annotated fns; unannotated fns (the at-scale default per /port) take T1 and are represented only by the residue pins. |
| (a) Substring where spec pins exact | **Confirmed** | §2.1. |
| (b) Zero-negative surfaces | **Confirmed** | §2.2. |

### 2.4 Proposed lanes (named, durable — S102 /qa work unless noted)

| Lane | File(s) | Content | Cures |
|---|---|---|---|
| **L-N1 display-exact** | `tests/display_exact.rs` (new) | Exact-output (`assert_stdout_eq` on the answer line / `assert_golden_masked` on transcripts) for every spec-pinned display class: value rendering incl. nested parameterized ADTs ×{Vec, ADT-in-ADT, Option-in-Option}, `/sig`+`/info`+bare-lookup primary-line *agreement* (assert the three render identically, not three substrings), §5.1 error format, §18.3 cascade report as a whole block, §18.5 trap line. Masks for spans/byte-counts. | P1 (0492/0493/trap-format class) |
| **L-N2 no-internal-artifacts sweep** | `tests/helpers/e2e.rs` + applied per-lane | A shared negative needle-set applied to captured stdout of diagnostic-producing tests: `FQSymbol {`, `ModuleFullPath(`, `Symbol(`, `__expr`, `__macro_`, `at 0..0`, `1000###..` internal-span shape (regex — first real use of `assert_stdout_matches`), `'...'` placeholder. Cheap to bolt onto existing error tests; consider harness-default with opt-out. | P6 (0485/0490 class), P1 |
| **L-S1 session-history preambles** | extend `repl_introspection.rs`, `repl_redefinition.rs` | For each introspection/report surface, re-run the core assertion under a preamble grid: {∅, bare lookup of the symbol, expression turn calling it, prior failed turn, `/reset`}. Parameterize via a helper that prepends preambles to stdin. Start with the surfaces 6a burned: `/info`/`/source` (0486), cascade report (0491), shadow-resolution order (0484). | P2 |
| **L-S2 session-lifecycle grid** | `tests/repl_lifecycle_matrix.rs` (new) or extend `repl_persist*.rs` | Restart × session-end-state grid: {healthy defns, broken symbol (0489), macro-defining-macro used (D1), redefined-with-frozen-slot, `/mod`-touched module} × {clean restart, `--no-cache` restart, cache-wiped restart}. Plus the **dirty-world cells** the tmpdir discipline hides: pre-seeded hand-authored `user.cl` (D2 authorship fidelity §15.4.7), pre-seeded stale `.meta.json`. Deliberate dirty fixtures are compatible with fresh-tmpdir isolation — the tmpdir is fresh, its *contents* are staged. | P3 |
| **L-S3 file-backed dev-loop** | `tests/repl_mod_devloop.rs` (new) | The exemplar-shaped loop as e2e: file-backed modules + `/mod M` turns × {fresh, cache-restored} × {same-module, cross-module dependents} × {prelude-using, prelude-free bodies} (0487 parity), redefine → cascade → revert → restart. Seeded by D3's guard + control pair. | P3, 0487 |
| **L-M1 reference-shape × referent-kind matrix** | extend `generic_value_use_mono.rs` + `vec_query_value_use.rs` | The generalized cat-3: referent {builtin-inline, builtin-extern, user-concrete, user-generic, imported-generic, stdlib-generic, trait-method} × position {direct, FQ call, HOF-arg, curried, returned, stored} × **instantiation count {1, ≥2}** (the 0483 axis). Populate incrementally: crashing/erroring cells become guards, passing cells become one-line controls. Do not enumerate blindly — one exemplar per registration/minting kind per axis (post-mortem §3.2 bounding rule stands). | P4 (e2e half) |
| **L-U1 unannotated-default siblings** | alongside every transaction e2e | Every redefinition/transaction lane gets ONE unannotated sibling pinning current T1 behavior (coherent-stale/no-report) with a flip-note naming the cure acceptance (report-or-recompile). This makes the at-scale default path *visible* in the suite and gives the T1 cure a ready acceptance surface. | P5-residue, (f) |

### 2.5 Standing rules fed back into QA practice (supersede post-mortem §3.3)

1. **Value-use rows key on artifact-minting, not registration kind:** anything whose
   callable artifact is minted per-consumer (wrappers, mono instances, curry
   thunks) gets value-use × **instantiation-count ≥2** rows at drafting.
2. **A MUST that pins display *shape* gets an exact assertion, not a substring.**
   Substring remains the standard for error *matching* resilience; shape-pinning
   MUSTs go in L-N1.
3. **New session-visible state kinds** (this sprint: BROKEN symbols, frozen slots,
   retained code) each get a restart row and a preamble row at drafting time — the
   lifecycle grid grows with the state space, not after it.
4. **When QA pins a designed floor, flag the floor to the user-proxy skills in the
   same sprint phase** (0489 lesson: the pin was faithful; the floor was the
   defect — earlier proxy eyes on "is this floor livable?" beats post-hoc).

---

## §3 Axis 3 — Per-crate unit-tier thinness map (submodule granularity)

Method: full submodule inventory (LOC via `wc -l`), test attribution via test-file
placement + name/API matching, scenario-class judgment per METHOD §2.2
{complexity, edge, negative}. "ZERO" = no attributable unit tests; "HAPPY" =
tests exist, no negative/edge coverage. This map is the work-list for the S102
`/dev`(crate) drains (FIXMEs §5).

### 3.1 Verdict table (one line per crate)

| Crate | LOC | Unit tests | Organization | Verdict |
|---|---|---|---|---|
| cranelisp-backend | 32,548 | 311 | **Anti-pattern**: flat 5,861-line crate-root `tests.rs` (76 tests) + partial sibling files | **THIN + unattributable core**: ~5,000 LOC of compiler strategy (rc_emission, fn_as_value, match_codegen, let_if, lambda, resolution, dependent_spark, context) with zero dedicated per-submodule tests |
| src/ (binary+lib) | 50,323 (incl. tests) | ~574 | Mixed: S101 + concurrency seams follow the sibling-tests.rs convention; many pre-S101 modules bare | **THIN on exactly the 6a defect surfaces**: lifecycle.rs (1,918 LOC, ZERO), eval.rs (600, ZERO), display.rs ADT-value render (ZERO direct), save.rs macro round-trip, repl handlers |
| cranelisp-typecheck | ~15k | ~480 | Per-submodule `tests.rs` convention — the positive exemplar | **GOOD except `traits/`**: ~3.1k LOC (monomorphise 1070, impl_check 842, type_resolve 453, dispatch 411, registry 357) pooled behind one 41-test file |
| cranelisp-intrinsics | 16,619 | 228 | Per-submodule convention | **ADEQUATE**; thin spots: io_guard (245, ZERO), strand (400, 3 tests), trace_format happy-only |
| cranelisp-primitives | 3,156 | 82 | Per-submodule convention | **ADEQUATE** (marshal.rs + ring0.rs happy-only) |
| cranelisp-types | ~8k | ~111 | Per-submodule convention | **ADEQUATE with holes**: ast.rs (831, ZERO), check.rs/newtype.rs/sexp.rs/macro_expander.rs/marshal.rs ZERO; got.rs + scheduling.rs happy-only |
| cranelisp-platform | ~3.6k | ~46 (+14 integration) | Crate-root tests.rs + partial siblings | **ADEQUATE at the marshaling boundary** (its strength); declare.rs (445) + concurrency.rs (113, v8/v9 ABI vtable/waker) ZERO inline |
| cranelisp-frontend | 9,538 | ~320 | Per-submodule tests.rs convention throughout | **GOOD** structurally (ast_builder 153 tests, reader 88, heavy negatives); gap is diagnostic-*string* quality (0485 class) — no test asserts a rendered message |

### 3.2 Backend — deep map (the priority drain target)

Flat `tests.rs` attribution (76 tests, bucketed by primary API): vec_codegen 20+,
got 6–20, lib/module-assembly 6–20, resolution/apply dispatch 6–20, fn_as_value
1–5, trap stub 3, fn_compiler 3, extern_call 2, lambda/launch 3, literals/match 2,
jit/disasm ~3. Splitting this file along submodule lines (moving each bucket to a
sibling `tests.rs` next to the module it exercises) is the enabling first step —
until then, per-submodule coverage claims in the flat file are archaeological.

Highest-risk thin submodules (all strategy-bearing; absolute paths under
`/home/alilee/cranelisp/crates/cranelisp-backend/src/`):

| Submodule | LOC | Attributable tests | Why it matters |
|---|---|---|---|
| `compiler/rc_emission.rs` | 788 | **2 inline** | Core RC inc/dec + drop-glue emission — the worst coverage-to-strategy ratio in the codebase; RC polarity bugs (0474 class) live here and were found by review reading, not tests |
| `compiler/control_flow/fn_as_value.rs` | 960 | ~7 (all happy) | The S100/S101/0483 crash seam; wrapper emission per arity/instantiation has no edge or negative coverage; **the 0483 instantiation-count matrix and 0474 rc-branch matrix belong here as unit scenarios** |
| `got.rs` | 104 | 2 inline + ~7 flat | Self-documented "UNCHECKED" allocation; exhaustion surfaced-error (W4 work), freeze, trap-patch have no direct unit tests |
| `compiler/match_codegen.rs` | 588 | 0 dedicated | Pattern lowering with no shape matrix |
| `compiler/control_flow/let_if.rs` | 472 | 0 dedicated | Branch RC (the copy-vs-mutate divergence across arms) untested |
| `compiler/control_flow/dependent_spark.rs` | 433 | 0 | Spark-dependency state machine, zero coverage |
| `compiler/resolution.rs` | 426 | 0 dedicated | Trait + curry resolution seam (the 0488-adjacent curry arm) |
| `compiler/control_flow/lambda.rs` | 538 | 0 dedicated | Closure/capture emission |
| `primitives_inline.rs` | 612 | 11 (all `_happy`-named) | The curry unknown-builtin arm (second 0483-fix seam) — zero negative |
| `cache/linker.rs` | 805 | 6 | Thin vs LOC for a strategy module |
| vec COW cores (`compiler/vec_codegen.rs` + intrinsics `vec_runtime.rs`) | 1,532 | rc-decision-table pinned; **runtime rc>1 copy branch NOT distinctly unit-tested** | The 0474 leak branch — exactly the untested cell |

Well-covered backend exemplars (proof the convention works where applied):
`jit/tests.rs` (20), `cache/manifest/tests.rs` (24, 10 neg), `sparkability_tests.rs`
(16), `par_codegen_tests.rs` (12).

### 3.3 src/ (binary+lib) and cranelisp-frontend — map

**src/**: 72 files, 50,323 LOC (incl. tests), ~574 `#[test]` fns. The convention
split is stark: the concurrency/persistence machinery built under recent-sprint
discipline is well covered per-submodule (`scheduler` 52 tests, `worker` 34,
`bind_chain_analysis` 41, `platform` 26, `observability` 31, S101's `redefine.rs`
11 incl. negatives); the older session/REPL strategy layer is bare.

ZERO-coverage strategy-bearing submodules (absolute paths under
`/home/alilee/cranelisp/src/`):

| Submodule | LOC | Why it matters |
|---|---|---|
| `session_v4/lifecycle.rs` | **1,918** | Restart/reload/watcher/shutdown — the 0489 lockout home and the S101 `*code = None` finding's home. **Largest untested surface in the repo.** |
| `eval.rs` | 600 | Core evaluation path |
| `process_form/macro_resolution.rs` | 617 | Macro resolution during form processing |
| `process_form/cache_restore.rs` | 448 | Cache-restored-session path — the D3 axis, zero unit scenarios |
| `process_form/form_dispatch.rs` | 368 | Form dispatch |
| `link/mod.rs` + `link/apple.rs` (+`gnu.rs` at 1 test) | 562 | Linker/ABI emission, platform-forked |
| `worker_pool.rs`, `sched_dump.rs`, `session_v4/types.rs` | ~590 | Lower blast radius |

Happy-path-only / defect-adjacent gaps (tests exist, the defect's cell doesn't):

- **`display.rs` (983 LOC, 24 tests) — the 0493 exhibit at unit tier**: all 24
  tests exercise primitive formatting or type-def helpers; `format_adt_value` /
  `format_adt_heap_value` (the nested-ADT render that garbles) has **zero direct
  tests**. The file *looks* covered; the strategy path isn't.
- **`save.rs` (1,529 LOC, 27 tests)**: regen role gate, docstring round-trip,
  preamble reemit covered; **no test aims at macro-definition regeneration** (the
  D1 poison grammar) or dep-sorted macro emission.
- **`process_form/dependency.rs` (1,580 LOC, 6 tests, happy-only)** — the
  consuming-turn batch derivation neighborhood (the 0488 defect's suspected src/
  half) is effectively untested at unit grain.
- **`repl.rs` (3,357 LOC, 16 tests)**: tests target formatters, not handlers —
  `handle_sig` (0492), `handle_mod` display half (0487), `handle_source` are not
  driven by any unit test.
- **`redefine.rs` report render**: tested (`report_render_sections_and_qualification`)
  but nothing asserts synth-wrapper (`__expr`) exclusion — the 0491 cell.
- **`session_v4/index_worker.rs` `record_source_hash`**: the `/info` render arms
  are pinned (info_source_tests, 2), but the bare-lookup-turn *recording* trigger
  (the 0486 mechanism) is not directly asserted.
- **`pipeline.rs` (382 LOC, 6 happy tests)** — `__expr` wrapper execution home.

**cranelisp-frontend**: 12 files, 9,538 LOC, ~320 tests — the per-submodule
convention throughout (`ast_builder/tests.rs` 153 with heavy negatives,
`reader/tests.rs` 88, `module_extract` 25, `defmacro` 22, `quasiquote` 15).
Structurally the second exemplar after typecheck. Its one systemic gap is
**diagnostic-string quality**: `defmacro.rs`'s span-carrying errors and
`module_extract.rs:533`'s `{:?}` Debug-leak (`"expected symbol for {}, got {:?}"`)
have no test asserting the *rendered message* — the 0485 failure mode (internal
span + Debug FQSymbol dump) is invisible to an otherwise well-tested crate. The
0485 fix should land with message-string unit tests per METHOD §2.2 (noted here
rather than a new FIXME — 0485 is already open against /frontend).

### 3.4 Typecheck, types, platform, intrinsics, primitives — flags

**cranelisp-typecheck** (the organizational exemplar — per-submodule tests.rs,
~480 attributable tests, strong negative counts in infer/program/adt/unify):

- `traits/monomorphise.rs` (1,070 LOC) — **zero inline tests**; the single most
  strategy-dense module (mono emission, `register_mono_entry`,
  `finalize_mono_codegen_view`, inner-parametric hops). Pooled `traits/tests.rs`
  (41 tests) is unattributable per-submodule — the crate's own local instance of
  the backend anti-pattern.
- `traits/impl_check.rs` (842) + `type_resolve.rs` (453) + `dispatch.rs` (411) +
  `registry.rs` (357) — same pool.
- `scheme.rs`, `cluster.rs` (SCC), `scope.rs` — happy-path-only (0 negative).
- **0488 relevance**: typecheck's edge-recording IS unit-tested
  (`program/tests.rs`: `callees_records_fn_as_value_*`, uniform-carrier); the
  defect's home — the consuming turn's codegen-*batch* derivation — is downstream
  in src/, which has no unit tier for it. The unit-tier hole is src/-side, not
  typecheck-side.

**cranelisp-types**: `ast.rs` (831, ZERO), `check.rs` (259, ZERO), `newtype.rs`
(253, ZERO), `sexp.rs` (159, ZERO), `macro_expander.rs` (137, ZERO), `marshal.rs`
(75, ZERO — rustdoc says it must stay byte-synced with primitives' marshal.rs and
builtin ctor order: a drift-prone constant table with **no drift-guard test**);
`got.rs` + `scheduling.rs` happy-only. `module.rs` `callable_got_slot` seam is
adequately tested (25 tests) — the S83 structural work carries its own pins.

**cranelisp-platform**: marshaling boundary well tested (byte-layout guards,
descriptor lifting, neg arms). `declare.rs` (445, the `declare_platform!`
emitter) and `concurrency.rs` (113 — the v8/v9 HostCtx vtable/Waker C-ABI) have
zero inline tests; both are ABI-bearing.

**cranelisp-intrinsics**: strong overall (reactor 33, io 35, panic 20/19-neg).
Thin: `io_guard.rs` (245, ZERO — an IO-guard state machine), `strand.rs` (400,
3 happy), `trace_format.rs` happy-only.

**cranelisp-primitives**: adequate; `marshal.rs` + `ring0.rs` happy-only. Zero
`#[should_panic]` crate-wide.

---

## §4 Axis 4 — Risk register for S102 sequencing (ranked by user impact)

Rank = what a real user hits first/worst. Internal severity noted where it
diverges. "Guards" = failing-not-ignored REDs already in the suite.

| # | Risk | User-visible symptom | Blast radius | Owner | Proposed S102 disposition |
|---|---|---|---|---|---|
| **1** | **T1 silent split-world on unannotated redefinition** (design residue, §10 session-transaction.md; /port 6a) | Edit a function live; REPL shows the new behavior; the running program silently keeps the old one. No report, no trap, no error — silent wrongness at the heart of the sprint's headline feature. | **The at-scale DEFAULT**: unannotated fns generalize → T1 downgrade; nearly all real code is unannotated (exemplar: ~all fns). The concrete-annotated path the S101 UX shines on is the exception in practice. | /int (+/design int: end-of-turn-sequenced module reload per §10 residue) | **Top of S102 scope** (competes only with the crash cluster). /qa lands L-U1 unannotated siblings FIRST so the cure has acceptance tests. Interim honesty: T1 turns could at minimum *print* the downgrade ("polymorphic target — dependents not recompiled") — a small /int change that converts silent to visible while the full cure lands. |
| **2** | **Persistence/restart integrity cluster: D1 + D2 + 0489** (guards: 3 RED) | D1: `(def x 1)` + `/quit` → next start exits(1); `--no-cache` doesn't recover — **directory poisoned by the most ordinary first-session input**. D2: REPL adopts and REWRITES a hand-authored `user.cl` — **user data loss**. 0489: ending a session with a broken symbol locks you out of the directory. | Every REPL user; D1/D2 destroy trust in persistence itself; recovery requires hand-editing files the user may not know exist. | /int | **S102 early wave.** These three share the save/load round-trip seam (save.rs regeneration grammar + adoption policy + load-failure floor). Fix as one seam visit; L-S2 lifecycle grid lands with it. D2's unreduced hybrid-meta residue rides the fix (ledger note). |
| **3** | **0488 generic-fn FQ-call / imported-value-use missing mono** (guards: 3 RED, three signatures, stdlib-free) | Passing any stdlib/imported generic fn as a value, or FQ-calling one, fails "undefined function/variable"; composition failures blame the WRONG function; stdlib `vec-flatten` unusable from user code. | High and *newly* load-bearing: S101's vec unlock invites exactly this usage one step further; the 6b `vec-concat` simplification attempt was reverted over it (a fold-bodied stdlib fn can abort cold startup). Blocks idiomatic functional style at scale. | /backend//typecheck seam — isolation owed (batch derivation is src/-side; typecheck edges verified complete) | **S102 with the fn-as-value seam work.** Sequence the cross-crate isolation (tests/CLAUDE.md §Isolating) before fix dispatch — the three signatures may not share a single home. |
| **4** | **fn_as_value/COW seam cluster: 0483 SIGBUS + 0474 leak (+0476 representation cure)** (guards: 3+3 RED) | 0483: two instantiations of one HOF taking a vec op as value → hard crash (SIGBUS), both modes. 0474: curried `vec-set`/`vec-push` leaks 2 allocs *per call*; /port notes the exemplar's `set-cell` is the leaking shape (deep backtracking → growth). | Crash-grade but shape-specific (one step past shipped examples); leak is silent and unbounded under load. | /backend | **Already sequenced**: rides increment I's rework of the same seam (backend §12.7, 0476 ruling pinned to increment-I first change-sets). Hold that sequencing; the METHOD §2.2 instantiation/rc matrices land as unit scenarios WITH the rework (FIXME below). |
| **5** | **File-backed dev-loop cluster: D3 + 0487** (guard: 1 RED + control) | The at-scale edit loop is blocked: `/mod M` can't compile real module fns (no prelude values/aliases in scope); in cache-restored sessions the redefining turn dies at an unknown-type wall; exemplar-grade faces false-BREAK with restart-only recovery. | Anyone using the REPL against a real multi-module project — i.e. the entire "live development at scale" story S101 was building toward. | /int | **S102 alongside #2** (same /int neighborhood: turn-environment construction + recompile env). L-S3 lane lands with it. 0487's introspection-FQ-names half is small and high-leverage (the cascade report prints names the user cannot paste into `/info`). |
| **6** | **0486 bare-lookup introspection corruption** (guards: 2 RED + control) | The first thing the self-documenting REPL teaches (type a name) corrupts `/info`/`/source` for that symbol — the S101 headline display shows the wrong source for exactly the symbols the user inspected. Restart heals. | Every REPL user, immediately; state-corruption class (a read mutating), likely small fix on the bare-lookup evaluation path's introspection recording. | /int | S102 with the /int wave. L-S1 preamble lane generalizes the guard. |
| **7** | **0484 import-shadow order dependence** (guard: 1 RED + control) | Whether your `defn count` wins over an import depends on whether you called the import first; `/info` disagrees with what a call does. | Coherence/trust; workaround (FQ call) is itself broken by 0488 — the two compound. | /int; /spec may pre-pin precedence (spec/08 anchor) | S102: /spec pins the precedence rule first (small), then fix; guard re-anchors if the ruling differs. |
| **8** | **Display/diagnostics cluster: 0493 + 0492 + trap-format + 0491 + 0490 + 0485** (guards: 7 RED across the set) | Garbled nested-ADT values with unbalanced parens (looks like memory corruption to a user), noisy triple-wrapped trap prefix, non-FQ `/sig`, `__expr` noise in cascade reports, misleading phantom-module errors, Debug-repr leaks in macro diagnostics. | Individually cosmetic-to-confusing; collectively they erode the "self-documenting REPL" principle the project leads with. 0493 is the loudest (structurally wrong output). | /int (0493/0492/0491/0490 display seams), /frontend (0485), /repl (0492 arbitration) | S102 batch as one display-seam sweep (most share `src/` display/rendering); L-N1/L-N2 lanes pin the class shut behind them. |
| **9** | **Unit-tier structural debt** (this audit, §3) | Not user-visible directly — it is the *manufacturing defect* behind #3/#4-class escapes: strategy seams with single-cell coverage keep shipping crash-adjacent cells. | rc_emission (788 LOC/2 tests), fn_as_value (960/7), traits/monomorphise (1,070/0 inline), save.rs-class src/ seams, types marshal drift-guard. | /dev per crate (FIXMEs §5) | S102+: drains ride each crate's first S102 touch (backend split first — it is also increment I's landing zone). Not a standalone sprint; a standing obligation per METHOD §2.2. |
| **10** | **D2 hybrid-meta residue + /docs 1-of-7 spurious-broken** (unreduced; ledger notes) | Next-session breakage after hybrid batch/REPL cache sharing (exemplar-only so far); one unreproduced spurious-broken under fast piped input. | Unknown — both are recorded, neither reproduced under reduction. | /qa watch | Re-probe when #2's fix lands (the same seam likely moves both); record any flake per the ledger rule, do not chase. |

**Recommended S102 shape (test-work priority order for /qa):** L-U1 unannotated
siblings (enables #1) → L-S2 lifecycle grid + L-S3 dev-loop lane (enables #2/#5)
→ L-N1/L-N2 display lanes (pins #8 shut as fixes land) → L-S1 preambles →
L-M1 matrix growth with the increment-I seam work (#3/#4).

---

## §5 Actions

### 5.1 Enabler FIXMEs filed by this audit

| FIXME | Target | Enabler |
|---|---|---|
| 0495 | /dev (cranelisp-backend) | Split the flat crate-root `tests.rs` along submodule lines + drain the named thin strategy submodules (§3.2 table) per METHOD §2.2 — sequenced with increment I's first backend change-sets |
| 0496 | /dev (src/) | Unit-tier drain for the named pre-S101 strategy seams (§3.3) — save.rs regeneration grammar, introspection recording, display rendering, batch derivation |
| 0497 | /dev (cranelisp-typecheck) | De-pool `traits/` — per-submodule test modules for monomorphise/impl_check/dispatch/type_resolve/registry per the crate's own convention |
| 0498 | /dev (cranelisp-types) | Drift-guard test for `marshal.rs` byte-sync contract + minimal cover for the ZERO logic modules (check.rs, newtype.rs) |

(No FIXMEs for guarded defects — the 22 REDs are the record, per
`memory/feedback_no_fixme_with_failing_test.md`. Lane construction (§2.4) is
/qa-owned S102 work and needs no FIXME.)

### 5.2 Durable /qa commitments (S102)

1. Land lanes in the priority order above; every lane's tests carry `// spec:`
   anchors and ledger rows per the standing discipline.
2. Apply §2.5 standing rules at every QA-first drafting pass.
3. Re-verify this document's §3 map at S102 close (the drains should visibly move
   the ZERO/HAPPY flags).
