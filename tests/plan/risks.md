# QA Risk Review

## S111 risk read (2026-07-17, /qa — shapes the depth of the S111 plan in `PLAN.md` §"Sprint 111")

S111 pairs an emission-affecting schema-window centrepiece (the §3.7 vec-COW
ownership root) with byte-identical refactors (R4/R5), a language-surface fix
with a data-corruption hazard (quasiquote fold vs int shield), and a
release-phase UB closure (GOT). The profile is dominated by *partial landings
of coordinated change-sets* and *fix-polarity inversions*.

| # | Risk | Severity | Why silent | Guard (PLAN §S111 rows) |
|---|---|---|---|---|
| S111-1 | **Schema-20 window discipline** — two persisted-meaning changes (truthful COW facts; 0621 `callees` → storage keys) must sit inside the ONE commit window that bumps `CACHE_SCHEMA_VERSION`; a cache written between two separate bumps carries schema-20 with alias edges, and the reverse-index consumer (when it goes live) silently misses affected-set closures — the 0472 starvation class | HIGH | No error at write OR read time; the failure fires in a future sprint's session-transaction machinery | CW-S1 (stale-cache invalidated wholesale) + CW-S2 rider units + CW-S4 one-window `/review` criterion |
| S111-2 | **RC fix-polarity inversion** (S110-8 successor) — curing the vec-COW under-count (UAF) by widening flips it into an over-count (leak) that the flipped-GREEN value-correctness repros cannot see; conversely the conservative copy-arm residual could silently WIDEN | HIGH | A leak is invisible to value assertions; a widened residual looks like "still no UAF" | The three `vec_cow_value_use_leak.rs` must-holds + CW-F2 pinning the residual at EXACTLY one count per call (any widening fails loudly) |
| S111-3 | **Partial landing of the 3-layer root** — facts (a2) without reachability (a3) leaves declared facts silently dead in production (the exact §3.7 gap); a1 without a2 has no producer; the suite stays green either way because the default is conservative | HIGH | Conservatism masks absence — nothing miscomputes, performance/RC behaviour just silently stays wrong-class | CW-F3a/CW-F3b twin fence (prelude-fallback leg RED until a3); CC-R1..R5 per-site three-path units; ONE-change-set is the arch ruling `/review` enforces |
| S111-4 | **Quasiquote fold-without-shield** — post-fold, int's Pass-1 macro expander rewrites macro-call-shaped lists INSIDE quoted literals before the desugar sees them: `(defn f [] '(m x))` silently corrupts quoted DATA (wrong value, no error) | HIGH | The corruption only fires when a quoted list head collides with a registered macro name — rare in tests, common in macro-writing code (the exact derive.cl audience) | QQ-I1/I2/I5 negatives authored BEFORE the wave; arch ordering: shield lands ≤ fold |
| S111-5 | **GOT fallible-refactor caller miss** — one of the 10 enumerated `allocate_got_slot` callers keeps an `unwrap`/`unreachable!` arm and exhaustion is a panic (or, pre-refactor, silent UB) on exactly that path | MEDIUM-HIGH | Exhaustion needs >1024 slots in one module — unreachable in the suite's natural fixtures | GE-1/GE-2 boundary units + GE-3 caller pins + the `/review` 10-caller sweep (GE-4 e2e if cheap) |
| S111-6 | **P24 sweep mis-classification** — an identity-scan waved through as "enumeration" launders a real divergence surface into the register as legit; the sweep's value inverts | MEDIUM | A wrong verdict looks identical to a right one unless grounds are stated and checkable | Register discipline (P24-1: grounds per row, acid-test verbatim); pre-seeded rows carry their evidence; findings must land as failing tests or FIXMEs (P24-4) |
| S111-7 | **Golden-attribution muddying** — interleaving the byte-identical R4/R5 refactors with the emission-affecting ownership wave makes CLIF diffs unattributable; a real emission drift hides inside the expected re-baseline | MEDIUM | The re-baseline "explains" every diff | §H gates + arch wave-order constraint 1 (R2 → R4/R5 byte-identical → ownership wave, re-baseline last act) |
| S111-8 | **0604 environment-bound repro** — the foreground write fires 16/16 in one environment and 0/175 in another; a fix validated only where it never fired is the S98 false-green class | HIGH | Symptom absence in the wrong environment proves nothing | IR-1 locate-first (deterministic repro or located-seam attribution BEFORE any patch) + IR-2 sweep-with-fix + twins must-hold |
| S111-9 | **0590 R1 fix regressing the S110 duty-split** — the finer discriminator re-touches `AmbiguityScanPhase` ordering; B1/B2 (wrong-reject AND wrong-accept) are one mis-ordering away in each direction | MEDIUM-HIGH | B2-class wrong-accepts codegen with never-scanned bodies — no error anywhere | OA-2 must-hold set (B1/B2 guards + RD-3 + rows 13–15 + VP-3/4/5) run at the fix |

Depth allocation: fences and pre-wave guards first (KC-N1..N6, QQ-I1/I2/I5,
CW-F3a probe, CW-F2), per the S108 Inc2 rule — arch-pre-flagged boundaries
and revert-class fences before happy paths.

## S110 risk read (2026-07-15, /qa — shapes the depth of the S110 plan in `PLAN.md` §"Sprint 110")

Most of S110 is behaviour-invariant plumbing (0583 waves, R-2 wiring,
0606/0608 decomposition) — the risk profile is therefore dominated by *silent
semantic drift under an invariance claim* and by *guards that structurally
cannot be e2e*. Each row names the loud-failure conversion.

| # | Risk | Severity | Why silent | Guard (PLAN §S110 rows) |
|---|---|---|---|---|
| S110-1 | **W0/W0.b invariance drift** — the producer change-set touches every mono view and relocates the lenient builder into `cranelisp-types`; a placeholder-semantics difference in the typecheck-built lenient view changes codegen for ctor/accessor/`f$Var`/template/`__expr`/macro-clause bodies | HIGH | The suite exercises behaviour, not IR; a drift that happens to compute the same values on covered inputs ships | KC-W0-1 (suite-green, zero new REDs) + KC-W0-2 (CLIF byte-identity across the six lenient entry classes) + KC-W0-4/5 totalization unit pins |
| S110-2 | **Cache schema 18→19 skew** — a stale `.meta`/`codegen_view` deserialises `None` carriers; pre-W1 they ride unread (invisible), post-W1 they hard-fail at a distant seam with a carrier-miss error that looks like a compiler bug | HIGH | No error at read time; the failure fires one wave later, far from the cause | KC-W0-3 warm-cache + stale-cache-invalidated-not-misread negative; bump rides the W0 change-set (definition of done) |
| S110-3 | **The soft-fallback hybrid** — one keyed-read-else-`resolve_driven` arm silently masks every producer gap, voids Principle 24, and reintroduces the arbitrary-order scan as a shadow path | HIGH | By construction: the fallback makes every miss look green | Rev-2 = per-wave `/review` REJECT criterion (PLAN §A.2 structural); KC-N1..N6 loud-miss unit family proves the hard-fail is real; W3 grep gate (KC-W3-1) is the end-state pin |
| S110-4 | **W1 harness red** — the backend unit suite's fixtures don't populate sidecars; W1's hard-miss flips the whole backend unit tier RED mid-wave, and the "fix" pressure invites a soft fallback (risk S110-3) | MEDIUM-HIGH (schedule + integrity) | Discovered mid-wave, exactly when the fallback temptation is highest | KC-W0-6 — fixture-sidecar population pinned as a W0 obligation, backend unit tier green at W0 AND W1 close |
| S110-5 | **0590 tightening blast radius** — deleting the never-error `Named` fabrication converts silent fabrication into loud errors; a program (test/stdlib/example/exemplar) that leaned on fabrication breaks at the flip; conversely an over-broad mint would swallow unknown types | MEDIUM-HIGH | The fabrication *accidentally works* today — nothing marks its consumers | TX blast-radius scout BEFORE the flip; TX-5/TX-6 REDs make the tightening deliberate; TX-8/TX-9 (FV-13/FV-14) fence over-broadening |
| S110-6 | **0604 false-green fix** — a scheduling-perturbation patch quiets the phantom under the tested interleaving (the S61→S93 treadmill + the verify-fix-not-symptom lesson); ALSO: the corrected attribution (cache channel) is itself a hypothesis — patching before the sweep locates the writer risks fixing the wrong seam | HIGH | Scheduling-dependent (16/16 in one env, 0/140 in another); symptom absence proves nothing | IF-1 locate-FIRST trace sweep (gate on the fix, with the explicit re-scope arm) + IF-2 write-seam unit + IF-3 ≥25× sweep landing WITH the fix + IF-5 structural grep |
| S110-7 | **R16/R17 false-positive regression** — the S109 revert class: any drift of the new gate back toward surface-type concreteness re-flags arg-directed dispatch (`(add2 3 4)` computes but displays unpinned) and blocks valid programs | HIGH | The false positive fires only on dispatch shapes with residual display vars — easy to miss, catastrophic to users | RD-3 explicit value-position fence (authored FIRST) + RD-4/RD-5 must-holds + the §D unit enumeration grounding the signal in dispatch OUTCOME |
| S110-8 | **vec-assoc RC-fix polarity inversion** — fixing the premature free (under-count) by unconditionally inc-ing the param-aliased return converts the defect into a leak (over-count), which the flipped-GREEN repro cannot see | MEDIUM | A leak is invisible to value-correctness assertions | VA-4 — the opposite-polarity sibling `vec_cow_value_use_leak.rs` named as a must-hold fence; VA-3 unit enumeration includes the identity-fn no-over-count control |
| S110-9 | **0609 deletion on an empirical leg** — the shim-unreachable verdict's private-member leg is empirically probed, not structurally proven (the real-span visibility raise seam was not located); a future `ResolveError` variant or probe-order edit could re-open the phantom shape with the shim gone | LOW-MEDIUM | The phantom shape reports a misleading-but-plausible diagnostic — nobody files it | PLAN §I pins D-1 (three diagnostic e2e must-holds) + D-2 (gap-selection unit) + D-3 (recommended structural closure: propagate the abs hard error, making the child gap unproducible) |
| S110-10 | **Gate blindness continuation (S109-8)** — until SG-1 lands, stdlib-breaking regressions still ship invisibly; and SG-1 scoped top-level-only would MISS nested modules (`num.bits` — the 0604 blast radius itself) | HIGH (gate gap) | Nothing in the suite imports the stdlib surface | SG-1 with the RECURSIVE public-module enumeration (PLAN §E refinement 1); SG-2 build-interleave infra fix in the same wave. **P5-S1 outcome: gate landed and CAUGHT `derive` (real layered defect, FIXMEs 0613/0614 — `s110-attribution-sg1-sg2.md` §1); stays RED tracing to both** |
| S110-11 | **Agent-lane binary provenance race (SG-2, attributed)** — the harness hardcodes `target/debug/cranelisp`; any `--features agent` cargo invocation rebuilds that SAME path, so an interleaved agent-lane build swaps the binary mid-default-suite and feature-OFF guards exec a feature-ON binary | MEDIUM (dev-workflow; single-profile runs safe) | Fails only when two differently-featured cargo invocations overlap — looks "flaky" (forbidden disposition; it is deterministic in binary provenance) | FIXME 0615 (`/testing`, W-GATE lane): agent-lane `CARGO_TARGET_DIR=target/agent` isolation + lane-aware harness binary resolution; acceptance = agent family 3× consecutive full-suite passes + deliberate dual-build clobber check. Separate root from 0604 — do not fold |

Depth allocation: fences and pre-wave guards first (RD-3, KC-W0-6, TX scout,
KC-W0-2 capture), per the S108 Inc2 rule — arch-pre-flagged boundaries and
revert-class fences before happy paths.

## S109 risk read (2026-07-13, /qa — shapes the depth of the S109 plan in `PLAN.md` §"Sprint 109")

The highest-silent-failure changes in the S109 scope, ranked. Each names the
guard that converts the silent failure into a loud one.

| # | Risk | Severity | Why silent | Guard (PLAN §S109 rows) |
|---|---|---|---|---|
| S109-1 | **In-flight auto-load race** (§8.5.4 edge 7): a member probe against a present-but-non-terminal module misclassifies as "has no member" only under ≥2 priority workers with an unlucky interleaving | HIGH | Nondeterministic — any single run (and most CI runs) passes; the failure surfaces in user sessions under load. Forbidden dispositions apply: one intermittent RED = a real bug | C1-e2e repeated-run sweep (≥25 iterations) + the FOUR enumerated C1-unit arms (deterministic fail-on-revert); the cure (unconditional member-absent gap) is pinned at both the int and typecheck seams |
| S109-2 | **Exhaustiveness blast radius** of the dotted-ctor keying (design §4): (a) covered-set normalizer misses the `.`-strip → FALSE non-exhaustive on dotted-covered matches; (b) internal-flag probe stops chain-following → IO `Bind`/`Pure`/`Effect` leak into user exhaustiveness | HIGH | (a) blocks valid code with a plausible-looking diagnostic; (b) changes which programs compile with no error at the change site — both fail at a DISTANT seam from the registration edit | BR-1 + BR-2 fail-on-revert guards, authored FIRST, landing in the SAME change-set as registration |
| S109-3 | **Cache schema 16→17 skew**: the ctor `Def` storage-key MEANING changes; a stale `.meta.json` (bare keys) read by the canonical-key resolver/`type_ctor_names` silently misses ctors and mis-classifies heap categories — a UAF class (`value_layout` is soundness-coupled) | HIGH | No error at read time — resolution just misses; heap misclassification corrupts later | DC-9 warm-cache row + stale-cache invalidation neg; the bump is part of the registration change-set's definition of done (Obligation B) |
| S109-4 | **0573 product-deftype persistence** — product defs dropped from the backing `.cl` | MEDIUM-HIGH | Data loss observable only at reload, possibly sessions later | The §E shape×persistence matrix (product rows RED; sum rows pinned; no-double-emit neg) |
| S109-5 | **0570 two-seam privacy**: `/dev` could fix the import gate while the `/search` index still surfaces private-submodule symbols (or vice versa) — one rule, two enforcement seams | MEDIUM | Each seam looks fixed in isolation; the conformance gap is only visible to whichever surface wasn't probed | MV-1 (search) + MV-2 (import, existing) as a PAIR, with the MV-3 public control |
| S109-6 | **Observability log grain**: content leaking into the §17.20 JSONL (form text, error messages, prose) is a one-way door — it defeats the greppable-index grain and is hard to walk back once consumers mine it | LOW-MEDIUM | Nothing fails; the file just thickens | OB-8 no-content negative; feature-off absence family |

Ranked depth allocation: rows guarding S109-1/-2/-3 are authored FIRST
(arch-pre-flagged boundaries + spec MUSTs before happy paths, per the S108
Inc2 rule recorded in `tests/CLAUDE.md` §"QA-first targeting").

### S109 Phase-6 addendum (2026-07-15, /qa attribution dispatch)

| # | Risk | Severity | Why silent | Guard |
|---|---|---|---|---|
| S109-7 | **Racy background stdlib file-index feed** — `index_worker.rs` branch (c) typechecks THROUGH the live tables (mutate-then-undo, R13-by-cleanup); a concurrent mis-attributed write injected a phantom `bit-and → primitives/bit-and` into the live `prelude` table, spuriously firing the (correct) §8.6.5 poison and making `num.bits` unimportable. Same feed behind the #4 `/search` leak (surfacing fixed `fff94fa7`; WRITE-race persists) | HIGH | Scheduling-dependent (16/16 in one environment, 0/140 in another) — most CI runs pass; fires in user sessions. Poison-consumer is spec-correct, so the failure masquerades as a legitimate ambiguity error | Attribution record `s109-attribution-index-feed-race.md`; FIXME 0604 (`/dev` src/int, S110 fix + ≥25-iteration fail-on-revert sweep in the fixing change-set); GREEN twins `tests/spec_08_prelude_outer_scope.rs::super_import_wrapper_*` pin the two poles |
| S109-8 | **Stdlib-compile CI blindness** — stdlib self-tests are not in `cargo nextest` (Stdlib-separation is correct for `tests/`, but no paired conformance gate exists), so a compiler regression that breaks stdlib compilation/importability ships with zero signal (27 `num.bits` self-tests were failing invisibly) | HIGH (gate gap) | Nothing in the suite imports the stdlib module surface; the failure lives outside every test binary | FIXME 0605 (`/testing`, S110): stdlib-compile smoke gate via `use_workspace_stdlib_for_stdlib_conformance_only()`, enumerating every top-level stdlib module; self-test execution gate as sized follow-on |

---

Historical baseline risk assessment below (ring-era; surviving load-bearing
risks: RC non-locality, batch/REPL parity, performance-regression
invisibility, error-message quality, Risk 11 FFI corruption).

Risk assessment for quality assurance in the Cranelisp reimplementation. Based on analysis of:
- 591 prototype tests (502 integration + 57 RC + 14 trace + 9 run-tests + 9 platform)
- 10 ignored tests, 2 known-issue-documenting tests
- 16 spec sections, architecture docs, KNOWN_ISSUES.md
- The 7-crate architecture and ring model

## Risk Summary

| # | Risk | Severity | Ring | Mitigation |
|---|---|---|---|---|
| 1 | RC correctness is non-local | **HIGH** | 1–4 | Dedicated RC test harness from Ring 1; every later ring re-runs RC suite |
| 2 | Batch/REPL parity gap | **HIGH** | 0–4 | Single `compile_unit()` is architectural; /qa validates with dual-mode tests |
| 3 | Test catalog portability | **MEDIUM-HIGH** | 0–4 | ~90% of 591 tests are spec-validation; ~10% are implementation-specific |
| 4 | Macro pipeline testability gap | **MEDIUM-HIGH** | 3 | No macros until Ring 3; /qa must test Rings 0–2 without prelude macros |
| 5 | Module system combinatorial explosion | **MEDIUM** | 2 | 35 module tests cover basics; cross-module trait/constrained-poly under-tested |
| 6 | `process::exit(1)` kills test harness | **MEDIUM** | 0+ | Redesign panic handler; 10 ignored tests depend on it |
| 7 | E2E transcript tests are brittle | **MEDIUM** | 4 | Only 4 E2E pairs; output format changes break them |
| 8 | Performance regression invisible | **MEDIUM** | 0–4 | No perf baselines yet; prototype runs ~2min for 978 tests |
| 9 | REPL slash command coverage thin | **LOW-MEDIUM** | 4 | 8 of 16 commands tested; rest deferred to /repl experience suite |
| 10 | Error message quality untested | **LOW-MEDIUM** | 0–4 | Only ~20 error tests; no golden-master error output tests |
| 11 | Slow-accumulating FFI/platform-ABI memory corruption | **HIGH** | (post-ring) | Sustained-repetition crossings + link-then-RUN-under-load + checking allocator (ASAN/heap-header debug-assert) + JIT/link callback parity. DEF-6 root cause. |

## Detailed Analysis

### Risk 1: RC Correctness is Non-Local (HIGH)

Reference counting interacts with every language feature. The prototype's 57 RC tests cover phases 2D–2F and step 11, but every new feature added in Rings 2–4 (traits, modules, macros, IO) can introduce RC bugs. The prototype discovered this the hard way — closures, ADT drop glue, vec COW, and match scrutinee dec were each separate debugging campaigns.

**Impact**: Memory leaks or use-after-free in any ring. RC bugs are silent (no immediate crash) and accumulate.

**Mitigation**:
- Ring 1 establishes the RC test harness with `CRANELISP_RC_TRACE=1` validation.
- Every subsequent ring adds RC-aware tests for its features (e.g., Ring 2 must test trait dispatch with heap-typed args).
- The RC test suite runs serially (`--test-threads=1`) and is never skipped.
- `/backend` owns RC correctness; `/qa` validates it via black-box allocation tracking.

### Risk 2: Batch/REPL Parity Gap (HIGH)

The prototype's worst structural debt was dual batch/REPL pipelines. The architecture addresses this with `compile_unit()` + `CompileMode`, but parity requires active validation. The prototype had 116+ REPL-specific tests because the REPL diverged from batch.

**Impact**: A feature works in batch but fails in the REPL (or vice versa). Users experience this as "it works in a file but not at the prompt."

**Mitigation**:
- Every integration test that validates language behavior runs in *both* batch and REPL modes.
- `/qa` maintains a `compile_and_eval()` helper that tests both paths and asserts identical results.
- Ring 0 wires the batch pipeline first; REPL mode is validated as soon as the pipeline exists.
- The `CompileMode::Interactive` path gets its own test coverage from Ring 0.

### Risk 3: Test Catalog Portability (MEDIUM-HIGH)

Of the 591 prototype tests, approximately 90% validate observable language behavior (spec-validation — directly portable). Approximately 10% test internal implementation details.

**Impact**: Implementation-specific tests can't be ported 1:1; some will need rewriting against the new API.

**Breakdown by portability**:
- **Directly portable** (~530): tests that compile source, run, and check output. Same source, same expected value.
- **Needs adaptation** (~40): tests that use prototype-specific types (`FnSlot`, `GotReference`, `CompiledModule`, `ReplSession`) or internal APIs.
- **Rewrite** (~20): tests tightly coupled to prototype internals (cache file structure, GOT layout, JIT details).

**Mitigation**:
- Portable tests are ported verbatim into `tests/` for each ring.
- Adaptation tests are rewritten against the new API when the relevant ring is implemented.
- No test is silently dropped — every prototype test gets a disposition.

### Risk 4: Macro Pipeline Testability Gap (MEDIUM-HIGH)

Rings 0–2 have no macros. The prototype's `compile_and_run()` helper loads the prelude (macros included). The reimplementation's Rings 0–2 must use `compile_and_run_simple()` equivalents.

**Impact**: Tests that use prelude macros (`list`, `vec`, `do`, `bind!`, `cond`, `case`, `->`, `->>`, `str`, `derive`, `const`, `def`) cannot run until Ring 3.

**Affected tests**: ~180 of 591 use macros (everything calling `compile_and_run` or `compile_and_run_with_macros`, plus all example file tests, all IO tests, all stdlib tests).

**Mitigation**:
- Ring 0–2 tests use only `compile_and_run_simple()` (no macros).
- The test catalog explicitly marks each test with its ring eligibility.
- Ring 3 unblocks the macro-dependent tests; Ring 4 unblocks IO-dependent tests.
- `/qa` maintains a "blocked tests" tracking list that shrinks as rings complete.

### Risk 5: Module System Combinatorial Explosion (MEDIUM)

The prototype has 35 module tests covering imports, visibility, exports, ambiguity, and qualified names. But cross-module interactions with traits, constrained polymorphism, and macros are under-tested. The prototype's KNOWN_ISSUES lists 12 module system limitations.

**Impact**: Module bugs surface late (Ring 2+) and are hard to diagnose because they involve interactions between the type system, symbol tables, and codegen GOT.

**Mitigation**:
- Ring 2 adds cross-module trait dispatch tests (not just import/export mechanics).
- Ring 2 adds cross-module constrained polymorphism tests (specialization in defining vs calling module).
- `/qa` works with `/typecheck` to define module-aware type inference tests.
- The 12 known module limitations each get a test that documents the behavior, with FIXME for those targeted for fixing in the reimplementation.

### Risk 6: `process::exit(1)` Kills Test Harness (MEDIUM)

10 integration tests are `#[ignore]` because `cranelisp_panic` calls `process::exit(1)`, which kills the entire test harness. These cover checked arithmetic overflow, vec out-of-bounds, and match exhaustiveness failure.

**Impact**: Panic-path tests can only run in isolation (`--test-threads=1 --ignored`). CI cannot catch regressions in these paths during normal test runs.

**Mitigation**:
- The reimplementation's `cranelisp_panic` should use `longjmp`/catch mechanism or return an error code rather than `process::exit(1)`.
- `/backend` + `/runtime` design this in Ring 0.
- If the redesign works, all 10 ignored tests become normal tests.
- If the redesign is deferred, `/qa` ensures these tests run in a separate CI step.

### Risk 7: E2E Transcript Tests are Brittle (MEDIUM)

Only 4 E2E transcript pairs exist (`basic_exprs`, `defn_and_call`, `reader_shortcuts`, `slash_help`). These compare exact output text.

**Impact**: E2E tests break on formatting changes, creating false negatives. Or they pass despite semantic regressions if the output accidentally matches.

**Mitigation**:
- E2E tests are Ring 4 (last); formatting stabilizes before they run.
- `/qa` writes E2E tests that match semantic content rather than exact byte-for-byte comparison where possible.
- `/repl` owns the experience test harness, which provides richer assertions than simple transcript comparison.

### Risk 8: Performance Regression Invisible (MEDIUM)

The prototype runs 978 tests in ~2 minutes. No performance baselines exist for individual operations.

**Impact**: The reimplementation could be 5x slower and no test would fail. Users notice at the REPL.

**Mitigation**:
- Ring 0 establishes performance baselines: reader throughput, inference time, codegen time, JIT execution.
- `/repl` defines performance targets (REPL startup <500ms, expression evaluation <100ms).
- Ring 4 adds benchmark tests comparing against prototype baselines.
- Use `criterion` or similar for repeatable benchmarks.

### Risk 9: REPL Slash Command Coverage Thin (LOW-MEDIUM)

8 of 16 slash commands are tested (`/sig`, `/info`, `/type`, `/list`). Untested: `/doc`, `/source`, `/sexp`, `/ast`, `/clif`, `/disasm`, `/time`, `/mem`, `/expand`, `/mod`, `/reload`.

**Mitigation**: `/repl` owns the experience test suite covering all 16 commands. `/qa` adds basic smoke tests in Ring 4.

### Risk 10: Error Message Quality Untested (LOW-MEDIUM)

Only ~20 dedicated error tests exist. No golden-master tests for error formatting.

**Mitigation**: Each ring adds error tests for its features. Error message testing uses substring matching, not exact comparison.

### Risk 11: Slow-Accumulating FFI/Platform-ABI Memory Corruption (HIGH)

The platform/FFI ADT-marshaling boundary is a C-ABI seam between the host
process and platform DLLs. When the two sides disagree on a pointer-base or
layout contract — a payload pointer where a base pointer is expected, a
header-size offset omitted, a struct field reordered — each crossing
overruns adjacent heap metadata by a *fixed small amount*. The damage is
**invisible below a threshold and catastrophic above it**: a few bytes per
crossing accumulate silently until enough chunk headers are clobbered to
trip the allocator's consistency check (glibc `double free or corruption`,
`corrupted size vs. prev_size`, SIGABRT / exit 134). This is a distinct
failure class from RC miscounts (Risks 1) — RC bugs leak or double-free a
*correctly-located* object; this class corrupts the *metadata around*
correctly-RC'd objects, so every RC-driven free hits `rc=0` cleanly right up
to the abort.

**Instance (DEF-6, root-caused S86)**: the `--link` host wiring
(`crates/cranelisp-exe-bundle/src/lib.rs`) handed platforms a **base
pointer** where the contract requires a **payload pointer** — `alloc`
returned `base` instead of `base + HEAP_HEADER_SIZE` (16 bytes). Every
host↔platform-DLL ADT crossing overran the previous chunk's heap metadata by
16 bytes. Invisible below ~40 crossings; glibc-aborts at ~40+. The
`--run`/JIT path (`src/platform.rs`) used the correct `heap_alloc_payload`,
so the bug was **`--link`-ONLY** — a divergence between two separately
hand-rolled host-callback wirings. See the ledger S86 DEF-6 entry for the
full bisection (git history of `tests/plan/ledger.md`, retired S108).

**Impact**: A platform/FFI program that passes every conformance test and
links cleanly aborts in production once a server loop, batch job, or any
sustained workload crosses the corruption threshold. Catastrophic, mode-
specific (`--link` only here), and undetectable by the existing suite.

**Why the 2808-green suite missed it — four detection gaps to record:**

1. **Per-call-correctness, never sustained-repetition.** Every platform test
   asserts a *handful* of crossings return correct values; none loops past
   the ~40-crossing corruption threshold. Slow accumulators are invisible to
   per-call assertions — they need sustained-repetition coverage.
2. **Link-success guarded, run-the-binary-under-load NOT.** The DEF-5 guard
   asserted the binary *links*; nothing *ran* it under load. "Builds/links ≠
   runs," and "runs once ≠ runs N times."
3. **No checking allocator.** A few-bytes-per-crossing overrun under the
   normal system allocator is silent until the threshold. ASAN/valgrind, or a
   heap-header-integrity debug-assert fired on each crossing, would have
   caught it on the *first* crossing.
4. **JIT-vs-link host-callback divergence.** The `--run` (JIT,
   `src/platform.rs`) and `--link` (`cranelisp-exe-bundle`) paths hand-roll
   the host callbacks SEPARATELY; they diverged (one correct, one off-by-16).
   This is a Principle-8/11 mode-divergence risk distinct from the S85
   program-driver unification — S85 unified the *driver*, not the
   *host-callback wiring*.

**Mitigation / diagnostic requirements** (obligations on compiler skills +
`/qa`, per `tests/CLAUDE.md §Diagnostic Requirements`):

- **Sustained-repetition coverage for the platform/FFI marshaling boundary.**
  Every host↔DLL ADT crossing kind (construct/produce AND consume) gets a
  test that drives ≥N crossings — N well above the observed ~40 threshold;
  use 200–2000 — and asserts no abort (exit 0). A handful of crossings is not
  coverage for an accumulator. First such guard is now committed:
  `tests/link.rs::link_repeated_platform_adt_marshal_does_not_corrupt_heap`
  (200× `(Rectangle 3 4)` → platform `area`; generic shapes fixture, no
  exemplar coupling; RED until the off-by-16 is fixed).
- **Link-then-RUN-under-load guards for every platform/`--link` capability**,
  not link-success-only. The `--link` binary must be executed, and executed
  *repeatedly* / under load, not merely produced. Pair every "it links" guard
  with an "it runs N times without aborting" guard.
- **Checking-allocator / heap-header-integrity debug-asserts in the platform
  marshaling path.** A `debug_assert!` that an allocated chunk's header is
  intact after each construct/consume crossing (fires in debug test runs,
  compiled out in release) turns a threshold-delayed abort into a first-
  crossing failure at the exact seam. PLUS a CI recommendation to run the
  platform/`--link` e2e tests under ASAN or valgrind so a fresh overrun is
  caught immediately rather than after N iterations.
- **JIT/link host-callback parity.** The `--run` (JIT) and `--link` host
  callbacks must SHARE the wiring — one source of truth for `alloc`,
  RC-header, and tag callbacks — OR a parity test must assert the two paths
  install byte-identical callbacks, so they cannot diverge again. This is the
  root enabler of DEF-6 and is flagged as an **`/arch`/structural follow-up**:
  the two hand-rolled wirings (`src/platform.rs` vs
  `crates/cranelisp-exe-bundle/src/lib.rs`) are a standing Principle-8/11
  mode-divergence hazard until unified.

## Spec Coverage Gaps

| Spec Section | Tests | Coverage Assessment |
|---|---|---|
| 01-lexical | ~6 | **Thin** — reader shortcuts, whitespace, comments lightly tested |
| 02-grammar | ~7 | **Thin** — parser edge cases (nested brackets, operator precedence) |
| 03-types | ~55 | **Good** — ADTs, type annotations, polymorphism well covered |
| 04-expressions | ~45 | **Good** — let, if, lambda, closure, curry covered |
| 05-definitions | ~15 | **Adequate** — multi-sig covered; defn- visibility needs more |
| 06-pattern-matching | ~20 | **Good** — exhaustiveness, wildcards, var patterns |
| 07-traits | ~45 | **Good** — default methods, derive, HKT, ambiguity |
| 08-modules | ~35 | **Adequate** — import/export/visibility; cross-module interactions thin |
| 09-macros | ~35 | **Good** — quasiquote, multi-clause, bracket destructuring |
| 10-io | ~12 | **Adequate** — pure/bind/do covered; par-bind! light |
| 11-stdlib | ~40 | **Good** — list, vec, seq, map/reduce/filter |
| 12-runtime | ~280 | **Heavy** — RC, cache, REPL, trace dominate; lenient eval good |

Priority gaps to address:
1. **01-lexical** and **02-grammar**: need more parser edge case tests (Ring 0)
2. **08-modules**: need cross-module trait and constrained-poly tests (Ring 2)
3. **Error paths**: need systematic error message tests per ring
4. **10-io**: par-bind! and platform interaction tests (Ring 4)
