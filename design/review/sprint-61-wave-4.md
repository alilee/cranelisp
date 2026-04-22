# Sprint 61 Wave 4 — /review Report

**Reviewer**: /review
**Date**: 2026-04-22
**Verdict**: **PASS**
**Scope**: Slice 4 — `21-hello-io.cl` intermittent-exit defect closure.
H(4-1'') coordinated trampoline/closure-drop-glue defect, fixed
backend-only via new `emit_capture_return_inc` helper in
`crates/cranelisp-backend/src/compiler/control_flow.rs`. Evidence-gated
discipline (reduction → evidence capture → /arch hypothesis ruling →
/backend fix → /qa integration test). Simpler than Wave 3's three-cycle
race closure — single deterministic defect, backend-local fix, no
concurrency dimension.

## Summary

- Blockers: 0
- Importants: 0
- Suggestions: 3

All four required read-only audits passed. Diff confirms zero edits
in `crates/cranelisp-runtime/src/io.rs` since SHA `776a6cf` (per
/arch §4d mandatory condition "do NOT weaken `consume_closure`"). Fix
is interface-internal: no `cranelisp-types` change, no
`design/arch/interfaces.md` change, no boundary-type surface. The
helper is strictly additive alongside `protect_return_value` —
pre-existing scope-stack discipline for all other return shapes is
preserved. Unit test (owned by /backend, lives alongside other
closure/lambda backend tests in `lib.rs`), integration test (owned by
/qa, new file), and normative rule doc (`ring2-rc.md §5.6`) all
present and internally consistent. Wave 4 ships.

## Blockers (B)

None.

## Importants (I)

None.

## Suggestions (S)

1. **`crates/cranelisp-backend/src/compiler/control_flow.rs:950` —
   `emit_capture_return_inc` does a `.cloned()` on
   `variable_types.get(name)` where a borrow would suffice.**

   The helper reads `ty` once and immediately passes `&ty` to
   `HeapCategory::classify`. There is no further use of the owned
   value and no need for ownership. Callsite `HeapCategory::classify(&ty, ...)`
   would work identically with `.get(name)` returning `Option<&Type>`
   and matching on the reference. The clone is cheap (Type is a small
   enum) but the idiom in the rest of `control_flow.rs` is borrow-by-
   default; this is the one helper that clones. Micro-consistency note;
   non-blocking. Owning skill: `/backend`.

2. **`tests/sprint61_io_closure_regression.rs:62-67` — `binary_path()`
   hard-codes `target/debug/cranelisp` without a feature gate for
   release builds.**

   If a contributor runs `cargo nextest run --release -p cranelisp
   --test sprint61_io_closure_regression`, the test panics with "binary
   not found at target/debug/cranelisp" because the binary only exists
   under `target/release/`. The existing sprint61 IO observability
   tests use the same pattern (per /qa's matching of convention), so
   this is harness-wide and not unique to Slice 4. Non-blocking because
   the project tests debug builds exclusively (per `CLAUDE.md §Testing`),
   but a future release-path harness run would trip here. Candidate
   follow-up: a helper in `tests/helpers/mod.rs` that inspects
   `cfg!(debug_assertions)` and picks the right subdir. Owning skill:
   `/qa` at Wave 5 `tests/helpers/` refresh.

3. **`design/backend/ring2-rc.md §5.6` — "Implementation" sub-section
   does not cross-reference the `// SAFETY:` or invariant wording in
   `emit_capture_return_inc`'s docstring.**

   The two sources of truth (design doc §5.6 + helper docstring at
   `control_flow.rs:911-948`) say the same thing in slightly different
   words. The helper docstring is thorough and includes a 3-point
   numbered invariant; §5.6 summarises the same content in prose with
   different framing ("Why `protect_return_value` does not cover
   this"). They are not contradictory, but a future reader tracking
   down the rule must read both to get the full picture. A one-line
   "see helper docstring at `control_flow.rs::emit_capture_return_inc`
   for the normative invariant wording" pointer in §5.6 would tie them
   together without duplicating content. Non-blocking, documentation
   drag only. Owning skill: `/backend`.

## Design-adherence audit

/arch §4d APPROVE WITH REVISIONS mandated four conditions; each is
satisfied:

1. **H(4-1'') ruling adopted** — fix is backend-side inc-on-return for
   captured heap values, not runtime-side trampoline edits. Confirmed
   by diff: `crates/cranelisp-backend/src/compiler/control_flow.rs` is
   the sole source edit; `crates/cranelisp-runtime/src/io.rs` is
   untouched (`git diff 776a6cf -- crates/cranelisp-runtime/src/io.rs`
   returns empty, per task-brief required audit).

2. **Preferred site — explicit helper in `control_flow.rs`, not gate
   change in `protect_return_value`** — /backend chose the exact
   /arch-preferred implementation shape. `emit_capture_return_inc`
   lives above `compile_lambda_body`; `protect_return_value`'s
   `scope_stack` discipline is unchanged. Pre-commit sanity: grep
   confirms single definition + single call site
   (`control_flow.rs:950` definition, `control_flow.rs:1111` call
   between `protect_return_value` and `pop_scope_with_cleanup`).

3. **Ring2-rc.md §5.6 additive rule** — new subsection sibling to §5.5
   "Rules that modify scope cleanup behavior" rather than an edit
   inside §5.5. Keeps §5.5's three bullets (unmoved_heap_vars,
   borrowed_vars, last-use analysis) structurally intact. The new
   rule's framing ("mirror case: the *return value* must be inc'd
   when it originates outside the scope frame") is accurate — §5.5
   governs cleanup-on-scope-exit, §5.6 governs inc-on-return. Both
   stem from the same underlying discipline (scope_stack tracks owning
   references only), but act on different pipeline points.

4. **Integration test uses the 7-line minimum repro, not the 8-test
   reduced main** — /qa followed /arch §4d test-authoring
   recommendation exactly. The minimum repro is strictly stronger as
   a regression surface (smaller, deterministic, no platform IO
   dependency); the 11-test `21-hello-io.cl` is the E2E gate via
   `examples_run::every_example_file_runs_under_examples_prelude`,
   which passes implicitly.

**Sketch comparison**: §4e "Sketch comparison" notes the sketch's
trampoline design predates `current_is_fresh` and has a different
failure mode (O(N) RC leak on long bind chains). The reimplementation
adopted `current_is_fresh` to close that leak, and Slice 4 discovered
the new-to-this-design capture-return case that the sketch's
top-level `consume_io_tree` sidesteps by never dec'ing captures
inline. This is a legitimate "divergence + new rule" — documented at
§4e, pointed at from §5.6.

**Evidence-gated discipline**: clean. Reduction narrative (§"Reduction
narrative") documents the 4 removals that each restore clean runs,
identifying the necessary conjunction (user-defined fn constructs
`(bind x (fn [_] captured-IO))` called inside an outer bind
continuation). Hypothesis weighting pre-arch: 0.85 H(4-1) + 0.15
H(4-1') + 0.0 H(4-2)/H(4-3). /arch re-cast as H(4-1'') (composed, not
alternative) at §4d; the two arms were observably indistinguishable
at the trace level, fix surface coordinated. Post-fix dump at
`21-hello-io-post-fix-776a6cf.log` shows balanced trampoline
sequence.

## Boundary-hygiene audit

- `git diff 776a6cf -- crates/cranelisp-runtime/src/io.rs` → empty.
  io.rs untouched per /arch §4d. ✓
- `rg 'FIXME' crates/cranelisp-runtime/src/io.rs` → single match at
  line 173 (pre-existing `FIXME(/backend): consider threading
  SchedulingClass`, from Wave 1 Slice 0). No new FIXMEs from Wave 4. ✓
- `rg 'emit_capture_return_inc' crates/cranelisp-backend/` → 2
  source matches (definition + call site) + 3 doc-comment matches in
  `lib.rs` test. Single helper, single call site per /arch §4d. ✓
- `rg '#\[ignore\]' tests/sprint61_io_closure_regression.rs` → 0. ✓
- No boundary-type changes in `crates/cranelisp-types`; no
  `design/arch/interfaces.md` edits in diff.
- The fix modifies only `compile_lambda_body`'s return path. All
  non-lambda returns, all lambda returns where body is not a bare
  `Expr::Var` naming a capture, and all returns where the named
  capture is non-heap, route through the unchanged
  `protect_return_value` → `pop_scope_with_cleanup` sequence. The
  surface of programs where behaviour changes is tightly bounded.

## The fix site

The helper's gate correctness (per task-brief dimension "is
`emit_capture_return_inc` the right place? Does it gate correctly on
'body is captured heap var'?"):

- `control_flow.rs:951-953` — `let Expr::Var { name, .. } = body else
  { return; }` — correctly rejects all non-Var return shapes
  (literals, Apply, Let-returns, Match-arms, If-branches). Non-Var
  returns cannot be "a captured heap variable" by construction.
- `control_flow.rs:954-956` — `if !self.captured_vars.contains(name)
  { return; }` — correctly rejects Vars that name scope-local
  bindings, parameters, or globals. Captures are precisely those
  names in `captured_vars`.
- `control_flow.rs:957-960` — `let Some(ty) = self.variable_types
  .get(name).cloned() else { return; }` — defensive type lookup.
  `variable_types` is seeded for captures by `compile_lambda_body` at
  capture-binding time; missing entry is a codegen invariant
  violation (would be an `unreachable!` candidate), but the early
  return fails safely rather than generating a wrong inc.
- `control_flow.rs:961-968` — `HeapCategory::classify` + match on
  `AlwaysHeap` (emit `rc_inc`) / `Mixed` (emit `rc_inc_guarded`) /
  `NeverHeap` (no-op). Matches the existing idiom used in
  `compiler/apply.rs:95`, `compiler/mod.rs:824` etc. Non-heap
  captures correctly skip the inc (no dec will fire on them in the
  drop-glue either, so nothing to balance).

**Correctness relative to /arch §4d ruling "the body DOES know, at
codegen time, when its return expression is a bare `Var(b)` where
`b` is in `captured_vars`"**: helper's gate is precisely this
condition, extended with heap-classification to no-op on non-heap
captures (which /arch §4d also specified: "inc the return value when
the inferred return type is heap-typed AND the returned expression
resolves to a captured variable"). Exact match.

## Integration with existing semantics

**Does the fix preserve `protect_return_value` scope_stack discipline
for non-capture returns?** Yes. Diff confirms `protect_return_value`'s
body (`crates/cranelisp-backend/src/compiler/mod.rs`) is unchanged.
The new helper runs AFTER `protect_return_value` and BEFORE
`pop_scope_with_cleanup`; it fires on a strictly narrower condition
(body-is-captured-heap-Var) than `protect_return_value`'s gate
(scope_stack has heap-typed cleanup targets). The two conditions are
non-overlapping in practice: captures are by definition not in
`scope_stack`, so if the body returns a capture, `protect_return_value`
emits no inc regardless of `scope_stack`'s state. The helper's inc
therefore never stacks with a prior inc on the same value.

**Does the fix match the intent (balance out the dec via matching
inc)?** Yes. The closure's drop-glue built by `build_closure_drop_glue`
dec's each heap capture when the closure is consumed
(`consume_closure` in `io.rs:345-356`, also fresh-closure call sites
elsewhere). For the `(fn [_] b)` shape with heap capture `b`, the
drop-glue dec runs exactly once after the body returns. The new inc
runs exactly once inside the body before return. The returned pointer
therefore arrives at the caller with its rc unchanged — which is the
correct "ownership transfer to caller" semantics.

**`current_is_fresh` / `consume_closure` invariants preserved?** Yes.
The runtime-side protocol (a fresh closure owns its captures; dec'ing
the closure releases them; `current_is_fresh=true` signals that the
trampoline may dec without caller coordination) is exactly as
specified in `ring2-rc.md §3.5`. The backend now ensures that when a
capture flows OUT of the closure via its return value, the body
leaves the caller's reference at its original rc by emitting the
inc. No protocol change; only a missing producer-side inc is added.

## Rule-documentation audit

`design/backend/ring2-rc.md §5.6`:

- **Structural placement**: correctly sibling to §5.5 rather than a
  bullet within §5.5. §5.5's three rules govern scope_stack cleanup
  emission; §5.6 governs return-value inc emission. Different pipeline
  phase, related discipline — sibling framing is accurate.
- **"Why `protect_return_value` does not cover this case"
  paragraph**: accurately describes the
  `has_cleanup_targets`/`scope_stack` gate. Matches the source at
  `compiler/mod.rs::protect_return_value`.
- **"Why captures are consumed after return" paragraph**: accurately
  describes `consume_closure`'s role and correctly names
  `build_closure_drop_glue` as the dec-emitter.
- **Implementation sub-section**: accurately names the helper, its
  location, its invocation point, and the three gate conditions.
  Matches the diff.
- **Regression history sub-section**: cites the minimum repro by
  path, the /arch verdict by path + anchor, and both the unit test
  and integration test by name.
- **No FIXME-to-resolver**: the rule is LANDED, not proposed. The
  implementation reference is terminal, not a TODO.

## Unit test placement trade-off

`crates/cranelisp-backend/src/lib.rs` houses the new
`lambda_return_captured_heap_var_emits_inc` unit test alongside the
existing `test_compile_lambda_closure`. /backend's explanation
(`lib.rs:1655-1659`): `test_compile_and_run` and `TestCheckResult`
scaffolding is private to `lib.rs`; a sibling mod in `control_flow.rs`
would require duplicating the pipeline bridge.

**Assessment**: acceptable.

- The three existing closure/lambda backend tests all live in
  `lib.rs`, so placement matches convention.
- The shared test infrastructure (`test_compile_and_run`,
  `empty_check`, `empty_tables`) is genuinely deep — moving it to a
  helpers module would be a /backend-local refactor out of scope for
  Wave 4.
- The test's docstring explicitly documents the placement rationale
  so future readers don't hunt for a missing `control_flow.rs #[cfg(test)]
  mod`.
- Per `memory/feedback_unit_tests_with_dev.md`, unit tests belong to
  the implementing skill and live inside the owning crate — that's
  satisfied (backend crate, backend skill). The exact file within the
  crate is a secondary concern.

Suggestion: log a /backend-local follow-up to extract
`test_compile_and_run` into a `cranelisp-backend::testutil` module so
future backend-internal tests can colocate with the code they test.
Not a Wave 4 action.

## Integration test shape

`tests/sprint61_io_closure_regression.rs` — 2 tests:

- `io_trampoline_then_combinator_does_not_double_free_capture`:
  exercises the 7-line minimum repro via subprocess `--run`, asserts
  exit=51 AND absence of each pre-fix surface exit (101/133/201/134
  individually) AND absence of "panicked" / "unknown IO tag" in
  stderr. Strong pointed discriminators — if a future regression
  reopens the bug, the failure message names the specific pre-fix
  signature that regressed.
- `io_trampoline_then_combinator_trace_shows_clean_trampoline_exit`:
  same repro under `CRANELISP_IO_TRACE=1`, asserts
  `TrampolineEnter`, `TrampolineExit`, and `result=51` all present
  in stderr. Stronger observable evidence than exit-code-alone —
  proves the trampoline reached its normal exit path (pre-fix the
  process aborted between the two events).

**Robustness**: both tests use fresh `tempfile::tempdir()` per run
(per /qa `tests/CLAUDE.md §Fresh-TempDir-per-test`). Both scope
`CRANELISP_CACHE_DIR` to the TempDir to avoid cache-collision under
parallel nextest. Both use `env_remove("CRANELISP_IO_TRACE")` before
conditionally setting it so stray environment state doesn't leak
between tests. 5/5 consecutive passes reported by /qa.

**Missing-case check**: the 2 tests together cover the exit-code axis
(numeric correctness) and the trace-observability axis
(process-completion shape). No obvious missing axis within the
minimum-repro scope. Extending to cover e.g. `Vec`-captured-and-
returned or `ADT`-captured-and-returned would broaden the invariant
(§5.6 is about heap-typed captures generally, not just IO), but that
scope extension is out of Wave 4's remit — the unit test at
`lambda_return_captured_heap_var_emits_inc` covers a String-captured
case (non-IO), demonstrating the rule is not IO-specific, and that
combined with the IO-specific integration test exercises two
representative heap types. Future-sprint follow-up for Vec/ADT cases
is plausible but not required.

## `examples_run.rs` accepted-exit tightening

The pre-change table accepted `[101, 133, 141]` for `21-hello-io.cl`.
Post-change: `[243]`, the spec-correct `499 & 0xFF` per the updated
comment. The investigation doc §4e "Integration acceptance" records
/backend's analysis:

> `examples_run::every_example_file_runs_under_examples_prelude`
> passes after tightening the 21-hello-io accepted-exit list from
> `[101, 133, 141]` to `[243]` (the direct-invocation value 499 &
> 0xFF; 21 does not read stdin, so 133/141 were crash artefacts not
> harness artefacts).

**Assessment**: rationale sound.

- `21-hello-io.cl` does NOT call `read-line`/`read-char` (the comment
  above the entry says "prints but does not read stdin"). Under
  `Stdio::null()` harness stdin, a non-reading program cannot
  legitimately exit 133 (SIGTRAP from `read-line` on closed fd) or
  141 (SIGPIPE on stdout pipe — the harness doesn't close stdout
  between subprocess start and its own process end).
- Exit 101 is Rust panic signature; correct for a panicking program,
  WRONG for a well-formed one.
- Exit 243 = 499 mod 256. The program returns 499 (= Part 1-6
  pass-count 457 + Part 7 pass-count 42), which truncates to 243 at
  the i32→u8 process-exit boundary. Spec-correct.
- Pre-fix, the "accepted exits" list was tolerating the bug's
  symptoms. Tightening to the spec-correct value is exactly what
  Sprint 60's lesson "getting things working by not doing them isn't
  getting things working" demands.
- The adjacent `24-io-echo.cl` entry retains `[20, 133, 141]` because
  it DOES read stdin — the accept-list is legitimately broader.
  Shows the reviewer that the tightening was considered per-entry
  and not a blanket sweep.

## Evidence-dump quality

`tests/sprint61/race-evidence/` carries 4 dump files + 1 README for
Slice 4:

- `21-hello-io-failing-776a6cf.log` — 8-test reduced variant, no
  platform IO, shows the `cont`-pointer-reused-as-IO-node signature.
- `21-hello-io-failing-min-776a6cf.log` — 7-line minimum repro,
  panic at io.rs:326 with `unknown IO tag 6578533`.
- `21-hello-io-passing-776a6cf.log` — 5-test reduced variant (no
  HOF), clean `TrampolineExit result=175`.
- `21-hello-io-post-fix-776a6cf.log` — post-fix minimum repro,
  balanced trampoline sequence ending `TrampolineExit result=51`.
- `21-hello-io-README.md` — frozen explanation of harness, exit-code
  distribution (73/13/13%), divergence signature table,
  reproduction recipe, scope ("do not overwrite at step 4e").

**Quality**: sufficient for future debugging. The README's
reproduction recipe is copy-pasteable (`cat > __bug.cl << 'EOF' ...`),
the dump files are frozen at the captured SHA, and the post-fix dump
provides an explicit green-baseline shape. If this bug ever regresses,
a future investigator has (a) the failing trace shapes, (b) the
passing trace shapes, (c) the divergence-signature table pinning the
single relevant variable, (d) the fix shape via the ring2-rc.md §5.6
pointer. This is the durable record /qa's reproduction protocol
targets.

## Review dimensions — all 10 checked

| # | Dimension | Status |
|---|---|---|
| 1 | Design adherence (/arch §4d four conditions) | all four met |
| 2 | Boundary hygiene (io.rs untouched, no cranelisp-types change) | verified by diff |
| 3 | Fix site correctness (gate on captured-heap-Var) | verified by code reading |
| 4 | `protect_return_value` discipline preserved | verified by diff (unchanged) |
| 5 | Runtime semantics (`consume_closure`, `current_is_fresh`) | verified no change |
| 6 | ring2-rc.md §5.6 structural soundness | sibling to §5.5, additive |
| 7 | Unit test placement (`lib.rs` vs `control_flow.rs`) | acceptable with rationale |
| 8 | Integration test shape (2 tests, covers exit + trace axes) | robust |
| 9 | `examples_run.rs` accepted-exit tightening to `[243]` | spec-correct |
| 10 | Evidence dump quality | sufficient for future debugging |

## Recommendations to /sprint

1. **Accept Wave 4 submission as PASS**. Zero Blockers, zero
   Importants, three minor Suggestions none of which gate commit.

2. **Wave 4 commit readiness: GO**. All changes sit in working tree
   (per pre-commit-gate protocol observed in Wave 3). Commit message
   should cite: H(4-1'') /arch ruling; `emit_capture_return_inc`
   helper; ring2-rc.md §5.6 new rule; four baseline-ledger entries
   resolved; /qa integration test + /backend unit test.

3. **Log S1-S3 for /backend + /qa follow-up**. None are sprint-
   blocking; fold into Wave 5 if there's slack, or defer to S62.

4. **Baseline ledger verification at close**: /qa has moved 4
   entries (S60 carry + 3 Wave-1 Slice-4-dependent) to the "Sprint
   61 Wave 4 — Slice 4" subsection. Per `tests/plan/baseline.md
   §"Close-time Verification Protocol" item 3`, these must be
   confirmed pass-green at close time, not just moved. /sprint
   re-runs the full suite as part of sprint-close audit.

5. **Wave 5 can open**. Slice 5 (methodology residual + showcase)
   is gated on Wave 4 close per `sprints/SPRINT.md §Wave ordering
   rationale` ("Wave 5 runs only after all defects closed"). Wave 4
   closes cleanly; the 5 `d6_exemplar_*`/`wave6_demo_repros` carries
   and H6 residue remain but are ledgered and targeted at S62, not
   blockers for Wave 5 showcase + close work.

Wave 4 closes Slice 4 cleanly on a single evidence-gated hypothesis
cycle. The fix is minimal (71 LOC helper + call site, strictly
additive, no gate change to existing machinery) and precisely
targeted (a three-condition gate: body-is-Var, name-is-capture,
type-is-heap). The rule is documented normatively in ring2-rc.md
§5.6 as a sibling of §5.5 rather than a retrofit to it. The
integration test exercises the minimum repro at Layer 4, the unit
test exercises a representative heap type (String) at Layer 1, and
the accepted-exit tightening in `examples_run.rs` converts the
bug's former tolerance into a regression surface. Ship Wave 4.

End of review.
