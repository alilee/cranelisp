# Sprint 57 Wave 0 Review — Super-Import Implementation

**Sprint**: 57 Wave 0
**Date**: 2026-04-18
**Reviewer**: `/review`
**Scope**: Super-import rewrite across `/frontend`, `/int`, `/spec`, `/qa`, `/arch` (Decision 30, arbitration doc).

## Verdict

**PASS with Suggestions.** The Wave 0 surface is small and cleanly executed. No Blockers, no Importants — spec §8.3.7 contract is correctly implemented at the single site dictated by the arbitration, the signature change is well-documented, and coverage (5 tests across frontend + integration) exercises both positive and negative paths.

## Findings

### Blocker findings

None.

Answers to the five Blocker-level questions, with evidence:

1. **Does the `/frontend` rewrite correctly implement the spec §8.3.7 contract?** **Yes.** `crates/cranelisp-frontend/src/module_extract.rs:176-192` triggers exclusively on `raw_module_path == "super"` (not `starts_with("super.")`, not substring), uses `rsplit_once('.')` to strip the last component (matches spec §8.3.7 wording: "stripping the last component from the current module's full path"), and returns `CranelispError::ModuleError` when the parent is absent. The error message ("`'super' import used in top-level module '{}' (no parent)`") mirrors the sketch template and names the offending module. The rewrite runs inside `parse_import_entries`, which is on the one code path that constructs `ImportSpec` — the "no `super` post-frontend" invariant from the arbitration doc is structurally enforceable.

2. **Does the public signature change preserve reader hygiene?** **Yes.** `parse_import_sexp(sexp: &Sexp, containing_module: &ModuleFullPath)` names the parameter unambiguously (not `module_path`, not `current`, not `context`), and the `/// containing_module is the path of the module whose source contains this import form` doc-comment at lines 382-386 eliminates any caller confusion. The three `classify_form` call sites in `src/worker.rs` (lines 678, 796, 930) all pass `module` — the `ModuleFullPath` of the module being processed by the worker — which is precisely what the contract requires.

3. **Does the worker fix pass the correct module-path variable at every `classify_form` call site?** **Yes.** All three call sites thread the same variable name (`module` at 678 and 930, `containing_module` at 796 inside `separate_macros`). `separate_macros` is called from `process_module_forms` at line 750 with `module` as its argument — the chain is uniform.

4. **Do the unit + integration tests actually exercise both success and error paths?** **Yes, non-trivially.** Frontend unit tests: `test_import_super_rewrites_to_parent` (math.test → math), `test_import_super_rewrites_nested_parent` (app.handler.test → app.handler — exercises multi-dot path), `test_import_super_at_root_errors` (asserts error, asserts message substrings). Integration tests: `super_import_rewrites_to_parent_end_to_end` (full compile + trampoline + post-hoc symbol-table inspection to prove no lingering "super" literal), `super_import_at_root_is_rejected_neg` (batch_run_file + message substring check). The integration positive test also explicitly walks the child's symbol table and asserts `src_mod != "super"` for every `ModuleEntry::Import` — this is the post-frontend invariant from the arbitration doc made executable. That is not a smoke test; it is a structural assertion.

5. **Are there any cases where `super` at a non-root module silently escapes the rewrite?** **No.** The rewrite checks `raw_module_path == "super"` only (not `starts_with`). `super.foo` would be a qualified symbol parsed as a single Symbol with string `"super.foo"` — the rewrite does not fire, and the downstream resolver treats `super.foo` as an ordinary module-path lookup that will fail to resolve (correct — spec §8.3.7 only defines the bare `super` shorthand). The aliased form `(import [(super alias) [*]])` flows through `parse_module_spec` which extracts `"super"` as the module string with `Some("alias")` as the alias — `parse_import_entries` then rewrites the module string to the parent while preserving the alias. Correct.

### Important findings

None.

Answers to the five Important-level questions:

1. **Is `parse_import_sexp`'s new signature documented adequately?** **Yes.** Doc-comment at lines 382-386 of `module_extract.rs` explicitly states the parameter's role AND the post-condition ("no `ImportSpec.module_path` contains the literal string `super`"). The private helpers `parse_import` (line 128) and `parse_import_entries` (line 162) carry identical documentation — the invariant is visible at every layer.

2. **Are the three frontend unit tests + two integration tests the right coverage?** Coverage is sufficient for Wave 0's contract:
   - Positive rewrite, one-dot parent (math.test → math) — covered.
   - Positive rewrite, multi-dot parent (app.handler.test → app.handler) — covered.
   - Negative root-module error — covered by frontend unit AND integration.
   - End-to-end invariant (no literal "super" in resolved symbol table) — covered by integration.
   Gaps are minor and belong in the Suggestion tier (see S-1, S-2 below).

3. **Are the FIXMEs filed in clean "owning-skill remove after resolve" shape?** **Yes, with one cosmetic imprecision.** The FIXME at `module_extract.rs:120-125` is clear, addresses the correct owner (`/frontend`), and explains why it is non-blocking. See S-4 below for the line-number imprecision.

4. **Does `/qa`'s positive integration test structure document the "why" well enough that a future developer doesn't naively restructure into a deadlock?** **Yes.** `tests/modules.rs:431-433` explicitly calls out the pattern: *"The child is used as the entry module so the parent does NOT import or qualify-ref into the child — this avoids the §8.3.7 known mutual-import deadlock while still exercising the super→parent rewrite end-to-end."* Cross-ref to Decision 30 would be a nice-to-have but is not essential — the comment explains the constraint locally.

5. **Is `design/arch/super-import-arbitration.md` still consistent after `/int`'s footnote correction and `/spec`'s §8.3.7 renumber?** **Mostly.** The arbitration doc's §"Error contract (spec §8.3.7)" and §"Implementation site" still cite §8.3.7 — correct post-renumber. However §"Consequences" first bullet refers to `test_import_super` (the pre-Wave-0 test name) which is now renamed to `test_import_super_rewrites_to_parent`. Minor currency issue. See S-5 below.

### Suggestion findings

**S-1. Qualified-reference (`super.foo`) is a documented non-goal — consider a test asserting that.**
- **Location**: `crates/cranelisp-frontend/src/module_extract.rs::tests`
- **Issue**: The rewrite only fires on bare `super`. Whether `(import [super.foo [bar]])` resolves at all is not asserted; spec §8.3.7 is silent; the sketch never supported it. A negative test asserting either "super.foo does not rewrite" or "super.foo produces an unresolved-module error with a span" would pin the behaviour for future refactors.
- **Proposed fix**: Add `test_import_super_dot_form_not_rewritten` (asserts module_path stays `"super.foo"` post-extraction, OR that the downstream module-resolution layer produces a clean error).
- **Owner**: `/qa` (integration) or `/frontend` (unit — cheaper).
- **Severity**: Low. Not blocking; adds a pinning assertion.

**S-2. No test at 4-level nesting depth (`a.b.c.d`).**
- **Location**: `crates/cranelisp-frontend/src/module_extract.rs::tests`
- **Issue**: The two positive tests cover 2-dot (`math.test` → `math`) and 3-dot (`app.handler.test` → `app.handler`). `rsplit_once('.')` is trivially correct at any depth, but a 4-level test would match the nesting depth most likely to appear in a real exemplar/stdlib layout.
- **Proposed fix**: Add a 4-or-more-dot case to `test_import_super_rewrites_nested_parent` or as a sibling.
- **Owner**: `/frontend` (unit test).
- **Severity**: Low. The implementation is obviously general; a sanity test is insurance, not necessity.

**S-3. Cross-reference to Decision 30 inside the integration test comment.**
- **Location**: `tests/modules.rs:430-433`
- **Issue**: The positive integration test comment explains the no-mutual-import constraint but does not cite `design/arch/CLAUDE.md` Decision 30 or `concurrent-pipeline.md §7.1 item 1`. A future developer reading this test might restructure parent→child imports and hit the deadlock without understanding the shape of the constraint.
- **Proposed fix**: Append `" — see design/arch/CLAUDE.md Decision 30 for the underlying scheduler constraint."` to the existing block comment.
- **Owner**: `/qa`.
- **Severity**: Low. The comment already explains *what*; the cross-ref explains *why at the architectural level*.

**S-4. FIXME in `module_extract.rs` cites stale line numbers.**
- **Location**: `crates/cranelisp-frontend/src/module_extract.rs:120-125`
- **Issue**: The FIXME says "Seven code-comment citations need updating (lines 124, 155, 169, 378, 593, 612, 625)". The actual current line numbers for §8.3.6 citations appear to be 130 (parse_import doc), 162 (parse_import_entries doc), 384 (parse_import_sexp doc), and test `// spec:` comments at lines 599, 618, 631. The line numbers in the FIXME were already stale before Wave 0 closed (the FIXME was added in the same commit that shifted them).
- **Proposed fix**: When `/frontend` picks this FIXME up, don't trust the cited line numbers — `Grep` for `§8.3.6` in the file first.
- **Owner**: `/frontend` (already owns the FIXME; just a note for when it's picked up).
- **Severity**: Cosmetic. The FIXME itself correctly says "pointer resolves unambiguously".

**S-5. Arbitration doc references pre-Wave-0 test name.**
- **Location**: `design/arch/super-import-arbitration.md:62`
- **Issue**: The §"Consequences" bullet says *"`crates/cranelisp-frontend/src/module_extract.rs::test_import_super` inverts"* — the test was renamed during Wave 0 implementation to `test_import_super_rewrites_to_parent`. Also mentions `test_import_super_root_errors` whose actual name is `test_import_super_at_root_errors`.
- **Proposed fix**: Update both names to the actual post-Wave-0 names, or replace with a range citation ("the three `test_import_super_*` tests at `module_extract.rs:604-660`").
- **Owner**: `/arch`.
- **Severity**: Low. The doc is an arbitration record; minor name drift does not affect architectural clarity.

**S-6. Arbitration doc `§8.3.6` references in text body.**
- **Location**: `design/arch/super-import-arbitration.md:17` ("`src/worker.rs:679` primary capture, `src/worker.rs:1065` `handle_import`...")
- **Issue**: Line references in arbitration docs are naturally time-bound; by Wave 2 these will drift. Not a finding against Wave 0 but worth noting that `/arch` should avoid absolute line refs in long-lived documents or mark them as "as-of sprint X" snapshots.
- **Proposed fix**: Convert to function-name references (`src/worker.rs::classify_form`, `src/worker.rs::handle_import`) on next `/arch` touch.
- **Owner**: `/arch`.
- **Severity**: Cosmetic / process suggestion.

## Checklist walkthrough

Verifying against `design/review/checklist.md`:

- **§1 Error Handling**: The new error path uses `CranelispError::ModuleError` with a span (`mod_span`) and a descriptive message. No `unwrap`, no `expect`, no `panic`. PASS.
- **§2 Code Structure**: `parse_import_entries` grew by ~15 lines for the rewrite; total body is still ~50 lines — well under the 100-line limit. The rewrite is a clearly demarcated `if ... else ...` block with a clear doc-comment. PASS.
- **§3 Naming**: `containing_module: &ModuleFullPath` uses the existing newtype, not bare `&str`. PASS.
- **§5 Single Source of Truth**: The rewrite happens at exactly one site (`parse_import_entries:176`). This is the key architectural property the arbitration selected Option A to achieve — verified present. PASS.
- **§6 Duplication**: No duplication introduced. PASS.
- **§7 Architectural Boundaries**: `ImportSpec` owns the post-rewrite invariant; the frontend enforces it. Cross-crate boundaries unchanged. PASS.
- **§9 Testing**: Unit tests live in `#[cfg(test)] mod tests` alongside the code (frontend); integration tests live in `tests/modules.rs` (`/qa`). Correct ownership split per `memory/feedback_unit_tests_with_dev.md`. PASS.

## Design doc assessment

- **`design/arch/super-import-arbitration.md`**: Comprehensive. Rationale, sketch comparison (the sketch's placement is explicitly compared and the divergence justified), error contract, consequences, ownership. Sketch comparison is substantive — not a "sketch does similar" gloss. **PASS** with S-5/S-6 noted above.
- **`design/arch/CLAUDE.md` Decision 30**: Thorough articulation of the mutual-import deadlock constraint, safe/unsafe patterns enumerated, workaround documented (`discover-tests` + `run-test`), future-work pointer. Decision 30 does the heavy lifting of preventing future re-discovery of the pass-order issue. PASS.
- **`spec/08-modules.md §8.3.7`**: Normative requirement plus non-normative "Known limitation" paragraph. The paragraph is well-written: crisp about the deadlock shape, prescribes implementation freedom ("MAY reject... MUST NOT silently produce a non-terminating compilation"), cross-refs Decision 30 and the test-scaffolding workaround. PASS.
- **`/int`, `/frontend`, `/qa` did not author standalone design docs** — not needed for a two-site code change covered by the arbitration doc. Correct judgement.

## Pre-existing issues noted

`/int` reports four pre-existing clippy errors in their Wave 0 close-out:
- `src/watch.rs:70` — pre-existing clippy error.
- `src/watch.rs:71` — pre-existing clippy error.
- `src/worker.rs:1914` — pre-existing clippy error (×2).

These are outside the Wave 0 code surface and predate this wave. **Ownership**: `/int` owns `src/`. **Disposition**: Wave 2 touches `worker.rs` substantively (G6 codegen-product deletion) and can sweep these in the same pass. NOT fixed in Wave 0 per review scope.

## Gate assessment

The Wave 0 gate criterion (sprint plan `sprints/SPRINT.md:480`):
- ✅ Exemplar `(mod test (import [super [*]]) …)` resolves correctly — proved by `super_import_rewrites_to_parent_end_to_end`.
- ✅ Negative case (super at root) errors with spec-mandated message — proved by `super_import_at_root_is_rejected_neg`.
- ✅ Test count — 2 new integration tests + 3 new frontend unit tests = 5 new tests added this wave.

Wave 0 is cleared for close from the code-review perspective.

## Summary

| Severity | Count |
|---|---|
| Blocker | 0 |
| Important | 0 |
| Suggestion | 6 |

All six suggestions are low-severity and deferrable. None gates Wave 0 close, and none blocks `/port` from consuming the super-rewrite capability.
