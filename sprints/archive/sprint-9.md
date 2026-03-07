# Sprint 9: Ring 2 Gate + Ring 3 Preparation

**Status**: COMPLETE
**Ring**: 2 (gate) + 3 (design)
**Goal**: Formally close Ring 2 with gate review, bug fixes, design docs, and showcase; design Ring 3 macro architecture so implementation can begin in Sprint 10.

## Scope

Sprint 8 completed QA catchup with 798 tests and comprehensive traceability. Ring 2 features (traits, modules, constrained poly, multi-sig, auto-curry) are implemented and tested but the ring has no formal gate review, 5 tests remain ignored due to real bugs, and Decision 17 (interim trait registration) is flagged for elimination. Meanwhile, Ring 3 (macros) is the next major ring and architecturally the most complex — designing it now prevents false starts.

### Core deliverables

1. **Ring 2 gate review** — `/review` produces `design/review/ring2-report.md` assessing code quality, architecture adherence, and ring completion criteria per `tests/plan/strategy.md`

2. **3 RC bug fixes** — `/backend` fixes the 3 ignored RC tests:
   - Vec element drop glue for ADT fields with heap children (`rc.rs:874`)
   - Consuming calling convention for intermediate heap ADT temporaries (`rc.rs:891`)
   - Closure env and captured String not freed when closure consumed (`rc.rs:965`)

3. **Bare type name introspection** — `/qa` implements type name lookup at REPL so `Int`, `Bool` etc. produce useful feedback instead of "undefined variable" (`e2e.rs:362`, `e2e.rs:379`)

4. **Decision 17 elimination** — Move `Num`, `Eq`, `Ord`, `Display` trait definitions from hardcoded Rust (`register_*_trait()` in `builtins.rs`) to Cranelisp source evaluated through the normal pipeline. Decision 17 notes: "No module system or macros required. This can ship immediately."

5. **Ring 3 macro architecture** — `/arch` designs the macro mini-pipeline (`parse -> typecheck -> compile -> execute`), `MacroExpander` trait implementation strategy, and interface types for Ring 3

6. **`/frontend` Ring 3 plan** — Study sketch macro system (`sketch/src/macro.rs`, `sketch/docs/macro.md`), plan implementation approach for the reimplementation

7. **FIXME and annotation cleanup**:
   - Remove 2 RESOLVED-but-present FIXMEs in `user/plan-docs.md`
   - Update 8 remaining `[R2 S8]` section-level spec annotations
   - Audit FIXME(/qa) REPL non-conformance list (roadmap.md:39) against Sprint 8 progress

## FIXME Debt

| File | Owning Skill | Issue | Deferrals | Resolution |
|------|-------------|-------|-----------|------------|
| `design/arch/roadmap.md:7` | /arch | U0.1 — batch hello-world needs IO | 0 | deferred to Ring 4 |
| `design/arch/roadmap.md:39` | /qa | REPL spec non-conformance (12 items) | 0 | **audit in scope** #7 |
| `design/arch/roadmap.md:57` | /backend | U1.1 — 11 missing string primitives | 0 | deferred to Ring 3 |
| `CLAUDE.md:97` | /spec | Num trait in spec vs stdlib | 0 | **related to** #4 (Decision 17) |
| `repl/spec.md:5` | /repl | CLI invocation modes | 0 | deferred to Ring 4 |
| `repl/spec.md:22` | /qa | Bare type name lookup broken | 1 (S8 finding) | **in scope** #3 |
| `tests/plan/ring0.md:3` | /qa | U0.2 — /learn tutorial engine | 0 | deferred to Ring 4 |
| `crates/cranelisp-typecheck/plan-typecheck.md:478` | /typecheck | Borrow-splitting doc | 0 | deferred |
| `user/plan-docs.md:236` | /repl | RESOLVED — stale FIXME comment | 0 | **in scope** #7 |
| `user/plan-docs.md:238` | /arch | RESOLVED — stale FIXME comment | 0 | **in scope** #7 |
| `src/pipeline.rs:448` | /typecheck | Batch mode: `is_primitive()` doesn't follow import chains | 0 | **RESOLVED** — fixed in Wave 6 |

**Ignored tests (5)**:

| Test | File | Root Cause | Deferrals | Resolution |
|------|------|-----------|-----------|------------|
| `rc_vec_adt_element_drop_glue` | `rc.rs:874` | Vec element drop glue missing for ADT fields | 1 (S8) | **in scope** #2 |
| `rc_function_boundary_heap_adt_temp` | `rc.rs:891` | Consuming convention missing dec for temps | 1 (S8) | **in scope** #2 |
| `rc_closure_env_captured_string` | `rc.rs:965` | Closure env lifetime not managed | 1 (S8) | **in scope** #2 |
| `bare_type_int_lookup` | `e2e.rs:362` | REPL doesn't check type names | 1 (S8) | **in scope** #3 |
| `bare_type_bool_lookup` | `e2e.rs:379` | REPL doesn't check type names | 1 (S8) | **in scope** #3 |

## Architecture Review

**Reviewer**: /arch — **Verdict**: APPROVED WITH NOTES

1. **Technical coherence — SATISFACTORY.** The sprint forms two cleanly separable increments: (A) Ring 2 closure (gate review, RC fixes, bare-type introspection, Decision 17, cleanup) and (B) Ring 3 design (macro architecture, frontend plan, dependency surveys). All tasks in Increment A are independent of each other and can proceed in parallel.

2. **No interim architecture — PASS.** RC bug fixes are permanent Ring 1 infrastructure. Bare type introspection is permanent REPL capability. Decision 17 elimination *removes* an interim implementation, which is exactly what Principle 8 demands. The backend's `primitive_for_trait_method()` optimization (Decision 14) survives unchanged — it short-circuits at codegen time regardless of how traits were registered.

3. **Interface gaps — NONE BLOCKING.** All boundary types needed for Sprint 9 already exist: `MacroExpander` trait, `MacroClauseInfo`, `MacroParam`, `ModuleEntry::Macro`, `TraitDecl`, `TraitImpl`. No new interface types required.

4. **Decision 17 approach — APPROVED WITH CONDITIONS.**
   - Use "parse + typecheck without backend compilation" approach: process Cranelisp source strings through `register_trait_decl`/`register_trait_impl`. The backend's `primitive_for_trait_method()` handles codegen — no backend changes required.
   - **Bootstrap verification required**: `/typecheck` must verify that `register_trait_impl` can type-check bodies like `(defn + [x y] (add-i64 x y))` when called after `register_primitives()` but before user code. Write a unit test for this sequence.
   - **Trait module location**: trait declarations and implementations for primitive types go in the `primitives` synthetic module, preserving current behavior. `/typecheck` and `/arch` must agree on this.

5. **Ring 3 design feasibility — CONFIRMED.** The spec is comprehensive (915 lines), interface types exist, the sketch provides a working oracle, and the architectural decision (MacroExpander trait) is already made. Design in one sprint is realistic.
   - **Must address**: how the `MacroExpander` implementation accesses typechecker and backend for macro body compilation while AST builder holds `&mut dyn MacroExpander`. Recommended: expander struct owns separate mini-pipeline state.

6. **Interaction risks — LOW.**
   - RC fixes (backend heap/compiler), bare type introspection (REPL eval), and Decision 17 (typecheck builtins) touch different crates with no overlap.
   - **One subtle interaction**: Decision 17 changes where trait decls land in the module system. Task #3 (bare type introspection) and task #4 (Decision 17) must cross-check that `Num` at the REPL still produces useful output after traits move to Cranelisp source.

7. **Gate review scope note**: `/review` gate may discover issues beyond the 5 known ignored tests. Newly discovered blockers should be evaluated and either fixed in Sprint 9 or explicitly deferred with rationale.

### Additional design refs from /arch review
- `/typecheck`: Also reference `crates/cranelisp-typecheck/src/traits.rs` (normal `register_trait_impl` path) and `crates/cranelisp-backend/src/operators.rs` (`primitive_for_trait_method()` to confirm preservation)
- `/qa`: Also reference `crates/cranelisp-typecheck/src/builtins.rs` (primitive type name registration)
- `/arch` Ring 3: Also reference `crates/cranelisp-types/src/pipeline.rs` (MacroExpander trait), `crates/cranelisp-frontend/src/ast_builder.rs` (expander call sites)

## Skill Plans

### /review
**Task**: Ring 2 gate review — assess Sprints 4-7 code against ring completion criteria
**Approach**: Review the 13,000-line delta (57 files) between Ring 1 completion and HEAD, spanning 7 crates + binary. Apply general checklist + Ring 2 specific criteria (trait system correctness, module system determinism, constrained poly, cross-module GOT). Assess known issues: 3 RC bugs (deferred twice — not Ring 2 gate blockers but MEDIUM), 2 bare-type gaps (LOW), Decision 17 (MEDIUM debt). Preliminary findings already surfaced: clippy regressed from 0 to 29 warnings (including complex-type and too-many-args), 8 functions exceed 100 lines (worst: 188), and no Ring 2 design docs exist for traits/modules/cross-module codegen. Carry forward deferred Ring 1 items (F-7, F-10, F-12). Produce `ring2-report.md` with checklist, findings by severity, and gate verdict.
**Design refs**: `tests/plan/strategy.md` §Ring gate, `tests/plan/ring2.md` §Acceptance Gate, `design/review/checklist.md`, `design/review/ring1-report.md` (template)
**Acceptance**: `design/review/ring2-report.md` produced; no Blocker findings; Ring 2 declared PASS or issues identified

### /backend
**Task**: Fix 3 RC bugs surfaced by ignored tests
**Approach**: Three RC bugs stem from missing infrastructure at function boundaries and in standalone dec functions. Bug 1 (Vec element drop glue): generate proper drop glue functions for ADT-typed Vec elements, mirroring the sketch's `resolve_drop_fn` pattern, and pass them as `drop_glue_id` to `emit_rc_dec` in `build_elem_dec_fn`. Bug 2 (function-parameter leak): add `pop_scope_with_cleanup` before `return_` in `compile_body` so callees dec heap-typed parameters at exit, plus caller-side `rc_inc` for non-last-use variable arguments at call sites. Bug 3 (closure env leak): populate `captured_vars` during `compile_lambda`, emit `rc_inc` for non-last-use captures, generate per-lambda drop glue that dec's heap-typed captures, and dec closure temporaries after closure calls. Implementation order: Bug 2 first (prerequisite for Bug 3), then Bug 1 (self-contained), then Bug 3 (builds on both).
**Design refs**: `design/backend/rc.md`, `spec/12-runtime.md` §12.3, ignored test comments in `tests/rc.rs`
**Acceptance**: 3 ignored RC tests un-ignored and passing; 0 RC regressions

### /qa
**Task**: Implement bare type name introspection at REPL; audit REPL non-conformance FIXME; clean annotations
**Approach**: Add primitive type name recognition to `special_form_feedback()` in `src/repl.rs` by checking `Type::from_name(trimmed)` before the existing `symbol_table().get()` lookup. When a primitive type name is recognized, return `:primitives/{name}` (matching the existing `ModuleEntry::TypeDef` format). Un-ignore the two e2e tests (`bare_type_int`, `bare_type_bool`) and add `Float`/`String` variants. Audit the 12-item REPL non-conformance FIXME at `roadmap.md:39` — 10 of 12 items are fixed (Sprints 4-8), 2 remain: bare type name (resolved here) and float display (deferred). Update `[R2 S8]` spec annotations: promote tested items, re-target untested items. Cross-check with `/typecheck` that bare `Num` still resolves after Decision 17 changes.
**Design refs**: `repl/spec.md` §4.1, `design/arch/roadmap.md:39` (REPL non-conformance list), `crates/cranelisp-typecheck/src/builtins.rs` (primitive type name registration)
**Acceptance**: `Int`/`Bool` at REPL produce type info; 2 ignored e2e tests un-ignored; REPL non-conformance FIXME updated; `[R2 S8]` spec tags resolved; bare `Num` still works after Decision 17 changes
**Arch condition**: Cross-check with /typecheck task #4 that trait name lookup works after traits move to Cranelisp source.

### /arch
**Task**: Design Ring 3 macro architecture; review sprint scope; clean resolved FIXMEs
**Approach**: The Ring 3 macro mini-pipeline uses dependency inversion: `defmacro` forms are intercepted by the pipeline orchestrator (binary crate) before the AST builder sees them, compiled through the full typecheck+backend pipeline using the shared `TypeChecker` and `Jit`, and their function pointers stored in a `CranelispExpander` struct implementing `MacroExpander`. The `expand()` method performs clause dispatch, Sexp marshalling (via `cranelisp-runtime/marshal.rs`), function pointer invocation, and result unmarshalling — none of which require re-borrowing the typechecker or backend. One interface change needed: add `rest_param: Option<Symbol>` to `MacroClauseInfo`. Bootstrapping follows spec §9.12: seed `macros` module types at startup, then process prelude forms sequentially so each `defmacro` is compiled and registered before subsequent forms use it. Stale RESOLVED FIXMEs in `user/plan-docs.md` will be removed.
**Design refs**: `design/arch/architecture.md` §MacroExpander trait, `sketch/docs/macro.md`, `spec/09-macros.md`, `crates/cranelisp-types/src/pipeline.rs` (MacroExpander trait), `crates/cranelisp-frontend/src/ast_builder.rs` (expander call sites), `crates/cranelisp-types/src/module.rs` (MacroClauseInfo)
**Acceptance**: Ring 3 macro design doc produced; sprint scope APPROVED; stale FIXMEs cleaned; design explicitly addresses expander-owns-pipeline question (how MacroExpander accesses typecheck+backend while AST builder holds &mut dyn MacroExpander)

### /frontend
**Task**: Plan Ring 3 macro implementation
**Approach**: The macro system follows a 7-phase plan: (1) seed synthetic `macros` module with `SList`/`Sexp` ADTs + implement marshalling in `cranelisp-runtime`; (2) quasiquote expansion engine in `cranelisp-frontend` transforming templates to explicit constructor calls; (3) `defmacro` parsing + body synthesis (nested match for parameter destructuring); (4) `MacroExpander` trait implementation in binary crate with mini-pipeline and expansion engine; (5) pipeline integration replacing `NoOpExpander` in batch and REPL; (6) SList helpers + prelude macros (`/stdlib` scope); (7) REPL polish (`/expand`, macro introspection). Estimated ~1850 lines across ~12 new files. Critical constraint: macro bodies compiled during sequential form processing, not during AST building — `expand()` only invokes already-compiled functions. Sprint 9 deliverable is this plan document; implementation begins Sprint 10.
**Design refs**: `sketch/src/macro.rs`, `sketch/docs/macro.md`, `spec/09-macros.md`, `/arch`'s Ring 3 design
**Acceptance**: Implementation plan documented with phases, dependencies, and risk assessment

### /typecheck
**Task**: Support Decision 17 elimination — ensure trait registration from Cranelisp source works through normal pipeline
**Approach**: Replace `register_core_traits()` (4 per-trait helpers) and `register_builtin_impls()` (`register_builtin_impl` bypass) with code constructing `TraitDecl`/`TraitImpl` AST structs routed through the existing `register_trait_decl()`/`register_trait_impl()` paths — the same paths used for user-defined traits. Cannot use Cranelisp source strings directly because `cranelisp-typecheck` cannot depend on `cranelisp-frontend` for parsing; instead, construct AST structs in Rust with doc comments showing the equivalent Cranelisp. Returned `Defn` nodes from `register_trait_impl()` are discarded — the backend's `primitive_for_trait_method()` already short-circuits all core methods to inline IR. Add Display.show mappings to `primitive_for_trait_method()` in operators.rs (currently missing). Remove `register_builtin_impl()` shortcut from traits.rs and ~200 lines of helpers from builtins.rs. Write bootstrap verification unit tests confirming trait bodies reference only named primitives already in scope.
**Design refs**: `design/arch/CLAUDE.md` Decision 17, `builtins.rs` (`register_core_traits`, `register_builtin_impls`), `crates/cranelisp-typecheck/src/traits.rs` (normal `register_trait_impl` path), `crates/cranelisp-backend/src/operators.rs` (`primitive_for_trait_method()`), `spec/07-traits.md` §7.7
**Acceptance**: `Num`/`Eq`/`Ord`/`Display` defined via Cranelisp source; `register_*_trait()` Rust code removed; all trait tests pass; bootstrap unit test verifying `register_trait_impl` works after `register_primitives()` but before user code
**Arch conditions**: Traits go in `primitives` module. Use parse+typecheck path only (no backend compilation at init). Verify `primitive_for_trait_method()` optimization is preserved.

### /spec
**Task**: Review Num trait placement FIXME in context of Decision 17
**Approach**: Decision 17 moves core trait definitions from Rust to Cranelisp source in the `primitives` module. This resolves the FIXME's question: Num/Eq/Ord/Display trait *declarations* are language infrastructure (part of the compiler-seeded `primitives` module, not user-space stdlib), while the *standard library* provides convenience re-exports and higher-level traits. Update §7.7 to clarify this distinction and remove the FIXME.
**Design refs**: `CLAUDE.md:97` FIXME, `spec/07-traits.md` §7.7
**Acceptance**: FIXME resolved or deferred with rationale

### /repl
**Task**: Validate bare type name fix; spot-check REPL improvements
**Approach**: After `/qa` implements bare type name introspection, validate that `Int`, `Bool`, `Float`, `String` each produce spec-compliant feedback per `repl/spec.md` §4.1. Also verify `Num`, `Eq`, `Ord`, `Display` produce trait descriptions after Decision 17 changes. Run the full `repl_experience.rs` suite to confirm no regressions.
**Design refs**: `repl/spec.md` §4.1
**Acceptance**: Bare type name feedback matches spec; no REPL regressions

### /stdlib
**Task**: Early engagement — survey Ring 3 dependencies (macros needed for prelude)
**Approach**: Review `spec/09-macros.md` §9.10 for the 10 prelude macros (`list`, `do`, `bind!`, `vec`, `cond`, `case`, `->`, `->>`, `when`, `def`/`const`). Classify each by: (a) required macro features (single-clause, multi-clause, bracket destructuring, quasiquote) and (b) runtime dependencies (IO for `do`/`bind!`, collections for `vec`/`list`). Produce a dependency matrix showing which macros can be implemented at each sub-stage of Ring 3.
**Design refs**: `lib/plan-stdlib.md`, `spec/11-stdlib.md`, `spec/09-macros.md` §9.10
**Acceptance**: Ring 3 prelude dependency list documented

### /examples
**Task**: Early engagement — identify which examples require Ring 3 macros
**Approach**: Survey `sketch/examples/` for macro-dependent examples. For each of the ~25 examples, note which macro forms it uses (`list`, `do`, `cond`, threading, etc.) and whether it requires IO (Ring 4). Classify as: Ring 3 portable (macros only), Ring 4 (requires IO), or already ported (Ring 0-2).
**Design refs**: `examples/plan-examples.md`, `sketch/examples/`
**Acceptance**: Example readiness assessment documented

### /docs
**Task**: No docs work this sprint
**Approach**: N/A
**Acceptance**: N/A

### /platform
**Task**: No platform work this sprint
**Approach**: N/A
**Acceptance**: N/A

### /port
**Task**: Early engagement — assess exemplar macro requirements
**Approach**: Review exemplar design (`exemplar/plan-port.md`) for macro-dependent patterns (e.g., `list` construction, `cond` branching, threading macros in data transformation). Identify which exemplar modules can be implemented with Ring 3 macros vs which require Ring 4 IO. Note any stdlib gaps that would block exemplar progress.
**Design refs**: `exemplar/plan-port.md`
**Acceptance**: Exemplar Ring 3 readiness note documented

## Waves

### Wave 1: Design + Review (parallel)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /review | Ring 2 gate review → `ring2-report.md` | **done** | CONDITIONAL PASS: 0B/5I/9S. 3 conditions: C-1 clippy (29 warnings), C-2 function length (8 >100 lines), C-3 missing design docs |
| /arch | Ring 3 macro architecture design doc; clean stale FIXMEs in `user/plan-docs.md` | **done** | `design/arch/macro-pipeline.md` (440 lines); 2 stale FIXMEs removed |
| /frontend | Ring 3 macro implementation plan (7-phase) | **done** | `design/frontend/macro-plan.md` (624 lines); ~2300 lines estimated for Ring 3 |
| /spec | Review Num trait FIXME in context of Decision 17 | **done** | §7.7 clarified; CLAUDE.md FIXME removed |
| /stdlib | Survey Ring 3 prelude macro dependencies | **done** | `lib/plan-stdlib.md` §13 — 12 macros classified, phased implementation order |
| /examples | Classify examples by Ring 3/4 readiness | **done** | All 21 sketch examples need IO (Ring 4); Ring 3 learning examples are REPL-first |
| /port | Assess exemplar macro requirements | **done** | 85% of exemplar implementable at Ring 3; only `main.cl` needs Ring 4 |

### Wave 2: Implementation (parallel, after Wave 1)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /backend | Fix 3 RC bugs: Bug 2 (function params) → Bug 1 (Vec drop glue) → Bug 3 (closure env); clippy cleanup | **done** | Split calling convention: consuming (user fns) vs borrowing (builtins). Vec drop glue + closure drop glue. 77 RC tests pass (was 74+3 ignored). 10 clippy auto-fixes. |
| /typecheck | Decision 17: replace `register_core_traits`/`register_builtin_impls` with normal pipeline; add Display.show to `primitive_for_trait_method` | **done** | 802 tests passing; 5 new unit tests; Display.show mappings added to operators.rs |
| /qa | Bare type name introspection (`Type::from_name` in `special_form_feedback`); REPL non-conformance audit (10/12 fixed); `[R2 S8]` annotation updates | **done** | 4 e2e tests passing (was 2 ignored); 11/12 REPL non-conformance items fixed; all `[R2 S8]` tags resolved |

### Wave 3: Validation + Gate (after Wave 2)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Verify: all RC tests pass, bare type+trait names work after Decision 17 | **done** | 805 passed, 0 failed, 0 ignored. All 3 RC bugs fixed. Bare types `:primitives/Int` working. |
| /repl | Validate bare type/trait name feedback matches spec; no REPL regressions | **done** | 178 REPL experience tests pass. Types show `:primitives/{name}`. Traits show `:user/{name}` (cosmetic — should be `primitives`, noted as finding). |
| /review | Assess Wave 2 changes; final Ring 2 gate verdict | **done** | Ring 2 gate: CONDITIONAL PASS upheld. C-1 clippy partially addressed (10 auto-fixes, 4 structural remain). C-2/C-3 deferred to S10. |

## Notes

- Phase 1 (scope): Sprint 8 COMPLETE → archived. 798 tests, 5 ignored, 0 failures. Ring 2 gate review needed. 8 active FIXMEs (+ 2 stale RESOLVED). Decision 17 flagged for elimination.
- Phase 2 (arch review): APPROVED WITH NOTES — Decision 17 via parse+typecheck only, traits in `primitives` module, cross-check bare type+trait name lookup.
- Phase 3 (skill plans): All 14 skills have approaches filled. Key findings from /review preliminary scan: 29 clippy warnings (was 0), 8 functions >100 lines, no Ring 2 design docs. /arch produced comprehensive macro mini-pipeline design (dependency inversion via pipeline orchestrator). /typecheck will construct TraitDecl/TraitImpl AST structs (can't use frontend parser from typecheck crate). /backend identified fix order: Bug 2 → Bug 1 → Bug 3. /qa fix is localized to `special_form_feedback()` in repl.rs.
- Phase 4 (waves): 3 waves. Wave 1 = design+review (7 skills parallel). Wave 2 = implementation (3 compiler skills parallel). Wave 3 = validation+gate (3 skills).
- Wave 1 complete: all 7 tasks done. FIXME gate PASS. /review verdict: CONDITIONAL PASS with 3 conditions: C-1 clippy warnings (add to Wave 2 — mechanical), C-2 function decomposition (defer to Sprint 10 — refactoring during Ring 3 is more efficient), C-3 Ring 2 design docs (defer to Sprint 10 — traits/modules docs best written alongside Ring 3 design updates). `neq-string` bug noted by /review — maps to error path, would break `(!= "a" "b")` for strings. Added to Wave 2 /qa scope.
- Wave 2: All 3 tasks **done**. /backend agent ran long but completed all 3 RC bug fixes via split calling convention (consuming for user fns, borrowing for builtins). Vec drop glue and closure drop glue also implemented. 10 clippy auto-fixes applied. /typecheck eliminated Decision 17. /qa added bare type introspection.
- Wave 3: All 3 validation tasks **done**. **805 tests pass, 0 failures, 0 ignored.** Bare type names produce `:primitives/{name}`. Trait names produce `:user/{name}` (should be `primitives` per arch review — cosmetic finding). REPL experience suite: 178 tests pass, 0 regressions. FIXME gate PASS.
- Wave 5: All 5 tasks **done**. **1383 tests pass, 0 failures, 0 ignored, 0 clippy warnings.** /arch reviewed 3 design docs, filed 13 FIXMEs, added Decision 20 (split calling convention). /qa derived 84 test cases into ring2.md. /backend fixed neq-string (str-eq + bxor_imm). /typecheck fixed trait module (register in primitives context; `defining_module_for()` method). All 22 clippy warnings resolved across 3 crates.
- Wave 5b: All 4 FIXME resolution tasks **done**. 13 FIXMEs resolved across 5 design docs. FIXME gate PASS — zero remaining FIXMEs in any design doc touched by Waves 4-5b.
- Wave 6: All 3 tasks **done**. /port created `ring2b.demo` (plays clean). /repl validated all 5 checks pass (bare types, bare traits, string !=, 4 showcases, 178 REPL tests). /examples found all 15 examples broken in batch mode → root cause: `is_primitive()` doesn't follow import chains → /typecheck fixed → all 15 examples pass. `/examples` skill definition reinforced with Working Examples Requirement and Release Gate. Constraint display cosmetic: `clamp` shows duplicate Ord constraint `:Ord Ord a`.
- Wave 7: All 3 tasks **done**. Float display fixed (12/12 REPL non-conformance items resolved). 8 oversized functions decomposed into 27 named helpers, all under 100 lines. 807 tests pass, 0 failures, 0 ignored, 0 clippy warnings. 15/15 examples pass. Review conditions C-1 (clippy), C-2 (function length), C-3 (design docs) all resolved — Ring 2 gate is now unconditional PASS.
- **Note**: `design/arch/roadmap.md:39` FIXME(/qa) needs update: float display now fixed, 12/12 REPL non-conformance items resolved.
- **Sprint reopened (2nd)**: Deferral principles updated — carrying defects and deferring refactoring are anti-patterns. Float display (defect) and C-2 function decomposition (refactoring) reopened as Wave 7.
- **Sprint reopened (1st)**: Process improvement — sprint archetype updated with two cardinal rules: "design before code" (compiler skills) and "it's not done unless a user can use it" (user-proxy skills). Deferred items reconsidered: C-3 (design docs) is a prerequisite for Ring 3, not cleanup. C-2 (function decomposition) genuinely deferred to Sprint 10. Clippy, neq-string, trait module fix, and showcase added as new waves.

### Waves 1-3 Delivered (prior to reopen)
- **3 RC bugs fixed** — Split calling convention: consuming (user fns) vs borrowing (builtins). Vec + closure drop glue. 77 RC tests pass (was 74 + 3 ignored).
- **Decision 17 eliminated** — Core traits via normal pipeline. ~200 lines removed. 5 new unit tests.
- **Bare type introspection** — 4 e2e tests. REPL non-conformance 11/12 fixed.
- **Ring 2 gate review** — CONDITIONAL PASS. 0 Blockers, 5 Important, 9 Suggestions.
- **Ring 3 macro architecture** — `design/arch/macro-pipeline.md` (440 lines) + `design/frontend/macro-plan.md` (624 lines).
- **Spec annotation cleanup** — All `[R2 S8]` tags resolved.
- **User-proxy surveys** — /stdlib, /examples, /port Ring 3 readiness.

### Wave 4: Design (compiler skills, parallel)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /backend | Write Ring 2 design doc: RC calling conventions (split consuming/borrowing), closure drop glue, Vec drop glue, ADT field cleanup | **done** | `design/backend/ring2-rc.md` — 6 sections, split calling convention decision table, Ring 3 guidance |
| /typecheck | Write Ring 2 design doc: trait dispatch, constrained polymorphism, monomorphisation, default methods | **done** | `design/typecheck/traits.md` — 10 sections, 14 invariants, Decision 17 bootstrap |
| /frontend | Write Ring 2 design doc: module system, cross-module resolution, import/export, visibility | **done** | `design/frontend/modules.md` — 9 sections, synthetic modules, Ring 3 macro guidance |

### Wave 5: Design Review + Fixes (parallel)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Review Wave 4 design docs; document split calling convention as Decision 20 | **done** | 3 design docs reviewed, 13 FIXMEs filed (6 critical, 5 moderate, 2 minor). Decision 20 added (split calling convention). |
| /qa | Derive test cases from design docs; update `tests/plan/ring2.md` | **done** | 84 new test cases derived from 3 design docs, tagged [R2 S9] in `tests/plan/ring2.md` |
| /backend | Fix `neq-string` bug: implement `!=` for String in `operators.rs` | **done** | str-eq extern + bxor_imm negation. 2 new tests. |
| /typecheck | Fix core trait module: register traits in `primitives` module, not `user` | **done** | `register_builtins()` switches to primitives module context. `defining_module_for()` method. Traits show `:primitives/Num`. |
| /backend + /typecheck + /frontend | Fix all clippy warnings (22 total: 12 collapsible-if, 4 complex-type, 3 box, 2 map-or, 1 too-many-args) | **done** | 0 clippy warnings remaining. 12 let-chains, 3 box fixes, 2 map_or, 4 type aliases, 1 allow attribute. |

### Wave 5b: FIXME Resolution (developer skills, parallel — after Wave 5)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Fix 6 FIXMEs in own files: Decision 11 (embedded drop_glue_ptr), Decision 13 (RC ordering), interfaces.md HeapClosure layout, drop glue section, RC ordering, MonoDefn expr_types | **done** | All 6 FIXMEs resolved. HeapClosure CAPTURES_START=32, drop_glue_ptr at offset 24. |
| /backend | Fix ring2-rc.md §3.3 clarity; remove resolved FIXME(/arch) comments | **done** | §3.3 paragraph rewritten; 2 FIXME(/arch) comments removed. |
| /frontend | Fix modules.md: add trait/constrained Def seeding detail (§5.5), trait registration detail (§6.1) | **done** | Seeding description updated with constrained Def entries and TraitDecl distinction. |
| /typecheck | Fix traits.md: update Decision 17 status (eliminated Sprint 9); remove resolved FIXME(/arch) comments | **done** | Decision 17 status updated to reflect Sprint 9 resolution. MonoDefn FIXME removed. |

### Wave 6: Showcase (user-proxy skills, parallel)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /port | Build Ring 2 REPL showcase demo: demonstrate traits, modules, constrained poly, ADTs with field access, operator dispatch | **done** | `repl/demos/ring2b.demo` — strings, Display, user traits, constrained poly, introspection |
| /examples | Verify learning sequence through Ring 2: all 15 example files run clean | **done** | All 15 pass after `is_primitive()` fix. Non-zero return values confirmed. |
| /repl | Validate REPL experience: trait names show `:primitives/{name}` after fix, `!=` works for strings, showcase plays clean | **done** | All 5 checks PASS: bare types, bare traits, string !=, 4 showcases, 178 REPL tests |

### Wave 7: Defect + Refactoring (parallel)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Fix float display: ensure Float values always show decimal point (e.g., `5.0` not `5`). Decompose `compile_and_execute` (188 lines), `run_repl` (141 lines), `compile_module_graph` (136 lines) under 100 | **done** | Float fix + 3 functions decomposed into 14 helpers. 807 tests pass. |
| /backend | Decompose `emit_inline_drop_glue` (140 lines), `compile_match` (128 lines), `compile_data_pattern` (116 lines) under 100 | **done** | 3 functions decomposed into 7 helpers. All tests pass. |
| /typecheck | Decompose `monomorphise_call` (149 lines) and `register_imports` (148 lines) under 100 | **done** | 2 functions decomposed into 6 helpers. All tests pass. |

## Outcome

### Delivered
- **Ring 2 gate review** — CONDITIONAL PASS (0 Blockers, 5 Important, 9 Suggestions); C-1 resolved (0 clippy), C-3 resolved (3 design docs)
- **3 RC bugs fixed** — Split calling convention (Decision 20): consuming (user fns) vs borrowing (builtins). Vec drop glue + closure drop glue. 77 RC tests pass (was 74+3 ignored)
- **Decision 17 eliminated** — Core traits via normal `register_trait_decl`/`register_trait_impl` pipeline. ~200 lines removed. 5 new unit tests
- **Bare type/trait introspection** — `Int` → `:primitives/Int`, `Num` → `:primitives/Num`. 4 e2e tests
- **Core trait module fix** — Traits registered in `primitives` module context; `defining_module_for()` method
- **neq-string fix** — `(!= "hello" "world")` works via str-eq + bxor_imm. 2 new tests
- **0 clippy warnings** — 22 warnings resolved across 3 crates (12 let-chains, 4 type aliases, 3 box, 2 map_or, 1 allow)
- **Ring 3 macro architecture** — `design/arch/macro-pipeline.md` (440 lines) + `design/frontend/macro-plan.md` (624 lines)
- **3 Ring 2 design docs** — `design/backend/ring2-rc.md`, `design/typecheck/traits.md`, `design/frontend/modules.md`
- **Design doc review** — /arch filed 13 FIXMEs, all resolved. Decision 11/13 updated, interfaces.md HeapClosure fixed
- **84 design-derived test cases** — Added to `tests/plan/ring2.md` tagged [R2 S9]
- **Ring 2B showcase** — `repl/demos/ring2b.demo` (strings, Display, user traits, introspection)
- **REPL validation** — 178 tests pass, all 4 showcases clean, bare type/trait names correct
- **Spec annotation cleanup** — All `[R2 S8]` tags resolved; REPL non-conformance 12/12 fixed
- **User-proxy surveys** — /stdlib (12 prelude macros classified), /examples (Ring 3/4 readiness), /port (85% at Ring 3)
- **Batch mode fix** — `is_primitive()` now follows import chains; all 15 examples pass via `--run`
- **Sprint archetype improved** — Two cardinal rules: "design before code" + "not done unless user can use it". 5 skill definitions updated with Design Doc/Test Plan Obligation sections
- **`/examples` skill definition reinforced** — Working Examples Requirement + Release Gate added
- **Float display fixed** — Whole-number floats now display with `.0` (e.g., `:primitives/Float 3.0` not `3`). Last REPL non-conformance item resolved (12/12)
- **8 oversized functions decomposed** — All functions now under 100 lines. Review condition C-2 fully resolved. 27 named helpers extracted across 5 files
- **`/sprint` skill definition updated** — Deferral Principles section: carrying defects is anti-pattern, deferring refactoring is anti-pattern, only legitimate deferral is avoiding interim architecture

### Deferred
- ~~Batch mode primitives~~ — **RESOLVED** in Wave 6. `is_primitive()` now follows import chains.
- ~~Review condition C-2~~ — **RESOLVED** in Wave 7. All 8 functions decomposed under 100 lines.
- ~~Float display~~ — **RESOLVED** in Wave 7. Float values always display with decimal point.

### Findings
- **Batch mode broken for named primitives** — `is_primitive()` in `crates/cranelisp-typecheck/src/infer.rs:240` uses raw `SymbolTable::get()` which doesn't follow import chains. In batch mode, `compile_module_graph` creates a non-`user` module where builtins are `ModuleEntry::Import` not `ModuleEntry::Def`, so `is_primitive()` returns false. No `BuiltinFn` resolution is recorded, codegen falls through to `compile_direct_call`, which fails with "undefined function" for inline primitives. Fix: `is_primitive()` should resolve imports. Filed FIXME(/typecheck).
- **Constraint display cosmetic** — `clamp` shows `:(Fn [:Ord Ord a :a :a] a)` with duplicate `Ord`. Pre-dates Sprint 9.
- **Process gap closed** — Design docs were being deferred as cleanup instead of written before implementation. Sprint archetype now mandates Design wave before Implementation wave.

## Next skills

- `/frontend` — Begin Ring 3 macro implementation (Phase 1: seed macros module with SList/Sexp ADTs)
- `/arch` — Finalize Ring 3 interface types (`MacroClauseInfo.rest_param`, marshalling types); fix stale `design-space.md` refs noted by /arch agent
- `/typecheck` — Ring 3 prep: macro body type-checking support
- `/backend` — Ring 3 codegen prep
- `/sprint` — Plan Sprint 10: Ring 3 Phase 1 (macro infrastructure)
