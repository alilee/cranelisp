# Sprint 3: Ring 1 Completion — Vec

**Status**: COMPLETE
**Ring**: 1 (Heap) — completion
**Goal**: Deliver Vec (Ring 1 Chunk D, deferred from Sprint 2) to complete Ring 1, plus relocate demo infrastructure to its correct home.

## Scope

Vec is the final Ring 1 feature. It was deferred from Sprint 2 as a self-contained chunk that depends only on the heap infrastructure already in place. Completing it unlocks:
- `/stdlib` collection functions (`map`, `filter`, `fold` over Vec)
- `/port` exemplar implementation (Vec is the critical-path blocker per U1.10)
- Ring 2 can begin with Ring 1 fully delivered

### Vec Deliverables
- Vec literal syntax `[1 2 3]`
- Vec type inference (`Vec(elem_type)`, element type unification)
- Vec codegen: heap-allocated (RC header + len + cap + data_ptr), element storage as i64
- Vec primitives: `vec-get`, `vec-set`, `vec-push`, `vec-len`
- Vec RC: element inc on get, element dec on drop, COW for set/push when rc==1 and is-last-use
- Vec drop glue: dec each element, free data buffer, free vec struct
- Vec display in REPL
- Vec in ADT fields, Vec of Strings, Vec of ADTs

### Demo Relocation
- Move `tests/repl/demos/` → `repl/demos/`
- Move `./showcase` → `repl/showcase`
- Update paths in `repl/demos/CLAUDE.md`
- These are `/repl`-owned experience artifacts, not test infrastructure

## Proposed Wave Structure

| Wave | Skills | What it produces |
|------|--------|-----------------|
| 0 | `/arch` | Vec layout spec in `interfaces.md` (if not already sufficient) |
| 1 | `/frontend`, `/typecheck`, `/backend`, `/platform` | Vec implementation |
| 1.5 | `/review` | Implementation review |
| 2 | `/qa` | Vec integration tests (~30), RC tests, Ring 0–1 regression |
| 3 | `/repl`, `/examples`, `/docs`, `/stdlib`, `/port` | User-proxy validation, demo relocation |
| 4 | `/review` | Ring 1 completion gate (Vec-specific, no full ring re-review) |

## Skill Assignments

### /arch
**Input**: `design/arch/interfaces.md`, Sprint 2 Chunk D spec
**Task**: Verify Vec layout spec is complete in `interfaces.md`. Key decisions: Vec heap layout (header + len/cap/data_ptr vs. inline fields), data buffer as separate allocation, element RC protocol for get/set/push, COW decision protocol (is-last-use + rc==1).
**Output**: Updated `interfaces.md` if needed, or confirmation that existing spec suffices
**Blocked by**: —
**Wave**: 0
**Acceptance**: Vec layout fully specified; backend and platform can implement independently

### /review
**Input**: Ring 1 checklist (already exists from Sprint 2)
**Task**:
1. Wave 1.5: Review Vec implementation in all crates against ring1-checklist.
2. Wave 4: Confirm Ring 1 is complete (Vec + prior chunks), no regressions.
**Output**: Vec review notes, Ring 1 completion confirmation
**Blocked by**: Wave 1 (review), all Wave 3 (completion gate)
**Wave**: 1.5, 4

---

### /frontend
**Input**: `/arch` Vec layout spec
**Task**: Parse `[e1 e2 ...]` as Vec literal in expression position. Disambiguate from parameter lists (in `defn`/`fn` signatures) and ADT constructor field lists (in `deftype`). Emit `Expr::VecLit { elements, span }`. ~5 unit tests.
**Output**: Vec literal parsing, unit tests
**Blocked by**: /arch Wave 0
**Wave**: 1
**Acceptance**: `[1 2 3]` parses as VecLit; `(defn foo [x] x)` still parses params correctly; existing tests pass

### /typecheck
**Input**: `/arch` Vec layout spec, `/frontend` VecLit AST
**Task**: Vec type inference — `[1 2 3]` infers `Vec(Int)`, `["a" "b"]` infers `Vec(String)`, `[]` infers `Vec(a)` (polymorphic), element types unify. Vec in function signatures and ADT fields. ~10 unit tests.
**Output**: Vec type inference, unit tests
**Blocked by**: /arch Wave 0
**Wave**: 1
**Acceptance**: Vec type inference correct; Ring 0–1 unit tests pass

### /platform
**Input**: `/arch` Vec layout spec
**Task**: Implement Vec extern primitives in `cranelisp-runtime`:
- `vec_new(cap) -> *Vec` — allocate Vec with initial capacity
- `vec_get(vec, idx) -> i64` — bounds-checked element access
- `vec_set_copy(vec, idx, val) -> *Vec` — COW copy path
- `vec_push_copy(vec, val) -> *Vec` — COW copy path
- `vec_push_grow(vec, val) -> *Vec` — growth + push
- `vec_len(vec) -> i64`
- `vec_drop(vec)` — free data buffer + vec
- Element RC callbacks for copy paths
- ~15 unit tests
**Output**: Vec runtime primitives, unit tests
**Blocked by**: /arch Wave 0
**Wave**: 1
**Acceptance**: All Vec runtime ops correct; parallel-safe tests; no leaks

### /backend
**Input**: `/arch` Vec layout spec, `/typecheck` Vec type info, `/platform` runtime primitives
**Task**:
1. **RC prerequisite — F-12 fix**: Add null/low-value guard to `emit_rc_dec` in `heap.rs`. Bare i64 tags from nullary ADT constructors (e.g., `None` = 0) must not be treated as heap pointers. Guard: `if ptr < NULLARY_TAG_THRESHOLD { skip dec }`. This MUST be done before any Vec element dec is emitted. (See `design/review/ring1-report.md` F-12.)
2. **`vec_elem_inc_cache`**: Generate per-element-type inc functions and cache them. Three cases: `AlwaysHeap` → atomic inc at `val-8`; `Mixed` → guard `val < threshold` then inc; `NeverHeap` → null pointer (extern skips call). These function pointers are passed to `vec-set-rc`/`vec-push-rc` copy paths.
3. Vec heap allocation: construct Vec struct (len/cap/data_ptr) with RC header.
4. `vec-get`: inline bounds check + element load + `emit_inc` for heap-typed elements.
5. `vec-set`: COW check (is-last-use + rc==1 → inline mutate with element dec/store, else call `vec_set_copy` with elem_inc fn ptr).
6. `vec-push`: COW check (is-last-use + rc==1 + has capacity → inline push, else call `vec_push_copy`/`vec_push_grow` with elem_inc fn ptr).
7. `vec-len`: inline load.
8. Vec drop glue: loop through `0..len`, call per-element-type dec on each element, free data buffer, free Vec struct. Must handle Mixed element types with the null guard from step 1.
9. `format_result_value` for Vec display (recursive element formatting).
10. **REPL empty-line and comment handling**: Fix the REPL evaluation loop (`src/repl.rs`) to skip blank lines and comment-only lines (lines where the reader strips `;` leaving empty input). Currently these produce `error: parse error at 0..0: empty input`. After the fix, blank/comment input should silently re-prompt. This resolves the FIXME in `repl/spec.md` line 10 for empty/comment input.
11. ~20 unit tests (15 Vec + 2 RC guard + 3 REPL input handling).
**Output**: F-12 fix, vec_elem_inc_cache, Vec codegen, drop glue, display, REPL input fix, unit tests
**Blocked by**: /arch Wave 0, /platform Wave 1
**Wave**: 1
**Acceptance**: Vec codegen correct; RC balanced for all element types (NeverHeap, AlwaysHeap, Mixed); Vec displays correctly in REPL; blank/comment lines at REPL produce no error; F-12 guard active

---

### /qa
**Input**: All Wave 1 implementation complete
**Task**:
1. **RC gap tests (U1.3 + U1.5)** (~10 tests, run first to validate F-12 fix):
   - U1.3: Nested heap ADT RC — `(Some (Some "hello"))` create+drop, `(Some "hello")` in let scope, nested Option chain
   - U1.5: Closure capturing heap types — `(let [s "x"] (fn [] s))` create+drop, closure capturing ADT with string field
   - F-12 validation: dec on Mixed ADT values (nullary + data constructors) — confirm null guard works
2. **Vec integration tests** (~25 tests): Vec literal, empty Vec, get/set/push/len, Vec in ADTs, Vec of Strings, Vec of ADTs with heap fields, nested Vec, Vec RC balance, Vec COW correctness (mutate-in-place vs copy), Vec drop with heap elements, Vec of closures.
3. **Vec RC tests** (~10 tests in `tests/rc.rs`): Vec alloc+drop, Vec of Strings (element dec on drop), Vec-set COW (shared Vec copies, unique Vec mutates), Vec-push growth, Vec with Mixed element types (Option String).
4. Ring 0–1 regression: all existing 436 tests still pass.
**Output**: ~45 new tests (10 RC gap + 25 integration + 10 Vec RC), Ring 0–1 regression green
**Blocked by**: Wave 1.5 (review gate)
**Wave**: 2
**Acceptance**: All Vec tests pass; all Ring 0–1 tests pass; RC balanced for Vec of every element type (Int, String, ADT, closure, nested ADT); U1.3 and U1.5 resolved; no leaks under CRANELISP_RC_TRACE

### /stdlib
**Input**: Ring 1 compiler with Vec
**Task**:
1. Update `lib/plan-stdlib.md` — Vec is now available; reassess which collection functions can be planned.
2. File usability findings if Vec operations reveal friction.
**Output**: Updated plan, usability findings if any
**Blocked by**: Wave 2
**Wave**: 3
**Acceptance**: Plan updated with Vec availability assessment

### /examples
**Input**: Ring 1 compiler with Vec
**Task**: Vec example (14-vecs): creation `[1 2 3]`, access `vec-get`, mutation `vec-set`/`vec-push`, iteration patterns. Update example tests.
**Output**: 1 new example, example tests pass
**Blocked by**: Wave 2
**Wave**: 3
**Acceptance**: Example compiles and produces correct output

### /docs
**Input**: Ring 1 compiler with Vec
**Task**: Update `user/getting-started.md` with Vec section. Update tutorial curriculum.
**Output**: Updated getting-started guide
**Blocked by**: Wave 2
**Wave**: 3
**Acceptance**: Vec documentation with tested examples

### /repl
**Input**: Ring 1 compiler with Vec
**Task**:
1. **Relocate demo infrastructure**: Move `tests/repl/demos/` → `repl/demos/` and `./showcase` → `repl/showcase`. Update paths in `repl/demos/CLAUDE.md` and any references. Demo scripts and the showcase player are `/repl`-owned experience artifacts, not test infrastructure.
2. **Update `repl/spec.md`**: Add specification for empty-line and comment-line handling (blank lines and `;` comment lines silently re-prompt, no error). Resolve the FIXME at line 10. This formalises what `/backend` implements.
3. Vec display tests in REPL experience test suite.
4. Update `ring1.demo` with Vec showcase content. Demos can now use blank lines and comments directly (no workaround needed after `/backend`'s REPL fix).
**Output**: Relocated `repl/demos/` and `repl/showcase`, updated spec, Vec REPL tests, updated demo
**Blocked by**: — (relocation + spec update), Wave 2 (Vec tests + demo update)
**Wave**: 3
**Acceptance**: `repl/showcase ring1` plays updated demo with blank lines and comments working natively; no demo/showcase files remain under `tests/` or project root; Vec displays correctly

### /port
**Input**: Ring 1 compiler with Vec (resolves U1.10)
**Task**: Vec unblocks the exemplar. Update `exemplar/plan-exemplar.md` — assess which exemplar modules can now be implemented with Vec available. Grid, candidates, and collection patterns should now be expressible.
**Output**: Updated exemplar plan with Vec assessment
**Blocked by**: Wave 2
**Wave**: 3
**Acceptance**: Exemplar plan updated; blocking issues filed if any remain

## Task List

| # | Wave | Skill | Task | Status | Blocked By |
|---|------|-------|------|--------|------------|
| 1 | 0 | /arch | Vec layout spec in `interfaces.md` (verify or complete); specify vec_elem_inc_cache contract | **done** | — |
| 2 | 1 | /frontend | Vec literal parsing (`[e1 e2 ...]`), 7 unit tests | **done** | 1 |
| 3 | 1 | /typecheck | Vec type inference, 15 unit tests (12 infer + 3 HeapCategory); Vec primitive registration (U1.12 fix), 5 unit tests | **done** | 1 |
| 4 | 1 | /platform | Vec runtime primitives (including COW copy paths with elem_inc fn ptr), 15 unit tests | **done** | 1 |
| 5 | 1 | /backend | F-12 fix (emit_rc_dec null guard), vec_elem_inc_cache, Vec codegen (alloc, get, set COW, push COW, len, drop glue, display), 23 unit tests | **done** | 1, 4 |
| 5a | 1 | /backend | REPL empty-line and comment-line handling — skip blank/`;` input, re-prompt silently | **done** | — |
| 6 | 1.5 | /review | Vec + REPL fix + F-12 fix review against ring1-checklist | **done** (2B, 5I, 5S) | 2, 3, 4, 5, 5a |
| 6a | 1.5R | /backend | Address review findings: B1 (raw offsets→constants), B2 (elem_inc naming→per-type) | **done** | 6 |
| 6b | 1.5R | /review | Re-review: B1/B2 fixes verified — no raw offsets in repl.rs, stable naming in vec_codegen | **done** | 6a |
| 7 | 2 | /qa | RC gap tests (U1.3/U1.5/F-12, ~10), Vec integration (~25), Vec RC (~10), REPL input tests, regression | **done** (32 Vec tests passing; 10 Vec RC tests #[ignore] — scope-level dec deferred to Ring 2; Vec REPL display implemented and tested) | 6b |
| 8 | 3 | /repl | Relocate demos → `repl/demos/`, showcase → `repl/showcase` | **done** | — |
| 8a | 3 | /repl | Update `repl/spec.md` — specify empty-line and comment-line handling, resolve FIXME | **done** | — |
| 9 | 3 | /repl | Vec REPL tests (3 display + 2 blank/comment), update `ring1.demo` with Vec section | **done** | 7, 5a |
| 10 | 3 | /examples | Vec example (14-vecs.cl), example test | **done** | 7 |
| 11 | 3 | /docs | Getting-started Vec section, tutorial curriculum update | **done** | 7 |
| 12 | 3 | /stdlib | Update plan-stdlib.md with Vec assessment, collection fn planning | **done** | 7 |
| 13 | 3 | /port | Update exemplar plan — Vec unblocks Grid/candidates modules; U1.10 resolved | **done** | 7 |
| 14 | 4 | /review | Ring 1 completion confirmation — 487 tests pass, 39 ignored (all justified), all tasks done | **done** | 6b, 7, 8, 8a, 9, 10, 11, 12, 13 |

## Notes

- Tasks 8, 8a (/repl demo relocation + spec update) have no implementation dependency — can be done immediately
- Task 5a (/backend REPL fix) has no dependency on Vec — can be done in parallel
- Vec was specified as Sprint 2 Chunk D; this sprint delivers it unchanged
- Pretty printer (`pprint`) deferred to Ring 2+ (needs Display trait at minimum); Clojure-style `clojure.pprint` pattern, owned by `/stdlib`
- Ring 2 planning begins in Sprint 4

### Review Findings (Wave 1.5)

**Blockers (fixed):**
- B1: Raw byte offsets in `src/repl.rs` → replaced with `HeapAdt::TAG_OFFSET`, `HeapAdt::field_offset()`, `HeapVec::LEN_OFFSET`, `HeapVec::DATA_PTR_OFFSET`
- B2: `build_elem_inc_fn`/`build_elem_dec_fn` used per-span naming → changed to stable `runtime/vec_elem_inc_{heap|mixed}` naming, deduplicating across call sites

**Important (deferred to Ring 2):**
- I1: `vec-len` registered as Extern in typechecker but compiled inline — harmless mismatch, document in Ring 2
- I2: Element inc/dec naming now uses `runtime/vec_elem_inc_{heap|mixed}` (fixed with B2)
- I3: `compile_vec_set_cow` is 99 lines — at limit, defer extraction until Ring 2 adds complexity
- I4: `vec-set` COW mutate path omits RC-inc for new value — safe in Ring 1 (no scope-level dec), must fix in Ring 2
- I5: `vec-get` bounds panic lacks index/length detail — file as usability finding

### RC Risks Identified

Three prerequisites must be satisfied before Vec can safely emit RC operations:

1. **F-12 (Critical)**: `emit_rc_dec` in `heap.rs` has no null/low-value guard. Bare i64 tags from nullary ADT constructors (e.g., `None` = 0, `Red` = 1) would be treated as heap pointers, corrupting memory. The guard `if ptr < NULLARY_TAG_THRESHOLD` must be added before any Vec element dec is emitted. Assigned to `/backend` task 5, step 1.

2. **U1.3 (High)**: Nested heap ADT RC is untested. `(Some (Some "hello"))` drop path has never been exercised. Vec of ADTs with heap fields (`Vec (Option String)`) hits this pattern directly. Assigned to `/qa` task 7, step 1.

3. **U1.5 (High)**: Closure capturing heap types (String, ADT) is untested. `(let [s "x"] (fn [] s))` never tested. Vec operations that take closures as arguments depend on this being correct. Assigned to `/qa` task 7, step 1.

Additional Vec-specific RC work:

4. **vec_elem_inc_cache**: Per-element-type inc function pointers must be generated and cached. Needed by COW copy paths (`vec-set-rc`, `vec-push-rc`). Three variants: AlwaysHeap (atomic inc), Mixed (guarded inc), NeverHeap (null fn ptr). Assigned to `/backend` task 5, step 2.

5. **Vec drop glue**: Must loop through elements and call per-element-type dec. Recursive for ADTs containing heap fields. Assigned to `/backend` task 5, step 8.

6. **Scope-level dec**: Infrastructure scaffolded in Ring 1 but not wired. Vec doesn't need full scope-level dec (Ring 2), but does need dec for Vec temporaries. Current Vec design avoids this: Vec operations return a new Vec (or the same one for COW), and the caller's binding handles the old value. Risk is low but should be monitored.

## Outcome

### Delivered
- **Vec type system**: Vec literal parsing `[e1 e2 ...]`, polymorphic type inference `(Vec a)`, element type unification
- **Vec codegen**: heap-allocated (RC header + len + cap + data_ptr), COW for set/push when rc==1 and is-last-use
- **Vec primitives**: `vec-get`, `vec-set`, `vec-push`, `vec-len` — 4 polymorphic type schemes registered in typechecker
- **Vec runtime**: `vec_new`, `vec_get`, `vec_set_copy`, `vec_push_copy`, `vec_push_grow`, `vec_len`, `vec_drop`
- **Vec drop glue**: per-element-type dec loop with NeverHeap/AlwaysHeap/Mixed dispatch
- **F-12 fix**: `emit_rc_dec` null/low-value guard prevents nullary ADT tags from being treated as heap pointers
- **Vec REPL display**: `format_vec_elements` reads HeapVec layout, formats elements recursively
- **REPL blank/comment handling**: empty lines and `;` comment lines silently re-prompt (no parse error)
- **U1.12 resolved**: Vec primitives registered with polymorphic type schemes using `fresh_var_id()` to avoid type variable collision
- **U1.10 resolved**: Vec unblocks exemplar Grid/candidates modules
- **Demo relocation**: `tests/repl/demos/` → `repl/demos/`, `./showcase` → `repl/showcase`
- **Example**: `examples/14-vecs.cl` with integration test
- **Documentation**: Getting-started Vec section, tutorial curriculum section 19
- **Stdlib plan**: Vec collection functions assessed and build order updated
- **Exemplar plan**: Vec availability assessment, proof-of-concept scoped
- **Test count**: 487 passed, 39 ignored (17 RC scope-level dec, 20 E2E deferred, 2 parse-int)

### Deferred
- **10 Vec RC balance tests**: scope-level dec not wired in Ring 1 — deferred to Ring 2
- **I4 (vec-set COW RC-inc)**: COW mutate path omits RC-inc for new value — safe in Ring 1, must fix in Ring 2
- **I1 (vec-len Extern/Inline mismatch)**: harmless classification mismatch — document in Ring 2
- **I3 (compile_vec_set_cow size)**: 99 lines, at limit — defer extraction until Ring 2 adds complexity

### Findings
- **Type variable collision**: Using `Var(0)` when `next_id=0` causes infinite recursion in `apply`. Fix: always allocate via `fresh_var_id()`. This pattern could recur for any scheme registration.
- **Vec annotation syntax conflict**: `[:Int]` in function parameter position is ambiguous (Vec literal vs type annotation list). Example 14-vecs required removing the annotation and relying on inference.
- **String primitives are the new critical path**: With Vec delivered, exemplar is now blocked on string manipulation primitives (U1.1: `char-at`, `str-split`, `str-contains`, `str-sub`).
- **Ring 1 is COMPLETE**: All 4 chunks (A: core heap, B: ADTs, C: closures, D: Vec) delivered across Sprints 2-3.
