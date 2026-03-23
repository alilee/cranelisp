# Sprint 24: HKT, Lazy Sequences & Terminal Styling

**Status**: COMPLETE
**Ring**: 4 (Effects)
**Goal**: Deliver higher-kinded types, lazy sequences, and REPL terminal styling — clearing all 4 ignored tests and completing the Ring 4 type system surface.

## Scope

Three features plus debt clearance:

### Feature 1: Higher-Kinded Types (§3.7, §5.3.2, §5.4.4)

Type constructor parameters in trait declarations (`Functor`, `Monad`). Enables abstractions over type constructors.

### Feature 2: Lazy Sequences (§12.4.2)

`Seq` ADT type with thunk-based lazy evaluation. Producers, consumers, multi-sig dispatch.

### Feature 3: Terminal Styling & Pretty-Printer (repl/spec.md §10)

Unified S-expression pretty-printer with syntax highlighting. Head=bold, types=cyan, literals=yellow, strings=green, comments=italic.

### Debt Clearance

- Checked integer division (§12.7.3)
- FIXME(/int) banner stdout
- FIXME(/backend) CompileMode doc consistency
- link_multi_module_project test fix
- Traceability annotation updates

## FIXME Debt

| File | Owning Skill | Issue | Resolution |
|------|-------------|-------|------------|
| `src/repl/mod.rs:1586` | /int | Banner should use println!, not eprintln! | **resolved** — Wave 2 |
| `design/backend/module-caching.md:422` | /backend | CompileMode enum consistency note | **resolved** — Wave 2 |

## Architecture Review

**Reviewer**: /arch | **Verdict**: APPROVED WITH NOTES

- HKT: `Type::TyConApp` already exists. No boundary changes. Follow sketch unification approach.
- Lazy Sequences: Stdlib/ADT work on established patterns. No new machinery.
- Sexp::Comment: Approved. Pipeline isolation via `preserve_comments` flag. interfaces.md needs 7→8 update.
- Pretty-Printer: Approved in `src/`. All output paths must be wired — no partial delivery.
- Checked Division: Backend-only. No interface changes.
- No interim architecture confirmed.

## Design Docs

| Skill | Document | Status |
|---|---|---|
| /typecheck | `design/typecheck/hkt.md` | **done** — /arch approved |
| /backend | `design/backend/hkt-codegen.md` | **done** — /arch approved |
| /int | `design/int/terminal-styling.md` | **done** — /arch approved |
| /frontend | `design/frontend/comment-preservation.md` | **done** — /arch approved |

## Waves

### Wave 0: Design — COMPLETE
| Skill | Task | Status |
|-------|------|--------|
| /typecheck | Write `design/typecheck/hkt.md` | **done** |
| /backend | Write `design/backend/hkt-codegen.md` | **done** |
| /int | Write `design/int/terminal-styling.md` | **done** |
| /frontend | Write `design/frontend/comment-preservation.md` | **done** |
| /arch | Review all 4 design docs | **done** |
| /repl | Update repl/spec.md §10 | **done** |

### Wave 1: Foundation — COMPLETE
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /frontend | `Sexp::Comment` variant + `preserve_comments` reader mode | **done** | 8 files, 13 new tests |
| /typecheck | `apply()` TyConApp remapping + `free_vars` constructor IDs | **done** | cranelisp-types changes |

### Wave 2: Implementation + QA — COMPLETE
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /typecheck | HKT unification, trait decl/impl, method resolution | **done** | 3 new unify arms, register_hkt_trait, 5 unit tests |
| /backend | Checked division (Int.MIN/-1) + link test fix + FIXME | **done** | emit_checked_div extended, ObjectModule symbol fix, doc FIXME resolved |
| /frontend | Verify HKT parsing with existing syntax | **done** | All forms parse correctly, 4 new tests |
| /int | Style primitives + pretty-printer + wire output paths + --no-color + banner fix | **done** | style.rs (131 lines), pretty.rs (611 lines), all output paths wired |
| /stdlib | Seq ADT + lazy producers/consumers | **done** | stdlib/seq.cl + stdlib/seq/lazy.cl, 4 producers, 9 consumers |
| /qa | Tests for HKT, styling, checked division, lazy sequences | **done** | 35 new tests (17 HKT/lazy ignored, 18 e2e) |
| /frontend | Verify HKT parsing | **done** | Confirmed, 4 new AST builder tests |

### Wave 3: Build/Test/Review cycle — COMPLETE
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /qa | Un-ignore 4 original tests, run full suite | **done** | 1439 passed, 0 failed, 0 ignored |
| /qa | Update spec traceability annotations | **done** | /spec delegated, 10 annotations updated |
| /review | Assess all new code | **done** | 2B+4I+3S, all B+I fixed |
| compiler skills | Fix review findings + HKT gap | **done** | B1,B2,I1-I4 fixed, HKT registration added |
| /frontend | Re-apply Sexp::Comment (lost in Wave 2) | **done** | |

### Wave 4: Showcase — COMPLETE
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /repl | Create sprint demo `repl/demos/ring4i.demo` | **done** | HKT+lazy+styling+division+filter |
| /repl | Verify all prior demos play cleanly | **done** | 16 demos reviewed |
| /examples | Add HKT + lazy sequence examples | **done** | 26-functor.cl (347), 27-lazy-seq.cl (183) |
| /docs | Update user guide for HKT, lazy sequences, --no-color | **done** | getting-started.md updated |
| /port | Evaluate exemplar Functor/Monad usage | **done** | Monad would help; Functor marginal; lazy N/A |

### Wave 5: Bug fix (batch→GOT bridge)
| Skill | Task | Status | Notes |
|-------|------|--------|-------|
| /arch | Diagnose imported fn as higher-order arg bug | **done** | REPL-only, batch-compiled fns invisible to GOT |
| /int | Implement batch→GOT bridge in pipeline.rs | **done** | bridge_batch_to_got() after finalize_batch_jit() |
| /qa | Write failing test + verify fix | **done** | e2e_imported_fn_as_higher_order_arg_repl passes |

## Notes

**Test baseline at sprint start**: 1355 passing, 1 failing, 4 ignored
**After Wave 2**: 1435 passing, 0 failed, 4 ignored (+75 tests, link_multi_module_project FIXED)

**Wave 2 delivery summary**:
- `/typecheck`: Full HKT implementation — unification, trait decls, impls, method resolution. 5 new unit tests.
- `/backend`: Checked division (zero + MIN/-1 guards), link test fix (ObjectModule symbol naming), FIXME resolved. 3 new tests.
- `/int`: Complete terminal styling — style.rs (9 styles, TTY detection), pretty.rs (head bold, types cyan, literals yellow, strings green, comments italic, Lisp indentation). All output paths wired. --no-color flag. Banner fix.
- `/stdlib`: Seq type with 4 producers, 9 consumers in stdlib/seq/.
- `/qa`: 35 new tests — 9 HKT, 8 lazy seq, 7 checked division, 11 terminal styling.
- `/frontend`: HKT parsing verified, 4 new tests. Comment preservation done in Wave 1.

**Design review findings** (/arch):
- Verify `generalize()` doesn't treat constructor IDs as regular type vars
- Drop unused RunMode enum approach in /int
- Verify all Sexp match sites updated for Comment variant

**QA traceability mapping**: /qa produced a mapping table of spec sections needing annotation updates — blocked by file ownership (spec owned by /spec). To be delegated to /spec in Wave 3.

## Outcome

### Delivered

**Higher-Kinded Types** (spec §3.7, §5.3.2, §5.4.4):
- `Type::TyConApp` unification (3 arms: TyConApp↔ADT, TyConApp↔TyConApp, occurs check)
- `register_hkt_trait()`: constructor variable detection, `hkt_param_index`, TyConApp method schemes
- HKT impl validation: arity checking, primitive rejection, concrete self-type construction
- Method resolution via `hkt_param_index` instead of always arg[0]
- `apply()` collapses TyConApp→ADT when constructor variable is bound
- 3 previously-ignored tests now passing

**Lazy Sequences** (spec §12.4.2):
- `stdlib/seq/` module: `Seq` ADT (SeqNil, SeqCons with thunked tail)
- 4 producers: `range-from`, `iterate`, `repeat`, `cycle`
- 9 consumers: `seq-take`/`take`, `seq-drop`/`drop`, `seq-nth`, `take-while`, `drop-while`, `to-list`, `to-vec`
- 3 lazy operations: `seq-map`, `seq-filter`, `seq-reduce`
- `seq-zip-with` for element-wise combination
- 1 previously-ignored test now passing (placeholder upgraded)

**Terminal Styling & Pretty-Printer** (repl/spec.md §10):
- `src/style.rs` (131 lines): Style enum (9 variants), `styled()`, TTY detection via OnceLock
- `src/pretty.rs` (611 lines): S-expression pretty-printer with syntax highlighting
  - Head position bold (recursive per-list rule)
  - Type annotations (`:Type`) cyan
  - Literals yellow, strings green, comments italic
  - 40-char flat threshold, special-form 2-space indent, argument alignment
- All REPL output paths wired through pretty-printer
- `--no-color` CLI flag + `NO_COLOR` env var support
- Batch mode suppression (no ANSI in piped/redirected output)
- Non-formatter styling: prompt dim, errors red, headers bold, banner dim

**Comment Preservation** (repl/spec.md §10.3.6):
- `Sexp::Comment(String, Span)` variant in cranelisp-types
- `preserve_comments` reader mode (default off, pipeline unaffected)
- `parse_preserving_comments()` public API
- Defense-in-depth in AST builder

**Checked Division** (spec §12.7.3):
- `emit_checked_div()` extended: zero divisor + `Int.MIN / -1` overflow guard
- Both conditions panic with "division by zero" via `cranelisp_panic`

**Batch→GOT Bridge** (bug fix):
- `bridge_batch_to_got()` in pipeline.rs: after batch JIT finalization, creates GOT entries for all batch-compiled functions
- Fixes: imported stdlib functions can now be called and passed as values in the REPL
- Unblocks `seq-filter` with imported predicates (e.g., `even?`)

**Link Test Fix**:
- `link_multi_module_project`: cross-module ObjectModule symbol naming mismatch fixed
- 5 other link tests fixed by building `cranelisp-exe-bundle`

**FIXME Resolutions** (2):
- Banner stdout (src/repl/mod.rs) — banner moved to stdout with dim styling
- CompileMode doc consistency (design/backend/module-caching.md) — doc updated, FIXME removed

**Traceability** (10 spec annotations updated):
- §3.2.4, §4.12 Trace → [Tested]
- §5.1.3 Auto-Currying → [Tested]
- §12.7.3 Arithmetic Policy → [Tested]
- §12.9 Value Display Format (5 subsections) → [Tested]

**Review** (2B+4I+3S findings, all B+I fixed):
- B1: panic! → TypeError for SelfType in HKT signatures
- B2: ANSI-aware line length measurement in pp_bracket
- I1: &str → &TypeName in resolve_type_expr_hkt_impl
- I2: type_expr_uses_con_var recurses into Applied args
- I3: double pp() call eliminated in pp_bracket
- I4: silent arity default → expect() with invariant message

**Showcase**: ring4i.demo (HKT, lazy sequences, styling narrative, checked division, seq-filter with imported fn)
**Examples**: 26-functor.cl, 27-lazy-seq.cl
**Docs**: user guide updated (HKT section, --no-color, checked division, lazy sequences)

**Test count**: 1441 passed, 0 failed, 0 ignored (was: 1355 passed, 1 failed, 4 ignored)

### Deferred

- **Trait methods as first-class values** (spec §7.6): `(fmap show (Some 42))` fails — trait methods can't be passed as values even when concrete type is inferrable. FIXME(/qa) filed on spec/07-traits.md §7.6. Requires architectural work (method resolution + closure wrapping interaction). Not a Sprint 24 regression.
- **`src/repl/mod.rs:1600` FIXME(/int)**: `"; Restored user.cl"` persistence message uses eprintln! — should use println!. Distinct from the banner fix (which was done). Minor cosmetic, carried.
- **`interfaces.md` Sexp variant count**: Should be updated from 7 to 8 for `Sexp::Comment`. Mechanical, carried.
- **Review suggestions** (S1-S3): Token parsing duplication, list/bracket multiline sharing, flat_list double call. Non-blocking.

### Findings

- **Batch→GOT gap was a pre-existing systemic bug**: Functions compiled via `compile_module_batch` (used by `load_prelude_into_session`) were invisible to the REPL's GOT-based codegen. This meant ALL non-trait stdlib functions were unusable as values in the REPL — not just the ones discovered during Sprint 24 testing. The bridge fix (`bridge_batch_to_got`) is architecturally significant.
- **Wave 2 agent conflicts**: The `Sexp::Comment` variant implemented in Wave 1 was lost when Wave 2 agents overwrote the files. Had to re-apply in Wave 3. Concurrent agents modifying the same crate are risky.
- **HKT was 80% in place**: `Type::TyConApp` already existed in cranelisp-types with all utility functions handling it. The main work was in the typecheck crate (unification rules, trait registration, method resolution).
- **`/port` assessment**: Functor alone is marginal for the exemplar. Option Monad would eliminate ~40 lines of mechanical match boilerplate in the Sudoku solver. Worth implementing when Monad trait lands.
