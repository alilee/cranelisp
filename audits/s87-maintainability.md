# Sprint 87 — Maintainability & Simplicity Deep-Pass

> **What this is.** The chartered simplicity/maintainability/duplication recommendation
> sets the 8 per-crate Stage-B audits under-delivered. Quantitative input:
> `audits/loc-s87.md` (corrected non-test LOC per module). This pass produces two
> concrete, actionable backlogs: (1) inline-test → sibling-file extraction, and
> (2) oversized production-module decomposition. READ-ONLY on code; advisory findings.
>
> Authored by `/review`, Sprint 87.

---

## Part 1 — Inline-test → sibling-file extraction

### 1.1 The existing convention (established, not invented here)

The project ALREADY has a settled convention for splitting unit tests out of a large
production module into a sibling file, demonstrated in `cranelisp-typecheck`:

- **Declaration form.** The production module declares, at the bottom of the file:
  ```rust
  #[cfg(test)]
  mod tests;
  ```
  This pulls in a sibling file under a same-named subdirectory: `<module>/tests.rs`.
  (Rust resolves `mod tests;` inside `foo.rs` to `foo/tests.rs` when `foo/` exists.)

- **Naming.** The sibling file is `<module>/tests.rs`. Shared test fixtures use
  `<module>/test_support.rs` (declared `#[cfg(test)] mod test_support;`). Topical test
  splits use `<module>/<topic>_tests.rs` (e.g. `traits/primitive_dispatch_tests.rs`).

- **Established exemplars** (from `audits/loc-s87.md` §2, all corrected-prod 0 — pure test):
  | Sibling test file | Test LOC | Production module it serves |
  |---|--:|---|
  | `typecheck/program/tests.rs` | 4935 | `typecheck/program.rs` |
  | `typecheck/infer/tests.rs` | 2183 | `typecheck/infer.rs` |
  | `typecheck/checker/tests.rs` | 1221 | `typecheck/checker.rs` |
  | `typecheck/traits/tests.rs` | 952 | `typecheck/traits.rs` |
  | `typecheck/checker/test_support.rs` | 494 | `typecheck/checker.rs` |
  | `typecheck/traits/primitive_dispatch_tests.rs` | 73 | `typecheck/traits.rs` |

- **`src/CLAUDE.md` reference.** §Testing: *"Every module gets `#[cfg(test)] mod
  tests`. Unit tests live next to the code they test."* The convention is documented
  but says "next to" — the sibling-file form is the scaled version when the inline
  block grows large (as typecheck already practises). This pass recommends the
  sibling-file form wherever the inline `#[cfg(test)]` block dominates the file.

> **Crates that ALREADY follow the convention — do NOT re-do.** `cranelisp-typecheck`
> is fully migrated (its four densest modules carry near-zero inline test; the test
> code is in `*/tests.rs` siblings). Recommendations below target the crates that
> still carry heavy inline `#[cfg(test)]` blocks.

### 1.2 Extraction targets (heavy inline-test, NOT yet extracted)

Each row: the production file, its inline `#[cfg(test)] mod tests { … }` block (the
form to convert to `mod tests;` + sibling `<module>/tests.rs`), inline-test LOC and
post-extraction production LOC (both from `audits/loc-s87.md` §2), and effort. Effort
is **S** for all of these because the extraction is purely mechanical: move the block
body to `<module>/tests.rs`, change `mod tests { … }` to `mod tests;`. The only care
needed is `use super::*;` / visibility (the sibling needs `pub(crate)` reach the
inline block had via `super`, which typecheck's existing siblings already demonstrate).

| Crate | File | inline-test block start | inline-test LOC | post-extract prod LOC | extracted? | effort |
|---|---|---|--:|--:|---|:--:|
| **backend** | `lib.rs` | **L1410** (`#[cfg(test)]`) | **4202** | **647** | inline `mod`s — **NO** | S |
| frontend | `ast_builder.rs` | L1768 (`mod tests {`) | 1830 | 1211 | inline `mod` — NO | S |
| src | `worker.rs` | (inline) | 1093 | 749 | inline — NO | S |
| src | `session_v4.rs` | L2302 / L2955 / L3627 (several blocks) | 807 | 1428 | inline — NO | S |
| frontend | `reader.rs` | L961 (`mod tests {`) | 585 | 1109 | inline `mod` — NO | S |
| intrinsics | `trace.rs` | (inline) | 515 | 409 | inline — NO | S |
| src | `observability.rs` | (inline) | 546 | 318 | inline — NO | S |
| backend | `jit.rs` | (inline) | 657 | 464 | inline — NO | S |
| src | `scheduler.rs` | L1802 (`mod tests {`) | 446 | 1047 | inline `mod` — NO | S |
| src | `process_form.rs` | L3208 (`mod tests {`) | 369 | 1765 | inline `mod` — NO | S |
| intrinsics | `io.rs` | (inline) | 456 | 335 | inline — NO | S |
| typecheck | `adt.rs` | (inline) | 1042 | 514 | inline — NO | S |
| typecheck | `form.rs` | (inline) | 643 | 243 | inline — NO | S |
| types | `module.rs` | (inline) | 852 | 685 | inline — NO | S |
| intrinsics | `drop.rs` | (inline) | 448 | 185 | inline — NO | S |

> The list above is the heavy hitters (inline-test ≥ ~370 LOC). Many smaller modules
> across `intrinsics` (the 59%-test crate), `primitives`, and `types` also carry inline
> blocks worth converting opportunistically, but the table captures where the
> navigability win is largest.

**Crates that ALREADY follow the convention — do NOT re-do.**

- **`cranelisp-typecheck` — fully migrated.** Its four densest production modules
  (`program.rs`, `traits.rs`, `checker.rs`, `infer.rs`) carry near-zero inline test
  (13, 13, 65, 2 LOC respectively). `traits.rs` declares **two** siblings
  (`#[cfg(test)] mod tests;` at L2710 and `#[cfg(test)] mod primitive_dispatch_tests;`
  at L1281); `program.rs`, `infer.rs`, `checker.rs` each declare `mod tests;` (+
  `checker` a `test_support;` sibling). These are the reference implementation of the
  convention — **leave them**. (`adt.rs` and `form.rs` in this crate are the exceptions
  that still carry inline blocks; they are in the table above.)

### 1.3 Aggregate payoff

**Headline.** `cranelisp-backend/lib.rs` is the single largest file in the workspace
at **6,785 raw lines**, of which production code is only lines 1–~1408. Converting its
inline test region (starting L1410) to a `lib/tests.rs` sibling collapses the *apparent*
file from 6,785 lines to ~1,408 — a **~79% navigability reduction on the workspace's
biggest file**, with zero behavioural change. Anyone opening `lib.rs` today scrolls
past ~5,400 lines of tests to read ~1,400 lines of `compile_to_module` orchestration.

**Workspace aggregate.** Summing the inline-test LOC across the table (~13,500 LOC of
the ~38,635 total inline-test LOC) and the longer tail, the extraction moves on the
order of **15,000–20,000 LOC of test code out of production files** into siblings —
without deleting or rewriting a line. The corrected production-LOC figures in
`loc-s87.md` already *net out* these tests; this Part-1 work makes the **file sizes on
disk match the corrected figures**, so a future reader (or a future LOC pass) sees the
true production size without needing the three-column correction at all.

**Why it matters beyond cosmetics.**
- **Review grain.** A `/review` change-set diff that touches production logic no longer
  drags a 4,000-line test block into the reviewer's context window.
- **Edit safety.** The project's "single agent, one working tree" constraint
  (`CLAUDE.md` §Testing) means large files are higher-risk to edit concurrently;
  smaller production files reduce the merge/clobber surface.
- **Compile feedback.** Editing a test in a 6,785-line file recompiles the whole TU;
  a sibling `tests.rs` is a separate `#[cfg(test)]` module — incremental rebuilds are
  tighter.
- **It is the cheapest maintainability win available.** All-S effort, mechanical,
  no design risk. This is the recommended first move of any decomposition sprint —
  do the test extractions before the Part-2 untangling, because the smaller production
  files make the Part-2 work legible.

---

## Part 2 — Oversized production-module decomposition

> **Methodology + caveat.** Sizes are the **corrected** non-test LOC from
> `audits/loc-s87.md`. Concerns, line ranges, and function lengths were surveyed by
> read-only structural passes over each file (note: surveyed line ranges are raw file
> lines, which run higher than the tokei corrected count because tokei excludes blanks
> and comments). **Two survey claims were checked against source and corrected** before
> inclusion: (a) the alleged "session_v4.rs slash-command handlers are a byte-identical
> duplicate of repl.rs" is **FALSE** — the `handle_*` methods live *only* in `repl.rs`
> (verified by grep); the survey confused impl-block line spans. (b) the alleged
> `checker.rs::fresh_instantiation_subst` "552-line god function" is **FALSE** — it is
> ~16 lines (L1686–1702); the survey miscounted to file-end. Both are excluded below.
>
> Effort/risk: **S** = mechanical extract (move cohesive block, fix `use`/visibility);
> **M** = extract with some shared-state threading; **L** = genuine untangle (state is
> interleaved, needs a context struct or careful ordering).

### Confirmed over-budget functions (the `src/CLAUDE.md` ~100-line ceiling)

These are the worst offenders against the documented "Max ~100 lines per function"
rule, verified in source:

| Function | Location | ~Length | Note |
|---|---|--:|---|
| `monomorphise_call` | `typecheck/traits.rs:1372` | ~307L | known; verified L1372→1679 |
| `finalize_check_result_inner` | `typecheck/program.rs:1776` | ~332L | verified L1776→2108 |
| `compile_to_module_impl` | `backend/lib.rs:755` | ~304L | within `compile_to_module` |
| `compile_resolved_call` | `backend/compiler/apply.rs:136` | ~271L | known; not in the top-12 file list (`apply.rs` is 575 corrected) |
| `check_form_body_single_defn` | `typecheck/program.rs:918` | ~283L | per-form single-defn body check |
| `try_cache_hit_load` | `src/process_form.rs:1829` | ~254L | known; cache restore + transitive import walk |
| `compile_par_bind_continuation` | `backend/compiler/control_flow.rs:401` | ~230L | par-bind IO continuation inner fn |
| `build_method_type` | `typecheck/traits.rs:362` | ~214L | trait method type builder |
| `check_form_body_multi_sig` | `typecheck/program.rs:1201` | ~209L | per-form multi-sig body check |
| `compile_auto_curry` | `backend/compiler/control_flow.rs:1585` | ~199L | auto-curry codegen |
| `process_regular_form` | `src/process_form.rs:1318` | ~192L | per-form expand-then-check driver |
| `register_defn_signature` | `typecheck/program.rs:2651` | ~164L | signature registration |
| `build_adt_drop_glue_fn` | `backend/compiler/vec_codegen.rs:912` | ~167L | ADT drop-glue generation |
| `check_hkt_impl_method` | `typecheck/traits.rs:919` | ~309L | HKT impl-method check |
| `CompilerSession::new` | `src/session_v4.rs` | ~216L | known; session construction |
| `compile_lambda_body` | `backend/compiler/control_flow.rs:1011` | ~149L | inner-fn compilation |

---

### 2.1 `typecheck/program.rs` — corrected 1966 (#1)

**Tangled concerns** (one file owns the entire program-level inference lifecycle):
- AST annotation / call-graph helpers (~L1–330) — `annotate_expr_from_maps` (~101L),
  callee writeback, substitution traversals.
- Per-form typecheck API types + multi-sig name-mangling (~L331–631).
- Per-form body dispatchers (~L667–1250) — `check_form_body_single_defn` (~283L),
  `check_form_body_multi_sig` (~209L).
- Multi-sig / overload resolution (~L1250–1475).
- Post-check finalization (~L1472–2108) — `finalize_check_result_inner` (~332L),
  `regeneralize_defn_schemes` (~124L), `register_defn_signature` (~164L).
- Monomorphisation pass-4 (~L3022–3264) — `pass4_monomorphise` (~242L).

**Proposed decomposition** (`program/` subdir):
- `program/annotation.rs` — AST post-pass annotation + substitution traversal helpers.
- `program/form_check.rs` — `check_form_body_single_defn` / `_multi_sig` + dispatchers.
- `program/overload.rs` — multi-sig name mangling + overload resolution.
- `program/finalize.rs` — `finalize_check_result_inner` (decompose first) + regeneralize + register.
- `program/monomorphise.rs` — `pass4_monomorphise`.

**Worst functions:** `finalize_check_result_inner` (~332L), `check_form_body_single_defn`
(~283L), `pass4_monomorphise` (~242L), `check_form_body_multi_sig` (~209L).

**Effort/risk: L.** These passes thread `CheckState` + symbol-table mutation; the split
is a genuine untangle, but the concerns are conceptually distinct (annotate / check /
finalize / mono are sequential phases), so the cut lines are clear once
`finalize_check_result_inner` is itself decomposed.

### 2.2 `src/process_form.rs` — corrected 1765 (#2)

**Tangled concerns:**
- `SymbolTableMacroResolver` + recognition/on-demand-compile pipeline (~L61–500).
- Macro-clause compilation adapters (`_with_state` / `_inline` → `_core`) (~L332–500).
- Form classification + Pass-0 structural peel (`classify_form` ~127L) (~L640–851).
- Cluster core: `process_cluster_once` (~148L), Pass-1/2 (~L852–1248).
- Per-form / cross-form handlers (import/export/mod/platform/file-IO) (~L1318–2607),
  incl. `process_regular_form` (~192L), `try_cache_hit_load` (~254L).
- `wrap_exprs_as_defns` (large utility; survey flagged it long).

**Proposed decomposition** (`process_form/` subdir):
- `process_form/macro_resolution.rs` — `SymbolTableMacroResolver`, recognize + on-demand compile.
- `process_form/macro_clause.rs` — the clause-compile adapters + `_core`.
- `process_form/form_dispatch.rs` — `classify_form`, structural handlers, per-form handlers.
- `process_form/cluster.rs` — `process_cluster_once`, Pass-0/1/2, `finalize_cluster`.
- `process_form/cache_restore.rs` — `try_cache_hit_load` + transitive import walk.

**Worst functions:** `try_cache_hit_load` (~254L), `process_regular_form` (~192L),
`process_cluster_once` (~148L), `classify_form` (~127L), `wrap_exprs_as_defns` (long).

**Effort/risk: M.** Mostly cohesive blocks; macro-resolution and cache-restore lift
out cleanly. The cluster core stays the spine and threads the most state.

### 2.3 `typecheck/traits.rs` — corrected 1718 (#3)

**Tangled concerns** (~1% inline test — almost pure production, the densest read):
- Trait registry + active-constraints tracking (~L24–120).
- Trait/HKT registration + `build_method_type` (~214L) (~L125–390).
- Impl + method checking (~L396–1015) — `check_impl_method_with_sig` (~173L),
  `check_hkt_impl_method` (~309L).
- Method resolution / dispatch + primitive dispatch table (~L1115–1263).
- **`monomorphise_call` (~307L)** (~L1372–1679) — the known god function.
- Type-resolution helpers (`resolve_trait_type_expr`, HKT variants — 3 near-dup) (~L2202–2710).

**Proposed decomposition** (`traits/` subdir; `tests`/`primitive_dispatch_tests`
siblings already exist):
- `traits/registry.rs` — trait/HKT registration, `build_method_type`, active constraints.
- `traits/impl_check.rs` — `check_impl_method_with_sig` + `check_hkt_impl_method` (split single vs HKT).
- `traits/dispatch.rs` — method resolution + primitive dispatch table.
- `traits/monomorphise.rs` — `monomorphise_call` + internals.
- `traits/type_resolve.rs` — the 3 `resolve_*_type_expr` variants (consolidate the duplication).

**Worst functions:** `monomorphise_call` (~307L), `check_hkt_impl_method` (~309L),
`build_method_type` (~214L), `check_impl_method_with_sig` (~173L).

**Effort/risk: L.** Highest-density file in the workspace; `monomorphise_call` is
documented as load-bearing. Untangle, not mechanical extract — touches trait-dispatch
semantics. **Highest-risk item in the backlog.**

### 2.4 `src/repl.rs` — corrected 1645 (#4)

**Tangled concerns** — one giant `impl CompilerSession` block hosting the entire
slash-command + introspection-display suite (~L290–end). Distinct responsibilities:
- Slash-command parse + dispatch router (`parse_slash_command`, `dispatch_command`).
- Introspection display formatters (`format_*` free fns, `format_overloaded_variants`).
- `describe_symbol` / `collect_related` / prelude-fallback lookup.
- ~20 `handle_*` command bodies (`/sig`, `/doc`, `/list`, `/mod`, `/source`, `/sexp`,
  `/ast`, `/clif`, `/disasm`, `/info`, `/type`, `/imports`, `/exports`, `/expand`,
  `/time`, `/mem`, `/run-tests`, `/platform-schema`).

**Duplication (verified pattern):** the current→prelude-fallback→root lookup walk is
repeated across `describe_symbol`, `handle_doc`, and the lookup helpers — a candidate
for one shared `lookup_with_prelude_fallback` (Principle 7).

**Proposed decomposition** (`repl/` subdir):
- `repl/command.rs` — `ReplCommand`, `parse_slash_command`, `dispatch_command`.
- `repl/display.rs` — `format_*` free fns + scheme/overload/docstring formatters.
- `repl/introspect.rs` — `describe_symbol`, `collect_related`, the shared fallback lookup.
- `repl/handlers.rs` — the `handle_*` bodies (or split query- vs list- vs eval-handlers).

**Worst functions:** survey flagged the impl block as a god-impl (~2300 raw lines);
no single body confirmed >200L, but several `handle_*` + `describe_symbol` exceed 100L.

**Effort/risk: M.** The handlers are `impl CompilerSession` blocks in a sibling module
already (per `src/CLAUDE.md` §Session/REPL decomposition); splitting further is more
of the same `pub(crate)`-field pattern — mechanical, but many call sites.

### 2.5 `backend/compiler/control_flow.rs` — corrected 1463 (#5)

**Tangled concerns** (0% inline test — dense codegen):
- Let codegen (sequential + lenient IVar fork-join) (~L25–206).
- If codegen (~L634–674).
- Lambda codegen + body + drop-glue (~L686–1159) — `compile_lambda_body` (~149L),
  `build_closure_drop_glue` (~112L).
- ParBind IO scheduling (~L306–630) — `compile_par_bind_continuation` (~230L).
- Function-as-value wrappers + auto-curry (~L1180–1783) —
  `compile_trait_method_as_value` (~117L), `compile_auto_curry` (~199L).

**Duplication (audit-relevant — `sketch/audits/codegen.md` heap-classification):** the
RC-inc-for-captures pattern (`signature_heap_category(ty)` → match `AlwaysHeap`/`Mixed`/
`NeverHeap` → `emit_rc_inc[_guarded]`) recurs at **4 sites** (`compile_lambda` ~813,
`compile_par_bind_continuation` ~614, `emit_capture_return_inc` ~997,
`compile_lambda_body` ~1076). Extract one `emit_capture_inc(category)` helper. This is
exactly the HIGH-severity "duplicate heap classification" pattern the audits warn about.

**Proposed decomposition** (`control_flow/` subdir):
- `control_flow/let_if.rs`, `control_flow/lambda.rs`, `control_flow/par_bind.rs`,
  `control_flow/fn_as_value.rs` (incl. auto-curry), `control_flow/drop_glue.rs`,
  plus a shared `capture_rc.rs` for the deduplicated capture-inc helper.

**Worst functions:** `compile_par_bind_continuation` (~230L), `compile_auto_curry`
(~199L), `compile_lambda_body` (~149L), `compile_trait_method_as_value` (~117L),
`build_closure_drop_glue` (~112L).

**Effort/risk: M.** Concern-per-function structure is already clean; the split is
mostly mechanical once the shared capture-inc helper is factored out (the only genuine
untangle is the 4-site dedup).

### 2.6 `src/session_v4.rs` — corrected 1428 (#6)

**Tangled concerns:**
- `RunMode` / `SessionSettings` / `CommandResult` / `EvalResult` + `parens_balanced` (~L82–263).
- `TypecheckProduct` / `Introspection` DTOs (~L269–351).
- `SharedState` (14+ fields) struct + init (~L357–603).
- `CompilerSession` struct + lifecycle: **`new` (~216L)**, accessors, module-intro gate (~L627–1126).
- Introspection read-side accessors (~L1201–1377).
- Nice-worker spawn + `compile_module_object` (~309L) (~L2402–2791).
- `TestRunnerState` + `discover_tests_extern` + `test_scheme_is_eligible` (~L2792–2939).

**Proposed decomposition** (`session_v4/` subdir):
- `session_v4/types.rs` — `RunMode`/`SessionSettings`/`EvalResult`/`parens_balanced`/DTOs.
- `session_v4/shared_state.rs` — `SharedState` + construction.
- `session_v4/lifecycle.rs` — `CompilerSession` struct + `new` (decompose first) + accessors.
- `session_v4/nice_worker.rs` — spawn + `compile_module_object`.
- `session_v4/test_runner.rs` — `TestRunnerState` + discovery + eligibility.

**Worst functions:** `compile_module_object` (~309L), `CompilerSession::new` (~216L).

**Effort/risk: M.** `new` is a long-but-linear constructor; `compile_module_object` is
a cohesive codegen routine. The DTO and test-runner cuts are S; the lifecycle cut is M.

### 2.7 `backend/compiler/mod.rs` — corrected 1279 (#7)

**Tangled concerns:**
- 5 free-fn resolvers (`resolve_got_target` ~107L, `resolve_platform_effect_target`
  ~89L, `resolve_extern_target` ~88L, `resolve_func_arity` ~87L) (~L100–555).
- `CompileContext` struct + constructor-metadata lookups (~L607–816).
- `FnCompiler` struct (88-line struct def, ~75 fields) + lifecycle (~L849–977).
- `FnCompiler` impl: `compile_body` (~116L), scope mgmt, RC emission (~L1005–1900).

**Duplication (verified):** the import-chain walk (`MAX_IMPORT_DEPTH` → `symbol_tables.get()`
→ match entry → recurse on `Import`) is copy-pasted as a nested fn at **4 sites**
(`resolve_in_module` ×2, `probe`, `arity_in_module`). Collapse to one generic
`resolve_chain<F>(filter: F)`. **Plus** the `signature_heap_category` → 3-arm match
recurs at 8+ sites here too (same audit pattern as 2.5).

**Proposed decomposition** (`compiler/mod.rs` → keep slim re-export hub + submodules):
- `compiler/resolution.rs` — the 5 resolvers + one shared `resolve_chain` walker.
- `compiler/context.rs` — `CompileContext` + ctor-metadata.
- `compiler/fn_compiler.rs` — `FnCompiler` struct + lifecycle + `compile_body` + scope mgmt.
- `compiler/rc_emission.rs` — `emit_*` RC/drop-glue helpers (single home for heap-class match).

**Worst functions:** `compile_body` (~116L), `resolve_got_target` (~107L).

**Effort/risk: M.** The resolver dedup is a clear win (4→1). `FnCompiler`'s ~75-field
struct is the harder part — its impl methods are tightly coupled to the field set, so
the split is "move impl blocks to sibling files on the same struct" rather than a true
responsibility carve. Flag the field count to `/arch` (god-object risk per
`sketch/audits/module.md`).

### 2.8 `frontend/ast_builder.rs` — corrected 1211 (#8)

**Tangled concerns:**
- Error/name helpers (~L45–140).
- Public API `build_form` (~107L) / `build_forms` (~L147–372).
- Per-shape parsers: defn/deftype/deftrait/impl/defmacro (~L410–1045) —
  `build_method_sig` (~130L).
- Expression builders + annotation-aware building (~L1050–1680).

**Duplication:** sexp structure-match-then-dispatch recurs at 4 sites
(`build_form`, `build_list_expr`, `build_impl_target`, `build_pattern`); the
`try_consume_annotation` + `build_one_expr_at` pattern recurs 6+ times. Field/param
bracket-extraction `while i < items.len()` loops recur 5+ times.

**Proposed decomposition** (`ast_builder/` subdir):
- `ast_builder/decls.rs` — defn/deftype/deftrait/impl/defmacro parsers.
- `ast_builder/exprs.rs` — `build_expr` dispatch + let/if/fn/match/vec/trace.
- `ast_builder/annotations.rs` — annotation-aware building + the shared
  `try_consume_annotation` helper.
- `ast_builder/helpers.rs` — sexp expect/extract + the shared bracket-extraction loop.
- **First do the test extraction** (1830 inline-test LOC, L1768) — this alone halves
  the file.

**Worst functions:** `build_method_sig` (~130L), `build_form` (~107L).

**Effort/risk: S–M.** Test extraction is S; the parser split is M (the shared
annotation/bracket helpers want extraction first to avoid re-duplicating).

### 2.9 `frontend/reader.rs` — corrected 1109 (#9)

**Tangled concerns:**
- Reader state/API + whitespace/comment + char classification (~L13–231).
- Tokenizers: strings, numbers, `+`/`-` disambiguation (~L297–553).
- **Symbol + qualified/dotted/module-path reading** (~L555–804) — the concentration:
  `read_symbol_or_keyword` (~80L) and `read_qualified_tail` (~57L) implement
  **near-duplicate** lookahead state machines for `module.seg.../local`.
- Reader macros (quote family) + gensym/percent/ampersand (~L825–955).

**Duplication:** the dotted-module-path vs dotted-symbol lookahead loop is duplicated
across `read_symbol_or_keyword` and `read_qualified_tail`; position save/restore for
backtracking recurs 6+ times.

**Proposed decomposition** (`reader/` subdir):
- `reader/scan.rs` — state, whitespace/comment, char classification.
- `reader/tokens.rs` — strings, numbers, operators.
- `reader/symbols.rs` — symbol/qualified/dotted reading, **refactored to one lookahead
  routine** (the genuine untangle).
- `reader/macros.rs` — quote family + gensym.
- **First do the test extraction** (585 inline-test LOC, L961).

**Worst functions:** none over 100L; the problem is *fragmentation* + duplication, not
a single god function.

**Effort/risk: M.** Test extraction S; the symbol-reading dedup is the M-risk untangle
(backtracking state machines are subtle — needs the reader test suite green throughout).

### 2.10 `typecheck/checker.rs` — corrected 1095 (#10)

**Tangled concerns** (~6% inline test; `checker/tests.rs` + `test_support.rs` siblings exist):
- State types + defaults (~L107–212).
- Module read/mut views + symbol-table access (5+ near-identical staging-aware accessors) (~L344–605).
- Bare-name resolution + prelude fallback (the 6+ chokepoints `src/CLAUDE.md` describes)
  (~L862–1072) — `lookup_in_current_module` (~129L).
- Qualified-name resolution (~L1143–1400) — `resolve_fq_symbol` (~130L).
- Fresh-variable / instantiation helpers (~L1686+). *(Note: the survey's "552-line
  `fresh_instantiation_subst`" is wrong — it is ~16L; the region is many small fns.)*

**Duplication (verified against `src/CLAUDE.md`):** the "inner miss → try prelude →
public-filter" walk recurs at the 6+ bare-name chokepoints; chain-follow entry
resolution (`resolve_entry_in_module` / `resolve_terminal_entry_and_home` /
`probe_module_entry_owned`) recurs as 3 variants. Single-source candidate (Principle 7).

**Proposed decomposition** (`checker/` subdir):
- `checker/state.rs` — state types + defaults.
- `checker/access.rs` — module views + the staging-aware accessors (dedup the 5).
- `checker/resolve_bare.rs` — prelude-fallback chokepoints (extract one shared gate).
- `checker/resolve_qualified.rs` — `resolve_fq_symbol` + chain-follow (dedup the 3).

**Worst functions:** `resolve_fq_symbol` (~130L), `lookup_in_current_module` (~129L).

**Effort/risk: M.** The prelude-fallback dedup is the high-leverage piece and is
explicitly load-bearing (S78 outer-scope model) — careful but well-documented.

### 2.11 `backend/compiler/vec_codegen.rs` — corrected 1026 (#12)

**Tangled concerns:**
- Vec literal + op dispatch + get (~L43–224).
- Vec-set (incl. COW fast-path ~115L) + vec-push (COW ~92L) (~L236–596).
- Element inc/dec fn generation + **`build_adt_drop_glue_fn` (~167L)** (~L754–1078).
- Element RC helpers + extern-call wrappers (~L600–1295).
- `emit_vec_rc_dec_with_drop` (long; survey truncated, likely >100L) (~L1319+).

**Duplication (verified):** `emit_extern_call_*` exists as **3 near-identical variants**
(2/3/4 args, L1210–1295) — replace with one `emit_extern_call_n(name, &[Value])` or a
macro. The vec-op RC-guard (`element_consuming_inc` decision) recurs at 3 sites.

**Proposed decomposition** (`vec_codegen/` subdir):
- `vec_codegen/ops.rs` — lit/get/set/push + dispatch.
- `vec_codegen/drop_glue.rs` — elem inc/dec fns, `build_adt_drop_glue_fn`,
  `emit_vec_rc_dec_with_drop`.
- `vec_codegen/extern_calls.rs` — the deduplicated `emit_extern_call_n`.

**Worst functions:** `build_adt_drop_glue_fn` (~167L), `emit_vec_rc_dec_with_drop`
(~160L+), `compile_vec_set_cow` (~115L).

**Effort/risk: M.** Extern-call dedup is S and high-value; drop-glue split is M.

### 2.x `src/scheduler.rs` — corrected 1047 (#11, summarized)

One ~1409-line `impl CompileScheduler` block holds registration, priority-worker
interface, notification/blocking kernel, nice-worker interface, and query accessors.
The duplication signal: `if let Some(ms) = state.modules.get_mut(&module) { … }` recurs
~17 times (small flag-set bodies) and the `drop(state); self.condvar.notify_all();`
release idiom recurs ~8 times. **Decomposition:** split the impl into sibling modules
`scheduler/registration.rs`, `scheduler/notify.rs` (notify_* + block/unblock/wait kernel),
`scheduler/workers.rs` (priority + nice interfaces), `scheduler/query.rs`. **Effort/risk:
M** — the notify/block kernel is the concurrency core and must move as one cohesive unit
(do not split block/notify/wait across files). No single function confirmed >150L;
the issue is impl-block size + the get_mut idiom repetition (consider a
`with_module_state(module, |ms| …)` helper to collapse the 17 sites).

---

## Part 3 — Prioritized maintainability backlog

Ordered by **leverage = LOC-moved/clarified × touch-frequency**, with effort/risk.
Touch-frequency is judged from `src/CLAUDE.md` (the pipeline-orchestration core and
codegen hot files are edited every sprint) and the defect history (the typecheck
trait/program files and the cluster orchestrator carry recurring defect campaigns).

| # | Item | Kind | LOC moved | Touch-freq | Effort | Risk | Leverage |
|---|---|---|--:|:--:|:--:|:--:|:--:|
| 1 | **Extract `backend/lib.rs` tests → `lib/tests.rs`** | test-extract | ~4200 | high | S | none | **highest** |
| 2 | Extract `frontend/ast_builder.rs` tests → sibling | test-extract | ~1830 | high | S | none | very high |
| 3 | Extract remaining src/ inline tests (`worker`, `session_v4`, `scheduler`, `process_form`, `observability`) | test-extract | ~3260 | high | S | none | very high |
| 4 | Extract `frontend/reader.rs` tests → sibling | test-extract | ~585 | med | S | none | high |
| 5 | Extract intrinsics inline tests (`trace`, `io`, `drop`, …) | test-extract | ~1900 | low | S | none | med |
| 6 | Dedup 4-site import-chain walker in `backend/compiler/mod.rs` → `resolve_chain` | dedup | ~120 | high | S | low | high |
| 7 | Dedup 3-site `emit_extern_call_*` in `vec_codegen.rs` → `emit_extern_call_n` | dedup | ~60 | med | S | low | high |
| 8 | Dedup 4-site capture-RC-inc in `control_flow.rs` → `emit_capture_inc` (heap-class single source) | dedup | ~40 | high | S | low | high |
| 9 | Dedup prelude-fallback walk in `checker.rs` + `repl.rs` → one shared gate | dedup | ~80 | high | M | med | high |
| 10 | Decompose `src/process_form.rs` (cluster / macro-res / cache-restore) | decompose | ~1765 | high | M | med | high |
| 11 | Decompose `src/session_v4.rs` (types / shared_state / lifecycle / test_runner) | decompose | ~1428 | high | M | med | high |
| 12 | Decompose `src/repl.rs` (command / display / introspect / handlers) | decompose | ~1645 | high | M | med | med-high |
| 13 | Decompose `backend/compiler/control_flow.rs` (let_if / lambda / par_bind / fn_as_value / drop_glue) | decompose | ~1463 | high | M | med | med-high |
| 14 | Decompose `backend/compiler/mod.rs` (resolution / context / fn_compiler / rc_emission) | decompose | ~1279 | high | M | med | med-high |
| 15 | Decompose `typecheck/program.rs` (annotation / form_check / finalize / monomorphise) | decompose | ~1966 | high | L | med | med |
| 16 | Decompose `backend/compiler/vec_codegen.rs` (ops / drop_glue / extern_calls) | decompose | ~1026 | med | M | med | med |
| 17 | Decompose `src/scheduler.rs` (registration / notify / workers / query) | decompose | ~1047 | med | M | med | med |
| 18 | Decompose `frontend/ast_builder.rs` (decls / exprs / annotations / helpers) | decompose | ~1211 | med | M | low | med |
| 19 | Decompose `frontend/reader.rs` + dedup symbol lookahead | decompose+dedup | ~1109 | med | M | med | med |
| 20 | Decompose `typecheck/checker.rs` (state / access / resolve_bare / resolve_qualified) | decompose | ~1095 | high | M | med | med |
| 21 | **Decompose `typecheck/traits.rs` (registry / impl_check / dispatch / monomorphise / type_resolve)** | decompose | ~1718 | high | L | **high** | med (high-risk) |

### Recommended sequencing for the scope-decision gate

1. **Do ALL test extractions first (items 1–5, all S, zero behavioural risk).** This
   is the cheapest ~12k-LOC clarity win in the project and makes every subsequent
   decomposition legible. It can land as one mechanical change-set per crate.
2. **Then the four S-effort dedups (items 6–8 + the M item 9).** Each removes a
   recurring-defect-class pattern (`sketch/audits/codegen.md` heap-classification;
   `Principle 7` single-source). High leverage per line touched.
3. **Then the M-effort src/ and backend decompositions (items 10–14, 16–20)** as the
   per-sprint capacity allows — these are the pipeline/codegen hot files, so the
   navigability dividend compounds.
4. **Defer the two L-risk typecheck untangles (items 15, 21) to a dedicated wave.**
   `traits.rs` (item 21) is the single highest-risk item: ~1% test coverage inline,
   the densest production logic in the workspace, and `monomorphise_call` is documented
   as load-bearing. It should NOT be attempted opportunistically — it wants its own
   change-set with the typecheck sibling test suite (`traits/tests.rs`) green
   throughout, and a `/design` pass first.

### Findings routing (advisory — `/review` files no edits)

Per `/review` boundary, these become FIXMEs at sprint planning:
- Items 1–8, 10–20 → `target: /dev` (implementation/structure).
- Item 9 (shared prelude-fallback gate) → `target: /dev`, but note the S78 outer-scope
  model is `/arch`-adjacent — flag for `/arch` awareness.
- `backend/compiler/mod.rs` `FnCompiler` ~75-field struct → `target: /arch` (god-object
  watch per `sketch/audits/module.md` `CompiledModule` precedent).
- Items 15, 21 (typecheck untangles) → `target: /design` first (decomposition plan),
  then `target: /dev`.

### Two survey claims rejected (recorded for honesty)

- **"session_v4.rs duplicates repl.rs slash-command handlers byte-for-byte"** —
  **FALSE.** `grep` confirms `handle_sig/doc/list/mod/imports` exist only in `repl.rs`.
  No duplication finding filed.
- **"`checker.rs::fresh_instantiation_subst` is a 552-line god function"** — **FALSE.**
  It is ~16 lines (L1686–1702). Removed from the over-budget list.
