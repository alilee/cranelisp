# cranelisp-typecheck audit — 2026-04-23

## Scope and method

This audit reviews `crates/cranelisp-typecheck/src` for **clarity**, **simplicity**, and **avoidance of duplicated code / duplicated code-paths**, with the goal of assessing **maintainability** and **extensibility**.

The review is based on direct source inspection plus lightweight structural metrics.

### Snapshot metrics

- Production Rust in crate: **~8,360 LOC**
- Tests co-located in the same source files: **~12,011 LOC**
- Largest production files:
  - `program.rs` — **2,815 LOC** (**33.7%** of production code)
  - `traits.rs` — **1,839 LOC** (**22.0%**)
  - `builtins.rs` — **1,218 LOC** (**14.6%**)
  - `infer.rs` — **849 LOC**
  - `checker.rs` — **812 LOC**
- Top 3 files contain **~70%** of production code; top 5 contain **~90%**
- Production functions ≥ 60 lines: **10**
- `ModuleEntry::Def { ... }` is constructed **132 times** across the crate

## Executive summary

This crate has a **good architectural core** but is carrying **too much structural weight in a few files**.

The strongest qualities are:
- a clear split between **shared environment** and **per-check transient state** (`TypeCheckEnv` vs `CheckState`)
- good local comments and invariant notes
- sensible smaller modules for foundational concerns (`unify.rs`, `resolve.rs`, `scope.rs`, `adt.rs`)
- `infer.rs` largely follows the desired “one method per `Expr` variant” style

The main maintainability risks are:
1. **parallel / legacy code-paths still live in production files**, especially in `program.rs`
2. **expression walking and annotation logic is duplicated in several places**
3. **symbol-table entry construction is repeated manually**, making invariant drift likely
4. **many lookups scan every loaded module**, which is simple locally but spreads lookup logic and weakens extensibility
5. **large mixed production+test files reduce navigability**, especially for agent-driven editing

Overall assessment:
- **Clarity:** moderate-good locally, weaker at crate scale
- **Simplicity:** moderate; core ideas are simple, but the control flow around program checking and trait handling is not
- **Duplication:** the largest active issue
- **Maintainability trajectory:** good if duplication is reduced soon; otherwise likely to degrade as new features land

## What is working well

### 1. State separation is strong
`checker.rs` establishes a useful split:
- `TypeCheckEnv` holds shared, long-lived state
- `CheckState` holds transient inference state

That is a maintainable foundation. It keeps the typechecker conceptually decomposed and makes concurrency boundaries explicit.

### 2. Several small modules are clean and understandable
`unify.rs`, `resolve.rs`, `scope.rs`, and much of `adt.rs` are compact and easy to reason about. They are the clearest parts of the crate and are good models for future work.

### 3. The newer per-form pipeline is directionally correct
`program.rs`’s `check_form` / accumulator / finalize structure is substantially clearer than a single monolithic “check everything” function. The issue is not that this direction is wrong; it is that the older paths still remain nearby.

## Findings

### Finding 1 — `program.rs` still contains multiple effective pipelines
**Impact:** High

`program.rs` contains the new path:
- `check()` / `check_inner()`
- `check_form_*()`
- `finalize_check_result_*()`

But it also still contains deprecated compatibility paths:
- `check_program()` / `check_program_inner()`
- `check_repl_input()` / `check_repl_input_inner()`

These are not tiny shims. They carry real logic for registration, body checking, monomorphisation, AST annotation, REPL result building, and multi-sig handling.

Representative locations:
- new path: `program.rs:527-1270`
- deprecated batch path: `program.rs:1784-1922`
- deprecated REPL path: `program.rs:1925-2025`

This is the single biggest maintainability issue in the crate because it creates a standing question for every change:
> “Do I need to patch one path or three?”

Even when comments say the old path is test-only, the code is still production-visible and still expensive to reason about.

**Why it matters**
- increases change surface
- encourages drift between code-paths
- makes regression fixes slower
- creates an easy trap for agents to edit the wrong entry point

**Recommended remediation**
- Make `check()` the only authoritative implementation.
- Move `check_program*` / `check_repl_input*` into a thin compatibility layer or test-only adapter.
- Convert remaining tests to drive `check()` / `check_form()` directly.

This should be the **highest-priority cleanup**.

---

### Finding 2 — expression-tree traversal is duplicated across the crate
**Impact:** High

There are multiple recursive walkers over `Expr`, each hand-maintained:
- `apply_subst_to_expr` — `program.rs:42`
- `annotate_expr_from_maps` — `program.rs:106`
- `collect_constrained_calls` — `program.rs:2682`
- `resolve_deferred_trait_calls` — `infer.rs:495`
- additional similar walkers exist in tests and helper code

These walkers are reasonable in isolation, but together they create a classic extensibility trap: when a new `Expr` variant is added, multiple functions across multiple files must be updated correctly.

**Why it matters**
- duplicated recursion logic is easy to miss during feature work
- variant coverage can silently drift
- maintenance cost rises with every new syntax form

**Recommended remediation**
- Introduce a small shared traversal utility for `Expr`:
  - either a visitor-style helper
  - or a `walk_expr_children` helper used by all recursive passes
- Keep specialized logic local, but centralize the child traversal shape

This would reduce duplicated code and make new expression forms safer to add.

---

### Finding 3 — `traits.rs` contains parallel non-HKT and HKT impl-method flows with duplicated tails
**Impact:** High

`traits.rs` has a large amount of shared logic between:
- `check_impl_method_with_sig` (`traits.rs:547`)
- `check_hkt_impl_method` (`traits.rs:719`)

The front half differs for legitimate type-resolution reasons, but the back half is almost the same:
- snapshot side maps
- check body
- resolve auto-curry
- build mangled name
- extract deltas
- annotate clone
- write/update `ModuleEntry::Def.ast`
- create concrete symbol-table entry if missing

This is duplicated code in one of the crate’s most complex areas.

**Why it matters**
- fixes in impl-method handling must be applied twice
- bug-fix asymmetry is likely
- HKT work becomes harder to extend because the shared flow is obscured

**Recommended remediation**
- Factor the common “checked impl method → annotated symbol-table entry” tail into one helper.
- Keep only the type-resolution front half separate.

This is the **second highest-impact cleanup** after the pipeline consolidation in `program.rs`.

---

### Finding 4 — symbol-table entry construction is too manual and too repeated
**Impact:** Medium-High

The crate constructs `ModuleEntry::Def { ... }` manually in many places (**132 occurrences**). Repeated fields include:
- `visibility`
- `docstring`
- `param_names`
- `kind`
- `callees`
- `got_slot`
- `trait_origin`
- `ast`
- `code`
- `platform_fn_ptr`

This pattern is especially visible in:
- `builtins.rs`
- `program.rs`
- `traits.rs`

The problem is not just verbosity; it is **invariant drift**. Some fields are semantically load-bearing (`got_slot`, `ast`, `code`, `trait_origin`), and repeating their setup manually makes accidental divergence likely.

**Recommended remediation**
- Introduce narrow constructors / builders for common entry shapes:
  - primitive def
  - user def placeholder
  - concrete checked def
  - overloaded placeholder
  - trait method def
- Prefer helper names that encode intent over giant literals

This change would improve both clarity and safety.

---

### Finding 5 — registry elimination simplified ownership, but lookup logic is now scattered as repeated full scans
**Impact:** Medium

A lot of lookup functionality now scans all loaded module tables directly:
- `lookup_type_def` / `lookup_constructor_type` / `all_type_defs`
- `lookup_trait_decl` / `method_to_trait` / `has_impl` / `get_implementing_types`
- `known_type_names`
- `find_hkt_param_index_in_registry`

Representative locations:
- `checker.rs:304-365`
- `checker.rs:1173-1245`
- `checker.rs:1449+`
- `traits.rs:1820+`

This is understandable as a simplification step, but the cost is that the crate now has **many ad hoc views over the same global data**.

**Why it matters**
- logic is harder to change consistently
- performance characteristics are implicit and scattered
- future indexing/caching improvements will be invasive

**Recommended remediation**
- Introduce a readonly lookup facade, e.g. `TypecheckIndexView`, that owns the “scan all modules” logic in one place.
- Keep it simple at first; this is primarily about centralizing behavior, not micro-optimizing.

---

### Finding 6 — large mixed production/test files hurt navigability
**Impact:** Medium

The crate has more test LOC than production LOC, and most of it is co-located inside the same files:
- `program.rs`: 2,815 prod / 4,170 test
- `infer.rs`: 849 prod / 2,205 test
- `checker.rs`: 812 prod / 1,986 test
- `builtins.rs`: 1,218 prod / 1,215 test

The tests are valuable; the issue is file ergonomics. In the largest files, production logic is already hard to hold in working memory before tests are considered.

**Recommended remediation**
- Keep small-module unit tests co-located.
- Split heavyweight tests from the giant files into sibling test modules (`program_tests.rs`, `infer_tests.rs`, etc.) or structured submodules.
- Do this after the pipeline cleanup, not before.

This is a secondary recommendation, but it will pay off for human and agent navigation.

## Prioritized remediations

### 1. Remove duplicate checking entry points from `program.rs`
**Impact:** Very high

Target outcome:
- `check()` / `check_form()` are the only real implementation paths
- old batch/REPL helpers become thin wrappers or test-only shims

### 2. Extract shared impl-method finalization in `traits.rs`
**Impact:** High

Target outcome:
- HKT and non-HKT paths differ only where type resolution actually differs
- annotation / symbol-table writeback is shared

### 3. Introduce shared `Expr` traversal helpers
**Impact:** High

Target outcome:
- new `Expr` variants require fewer edits
- recursive logic becomes visibly centralized

### 4. Add constructors/builders for `ModuleEntry::Def`
**Impact:** Medium-High

Target outcome:
- repeated entry boilerplate drops sharply
- slot/AST/code invariants are encoded once

### 5. Centralize “scan all modules” lookups behind one facade
**Impact:** Medium

Target outcome:
- lookup semantics become easier to audit and evolve
- indexing can be added later without touching many call sites

### 6. Split heavyweight tests out of giant implementation files
**Impact:** Medium

Target outcome:
- source navigation improves
- code review and agent edits become less error-prone

## Agent guidance / apparent traps

These are worth calling out explicitly because they are easy places for an agent to do the wrong thing.

1. **`check()` is the real path.**
   `check_program*` and `check_repl_input*` are deprecated compatibility code in `program.rs`; avoid treating them as the primary implementation.

2. **Trait impl changes have two paths.**
   If you change impl-method behavior, inspect both:
   - `check_impl_method_with_sig`
   - `check_hkt_impl_method`

3. **New `Expr` variants require more than `infer_expr`.**
   Search for recursive `match expr` walkers across `program.rs` and `infer.rs`; updating only inference dispatch is not enough.

4. **Be cautious with manual `ModuleEntry::Def` creation.**
   Important fields like `got_slot`, `ast`, `code`, and `trait_origin` are easy to mishandle. A helper should eventually own these invariants.

5. **Whole-module scans are intentional today.**
   Do not locally optimize one lookup in isolation; if lookup behavior needs to change, centralize it instead.

## Final assessment

This crate is **closer to maintainable than it may first appear** because its foundational ideas are sound: state is split cleanly, several base modules are compact, and the newer per-form pipeline is a better architecture.

The main risk is not algorithmic complexity; it is **structural duplication in the high-complexity areas**:
- duplicate check pipelines in `program.rs`
- duplicate traversal logic
- duplicate impl-method flows in `traits.rs`
- repeated symbol-table entry construction

If the project addresses those four areas soon, the crate should remain extensible. If not, future feature work will likely accumulate accidental divergence faster than the current comments and tests can contain it.
