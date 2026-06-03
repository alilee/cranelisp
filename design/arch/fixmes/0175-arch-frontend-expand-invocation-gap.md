---
number: 0175
target: /arch
filed_by: /dev (frontend)
filed_at: 2026-05-13
sprint_filed: 66
refers_to: crates/cranelisp-frontend/src/lib.rs //! preamble + per-item rustdoc on pub fn expand + bounded-contexts.md §1 §2 §6, design/arch/macro-expansion-ownership.md, crates/cranelisp-types/src/macro_expander.rs, src/marshal.rs, src/expander.rs, design/arch/sequences/exec-flow-compilation.mmd
status: resolution-designed-impl-pending
---

# `cranelisp_frontend::expand` cannot perform macro invocation under current dep rules

## RESOLUTION (S76 W-Macro, Phase 3 — user-arbitrated)

**Direction decided; design formalized; implementation pending /dev waves.**

The `cranelisp-marshal` bridge-crate option (a) is **REJECTED** (user-arbitrated, S76 Phase 2). None of (a)–(d) is adopted as written; instead the two conflated jobs are split along their natural dependency lines:

- **Macro recognition** (walk + macro-vs-fn discrimination + clause matching) moves to **typecheck** — it already resolves every head symbol against the symbol-table view, and needs only `cranelisp-types`.
- **Macro execution** (marshal + signal-protected JIT call) stays in **int**, behind the injected `cranelisp_types::MacroExpander` callback (trait object). int implements it over its existing `src/expander.rs` invocation core + `src/marshal.rs`.
- **Frontend** keeps only quasiquote desugaring; `expand` + `ExpansionError` retire from the frontend boundary; the structural-walk skeleton in `crates/cranelisp-frontend/src/expand.rs` is deleted.
- The expanded `Sexp` is re-classified by typecheck itself (structural-form re-entry resolution = option (a): typecheck re-classifies, NOT signal-back-to-int's-form-pipeline), preserving Decision 44 cluster-atomicity + Principle 17 module-locality.

The callback boundary type (`MacroExpander` trait + `MacroInvokeError`) is authored in `crates/cranelisp-types/src/macro_expander.rs` this change-set; the full design (two-jobs analysis, DAG proof, structural-form re-entry resolution + rationale, interior-factoring choice for /dev) is `design/arch/macro-expansion-ownership.md`. Cascaded: BC §1/§2/§6, `facades/int.md`, `exec-flow-compilation.mmd`+`.svg`.

**This FIXME stays open until /dev lands the implementation** (the `expand` retirement, the typecheck recognition + `MacroExpander` impl, the `src/expander.rs` walk deletion). When the code lands, /dev deletes this file. The architecture is settled; only the implementation remains.

---

## Original issue (preserved for context)

# `cranelisp_frontend::expand` cannot perform macro invocation under current dep rules

## Issue

The Wave 3a-β design (`design/frontend/wave-3a-build-form.md` §5) and the
frontend public-surface contract (`crates/cranelisp-frontend/src/lib.rs`
//! preamble + per-item rustdoc on `pub fn expand`; post-S70 B3-C the
canonical home — `facades/frontend.md` retired) direct
`/dev (frontend)` to migrate
`expand_sexp_recursive` from `src/expander.rs` into `crates/cranelisp-frontend/`,
giving it the signature

```rust
pub fn expand<C, L>(sexp: Sexp, symbol_tables: &SymbolTables<C, L>)
    -> Result<Sexp, ExpansionError>
where C: CodeStore, L: LinkerStore;
```

The implementation must, on retry (per facade §"expand" — "On the retry, expand
sees the now-ready entry and either invokes the macro or leaves the form as a
function call — no second gap"), **invoke** the JIT-compiled macro clause
through the GOT slot. Invocation requires:

1. `cranelisp_runtime::heap_alloc` + `heap_alloc_string` + `string_read` —
   to marshal compiler `Sexp` → runtime ADT value and back (`src/marshal.rs`).
2. `cranelisp_runtime::panic::take_runtime_error` — to clear/read the
   thread-local runtime-error slot before/after the `extern "C" fn(i64) -> i64`
   call.
3. `libc` + `sigsetjmp`/`siglongjmp` — to recover from SIGFPE/SIGILL/SIGBUS
   raised by JIT'd macro bodies (`src/expander.rs::invoke_jit_protected`).

**Frontend's current `Cargo.toml` depends only on `cranelisp-types`.** The
facade explicitly forbids depending on `cranelisp-runtime`/-primitives/-intrinsics/-platform
("The frontend imports from no other workspace crate"). Under these rules
the frontend cannot perform invocation. The full migration as written is
therefore not implementable without one of:

(a) Widening frontend's allowed deps (e.g., a new `cranelisp-marshal` crate
    consumable by both frontend and the binary, with primitives-side
    `heap_alloc` re-exported through a narrow types-stable surface);
(b) Relocating `marshal` to `cranelisp-types` (currently disallowed —
    types is data-only, no `extern "C"` invocation logic, no `libc` dep);
(c) Adding a callback parameter to `expand` (e.g., `&dyn Fn(*const u8,
    &[Sexp], Span) -> Result<Sexp, ExpansionError>`) so the orchestrator
    supplies the invocation glue. Facade signature would change.
(d) Leaving `expand_sexp_recursive` in `src/` as the real implementation and
    making `cranelisp_frontend::expand` a structural-skeleton facade that
    returns `Gap(MacroInMem(fq))` for every encountered macro head. The
    orchestrator's retry never actually resolves the gap; in practice
    `int`'s `process_form` keeps calling `src/expander.rs` directly. The
    facade signature stands but the contract ("retry sees a now-ready
    entry and invokes") becomes vacuous.

## What this wave delivered

The frontend `/dev` agent landed the `build_form` shape pivot and demotion
of internal helpers per Wave 3a-β. For `expand`, option (d) was implemented
as the only path consistent with current dep rules:

- `cranelisp_frontend::expand::expand<C, L>(sexp, &SymbolTables<C, L>)` is
  authored with the facade-aligned signature.
- It performs the structural traversal — recursing into `List`/`Bracket`
  children, recognising macro-head positions (bare symbol + lookup of
  `ModuleEntry::Macro` via `symbol_tables`), enforcing the depth limit, and
  expanding quasiquotes via `expand_quasiquotes`.
- On any macro head encountered with the entry resolved as
  `ModuleEntry::Macro`, it returns `Err(ExpansionError::Gap(
  ResolutionGap::MacroInMem(fq)))` — uniform Gap per facade §"expand".
- On `Malformed` shapes (macro tagged but with invalid args), the depth
  limit, or unresolved bare symbols, it returns the appropriate
  `Malformed`/`Gap` variants.
- It does NOT invoke. `src/expander.rs::expand_sexp_recursive` remains the
  real invocation path until `/int`'s Wave 3a-β switches sites, which is
  itself blocked on a resolution of this gap.

## Proposed resolution

`/arch` chooses one of (a)–(d) above and either revises the frontend
public-surface contract (`crates/cranelisp-frontend/src/lib.rs` //!
preamble + per-item rustdoc on `pub fn expand`; post-S70 B3-C the
canonical home — `facades/frontend.md` retired) to match, or revises
the frontend's allowed-deps statement in `bounded-contexts.md` §1 to
permit the chosen dependency widening. The current wording is
internally inconsistent: the surface contract requires invocation, the
BC forbids the only crates that provide it.

Likely cleanest: (a) — a new `cranelisp-marshal` crate that bridges
frontend ↔ primitives without leaking trait knowledge. The marshal logic is
small (~250 LOC) and self-contained; the existing `src/marshal.rs` already
isolates the runtime touch points.

Worst: (c) — adding a callback collapses the dep-graph win the Decision-8
retraction was supposed to deliver (the whole point of "direct
`&SymbolTables` lookup" was eliminating trait dispatch; reintroducing a
callback for invocation undoes half of that).

## Operational implication / Context

This blocks /int Wave 3a-β `process_form` shape pivot from cleanly
switching to the frontend `expand` — int will keep calling the in-tree
`src/expander.rs` until /arch resolves. The dual-source state is
acceptable for one wave but is real debt: Wave 4 ("trait-knowledge
deletions") cannot delete `MacroResolver` in `src/expander.rs` while the
frontend's `expand` returns Gap on every macro.

Recommended `/arch` action: option (a) — add a 5th workspace crate
`cranelisp-marshal` between platform and frontend. Coordinate with the
parallel /dev (int) and /dev (typecheck) agents currently running on
Sprint 66 Wave 3a so they know the cleanup is one wave deferred.
