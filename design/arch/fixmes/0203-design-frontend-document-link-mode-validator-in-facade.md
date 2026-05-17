---
number: 0203
target: /design (frontend)
filed_by: /dev (frontend)
filed_at: 2026-05-16
sprint_filed: 67
refers_to: design/arch/facades/frontend.md §"Public surface (as-designed)", crates/cranelisp-frontend/src/link_mode.rs, design/arch/decisions/0040-runtime-trace-io-trace-relocate-to-int.md, spec/04-expressions.md §4.12.9
status: open
---

# Document `link_mode` validator pass on the frontend facade

## Issue

FIXME 0199 resolution added a new public surface to `cranelisp-frontend`:

- `pub mod cranelisp_frontend::link_mode`
- `pub const cranelisp_frontend::link_mode::TRACE_LINK_MODE_REJECTION_MESSAGE: &str`
- `pub fn cranelisp_frontend::link_mode::validate_expr_for_build_mode(expr: &Expr, mode: CodegenBehaviour) -> Result<(), CranelispError>`
- `pub fn cranelisp_frontend::link_mode::validate_parsed_entry_for_build_mode(entry: &ParsedEntry, mode: CodegenBehaviour) -> Result<(), CranelispError>`
- Root re-exports of the const + the two fns.

The corresponding entries appear in
`crates/cranelisp-frontend/public-api.txt` (regenerated in the same
change-set per `design/arch/CLAUDE.md` §"Baseline-diff discipline"). The
facade spec at `design/arch/facades/frontend.md` does NOT yet name this
pass; `/dev (frontend)` cannot edit the facade per the file-ownership
rule.

## Proposed resolution

Add a §"Build-mode rejection — `link_mode::*`" subsection between the
existing §"Free functions" and §"Sub-parsers for structural forms"
sections in `facades/frontend.md`, describing:

1. The Path-B1 product constraint (Decision 40, spec §4.12.9) — the
   reason this surface exists.
2. The two free functions
   (`validate_expr_for_build_mode` /
   `validate_parsed_entry_for_build_mode`)
   and the const (`TRACE_LINK_MODE_REJECTION_MESSAGE`) — signature +
   intended caller (the cluster orchestrator in `int`, post-`build_form`
   / post-`build_expr` per form).
3. Why a separate pass and not a parameter on `build_form` /
   `build_expr` — Principle 6 (complexity budget): keeping the
   four-free-function form-by-form boundary stable + avoiding signature
   churn through 100+ recursive call sites inside `ast_builder.rs`.
   Per-form post-build walks are O(node count) and add no observable
   cost outside `--link` mode (the `InMemoryAndObject` fast path is an
   early `Ok(())`).
4. Macro-expansion ordering — the validator runs on `Expr` /
   `ParsedEntry`, which are post-AST-build and therefore post-macro-expansion.
   Quoted occurrences (`'(trace x)`, `` `(trace x) ``) are desugared by
   the expander into `Sexp` constructor calls (`SexpList`, `SexpSym`, …)
   and reach the AST builder as `Expr::Apply` to those constructors —
   not as `Expr::Trace`. The validator therefore correctly distinguishes
   evaluation occurrences from data occurrences per spec §4.12.

Optional: extend §"Bounded-context invariants" with a new item — "The
frontend enforces build-mode rejection at the form-by-form boundary; no
downstream layer (typecheck, backend) carries fallback logic for
`(trace ...)` under `--link`. Per Principle 7."

## Operational implication / Context

The integration-layer wiring — when the cluster orchestrator actually
calls these validators — is filed separately as FIXME 0204
(`target: /dev (int)`). The facade should describe the validator as
"called by the cluster orchestrator per form" without prescribing the
exact call site (that's a `/dev (int)` implementation choice within
`src/cluster.rs` / `src/worker.rs`).

**Public-API impact**: 7 net lines added to `public-api.txt`
(regenerated in the same change-set):

```
+pub mod cranelisp_frontend::link_mode
+pub const cranelisp_frontend::link_mode::TRACE_LINK_MODE_REJECTION_MESSAGE: &str
+pub fn cranelisp_frontend::link_mode::validate_expr_for_build_mode(...)
+pub fn cranelisp_frontend::link_mode::validate_parsed_entry_for_build_mode(...)
+pub const cranelisp_frontend::TRACE_LINK_MODE_REJECTION_MESSAGE: &str
+pub fn cranelisp_frontend::validate_expr_for_build_mode(...)
+pub fn cranelisp_frontend::validate_parsed_entry_for_build_mode(...)
```

These are the qualified-path + root-re-export pairs (same shape as the
existing `parse` / `reader::parse` and `extract_module_declarations` /
`module_extract::extract_module_declarations` pairs the facade already
endorses).
