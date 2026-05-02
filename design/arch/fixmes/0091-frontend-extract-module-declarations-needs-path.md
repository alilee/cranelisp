---
number: 0091
target: /arch
filed_by: /design
filed_at: 2026-05-01
sprint_filed: 63
refers_to: design/arch/facades/frontend.md (lines 18, 81-86), crates/cranelisp-frontend/src/module_extract.rs §parse_import
status: open
---

# Frontend facade `extract_module_declarations` and `parse_import_sexp` signatures lack `containing_module`

## Issue

The frontend facade specifies:

```rust
pub fn extract_module_declarations(forms: Vec<Sexp>)
    -> Result<(StructuralDecls, Vec<Sexp>), CranelispError>;

pub fn parse_import_sexp(sexp: &Sexp) -> Result<ImportSpec, CranelispError>;
```

Both signatures are missing the parsing module's path. The frontend BC §1 invariant 3 mandates that `super` resolution happens at parse time — `ImportSpec.module_path` MUST never contain the literal `"super"` past the frontend boundary. To resolve `super`, the parser needs the containing module's path (per spec §8.3.7: inside `a.b.c`, `super` resolves to `a.b`).

The current implementation correctly takes `containing_module: &ModuleFullPath` (`module_extract.rs:128, 161`); the facade signature drops it. With the as-stated signatures, frontend cannot fulfill BC invariant 3.

Additionally, `parse_import_sexp`'s singular `ImportSpec` return is incongruent with the source: a single `(import [...])` form contains pairs of `(module-spec, names-list)` and produces multiple `ImportSpec` entries (`parse_import_entries` returns `Vec<ImportSpec>`). The facade must return `Vec<ImportSpec>` for this entry — the call site in the integration layer needs all the entries the form declares.

## Proposed resolution

Update `design/arch/facades/frontend.md` to either:

(a) Thread the path through both APIs:

```rust
pub fn extract_module_declarations(
    path: &ModuleFullPath,
    forms: Vec<Sexp>,
) -> Result<(StructuralDecls, Vec<Sexp>), CranelispError>;

pub fn parse_import_sexp(
    sexp: &Sexp,
    containing_module: &ModuleFullPath,
) -> Result<Vec<ImportSpec>, CranelispError>;
```

OR (b) Bundle path into `StructuralDecls` and require that `extract_module_declarations` accepts the path; drop `parse_import_sexp` from the public surface entirely (the only caller is `extract_module_declarations` internally; REPL `/import` parsing can route through `extract_module_declarations` with a single-form input).

(a) preserves the current shape; (b) narrows the public surface and is preferred by Principle 2 (narrow interfaces).

Either resolution unblocks the frontend design from claiming as-stated facade fidelity. The current `frontend.md` design doc (proposed by `/design`) currently restates the as-stated facade signature and notes the inconsistency in §10; this FIXME elevates the gap so `/arch` can settle it.

## Context

BC §1 invariant: "super resolved at frontend." Source today fulfills the invariant via `parse_import`'s `containing_module` parameter. Facade went out of sync when the two-call shape was introduced (per facade §"Free functions").

This is a pure facade-text issue; no implementation change is required by either resolution. The implementation already does the right thing.
