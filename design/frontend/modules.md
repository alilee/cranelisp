# Module Declaration Extraction

Interior design for `crates/cranelisp-frontend/src/module_extract.rs` — the
frontend's slice of the module system. Spec: `spec/08-modules.md`.

The frontend's whole module responsibility is **syntactic**: recognise the
structural declarations in a parsed form vector, normalise module identity, and
hand the result to the integration layer. It does not discover files, load
modules, resolve names, register imports, or own a symbol table. Those are int's
and typecheck's, and this document does not describe their interiors.

## 1. Where extraction sits

```
source --[reader]--> Vec<Sexp>
       --[extract_module_declarations]--> (ExtractedDeclarations, residual Vec<Sexp>)
       --[build_forms / build_form]--> AST
```

`extract_module_declarations(containing_module, forms)` runs once per source
unit, immediately after `parse` and **before** macro expansion (spec §8.12.1).
Three consequences follow from that ordering, and all three are deliberate:

- A macro **cannot** expand into a `(mod …)` or `(import …)`. Structural
  declarations are recognised syntactically, never produced. The alternative
  inverts the order — you cannot run macros before you know what is imported.
- The declarations are available to the integration layer before any form-by-form
  processing begins, which is what lets the dependency graph be known up front.
- Structural declarations never reach the AST builder, so `build_form` rejects
  one as a caller bug rather than handling it.

Trait impls and DLL paths are **not** extracted here. They are ordinary forms and
reach typecheck through the residual vector.

## 2. The declaration vocabulary

| Form | Meaning |
|---|---|
| `(mod name)` / `(mod- name)` | Public / private submodule, loaded from a file |
| `(mod name forms…)` / `(mod- name forms…)` | Inline submodule — a one-time creation syntax whose body is extracted to a file on first compilation |
| `(import [module-spec names-list …])` | Pairs of module specifier and names list |
| `(export [module names-list …])` | Re-export list, mirroring the import structure |
| `(platform [...])` | Platform DLL binding |

A module specifier is a bare dotted path (`core.option`), `super`, or
`(path alias)`. A names list is `[a b]` (specific), `[*]` (glob),
`[Display.*]` (member glob), or `[]` (alias-only). Several pairs may appear in
one form, and several forms accumulate in source order.

`mod` and `platform` names carry their own module-phase guard: the name must be a
**simple symbol**, neither qualified nor dotted, because it is composed into a
module path (`platform.<name>`) and a separator there would corrupt the composed
path. This is a different rule from the §5 declaration-head binder reject — a
different phase with a different reason — and it lives in `module_extract.rs`
rather than routing through the binder helper.

## 3. `super` is resolved here

The frontend is the boundary at which `super` is resolved. `parse_import`
requires `containing_module: &ModuleFullPath` so it can rewrite `super` to the
parent path (spec §8.3.7). **Past the frontend, no `ImportSpec.module_path`
contains the literal `"super"`** (BC §1 invariant 3), and downstream code — in
this crate and in every other — may rely on that.

The parameter is therefore not incidental: it is what makes the invariant
enforceable at one place instead of at every consumer.

## 4. `ExtractedDeclarations` and how it reaches the symbol table

`ExtractedDeclarations` is the frontend's one public DTO. It carries the
containing module's `path` plus `mod_decls`, `import_specs`, `export_specs` and
`platform_specs`, each in source order. It is `#[non_exhaustive]`, so a new
declaration category is a non-breaking addition.

**The append contract is the `pub` structural `Vec` fields on `SymbolTable`.**
There is no bulk-load method and no append helper: int's form handlers push
directly onto `imports` / `exports` / `platforms` / `submodules` in source order,
append-only and without dedup, as each field's own documentation states.

Two names that a reader may look for do not exist.
`SymbolTable::append_structural_decl` and its `StructuralDeclEntry` carrier were
deleted at S119 with zero callers, settling the Decision-39 append-carrier
question; `SymbolTable::write_structural_decls` never existed anywhere in the
tree. Do not reintroduce either into a design, a rustdoc or a diagram — naming a
method that does not exist is what sent readers looking for a carrier the tree
had already decided against.

The preamble is captured separately and is **not** a field on this DTO. It needs
the raw source head (for blank-line awareness and `;;` markers) while extraction
walks the comment-stripped parse; bolting it on would widen a narrow boundary for
an orthogonal concern. `module-preamble.md` §4 records that judgment.

## Cross-references

- `spec/08-modules.md` §8.3.7 (`super`), §8.12.1 (extraction before expansion), §8.16 (the preamble).
- `design/arch/bounded-contexts.md` §1 — invariant 3.
- `design/int/int.md` §6.1 — `register_module` Phase 0, where the append happens.
- `design/frontend/module-preamble.md` — the sibling capture the load seam calls alongside extraction.
