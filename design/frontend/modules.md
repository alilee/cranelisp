# Module Declaration Extraction

Interior design for `crates/cranelisp-frontend/src/module_extract.rs` — the
frontend's slice of the module system. Spec: `spec/08-modules.md`.

The frontend's whole module responsibility is **syntactic**: recognise the
structural declarations in a parsed form vector, classify each import and export
entry, derive the name each entry binds, normalise module identity, and hand the
result to the integration layer. It does not discover files, load modules,
resolve names, register imports, or own a symbol table. Those are the binary's
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
| `(import [module-spec names-list …])` | Pairs of module specifier and names list (§8.3) |
| `(export [module-spec names-list …])` | The same pairs, bound public (§8.4, §8.4.0) |
| `(platform name)` | Platform DLL binding |

`mod` and `platform` names carry their own module-phase guard: the name must be a
**simple symbol**, neither qualified nor dotted, because it is composed into a
module path (`platform.<name>`) and a separator there would corrupt the composed
path. This is a different rule from the §5 declaration-head binder reject — a
different phase with a different reason — and it lives in `module_extract.rs`
rather than routing through the binder helper.

### 2.1 One entry grammar for imports and exports

Import and export are one operation differing only in visibility (§8.4.0), and
§8.4 applies the full §8.3 grammar to exports. The frontend therefore has **one
pair parser**: a module-specifier parser and a names-list parser, both shared.
The `import` and `export` arms differ only in the record they wrap the result in
(`ImportSpec` or `ExportSpec`) and the form noun their diagnostics name.

A second export-side parser is the defect shape this replaces: it is how exports
lost the `(module alias)` specifier (ACT-1056) while imports kept it.

**Module specifier.** A bare module path, `super`, or `(path alias)`. The path is
a reference and may be dotted. The alias is a binder (§8.3.4, which names export
mount aliases too) and rejects a qualified or dotted spelling through the shared
binder helper ([binder-head-reject.md](binder-head-reject.md)). An export's alias
is its mount (spec §8.4.4) and
travels in `ExportSpec::alias`; the frontend writes it and nothing else
([alias contract](../arch/module-alias-scoped-lookup.md) §5.1 — the parser is this
surface's, the writer is the binary's).

**Names list.** The list-level shape is decided first, then every element of a
specific list is classified on its own (§8.3.11):

| Written list | Carrier |
|---|---|
| `[]` | `ImportNames::None` — alias-only, mount-only or null |
| `[*]`, the sole element | `ImportNames::Glob` |
| anything else | `ImportNames::Specific`, one `ImportEntry` per element, in source order |

`*` means the glob only as the sole element (§8.3.2); among other elements it is
the multiplication operator, an ordinary plain entry. A singleton `[Display.*]` is
a one-entry specific list, because the list-level member glob no longer exists.
The frontend never produces an empty `Specific`: emptiness is `None`.

**Entries.** Each element of a specific list is exactly one of:

| Element | Entry | `source` | `local` |
|---|---|---|---|
| `name` | `Name` | `name` | `name` |
| `Type.member` | `Name` | `Type.member` | `member` |
| `(source local)` | `Name` | `source` — bare or dotted | `local` |
| `Parent.*` | `MemberGlob(Parent)` | — | — |

Any other element is a located module error at that element, naming the form
and the shapes it accepts:

- a qualified spelling (`m/x`) as an entry source or a member-glob parent — the
  §8.3 `name` and `member_glob` productions admit only bare and dotted symbols;
- a member glob as the source of a rename (`(Option.* X)`);
- a rename that is not exactly two symbols;
- a rename whose local name is qualified or dotted — it is a binder, so the
  shared binder helper rejects it (§8.3.4);
- a member glob with an empty or non-bare parent.

### 2.2 The bound name is derived here, once

`local` is computed by the frontend and by no one else
([Principle 24](../arch/principles/24-resolve-once.md); BC §1 invariant 11). The
installer binds `local` to the candidates reached through `source` and never
reads a written spelling, so a dotted entry bound under its dotted spelling
(ACT-1055) has no representation.

The member of a dotted entry is everything after its last `.`, with both halves
non-empty — the frontend's one dotted splitter, `split_dotted_name`. Reusing it
here is a **reference** decomposition, not a binder check; the crate memory's
rule that the splitter feeds only the binder reject concerns binder checks and
should be restated by `dev` to admit this one reader. A rename's local is taken
as written after the binder reject. A self-rename `(Some Some)` is valid and
produces `source == local` (§8.3.5).

The installer separately projects a member glob's table entries to bare names
through `cranelisp_types::bare_member_name`. The two projections read different
inputs — a written dotted spelling here, a canonical member symbol there — and
apply the same last-`.` rule. *Falsifier:* a dotted entry and the member glob of
its parent binding different local spellings for the same member. Calling the
types projection from the frontend instead would single-source the rule but is a
new cross-crate consumer edge, which needs its own API row.

### 2.3 What the frontend does not decide

These belong to the binary, which sees the symbol tables and every form across
REPL turns. A frontend copy would be a second seam with a partial view.

- Whether a source name exists, is public, or names a type or trait (§8.3.1,
  §8.3.3).
- Deduplication and candidate sets. Two entries with the same `local` are
  carried as written; §8.6.4 decides whether they deduplicate or coexist.
- Mount collisions. A duplicate mount alias and a mount colliding with a
  submodule short name (§8.4.4) span forms and turns; they are raised at the
  binary's declaration seam ([alias contract](../arch/module-alias-scoped-lookup.md)
  §5.1). The frontend does not check them even within one form. The same holds
  for an import alias and an export mount sharing a spelling, which §8.4.4
  refuses only when their targets differ: target equality needs canonical
  module identity the frontend does not hold.
- `(export [m []])`. §8.4.4 makes it a no-op; the frontend emits it as written,
  an `ExportSpec` with no alias and `ImportNames::None`, and the binary loads
  nothing for it.
- Identity of an impl written through a renamed import, and a renamed trait in
  type-or-trait routes. These are persistence and typecheck obligations the
  carrier enables (ACT-0997); the frontend's part ends at a correct `source` and
  `local`, and at an `impl` head whose trait and target references keep their
  written qualifiers (`trait-impl-head-parse.md` §2). The types crate derives
  the impl's authored label from those written references (API row D10), so
  re-rooting a bare head under the current module here would change the label.

**Where the frontend's responsibility ends**, by filing:

| Filing | Frontend part | Remainder |
|---|---|---|
| ACT-0997 | Parse `(source local)` into a `Name` entry; keep an `impl` head's written references | Binary binds `local`; the authored impl label (row D10) and typecheck's renamed-trait routes |
| ACT-1055 | Derive `local` = member for `Type.member` | Binary binds `local` instead of the written spelling (`src/imports.rs`) |
| ACT-1056 | Classify every element; parse an export's `(path alias)` and set `ExportSpec::alias` | Binary installs the mount through one writer, fresh and restore, and raises the collision errors |

## 3. `super` is resolved here

The frontend is the boundary at which `super` is resolved. The shared
module-specifier parser takes `containing_module: &ModuleFullPath` so it can
rewrite `super` to the parent path (spec §8.3.8). **Past the frontend, neither an
`ImportSpec` nor an `ExportSpec` module path contains the literal `"super"`**
(BC §1 invariant 3, which names `ImportSpec`), and downstream code may rely on
that. `super` in a root module is a located error at the specifier, for either
form.

The parameter is therefore not incidental: it is what makes the invariant
enforceable at one place instead of at every consumer. Sharing the specifier
parser extends it to exports.

## 4. `ExtractedDeclarations` and how it reaches the symbol table

`ExtractedDeclarations` is the frontend's one public DTO. It carries the
containing module's `path` plus `mod_decls`, `import_specs`, `export_specs` and
`platform_specs`, each in source order. It is `#[non_exhaustive]`, so a new
declaration category is a non-breaking addition. Its shape does not change
under D3: the entry carrier lives inside the types-owned specs.

**The append contract is the `pub` structural `Vec` fields on `SymbolTable`.**
There is no bulk-load method and no append helper: the binary's form handlers
push directly onto `imports` / `exports` / `platforms` / `submodules` in source
order, append-only and without dedup, as each field's own documentation states.
The direct field append is the settled design; do not describe a bulk-load or
append-carrier method on `SymbolTable`.

The preamble is captured separately and is **not** a field on this DTO. It needs
the raw source head (for blank-line awareness and `;;` markers) while extraction
walks the comment-stripped parse; bolting it on would widen a narrow boundary for
an orthogonal concern. `module-preamble.md` §4 records that judgment.

## 5. Unit scenarios

Module tests in `module_extract/tests.rs` assert the extracted carrier directly.
`qa` allocates the solution cells; these rows are the parser mechanisms each
change-set must pin.

| Mechanism | Positive | Negative |
|---|---|---|
| Per-entry classification | `[Option Option.*]`, `[Option.* helper]`, `[Option.None]`, `[(Some Just) None]`, `[(Option.Some Just)]`, `[(Some Some)]`, `[+ - * /]` — every entry kept, in order, with its `source` and `local` | qualified source; rename of a member glob; three-element rename; qualified or dotted rename local; empty member-glob parent — each located at the element |
| List shape | `[]` → `None`; `[*]` → `Glob`; `[Display.*]` → one `MemberGlob` entry | no `Specific` is empty |
| Export specifier | `(export [(m a) [x]])` and `(export [(m a) []])` carry `alias`; `(export [m [x]])` carries none | qualified or dotted export alias |
| Shared parser | the same element list yields equal entries under `import` and `export` | — |
| `super` | `super` rewrites to the parent under `import` and `export` | `super` in a root module, both forms |

## Cross-references

- `spec/08-modules.md` §8.3 (grammar and §8.3.11 classification), §8.3.8 (`super`), §8.4 and §8.4.4 (exports and mounts), §8.12.1 (extraction before expansion), §8.16 (the preamble).
- `design/arch/bounded-contexts.md` §1 — invariants 3 and 11.
- `design/arch/interfaces.md` — import and export entries (the D3 carrier).
- `design/int/int.md` §6.1 — `register_module` Phase 0, where the append happens.
- `design/frontend/binder-head-reject.md` — the alias and rename-local binder reject.
- `design/frontend/module-preamble.md` — the sibling capture the load seam calls alongside extraction.
