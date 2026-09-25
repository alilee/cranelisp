# Private submodule imports

How the import handler enforces `spec/08-modules.md` §8.2.3: a module outside
the declaring module's subtree must not import a `(mod- name)` private
submodule.

## 1. Rule

A `(mod- internal)` declaration in module `P` makes `P.internal` private to
`P`'s subtree. An import of `P.internal` is allowed only when the importer is
`P` itself or a module whose path starts with `P.`. Every other importer,
including the root and `P`'s peers, is refused.

- Nested private modules need no recursion. Each level is checked on its own
  import, so `P.internal.deeper`, imported from `P`, passes both its own check
  and the transitive check on `P.internal`.
- The check gates importing the private module **path**. A name that `P`
  re-exports from `P.internal` is `P`'s public name, and importing it from `P`
  is allowed.

## 2. Privacy record

The parent's persisted `SymbolTable.submodules` is the one source of truth.
Each entry is a `ModDecl` whose `visibility` distinguishes `(mod- name)` from
`(mod name)`. The declaration writer records it when the parent's structural
forms are processed, and cache restore rebuilds it from the same field
(`int.md` §7.5). No second privacy index exists.

## 3. Where the check sits

`src/process_form/dependency.rs::check_private_submodule_import` runs from
`handle_import` after current-module-relative path resolution and the
null-import shortcut, and before the already-loaded shortcut and file
resolution. A refused import therefore never loads the private module's source.

1. Split the imported path into the parent path and the trailing component.
   A single-segment path has no parent and is never private.
2. Look up the parent's table. If it holds a private `ModDecl` for the
   trailing component, apply the subtree rule in §1.
3. On refusal, return a `ModuleError` at the import spec's span. It names the
   private module, the declaring parent and the importer, and cites §8.2.3.

**Unloaded parent (open).** If the parent's table is not yet installed, or is
installed without its structural declarations, the check returns success on
that visit. The source expects a later resumed visit to decide once the parent
has typechecked, but nothing forces the parent to load first. Whether a peer
can import a private submodule whose parent loads later is unmeasured.

- The earlier design required the importer to block on the parent's
  typecheck before deciding. The source does not do this.
- **Falsifier:** an entry that imports the peer before any module declares
  the parent, then compiles successfully.
- Attribution of any failure belongs to `qa`.

## 4. Evidence

- `tests/spec_08_modules.rs::mod_dash_private_submodule_not_importable_from_peer_neg`
  covers the peer refusal with the parent already loaded.
- `src/worker/tests.rs::writer_records_private_submodule_with_is_private_true`
  pins the writer recording the private `ModDecl`, which is the check's input.
