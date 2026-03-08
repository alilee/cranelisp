# stdlib/

Standard library for Cranelisp. Owned by `/stdlib` skill.

## Current State (Sprint 12)

The prelude (`prelude.cl`) compiles successfully during `load_prelude` but its symbols
do not reach the user module due to a pipeline import-target bug (see FIXME in prelude.cl).

### What works

- `prelude.cl` loads without errors (no "prelude loading failed" warning)
- Traits (Num, Eq, Ord, Display) are defined with impls for all primitive types
- Option type defined
- All macros (do, cond, str, case, ->, ->>, def, def-, const, vec, when, bind!) defined

### What is blocked by pipeline bugs

1. Prelude symbols don't propagate to user module (FIXME(/int) #2 in prelude.cl)
2. List type can't be defined (recursive type bug, FIXME(/int) #3)
3. Prelude submodules can't access primitives (FIXME(/int) #1)

### Files

| File | Purpose |
|---|---|
| `prelude.cl` | Self-contained prelude: types, traits, macros |
| `core.cl` | Module shell for core.syntax (currently unused by prelude) |
| `core/syntax.cl` | SList helpers for macro authors (standalone, not prelude dep) |
| `plan-stdlib.md` | Normative module tree and delivery plan |

## Conventions

- Prelude is self-contained (no submodule deps) until pipeline bugs are fixed
- Trait method parameter names use `self` syntax per spec §7.1
- Primitive names match the Ring 0/1 tables exactly (add-i64, str-concat, etc.)
- Macro bodies inline helper logic rather than calling defn-defined helpers
  (because defn forms are Phase 4, macros are Phase 3)
