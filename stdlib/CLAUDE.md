# stdlib/

Standard library for Cranelisp. Owned by `/stdlib` skill.

## Current State (Sprint 14 Wave 3)

The prelude loads successfully and re-exports from domain modules. Threading macros
(`->`, `->>`) moved to `fn/threading.cl`. Ring 2 modules (string, int, float, list,
vec) implemented. Derive macro ported from sketch. Pipeline fixed to register macros
in symbol table for cross-module import.

### Module Tree (implemented)

```
stdlib/
  prelude.cl              ; re-export shell + inline macros
  compare.cl              ; shell: (mod eq) (mod ord)
  compare/eq.cl           ; Eq trait + primitive impls
  compare/ord.cl          ; Ord trait + primitive impls
  num.cl                  ; shell: (mod num) (mod int) (mod float)
  num/num.cl              ; Num trait + primitive impls
  num/int.cl              ; Int operations: rem, abs, sign, even?, odd?, etc.
  num/float.cl            ; Float operations: abs-float, sign-float, etc.
  text.cl                 ; shell: (mod display) (mod string)
  text/display.cl         ; Display trait + primitive impls
  text/string.cl          ; String operations: blank?, repeat-str, index-of, etc.
  fn.cl                   ; shell: (mod option) (mod result) (mod compose) (mod threading)
  fn/option.cl            ; Option type: None, Some
  fn/result.cl            ; Result type: Ok, Err + operations
  fn/compose.cl           ; compose, pipe, identity, flip
  fn/threading.cl         ; ->, ->> macros (imported by prelude)
  default.cl              ; Default trait + primitive impls
  collections.cl          ; shell: (mod pair) (mod either) (mod list) (mod vec)
  collections/pair.cl     ; Pair type + first, second, swap
  collections/either.cl   ; Either type: Left, Right + operations
  collections/list.cl     ; List type (recursive ADT) + operations
  collections/vec.cl      ; Vec utility functions: vec-map, vec-filter, etc.
  testing.cl              ; shell: (mod assertions)
  testing/assertions.cl   ; assert-eq, assert-true, assert-false
  core.cl                 ; shell for core.syntax (macro authors)
  core/syntax.cl          ; SList helpers (standalone, not prelude dep)
  derive.cl               ; derive macro: derive-Eq, derive-Ord, derive-Display
  plan-stdlib.md          ; normative module tree and delivery plan
```

### What works

- `prelude.cl` loads without errors via multi-file module discovery
- Domain modules compiled in dependency order (toposorted)
- Traits (Num, Eq, Ord, Display) defined in domain modules, re-exported through prelude
- Option and Result types in separate modules
- Function composition utilities (compose, pipe, identity, flip)
- Default trait with primitive impls
- Pair and Either types with operations
- Testing assertions (assert-eq, assert-true, assert-false)
- Threading macros (`->`, `->>`) in `fn/threading.cl`, imported by prelude
- String operations (blank?, repeat-str, index-of, reverse-str, pad-left, pad-right)
- Int operations (rem, abs, sign, negate, even?, odd?, min-int, max-int, clamp)
- Float operations (abs-float, sign-float, negate-float, min-float, max-float, clamp-float)
- Vec utilities (vec-map, vec-filter, vec-reduce, vec-reverse, vec-any?, vec-all?, etc.)
- List type (recursive ADT) with operations (fold, map-list, filter-list, reverse, etc.)
- Derive macro (derive-Eq, derive-Ord, derive-Display) ported from sketch
- All macros (do, cond, str, case, def, def-, const, vec, when, bind!) in prelude

### Known blockers

- **No floor/ceil/round**: Float operations limited to what can be built from
  existing Ring 0 primitives. Need runtime extern functions for IEEE 754 rounding.

### What is NOT in prelude (requires explicit import)

- `fn.result` operations: is-ok?, is-err?, unwrap-or, map-ok, map-err, and-then
- `fn.compose`: compose, pipe, identity, flip
- `default`: Default trait
- `collections.pair`: Pair, first, second, swap
- `collections.either`: Either, Left, Right, either, map-left, map-right
- `collections.list` operations: length, fold, map-list, filter-list, reverse, etc.
- `collections.vec`: vec-map, vec-filter, vec-reduce, vec-reverse, etc.
- `num.int`: rem, abs, sign, negate, even?, odd?, min-int, max-int, clamp
- `num.float`: abs-float, sign-float, negate-float, min-float, max-float, clamp-float
- `text.string`: blank?, repeat-str, index-of, reverse-str, pad-left, pad-right
- `testing.assertions`: assert-eq, assert-true, assert-false
- `derive`: derive, derive-Eq, derive-Ord, derive-Display

### Prelude re-exports

Traits: Eq, Ord, Num, Display (with =, !=, <, >, <=, >=, +, -, *, /, show)
Types: Option (None, Some), Result (Ok, Err), List (Nil, Cons, empty?)
Macros: ->, ->>, vec, when, const, const-, do, cond, list, str, case, def, def-, bind!

## Conventions

- Trait method parameter names use `self` syntax per spec section 7.1
- Primitive names match the Ring 0/1 tables exactly (add-i64, str-concat, etc.)
- Macro bodies inline helper logic rather than calling defn-defined helpers
  (because defn forms are Phase 4, macros are Phase 3)
- Domain modules use `(import [...])` to declare dependencies
- Shell modules (compare.cl, num.cl, etc.) contain only `(mod ...)` declarations
- Prelude imports specific names from domain modules (not globs)
- Modules outside prelude graph (derive.cl) use primitives directly, not trait operators
- Macros in submodules are registered in both expander AND symbol table (pipeline fix)

## Pipeline Fix (Sprint 14 Wave 3)

`compile_and_register_macro` in `src/pipeline.rs` was updated to register macros
in the current module's symbol table (as `ModuleEntry::Macro`), not just in the
expander's `MacroEnv`. Without this, macros defined in submodules could not be
imported by other modules via `(import [module [macro-name]])`. The REPL's
`eval_defmacro` already did this; the batch pipeline was missing it.

## Key Architecture Finding

The `load_prelude` function already supports multi-file module discovery.
It calls `discover_module_graph` on `prelude.cl`, which follows both `(mod ...)`
declarations and `(import [...])` references to discover and toposort all
dependent modules. The FIXME about "submodule primitive seeding" was stale --
`set_current_module` correctly seeds new modules with primitives from `user`.

A pipeline fix was needed: modules with only type definitions (e.g., fn/option.cl)
or only trait declarations have no function definitions for codegen. The pipeline
now skips codegen for such modules after typechecking (which registers the types
and traits).
