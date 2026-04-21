# stdlib/

Standard library for Cranelisp. Owned by `/stdlib` skill.

## Current State (Sprint 17 Wave 2)

The prelude is now a **pure re-export shell** — zero inline definitions. All macros
have been moved to their plan-designated domain modules. The `do` macro uses IO
semantics (bind-based) per spec §10.4. Module discovery extended to process
`(export ...)` forms so the prelude can reference root-level domain modules
without import statements.

### Module Tree (implemented)

```
stdlib/
  prelude.cl              ; pure re-export shell (export only, no defmacro)
  control.cl              ; when, unless, cond, case macros
  defs.cl                 ; const, const-, def, def- macros
  compare.cl              ; shell: (mod eq) (mod ord)
  compare/eq.cl           ; Eq trait + primitive impls
  compare/ord.cl          ; Ord trait + primitive impls
  num.cl                  ; shell: (mod num) (mod int) (mod float)
  num/num.cl              ; Num trait + primitive impls
  num/int.cl              ; Int operations: rem, abs, sign, even?, odd?, etc.
  num/float.cl            ; Float operations: abs-float, sign-float, etc.
  text.cl                 ; shell: (mod display) (mod string)
  text/display.cl         ; Display trait + primitive impls
  text/string.cl          ; str macro + string operations
  fn.cl                   ; shell: (mod option) (mod result) (mod compose) (mod threading)
  fn/option.cl            ; Option type: None, Some
  fn/result.cl            ; Result type: Ok, Err + operations
  fn/compose.cl           ; compose, pipe, identity, flip
  fn/threading.cl         ; ->, ->> macros
  default.cl              ; Default trait + primitive impls
  collections.cl          ; shell: (mod pair) (mod either) (mod list) (mod vec)
  collections/pair.cl     ; Pair type + first, second, swap
  collections/either.cl   ; Either type: Left, Right + operations
  collections/list.cl     ; List type + list macro + operations
  collections/vec.cl      ; vec macro + Vec utility functions
  testing.cl              ; shell: (mod assertions) (mod runner)
  testing/assertions.cl   ; assert-eq, assert-true, assert-false
  testing/runner.cl       ; check macro, run-tests-pass-default, run-tests-fail-default, run-tests-report
  core.cl                 ; shell for core.syntax + core.io (+ re-exports)
  core/syntax.cl          ; SList helpers (standalone, not prelude dep)
  core/io.cl              ; IO combinators: pure, >>, map-io, when-io, unless-io, sequence-io
  io.cl                   ; shell: (mod monad)
  io/monad.cl             ; pure, do (IO bind-based), bind! macros
  derive.cl               ; derive macro: derive-Eq, derive-Ord, derive-Display
  plan-stdlib.md          ; normative module tree and delivery plan
```

### What works

- `prelude.cl` is a pure re-export shell using only `(export ...)` forms
- Domain modules compiled in dependency order (toposorted)
- Traits (Num, Eq, Ord, Display) defined in domain modules, re-exported through prelude
- Option and Result types in separate modules
- Function composition utilities (compose, pipe, identity, flip)
- Default trait with primitive impls
- Pair and Either types with operations
- Testing assertions (assert-eq, assert-true, assert-false)
- Testing runner (check macro, run-tests-pass-default, run-tests-fail-default, run-tests-report)
- Threading macros (`->`, `->>`) in `fn/threading.cl`
- String operations + `str` macro in `text/string.cl`
- Int operations (rem, abs, sign, negate, even?, odd?, min-int, max-int, clamp)
- Float operations (abs-float, sign-float, negate-float, min-float, max-float, clamp-float)
- Vec utilities + `vec` macro in `collections/vec.cl`
- List type + `list` macro in `collections/list.cl` with operations
- Control flow macros (when, unless, cond, case) in `control.cl`
- Definition macros (const, const-, def, def-) in `defs.cl`
- IO monadic interface (pure, do, bind!) in `io/monad.cl`
- `do` macro uses IO semantics (bind-based) per spec §10.4
- IO combinators (>>, map-io, when-io, unless-io, sequence-io) in `core/io.cl`
- Derive macro (derive-Eq, derive-Ord, derive-Display) ported from sketch

### Known blockers

- **No floor/ceil/round**: Float operations limited to what can be built from
  existing Ring 0 primitives. Need runtime extern functions for IEEE 754 rounding.
- **IO combinators untested**: `core/io.cl` is written but cannot be tested
  until the backend IO trampoline (I2) and platform DLL loading (I3) are complete.

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
- `testing.runner`: check, run-tests-pass-default, run-tests-fail-default, run-tests-report
- `derive`: derive, derive-Eq, derive-Ord, derive-Display
- `core.io`: >>, map-io, when-io, unless-io, sequence-io

### Prelude re-exports

Traits: Eq, Ord, Num, Display (with =, !=, <, >, <=, >=, +, -, *, /, show)
Types: Option (None, Some), Result (Ok, Err), List (Nil, Cons, empty?)
Functions: pure, str-eq
Macros: ->, ->>, vec, when, unless, const, const-, do, cond, list, str, case, def, def-, bind!
Primitives (30, re-exported from `primitives` for `--run` parity with the REPL surface — see design/stdlib/examples-run-path.md): add-i64, sub-i64, mul-i64, div-i64, eq-i64, lt-i64, gt-i64, le-i64, ge-i64, not, eq-bool, add-f64, sub-f64, mul-f64, div-f64, eq-f64, lt-f64, gt-f64, le-f64, ge-f64, str-concat, str-eq, str-len, char-at, int-to-string, float-to-string, bool-to-string, vec-len, vec-get, vec-set, vec-push

## Conventions

- Trait method parameter names use `self` syntax per spec section 7.1
- Primitive names match the Ring 0/1 tables exactly (add-i64, str-concat, etc.)
- Macro bodies inline helper logic rather than calling defn-defined helpers
  (because defn forms are Phase 4, macros are Phase 3)
- Domain modules use `(import [...])` to declare dependencies
- Shell modules (compare.cl, num.cl, etc.) contain only `(mod ...)` declarations
- Prelude uses only `(export ...)` forms — pure re-export shell
- Modules outside prelude graph (derive.cl) use primitives directly, not trait operators
- Macros in submodules are registered in both expander AND symbol table (pipeline fix)
- **All stdlib modules MUST include `(import [prelude []])`** — the null import (spec §8.3.6) suppresses the implicit prelude glob (spec §8.8.1). This is required because any stdlib module could be re-exported by a project's custom prelude, and importing from a prelude that depends on you is a circular dependency. Stdlib modules use only primitives and explicit imports from each other, never prelude symbols.

## Pipeline Changes

### Sprint 17 Wave 2: Export-based module discovery

`discover_import_dependencies` in `src/pipeline.rs` was extended to also process
`(export ...)` specs during module graph discovery. Previously, exports were
excluded because they referenced submodules already discovered via `(mod ...)`
declarations. With the prelude converted to a pure re-export shell, exports now
reference root-level domain modules that need discovery. The function iterates
over both `import_specs` and `export_specs` module paths.

### Sprint 14 Wave 3: Macro symbol table registration

`compile_and_register_macro` in `src/pipeline.rs` was updated to register macros
in the current module's symbol table (as `ModuleEntry::Macro`), not just in the
expander's `MacroEnv`. Without this, macros defined in submodules could not be
imported by other modules via `(import [module [macro-name]])`. The REPL's
`eval_defmacro` already did this; the batch pipeline was missing it.

## Key Architecture Finding

The `load_prelude` function already supports multi-file module discovery.
It calls `discover_module_graph` on `prelude.cl`, which follows `(mod ...)`,
`(import [...])`, and `(export [...])` references to discover and toposort all
dependent modules. `set_current_module` correctly seeds new modules with
primitives from `user`.

A pipeline fix was needed: modules with only type definitions (e.g., fn/option.cl)
or only trait declarations have no function definitions for codegen. The pipeline
now skips codegen for such modules after typechecking (which registers the types
and traits).
