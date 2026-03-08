# Pipeline Orchestration: Prelude Loading and Macro Integration

Design document for wiring the CraneliftExpander into the compilation pipeline, enabling prelude loading through normal module resolution, and eliminating Decision 17's interim trait registration.

## Requirements Summary

Seven concrete problems (P1-P7) blocked the previous implementation attempt. Additionally, Decision 17 (compiler-seeded traits) must be eliminated now that prelude loading is being implemented.

| ID | Problem | Owner |
|---|---|---|
| P1 | `macros/sconcat` — quasiquote emits qualified reference that typechecker can't resolve | /typecheck, /backend |
| P2 | `quote-sexp` — primitive not registered in typechecker or JIT | /typecheck, /backend |
| P3 | Prelude loading — how `stdlib/` gets compiled and wired into session | /qa |
| P4 | Cross-module calls — functions from one JIT module callable in another | /backend |
| P5 | `& rest` vs `&rest` — reader whitespace handling for rest params | n/a (both work) |
| P6 | Recursive ADT pre-seeding — self-referencing type fields | /typecheck |
| P7 | Match var-pattern alias double-dec — RC bug in match codegen | /backend |
| D17 | Eliminate compiler-seeded traits — Num, Eq, Ord, Display belong in prelude `.cl` files | /typecheck, /stdlib, /qa |

## Key Design Principle: Prelude Is Not Special

The prelude is ordinary user code. It is a module named `prelude`, resolved through the standard module search sequence (project root → `stdlib/`), and compiled through the standard `compile_module_graph` pipeline. There is no separate bootstrap path.

The **only** special behavior is: unless a module has an explicit `(import [prelude [...]])` statement, the compiler injects an implicit `(import [prelude [*]])`. This is the same mechanism as the sketch (`sketch/src/repl.rs:937`).

Consequences:
- A local `prelude.cl` at the project root overrides `stdlib/prelude.cl` (normal module resolution priority)
- An **empty** `prelude.cl` is valid — it gives the user a clean slate with no macros, no traits, no operators
- The prelude can depend on other modules via `(import ...)` and `(mod ...)` — these are resolved normally
- The compiler works without any prelude at all (no `prelude.cl` found → no implicit import → named primitives still available)

## 1. Startup Sequence

```
1. TypeChecker::new()
     register_primitives()         → Ring 0 named primitives in `primitives` module
     register_ring1_primitives()   → Ring 1 string/conversion externs
     register_vec_primitives()     → Vec polymorphic externs
     register_special_forms()      → special form metadata
     register_macros_module()      → Sexp, SList ADTs + sconcat extern in `macros` module
     register_ring3_primitives()   → quote-sexp in `primitives` (requires Sexp from above)
     import_primitives_into_user() → copy primitives → user

2. CraneliftExpander::new()       → empty MacroEnv

3. Resolve and compile prelude module (if found):
     resolve "prelude" via normal module resolution (project root → stdlib/)
     if found: build ModuleGraph → compile_module_graph()
     inject implicit (import [prelude [*]]) into user module

4. Begin processing user input (batch compile_and_run / REPL eval loop)
```

**What changed from prior rings**: `register_core_trait_decls()` and `register_core_trait_impls()` are **removed** (Decision 17 elimination). Traits come from prelude `.cl` files during step 3.

Step 3 is **optional**. If no `prelude` module is found, the system proceeds without it. Named primitives (`add-i64`, `str-concat`, etc.) remain available via the `primitives` module.

## 2. Module Compilation Pipeline

### Sequential Form Processing (Per-Module)

Every module — prelude modules, user modules, library modules — is compiled with this two-pass model within `compile_module_graph`. This matches the sketch (`sketch/src/batch.rs:301-466`, `sketch/src/repl.rs:301-466`).

**Pass 1 — Type pre-registration**:
```
for each sexp in module:
    if sexp is (deftype ...):
        build AST, register_type_def()
```

**Pass 2 — Sequential compilation**:
```
for each sexp in module:
    if (deftype): skip (registered in Pass 1)

    if (defmacro):
        compile_and_register_macro(sexp)
        continue

    expand macros in sexp
    flatten (begin ...) results
    for each form in flattened:
        if (defmacro): compile_and_register_macro (defmacro-in-results)
        if (deftype): register_type_def (type-in-results)
        else: accumulate for batch compilation

    compile accumulated non-macro, non-type forms:
        build AST → typecheck → codegen
        handle TraitDecl, TraitImpl, Defn normally
```

This is the same loop for ALL modules: `core/numerics.cl` (traits), `core/syntax.cl` (macros), user code. No special cases.

**Current state**: `process_forms_sequentially()` in `src/pipeline.rs` implements this for single-module batch compilation. It needs to be used within `compile_module_graph` for each module in the topological order.

### Prelude Module Structure (Matching Sketch)

```
stdlib/prelude.cl          → re-export shell: (export [core [*] primitives [...]])
stdlib/core.cl             → (mod numerics) (mod formats) (mod collections) (mod syntax) ... (export [...])
stdlib/core/numerics.cl    → deftrait Num/Eq/Ord + impl for Int/Float/String/Bool
stdlib/core/formats.cl     → deftrait Display + impl for Int/Float/Bool/String
stdlib/core/collections.cl → deftype List, operations, deftrait Functor
stdlib/core/syntax.cl      → SList helpers + defmacro list/do/cond/str/->/->>/case/etc.
```

The prelude compiles through `compile_module_graph` just like any user project. Module graph toposort ensures `core/numerics.cl` compiles before modules that use operators, and `core/syntax.cl` compiles before modules that use macros.

## 3. Synthetic Primitive Resolution (P1 + P2)

### P1: `sconcat`

**Decision**: Register `sconcat` as an extern primitive in the `macros` module, backed by `cranelisp-runtime::marshal::sconcat`. This matches the sketch.

**Why**: The quasiquote expander emits `macros/sconcat`. Making it a runtime extern means it's available before any `.cl` file loads — no bootstrapping ordering concerns.

**Implementation**:
1. `/typecheck` (`builtins.rs`): In `register_macros_module()`, register `sconcat` as extern primitive
   - Type: `(Fn [(SList Sexp) (SList Sexp)] (SList Sexp))`
   - DefKind: `Primitive { primitive_kind: PrimitiveKind::Extern }`
2. `/backend` (`jit.rs`): `builder.symbol("sconcat", cranelisp_runtime::sconcat as *const u8)`
3. `/backend` (`apply.rs`): Add `"sconcat"` to `is_extern_primitive()` list

### Qualified Primitive Resolution

The typechecker's `is_primitive()` in `infer.rs` only checks `resolve_entry_in_current_module(name)`, which doesn't handle qualified names like `macros/sconcat`. When a macro body calls `macros/sconcat`, it won't get `ResolvedCall::BuiltinFn` registration.

**Fix**: Change `is_primitive()` → `resolve_primitive_jit_name()` returning `Option<Symbol>`. When `name` contains `/`, split into module/name, look up in the target module, check for `DefKind::Primitive`. Return the JIT-level name (bare name, not qualified) for `ResolvedCall::BuiltinFn`.

This is a `/typecheck` change: `is_primitive()` and its one call site in `infer_apply`.

### P2: `quote-sexp`

**Decision**: Register as extern primitive in `primitives` module, backed by `cranelisp-runtime::marshal::quote_sexp`. Per `spec/appendix-a-builtins.md`.

**Implementation**:
1. `/typecheck` (`builtins.rs`): Register in primitives AFTER `register_macros_module()` (type references `Sexp`)
   - Type: `(Fn [Sexp] Sexp)`
2. `/backend` (`jit.rs`): `builder.symbol("quote-sexp", cranelisp_runtime::quote_sexp as *const u8)`
3. `/backend` (`apply.rs`): Add `"quote-sexp"` to `is_extern_primitive()` list
4. `cranelisp-types` (`operator.rs`): Add to primitive definitions

### Registration Order

```
1. register_primitives()          → types + Ring 0 inline prims
2. register_ring1_primitives()    → str-concat, int-to-string, etc.
3. register_vec_primitives()      → vec-get, vec-set, etc.
4. register_special_forms()       → defn, let, if, match, deftrait, impl, defmacro, etc.
5. register_macros_module()       → Sexp, SList ADTs + sconcat extern
6. register_ring3_primitives()    → quote-sexp (requires Sexp type from step 5)
7. import_primitives_into_user()  → copy genuine primitives → user
```

## 4. Cross-Module Call Mechanism (P4)

**Decision**: `Jit::new_with_symbols()` — pre-register function pointers from previously compiled JIT modules on the JITBuilder.

```rust
pub fn new_with_symbols(
    extra_symbols: &[(&str, *const u8)],
) -> Result<Self, CranelispError>
```

Same mechanism as runtime intrinsics. When `compile_module_graph` compiles module A, it extracts function pointers. When compiling module B (which depends on A), it creates a JIT with A's symbols pre-registered. All JIT modules stored in session to keep code alive.

## 5. Decision 17 Elimination (D17)

**Decision**: Remove `register_core_trait_decls()` and `register_core_trait_impls()` from `builtins.rs`. Traits are ordinary Cranelisp defined in prelude `.cl` files.

**What stays compiler-seeded** (genuinely primitive):
- Primitive types: `Int`, `Bool`, `Float`, `String`
- Named primitives: `add-i64`, `str-concat`, `vec-get`, etc.
- Special forms: `defn`, `let`, `if`, `match`, `fn`, `deftype`, `deftrait`, `impl`, `defmacro`, `mod`, `import`, `export`
- Synthetic module types: `Sexp`, `SList` (in `macros`), `Vec` (in `primitives`)
- Synthetic extern primitives: `sconcat` (in `macros`), `quote-sexp` (in `primitives`)

**What moves to prelude `.cl` files**:
- `deftrait Num/Eq/Ord/Display` and all `impl` forms
- Convenience functions: `inc`, default methods for `<=`/`>=`

**Impact on tests**: Tests using operators need to either load the prelude, define traits inline, or use named primitives. Most Ring 0-1 tests already use named primitives. Ring 2 trait dispatch tests should define traits inline — this makes dependencies explicit.

**Implementation**:
1. `/typecheck`: Remove `register_core_trait_decls()`, `register_core_trait_impls()` from `builtins.rs`
2. `/stdlib`: Create `stdlib/core/numerics.cl`, `stdlib/core/formats.cl` (matching sketch). Update `stdlib/core.cl`, `stdlib/prelude.cl`.
3. `/qa`: Fix tests that break — switch to named primitives or inline trait definitions

## 6. Remaining Problem Resolutions

### P5: `& rest` vs `&rest`
Both forms work. No action needed.

### P6: Recursive ADT type pre-seeding
Handled by the type pre-registration pass (Pass 1 in §2). No new mechanism needed.

### P7: Match var-pattern alias double-dec
Backend codegen bug. When a match var pattern aliases an existing variable, the alias should NOT be registered in `scope_stack` for RC cleanup. `/backend` fix in `match_codegen.rs`.

## 7. Crate Responsibilities

| Crate | Changes |
|---|---|
| `cranelisp-types` | Add `quote-sexp` to primitive definitions |
| `cranelisp-frontend` | None |
| `cranelisp-typecheck` | Register `sconcat`/`quote-sexp` as externs; extend `is_primitive()` for qualified names; remove Decision 17 trait registration |
| `cranelisp-backend` | Register JIT symbols; `Jit::new_with_symbols()`; update `is_extern_primitive()` list; fix P7 |
| `cranelisp-runtime` | None — `sconcat` and `quote_sexp` already exist |
| `cranelisp` (binary) | Wire prelude resolution + `compile_module_graph` into startup; inject implicit import |

## 8. Risks and Mitigations

| Risk | Mitigation |
|---|---|
| JIT module lifetime — prelude code freed while referenced | Store JIT modules in session (same as macro JIT lifetime) |
| No prelude found — tests/programs without `stdlib/` | Implicit import skipped; named primitives still available |
| Circular prelude import | Implicit import injected AFTER prelude compiles; toposort prevents cycles |
| Decision 17 test breakage | Mechanical fix: named primitives or inline traits |
| `sconcat` ordering | Runtime extern registered at startup, before any `.cl` loads |
