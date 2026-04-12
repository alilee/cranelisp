# Sprint 50 Typecheck Fixes

Two fixes targeting regressions RC4 (builtin type leaking) and RC5 (macro body type checking).

## Fix 1: Builtin Type Leaking (RC4)

### Problem

`ensure_module_exists` in `crates/cranelisp-typecheck/src/checker.rs` (line 296) seeds every new module with entries copied from the `user` module's symbol table. The filter at line 314-322 allows through:

1. `ModuleEntry::Def` with `DefKind::SpecialForm` -- correct, spec §11.1
2. **All** `ModuleEntry::TypeDef` entries -- **wrong**
3. `ModuleEntry::Constructor` where `is_root_type_constructor` matches -- partially wrong
4. Entries matching `is_root_primitive` (`discover-tests`, `run-test`) -- wrong

The `user` module inherits builtin type names (`Int`, `Bool`, `Float`, `String`, `Vec`) and test infrastructure types (`TestResult`) from compiler seeding. Because the filter passes all `TypeDef` entries unconditionally, these leak into every new module. The `/list` command then shows them as user-defined types, causing ~7 test failures:

- `e2e_s3_3_list_empty_module` -- expects `(no definitions)`, gets types
- `list_neg_fresh_session_special_forms_only` -- expects empty Types, finds `Int`, `Bool`, etc.
- `list_neg_no_primitives_types_in_types` -- explicitly checks for absence of primitive types

### Spec reference

Spec §8.9.1: builtin types (`Int`, `Bool`, `String`, `Float`, `Vec`) live in the `primitives` module. They are stored in qualified form only (`primitives/Int`) and are NOT available as bare names unless imported through the prelude chain.

Spec §8.9.4: synthetic modules are always known to the module system, but their names require explicit import.

### Proposed solution

Remove the blanket `ModuleEntry::TypeDef` pass-through from `ensure_module_exists`. Only special forms should be seeded into new modules. The specific changes:

1. **Delete the `ModuleEntry::TypeDef` arm** from the filter in `ensure_module_exists` (line 318). No type definitions should be copied from `user` into new modules. Builtin types are in `primitives` and accessed via import; user-defined types belong to the module that defines them.

2. **Delete `is_root_type_constructor`** (line 197-199) and the `ModuleEntry::Constructor` arm (line 319-320). `TestResult` constructors (`TestPass`, `TestFail`) should not be globally seeded. They belong to whatever module defines the test infrastructure and should be imported explicitly.

3. **Delete `is_root_primitive`** (line 203-205) and its filter arm (line 321). `discover-tests` and `run-test` are test infrastructure functions, not language primitives. They should be imported explicitly by modules that need them.

After this change, `ensure_module_exists` seeds ONLY special forms. This matches the spec: special forms are language keywords universally available (spec §11.1); everything else requires explicit import or qualified access.

### Affected files

| File | Change |
|---|---|
| `crates/cranelisp-typecheck/src/checker.rs` | Simplify `ensure_module_exists` filter to special forms only; delete `is_root_type_constructor` and `is_root_primitive` helper functions |

### Risks

- **Modules that relied on implicit type visibility**: If any module code assumes `Int`, `Bool`, etc. are in scope without import, it will break. However, this is the correct behavior per spec §8.9.1. The prelude chain provides these names through explicit import, and test fixtures that use bare primitive names are already being fixed in Wave 3a (RC3).

- **TestResult/discover-tests/run-test availability**: The `run-tests` special form (RC6) depends on `TestResult`. If it was relying on global seeding, it will need to be updated to use explicit imports. This is out of scope for Sprint 50 (RC6 may be deferred to Sprint 51).

- **Low risk overall**: The change is a deletion (removing filter arms), not an addition. The result is a stricter, spec-compliant module boundary.

## Fix 2: Macro Body Type Checking (RC5)

### Problem

In the v4 pipeline, `defmacro` forms are processed in two phases:

- **Pass 1** (`register_macro_in_module`, worker.rs line 643): Parses clause info and stores `ModuleEntry::Macro` in the symbol table. No AST building, no typechecking, no codegen. The macro body sexp is stored for later use.

- **First use** (`compile_macro_clause_inline`, worker.rs line 1701): When a macro is first called during expansion, the clause body is synthesized into a `defn`, expanded (quasiquotes), built into AST, typechecked, and compiled. Type errors surface here.

This means a macro with a type error in its body (`(defmacro bad [x] 42)` -- returns `Int` instead of `Sexp`) succeeds at definition time and only fails when first used. The batch test `neg_macro_non_sexp_return_type_batch` passes because it includes a call `(bad 1)` that triggers compilation. The REPL tests fail because they expect the error at definition time:

- `neg_macro_non_sexp_return_type_repl` -- `s.eval("(defmacro bad [x] 42)")` expected to be `Err`
- `r3_neg_macro_body_must_return_sexp` -- same pattern, also checks error message mentions `Sexp`

### Spec reference

Spec §9.2.3: "The body of a macro MUST return a value of type Sexp. If the body has any other type, the implementation MUST report a compile-time error."

The spec says "compile-time error" without specifying whether that means definition time or first-use time. However, the MUST language and the phrase "compile-time" strongly suggest the error should be caught at the earliest possible point -- definition time.

### Design decision: Eager type checking at definition time

**Recommendation**: Add eager type checking of macro clause bodies during Pass 1 registration, immediately after `register_macro_in_module`. This is the better DX: errors are caught at the point of definition, matching user expectations and the spec's intent.

### Proposed solution

After `register_macro_in_module` succeeds in the Pass 1 loop (worker.rs line 537-539), call `compile_macro_clause_inline` for each clause. This already exists and performs the full synthesize-expand-typecheck-compile pipeline. The type error will surface during Step 4 (typecheck) inside `compile_macro_clause_inline`.

Specifically, change the Pass 1 macro registration block from:

```rust
for (name, info, sexp) in &macro_infos {
    register_macro_in_module(ctx.tc, name, info, sexp)?;
}
```

to:

```rust
for (name, info, sexp) in &macro_infos {
    register_macro_in_module(ctx.tc, name, info, sexp)?;
    // Eagerly compile macro clauses to catch type errors at definition time.
    // spec §9.2.3: body MUST return Sexp; report error at compile time.
    compile_macro_if_needed(ctx, module, info, sexp.span(), accumulator)?;
}
```

`compile_macro_if_needed` (worker.rs line ~1496) already handles:
- Checking if clauses are already compiled (skips if so)
- Resolving transitive callee dependencies
- Calling `compile_macro_clause_inline` for each uncompiled clause

This means the typechecker runs on the synthesized defn immediately. If the body returns `Int` instead of `Sexp`, unification fails and the error propagates through `?` back to the caller.

### Side effect: eager compilation

Eager type checking implies eager compilation (codegen), not just type checking alone. `compile_macro_clause_inline` runs Steps 1-5 including Cranelift codegen. This is acceptable because:

1. The compiled code pointer is needed anyway at first use -- we just do it earlier.
2. Macro clause functions are small (one synthesized defn per clause).
3. The existing deferred-compilation path (`compile_macro_if_needed`) already short-circuits if code pointers exist, so no double compilation occurs.

Alternatively, we could split `compile_macro_clause_inline` into a typecheck-only path and a full compile path. This adds complexity for no practical benefit -- macro clause compilation is cheap and always needed eventually.

### Affected files

| File | Change |
|---|---|
| `src/worker.rs` | Add `compile_macro_if_needed` call after `register_macro_in_module` in the Pass 1 loop (~line 538) |

### Risks

- **Ordering dependencies**: If a macro body references symbols that haven't been registered yet in Pass 1, the typecheck will fail with an "undefined variable" error instead of succeeding and catching it later. However, the current pipeline processes all Pass 1 registrations before Pass 2, and macro bodies primarily reference `macros/` module constructors (available via quasiquote expansion) and primitives. User-defined symbols referenced in macro bodies would fail at first use anyway, so early failure is still correct.

- **Macro-calls-macro chains**: If macro A's body calls macro B (which is also defined in the same batch), macro B must be compiled before macro A's body can be typechecked. The current `compile_macro_if_needed` handles transitive deps via `collect_transitive_uncompiled_deps`, so this should work -- but it depends on macro B being registered in the symbol table first. Since Pass 1 processes all `register_macro_in_module` calls before the eager compilation loop, an adjustment may be needed: register ALL macros first, THEN eagerly compile all. This can be done by splitting the loop into two passes:

```rust
// First: register all macros in symbol table
for (name, info, sexp) in &macro_infos {
    register_macro_in_module(ctx.tc, name, info, sexp)?;
}
// Second: eagerly compile all macro clauses (type check + codegen)
for (name, info, sexp) in &macro_infos {
    compile_macro_if_needed(ctx, module, info, sexp.span(), accumulator)?;
}
```

This two-pass approach ensures all macro names are visible before any body is compiled.

- **Wave 3a interaction**: The macro resolver refactor (RC1) is changing how macros are compiled. The eager compilation call should use whatever compilation path the refactor settles on. If the refactor changes `compile_macro_if_needed` or `compile_macro_clause_inline`, the eager call site needs to match. Coordinate with `/int` during Wave 3b.

## Fix 3: TypeChecker State-Holding Methods for Macro Resolver (Wave 3 Coordination)

### Problem

The `SymbolTableMacroResolver` (being introduced in Wave 3a by `/int` skill) needs to hold `&mut CheckState` separately from `&TypeChecker` to enable borrow-scoped isolation during macro expansion. The resolver holds the mutable reference across phases, but needs to read the TypeChecker's symbol tables and module information without simultaneously holding a mutable borrow.

Currently, `TypeChecker.state` can only be accessed by `&mut self`, forcing code to choose: either hold a mutable borrow of state (preventing immutable borrows of the rest of the TypeChecker), or drop the mutable borrow (losing the reference). This creates a "borrow scoping" problem that the resolver needs to solve.

### Spec reference

Spec §1 (general): typechecking must be isolated per-expansion to ensure macro-defined names don't leak into subsequent expansions.

### Design decision: Interior mutation wrapper

**Recommendation**: Add `take_state()` and `restore_state()` methods to `TypeChecker` that use `mem::replace` to move `self.state` in and out of the TypeChecker, allowing the resolver to hold `&mut CheckState` independently while still accessing the TypeChecker for symbol lookups and module info.

### Proposed solution

Add two methods to `TypeChecker` in `crates/cranelisp-typecheck/src/checker.rs`:

```rust
/// Extract the mutable CheckState from the TypeChecker, leaving a temporary
/// placeholder. Used by scope-isolating code paths (e.g., SymbolTableMacroResolver)
/// that need to hold &mut CheckState while accessing &TypeChecker for symbol info.
///
/// IMPORTANT: Must be paired with restore_state() to rebuild the TypeChecker.
/// Do not drop the returned state without restoring it.
pub fn take_state(&mut self) -> CheckState {
    mem::replace(&mut self.state, CheckState::default())
}

/// Restore the CheckState to the TypeChecker, replacing whatever temporary state
/// was left in its place. Inverse of take_state().
pub fn restore_state(&mut self, state: CheckState) {
    self.state = state;
}
```

This pattern mirrors the existing usage inside `check_form` (program.rs:346-360) where state is temporarily swapped:

```rust
let old_state = mem::replace(&mut self.state, ...);
// ... use new state ...
self.state = mem::replace(&mut self.state, old_state);
```

The resolver can now hold `&mut CheckState` in a local variable while accessing `&TypeChecker` methods:

```rust
let mut state = tc.take_state();
// Now can use &tc for symbol lookups while holding &mut state
// ... resolver logic ...
tc.restore_state(state);
```

### Affected files

| File | Change |
|---|---|
| `crates/cranelisp-typecheck/src/checker.rs` | Add `take_state()` and `restore_state()` public methods (~50 lines) |

### Risks

- **Temporary invalid state**: If `take_state()` is called but `restore_state()` is never called, the TypeChecker is left in an invalid state (default CheckState). This is caught by the type system if the caller follows the pattern (scope-guard unwinding), but there is no compile-time enforcement. Document in comments that these methods must always be paired.

- **Accidental mutation during state absence**: Code that tries to access `tc.state` while it's been taken out will see a default CheckState, potentially reading/writing wrong values. However, this is only a problem if code inside the resolver tries to access `tc.state` directly rather than passing it explicitly. Use interior-mutability patterns (hold the reference explicitly) to prevent this.

- **Low risk overall**: The change is a small, mechanical API addition that doesn't change semantics. It just makes interior state movement explicit and safe.

### Coordination with Wave 3a

This API is needed by the `/int` skill's `SymbolTableMacroResolver` during macro expansion refactoring (Wave 3a). The `/typecheck` skill should implement this as part of its Wave 3 deliverables. No additional coordination is needed beyond confirming that `take_state()` and `restore_state()` are the right pattern for the resolver's borrow scope.

## Implementation order

1. Fix 1 (builtin type leaking) first -- it is a pure deletion with no dependencies on other Wave 3 work.
2. Fix 2 (macro body type checking) second -- coordinate with `/int` on the exact compilation function to call, since Wave 3a may refactor the macro compilation path.
3. Fix 3 (state-holding methods) third -- this is a small API addition that unblocks the macro resolver refactor in Wave 3a. Can be implemented in parallel with Fixes 1 and 2.
