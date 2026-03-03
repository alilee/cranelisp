# src/

Cross-cutting source conventions for the Cranelisp reimplementation. All compiler skills must follow these rules. Local `CLAUDE.md` files in subdirectories may add conventions but must not contradict these.

## Error Handling

- **No `unwrap()` in pipeline code.** Use `?` with `CranelispError`. `unwrap()` is permitted only in tests and in `main()`.
- **No `panic!()`** Use `unreachable!("invariant: <description>")` for true programmer errors (logic bugs that should never occur). Never `panic!` on user input.
- **No `expect()` in pipeline code.** If the value might be None/Err due to user input, return a proper error. If it's a programmer invariant, use `unreachable!`.
- **Every error carries a `Span`** for source location. Parse errors use byte offset converted to Span at the reader boundary.
- **Warnings are data, not side effects.** Accumulate `Vec<Warning>`, never `eprintln!`. Warnings flow to the caller and are displayed by the binary crate.

## Code Structure

- **Max ~100 lines per function.** If a function grows beyond this, decompose it into named helpers. Long functions are the prototype's primary structural debt.
- **Max 8 parameters.** Group related parameters into context structs. The prototype's `compile_function` had 21 parameters — this must not recur.
- **One dispatch method per Expr variant.** `infer_expr` and `compile_expr` dispatch to `infer_let`, `infer_apply`, `compile_let`, `compile_apply`, etc.
- **Named structs for multi-field returns.** No bare tuples `(Vec<Type>, Type, String)` — use `MonoDefn`, `OverloadVariant`, etc.

## Naming Conventions

- **String newtypes for all identifiers.** `Symbol`, `ModuleFullPath`, `FQSymbol`, `TraitName`, `TypeName`, `ModuleName`, `JitSymbol`. Never pass bare `String` or `&str` where a typed identifier is expected.
- **Named constants for magic numbers.** `GOT_TABLE_SIZE`, `NULLARY_TAG_THRESHOLD`, etc. No bare numeric literals in logic.
- **Rust naming conventions.** `snake_case` for functions and variables, `CamelCase` for types and enum variants, `SCREAMING_SNAKE` for constants.

## Scope Management

- **Scope stack (push/pop), not `env.clone()`.** The prototype cloned `local_env` (~70+ entries) at every scope boundary. Use a stack-based approach: push a scope frame, pop on exit.
- **Consuming calling convention.** Callee owns heap parameters. Caller emits inc for non-last-use, or transfers ownership for last-use.

## Serialization

- **Serde derives on all cross-boundary types.** `#[derive(Serialize, Deserialize)]` on types in `cranelisp-types`.
- **`#[serde(skip)]` for runtime-only fields.** Function pointers, JIT handles, `Duration` — skip with sensible defaults.

## Type System

- **Ring 0 defines the full `Type` enum.** All variants (`Int`, `Bool`, `String`, `Float`, `Fn`, `ADT`, `Var`, `TyConApp`) exist from the start. Rings exercise them incrementally.
- **`Type::from_name()` / `Type::type_name()`** centralize primitive name mapping. No scattered match blocks.
- **`TypeId` is `u32`.** Not `usize`. 4 billion type variables is sufficient.

## Testing

- **Every module gets `#[cfg(test)] mod tests`.** Unit tests live next to the code they test.
- **Integration tests in `tests/`.** Owned by `/qa`, organized by ring.
- **Test names describe the behavior, not the implementation.** `test_let_polymorphism_infers_identity` not `test_case_47`.

## Dependencies Between Crates

- `cranelisp-types`: no dependencies (except `serde`, `std`)
- `cranelisp-frontend`: depends on `cranelisp-types`
- `cranelisp-typecheck`: depends on `cranelisp-types`
- `cranelisp-backend`: depends on `cranelisp-types`, `cranelisp-runtime`
- `cranelisp-runtime`: depends on `cranelisp-platform`
- `cranelisp-platform`: no dependencies (except `std`)
- `cranelisp` (binary): depends on all above

No circular dependencies. Cargo enforces this at build time.
