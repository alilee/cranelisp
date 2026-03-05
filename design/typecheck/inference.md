# Inference Engine

Solution design for the Cranelisp type inference engine. Covers Algorithm W implementation, unification, substitution strategy, and per-ring evolution.

## Architecture

The typechecker is structured as a single `TypeChecker` struct with `impl` blocks split across multiple modules using Rust's borrow-splitting pattern. Hot-path functions (`unify`, `fresh_var`) take explicit `&mut Subst` / `&mut TypeId` parameters to avoid `&mut self` conflicts.

### Module Layout

| Module | Responsibility |
|--------|---------------|
| `checker.rs` | `TypeChecker` struct definition, scope ops, fresh var generation, unification delegation |
| `infer.rs` | Expression type inference: one helper method per `Expr` variant |
| `program.rs` | Two-pass batch checking (`check_program`) and REPL input checking (`check_repl_input`) |
| `unify.rs` | Unification algorithm with occurs check |
| `scheme.rs` | Scheme instantiation (`instantiate`) and generalization (`generalize`) |
| `scope.rs` | Lexical scope stack for local bindings |
| `resolve.rs` | `TypeExpr` -> `Type` resolution (annotations, type expressions) |
| `adt.rs` | ADT registration, constructor schemes, exhaustiveness checking |
| `builtins.rs` | Ring 0 primitive type scheme registration |

### Key Design Decisions

**Borrow-splitting over method chaining**: Free functions for `unify` and `fresh_var` take `&mut Subst` / `&mut TypeId` rather than `&mut self`. This avoids borrow conflicts when inference needs both substitution and fresh variable generation simultaneously. The `TypeChecker` methods are thin wrappers.

**Per-variant infer helpers**: `infer_expr` dispatches to `infer_int_lit`, `infer_var`, `infer_lambda`, etc. Each helper is 10-40 lines, independently testable. This addresses the sketch audit finding HIGH-1 (monolithic `infer_expr`).

**Single substitution**: One global `Subst` (HashMap<TypeId, Type>) for the entire compilation unit. No separate "local" substitutions. This matches standard Algorithm W.

## Two-Pass Pipeline

Batch mode (`check_program`) uses two passes:

1. **Pass 1 — Registration**: Register type definitions (`TypeDef`), then register function signatures with fresh type variables. Functions are added to the symbol table with monomorphic schemes containing fresh vars.

2. **Pass 2 — Checking**: Check each function body. Bind parameters to the fresh vars from Pass 1, infer the body type, unify with the return type var. After all bodies are checked, generalize each function's type and update the symbol table.

This supports forward references: function `f` can call function `g` defined later in the same program, because `g`'s signature (with fresh vars) is registered before any bodies are checked.

### REPL Mode

`check_repl_input` handles one definition or expression at a time. For definitions, it does registration + body checking + generalization in a single step (no forward references across REPL inputs). The REPL supports snapshot/restore for error recovery.

## Unification

Standard Algorithm W unification with occurs check:

```
unify(Var(a), t)  = if a in fv(t) then OccursCheckError else subst[a] = t
unify(t, Var(a))  = unify(Var(a), t)
unify(Int, Int)   = ok
unify(Fn(ps1, r1), Fn(ps2, r2)) = unify each (p1, p2), then unify(r1, r2)
unify(ADT(n1, as1), ADT(n2, as2)) = if n1 == n2 then unify each (a1, a2)
unify(_, _)       = TypeError
```

The substitution is applied transitively: looking up `Var(a)` follows the chain until a non-var type is found.

## Scheme Operations

**Instantiation**: Replace quantified type variables with fresh variables. Each call to `instantiate` produces a fresh copy, enabling polymorphic use.

**Generalization**: Collect free variables in a type that do NOT appear free in the environment, and quantify over them. Uses the current substitution to resolve the type before collecting.

```
generalize(env, ty) =
  let resolved = apply(subst, ty)
  let env_fv = free_vars_in_env(env)
  let ty_fv = free_vars(resolved) - env_fv
  Scheme { vars: ty_fv, ty: resolved }
```

## Expression Type Recording

Every `infer_*` method calls `record_expr_type(span, ty)` to associate the inferred type with the expression's source span. The `expr_types` map is resolved through the substitution in `build_check_result` / `build_repl_result` before being returned to the caller.

The backend relies on `expr_types` for heap classification (via `HeapCategory::classify`). Missing entries would cause silent codegen bugs.

### Polymorphic Type Variables in expr_types

In Ring 0-1, `expr_types` may contain `Type::Var` entries for expressions inside polymorphic function bodies. For example, `(defn id [x] x)` records `x` with `Type::Var(N)` — this is correct because `x` has a universally quantified type. The invariant that all `Var` entries must be resolved activates in Ring 2 when monomorphisation produces specialized function bodies with fully concrete types.

## Per-Ring Evolution

### Ring 0 (Core)

- Int, Bool, Float literals and arithmetic
- If/else with branch unification
- Let bindings with sequential scope
- Lambda (non-capturing) and function application
- Pattern matching on nullary ADT constructors
- Forward references via two-pass pipeline

### Ring 1 (Heap) — Current

- String literal inference (`Type::String`)
- Full polymorphic ADT registration with data constructor fields
- Constructor pattern matching with field bindings
- `TypeExpr::Applied` resolution with arity validation
- `WarningKind` enum for typed warnings (M-3)
- `#[must_use]` on public API functions (M-5)

### Ring 2 (Abstraction) — Planned

- Trait declarations and implementations
- Constrained polymorphism (monomorphisation)
- Multi-signature functions
- `debug_assert!` for Type::Var-free expr_types (post-monomorphisation)

### Ring 3 (Meta) — Planned

- Module system integration
- Import resolution
- Cross-module type checking
