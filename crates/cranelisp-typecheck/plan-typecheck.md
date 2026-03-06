# Ring 0 Typechecker Plan

Plan for the `cranelisp-typecheck` crate, covering Ring 0 scope. Produced by `/typecheck` during Sprint 0, Task 6.

## 1. Ring 0 Type System Scope

Ring 0 establishes the core inference engine. The property is: **expressions, types, functions, let, if, match. No heap allocation, no reference counting.**

### 1.1 Types Exercised

| Type variant | Ring 0 usage |
|---|---|
| `Type::Int` | Integer literals, arithmetic results |
| `Type::Bool` | Boolean literals, comparison results, `if` conditions |
| `Type::Float` | Float literals, float arithmetic |
| `Type::Fn(params, ret)` | Function types (no closures -- bare function pointers) |
| `Type::Var(id)` | Unification variables (inference-internal, resolved before codegen) |
| `Type::ADT(name, vec![])` | Enum-only types (nullary constructors, bare i64 tags) |

Types NOT exercised in Ring 0: `Type::String` (Ring 1), `Type::ADT` with non-empty type args (Ring 1), `Type::TyConApp` (Ring 2+).

### 1.2 Expression Forms

All 10 Ring 0 expression variants from `ring0-interfaces.md`:

| Expression | Typing rule | Spec ref |
|---|---|---|
| `IntLit` | Constant `Int` | spec 4.1.1 |
| `FloatLit` | Constant `Float` | spec 4.1.2 |
| `BoolLit` | Constant `Bool` | spec 4.1.3 |
| `Var` | Lookup in env, instantiate scheme | spec 4.2 |
| `Let` | Infer binding, extend env (monomorphic), infer body | spec 4.3 |
| `If` | Condition unifies with `Bool`, branches unify with each other | spec 4.4 |
| `Lambda` | Fresh vars for params, infer body, produce `Fn` type | spec 4.5 |
| `Apply` | Infer callee + args, unify callee with `Fn(arg_types, fresh_ret)` | spec 4.6 |
| `Match` | Infer scrutinee, check patterns, unify arm bodies | spec 4.8 |
| `Annotate` | Infer expr, unify with annotation type | spec 4.9 |

### 1.3 Top-Level Forms

| Form | Ring 0 scope |
|---|---|
| `TopLevel::Defn` | Single-signature function definitions |
| `TopLevel::TypeDef` | Enum-only ADTs (all constructors nullary, no type params) |

NOT exercised: `DefnMulti` (Ring 2), `TraitDecl` (Ring 2), `TraitImpl` (Ring 2).

### 1.4 Builtin Operators

In Ring 0, operators are hard-wired as builtins (not trait methods). Each is registered as `DefKind::Primitive { primitive_kind: PrimitiveKind::Inline, jit_name: None }` with a fixed type scheme. The typechecker records `ResolvedCall::BuiltinFn { name }` at each call site.

| Operator | Type scheme | Cranelift IR (for backend reference) |
|---|---|---|
| `+` | `(Fn [Int Int] Int)` and `(Fn [Float Float] Float)` | `iadd` / `fadd` |
| `-` | `(Fn [Int Int] Int)` and `(Fn [Float Float] Float)` | `isub` / `fsub` |
| `*` | `(Fn [Int Int] Int)` and `(Fn [Float Float] Float)` | `imul` / `fmul` |
| `/` | `(Fn [Int Int] Int)` and `(Fn [Float Float] Float)` | `sdiv` / `fdiv` |
| `=` | `(Fn [Int Int] Bool)` and `(Fn [Float Float] Bool)` | `icmp eq` / `fcmp eq` |
| `<` | `(Fn [Int Int] Bool)` and `(Fn [Float Float] Bool)` | `icmp slt` / `fcmp lt` |
| `>` | `(Fn [Int Int] Bool)` and `(Fn [Float Float] Bool)` | `icmp sgt` / `fcmp gt` |
| `<=` | `(Fn [Int Int] Bool)` and `(Fn [Float Float] Bool)` | `icmp sle` / `fcmp le` |
| `>=` | `(Fn [Int Int] Bool)` and `(Fn [Float Float] Bool)` | `icmp sge` / `fcmp ge` |
| `not` | `(Fn [Bool] Bool)` | `bxor` with 1 |

**Ring 0 operator type resolution strategy**: Since Ring 0 has no traits, operators like `+` cannot be fully polymorphic (they would need `Num` constraints). Instead, each arithmetic/comparison operator is registered with TWO type entries: one for `Int` operands and one for `Float` operands. The typechecker resolves the concrete overload at the call site by attempting unification with each candidate:

1. Infer argument types.
2. Try unifying with the `Int` signature.
3. If that fails, try unifying with the `Float` signature.
4. If both fail, type error.

This is a temporary mechanism -- in Ring 2, operators become trait methods (`Num.+`, `Eq.=`, `Ord.<`) and this hard-wired dispatch is removed. The critical design decision: **use `ResolvedCall::BuiltinFn` for all Ring 0 operators**. This is a simpler variant than `TraitMethod` and avoids needing any trait infrastructure. The backend interprets `BuiltinFn { name: "+" }` to emit inline Cranelift IR.

### 1.5 Let-Polymorphism

Ring 0 implements let-polymorphism at the `defn` boundary only (consistent with spec 3.5.2):

- **`defn` bodies**: After checking the body, generalize over free type variables that are not in the module-level environment. Example: `(defn id [x] x)` generalizes to `forall [a]. (Fn [a] a)`.
- **`let` bindings**: NOT generalized. `(let [f (fn [x] x)] ...)` gives `f` a monomorphic scheme. This matches the spec (3.5.3 "Let Binding" -- `Mono(T1)`).
- **`lambda` parameters**: Fresh type variables, unified with usage. No generalization within lambda bodies.

### 1.6 Pattern Matching (Enum-Only)

Ring 0 `match` handles enum-only ADTs (nullary constructors):

- **Constructor patterns**: Bare symbol matching a known constructor. Empty `bindings` vector.
- **Wildcard patterns**: Match anything, bind nothing.
- **Variable patterns**: Match anything, bind the scrutinee to the name.
- **Exhaustiveness**: Required for concrete ADT scrutinees. Check that all constructors are covered, or that a wildcard/variable pattern exists.
- **Type checking**: Scrutinee type unifies with the constructor's parent ADT type. All arm bodies unify to a single result type.

Data constructor patterns (with field bindings) are Ring 1.

---

## 2. Algorithm W Implementation Plan

### 2.1 Core State

The `TypeChecker` struct holds the mutable state for inference:

```
TypeChecker {
    next_id: TypeId,                              // monotonic counter for fresh vars
    subst: Subst,                                 // HashMap<TypeId, Type>
    scope_stack: Vec<HashMap<Symbol, Scheme>>,     // lexical scope stack (see 2.3)
    expr_types: HashMap<Span, Type>,              // inferred type per expression
    builtin_resolutions: HashMap<Span, ResolvedCall>, // Ring 0: BuiltinFn only
    warnings: Vec<Warning>,                       // accumulated diagnostics
    symbol_table: SymbolTable,                    // single module ("user") in Ring 0
}
```

Key differences from the prototype:
- **No `local_env: HashMap<Symbol, Scheme>`** -- replaced by a scope stack (see section 2.3, addresses audit MED-4).
- **No pending resolution vectors** in Ring 0 -- trait method resolution, constrained fn detection, mono calls, and deferred resolutions are all Ring 2. The five `pending_*` fields (audit MED-3) are not introduced until needed.
- **`warnings: Vec<Warning>`** instead of `eprintln!` (addresses audit MED-6).

### 2.2 Five Core Operations

Per spec 3.5.1:

**`fresh_var(&mut self) -> Type`**: Increment `next_id`, return `Type::Var(next_id - 1)`. Also provide `fresh_var_id(&mut self) -> (Type, TypeId)` to eliminate the repeated extraction pattern from the prototype (addresses audit MED-5).

**`unify(&mut self, a: &Type, b: &Type, span: Span) -> Result<(), CranelispError>`**: Apply current substitution to both sides, then match structurally. Updates `self.subst`. Returns `CranelispError::TypeError` on failure (never panics -- addresses audit HIGH-4). Ring 0 unification cases:

| Case | Action |
|---|---|
| Same primitive (`Int`/`Int`, `Bool`/`Bool`, `Float`/`Float`) | Success |
| `Var(id)` with anything | Occurs check, then bind `id -> T` in subst |
| `Fn(ps1, r1)` with `Fn(ps2, r2)` | Check arity match, unify pairwise |
| `ADT(n1, args1)` with `ADT(n2, args2)` | Check name match, unify args pairwise |
| Everything else | `TypeError` |

The occurs check prevents infinite types: if `id` appears free in `T`, error.

Constraint merging (for `Var`-`Var` unification) is deferred to Ring 2 since Ring 0 has no trait constraints.

**`apply(subst: &Subst, ty: &Type) -> Type`**: Free function in `cranelisp-types`. Recursively replaces `Var(id)` with its substitution. Follows chains: if `subst[id] = Var(id2)`, recursively apply to `Var(id2)`.

**`instantiate(&mut self, scheme: &Scheme) -> Type`**: Replace each quantified variable in `scheme.vars` with a fresh variable. Returns the substituted type. In Ring 0, `scheme.constraints` is always empty, so no constraint propagation occurs.

**`generalize(&self, ty: &Type) -> Scheme`**: Collect all free type variables in `ty` that are NOT free in any scope of the scope stack. These become the `vars` of the resulting `Scheme`. In Ring 0, `constraints` is always empty.

### 2.3 Scope Management (Scope Stack)

The prototype uses `local_env.clone()` to save/restore lexical scopes, which is O(n) per scope entry/exit. The reimplementation uses a **scope stack** (addresses audit MED-4):

```rust
struct TypeChecker {
    scope_stack: Vec<HashMap<Symbol, Scheme>>,
    // ...
}

impl TypeChecker {
    fn push_scope(&mut self) {
        self.scope_stack.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.scope_stack.pop();
    }

    fn bind_local(&mut self, name: Symbol, scheme: Scheme) {
        if let Some(top) = self.scope_stack.last_mut() {
            top.insert(name, scheme);
        }
    }

    fn lookup(&self, name: &str) -> Option<&Scheme> {
        // Search stack top-to-bottom (inner scopes shadow outer)
        for scope in self.scope_stack.iter().rev() {
            if let Some(scheme) = scope.get(name) {
                return Some(scheme);
            }
        }
        // Fall through to module-level symbol table
        self.lookup_in_symbol_table(name)
    }
}
```

Scope operations:
- **Lambda**: `push_scope()`, bind params, infer body, `pop_scope()`.
- **Let**: For each binding, bind into the current scope (no new scope needed -- `let` bindings are sequential and visible to subsequent bindings). The body is in the same scope.
- **Match arm**: `push_scope()` per arm, bind pattern variables, infer body, `pop_scope()`.
- **`check_defn`**: `push_scope()`, bind params, bind the function name (for recursion), infer body, `pop_scope()`.

This eliminates all `clone()` calls for lexical scoping. The depth is bounded by nesting (typically 5-10 levels). Lookup is O(depth * scope_size), which is faster than cloning a 70+ entry environment per scope.

### 2.4 Two-Pass Checking

Per spec 3.5.2, `check_program` uses two passes:

**Pass 1 -- Registration**:
1. Register enum-only `TypeDef`s: create `TypeDefInfo`, insert `ModuleEntry::TypeDef` and `ModuleEntry::Constructor` entries.
2. Register builtin operators (hard-wired `+`, `-`, `*`, `/`, `=`, `<`, `>`, `<=`, `>=`, `not`).
3. Register special form entries (`if`, `let`, `fn`, `defn`, `deftype`, `match`) for REPL introspection.
4. For each `Defn`, create fresh type variables for params and return, insert `ModuleEntry::Def` with a monomorphic scheme `Fn([t0, t1, ...], t_ret)`.

**Pass 2 -- Checking**:
1. For each `Defn`, `push_scope()`, bind params with their type variables, infer body, unify body type with return type variable, `pop_scope()`.
2. After all bodies are checked, generalize each function's type into a `Scheme`.
3. Update the symbol table entries with the generalized schemes.

**Pass 2 detail for `check_defn`**:
```
1. push_scope()
2. For each param: bind_local(param_name, Scheme::mono(param_type_var))
3. Optionally process param annotations:
   - TypeExpr::Named("Int") -> unify param_type_var with Type::Int
   - TypeExpr::FnType(...) -> resolve to Type::Fn and unify
   - TypeExpr::TypeVar(...) -> Ring 0 skips (no type variable annotations until Ring 2)
4. Bind the function name itself (for recursion) with the pre-generalized Fn type
5. body_ty = infer_expr(body)
6. unify(body_ty, ret_type_var)
7. pop_scope()
8. Apply subst to the Fn type, generalize -> Scheme
9. Update symbol table with the generalized Scheme
```

### 2.5 Expression Inference

Each expression variant is handled by a dedicated method on `TypeChecker`. This addresses audit HIGH-1 (monolithic `infer_expr`).

```
infer_expr(expr) -> Result<Type, CranelispError>
  match expr {
    IntLit   -> infer_int_lit(expr)
    FloatLit -> infer_float_lit(expr)
    BoolLit  -> infer_bool_lit(expr)
    Var      -> infer_var(expr)
    Let      -> infer_let(expr)
    If       -> infer_if(expr)
    Lambda   -> infer_lambda(expr)
    Apply    -> infer_apply(expr)
    Match    -> infer_match(expr)
    Annotate -> infer_annotate(expr)
    _        -> Err(TypeError "not supported in Ring 0")
  }
```

Each method is self-contained (typically 10-40 lines). The `infer_apply` method is the most complex:

```
infer_apply(callee, args, span):
  1. callee_ty = infer_expr(callee)
  2. arg_tys = args.map(|a| infer_expr(a))
  3. ret_ty = fresh_var()
  4. Check if callee is a Var referencing a builtin operator:
     - If so, resolve the concrete overload (Int or Float) and record
       BuiltinFn in builtin_resolutions
     - Unify accordingly
  5. Otherwise: unify(callee_ty, Fn(arg_tys, ret_ty))
  6. record_expr_type(expr, apply(subst, ret_ty))
  7. Return apply(subst, ret_ty)
```

The key simplification vs. the prototype: in Ring 0, the `infer_apply` callee analysis has exactly ONE concern (builtin operator resolution), not five interleaved blocks. Each ring adds at most one concern:
- Ring 0: builtin operators
- Ring 2: trait method dispatch, constrained fn interception, overload dispatch, auto-curry

### 2.6 Type Annotation Handling

`infer_annotate`:
1. Resolve the `TypeExpr` to a `Type` via `resolve_type_expr()`.
2. Infer the inner expression.
3. Unify the annotation type with the inferred type.
4. Return the (unified) type.

`resolve_type_expr` in Ring 0 handles:
- `TypeExpr::Named(name)` -> `Type::from_name(name)` for primitives, or look up user-defined ADT name. Return `Result`, never panic (addresses audit HIGH-4).
- `TypeExpr::FnType(params, ret)` -> recursively resolve, produce `Type::Fn`.
- `TypeExpr::TypeVar(name)` -> look up in a var_map parameter. Return `Err` if not found (addresses audit HIGH-4).
- `TypeExpr::SelfType` -> Ring 2 only; return error in Ring 0.
- `TypeExpr::Applied(name, args)` -> Ring 1 only; return error in Ring 0.

---

## 3. `CheckResult` Population Strategy

The typechecker produces a `CheckResult` that the backend consumes. In Ring 0:

```rust
CheckResult {
    method_resolutions: MethodResolutions,    // BuiltinFn entries only
    expr_types: HashMap<Span, Type>,          // every expression's type
    warnings: Vec<Warning>,                   // accumulated warnings
    constrained_fn_names: HashSet::new(),     // empty in Ring 0
    mono_defns: Vec::new(),                   // empty in Ring 0
    default_method_defns: Vec::new(),         // empty in Ring 0
}
```

### 3.1 `method_resolutions`

Populated during `infer_apply` when the callee is a builtin operator. The key is the `Apply` expression's `Span`; the value is `ResolvedCall::BuiltinFn { name }`.

Example: `(+ 1 2)` at span (0,7) records `{ Span(0,7) => BuiltinFn { name: "+" } }`.

The backend uses this map to emit inline Cranelift IR instead of a function call.

### 3.2 `expr_types`

Populated via `record_expr_type` during every `infer_*` call. After all inference completes, resolve all types through the final substitution:

```rust
let resolved_expr_types: HashMap<Span, Type> = self.expr_types
    .iter()
    .map(|(span, ty)| (*span, apply(&self.subst, ty)))
    .collect();
```

This is done once at the end of `check_program`, not incrementally during inference. The prototype does this at lines 303-308 of `program.rs`.

In Ring 0, the backend uses `expr_types` primarily to determine the type of `if`/`match` branches and function return values. Since Ring 0 has no heap types, `HeapCategory::classify` always returns `NeverHeap`, but the expr_types are still needed for codegen decisions (e.g., `iadd` vs `fadd`).

### 3.3 `warnings`

Accumulated in `self.warnings: Vec<Warning>` during inference. Moved into `CheckResult` at the end. Ring 0 warnings include:
- Unused variables (if implemented; may defer to Ring 1).
- Shadowed bindings (optional).

---

## 4. Addressing HIGH Audit Findings

### 4.1 HIGH-1: `infer_expr()` is 603 lines with five callee-inspection blocks

**Audit**: `inference.rs:30-633` -- monolithic match with 13+ expression variants.

**Resolution**: Extract each `Expr` variant into a dedicated method. Ring 0 starts with 10 small methods:

```
infer_int_lit     -> ~5 lines
infer_float_lit   -> ~5 lines
infer_bool_lit    -> ~5 lines
infer_var         -> ~20 lines (lookup + instantiate)
infer_let         -> ~15 lines
infer_if          -> ~10 lines
infer_lambda      -> ~15 lines
infer_apply       -> ~30 lines (Ring 0: only builtin dispatch)
infer_match       -> ~25 lines
infer_annotate    -> ~10 lines
```

The `infer_expr` dispatcher is a 15-line match that delegates to these methods. Each method is independently testable.

The five callee-inspection blocks in `infer_apply` (prototype lines 173-340) do not exist in Ring 0. Ring 2 introduces trait method dispatch and constrained fn interception as explicit methods (`analyze_callee` or equivalent), not interleaved blocks.

### 4.2 HIGH-2: `check_program()` is 318 lines -- monolithic batch pipeline

**Audit**: `program.rs:13-318` -- 17+ phases in a single function.

**Resolution**: Extract phases into named private methods. Ring 0 `check_program` is a readable sequence:

```rust
pub fn check_program(&mut self, program: &Program) -> Result<CheckResult, CranelispError> {
    self.register_builtins();                           // operators, special forms
    self.register_type_defs(program)?;                  // enum-only TypeDefs
    let defns = Self::collect_defns(program);
    self.pass1_register_signatures(&defns)?;             // fresh vars for all defns
    self.pass2_check_bodies(&defns)?;                    // infer + generalize
    Ok(self.build_check_result())
}
```

Each method is 20-50 lines. The phase ordering is explicit and easy to extend ring-by-ring:
- Ring 1: insert `self.register_type_defs_with_fields()` (product/sum types)
- Ring 2: insert `self.register_traits()`, `self.validate_impls()`, `self.process_multi_sigs()`, `self.detect_constrained_fns()`, `self.resolve_dispatches()`, `self.monomorphise()`

### 4.3 HIGH-3: `resolve_one_method()` is 142 lines with deep nesting

**Audit**: `traits.rs:642-784` -- deep nesting, clone-to-avoid-borrow.

**Resolution**: `resolve_one_method` does not exist in Ring 0. It is part of the trait method resolution pipeline (Ring 2). When implemented:
- Split into `resolve_concrete_method` and `resolve_polymorphic_method`.
- Use a two-pass approach (find index, then unify) to eliminate the clone-to-avoid-borrow pattern.
- Maximum nesting depth of 2 levels.

### 4.4 HIGH-4: Production `panic!()` calls in `unification.rs` and `traits.rs`

**Audit**: 5 `panic!()` calls reachable from production code.

**Resolution**: All type resolution functions return `Result<Type, CranelispError>` from the start:

```rust
fn resolve_type_expr(
    &self,
    texpr: &TypeExpr,
    var_map: &HashMap<Symbol, TypeId>,
    span: Span,
) -> Result<Type, CranelispError> {
    match texpr {
        TypeExpr::Named(name) => {
            Type::from_name(name)
                .or_else(|| self.lookup_user_type(name).map(|_| Type::ADT(name.clone(), vec![])))
                .ok_or_else(|| CranelispError::TypeError {
                    message: format!("unknown type: {}", name),
                    span,
                })
        }
        TypeExpr::TypeVar(name) => {
            var_map.get(name)
                .map(|&id| Type::Var(id))
                .ok_or_else(|| CranelispError::TypeError {
                    message: format!("unresolved type variable: {}", name),
                    span,
                })
        }
        // ...
    }
}
```

Zero `panic!()` calls in the crate. The `traits.rs` panics are Ring 2 -- when that code is written, it will also return `Result`.

### 4.5 HIGH-5: Additional `.expect()` panics in `mono.rs` and `primitives.rs`

**Audit**: 6 `.expect()` calls in non-test code.

**Resolution**:
- `mono.rs` does not exist in Ring 0 (monomorphisation is Ring 2). When implemented, all operations return `Result`.
- `primitives.rs` equivalent (builtin registration) in Ring 0 uses `debug_assert!` for true invariants (e.g., "primitives module must exist after we just created it") and `Result` for user-facing operations.

Design rule: **No `.unwrap()` or `.expect()` in any non-test code path.** Use `?` for fallible operations. Use `debug_assert!` for invariants that are programmer errors.

### 4.6 HIGH-6: Test coverage remains thin for critical subsystems

**Audit**: `unification.rs`, `program.rs`, `adt.rs` have zero unit tests.

**Resolution**: Ring 0 ships with comprehensive unit tests for every module:

| Module | Minimum test targets |
|---|---|
| `unify.rs` | Primitive-primitive, Var binding, occurs check, Fn-Fn arity mismatch, ADT-ADT name mismatch, error messages include spans |
| `infer.rs` | One test per expression form (10 tests minimum), forward reference, mutual recursion |
| `scope.rs` | Push/pop, shadowing, lookup falls through to module level |
| `program.rs` | Two-pass pipeline, generalization, `CheckResult` structure |
| `adt.rs` | Enum registration, constructor lookup, exhaustiveness check |
| `builtins.rs` | Operator resolution (Int and Float), `not`, type errors |

Shared test infrastructure: a single `#[cfg(test)] mod test_helpers` module providing `tc_with_builtins()` (addresses audit LOW-4 -- no duplicated test helpers).

---

## 5. Module Decomposition: `cranelisp-typecheck` Crate

### 5.1 File Layout

```
cranelisp-typecheck/
  src/
    lib.rs          -- public API: check_program, check_repl_input
    CLAUDE.md       -- conventions, substitution env docs, Scheme representation
    checker.rs      -- TypeChecker struct, constructor, scope stack
    infer.rs        -- infer_expr + per-variant methods (infer_int_lit, infer_var, ...)
    unify.rs        -- unify(), occurs_check(), apply_subst_to_type()
    scheme.rs       -- Scheme operations: instantiate, generalize, Scheme::mono()
    resolve.rs      -- resolve_type_expr (TypeExpr -> Type)
    builtins.rs     -- register_builtins (operators, special forms)
    adt.rs          -- register_type_def, exhaustiveness checking
    program.rs      -- check_program (two-pass orchestration)
    check_result.rs -- build_check_result (finalize expr_types, collect resolutions)
    tests/
      mod.rs        -- test helpers (tc_with_builtins, assert_infers_to, etc.)
      unify_tests.rs
      infer_tests.rs
      program_tests.rs
      adt_tests.rs
      builtins_tests.rs
```

### 5.2 Module Responsibilities

**`lib.rs`** -- Public API surface. Re-exports `TypeChecker`, `check_program`, and any types needed by the binary crate. Minimal code.

<!-- FIXME(/typecheck): Document the borrow-splitting strategy for TypeChecker methods. When infer_apply calls unify (mutating subst) while also needing to record in expr_types, how are &mut self borrow conflicts avoided? The prototype hit this in resolve_one_method (audit HIGH-3: clone-to-avoid-borrow). Recommend: unify() and occurs_check() take explicit &mut Subst parameters rather than going through &mut self, keeping expr_types borrowable independently. State the chosen pattern so Ring 0 code is structured correctly from the start. -->

**`checker.rs`** -- The `TypeChecker` struct definition. Constructor (`new()`), scope stack operations (`push_scope`, `pop_scope`, `bind_local`, `lookup`), `fresh_var`, `fresh_var_id`, `record_expr_type`. This module owns the struct but delegates work to other modules via `impl TypeChecker` blocks.

Ring 0 `TypeChecker` fields:
```rust
pub struct TypeChecker {
    next_id: TypeId,
    subst: Subst,
    scope_stack: Vec<HashMap<Symbol, Scheme>>,
    expr_types: HashMap<Span, Type>,
    builtin_resolutions: HashMap<Span, ResolvedCall>,
    warnings: Vec<Warning>,
    symbol_table: SymbolTable,
}
```

Ring 2 adds: `var_constraints`, `pending_resolutions`, `deferred_resolutions`, `pending_mono_calls`, `generated_specializations`, `overloads`, `resolved_overloads`, `pending_overload_resolutions`, `pending_auto_curry`, `modules` (multi-module), `current_module_path`.

**`unify.rs`** -- `unify(&mut self, a: &Type, b: &Type, span: Span) -> Result<(), CranelispError>` and `occurs_check(id: TypeId, ty: &Type, subst: &Subst) -> bool`. Self-contained, no dependencies on AST types. Ring 0 handles: primitives, Var, Fn, ADT. Ring 2 adds TyConApp, constraint merging.

**`scheme.rs`** -- `Scheme::mono(ty: Type) -> Scheme`, `instantiate(&mut self, scheme: &Scheme) -> Type`, `generalize(&self, ty: &Type) -> Scheme`. The generalize function checks free variables against all scopes in the scope stack plus the symbol table.

**`resolve.rs`** -- `resolve_type_expr(texpr: &TypeExpr, var_map: &HashMap<Symbol, TypeId>, span: Span) -> Result<Type, CranelispError>`. All type expression resolution in one place. Returns `Result`, never panics. Ring 2 adds `resolve_type_expr_hkt` and `resolve_annotation` (for trait constraint annotations).

**`infer.rs`** -- `infer_expr(&mut self, expr: &Expr) -> Result<Type, CranelispError>` dispatcher plus per-variant methods. Each method is an `impl TypeChecker` method in this module. Ring 0: 10 methods. Ring 2 adds `infer_string_lit`, `infer_vec_lit`, and modifies `infer_apply` with trait/overload dispatch.

**`builtins.rs`** -- `register_builtins(&mut self)`. Creates `ModuleEntry::Def` entries for operators and `ModuleEntry::Def` (with `DefKind::SpecialForm`) entries for special forms. Ring 2 replaces operator entries with trait method entries.

**`adt.rs`** -- `register_type_def(&mut self, typedef: &TopLevel) -> Result<(), CranelispError>`. Creates `TypeDefInfo` and `ConstructorInfo`, inserts `ModuleEntry::TypeDef` and `ModuleEntry::Constructor` entries. Also contains `check_exhaustiveness`. Ring 1 extends to handle data constructors (with fields) and type parameters.

**`program.rs`** -- `check_program(&mut self, program: &Program) -> Result<CheckResult, CranelispError>`. Orchestrates the two-pass pipeline. Each phase is a named private method. Ring 2 adds phases for traits, impls, overloads, monomorphisation.

**`check_result.rs`** -- `build_check_result(&self) -> CheckResult`. Finalizes `expr_types` by applying the substitution, collects `builtin_resolutions` into `method_resolutions`, moves `warnings`.

### 5.3 Design Decisions

**One `impl TypeChecker` per module**: Rust allows multiple `impl` blocks for the same struct across modules within a crate. Each module adds methods to `TypeChecker` relevant to its concern. This avoids a god file while keeping a single struct.

**No circular dependencies between modules**: The dependency flow within the crate is:
```
lib.rs -> program.rs -> {infer.rs, builtins.rs, adt.rs, check_result.rs}
                         infer.rs -> {unify.rs, scheme.rs, resolve.rs}
```
Every module depends on `checker.rs` (for the struct definition and scope operations). No module depends on `program.rs` except `lib.rs`.

**Shared test helpers in `tests/mod.rs`**: A single `tc_with_builtins()` function creates a `TypeChecker` with Ring 0 builtins registered. All test modules import from here. No duplication.

---

## 6. REPL Integration

Ring 0 REPL support requires a `check_repl_input` method (or equivalent) that handles single expressions and definitions incrementally:

```rust
pub fn check_repl_input(
    &mut self,
    input: &ReplInput,
) -> Result<ReplCheckResult, CranelispError>
```

Where `ReplCheckResult` contains the inferred type (for display) and any method resolutions / expr_types needed by the backend.

Key REPL behaviors in Ring 0 (per `repl/spec.md`):
- **Expression evaluation**: infer type, return for `:Type value` display.
- **Function definition**: check the defn, generalize, update symbol table, return the scheme for `:(Fn [a] a) user/id` display.
- **Type definition**: register the enum, return the type name for `:user/Color` display.
- **Bare symbol lookup**: instantiate and return scheme for display.
- **Error recovery**: a type error in one expression must not corrupt the TypeChecker state.

Error recovery strategy: snapshot the `TypeChecker` state (or relevant parts) before checking a REPL input, and roll back on error. In Ring 0, the relevant mutable state is `subst`, `scope_stack` (should be empty between inputs), `next_id`, `expr_types`, and `symbol_table`. A lightweight approach: on error, restore `subst` and `next_id` to their pre-input values. Symbol table mutations (new entries) can be reverted by tracking which entries were added.

---

## 7. Display Format Requirements

Per `repl/spec.md`, the typechecker must produce types that can be displayed in the `:Type value` format with fully-qualified names. The type display logic lives in the binary crate (or a shared formatting module), not in `cranelisp-typecheck`. The typechecker's responsibility is:

1. Produce `Type` values with correct structure (primitive types, `Fn` with param/return, `ADT` with name).
2. Produce `Scheme` values with correctly generalized variables.
3. The display layer maps `Type::Int` to `"primitives/Int"`, `Type::Bool` to `"primitives/Bool"`, etc.
4. Quantified type variables are displayed as `a`, `b`, `c`, ... (alphabetical order of `vars` in the `Scheme`).

The typechecker does NOT format strings. It provides structured `Type` and `Scheme` data.

---

## 8. Interface Gaps

### 8.1 Operator Overload Representation in Ring 0

The current `interfaces.md` design registers operators as single `ModuleEntry::Def` entries. But Ring 0 operators need to handle BOTH `Int` and `Float` operands. Options:

**Option A -- Two entries per operator**: Register `+_Int` and `+_Float` (or similar internal names). The bare name `+` is an alias. This is clean but requires the `infer_apply` logic to resolve the alias.

**Option B -- Single entry with inference-time dispatch**: Register `+` with a polymorphic scheme like `(Fn [a a] a)` and let the inference discover `a = Int` or `a = Float` from context. This works but the scheme is overly permissive (it would accept `(+ true false)` until Ring 2 adds trait constraints).

**Recommended -- Option B with validation**: Register `+` as `(Fn [a a] a)` with `vars: [a_id]`. During `infer_apply`, after unification resolves `a` to a concrete type, validate that the resolved type is `Int` or `Float`. If not, emit a type error. This is simple, correct, and transitions cleanly to Ring 2 (where the validation becomes a `Num` trait constraint check).

When registering the resolution in `method_resolutions`, record `ResolvedCall::BuiltinFn { name: Symbol::from("+") }`. The backend uses the resolved operand type (from `expr_types`) to choose between `iadd` and `fadd`.

**Resolved (Sprint 5)**: This FIXME is moot. Ring 2 trait dispatch replaced the Ring 0 `BuiltinFn` approach for operators. Operators like `+` now resolve to `ResolvedCall::TraitMethod { mangled_name: "Num.+$Int", impl_type: "Int", ... }`, which carries the concrete type directly. The backend dispatches on `mangled_name`/`impl_type` — no `expr_types` lookup needed for operator type discrimination. `BuiltinFn` remains only for monomorphic named primitives (e.g., `add-i64`, `str-concat`) where there is no type ambiguity.

### 8.2 Exhaustiveness Checking Return Type

The current interface does not specify how exhaustiveness warnings/errors flow. Exhaustiveness is a hard requirement per spec 6.5 -- non-exhaustive match on a concrete ADT is a compile-time error. The typechecker should return this as a `CranelispError::TypeError` during `infer_match`, not as a warning.

### 8.3 `SymbolTable` Mutability

The typechecker needs to mutate the `SymbolTable` during checking (Pass 1 registration, Pass 2 updates after generalization). The current `SymbolTable` in `interfaces.md` is a simple data container with `insert` and `get` methods, which is sufficient. No gap here.

---

## 9. Risk Analysis

### 9.1 Operator Dispatch Transition (Ring 0 -> Ring 2)

Ring 0 hard-wires operators. Ring 2 replaces them with trait method dispatch. The risk is that Ring 0's builtin dispatch creates assumptions in the backend that are hard to remove.

**Mitigation**: Use `ResolvedCall::BuiltinFn` consistently. The backend should NOT special-case operator names in any other path. When Ring 2 arrives, the same call sites will produce `ResolvedCall::TraitMethod` instead, and the backend's existing `TraitMethod` handling will take over. The only backend change is removing the `BuiltinFn` code path for operators (which becomes dead code).

### 9.2 Scope Stack vs. Environment Clone

The scope stack is a design improvement over the prototype, but it changes the lookup semantics slightly: in the prototype, `self.local_env` contains ALL currently-visible bindings (a flat map). With a scope stack, lookup requires traversing the stack. This is functionally equivalent but changes the implementation of `generalize` (which must scan all scopes for free variables, not just one flat map).

**Mitigation**: `generalize` collects free variables from all scopes plus the symbol table. This is a one-time scan at generalization time (once per `defn`), not on every lookup.

### 9.3 `Span` Uniqueness as Map Key

Both `expr_types` and `method_resolutions` use `Span` as the map key. If two expressions have the same span (e.g., compiler-generated code with `Span::SYNTHETIC`), the map entries collide.

**Mitigation**: In Ring 0, all expressions come from user source text with unique spans. Synthetic spans only arise in Ring 3+ (macro expansion). For Ring 0, span-as-key is safe. When Ring 3 arrives, the macro expander must assign unique synthetic spans (the prototype uses a monotonic counter for this).

---

## 10. Implementation Sequence

Within Ring 0, the typechecker implementation proceeds in this order:

1. **Foundation** (`checker.rs`, `unify.rs`, `scheme.rs`): TypeChecker struct, fresh_var, unify, instantiate, generalize. Unit tests for each.
2. **Type resolution** (`resolve.rs`): `resolve_type_expr` for Named, FnType. Unit tests.
3. **Literal inference** (`infer.rs`): IntLit, FloatLit, BoolLit. Unit tests.
4. **Variable + Let + If** (`infer.rs`): Var lookup, Let binding, If branching. Unit tests.
5. **Lambda** (`infer.rs`): Lambda inference with scope stack. Unit tests.
6. **Apply + builtins** (`infer.rs`, `builtins.rs`): Function application, operator resolution. Unit tests.
7. **ADT + Match** (`adt.rs`, `infer.rs`): Enum registration, match inference, exhaustiveness. Unit tests.
8. **Annotations** (`infer.rs`, `resolve.rs`): Annotate expression. Unit tests.
9. **Two-pass pipeline** (`program.rs`): check_program orchestration. Integration tests.
10. **CheckResult** (`check_result.rs`): Finalization. Integration tests verifying the backend contract.

Steps 1-6 can be developed and tested without any AST builder (using hand-constructed `Expr` values). Steps 7-8 add ADT support. Steps 9-10 wire everything together.

---

## Next skills

- `/backend` -- Ring 0 codegen can begin in parallel, consuming `CheckResult` with `BuiltinFn` resolutions and `expr_types`.
- `/frontend` -- Ring 0 AST builder produces `Expr` and `TopLevel` values that the typechecker consumes. Can develop in parallel using hand-constructed ASTs for typechecker tests.
- `/qa` -- Integration tests wire frontend -> typecheck -> backend through `compile_unit()`. Blocked on all three compiler skills having at least a stub implementation.
