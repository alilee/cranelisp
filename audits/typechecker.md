# Typechecker Module Audit

**Module**: `src/typechecker/` (11 files, 4,392 lines)
**Date**: 2026-02-13
**Scope**: Simplicity, maintainability, complexity, duplication, data modeling, test coverage

## Module Overview

The typechecker implements Algorithm W (Hindley-Milner) type inference with extensions for trait dispatch, overloaded functions, auto-curry, and monomorphization. It is the largest module in the compiler.

### File Metrics

| File | Lines | Responsibility | Tests |
|---|---|---|---|
| `mod.rs` | 247 | TypeChecker struct, public types, re-exports | 0 |
| `inference.rs` | 792 | `infer_expr`, `check_defn`, `check_impl_method`, annotations | 8 |
| `unification.rs` | 444 | `unify`, `resolve_type_expr`, `instantiate`, `generalize` | 0 |
| `traits.rs` | 860 | Trait registration, impl validation, method resolution | 4 |
| `program.rs` | 286 | `check_program` batch-mode two-pass checker | 0 |
| `primitives.rs` | 263 | Primitive registration, `is_inline_primitive`/`is_extern_primitive` | 0 |
| `mono.rs` | 355 | Constrained fn detection, monomorphization | 0 |
| `overloads.rs` | 368 | Multi-sig function checking, overload dispatch | 0 |
| `adt.rs` | 111 | `register_type_def` for deftype | 0 |
| `introspect.rs` | 475 | `describe_symbol`, `list_symbols` for REPL | 12 |
| `tests.rs` | 191 | Integration tests via `check_program` | 25 |

**Total tests**: 49

---

## Findings

### HIGH-1: `infer_expr()` is 447 lines with deeply nested match arms

**File**: `inference.rs:15-461`
**Severity**: High (maintainability)

The core expression inference function is a single `match expr` with 13 arms, some deeply nested (e.g., `Expr::Apply` spans 140 lines, `Expr::Match` spans 116 lines). The `Apply` arm alone contains four separate `if let Expr::Var` blocks that each check whether the callee is a special kind of function.

```rust
// inference.rs:134-273 — the Apply arm (140 lines)
Expr::Apply { callee, args, span, .. } => {
    // Intercept: overloaded callee (multi-signature function)
    if let Expr::Var { name, .. } = callee.as_ref() {
        // ... 17 lines ...
    }
    // Intercept: constrained function call
    let callee_ty = if let Expr::Var { name, .. } = callee.as_ref() {
        // ... 12 lines ...
    };
    // ... infer args, unify, auto-curry fallback ...
    // Track trait method calls for later resolution
    if let Expr::Var { name, .. } = callee.as_ref() {
        // ... 35 lines ...
    }
    // Track calls to constrained functions
    if let Expr::Var { name, .. } = callee.as_ref() {
        // ... 10 lines ...
    }
    // ...
}
```

**Impact**: Difficult to understand the flow of function application inference. Each concern (overload interception, constrained fn interception, trait method tracking, mono call tracking) is interleaved in a single arm.

**Recommendation**: Extract each `Expr` arm into a dedicated method (e.g., `infer_apply`, `infer_match`, `infer_lambda`). The Apply arm should further extract its four callee-inspection blocks into helpers.

---

### HIGH-2: `check_program()` is 273 lines — monolithic batch pipeline

**File**: `program.rs:13-285`
**Severity**: High (maintainability)

This function orchestrates the entire batch-mode typechecking pipeline in a single method: builtin registration, type def registration, trait registration, impl validation, multi-sig processing, two-pass type checking, operator resolution, overload resolution, trait method resolution, monomorphization (twice), and main validation. The control flow is sequential but hard to follow because each phase mutates shared state.

```rust
pub fn check_program(&mut self, program: &Program) -> Result<CheckResult, CranelispError> {
    // Register `print` builtin ...                    // lines 14-27
    // Register inline and extern primitives           // line 30
    // Register type definitions                       // lines 33-37
    // Register user-defined traits                    // lines 40-42
    // Validate and register trait impls               // lines 45-48
    // Process DefnMulti items                         // lines 51-69
    // Extract impl method defns                       // lines 72-85
    // Collect all defns                               // lines 89-96
    // Pass 1: register signatures                     // lines 98-106
    // Process param annotations                       // lines 108-117
    // Pass 2: check bodies + generalize               // lines 119-152
    // Resolve operator methods                        // line 158
    // Resolve multi-sig overloads                     // lines 162-204
    // Verify main                                     // lines 207-240
    // Detect constrained fns + monomorphise           // lines 246-270
    // Resolve expr_types                              // lines 273-277
    // Return CheckResult                              // lines 279-285
}
```

**Impact**: Any change to the pipeline order requires understanding the entire function. Each phase's preconditions are implicit.

**Recommendation**: Extract phases into named methods (e.g., `register_all_types`, `pass1_register_signatures`, `pass2_check_bodies`, `resolve_all_dispatches`, `validate_main`). The top-level function becomes a readable sequence of named steps.

---

### HIGH-3: `resolve_one_method()` is 158 lines with deep nesting

**File**: `traits.rs:586-743`
**Severity**: High (complexity)

This function resolves a single pending trait method call. It has a top-level `match &concrete` with two major arms (`Type::Var` at 70 lines, concrete types at 70 lines), each containing nested conditionals 4+ indentation levels deep.

```rust
fn resolve_one_method(&mut self, span, method_name, arg_type)
    -> Result<Option<ResolvedCall>, CranelispError>
{
    let concrete = apply(&self.subst, arg_type);
    match &concrete {
        Type::Var(_) => {
            // ... find unique impl ... 70 lines ...
        }
        Type::Int | Type::Bool | Type::String | Type::Float | Type::ADT(_, _) => {
            // ... find impl for concrete type ... 70 lines ...
            if let Some(target_mangled) = self.find_impl_for_type(...) {
                if let Type::ADT(base_name, args) = &concrete {
                    if args.iter().any(has_type_var) {
                        // Clone the matching impl to avoid borrow conflict
                        let matching_impl = self.user_impls.iter()...
                        if let Some(ui) = matching_impl {
                            // ... 4 levels deep ...
                        }
                    }
                }
                // ...
            }
        }
    }
}
```

**Impact**: Hard to verify correctness of the resolution logic. The borrow-conflict workaround (clone matching impl) adds noise.

**Recommendation**: Split into `resolve_polymorphic_method` and `resolve_concrete_method`. Extract the "find and unify polymorphic impl" block into a helper.

---

### HIGH-4: Production `panic!()` calls crash on invalid type names

**File**: `unification.rs:49,68,87`
**Severity**: High (robustness)

Three `panic!()` calls in `resolve_type_expr_with_vars` crash the process when encountering an unknown type name or unresolved type variable. These are reachable from user-facing operations (trait registration, type definitions).

```rust
// unification.rs:49
TypeExpr::Named(name) => match name.as_str() {
    "Int" => Type::Int,
    // ...
    _ => {
        // ...
        if self.type_defs.contains_key(name) {
            Type::ADT(name.clone(), vec![])
        } else {
            panic!("unknown type: {}", name)           // <-- CRASH
        }
    }
},

// unification.rs:68
TypeExpr::TypeVar(name) => {
    if let Some(&id) = var_map.get(name) {
        Type::Var(id)
    } else {
        panic!("unresolved type variable: {}", name)   // <-- CRASH
    }
}

// unification.rs:87 (inside TypeExpr::Applied)
    } else {
        panic!("unknown type: {}", name)               // <-- CRASH
    }
```

**Additional panics**:
- `traits.rs:192` — `panic!("unknown type in HKT trait sig: {}", name)` in `resolve_type_expr_hkt`
- `traits.rs:198` — `panic!("SelfType in HKT trait signature")` in `resolve_type_expr_hkt`
- `mono.rs:220` — `.expect("function not in env")` in `finalize_defn_type`

**Total**: 5 `panic!()` + 1 `.expect()` in production code paths.

**Impact**: A typo in a type name in the prelude or user code crashes the compiler instead of producing a diagnostic error. The `resolve_type_expr_with_vars` panics are reachable from `register_type_def` (via `adt.rs:44`) and trait method signature processing.

**Recommendation**: Change all to return `Result<Type, CranelispError>` with span-aware error messages. This requires threading spans through the `resolve_type_expr_*` call chain, but callers already have spans available.

---

### HIGH-5: Test coverage is thin — major subsystems have zero unit tests

**Severity**: High (quality assurance)

Of the 49 tests, 25 are integration tests in `tests.rs` that exercise `check_program` end-to-end. These cover basic expressions (literals, let, if, lambda, apply) and IO types. However, zero dedicated tests exist for:

| Subsystem | Lines | Unit tests | Integration coverage |
|---|---|---|---|
| ADT registration (`adt.rs`) | 111 | 0 | Indirect via prelude |
| Trait resolution (`traits.rs` resolve logic) | ~200 | 0 | Indirect via operators |
| Overload dispatch (`overloads.rs`) | 368 | 0 | None |
| Monomorphization (`mono.rs`) | 355 | 0 | None |
| Auto-curry | ~50 | 0 | None |
| Constrained functions | ~100 | 0 | None |
| HKT trait registration | ~130 | 0 | None |
| Polymorphic impl resolution | ~100 | 0 | None |

The `tc_with_prelude()` test helper is duplicated identically in 3 files (`inference.rs:662-696`, `traits.rs:791-825`, `introspect.rs:256-290`).

**Impact**: Regressions in trait resolution, monomorphization, or overload dispatch would go undetected. The integration tests only verify that programs typecheck or fail, not that specific resolution outcomes are correct.

**Recommendation**: Add targeted unit tests for each subsystem. Deduplicate the `tc_with_prelude()` helper into a shared test utility.

---

### MED-1: `resolve_dotted_var()` has two nearly identical 30-line branches

**File**: `inference.rs:465-548`
**Severity**: Medium (duplication)

The Type.Constructor branch (lines 474-507) and Trait.method branch (lines 510-542) share identical logic for looking up the member in `env`, checking for overloaded/constrained status, instantiating, and recording the type. The only difference is the parent validation (type_defs vs traits lookup).

```rust
// Type.Constructor case (lines 477-501):
if let Some(scheme) = self.env.get(member) {
    let scheme = scheme.clone();
    if self.overloads.contains_key(member) { return Err(...) }
    if scheme.is_constrained() { return Err(...) }
    let ty = self.instantiate(&scheme);
    self.record_expr_type(expr, &ty);
    return Ok(ty);
}

// Trait.method case (lines 513-536) — IDENTICAL logic:
if let Some(scheme) = self.env.get(member) {
    let scheme = scheme.clone();
    if self.overloads.contains_key(member) { return Err(...) }
    if scheme.is_constrained() { return Err(...) }
    let ty = self.instantiate(&scheme);
    self.record_expr_type(expr, &ty);
    return Ok(ty);
}
```

**Recommendation**: Extract a `lookup_and_instantiate_member()` helper that both branches call after validating the parent.

---

### MED-2: `check_defn()` and `check_impl_method()` share ~30 lines of duplicated logic

**File**: `inference.rs:552-646`
**Severity**: Medium (duplication)

These two methods follow the same pattern: create fresh param types, process annotations, register the function, save env, add params, infer body, unify, restore env, remove entry, generalize, re-insert. The only difference in `check_impl_method` is a pre-unification step with `self_type` (lines 625-628).

```rust
// Shared pattern in both methods:
let param_tys: Vec<Type> = defn.params.iter().map(|_| self.fresh_var()).collect();
let ret_ty = self.fresh_var();
let fn_ty = Type::Fn(param_tys.clone(), Box::new(ret_ty.clone()));
// ... process annotations ...
self.env.insert(defn.name.clone(), Scheme::mono(fn_ty));
let saved_env = self.env.clone();
for (name, ty) in defn.params.iter().zip(param_tys.iter()) { ... }
let body_ty = self.infer_expr(&defn.body)?;
self.unify(&body_ty, &ret_ty, defn.span)?;
self.env = saved_env;
self.env.remove(&defn.name);
let resolved_ty = apply(&self.subst, &Type::Fn(param_tys, Box::new(ret_ty)));
let scheme = self.generalize(&resolved_ty);
self.env.insert(defn.name.clone(), scheme.clone());
```

**Recommendation**: Unify into `check_defn_with_self_type(defn, Option<&Type>)` where `None` means no pre-unification.

---

### MED-3: Four separate `pending_*` Vec fields could be modeled as one Vec of an enum

**File**: `mod.rs:110-125`
**Severity**: Medium (data modeling)

The TypeChecker has four separate pending resolution vectors plus one deferred vector:

```rust
pending_resolutions: Vec<(Span, String, Type)>,                    // line 110
pending_overload_resolutions: Vec<(Span, String, Vec<Type>, Type)>, // line 117
pending_auto_curry: Vec<(Span, String, usize, usize)>,             // line 119
pending_mono_calls: Vec<(Span, String, Vec<Type>)>,                // line 125
deferred_resolutions: Vec<(Span, String, Type)>,                   // line 123
```

All represent "work to do after inference." They're consumed in different phases of `check_program` and `resolve_methods`, but their lifecycle is the same: accumulated during inference, drained during resolution.

**Impact**: The struct has 22 fields total. The separate vectors make it hard to see what pending work exists and in what order it's processed.

**Recommendation**: Consider a `PendingResolution` enum with variants for each kind, stored in a single `Vec<PendingResolution>`. This makes the ordering explicit and the struct smaller. Alternatively, group into a `PendingWork` sub-struct to reduce the field count on `TypeChecker`.

---

### MED-4: `self.env.clone()` clones the entire environment repeatedly

**File**: `inference.rs:121,336,571,630` and `program.rs:132`
**Severity**: Medium (performance)

The environment is cloned to implement lexical scoping (save before adding bindings, restore after). This happens for every lambda, every match arm, every `check_defn`, and every function in pass 2 of `check_program`.

```rust
// inference.rs:121 (Lambda)
let saved_env = self.env.clone();
// ... add params, check body ...
self.env = saved_env;

// inference.rs:336 (Match — per arm!)
for arm in arms {
    let saved_env = self.env.clone();
    // ... add bindings, check body ...
    self.env = saved_env;
}
```

**Impact**: For deeply nested expressions or large environments (post-prelude, the env has ~70+ entries), this creates unnecessary allocations. In `check_program` pass 2, the env is cloned once per function definition.

**Recommendation**: Use a scope-stack approach: push new bindings onto a scope, pop on exit. This avoids cloning the entire HashMap. A simpler intermediate step: only save and restore the specific keys that are being shadowed.

---

### MED-5: `primitives.rs` registration is highly repetitive

**File**: `primitives.rs:10-201`
**Severity**: Medium (maintainability)

The file registers ~30 primitives across 5 groups with nearly identical boilerplate. Each registration requires an `env.insert()` + `fn_meta.insert()`, and docstrings are added in a separate loop that re-looks-up each entry.

```rust
// Registration loop (repeated 5 times with slight type variations):
for name in &["add-i64", "sub-i64", "mul-i64", "div-i64"] {
    self.env.insert(
        name.to_string(),
        Scheme::mono(Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int))),
    );
    self.fn_meta.insert(name.to_string(), FnMeta { ... });
}

// Then docstrings in a SEPARATE loop:
for (name, doc) in &[("add-i64", "Add two integers"), ...] {
    if let Some(meta) = self.fn_meta.get_mut(*name) {
        meta.docstring = Some(doc.to_string());
    }
}
```

**Impact**: Adding a new primitive requires edits in 3+ places (registration loop, docstring loop, `is_inline_primitive` or `is_extern_primitive` match). Easy to forget one.

**Recommendation**: Define primitives as a static table `&[(&str, &[Type], Type, &str)]` and register from a single loop. Derive `is_inline_primitive`/`is_extern_primitive` from the same table.

---

### MED-6: Additional panics in trait and mono code

**File**: `traits.rs:192,198` and `mono.rs:220`
**Severity**: Medium (robustness)

Beyond the HIGH-4 panics in `unification.rs`, additional panics exist:

```rust
// traits.rs:192 — resolve_type_expr_hkt
TypeExpr::Named(name) => match name.as_str() {
    // ...
    _ => {
        if self.type_defs.contains_key(name) { ... }
        else { panic!("unknown type in HKT trait sig: {}", name) }
    }
}

// traits.rs:198
TypeExpr::SelfType => {
    panic!("SelfType in HKT trait signature")
}

// mono.rs:220 — finalize_defn_type
let old_scheme = self.env.remove(name).expect("function not in env");
```

**Impact**: Same as HIGH-4 — user-triggerable crashes instead of error diagnostics.

**Recommendation**: Same as HIGH-4 — return `Result` with diagnostic errors.

---

### MED-7: `check_program` duplicates builtin registration from `init_builtins`

**File**: `program.rs:14-27` vs `primitives.rs:204-219`
**Severity**: Medium (duplication)

`check_program` manually registers `print` and `read-line` builtins (lines 14-27), then calls `register_primitives()` (line 30). Meanwhile, `init_builtins()` (primitives.rs:204-219) does the exact same `print` + `read-line` registration followed by `register_primitives()`. The REPL path uses `init_builtins()`, the batch path uses `check_program`'s inline registration.

```rust
// program.rs:14-21 (batch path)
self.env.insert("print".to_string(), Scheme::mono(Type::Fn(...)));
self.env.insert("read-line".to_string(), Scheme::mono(Type::Fn(...)));
self.register_primitives();

// primitives.rs:204-218 (REPL path via init_builtins)
self.env.insert("print".to_string(), Scheme::mono(Type::Fn(...)));
self.env.insert("read-line".to_string(), Scheme::mono(Type::Fn(...)));
self.register_primitives();
```

**Impact**: If a builtin signature changes, both locations must be updated in sync. The `FnMeta` for `print`/`read-line` is only registered in `init_builtins`, not in `check_program`.

**Recommendation**: Have `check_program` call `init_builtins()` instead of inlining the registration.

---

### LOW-1: Primitive type name strings matched in 10+ locations

**Severity**: Low (consistency)

The pattern `match name { "Int" => Type::Int, "Bool" => Type::Bool, "String" => Type::String, "Float" => Type::Float, ... }` appears in:

1. `unification.rs:32-35` — `resolve_type_expr_with_vars`
2. `unification.rs:156-163` — `resolve_annotation`
3. `unification.rs:227-232` — `resolve_annotation_type`
4. `traits.rs:183-187` — `resolve_type_expr_hkt`
5. `traits.rs:315-319` — `name_to_type`
6. `traits.rs:368-378` — `validate_impl` (primitive arity check)
7. `traits.rs:486-489` — `find_impl_for_type`
8. `traits.rs:628-635` — `resolve_one_method`
9. `mono.rs:328-331` — `type_to_name`
10. `introspect.rs:237` — `impls_for_type`

**Impact**: Adding a new primitive type (e.g., `Char`) requires updates in 10+ places.

**Recommendation**: Add a `Type::from_name(name: &str) -> Option<Type>` method and a `Type::type_name(&self) -> Option<&str>` method to centralize this mapping.

---

### LOW-2: `user_impls` is a `Vec<TraitImpl>` scanned linearly

**File**: `traits.rs` (multiple methods)
**Severity**: Low (performance)

`user_impls` is scanned linearly in:
- `find_impl_for_type` — 4 separate scan loops (concrete match, bare match, polymorphic match, unresolved match) at lines 496-579
- `resolve_one_method` — scanned to count matching impls (line 605-613), then again to find the impl (lines 618-627)
- `impls_for_trait` — full scan (introspect.rs:210-231)
- `impls_for_type` — full scan (introspect.rs:241-246)

**Impact**: Currently negligible (prelude has ~20 impls), but would become noticeable with many user-defined impls. The multiple scans in `find_impl_for_type` also make the priority logic hard to follow.

**Recommendation**: Index `user_impls` as `HashMap<(trait_name, target_type), Vec<TraitImpl>>` for O(1) lookup. This would simplify `find_impl_for_type` considerably.

---

### LOW-3: `is_inline_primitive` / `is_extern_primitive` match against hardcoded string lists

**File**: `primitives.rs:222-262`
**Severity**: Low (maintainability)

These functions duplicate the primitive names that are already registered in `register_primitives`. They're called from codegen to decide how to compile a function call.

```rust
pub(crate) fn is_inline_primitive(name: &str) -> bool {
    matches!(name, "add-i64" | "sub-i64" | "mul-i64" | ... )  // 18 names
}
pub(crate) fn is_extern_primitive(name: &str) -> bool {
    matches!(name, "int-to-string" | "bool-to-string" | ... )  // 11 names
}
```

**Impact**: Adding a primitive requires updating both the registration loop and these match lists.

**Recommendation**: Derive from the same table as MED-5, or store sets on `TypeChecker` populated during registration.

---

### LOW-4: Four `pub` fields on TypeChecker should be `pub(crate)`

**File**: `mod.rs:131-142`
**Severity**: Low (encapsulation)

Four fields are `pub` instead of `pub(crate)`:
- `type_defs` (line 131)
- `constructor_to_type` (line 134)
- `expr_types` (line 137)
- `fn_meta` (line 142)

**Impact**: These are accessed from codegen and REPL modules within the crate, but `pub` exposes them beyond the crate boundary.

**Recommendation**: Change to `pub(crate)` for all four.

---

### LOW-5: `tc_with_prelude()` test helper duplicated 3 times

**File**: `inference.rs:662-696`, `traits.rs:791-825`, `introspect.rs:256-290`
**Severity**: Low (test maintainability)

The exact same 34-line function is copy-pasted in three test modules. If the prelude loading sequence changes, all three must be updated.

**Recommendation**: Move to a shared test utility module (e.g., `typechecker::test_util`) or a `#[cfg(test)]` module at the `mod.rs` level.

---

### LOW-6: `apply_concrete_ret` has an unreachable fallback

**File**: `mono.rs:343-355`
**Severity**: Low (code clarity)

```rust
pub(super) fn apply_concrete_ret(scheme: &Scheme, concrete_params: &[Type]) -> Type {
    // ...
    if let Type::Fn(_, ret) = &scheme.ty {
        substitute_vars(ret, &mapping)
    } else {
        Type::Int // fallback, shouldn't happen
    }
}
```

The `Type::Int` fallback masks bugs if a scheme's type is ever not a function.

**Recommendation**: Use `unreachable!()` or return `Result` with a diagnostic error.

---

## Prioritized Improvement Plan

### Phase 1: Panic Removal (Safety)

**Goal**: Eliminate all `panic!()` and `.expect()` from non-test code.

1. Change `resolve_type_expr_with_vars` to return `Result<Type, CranelispError>`, threading spans from callers (HIGH-4)
2. Change `resolve_type_expr_hkt` to return `Result<Type, CranelispError>` (MED-6)
3. Change `finalize_defn_type` to return `Result<Scheme, CranelispError>` (MED-6)
4. Replace `apply_concrete_ret` fallback with `unreachable!()` or `Result` (LOW-6)
5. Audit remaining `unreachable!()` calls — they're in `fresh_var()` extraction patterns and are genuinely unreachable

### Phase 2: Function Decomposition (Complexity)

**Goal**: Break large functions into composable pieces.

1. Extract `infer_expr` match arms into per-variant methods: `infer_apply`, `infer_match`, `infer_lambda`, `infer_let`, `infer_bind`, `infer_do`, `infer_vec_lit`, `infer_annotate` (HIGH-1)
2. Further decompose `infer_apply` into helpers for overload interception, constrained fn interception, trait method tracking, mono call tracking (HIGH-1)
3. Extract `check_program` phases into named methods (HIGH-2)
4. Split `resolve_one_method` into `resolve_polymorphic_method` and `resolve_concrete_method` (HIGH-3)

### Phase 3: Deduplication

**Goal**: Remove copy-pasted logic.

1. Unify `check_defn` and `check_impl_method` into `check_defn_with_self_type(defn, Option<&Type>)` (MED-2)
2. Extract shared `lookup_and_instantiate_member` from `resolve_dotted_var` (MED-1)
3. Have `check_program` call `init_builtins()` instead of duplicating registration (MED-7)
4. Deduplicate `tc_with_prelude()` test helper (LOW-5)

### Phase 4: Data Modeling

**Goal**: Improve type safety and reduce stringly-typed patterns.

1. Add `Type::from_name(name) -> Option<Type>` and `Type::type_name(&self) -> Option<&str>` to centralize primitive name mapping (LOW-1)
2. Define primitives as a static table; derive registration, `is_inline_primitive`, `is_extern_primitive` from it (MED-5, LOW-3)
3. Group pending resolution fields into a `PendingWork` sub-struct or use a `PendingResolution` enum (MED-3)
4. Change `pub` fields to `pub(crate)` (LOW-4)
5. Consider indexing `user_impls` as `HashMap<(String, String), Vec<TraitImpl>>` (LOW-2)

### Phase 5: Performance

**Goal**: Reduce unnecessary allocations.

1. Replace `self.env.clone()` save/restore with a scope-stack or targeted key save/restore (MED-4)

### Phase 6: Test Coverage

**Goal**: Achieve unit test coverage for all subsystems.

1. Add ADT registration tests: type params, constructors, field accessors, error cases
2. Add trait resolution tests: single impl, multiple impls, polymorphic impl, HKT dispatch
3. Add overload dispatch tests: exact match, auto-curry, ambiguity errors
4. Add monomorphization tests: basic specialization, duplicate detection, constrained fn with multiple trait calls
5. Add constrained function tests: detection, deferred resolution
6. Add negative tests: unknown type in trait sig, missing method in impl, arity mismatch

---

## Verification

After implementing changes:

1. `just test` — all existing 49 tests pass
2. `just check` — no new clippy warnings
3. `just run examples/hello.cl` and `just run examples/factorial.cl` — programs execute correctly
4. New unit tests pass for each subsystem modified
5. No `panic!()` or `.expect()` remain in non-test code (verify with `grep -n 'panic!\|\.expect(' src/typechecker/*.rs | grep -v '#\[cfg(test)\]'`)
