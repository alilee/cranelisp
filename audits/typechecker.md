# Typechecker Module Audit

**Module**: `src/typechecker/` (11 files, 5,799 lines) + `src/typechecker.rs` (1,246 lines)
**Date**: 2026-03-03
**Scope**: Simplicity, maintainability, complexity, duplication, data modeling, test coverage

## Module Overview

The typechecker implements Algorithm W (Hindley-Milner) type inference with extensions for trait dispatch, overloaded multi-sig functions, auto-curry, and monomorphization of constrained polymorphic functions. It also registers all builtins (primitives, IO, Trace, macro types, special forms, platform functions), manages per-module symbol tables, and provides REPL introspection. The module has grown significantly since the February 2026 audit to incorporate IO scheduling metadata, the `run-tests` special form, `ParBind` type checking, Trace ADT type handling, and cross-module mono specialization.

### File Metrics

| File | Lines | Responsibility | Tests |
|---|---|---|---|
| `typechecker.rs` | 1,246 | TypeChecker struct, public types, module-walk resolution, scope management, platform registration | 0 |
| `inference.rs` | 1,169 | `infer_expr`, `check_defn`, `check_impl_method`, pattern matching, exhaustiveness checking | 8 |
| `primitives.rs` | 1,205 | Primitive registration, IO/Trace/macro type seeding, platform registration, type sig parsing | 9 |
| `traits.rs` | 978 | Trait registration (regular + HKT), impl validation, method resolution, default synthesis | 4 |
| `introspect.rs` | 603 | `describe_symbol`, `list_symbols`, codegen views for REPL | 13 |
| `overloads.rs` | 371 | Multi-sig dispatch, `check_defn_multi`, auto-curry resolution | 0 |
| `unification.rs` | 439 | `unify`, `resolve_type_expr_*`, `instantiate`, `generalize` | 0 |
| `mono.rs` | 370 | Constrained fn detection, monomorphization, `finalize_defn_type` | 0 |
| `program.rs` | 318 | `check_program` batch-mode two-pass checker | 0 |
| `adt.rs` | 163 | `register_type_def` for deftype | 0 |
| `tests.rs` | 470 | Integration tests via `check_program`, module scope tests | 36 |

**Total tests**: 70 (up from 49 in February 2026)

---

## Findings

### HIGH-1: `infer_expr()` is 603 lines with five separate callee-inspection blocks

**File**: `inference.rs:30-633`
**Severity**: High (maintainability)

The core expression inference function has grown from 447 to 603 lines. The `Apply` arm (lines 170-345) now has five sequential `if let Expr::Var { name, .. }` blocks that each inspect the callee for different concerns. The overall function still handles 13+ expression variants in one monolithic match.

```rust
// inference.rs:170-345 — the Apply arm (175 lines, five callee inspection blocks)
Expr::Apply { callee, args, span, .. } => {
    // 1. Intercept: overloaded callee               (lines 173-191)
    if let Expr::Var { name, .. } = callee.as_ref() { ... }

    // 2. Intercept: constrained function call       (lines 194-209)
    let callee_ty = if let Expr::Var { name, .. } = callee.as_ref() { ... };

    // ... infer args, unify, auto-curry ...

    // 3. Track trait method calls                   (lines 254-296)
    if let Expr::Var { name, .. } = callee.as_ref() { ... }

    // 4. Track constrained function calls           (lines 299-323)
    if let Expr::Var { name, .. } = callee.as_ref() { ... }

    // 5. Track extern/platform primitive calls      (lines 325-340)
    if let Expr::Var { name, .. } = callee.as_ref() { ... }
}
```

New expressions (`Expr::ParBind`, `Expr::ParLet`, `Expr::Trace`, `Expr::RunTests`) have also been added inline, each adding new arms to the already large match. The `Expr::RunTests` arm at lines 605-631 hard-codes expected function signatures.

**Impact**: Adding a new expression form or new callee-inspection concern requires reading 600+ lines to understand what already exists. The five callee blocks are interleaved with argument type inference, making the control flow hard to trace.

**Recommendation**: Extract each `Expr` arm into a dedicated method (`infer_apply`, `infer_match`, `infer_lambda`, `infer_par_bind`, `infer_run_tests`). Consolidate the five callee-inspection passes in `infer_apply` into a single `analyze_callee` method that returns a structured enum.

---

### HIGH-2: `check_program()` is 318 lines — monolithic batch pipeline

**File**: `program.rs:13-318`
**Severity**: High (maintainability)

This function orchestrates the entire batch-mode typechecking pipeline in a single method. The pipeline has grown from the February 2026 version and now has 17 distinct phases:

```rust
pub fn check_program(&mut self, program: &Program) -> Result<CheckResult, CranelispError> {
    // 1.  Register builtins                          lines 16-17
    // 2.  Register type definitions                  lines 19-25
    // 3.  Register user traits                       lines 27-30
    // 4.  Validate/register impls                    lines 32-36
    // 5.  Process DefnMulti items                    lines 38-58
    // 6.  Extract impl method defns                  lines 60-74
    // 7.  Synthesize default method defns            lines 64-73
    // 8.  Build impl self type map                   lines 76-103
    // 9.  Collect all defns                          lines 105-114
    // 10. Pass 1: register signatures                lines 116-124
    // 11. Process param annotations                  lines 126-135
    // 12. Pass 2: check bodies + generalize          lines 137-173
    // 13. Detect constrained fns                     lines 175-182
    // 14. Early trait resolution                     lines 187
    // 15. Resolve multi-sig overloads                lines 191-233
    // 16. Verify main                                lines 235-269
    // 17. First monomorphisation + overload + late resolution + second mono
    //                                                lines 271-315
    // 18. Resolve expr_types                         lines 303-308
}
```

**Impact**: Any change to the pipeline order requires understanding the entire 318-line function. The ordering of phases 13-17 is especially subtle (detect constrained fns before first resolution; run mono twice; deferred resolutions are moved back after overload resolution).

**Recommendation**: Extract phases into named private methods: `register_all_builtins_and_types`, `pass1_register_signatures`, `pass2_check_bodies`, `resolve_all_dispatches`, `validate_main`. Top-level function becomes a readable 20-line sequence of named steps.

---

### HIGH-3: `resolve_one_method()` is 142 lines with deep nesting

**File**: `traits.rs:642-784`
**Severity**: High (complexity)

This function resolves a single pending trait method call. The top-level `match &concrete` dispatches to two major arms, each with 3-4 levels of nested conditionals. The function now has an additional code path for polymorphic impl methods (constrained fn detection + `pending_mono_calls`), adding another level of nesting inside the concrete type arm.

```rust
// traits.rs:714-766 — concrete type arm (52 lines of nested logic)
Type::Int | Type::Bool | ... | Type::ADT(_, _) => {
    if let Some(target_mangled) = self.find_impl_for_type(...) {
        if let Type::ADT(base_name, args) = &concrete {
            if args.iter().any(has_type_var) {
                // Clone impls to avoid borrow — then unify
                let all_impls_vec2: Vec<_> = self.all_impls().cloned().collect();
                let matching_impl = all_impls_vec2.into_iter().find(...);
                if let Some(ui) = matching_impl {
                    let self_type = self.resolve_impl_self_type(&ui)?;
                    self.unify(arg_type, &self_type, span)?;
                }
            }
        }
        // Re-apply subst after potential unification
        let concrete = apply(&self.subst, arg_type);
        // Check if target is a constrained fn (polymorphic impl)
        if self.resolve_constrained_fn_via_modules(&mangled).is_some() {
            if let Type::ADT(_, args) = &concrete {
                if !args.is_empty() && args.iter().all(|a| !has_type_var(a)) {
                    // ... push to pending_mono_calls, return SigDispatch ...
                }
            }
        }
        return Ok(Some(ResolvedCall::TraitMethod { ... }));
    }
}
```

**Impact**: The borrow-conflict workaround (clone all impls into a Vec to unify with one of them) adds noise and allocation. The four-level nesting makes it hard to verify correctness of the ADT + poly-impl resolution path.

**Recommendation**: Split into `resolve_polymorphic_method` and `resolve_concrete_method`. Extract the poly-impl unification block into `unify_poly_impl_type`. Eliminate the clone-to-avoid-borrow pattern with a two-pass approach (find index, then unify).

---

### HIGH-4: Production `panic!()` calls in `unification.rs` and `traits.rs`

**File**: `unification.rs:52,68,88` and `traits.rs:216,222`
**Severity**: High (robustness)

Five `panic!()` calls in production (non-test) code remain from the February 2026 audit, unchanged:

```rust
// unification.rs:52 — resolve_type_expr_with_vars
_ => { panic!("unknown type: {}", name) }          // reachable from adt.rs:44

// unification.rs:68 — resolve_type_expr_with_vars
_ => { panic!("unresolved type variable: {}", name) } // reachable from adt.rs:44

// unification.rs:88 — resolve_type_expr_with_vars
_ => { panic!("unknown type: {}", name) }          // Applied branch

// traits.rs:216 — resolve_type_expr_hkt
_ => { panic!("unknown type in HKT trait sig: {}", name) }

// traits.rs:222 — resolve_type_expr_hkt
TypeExpr::SelfType => { panic!("SelfType in HKT trait signature") }
```

**Impact**: A typo in a type name in a `deftype`, trait declaration, or impl crashes the compiler process rather than producing a diagnostic error with a source span. The `resolve_type_expr_with_vars` panics are reachable from `register_type_def` (via `adt.rs:44`).

**Recommendation**: Convert `resolve_type_expr_with_vars` and `resolve_type_expr_hkt` to return `Result<Type, CranelispError>`. Callers already have spans available. The annotation path (`resolve_annotation_type`, `unification.rs:222-253`) already returns `Result` — use it as the template.

---

### HIGH-5: Additional `.expect()` panics in `mono.rs` and `primitives.rs`

**File**: `mono.rs:183,237` and `primitives.rs:730,736,772,778`
**Severity**: High (robustness)

Six `.expect()` calls that can panic at runtime in non-test code paths:

```rust
// mono.rs:183 — monomorphise_all
let cf_scheme = self
    .resolve_constrained_fn_via_modules(&fn_name)
    .expect("constrained fn must exist for monomorphisation");

// mono.rs:237 — finalize_defn_type
let old_scheme = self.remove_def(name).expect("function not in env");

// primitives.rs:730 — add_internal_bind_constructor
let cm = self.modules.get_mut(&mod_path)
    .expect("primitives module must exist");

// primitives.rs:736 — add_internal_bind_constructor
let entry = cm.symbols.get_mut(&io_sym)
    .expect("IO type must exist after register_type_def");

// primitives.rs:772,778 — add_internal_par_constructor (same pattern)
```

The `primitives.rs` expects are legitimate invariants (primitives module is always populated by `register_primitives` before these methods are called), but they would produce panic messages without source context in the unlikely event of a bug. The `mono.rs` expects are genuine user-triggerable paths if monomorphisation state becomes inconsistent.

**Impact**: `mono.rs:183` can panic if a constrained function is removed from the env between detection and monomorphisation (e.g., in REPL redefinition scenarios). `mono.rs:237` (`finalize_defn_type`) panics if called on a name that was removed.

**Recommendation**: Convert `mono.rs` expects to `Result<_, CranelispError>` with informative messages. For `primitives.rs`, replace with `unreachable!("invariant violated: ...")` to signal they are programmer errors, not user errors.

---

### HIGH-6: Test coverage remains thin for critical subsystems

**Severity**: High (quality assurance)

Despite growing from 49 to 70 tests, the increase is concentrated in integration tests (`tests.rs`: 36 tests) and `primitives.rs` platform registration tests (9 tests). The following subsystems still have zero unit tests:

| Subsystem | Lines | Unit tests | Integration coverage |
|---|---|---|---|
| `mono.rs` — monomorphisation | 370 | 0 | Indirect via integration tests |
| `overloads.rs` — multi-sig dispatch | 371 | 0 | None |
| `adt.rs` — type registration | 163 | 0 | Indirect via prelude |
| `unification.rs` — unify/generalize | 439 | 0 | None |
| `program.rs` — pipeline | 318 | 0 | None |
| `RunTests` type checking | ~27 | 0 | None |
| `ParBind` / `ParLet` type checking | ~65 | 0 | None |
| IO scheduling integration | — | 0 | None |
| Constrained fn detection | ~55 | 0 | None |
| Cross-module mono specialization | — | 0 | None |

The `tc_with_prelude()` test helper is now duplicated in three files (see LOW-5). The three copies diverged slightly: `inference.rs:1029` includes default method synthesis logic; `traits.rs:903` and `introspect.rs:356` use the older variant without it.

**Impact**: Regressions in monomorphisation, overload dispatch, or the scheduling integration would go undetected. The `RunTests` special form type-checks callback signatures against hard-coded types (inference.rs:611-631) with no unit test coverage.

**Recommendation**: Add targeted unit tests for each subsystem listed above. Deduplicate `tc_with_prelude()` into a shared `#[cfg(test)]` module at the `typechecker.rs` level. Add at least one test for `RunTests` type checking and `ParBind` IO type enforcement.

---

### MED-1: `check_defn()` and `check_impl_method()` duplicate ~30 lines of logic

**File**: `inference.rs:917-1011`
**Severity**: Medium (duplication)

These two methods follow identical structure: create fresh param types, process annotations, register the function (allowing recursion), save local env, add params, infer body, unify with return type, restore env, remove entry, generalize, re-insert. The only difference in `check_impl_method` is pre-unifying one param with `self_type` (lines 989-992).

```rust
// inference.rs:917-964 (check_defn, 48 lines)
// inference.rs:968-1011 (check_impl_method, 44 lines)
// Shared structure:
let param_tys: Vec<Type> = defn.params.iter().map(|_| self.fresh_var()).collect();
let ret_ty = self.fresh_var();
// ... annotations ...
self.insert_def(defn.name.clone(), Scheme::mono(fn_ty));
let saved_local = self.local_env.clone();
// ... add params to local_env ...
let body_ty = self.infer_expr(&defn.body)?;
self.unify(&body_ty, &ret_ty, defn.span)?;
self.local_env = saved_local;
self.remove_def(&defn.name);
// ... generalize and re-insert ...
```

**Recommendation**: Unify into `check_defn_internal(defn, Option<(usize, &Type)>)` where the option is `(param_idx, self_type)` for impl methods and `None` for regular functions.

---

### MED-2: `resolve_dotted_var()` has two structurally identical lookup-and-instantiate blocks

**File**: `inference.rs:635-735`
**Severity**: Medium (duplication)

The Type.Constructor branch (lines 660-683) and the Trait.method branch (lines 698-723) each independently: check for overloads, check for constrained fn, instantiate, record expr type, and return. The logic is identical; only the parent validation differs.

```rust
// Type branch (lines 660-682):
if self.overloads.contains_key(member) { return Err(...) }
if scheme.is_constrained() { return Err(...) }
let ty = self.instantiate(&scheme);
self.record_expr_type(expr, &ty);
return Ok(ty);

// Trait branch (lines 710-722): identical except lookup source
if self.overloads.contains_key(member) { return Err(...) }
if scheme.is_constrained() { return Err(...) }
let ty = self.instantiate(&scheme);
self.record_expr_type(expr, &ty);
return Ok(ty);
```

**Recommendation**: Extract `lookup_and_instantiate(scheme: Scheme, full_name: &str, expr: &Expr, span: Span) -> Result<Type, CranelispError>` and call it from both branches.

---

### MED-3: Five `pending_*` Vec fields on TypeChecker with heterogeneous lifetimes

**File**: `typechecker.rs:201-216`
**Severity**: Medium (data modeling)

The TypeChecker struct holds five pending resolution vectors that all represent "work to do after inference":

```rust
pending_resolutions: Vec<(Span, String, String, Type)>,           // line 201
pending_overload_resolutions: Vec<(Span, String, Vec<Type>, Type)>, // line 208
pending_auto_curry: Vec<(Span, String, usize, usize)>,            // line 210
deferred_resolutions: Vec<(Span, String, String, Type)>,          // line 214
pending_mono_calls: Vec<(Span, String, Vec<Type>)>,               // line 216
```

All are bare tuples with positional fields. `pending_resolutions` and `deferred_resolutions` have identical tuple types but different semantics (the former is "not yet tried"; the latter is "tried but deferred for multi-impl resolution"). This is easily confused.

**Impact**: The struct has 23 fields total. The separate vectors with bare-tuple fields make it hard to read call-sites. `detect_constrained_fns` takes items from both `deferred_resolutions` and `pending_resolutions` by consuming both and putting back the remainder, which requires careful index tracking.

**Recommendation**: Define named structs for the pending items (e.g., `PendingMethodCall`, `PendingOverloadCall`, `PendingMonoCall`) and group them in a `PendingWork` sub-struct. Rename `deferred_resolutions` to `deferred_method_resolutions` to clarify the difference.

---

### MED-4: `self.local_env.clone()` repeated in every lexical scope

**File**: `inference.rs:156,367,936,994` and `program.rs:150`
**Severity**: Medium (performance)

The environment is cloned to implement lexical scoping in every lambda, every match arm, every `check_defn`, and every function in `check_program` pass 2. The post-prelude environment contains 70+ entries (all primitives, traits, constructors).

```rust
// inference.rs:156 (Lambda):
let saved_local = self.local_env.clone();
// ... add params, check body ...
self.local_env = saved_local;

// inference.rs:367 (Match — per arm!):
for arm in arms {
    let saved_local = self.local_env.clone();
    // ...
    self.local_env = saved_local;
}
```

The most expensive case is `check_program` pass 2 (program.rs:150): the env is cloned once per function definition in the program.

**Impact**: Measurable allocation cost for programs with many match arms or many function definitions. A program with 50 functions clones the env 50 times in pass 2; a match with 8 arms clones it 8 times.

**Recommendation**: Use a scope-stack: push a `HashMap<Symbol, Scheme>` for each scope, pop on exit. Lookup first checks the top of the stack, then falls through to the module system. This eliminates all `clone()` calls for lexical scoping.

---

### MED-5: `primitives.rs` Vec primitive registration uses repeated `fresh_var()` extraction pattern

**File**: `primitives.rs:247-405`
**Severity**: Medium (duplication)

The `register_vec_primitives` method registers 6 vec primitives. Each registration follows an identical pattern: allocate a fresh type var, immediately extract its `TypeId` via a match-or-`unreachable!()`, construct the scheme, call `register_builtin_with_jit_name`. The extraction pattern is repeated 12 times:

```rust
// Repeated 12 times (two per vec primitive):
let a_N = self.fresh_var();
let a_N_id = match &a_N {
    Type::Var(id) => *id,
    _ => unreachable!(),
};
```

**Impact**: Adding a new vec primitive requires copying this boilerplate. The `unreachable!()` arm is dead code noise.

**Recommendation**: Add a `TypeChecker::fresh_var_id(&mut self) -> (Type, TypeId)` helper that returns both the `Type::Var` and its `TypeId` atomically. Eliminate the separate extraction pattern everywhere it appears (also used in `register_bind_primitive`, `register_trait_internal`, `lookup_trait_method_scheme`).

---

### MED-6: Ambiguity warnings printed to `eprintln!` instead of structured diagnostics

**File**: `typechecker.rs:411-417`, `typechecker.rs:854-859`, `typechecker.rs:881-889`
**Severity**: Medium (robustness)

When a bare name becomes ambiguous, the code emits a warning via `eprintln!` rather than returning a structured error or storing it for later reporting:

```rust
// typechecker.rs:411-417 — insert_def_checked
if poisoned {
    let alts = self.find_ambiguous_alternatives(&name);
    eprintln!(
        "warning: bare name '{}' is now ambiguous — use {}",
        name, alts.join(" or ")
    );
}
```

The same pattern appears in `begin_module_scope` (line 854) and `install_imported_names` (line 881).

**Impact**: These warnings are silently swallowed in batch mode, lost in test output, and cannot be tested. The REPL does not see them as structured feedback. A user-facing diagnostic system should collect warnings alongside errors.

**Recommendation**: Return a `Vec<Warning>` or accumulate warnings in a `TypeChecker::warnings: Vec<String>` field that callers can display. This would also allow the test suite to assert on expected warnings.

---

### MED-7: `find_trait_for_method` scans all module symbols on every call

**File**: `typechecker.rs:693-710`
**Severity**: Medium (performance)

`find_trait_for_method` is called multiple times per function application during inference. It walks all symbols in the current module, follows import chains, and scans every `TraitDecl` entry's method list to find the trait for a given method name:

```rust
fn find_trait_for_method(&self, method_name: &str) -> Option<&str> {
    let cm = self.modules.get(current.as_ref())?;
    let candidates: Vec<crate::names::Symbol> = cm.symbols.keys().cloned().collect();
    for sym in &candidates {
        if let Some(entry) = self.resolve_entry_in_module(current, sym, 0, false) {
            if let ModuleEntry::TraitDecl { decl, .. } = entry {
                if decl.methods.iter().any(|m| m.name == method_name) {
                    return Some(&decl.name);
                }
            }
        }
    }
    None
}
```

This is O(S × M) per call where S is the number of symbols and M is the average methods per trait.

**Impact**: In the `Apply` arm of `infer_expr`, `find_trait_for_method` is called twice per function application (once for trait tracking, once for constrained fn detection). With a typical prelude of 50+ symbols and 5 traits, this is 500+ comparisons per function call site during inference.

**Recommendation**: Build a `method_to_trait: HashMap<Symbol, Symbol>` cache during `register_trait` and invalidate it when traits are removed. Populate it at trait registration time instead of scanning at lookup time.

---

### LOW-1: Primitive type name mapping in 8+ locations

**Severity**: Low (consistency)

The pattern `match name { "Int" => Type::Int, "Bool" => Type::Bool, "String" => Type::String, "Float" => Type::Float, ... }` appears in:

1. `unification.rs:31-35` — `resolve_type_expr_with_vars`
2. `unification.rs:158-163` — `resolve_annotation`
3. `unification.rs:227-232` — `resolve_annotation_type`
4. `traits.rs:206-210` — `resolve_type_expr_hkt`
5. `traits.rs:356-361` — `name_to_type`
6. `traits.rs:677-683` — `resolve_one_method` (Var arm unification)
7. `mono.rs:343-348` — `type_to_name`
8. `primitives.rs:1007-1013` — `sexp_to_type`
9. `introspect.rs:331-333` — `impls_for_type`

**Impact**: Adding a new primitive type (e.g., `Char`) requires updates in 9+ places.

**Recommendation**: Add `Type::from_name(name: &str) -> Option<Type>` and `Type::type_name(&self) -> Option<&str>` to `types.rs` to centralize this mapping.

---

### LOW-2: `user_impls` scanned linearly via `all_impls()` in many hot paths

**File**: `traits.rs` (multiple methods), `introspect.rs:241-270`
**Severity**: Low (performance)

`all_impls()` is an iterator over `self.modules.values().flat_map(|cm| cm.impls.iter())`. It is called in:
- `find_impl_for_type` — up to 4 times with different filters
- `resolve_one_method` — to count and find matching impls (lines 654-674)
- `impls_for_trait` in introspect — full scan
- `impls_for_type` in introspect — full scan

**Impact**: Currently negligible (prelude has ~25 impls across modules), but the four-pass scan in `find_impl_for_type` makes the priority logic hard to follow and scales poorly with many user impls.

**Recommendation**: Index impls as `HashMap<(trait_name, target_type_base), Vec<&TraitImpl>>` per module, or maintain a global `impl_index` on TypeChecker that is updated when `register_impl` is called.

---

### LOW-3: `apply_concrete_ret` still has the `Type::Int` fallback

**File**: `mono.rs:358-370`
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

This fallback silently returns `Type::Int` if a scheme is not a function type. It masks a potential invariant violation. Unchanged from February 2026 audit.

**Recommendation**: Replace with `unreachable!("apply_concrete_ret called on non-function scheme")` or return `Result<Type, CranelispError>`.

---

### LOW-4: `tc_with_prelude()` test helper duplicated 3 times and has diverged

**File**: `inference.rs:1029`, `traits.rs:903`, `introspect.rs:356`
**Severity**: Low (test maintainability)

Three distinct versions of the 34-50 line helper exist. They diverged since February 2026:
- `inference.rs:1029` — includes default method synthesis (synthesize_default_defns) at lines 1066-1073; handles `tc.impl_target_mangled()` correctly
- `traits.rs:903` — older version, does not synthesize default methods
- `introspect.rs:356` — same as `traits.rs` version (no default method synthesis)

This means tests in `traits.rs` and `introspect.rs` run with a slightly different environment than tests in `inference.rs`, potentially missing bugs related to default method interactions.

**Recommendation**: Move the canonical (most complete) version to a shared `#[cfg(test)]` module at the `typechecker.rs` level and import it in all three test modules.

---

### LOW-5: `Expr::RunTests` hard-codes expected callback signatures in the typechecker

**File**: `inference.rs:605-631`
**Severity**: Low (maintainability)

The `Expr::RunTests` arm hard-codes the expected signatures for `pass_fn` and `fail_fn`:

```rust
// inference.rs:611-625
let expected_pass = Type::Fn(
    vec![acc_ty.clone(), Type::String, Type::Int],
    Box::new(acc_ty.clone()),
);
// ...
let expected_fail = Type::Fn(
    vec![acc_ty.clone(), Type::String, Type::Int, Type::String, trace_ty],
    Box::new(acc_ty.clone()),
);
```

If the `run-tests` contract changes (e.g., adding a fourth parameter to `pass_fn`), the change must be made in both the special form documentation (`primitives.rs:821`) and the type-checking logic, with no compile-time link between them.

**Impact**: Easy to make the documentation and type-checking diverge. There are zero tests for `RunTests` type checking.

**Recommendation**: Define the callback signatures as named constants or helper functions that are referenced from both the docstring and the type-checking logic. Add unit tests covering both valid and invalid `run-tests` expressions.

---

### LOW-6: `add_internal_bind_constructor` and `add_internal_par_constructor` are near-identical

**File**: `primitives.rs:723-799`
**Severity**: Low (duplication)

These two private methods (76 lines total) share identical structure: look up `primitives` module, get the `IO` type entry, push a new `ConstructorInfo` with `internal: true`. They differ only in the constructor name, tag, and field types.

```rust
// Both methods:
let mod_path = ModuleFullPath::from("primitives");
let cm = self.modules.get_mut(&mod_path).expect(...);
let io_sym = crate::names::Symbol::from("IO");
let entry = cm.symbols.get_mut(&io_sym).expect(...);
if let ModuleEntry::TypeDef { info, .. } = entry {
    // ... push ConstructorInfo { internal: true, ... }
}
```

**Recommendation**: Extract `add_internal_io_constructor(name, tag, fields, docstring)` and call it from both. This also reduces the risk of the `expect()` calls being duplicated incorrectly.

---

### LOW-7: IO scheduling integration is a single opaque field with no invariants documented

**File**: `typechecker.rs:236-239`
**Severity**: Low (data modeling)

The `platform_scheduling` field stores scheduling classes for platform functions:

```rust
pub platform_scheduling: HashMap<String, crate::platform::SchedulingClass>,
```

This field is populated by `register_platform` (primitives.rs:977-979) and read by `schedule.rs` via `tc.scheduling_of()`. There is no documentation on:
- What happens if a platform function is registered twice (second write wins silently)
- Whether scheduling classes can be overridden after initial registration
- Why the field is `pub` rather than accessed only via `scheduling_of()`

**Impact**: The `schedule.rs` module takes a `&TypeChecker` reference and calls `scheduling_of()`, coupling the scheduling pass tightly to the typechecker struct. The `pub` field allows callers to mutate scheduling state directly, bypassing the structured registration path.

**Recommendation**: Make `platform_scheduling` `pub(crate)` and document its invariants. Add a comment in `register_platform` about duplicate registration behavior.

---

## Prioritized Improvement Plan

### Phase 1: Panic Removal (Safety)

**Goal**: Eliminate all `panic!()` and unsafe `.expect()` from non-test code.

1. Convert `resolve_type_expr_with_vars` to return `Result<Type, CranelispError>`, threading spans from callers. (HIGH-4)
2. Convert `resolve_type_expr_hkt` to return `Result<Type, CranelispError>`. (HIGH-4)
3. Convert `finalize_defn_type` to return `Result<Scheme, CranelispError>`. (HIGH-5)
4. Convert `monomorphise_all` to use `?` instead of `.expect()` on `resolve_constrained_fn_via_modules`. (HIGH-5)
5. Replace `primitives.rs` expects in `add_internal_bind_constructor` / `add_internal_par_constructor` with `unreachable!("invariant violated: ...")`. (HIGH-5)
6. Replace `apply_concrete_ret` fallback with `unreachable!()`. (LOW-3)

### Phase 2: Function Decomposition (Complexity)

**Goal**: Break large functions into composable pieces.

1. Extract `infer_expr` match arms into per-variant methods: `infer_apply`, `infer_match`, `infer_lambda`, `infer_par_bind`, `infer_run_tests`. (HIGH-1)
2. Consolidate the five callee-inspection blocks in `infer_apply` into an `analyze_callee` method. (HIGH-1)
3. Extract `check_program` phases into named private methods. (HIGH-2)
4. Split `resolve_one_method` into `resolve_polymorphic_method` and `resolve_concrete_method`. (HIGH-3)
5. Extract `add_internal_io_constructor` helper from the duplicate `add_internal_bind_constructor` / `add_internal_par_constructor`. (LOW-6)

### Phase 3: Deduplication

**Goal**: Remove copy-pasted logic.

1. Unify `check_defn` and `check_impl_method` into `check_defn_internal`. (MED-1)
2. Extract `lookup_and_instantiate` helper in `resolve_dotted_var`. (MED-2)
3. Add `TypeChecker::fresh_var_id()` helper to eliminate repeated extraction boilerplate in `primitives.rs` and trait registration. (MED-5)
4. Consolidate the three `tc_with_prelude()` test helper copies into one canonical version. (LOW-4)

### Phase 4: Data Modeling

**Goal**: Improve type safety and reduce stringly-typed patterns.

1. Add `Type::from_name(name) -> Option<Type>` and `Type::type_name(&self) -> Option<&str>` to centralize primitive name mapping. (LOW-1)
2. Define named structs for pending work items; group into a `PendingWork` sub-struct on TypeChecker. (MED-3)
3. Make `platform_scheduling` `pub(crate)` and document registration invariants. (LOW-7)
4. Return structured warnings from `begin_module_scope`/`insert_def_checked` instead of `eprintln!`. (MED-6)

### Phase 5: Performance

**Goal**: Reduce unnecessary allocations and scans.

1. Add a `method_to_trait: HashMap<Symbol, Symbol>` cache populated during `register_trait`, replacing the per-call linear scan in `find_trait_for_method`. (MED-7)
2. Replace `self.local_env.clone()` save/restore with a scope-stack (push/pop layers). (MED-4)
3. Index `user_impls` as `HashMap<(trait_name, target_type_base), Vec<TraitImpl>>` to avoid O(n) scans in `find_impl_for_type`. (LOW-2)

### Phase 6: Test Coverage

**Goal**: Achieve unit test coverage for all subsystems.

1. Add tests for `RunTests` type checking: valid callbacks, wrong callback arity, wrong return type. (HIGH-6, LOW-5)
2. Add tests for `ParBind` type checking: non-IO binding, valid parallel IO. (HIGH-6)
3. Add tests for constrained fn detection and monomorphization: basic specialization, duplicate detection. (HIGH-6)
4. Add tests for overload dispatch: exact match, auto-curry, ambiguity error. (HIGH-6)
5. Add tests for ADT registration: type params, constructors, field accessors. (HIGH-6)
6. Add tests for unification edge cases: occurs check, TyConApp resolution. (HIGH-6)
7. Add negative tests: missing trait impl, method arity mismatch, unknown type in HKT sig. (HIGH-6)

---

## Verification

After implementing changes:

1. `just test` — all 70+ existing tests pass
2. `just check` — no new clippy warnings
3. `just run examples/hello.cl` and `just factorial` — programs execute correctly
4. New unit tests pass for each subsystem modified
5. No `panic!()` or user-triggerable `.expect()` remain in non-test code:
   ```
   grep -n 'panic!\|\.expect(' src/typechecker.rs src/typechecker/*.rs | grep -v '#\[cfg(test)\]' | grep -v 'tests\.rs'
   ```
6. `eprintln!` warnings replaced by structured accumulation:
   ```
   grep -n 'eprintln!' src/typechecker.rs src/typechecker/*.rs
   ```
