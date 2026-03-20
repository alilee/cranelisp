# Auto-Curry Design

This document describes the design for auto-curry detection (A1) in the reimplementation typechecker. Auto-currying is the language feature where calling a function with fewer arguments than it declares parameters returns a closure capturing the applied arguments (spec 04-expressions.md section 4.6.3).

## Spec Summary

- `(f arg1 ... argk)` where `f :: (Fn [T1 ... Tn] R)` and `k < n` produces a closure of type `(Fn [Tk+1 ... Tn] R)`
- Works at any depth: supplying k of n arguments returns a function expecting n-k
- `args.is_empty()` is NOT auto-curry (zero-arg call is a normal call or bare reference)
- Multi-sig disambiguation uses expected return type arity when multiple variants are curry candidates (section 4.7.4)
- Multi-sig bare references (zero args) are a compile error (ambiguous)

## Sketch Comparison

The sketch implements auto-curry via two mechanisms:

### 1. Single-arity auto-curry (in `inference.rs`)

Detection happens during `infer_apply`. The sketch attempts normal unification (`callee_ty` with `Fn(arg_types, ret_ty)`) first. When that unification FAILS:

1. Resolve the callee type to check if it is `Type::Fn(params, ret)`
2. Check `args.len() < params.len() && !args.is_empty()`
3. Unify each applied arg with the corresponding parameter
4. Build the curry return type: `Fn(remaining_params, ret)`
5. Push a `(span, name, applied_count, total_count)` tuple onto `pending_auto_curry`
6. Return the curry return type — the original unification error is discarded

This approach uses unification failure as the trigger for auto-curry detection.

### 2. Multi-sig auto-curry (in `overloads.rs`)

In `resolve_overloads`, after checking exact-arity matches, the sketch checks for curry candidates:

1. For each variant where `param_types.len() > concrete_args.len() && !concrete_args.is_empty()`, check type compatibility
2. If exactly one curry candidate: unify applied args, build `Fn(remaining, ret)`, emit `ResolvedCall::AutoCurry`
3. If multiple curry candidates: try to disambiguate using the resolved return type — if it is `Type::Fn(expected_params, _)`, keep only candidates where `remaining == expected_params.len()`
4. After narrowing, if exactly one candidate remains, proceed; otherwise error

### Key data structures

- `pending_auto_curry: Vec<(Span, String, usize, usize)>` — span, function name, applied_count, total_count
- `ResolvedCall::AutoCurry { target_name, applied_count, total_count }` — the resolution stored in `MethodResolutions`

### Resolution timing

Both single-arity and multi-sig auto-curry resolutions are finalized in `resolve_overloads()`, which runs as a post-inference pass. Single-arity entries are trivially converted from the pending list. Multi-sig entries are resolved alongside overload dispatch.

## Reimplementation Approach

### Strategy: detect at unification failure in `infer_apply`

Follow the sketch's approach of detecting auto-curry as a fallback when normal function application unification fails. This is clean because:

- No speculative branching before trying the normal path
- The callee type is already inferred, so we know the full parameter list
- Unification failure is a natural trigger — it means "these types don't match as a direct call"

### Changes to `infer_apply` (in `crates/cranelisp-typecheck/src/infer.rs`)

Currently, `infer_apply` does:

```rust
let expected_fn = Type::Fn(arg_types.clone(), Box::new(ret_ty.clone()));
self.unify(&callee_ty, &expected_fn, span)?;
```

Change to:

```rust
let expected_fn = Type::Fn(arg_types.clone(), Box::new(ret_ty.clone()));
let unify_result = self.unify(&callee_ty, &expected_fn, span);

if let Err(ref _e) = unify_result {
    // Try auto-curry: callee has more params than provided args
    let resolved_callee = self.apply_subst(&callee_ty);
    if let Type::Fn(params, ret) = &resolved_callee {
        if args.len() < params.len() && !args.is_empty() {
            // Unify applied args with first N params
            for (arg_ty, param_ty) in arg_types.iter().zip(params.iter()) {
                self.unify(arg_ty, param_ty, span)?;
            }
            let remaining: Vec<Type> = params[args.len()..]
                .iter()
                .map(|t| self.apply_subst(t))
                .collect();
            let curry_ret = Type::Fn(remaining, ret.clone());

            // Record auto-curry resolution
            if let Expr::Var { name, .. } = callee {
                self.pending_auto_curry.push((
                    span,
                    name.clone(),
                    args.len(),
                    params.len(),
                ));
            }

            let ty = self.apply_subst(&curry_ret);
            self.record_expr_type(span, ty.clone());
            return Ok(ty);
        }
    }
    // Not auto-curryable — propagate original error
    unify_result?;
}
```

### New field on TypeChecker (in `crates/cranelisp-typecheck/src/checker.rs`)

Add:

```rust
/// Pending auto-curry resolutions for single-arity functions.
/// (call_span, function_name, applied_arg_count, total_param_count)
pub(crate) pending_auto_curry: Vec<(Span, Symbol, usize, usize)>,
```

Initialize to `Vec::new()` in `TypeChecker::new()`.

### Changes to `ResolvedCall::AutoCurry` (in `crates/cranelisp-types/src/check.rs`)

The existing definition is missing `total_count`. The backend needs total_count to know how many parameters the wrapper closure must accept. Add it:

```rust
AutoCurry {
    target_name: Symbol,
    applied_count: usize,
    total_count: usize,
}
```

### Resolution pass: drain pending_auto_curry

Add a method to TypeChecker (in a new `overloads.rs` or in `program.rs`):

```rust
pub(crate) fn resolve_auto_curry(&mut self) {
    let pending = std::mem::take(&mut self.pending_auto_curry);
    for (span, name, applied_count, total_count) in pending {
        self.method_resolutions.insert(
            span,
            ResolvedCall::AutoCurry {
                target_name: name,
                applied_count,
                total_count,
            },
        );
    }
}
```

Call this at the end of `check_program` (or wherever `resolve_overloads` will eventually live), before building `CheckResult`.

### REPL path

The REPL checks one form at a time. After `infer_expr` for a REPL input, call `resolve_auto_curry()` before returning `ReplCheckResult`. The `pending_auto_curry` list should be drained per-input.

## Key Decisions

### Q1: When is partial application detected?

**During `infer_apply`, on unification failure.** This is the sketch's approach and it works well. The alternative — checking arity before unification — would require extra machinery to distinguish "too few args" from "wrong types", and would complicate the normal path.

### Q2: How does it interact with multi-sig functions?

Multi-sig functions are not yet implemented in the reimplementation. When they are added (via `resolve_overloads`), multi-sig auto-curry follows the sketch pattern:

1. In the overload resolution loop, after checking exact-arity matches, check for curry candidates (variants with more params than supplied args)
2. If multiple curry candidates, disambiguate using the resolved return type's arity
3. Emit `ResolvedCall::AutoCurry` with the mangled variant name as `target_name`

The single-arity detection in `infer_apply` will NOT fire for multi-sig calls because multi-sig callee types are registered with their base name (which maps to multiple signatures). The overload resolution path handles them separately. This is the same separation the sketch uses.

### Q3: How does it interact with constrained polymorphism?

A constrained polymorphic function (e.g., `(defn add [x y] (+ x y))` with inferred `:Num a => (Fn [a a] a)`) currently cannot be used as a bare value (the `in_call_position` check in `infer_var`). Auto-curry is a call — the callee IS in call position — so constrained fns can be auto-curried.

However, the auto-curried result is a closure. The monomorphisation request must still be generated at the call site where the curried closure is applied. This means:

- At the curry site `(add 5)`, the constraint `Num Int` is established and the concrete specialization `add$Int+Int` is known
- The `target_name` in `AutoCurry` should be the monomorphised name (e.g., `add$Int+Int`), not the base name
- This requires that constrained fn detection runs before or during auto-curry resolution

For now (A1 scope), constrained + auto-curry interaction is deferred. The initial implementation handles non-constrained user functions and inline primitives (like `(+ 1)` which is already a trait method call, handled differently). A follow-up task will address the constrained case.

### Q4: What type does the curried result have?

`(Fn [Tk+1 ... Tn] R)` where the types are taken from the callee's function type after applying current substitutions. This is straightforward: the callee type is `Fn(params, ret)`, we take `params[k..]` and `ret`.

## Edge Cases

### Bare function references (zero args)

`(let [f add] ...)` where `add :: (Fn [Int Int] Int)` is NOT auto-curry. This is a normal variable reference — the function value is captured. `args.is_empty()` guard prevents this from entering the auto-curry path.

For constrained fns, bare references are already rejected by the `in_call_position` check.

For multi-sig fns, bare references are a compile error per spec section 4.6.3.

### Zero-arg functions

`(defn f [] 42)` — calling `(f)` is a normal zero-arg call. There is no auto-curry for zero-arg functions because you cannot supply fewer than zero arguments.

### Currying a curried result

```clojure
(defn add3 [x y z] (+ x (+ y z)))
(let [f (add3 1)]       ; f :: (Fn [Int Int] Int)
  (let [g (f 2)]        ; g :: (Fn [Int] Int) — curries the closure
    (g 3)))
```

The second curry `(f 2)` where `f` is already a closure works because:
- `f` has type `(Fn [Int Int] Int)`
- `(f 2)` supplies 1 of 2 args
- Unification of `(Fn [Int Int] Int)` with `(Fn [Int] ?ret)` fails
- Auto-curry fallback fires: remaining is `[Int]`, curry result is `(Fn [Int] Int)`

The callee is NOT a `Var` naming a top-level function — it is a `Var` naming a let-bound closure. In the sketch, `pending_auto_curry` records are only pushed when callee is a `Var`, so this case IS handled. The backend sees `AutoCurry { target_name: "f" }` but `f` is a closure variable, not a named function. The codegen for auto-curry of a closure is: allocate a new env capturing the old env pointer plus the new args, produce a wrapper that unpacks and calls. This is entirely a backend concern.

**Important subtlety**: For let-bound closures, we still need to emit the `AutoCurry` resolution so the backend knows to generate a wrapper. But the `target_name` should be the variable name (for closures, this gets the code pointer from the env). The sketch handles this by always pushing to `pending_auto_curry` when callee is a Var, regardless of whether it names a top-level function or a local binding.

### Operator auto-curry: `(+ 1)`

`+` resolves via trait method dispatch to `Num.+`. The callee type after trait resolution is `(Fn [Int Int] Int)` (or polymorphic). The auto-curry path fires because unification of `(Fn [Int Int] Int)` with `(Fn [Int] ?ret)` fails. The result is `(Fn [Int] Int)`.

This works for concrete types. For unconstrained polymorphic operators, the monomorphisation interaction (Q3 above) applies. The initial A1 implementation may need to test this case specifically.

## Implementation Checklist

1. **Add `total_count` to `ResolvedCall::AutoCurry`** in `crates/cranelisp-types/src/check.rs`
2. **Add `pending_auto_curry` field** to `TypeChecker` in `crates/cranelisp-typecheck/src/checker.rs`
3. **Modify `infer_apply`** in `crates/cranelisp-typecheck/src/infer.rs` — add unification-failure fallback with auto-curry detection
4. **Add `resolve_auto_curry` method** — drain pending list into `method_resolutions`
5. **Call `resolve_auto_curry`** at the end of batch `check_program` and REPL per-input checking
6. **Include `pending_auto_curry` in `ReplSnapshot`** — snapshot/restore must save/restore this list for error recovery
7. **Un-ignore tests** in `tests/io.rs` — the 4 auto-curry tests (`auto_curry_two_param_partial_apply`, `auto_curry_three_param_partial_apply`, `auto_curry_higher_order_usage`, `auto_curry_repl`)
8. **Backend work** (owned by `/backend`): implement `compile_auto_curry` in codegen — allocate closure env, capture applied args, generate wrapper function

### Out of scope for A1

- Multi-sig auto-curry (requires multi-sig dispatch, not yet reimplemented)
- Constrained polymorphic auto-curry (requires monomorphisation integration)
- Auto-curry of constructors (e.g., `(Some)` is already a function value, not auto-curry)
