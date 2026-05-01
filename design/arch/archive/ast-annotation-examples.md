# AST Annotation Examples: Defining "Fully Annotated"

Sprint 55 Step 1b specification. These examples define what `/qa` tests must verify
and what `/typecheck` must produce on each AST node.

## 1. The Problem

Step 1b dual-writes annotations during `infer_expr` (line 77 of `infer.rs`):

```rust
expr.set_inferred_type(Some(Box::new(ty.clone())));
if let Expr::Apply { resolved_call, span, .. } = expr {
    if let Some(resolution) = state.method_resolutions.get(span) {
        *resolved_call = Some(Box::new(resolution.clone()));
    }
}
```

This captures the type and resolution **as they exist at `infer_expr` return**. But
four post-passes in `finalize_check_result_inner` modify the side maps after
inference completes:

| Post-pass | What it writes to side maps | Why the AST node may be stale |
|---|---|---|
| `resolve_deferred_trait_calls` | New `method_resolutions` entries for Apply nodes where the callee is a trait method but the types weren't concrete during inference | `resolved_call` on the Apply node is `None` |
| `resolve_pending_overloads` | `SigDispatch` entries for multi-sig call sites | `resolved_call` on the Apply node is `None` |
| `resolve_auto_curry` | `AutoCurry` entries for partial application sites | `resolved_call` on the Apply node is `None` |
| Final substitution sweep | Resolves `Var(N)` in `expr_types` via `apply(&state.subst, ty)` | `inferred_type` on the node still contains `Var(N)` |

Step 1c switches codegen to read from AST nodes. If these post-pass updates are not
propagated back to the AST nodes, codegen will read stale/incomplete annotations.

This document specifies **concrete examples** that exercise each post-pass, with
expected AST annotations. These become the acceptance tests for Step 1b.

## 2. Terminology

- **`inferred_type`**: The `Option<Box<Type>>` field on every `Expr` variant.
  "Fully annotated" means `Some(concrete_type)` with no `Var(N)` remaining.
- **`resolved_call`**: The `Option<Box<ResolvedCall>>` field on `Expr::Apply` only.
  "Fully annotated" means `Some(resolution)` for every Apply that codegen dispatches.
- **Concrete type**: A `Type` with no `Var(N)` — only `Int`, `Float`, `Bool`,
  `String`, `Fn(...)`, `ADT(...)`, `Vec(...)`, `Unit`.
- **Side map**: `CheckResult.method_resolutions` and `CheckResult.expr_types` —
  the existing `HashMap<Span, _>` paths.

## 3. Examples

### 3.1 Simple monomorphic function — trait method resolution

**Source**:
```clojure
(defn double [x] (+ x x))
(double 5)
```

**Post-passes exercised**: `resolve_deferred_trait_calls` (the `+` call), final
substitution sweep (resolving type vars after call site unification).

**Expected AST annotations on `double` body** (`(+ x x)`):

| Node | `inferred_type` | `resolved_call` | Notes |
|---|---|---|---|
| `Apply (+ x x)` | `Some(Int)` | `Some(TraitMethod { trait: Num, method: +, impl_type: Int, mangled: "Num.+$Int" })` | The `+` is a trait method; resolution deferred until arg types are known |
| `Var +` | `Some(Fn([Int, Int], Int))` | n/a (not Apply) | Callee type — must be concrete for heap classification |
| `Var x` (1st) | `Some(Int)` | n/a | Parameter type, resolved by call site unification |
| `Var x` (2nd) | `Some(Int)` | n/a | Same |

**What breaks if incomplete**:
- `resolved_call = None` on the Apply: codegen has no dispatch target for `+`.
  Falls through to generic function call, which emits an undefined JIT symbol
  `+` instead of `Num.+$Int`. Linker error or crash.
- `inferred_type = Var(N)` on `Var x`: heap classifier sees `Var(N)`, cannot
  determine if heap-allocated. May conservatively emit RC inc/dec on an integer,
  which corrupts the value (treating an integer as a heap pointer).

**Note on deferred resolution**: When `double` is checked in isolation (before any
call site), the body types contain `Var(N)`. The `+` call cannot resolve because
the impl type is unknown. `resolve_deferred_trait_calls` runs after generalization
and call-site unification have pinned the type variables.

For the *constrained polymorphic* case where types remain generic, see Example 3.2.

### 3.2 Constrained polymorphic function — monomorphisation

**Source**:
```clojure
(defn add [x y] (+ x y))
(add 1 2)
```

**Post-passes exercised**: `detect_constrained_fns` (identifies `add` as
constrained), `pass4_monomorphise` (creates `add$Int+Int`), final substitution.

**Expected AST annotations on the template body** (`add` before monomorphisation):

| Node | `inferred_type` | `resolved_call` | Notes |
|---|---|---|---|
| `Apply (+ x y)` | `Some(Var(N))` or `Some(Var(M))` | `None` | Template body: types are not concrete. **This is correct** — the template is never compiled directly. |
| `Var x` | `Some(Var(N))` | n/a | Unconstrained type var |
| `Var y` | `Some(Var(M))` | n/a | Unconstrained type var |

**Expected AST annotations on the monomorphised body** (`add$Int+Int`):

| Node | `inferred_type` | `resolved_call` | Notes |
|---|---|---|---|
| `Apply (+ x y)` | `Some(Int)` | `Some(TraitMethod { trait: Num, method: +, impl_type: Int, mangled: "Num.+$Int" })` | Fully resolved for the Int specialisation |
| `Var x` | `Some(Int)` | n/a | Concrete param type |
| `Var y` | `Some(Int)` | n/a | Concrete param type |

**What breaks if incomplete**:
- If the mono body inherits the template's unresolved `Var(N)` types: codegen
  cannot determine stack slot sizes, calling convention, or RC classification.
  Every downstream pass fails.
- If the mono body has concrete types but `resolved_call = None`: same failure
  as Example 3.1 — no dispatch target for `+`.

**Key invariant**: The template body (`add`) may have unresolved annotations.
Monomorphised copies (`add$Int+Int`) must be fully annotated. Codegen never
compiles the template — it compiles only the mono copies. Tests must verify the
mono copy, not the template.

### 3.3 Deferred trait resolution — type not known at Apply site

**Source**:
```clojure
(defn show-it [x] (show x))
(show-it 42)
```

**Post-passes exercised**: `resolve_deferred_trait_calls`. During inference of
`show-it`'s body, `x` has type `Var(N)`. The `show` call is a `Display.show`
trait method, but the impl type is unknown. The resolution is deferred.
After `(show-it 42)` unifies `Var(N) = Int`, the deferred resolution pass
fills in the trait method resolution.

This is similar to Example 3.1 but focuses specifically on the deferred
resolution mechanism. The distinction: in Example 3.1, `double` is called with
a literal so unification is straightforward. Here, `show-it` is a constrained
polymorphic function — the deferred call in its template body is resolved only
in the monomorphised copy `show-it$Int`.

**Expected AST annotations on the monomorphised body** (`show-it$Int`):

| Node | `inferred_type` | `resolved_call` | Notes |
|---|---|---|---|
| `Apply (show x)` | `Some(String)` | `Some(TraitMethod { trait: Display, method: show, impl_type: Int, mangled: "Display.show$Int" })` | Resolved during mono pass |
| `Var show` | `Some(Fn([Int], String))` | n/a | |
| `Var x` | `Some(Int)` | n/a | |

**What breaks if incomplete**:
- `resolved_call = None`: codegen emits a call to bare `show`, which is not a
  concrete JIT symbol. Linker error.
- The key failure mode is that `resolve_deferred_trait_calls` writes to
  `state.method_resolutions` (keyed by Span) but does NOT currently update the
  `Expr::Apply.resolved_call` field on the AST node. This is the primary gap
  that Step 1b must close.

### 3.4 Auto-curry — partial application

**Source**:
```clojure
(defn apply-add [x] (+ x))
```

**Post-passes exercised**: `resolve_auto_curry`. During inference, `(+ x)` has
one argument but `+` expects two. The typechecker detects the arity mismatch,
records a pending auto-curry entry, and returns a closure type `Fn([Int], Int)`.
The `resolve_auto_curry` post-pass creates the `AutoCurry` resolution.

**Expected AST annotations**:

| Node | `inferred_type` | `resolved_call` | Notes |
|---|---|---|---|
| `Apply (+ x)` | `Some(Fn([Int], Int))` | `Some(AutoCurry { target: +, applied: 1, total: 2, trait_resolution: Some(TraitMethod { trait: Num, method: +, impl_type: Int, ... }) })` | Auto-curry with resolved inner trait |
| `Var +` | `Some(Fn([Int, Int], Int))` | n/a | Full function type |
| `Var x` | `Some(Int)` | n/a | |

**What breaks if incomplete**:
- `resolved_call = None`: codegen falls through to regular function call with
  one argument. `+` expects two arguments. Either a segfault (reads garbage for
  second arg) or a type mismatch crash in the JIT.
- `resolved_call = Some(AutoCurry { ..., trait_resolution: None })`: codegen
  builds the curry closure but cannot resolve the inner `+` to `Num.+$Int`.
  The closure captures a reference to undefined symbol `+`.
- `inferred_type = None` on the Apply: codegen cannot determine the closure
  return type, cannot classify whether the result is heap-allocated (closures
  are always heap).

**Note on deferred trait resolution within auto-curry**: The `resolve_auto_curry`
post-pass attempts a secondary trait resolution (lines 2389-2401 in `program.rs`)
because the types may have been `Var(N)` when the curry was first detected but
are now concrete after unification. Both the `AutoCurry` resolution AND its
nested `trait_resolution` must be propagated to the AST node.

### 3.5 Multi-sig overload dispatch

**Source**:
```clojure
(defn foo
  ([x] (+ x 1))
  ([x y] (+ x y)))
(foo 10)
```

**Post-passes exercised**: `resolve_pending_overloads`. During inference of
`(foo 10)`, the typechecker finds `foo` in the overload registry. It records a
pending overload resolution (Span + base name + arg types + return type var).
The `resolve_pending_overloads` post-pass matches arg count and types to find
the correct variant, then inserts a `SigDispatch` resolution.

**Expected AST annotations on the call site** (`(foo 10)`):

| Node | `inferred_type` | `resolved_call` | Notes |
|---|---|---|---|
| `Apply (foo 10)` | `Some(Int)` | `Some(SigDispatch { mangled_name: "foo$Int" })` | Resolved to the 1-arg variant |
| `Var foo` | `Some(Fn([Int], Int))` | n/a | Resolved to variant type |
| `IntLit 10` | `Some(Int)` | n/a | |

**Expected AST annotations on variant bodies** (compiled as `foo__v0`, `foo__v1`):

| Variant | Body Apply | `resolved_call` |
|---|---|---|
| `foo__v0` (1-arg): `(+ x 1)` | `Some(TraitMethod { trait: Num, method: +, impl_type: Int, ... })` | Via `resolve_deferred_trait_calls` on internal defn |
| `foo__v1` (2-arg): `(+ x y)` | `Some(TraitMethod { trait: Num, method: +, impl_type: Int, ... })` | Same |

**What breaks if incomplete**:
- `resolved_call = None` on `(foo 10)`: codegen has no dispatch target. It tries
  to call bare `foo`, which is not a JIT symbol (only `foo$Int` and `foo$Int+Int`
  are). Linker error.
- `resolved_call` has wrong mangled name: codegen calls the wrong variant,
  passing one argument to a function expecting two. Stack corruption.

### 3.6 Self-recursive tail call — TCO detection

**Source**:
```clojure
(defn fact [n acc]
  (if (= n 0)
    acc
    (fact (- n 1) (* n acc))))
```

**Post-passes exercised**: `resolve_deferred_trait_calls` (for `=`, `-`, `*`),
final substitution sweep. TCO detection itself is a codegen concern, but it
depends on being able to identify the recursive Apply node.

**Expected AST annotations**:

| Node | `inferred_type` | `resolved_call` | Notes |
|---|---|---|---|
| `If` (outer) | `Some(Int)` | n/a | |
| `Apply (= n 0)` | `Some(Bool)` | `Some(TraitMethod { trait: Eq, method: =, impl_type: Int, ... })` | |
| `Var acc` (then) | `Some(Int)` | n/a | Tail position |
| `Apply (fact ...)` | `Some(Int)` | `None` | Regular function call — no trait dispatch, no overload, no curry. `fact` is a user fn, not a trait method. |
| `Apply (- n 1)` | `Some(Int)` | `Some(TraitMethod { trait: Num, method: -, impl_type: Int, ... })` | |
| `Apply (* n acc)` | `Some(Int)` | `Some(TraitMethod { trait: Num, method: *, impl_type: Int, ... })` | |

**TCO-relevant annotation**: The recursive `(fact ...)` Apply node has
`resolved_call = None` because it is a plain user function call — `fact` is
not a trait method, not an overload, and not a curry target. This is correct.
Codegen identifies self-recursion by checking `callee == current_fn_name`, not
via `resolved_call`.

**What breaks if `inferred_type` is incomplete**:
- `inferred_type = Var(N)` on the `If` node: codegen cannot determine the
  function's return type. The Cranelift function signature is wrong, producing
  ABI mismatches at the call site.
- `inferred_type = Var(N)` on `Var acc`: heap classifier treats an integer as
  potentially heap-allocated. Emits RC dec on an integer, corrupting the value.

**What breaks if `resolved_call` is incomplete on trait method Applys**:
- `resolved_call = None` on `(= n 0)`: codegen cannot dispatch the comparison.
  Falls through to undefined symbol `=`. Linker error.
- Same for `(- n 1)` and `(* n acc)`.

### 3.7 Let binding — expression types for heap classification

**Source**:
```clojure
(let [x (+ 1 2)] x)
```

**Post-passes exercised**: Final substitution sweep (ensuring `x` binding expr
type is concrete), `resolve_deferred_trait_calls` (the `+`).

**Expected AST annotations**:

| Node | `inferred_type` | `resolved_call` | Notes |
|---|---|---|---|
| `Let` (outer) | `Some(Int)` | n/a | Overall expression type |
| `Apply (+ 1 2)` | `Some(Int)` | `Some(TraitMethod { trait: Num, method: +, impl_type: Int, ... })` | Binding expression |
| `IntLit 1` | `Some(Int)` | n/a | |
| `IntLit 2` | `Some(Int)` | n/a | |
| `Var x` (body) | `Some(Int)` | n/a | References the binding |

**What breaks if incomplete**:
- `inferred_type = Var(N)` on the `Apply (+ 1 2)` node: heap classifier cannot
  determine whether `x` is heap-allocated. Two failure modes:
  - Conservative (assume heap): emits `rc_inc` on an integer. Treats the value `3`
    as a heap pointer, reads memory at address `3`. Segfault.
  - Optimistic (assume non-heap): if the binding expression returns a String
    (change `+` to `str-concat`), the string is never RC'd. Memory leak or
    use-after-free.
- `resolved_call = None` on `(+ 1 2)`: same as Example 3.1 — no dispatch target.

## 4. Propagation Requirements

Based on the examples above, Step 1b must ensure these invariants:

### 4.1 After `infer_expr` (current dual-write)

Already implemented: `set_inferred_type` is called on every node, and
`resolved_call` is set on Apply nodes from `state.method_resolutions`.

**Gap**: The type written is `ty.clone()` — the type as returned by the
per-variant inference method. For nodes where unification has not yet resolved
all type variables (common for function parameters that are unified later by
call sites), this type contains `Var(N)`.

### 4.2 After `resolve_deferred_trait_calls` (Phase 3 in finalize)

This pass walks the AST and inserts new `method_resolutions` entries for Apply
nodes where trait resolution was deferred. **It must also set
`Expr::Apply.resolved_call`** on the visited node. Currently it only writes to
the side map.

### 4.3 After `resolve_pending_overloads` (Pass 5 in finalize)

This pass inserts `SigDispatch` entries into `method_resolutions`. **It must
also set `Expr::Apply.resolved_call`** on the corresponding Apply node.
Currently it operates on `(Span, base_name, arg_types, ret_type_var)` tuples
without access to the AST — it needs either AST access or a reconciliation
pass.

### 4.4 After `resolve_auto_curry` (Pass 5 in finalize)

Same pattern: inserts `AutoCurry` entries into `method_resolutions`. **Must
propagate to the AST node.**

### 4.5 Final substitution sweep

Currently resolves `expr_types` via `apply(&state.subst, ty)`. **Must also
walk the AST and update `inferred_type` on every node** with the substitution-
resolved type. Without this, `inferred_type` contains stale `Var(N)` values.

### 4.6 Monomorphised copies

`pass4_monomorphise` creates copies of constrained function bodies with fresh
type variables, then re-checks them. The mono body goes through `infer_expr`
again, so it gets fresh `inferred_type` annotations. **Verify that the mono
body also gets post-pass treatment** (deferred trait resolution, final
substitution) — if mono bodies are checked in a sub-pipeline that skips
post-passes, their annotations will be incomplete.

## 5. Test Strategy

Each example maps to one or more test cases. Tests should:

1. Compile the source through the full pipeline (typecheck + finalize).
2. Extract the `Defn` from `ModuleEntry::Def.ast` (or from `MonoDefn.defn`
   for constrained polymorphic examples).
3. Walk the AST and verify `inferred_type` and `resolved_call` on specific
   nodes, matching the tables above.
4. Verify agreement with the side maps (dual-write assertion).

### Test naming convention

```
test_ast_annotation_{scenario}_{aspect}
```

Examples:
- `test_ast_annotation_simple_fn_resolved_call` (3.1)
- `test_ast_annotation_constrained_mono_types` (3.2)
- `test_ast_annotation_deferred_trait_resolution` (3.3)
- `test_ast_annotation_auto_curry_resolution` (3.4)
- `test_ast_annotation_multi_sig_dispatch` (3.5)
- `test_ast_annotation_self_recursive_all_resolved` (3.6)
- `test_ast_annotation_let_binding_concrete_type` (3.7)

### Spec traceability

These tests verify an internal invariant (AST annotation completeness), not a
language-spec requirement. They trace to `design/arch/pipeline-v4.md` Section 9.1
(target data model) and `design/arch/ast-annotation-examples.md` (this document).

```rust
// spec: design/arch/ast-annotation-examples.md §3.1 — simple fn resolved_call
#[test]
fn test_ast_annotation_simple_fn_resolved_call() { ... }
```

## 6. Summary of Gaps

| Gap | Which examples affected | Fix required |
|---|---|---|
| Post-passes write to side maps but not AST nodes | 3.1, 3.3, 3.4, 3.5 | Each post-pass must also update `Expr::Apply.resolved_call` |
| Final substitution not applied to AST `inferred_type` | 3.1, 3.2, 3.6, 3.7 | Walk AST after finalize, apply substitution to every `inferred_type` |
| `resolve_pending_overloads` has no AST access | 3.5 | Either pass `&mut [TopLevel]` or add reconciliation walk |
| `resolve_auto_curry` has no AST access | 3.4 | Same as above |
| Mono body post-pass coverage unverified | 3.2, 3.3 | Verify mono sub-pipeline includes deferred resolution + substitution |
