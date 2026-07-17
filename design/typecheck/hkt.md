# Higher-Kinded Types (HKT)

Solution design for higher-kinded type support in the Cranelisp typechecker. Covers trait declarations with constructor variables, TyConApp unification, HKT impl registration, dispatch, and the boundary with codegen.

Spec references: `spec/03-types.md` SS3.7, `spec/05-definitions.md` SS5.3.2 and SS5.4.4, `spec/07-traits.md` SS7.2.

## 1. Problem Statement

Cranelisp needs to support traits that abstract over type constructors (kind `* -> *`) rather than concrete types (kind `*`). The canonical example is `Functor`:

```clojure
(deftrait (Functor f)
  (fmap [(Fn [a] b) (f a)] (f b)))
```

Here `f` ranges over type constructors like `Option` and `List`, and `(f a)` means "apply the constructor `f` to type argument `a`".

### What is already in place

1. **`Type::TyConApp(TypeId, Vec<Type>)`** exists in `crates/cranelisp-types/src/types.rs` and is handled by all utility functions: `apply`, `free_vars`, `contains_var`, `max_type_var_id`, `collect_var_ids_ordered`, the shared `render_type(ty, PrimitiveNaming, VarNaming)` renderer, and `Display`.

2. **AST support**: `TraitDecl.type_params: Vec<Symbol>` carries the constructor variable names. `TraitMethodSig.hkt_param_index: Option<usize>` records which method parameter carries the constructor for dispatch. Both are already defined in `crates/cranelisp-types/src/ast.rs`.

3. **Tests**: Two ignored tests exist in `tests/ring2.rs`: `hkt_trait_declaration` and `hkt_impl_bare_constructor`. A third test (`hkt_functor_basic`) is referenced in the sprint plan but does not yet exist as a test function.

### What is missing

The typecheck crate (`crates/cranelisp-typecheck/`) has zero references to `TyConApp`. The following subsystems need HKT awareness:

- **Trait registration** (`traits.rs`): `register_trait_decl` must detect HKT traits and produce `TyConApp` in method schemes.
- **Unification** (`unify.rs`): needs `TyConApp` vs `ADT` and `TyConApp` vs `TyConApp` rules.
- **Impl registration** (`traits.rs`): `register_trait_impl` must handle bare constructor targets and validate arity.
- **Method resolution** (`traits.rs`): `try_resolve_trait_method` must use `hkt_param_index` for dispatch instead of always using the first argument.
- **Substitution for TyConApp** (`unify.rs`): `substitute_vars` must map constructor variable IDs through the instantiation mapping while preserving the `TyConApp` wrapper.

## 2. Sketch Comparison

The sketch has a working HKT implementation in `sketch/src/typechecker/traits.rs`, `sketch/src/typechecker/unification.rs`, and `sketch/src/typechecker/mono.rs`. The reimplementation follows the same overall approach with minor structural differences.

### How the sketch handles it

**Trait registration** (`register_hkt_trait`):
- Detects HKT via `!decl.type_params.is_empty()`.
- Allocates fresh `TypeId` for each constructor param (the "con_var_map").
- Calls `find_hkt_param_index` to scan method params for the first one using a constructor variable in `Applied` position. Stores result in `method.hkt_param_index`.
- Resolves method signatures via `resolve_type_expr_hkt`, which produces `TyConApp(con_id, args)` for constructor variable applications and regular `ADT`/`Var` for everything else.
- Registers each method with a `Scheme` whose `constraints` map includes the constructor variable IDs.

**Unification** (`unify`):
- `TyConApp(f, args1)` vs `ADT(name, args2)`: binds `f -> ADT(name, [])` (the bare constructor), then unifies args pairwise. Requires `args1.len() == args2.len()`.
- `TyConApp(f1, args1)` vs `TyConApp(f2, args2)`: binds `f1 -> Var(f2)`, then unifies args pairwise.
- Occurs check: `TyConApp(con_id, args)` reports occurrence if `id == con_id` or `id` occurs in any arg.

**Impl validation** (`validate_impl`):
- If the trait has `type_params`, computes expected arity via `con_var_arity` (scans method signatures for `Applied` uses of the constructor name).
- Validates the impl target's type parameter count matches the expected arity.
- Rejects primitives as HKT impl targets.

**Method resolution** (`hkt_param_idx_for_method`):
- Walks all module `TraitDecl` entries to find a method's `hkt_param_index`.
- `infer_apply` uses this index instead of 0 to pick the dispatch argument.

**Mono** (`collect_var_mapping`, `apply_with`):
- `TyConApp(id, sa)` vs `ADT(_, ca)`: maps the constructor ID to the full concrete ADT.
- `apply_with` on `TyConApp(id, args)`: looks up the mapping; if found, reconstructs as `ADT(name, resolved_args)`.

### Divergences from the sketch

| Aspect | Sketch | Reimplementation |
|---|---|---|
| Registration path | `register_hkt_trait` is a separate method called from `register_trait` | Same approach -- separate method is cleanest |
| Type expression resolver | `resolve_type_expr_hkt` is a distinct method from the normal `resolve_type_expr` | Same -- HKT context needs con_var_map parameter |
| hkt_param_index storage | Mutates the `TraitDecl` in `CompiledModule` after initial insertion | Same -- set during registration, stored on `TraitMethodSig` |
| Unification borrow splitting | Sketch uses `&mut self` on TypeChecker | Reimplementation uses free-function `unify(&mut Subst, ...)` -- extend this function |
| Substitution | Sketch's `substitute_vars` handles `TyConApp` ID remapping | Reimplementation's `apply` already handles TyConApp args but does NOT remap the constructor ID -- this must be added |

**Rationale for following the sketch**: The sketch's approach is clean and well-tested. The key insight -- that `TyConApp` binds its constructor variable to a bare `ADT(name, [])` during unification -- is sound and simple. No reason to diverge on the algorithm.

## 3. Unification Rules for TyConApp

Three new match arms in `unify()` (`crates/cranelisp-typecheck/src/unify.rs`):

### 3.1 TyConApp vs ADT

```
TyConApp(f_id, [A1, ..., An])  ~  ADT(name, [B1, ..., Bn])
```

1. Check `n == m` (arity match).
2. Bind `f_id -> ADT(name, [])` (the bare constructor).
3. For each `i`, unify `Ai` with `Bi`.

This works symmetrically: `ADT` on left and `TyConApp` on right uses the same logic.

```rust
(Type::TyConApp(f_id, args1), Type::ADT(name, args2))
| (Type::ADT(name, args2), Type::TyConApp(f_id, args1)) => {
    if args1.len() != args2.len() {
        return Err(/* arity mismatch */);
    }
    // Bind constructor variable to bare ADT constructor
    bind_var(subst, *f_id, &Type::ADT(name.clone(), vec![]))?;
    for (a1, a2) in args1.iter().zip(args2.iter()) {
        unify(subst, a1, a2)?;
    }
    Ok(())
}
```

### 3.2 TyConApp vs TyConApp

```
TyConApp(f1, [A1, ..., An])  ~  TyConApp(f2, [B1, ..., Bn])
```

1. Check arity match.
2. If `f1 != f2`, bind `f1 -> Var(f2)`.
3. Unify args pairwise.

```rust
(Type::TyConApp(f1, args1), Type::TyConApp(f2, args2)) => {
    if args1.len() != args2.len() {
        return Err(/* arity mismatch */);
    }
    if f1 != f2 {
        bind_var(subst, *f1, &Type::Var(*f2))?;
    }
    for (a1, a2) in args1.iter().zip(args2.iter()) {
        unify(subst, a1, a2)?;
    }
    Ok(())
}
```

### 3.3 Occurs check

The existing `occurs_check` uses `free_vars`, which already collects `TyConApp` arg vars. However, the constructor ID itself (`TyConApp(id, _)`) must also be treated as a variable for occurs-check purposes. Verify that `free_vars` includes TyConApp's constructor ID.

Looking at the current `free_vars` implementation: it collects vars from `TyConApp(_, args)` args but does NOT include the constructor ID itself. This is correct because `free_vars` collects `Var` occurrences, and the constructor ID is not a `Var` -- it is bound separately via `bind_var`. The occurs check in `bind_var` calls `free_vars` on the resolved type, which will detect if `id` appears as a `Var(id)` anywhere. Since TyConApp's constructor ID is bound via `bind_var(subst, f_id, ...)`, the standard occurs check works: if the target type contains `Var(f_id)`, the binding would be circular.

However, there is a subtle case: if `f_id` appears as the constructor ID in a nested `TyConApp(f_id, ...)` inside the type being bound. The current `free_vars` does not catch this. We need to either:

1. Add the constructor ID to `free_vars` for `TyConApp`, or
2. Add a separate `occurs_in_tycon` check.

**Decision**: Follow the sketch -- the sketch's `occurs` function explicitly checks `id == *con_id` for `TyConApp(con_id, args)`. We should add TyConApp constructor ID awareness to occurs checking. The cleanest approach: modify `occurs_check` in `unify.rs` to use a custom recursive check rather than `free_vars`, matching the sketch's dedicated `occurs` function.

## 4. HKT Trait Declaration Handling

When `register_trait_decl` is called with a `TraitDecl` where `type_params` is non-empty, the HKT path activates.

### 4.1 Detection

```rust
if !decl.type_params.is_empty() {
    return self.register_hkt_trait(decl);
}
```

### 4.2 Constructor variable allocation

For each name in `decl.type_params`, allocate a fresh `TypeId`. Store in a `con_var_map: HashMap<Symbol, TypeId>`.

### 4.3 HKT param index computation

For each method, scan its parameter `TypeExpr` list for the first parameter that uses a constructor variable in `TypeExpr::Applied` position. Store the index in `method.hkt_param_index`.

Algorithm (`find_hkt_param_index`):
1. For each param at index `i`, recursively check if it contains `TypeExpr::Applied(name, _)` where `name` is in `decl.type_params`.
2. Return the first such `i`.
3. Fallback: 0 (should not happen for well-formed HKT traits).

### 4.4 Type expression resolution in HKT context

A separate method `resolve_type_expr_hkt` takes the `con_var_map` and a mutable `type_var_map` (for regular type vars). It mirrors the normal `resolve_type_expr` but produces `TyConApp` for constructor applications:

| TypeExpr | Normal resolution | HKT resolution |
|---|---|---|
| `Applied("f", [a])` where `f` in con_var_map | N/A | `TyConApp(f_id, [resolve(a)])` |
| `Applied("Option", [a])` | `ADT("Option", [resolve(a)])` | Same |
| `TypeVar("a")` not in con_var_map | `Var(fresh)` | Same |
| `TypeVar("f")` in con_var_map | N/A | `Var(f_id)` (bare constructor ref -- unusual) |
| `SelfType` | `Var(type_var_id)` | Error (HKT traits do not use `self`) |
| `Named("Int")` | `Type::Int` | Same |
| `FnType(ps, r)` | `Fn(ps', r')` | `Fn(resolve_hkt(ps), resolve_hkt(r))` |

### 4.5 Method scheme construction

Each method gets a `Scheme` with:
- `vars`: all constructor var IDs + all regular type var IDs (sorted, deduped)
- `constraints`: constructor var IDs mapped to `[trait_name]`
- `ty`: `Type::Fn(param_tys, ret_ty)` where param/ret types contain `TyConApp` nodes

Example for `fmap`:
```
Scheme {
    vars: [f_id, a_id, b_id],
    constraints: { f_id: ["Functor"] },
    ty: Fn(
        [Fn([Var(a_id)], Var(b_id)), TyConApp(f_id, [Var(a_id)])],
        TyConApp(f_id, [Var(b_id)])
    )
}
```

### 4.6 Storing hkt_param_index

After computing `hkt_param_index` for each method, update the `TraitDecl` stored in `CompiledModule` so downstream consumers (method resolution, backend) can access it.

## 5. HKT Trait Implementation Handling

### 5.1 Impl target validation

When `register_trait_impl` processes an impl for an HKT trait:

1. **Detect HKT trait**: Look up the trait declaration. **HKT-ness comes from the DECLARATION
   FORM, not from method-body usage**: a trait declared `(Name var …)` (parenthesized head with
   a type parameter) makes `var` a type-constructor variable of kind `* -> *` — higher-kinded —
   **regardless of whether any method uses `var` applied (`(f a)`) or bare (`:a`)**. So
   `decl.type_params` non-empty ⟺ HKT (grammar §7 L12; a `*`-kind return-poly trait uses the
   bare head `Name` + `self` and carries NO type_params — spec §7.1.1). See §5.4 for the 0628
   correction to a former usage-derived gate.

2. **Compute expected arity**: Scan method signatures for the first `Applied` use of each
   constructor variable name (`con_var_arity`). The number of args in that `Applied` node is the
   expected arity. **A con_var used only BARE (`:a`, never `(f a)`) yields no applied use, so
   `con_var_arity` returns `None` — but the declaration still asserts kind `* -> *` (arity ≥ 1).**
   The arity is used only to check a *matching-arity ADT* target; it is NOT needed to reject a
   *non-constructor* (primitive) target (§5.4).

3. **Validate target arity**: Look up the impl target type (e.g., `Option`). If it's a known ADT,
   check that its `type_params.len()` matches the expected arity (when known). **If the target is
   not a type constructor at all — a primitive scalar (`Int`/`Bool`/`String`/`Float`) or a
   nullary/0-param type — reject with "not a type constructor", INDEPENDENT of the exact expected
   arity** (a scalar can never satisfy a `* -> *` con_var). This rejection is the §7.2 gate and
   MUST fire for every con_var-use shape (applied and bare — §5.4).

4. **Register impl**: Store in `ImplRegistry` under the bare constructor name (e.g., `"Option"`, not `"(Option a)"`).

### 5.4 The bare-con_var impl-on-primitive leak (FIXME 0628, S111)

**Defect.** An HKT trait implemented on a **primitive** is silently accepted, then leaks an
opaque backend `undefined function` at first use, when the constructor var appears **bare**
(`:a`) in a method type rather than **applied** (`(f a)`) — violating the self-documenting-REPL
principle (an ill-formed program must be rejected check-side with an actionable message, not a
codegen leak). Repro:

```
(deftrait (Zeroable a) (zed [] :a))   ; (Name var) ⇒ higher-kinded; `a` : *->*
(impl Zeroable Int (defn zed [] 0))   ; MUST reject "Int is not a type constructor"; today ACCEPTED
:Int (zed)                            ; today → codegen error: undefined function: zed
```

A sibling type-display defect: `(deftrait (Container a) (unwrap [:a x] :a))` + `(impl Container
Int …)` is accepted and `(unwrap 7)` prints `:a 7` instead of `:primitives/Int 7`. One root, two
symptoms.

**Root cause (source-verified).** The impl-target validation gate (`traits/impl_check.rs:39–92`)
derives HKT-ness from **method-body usage**, not the declaration:

```rust
let is_hkt = decl.methods.iter().any(|m|
    m.params.iter().any(|(_, p)| type_expr_uses_con_var(p, &decl.type_params))
        || type_expr_uses_con_var(&m.ret_type, &decl.type_params));
```

and `type_expr_uses_con_var` / `con_var_arity` / `find_applied_arity`
(`traits/type_resolve.rs:165–226`) match ONLY `TypeExpr::Applied` (recursing into `FnType`),
with a `_ => false` / `_ => None` arm — so a **bare** con_var (a `TypeVar`/`Named` leaf) is
invisible to all three. Consequence for `(Zeroable a)` with `(zed [] :a)`: `is_hkt = false` ⇒
the whole con_var loop (incl. the primitive rejection) is skipped; and even if reached,
`con_var_arity` returns `None` and `if expected_arity > 0` (`:50`) gates the primitive-reject out.

**The fix — the HKT gate is the declaration; the primitive-reject is arity-independent.**

1. **HKT-ness from the declaration.** The outer guard `if !decl.type_params.is_empty()` (`:39`)
   IS the correct HKT condition; the inner usage-derived `is_hkt` is exactly the buggy narrowing
   — **remove it and run the con_var validation for every trait with type parameters**. (Confirm
   the premise "`(Name var)` ⇒ HKT" against spec §7.1.1 / grammar §7 L12 — the FIXME grounds it
   there; if a future non-HKT parametric-trait form is ever added, this gate revisits. No `/spec`
   change is requested; the premise is asserted, cited, and the "Not this" `self`-spelled *-kind
   case confirms *-kind traits carry no type_params.)

2. **Reject any non-type-constructor target, arity-independent.** For an HKT trait, resolve the
   impl target once (through the scope — the `:71` `scope_resolve` + `type_def_view_of` already
   present, prelude-fallback-aware) and reject when it is **not a type constructor**: a primitive
   scalar, OR a resolved type with 0 `type_params`. This subsumes and hardens the hardcoded
   `"Int"|"Bool"|"String"|"Float"` list (a Principle-19 module-by-name smell) into a structural
   "is this a `* -> *`-kinded constructor?" check, and it fires for bare-con_var traits because
   it no longer depends on `expected_arity > 0`. The matching-arity ADT check (`:76`,
   `td.type_params.len() != expected_arity`) stays as the additional precision for applied
   con_vars where `con_var_arity` is `Some`.

**Target diagnostic** (ideal, per the FIXME): name the higher-kinded trait and point at `self`
for `*`-kind intent — e.g. *"`Int` is not a type constructor; trait `Zeroable` is higher-kinded
(kind `* -> *`). For a trait whose method returns the implementing type, declare it `*`-kind:
`(deftrait Zeroable (zed [] self))`."* Minimal acceptable: the existing "not a type constructor
(trait `T` expects arity `n`)" message, made reachable for the bare shape.

**Coverage (routed `/qa`, FIXME 0628 / SPRINT.md §5).** The §7.2 rejection needs a
**con_var-use × impl-target matrix**: {applied `:(f a)`, bare-ret `:a`, bare-arg `:a`} ×
{primitive target, arity-mismatched ADT, well-kinded ADT}. `tests/spec_07_traits.rs::
hkt_impl_on_primitive_type_is_rejected_neg` covers only the applied×primitive cell (GREEN); the
bare rows are the hole. Repro class: `check-gate-leak` (a source fault typecheck must decide,
that today leaks past the check boundary as a backend codegen error — sibling of S108 0571 D1).

**Scope.** Typecheck-only (`traits/impl_check.rs` gate + optionally the `type_expr_uses_con_var`
family if a reviewer prefers the detector-level fix; the gate-level fix above is sufficient and
narrower). No `cranelisp-types` edit, no schema bump — rides the typecheck adjacent-carries
track (SPRINT.md §5), serial after the centrepiece.

### 5.2 Self-type construction for HKT impls

For non-HKT impls, the self-type for method checking is either `Type::Int` (primitives) or `Type::ADT("Option", [Var(a)])` (parameterized). For HKT impls, the self-type used during method body inference must be the fully applied form.

Given `(impl Functor Option ...)`:
- The constructor is `Option` with 1 type param.
- The self-type for checking `fmap`'s body is `ADT("Option", [Var(fresh_a)])`.
- The `Var(fresh_a)` corresponds to the constructor's applied arg.

During impl method type checking:
- The trait's constructor variable `f` should be pre-unified with `ADT("Option", [])` (the bare constructor).
- When the method's parameter type `TyConApp(f, [Var(a)])` is applied with this substitution, it becomes `ADT("Option", [Var(a)])` -- the concrete applied type.

### 5.3 Pre-unification of dispatch parameter

For the dispatch parameter (identified by `hkt_param_index`), pre-unify the method param type with the concrete self-type. This is how the sketch does it:

```rust
let param_idx = self.hkt_param_idx_for_method(&defn.name);
if let Some(target_param) = param_tys.get(param_idx) {
    self.unify(target_param, self_type, defn.span)?;
}
```

This triggers the TyConApp-vs-ADT unification rule, binding the constructor variable to the bare ADT constructor and the inner type vars to fresh vars.

## 6. Method Resolution for HKT

### 6.1 Dispatch parameter selection

Currently `try_resolve_trait_method` always uses `arg_types[0]` for dispatch. For HKT methods, it must use the argument at `hkt_param_index`.

Change:
```rust
// Before: always first arg
let dispatch_arg = arg_types.first();

// After: use hkt_param_index if available
let param_idx = self.hkt_param_idx_for_method(callee_name);
let dispatch_arg = arg_types.get(param_idx);
```

### 6.2 Extracting the constructor name

Given the dispatch argument type (after substitution), extract the ADT name:
- `ADT("Option", [...])` -> `"Option"` (bare constructor name)
- `Var(_)` -> defer (type not yet resolved)
- `TyConApp(_, _)` -> should not happen at resolution time (means constructor variable was not yet resolved)

The existing `concrete_type_name` function handles `ADT` already, which is all that's needed -- by the time `try_resolve_trait_method` runs, the dispatch arg should be a concrete ADT, not a TyConApp.

### 6.3 Mangling

HKT method mangled names use the bare constructor: `Functor.fmap$Option`, not `Functor.fmap$Option$Int`. This is per spec SS7.4.1.

### 6.4 hkt_param_idx_for_method

A helper that walks trait declarations in all modules to find a method's `hkt_param_index`. Must handle mangled names: `"Functor.fmap$Option"` -> extract base `"fmap"` -> look up.

```rust
pub(crate) fn hkt_param_idx_for_method(&self, name: &str) -> usize {
    // Direct lookup
    if let Some(idx) = self.find_hkt_param_index_in_modules(name) {
        return idx;
    }
    // Mangled: "Trait.method$Type" -> "method"
    if let Some(dollar_pos) = name.find('$') {
        let prefix = &name[..dollar_pos];
        let base = prefix.rfind('.').map_or(prefix, |dot| &prefix[dot + 1..]);
        if let Some(idx) = self.find_hkt_param_index_in_modules(base) {
            return idx;
        }
    }
    0 // default: first param (normal traits)
}
```

## 7. Monomorphisation Interaction

Per spec SS3.7.6: **HKT methods are NOT constrained polymorphic functions**. They dispatch through the trait resolution mechanism, not through monomorphisation. At every call site, the concrete type constructor is known.

This means:
- `fmap` should NOT be registered as a constrained function in `detect_constrained_fns`.
- Resolution of `(fmap inc (Some 5))` goes through `try_resolve_trait_method`, which finds the impl for `Option` and returns `Functor.fmap$Option`.
- The backend compiles `Functor.fmap$Option` as a regular function -- no specialisation needed.

**However**, the monomorphisation module (`mono.rs`) does need TyConApp awareness in its `collect_var_mapping` and `apply_with` helpers. These are used for polymorphic ADT trait impls (e.g., `impl Display (Option :Display a)`) which can co-exist with HKT. The sketch's approach:
- `collect_var_mapping(TyConApp(id, sa), ADT(_, ca))`: maps `id` to the full concrete ADT.
- `apply_with(TyConApp(id, args))`: looks up the ID in the local mapping; if found as `ADT(name, _)`, reconstructs as `ADT(name, resolved_args)`.

The reimplementation should add these cases to the mono module when it exists.

## 8. Invariants

1. **TyConApp is inference-only**: By the time `CheckResult` is returned to codegen, ALL `TyConApp` nodes must be resolved to concrete `ADT` types. The backend never sees `TyConApp`. This is enforced by `Type::contains_var()` assertions (which already handle TyConApp args) and should also check that no `TyConApp` nodes remain as a separate assertion.

2. **Constructor IDs are type variable IDs**: A `TyConApp(f_id, ...)` uses the same `TypeId` namespace as `Var(id)`. The constructor ID is bound in the substitution just like any type variable. The key difference is what it binds TO: a bare `ADT(name, [])` rather than a fully applied type.

3. **Arity is implicit**: There is no kind system. Arity is determined by usage in method signatures and validated at impl registration time. A constructor variable used as `(f a)` has arity 1; as `(f a b)`, arity 2.

4. **hkt_param_index is set once**: Computed during trait registration and stored on `TraitMethodSig`. All downstream consumers read this field rather than recomputing.

5. **No default methods on HKT traits**: Per spec SS7.1.3, this is checked at parse time (frontend responsibility, not typecheck).

6. **HKT methods use trait dispatch, not monomorphisation**: The `Functor` constraint on `f` is resolved via `ImplRegistry`, not via `ConstrainedFn` machinery.

## 9. Edge Cases

### 9.1 Nullary constructors as HKT targets

Enum types like `(deftype Color Red Green Blue)` have 0 type parameters. They are valid types but invalid HKT impl targets because Functor expects arity 1. The arity validation in SS5.1 catches this.

### 9.2 Multiple constructor variables

The spec supports single-constructor HKT only (SS7.12.1: "No multi-parameter type classes"). `decl.type_params` will have at most one element for now. The implementation should handle `Vec<Symbol>` generically for future extension but can assume length 1 for Sprint 24.

### 9.3 Nested TyConApp

A type like `TyConApp(f, [TyConApp(g, [Var(a)])])` would represent `(f (g a))` -- a doubly-nested constructor application. This does not arise from single-parameter HKT traits but the unification rules handle it correctly (recursive unification resolves inner TyConApp first).

### 9.4 Constructor variable in non-Applied position

If a method signature uses the constructor variable name as a bare `TypeVar` (not in `Applied` position), e.g., `(deftrait (Bad f) (m [f] f))`, this treats `f` as a regular type variable. The `resolve_type_expr_hkt` method produces `Var(f_id)` for this case. This is arguably a spec violation (constructor variables should appear in applied position) but the sketch allows it silently. We follow the sketch for now.

### 9.5 REPL incremental compilation

HKT trait registration in the REPL follows the same path as batch. The `hkt_param_index` is stored on the `TraitDecl` in `CompiledModule`, which persists across REPL evaluations. Method resolution uses the stored index. No special REPL handling needed.

## 10. Changes Required

### 10.1 `crates/cranelisp-typecheck/src/unify.rs`

- Add two match arms to `unify`: TyConApp-vs-ADT and TyConApp-vs-TyConApp (see SS3).
- Add TyConApp constructor ID awareness to occurs checking (either modify `occurs_check` to use a direct recursive function, or extend `free_vars` in the types crate).

### 10.2 `crates/cranelisp-typecheck/src/traits.rs`

- Add `register_hkt_trait` method (called from `register_trait_decl` when `type_params` is non-empty).
- Add `resolve_type_expr_hkt` method.
- Add `find_hkt_param_index`, `type_expr_uses_con_var`, `con_var_arity`, `find_applied_arity` helpers.
- Add `hkt_param_idx_for_method` and `find_hkt_param_index_in_modules` helpers.
- Modify `try_resolve_trait_method` to use `hkt_param_idx_for_method` for dispatch parameter selection.
- Modify `register_trait_impl` to validate arity for HKT traits and reject primitive targets.

### 10.3 `crates/cranelisp-typecheck/src/checker.rs`

- Add `instantiate_constrained` awareness: when instantiating an HKT method scheme, the constructor variable ID must be remapped in TyConApp nodes, not just in Var nodes. Currently `apply` in the types crate handles TyConApp args but does NOT remap the constructor ID. Either:
  - (a) Extend `apply` to check if a TyConApp's constructor ID is in the substitution and, if so, restructure the type, OR
  - (b) Add a separate `substitute_tycon_vars` pass after instantiation.

  **Decision**: Option (a) -- extend `apply` in `crates/cranelisp-types/src/types.rs`. When `apply` encounters `TyConApp(id, args)` and `subst[id]` exists:
  - If `subst[id] = ADT(name, [])`: return `ADT(name, applied_args)`.
  - If `subst[id] = Var(other_id)`: return `TyConApp(other_id, applied_args)`.
  - Otherwise: return `TyConApp(id, applied_args)` (no remapping).

  This is the most impactful change because it makes TyConApp resolution automatic via the standard substitution mechanism.

### 10.4 `crates/cranelisp-types/src/types.rs`

- Modify `apply` to remap TyConApp constructor IDs through the substitution (see SS10.3).
- Verify `free_vars` behavior for TyConApp constructor IDs. Currently it does NOT include the constructor ID. For occurs-check correctness when using `bind_var`, the constructor ID must be treated as a free variable. Add it to `collect_free_vars`.

### 10.5 No backend changes

TyConApp is fully resolved before codegen. The backend never sees it. No changes to `crates/cranelisp-codegen/`.

## 11. Implementation Order

1. **types.rs**: Extend `apply` to remap TyConApp constructor IDs. Add constructor ID to `free_vars`.
2. **unify.rs**: Add TyConApp unification rules. Add TyConApp-aware occurs check.
3. **traits.rs**: Add `register_hkt_trait` and all supporting helpers.
4. **traits.rs**: Modify `try_resolve_trait_method` to use `hkt_param_idx_for_method`.
5. **traits.rs**: Modify `register_trait_impl` for HKT arity validation.
6. **End-to-end test**: Un-ignore `hkt_trait_declaration` and `hkt_impl_bare_constructor`. Write `hkt_functor_basic`.

## Next skills

- `/qa` -- write `hkt_functor_basic` test; un-ignore the two existing HKT tests once implementation lands.
- `/arch` -- review this design doc for architectural coherence (especially the `apply` change in types.rs, which is a cross-crate change).
