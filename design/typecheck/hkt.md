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

> **S112 SETTLED-MODEL RECONCILIATION (leg b, FIXMEs 0628+0639; /arch A2).** §5.1
> and §5.4 below are rewritten to the S111-settled spec (`spec/07-traits.md`
> §7.1.1/§7.2.1/§7.3.4–§7.3.6, commits `c9f05b64`/`b37d77e6`). Two model changes
> supersede the prior text: (1) **kind is derived ONCE at declaration
> registration**, and a parenthesized head whose con_var is **never applied** is
> **rejected at `deftrait` as malformed** (§7.2.1) — it is *not* "still kind
> `* -> *`" as the old §5.1 claimed; (2) the **impl form** echoes the declared head
> in slot 1 and names a **trait-constructor pairing** `(Trait Constructor)` in slot 2
> (§7.3.4), and the kind-check is the ONE §7.3.5 Case-3 seam — no second "is this a
> trait or a type-constructor?" classifier. The former "reject the bare-con_var
> impl-on-primitive at impl time" framing (old §5.4) is superseded: that shape is now
> a *declaration*-time reject.

### 5.1 Kind derivation at declaration; consumers read `type_params`

**Kind is a property of the DECLARATION, derived ONCE at trait registration, and
recorded on `TraitDeclInfo.type_params`.** Three declaration shapes, three kinds
(spec §7.1/§7.2.1):

| `deftrait` head | con_var applied `(f a)` anywhere? | kind | `type_params` |
|---|---|---|---|
| bare `Name` (+ `self`) | — (no con_var) | `*` (conventional) | **empty** |
| `(Name f)`, `f` applied ≥ once | yes | `* -> *` (higher-kinded) | `["f"]` |
| `(Name f)`, `f` never applied | no | **malformed — rejected at `deftrait`** | (never registers) |

1. **The malformed case is rejected at DECLARATION time, not at impl.** A
   parenthesized head whose con_var is never applied in any method signature
   (`(deftrait (Zeroable a) (zed [] :a))`, `a` bare-only) is malformed per §7.2.1
   ("A parenthesized head whose variable is never applied is malformed … there is
   no kind-`*` trait with a head type variable; conventional traits use the bare
   head and `self`"). `register_trait_decl` MUST reject it with a diagnostic that
   names the fix — *"trait `Zeroable`'s type parameter `a` is never applied
   `(a …)`; a trait that returns the implementing type uses the bare head and
   `self`: `(deftrait Zeroable (zed [] self))`."* This subsumes the old §5.4
   "bare-con_var impl-on-primitive leak": the `(impl Zeroable Int)` question never
   arises because the *declaration* is already rejected.

2. **`type_params` non-empty ⟺ HKT is then EXACT.** Because the malformed
   never-applied case is rejected at declaration, any trait that successfully
   registers with non-empty `type_params` is genuinely higher-kinded. Every
   downstream consumer (impl-target validation §5.4, dispatch §6, the REPL
   trait-classification display) reads `TraitDeclInfo.type_params` — non-empty ⟺
   HKT — and **never re-scans method-body usage** (Principle 24 "Resolve once":
   the two divergent usage-derived kind derivations at `registry.rs:117–126` and
   `impl_check.rs:39–92` collapse onto this single declaration-time fact).

3. **`register_trait_decl` guard fix (roots the `:a 7` display defect, FIXME 0628
   body).** The current guard (`registry.rs:117–124`) routes to `register_hkt_trait`
   only when `!type_params.is_empty()` **AND** a method uses the con_var applied —
   the usage scan. A bare-con_var trait therefore registered via the *regular*
   `register_trait_method` path, so `(unwrap 7)` displayed `:a 7` instead of
   `:primitives/Int 7`. Fix: drop the usage scan; register via `register_hkt_trait`
   whenever `!decl.type_params.is_empty()` — matching the (now sole) declaration-
   derived kind. The declaration-time malformed reject (step 1) runs first, so
   `register_hkt_trait` only ever sees a genuinely-HKT (applied-con_var) decl.

4. **Expected constructor arity** is the con_var's usage-derived arity (§7.2.1):
   the number of args in its first `Applied` occurrence (`con_var_arity`). For a
   genuinely-HKT trait this is always `Some(n≥1)` (step 1 guarantees at least one
   applied use). It is used to kind-check a matching-arity ADT target (§5.4 Case 2).

### 5.4 The settled impl form + the §7.3.5 Case-3 kind-check seam (leg b)

The impl form and its kind-check are settled (spec §7.3–§7.3.6). `register_trait_impl`
consumes the new frontend carrier and interprets slot 2 at **one** seam.

**The impl form (spec §7.3, §7.3.4).** `(impl impl_head impl_target method_def+)`:

- **Conventional trait** — slot 1 is the bare trait name (as declared, §7.1); slot 2
  is a **type**: `(impl Display Int …)`, `(impl Display (Option Int) …)`,
  `(impl Display (Option :Display a) …)`.
- **Higher-kinded trait** — slot 1 **echoes the parenthesized head verbatim**
  `(Functor f)`; slot 2 is a **trait-constructor pairing** `(Functor Option)` — the
  trait applied to the constructor it is implemented *about*:
  `(impl (Functor f) (Functor Option) …)`.

**Frontend carrier (/arch A1 pinned diff, landed b0).** The b0 `parse_impl` change
admits the echoed head at slot 1 and records the written head shape on
`TraitImpl.head_con_var: Option<Symbol>` (`#[serde(default)]`): `Some("f")` for an
HK head `(Functor f)`, `None` for a bare conventional head. Slot 2 continues to ride
the existing `target: TypeExpr` — for the HK case it parses as
`Applied("Functor", [Named("Option")])` (the pairing), kind-interpreted here at the
ONE §7.3.5 Case-3 seam. **No second classifier.**

**The Case-3 seam (spec §7.3.5) — one deterministic path in `register_trait_impl`:**

1. **Resolve the trait by name** from slot 1 (`impl_.trait_name.name`) — the existing
   `resolve_trait_decl` scope-resolve, prelude-fallback-aware (`impl_check.rs:30`).
2. **The trait's DECLARATION is authoritative on its kind** — read
   `TraitDeclInfo.type_params`: non-empty ⟺ HK (§5.1); this is the sole kind source.
3. **Slot-1 echo validation — shape AND con_var spelling.** Slot 1 MUST echo the
   declared head **verbatim** (§7.3, "Slot 1 is fixed, not inferable": for a higher-
   kinded impl slot 1 "reproduces the `deftrait` head **verbatim as declared** — the
   same constructor-variable spelling `(Functor f)`; it is neither renamed nor
   omitted"). This is **two** bits, and BOTH are validated **here** against the
   declaration read at step 2 — checking only the shape bit is a fidelity gap, because
   a parenthesized head with the *wrong* con_var spelling still carries `Some(_)`:
   - **Shape.** An HK trait requires `head_con_var: Some(_)` (a parenthesized echoed
     head); a conventional trait requires `head_con_var: None` (a bare name). A shape
     mismatch is rejected — *"trait `Functor` is higher-kinded; its impl head must echo
     the declared form `(Functor f)`"* / *"trait `Display` is a conventional (kind-`*`)
     trait; its impl head is the bare name `Display`."*
   - **Spelling (HK only).** When the trait is HK and the shape bit passes, the symbol
     inside `head_con_var: Some(name)` MUST equal the declaration's con_var —
     `TraitDeclInfo.type_params[0]` (§9.2: a single con_var). `(impl (Functor g) …)`
     against `(deftrait (Functor f) …)` passes the shape check (`Some(_)`) but its
     spelling `g` ≠ the declared `f`, so it is rejected **here** with a **located**
     diagnostic (on the impl form's slot 1 — the same span the shape-mismatch diagnostic
     uses) that names **both** spellings and the expected form — *"impl head `(Functor g)`
     does not echo trait `Functor`'s declared head `(Functor f)`: the constructor variable
     is spelled `g` but was declared `f`; reproduce the declared head verbatim as
     `(Functor f)`."* (Conventional traits carry no binder to vary, so there is no spelling
     bit to check for them — the shape check `head_con_var: None` is total.)
4. **Slot-2 interpretation strictly per the known kind** — no "is slot-2 a trait or a
   type-constructor?" classifier (§7.3.5 Case 3 forbids it as pure redundancy):
   - **Conventional (Case 1):** slot 2 (`target`) MUST be kind `*` (a type). A
     bare/under-applied constructor (`(impl Display Option)`) is the sole rejection —
     *"`Option` is a constructor, not a type; apply it: `(Option a)` or `(Option Int)`."*
   - **Higher-kinded (Case 2):** slot 2 is the pairing `(Trait Constructor)`; the
     kind-check lands on `Constructor` (the arg of the pairing), which MUST be a
     **bare constructor whose arity matches** the con_var's usage-derived kind (§5.1
     step 4). Three rejections, each with the correct §7.3.5 diagnostic:
     - primitive → *"`Int` is not a type constructor"* (§7.2.3);
     - fully-applied type (`(Functor (Option Int))`) → *"kind-mismatch: slot 2 names
       the bare constructor `Option`, not an applied type"*;
     - wrong arity (`(Functor Pair)`, `Pair : * -> * -> *`) → *"`Pair` has 2 type
       parameters; trait `Functor` expects a constructor of arity 1."*

**Consequence (§7.3.5 "the two forms never collide for the same trait").** Because slot
2 is interpreted in the single mode the trait's declared kind dictates, `(Functor Option)`
(a trait-constructor pairing) and `(Option a)` (a type application) never contend — the
surface parallelism is resolved *before* slot 2 is inspected. This is Principle 24
("Resolve once") applied to the impl gate: the two former usage-derived kind derivations
(`registry.rs:117–126`, `impl_check.rs:39–92`) both collapse onto the one declaration
fact read at step 2.

**Where the old §5.4 defect went.** The prior "bare-con_var impl-on-primitive silently
accepted → backend `undefined function` leak" is closed by construction: that shape
(`(deftrait (Zeroable a) (zed [] :a))`, `a` never applied) is now rejected at the
`deftrait` (§5.1 step 1), so the impl never registers and no codegen leak can arise. A
**genuinely** HK trait (`Functor`, `f` applied) impl'd on a primitive is rejected at this
Case-2 seam with the clean §7.2.3 diagnostic. The two rejections carry **distinct
reasons** and must not be conflated (§7.1.1 occurrence rule vs §7.2.3 kind-check): a
no-occurrence method is *"nothing to dispatch on"*; a primitive HK target is *"not a type
constructor."*

**Diagnostic-uniqueness note (matrix input for /qa).** The 0628 repro's THREE symptoms
(silent-accept + codegen leak; `:a 7` display; accepted `(unwrap 7)`) all trace to the
single declaration-time reject + the `register_hkt_trait` guard fix (§5.1 step 3) — once a
bare-con_var trait cannot register, none of the three states is reachable. The §7.3.5
rejection matrix `/qa` owns: slot-1 echo {`None`, `Some`-matching-spelling,
`Some`-mismatched-spelling} × trait-declared-kind {conv, HK} ×
slot-2 {type, bad-applied, pairing-correct, pairing-primitive, pairing-wrong-arity} — the
declaration-reject row, the echo-shape-mismatch row, and the echo-spelling-mismatch row
(`(impl (Functor g) …)` vs declared `(Functor f)`, step 3 "Spelling") are new; the
diagnostic MUST name the new form. Class: `check-gate-leak` (S108 0571 D1 sibling).

**Fixture migration constraint (not designed here; /dev + /testing).** The ~24 typecheck
unit fixtures and ~7 e2e that model the old `(X a)`-head-as-`*`-kind-parametric mismodel
migrate to the settled form. Two grades (from the resolved FIXME 0639): **dispatch-only**
fixtures move to the bare head + empty `type_params`; **constraint-carrying** fixtures
(`register_num_trait_inline`, `register_num_for_int`, the inline `Double` decl) REQUIRE
`SelfType` methods (not merely empty `type_params`) so the `Num self` constraint rides
`self` for constrained-fn detection. The mechanics were prototyped + green-verified in
S111 CS-4 and reverted with the gate; git history is the reference. The e2e that REGRESS
under the naive gate (and so must migrate to the `self` / bare-head form, /testing):
`spec_05_definitions::deftrait_with_docstring_and_method_docstring_does_not_affect_dispatch`,
`spec_07_traits::trait_deftrait_impl_in_child_module_imported_dispatch_from_parent`,
`spec_07_traits::impl_hkt_arity_neg_prelude_provided_target_wrong_arity_rejected`
(message drift), `repl_introspection::bare_user_trait_lookup_impl_section_lists_type_not_others`,
`repl_introspection::impl_form_display_result_is_exactly_impl_trait_for_type`.

**Scope + cross-crate.** Typecheck-side: the `register_trait_decl` declaration-reject +
guard fix (`registry.rs`), and the `register_trait_impl` Case-3 seam (`impl_check.rs`)
consuming `TraitImpl.head_con_var`. The `head_con_var` field + the b0 `parse_impl` change
are **/arch + /dev(frontend)** — not designed here. The `CACHE_SCHEMA_VERSION` 20→21 bump
(pinned to b2, /arch A4) covers the `TraitDeclInfo.type_params` meaning change (a never-
applied `(X a)` no longer registers, so a stale schema-20 cache could resurrect a now-
rejected trait via cache-hit typecheck bypass).

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
