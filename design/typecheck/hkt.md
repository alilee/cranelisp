# Higher-kinded traits — typecheck interior

**Owner:** `design`, narrow-deployed to `cranelisp-typecheck`.
**Subordinate to:** [`typecheck.md`](typecheck.md) §9.1; the trait subsystem is
[`traits.md`](traits.md).
**Required behaviour:** `spec/03-types.md` §3.7 and `spec/07-traits.md` §7.2,
§7.3–§7.3.6 and §7.12.1.
**Neighbours:** slot-1 trait resolution and impl enrolment are
[`qualified-trait-impl.md`](qualified-trait-impl.md); the parser carrier for the
echoed head is `design/frontend/trait-impl-head-parse.md`; `Type` and `apply`
belong to `cranelisp-types` (`arch`).

A higher-kinded trait abstracts over a type constructor: in
`(deftrait (Functor f) (fmap [:(Fn [a] b) func :(f a) x] (f b)))`, `f` ranges over
constructors such as `Option`. This document states how typecheck represents,
registers, checks, implements and dispatches such traits.

---

## 1. Representation

- A constructor application `(f a)` in a higher-kinded signature is
  `Type::TyConApp(f_id, [a])`. `f_id` is an ordinary `TypeId`, in the same
  namespace as `Type::Var`.
- A constructor variable binds to a **bare** constructor, `ADT(name, [])`, never to
  an applied type. `cranelisp_types::apply` rewrites a bound head:
  `TyConApp(f, args)` with `f ↦ ADT(name, _)` becomes `ADT(name, args)`, and with
  `f ↦ Var(g)` becomes `TyConApp(g, args)`.
- `free_vars` includes the head id, so the ordinary occurs check sees a
  constructor variable wherever it appears.
- There is no kind annotation. A constructor variable's arity is its usage-derived
  arity ([declaration kind](#51-kind-derivation-at-declaration-consumers-read-type_params), item 4). A trait has at most one constructor variable (spec §7.12.1);
  code indexes `type_params[0]` on that basis.

## 2. Unification

`unify_with_rigid` adds two arms:

| Pair | Rule |
|---|---|
| `TyConApp(f, as)` ~ `ADT(n, bs)` (either order) | Arities must match; bind `f ↦ ADT(n, [])`; unify `as` with `bs` pairwise. |
| `TyConApp(f, as)` ~ `TyConApp(g, bs)` | Arities must match; if `f ≠ g` bind `f ↦ Var(g)`; unify pairwise. |

An arity mismatch is a type error. Both head binds go through `unify_var`, not a raw
bind, so a rigid variable that reached head position is a skolem-escape error rather
than a silent binding (`inference.md` §"Written type variables").

## 3. Resolution of signature types

Higher-kinded signatures resolve through the one `TypeExpr → Type` resolver
(`type-expr-resolver-convergence.md`), selected by its constructor-variable context:

| Context | `(f a)` with `f` a constructor variable | Bare `f` |
|---|---|---|
| Declaration (`ConVars::Decl`) | `TyConApp(f_id, [a'])` | `Var(f_id)` |
| Impl method check (`ConVars::Impl`) | `ADT(target, [a'])` | — |

The trait-side wrappers (`resolve_hkt_sig_type_expr`, `resolve_hkt_impl_type_expr`)
only build that context. An unknown type name in a signature is a source error, as in
any other signature.

## 4. Declaration registration

`register_trait_decl` derives the kind from the declaration head (§5.1) and routes a
higher-kinded declaration to `register_hkt_trait`:

1. A higher-kinded method with a default body is rejected (spec §7.1.5; the
   method-tail classification is `s116-method-signature-resolution.md`).
2. A parenthesized head whose constructor variable is never applied is rejected
   ([declaration kind](#51-kind-derivation-at-declaration-consumers-read-type_params), item 1).
3. Each constructor variable gets a fresh `TypeId`.
4. Each method records `hkt_param_index`: the first parameter whose type applies a
   constructor variable (`spec/03-types.md` §3.7.6). The result is written once onto the stored
   `TraitMethodSig`; every consumer reads it.
5. Each method scheme quantifies the constructor ids and the method's ordinary
   variables, and constrains each constructor id to the trait's `FQTraitName`.
6. Methods install through the trait-method funnel with the trait's visibility; the
   `TraitDecl` binding carries `type_params` and the indexed methods.

## 5. Implementation registration

### 5.1 Kind derivation at declaration; consumers read `type_params`

Kind is a property of the declaration, derived once at registration and recorded on
`TraitDeclInfo.type_params` (spec §7.1, §7.2.1):

| `deftrait` head | Constructor variable applied somewhere? | Kind | `type_params` |
|---|---|---|---|
| bare `Name` (methods use `self`) | no variable | `*` (conventional) | empty |
| `(Name f)` | yes | `* -> *` (higher-kinded) | `[f]` |
| `(Name f)` | never | malformed — rejected at `deftrait` | never registers |

1. **The never-applied head is rejected at the declaration.** The diagnostic names
   the fix: a trait that returns the implementing type uses the bare head and
   `self`. Because such a trait never registers, no impl of it, no unresolved-var
   display and no codegen leak can follow from it.
2. **Non-empty `type_params` ⟺ higher-kinded, exactly.** Impl validation (§5.4)
   and dispatch (§6) read `type_params`; neither re-scans
   method signatures to rediscover kind (Principle 24). A second, usage-derived kind
   test is the mistake this rule exists to prevent: two such tests diverged once, and
   a never-applied head then registered as a conventional trait.
3. **Routing depends on `type_params` alone.** Every declaration that passes item 1
   with non-empty `type_params` goes through `register_hkt_trait`.
4. **Expected constructor arity** is the argument count of the constructor
   variable's first applied occurrence, in parameters then result (`con_var_arity`).
   Item 1 guarantees one exists for every registered higher-kinded trait.

### 5.2 Self type for a higher-kinded impl method

For `(impl (Functor f) (Functor Option) …)` the effective target is the bare
constructor `Option` (§5.4 step 4). Each method body is checked with:

- signature types resolved in the impl context, so `(f a)` becomes `(Option a)`;
- a concrete self type `ADT(Option, [fresh…])`, one fresh variable per
  expected-arity position;
- the result wrapped with the impl's conformance context on error.

### 5.3 Pre-unification of the dispatch parameter

Before the body is checked, the parameter at `hkt_param_index` is unified with the
concrete self type. This fixes the parameter's constructor and leaves its element
types as fresh variables for the body to settle.

### 5.4 The impl form and the §7.3.5 Case-3 kind-check seam

**The form (spec §7.3, §7.3.4).** `(impl impl_head impl_target method_def+)`:

- a conventional trait writes the bare trait name in slot 1 and a type in slot 2:
  `(impl Display (Option :Display a) …)`;
- a higher-kinded trait echoes the declared head in slot 1 and writes a
  trait-constructor pairing in slot 2: `(impl (Functor f) (Functor Option) …)`.

The parser records the written slot-1 shape on `TraitImpl.head_con_var` (`Some(f)`
for a parenthesized head, `None` for a bare one). Slot 2 stays a `TypeExpr`; a pairing
arrives as `Applied(Functor, [Named(Option)])`. The parser classifies nothing
(`design/frontend/trait-impl-head-parse.md`).

**One deterministic path in `register_trait_impl`.** There is no second
"is slot 2 a trait or a constructor?" classifier; spec §7.3.5 Case 3 forbids it, and
the declared kind already answers it.

1. **Resolve slot 1 as a trait reference** to its canonical identity
   (`qualified-trait-impl.md`).
2. **Read the kind from the declaration:** `type_params` non-empty ⟺
   higher-kinded ([declaration kind](#51-kind-derivation-at-declaration-consumers-read-type_params)).
3. **Validate the slot-1 echo — shape and spelling.** Both bits are checked here,
   against the declaration from step 2, at the impl form's location:
   - *Shape.* A higher-kinded trait needs `head_con_var: Some(_)`; a conventional
     trait needs `None`. Each mismatch names the form the declaration requires.
   - *Spelling (higher-kinded only).* The written variable must equal the declared
     one, `type_params[0]`. `(impl (Functor g) …)` against `(deftrait (Functor f) …)`
     passes the shape bit, so checking shape alone would accept it. The diagnostic
     names both spellings and the verbatim head to write.

   The constructor variable is a **binder**, so it is matched by spelling. Trait
   names are **references**, matched by resolved identity (step 4, Case 2).
4. **Interpret slot 2 strictly by the known kind.**
   - **Conventional (Case 1).** Slot 2 is a type. When its head resolves to a type
     constructor, it must be applied to exactly that constructor's declared arity.
     Two rejections flank the well-kinded set:
     - *under-applied or bare* (`(impl Display Option)`): the constructor is not a
       type;
     - *over-applied* (`(impl Display (Option Int Int))`): it takes fewer
       parameters than supplied.

     **M2 — arity-aware fix suggestion.** Both diagnostics suggest the constructor
     applied to one fresh variable per declared parameter: `(Option a)`,
     `(Pair a b)`, `(Tri a b c)`. A fixed one-variable template is itself ill-kinded
     for a multi-parameter constructor.

     **Care — the poly-applied positive stays admissible.** `(Option a)`,
     `(Option Int)` and `(Option :Display a)` each supply exactly one argument to an
     arity-1 constructor, so the arity test never fires on them (spec §7.3.3,
     §7.3.6). Only a genuine shortfall or surplus is rejected; do not tighten the
     test into "no type variables in slot 2".
   - **Higher-kinded (Case 2).** Slot 2 must be `(Trait Constructor)`. The pairing
     head is validated first, then the constructor:
     1. *Pairing head.* It is resolved as a trait reference, with its written
        qualifier, through the same resolution as slot 1, and its canonical identity
        must equal slot 1's. A qualified or differently imported spelling of the
        same trait is accepted; a different trait or an unresolvable name is
        rejected with a diagnostic naming what was written and the pairing to write
        (spec §7.3.5 *Pairing-head identity*).
     2. *Applied type* (`(Functor (Option Int))`): slot 2 must name the bare
        constructor.
     3. *Primitive* (`(Functor Int)`): not a type constructor (`spec/07-traits.md` §7.2.3).
     4. *Wrong arity* (`(Functor Pair)` for an arity-1 variable): the constructor's
        declared parameter count must equal the expected arity ([declaration kind](#51-kind-derivation-at-declaration-consumers-read-type_params), item 4).

     On success the effective target becomes `Named(Constructor)`. Every downstream
     step — method presence, default generation, method checking and the `$Type`
     suffix — then sees the bare constructor, exactly as for a conventional target.
     `src/session_v4/types.rs::impl_echo_type_name` performs the reciprocal extraction for the
     REPL's impl echo; the two must keep reading the constructor out of the pairing.

**Distinct reasons stay distinct.** A conventional method that never mentions the
implementing type is rejected by the occurrence rule (spec §7.1.1, `design/typecheck/traits.md` §2);
a higher-kinded impl on a primitive is rejected by the kind check (`spec/07-traits.md` §7.2.3).
Neither diagnostic may stand in for the other.

## 6. Method resolution

- Dispatch selects the argument at the method's `hkt_param_index`, read from the
  trait declaration at the trait's home. A method whose declaration is not reachable
  that way falls back to the shared bulk trait-declaration scan
  (`traits/dispatch.rs::find_trait_method_decl`), whose not-found result stays
  distinct from a present method with no index. Conventional methods default to
  index 0.
- The selected argument must have a concrete nominal head (`concrete_type_name`); a
  still-open variable defers the call (`traits.md` §7).
- A higher-kinded method symbol carries the constructor's home-qualified head only,
  `Functor.fmap$<home>/Option`, through the one mangler shared with impl
  definition (`traits.md` §3.1).

## 7. Monomorphisation interaction

- A trait-method call resolves by trait dispatch at its concrete call site
  (`spec/03-types.md` §3.7.6); the method itself is not a monomorphisation template.
- `Type::is_concrete` is false for every `TyConApp`, so no constructor application
  can reach a concrete callable or a codegen view (`monomorphisation.md` §1). A
  residual one is refused by the ambiguity backstop (`monomorphisation.md` §4).

## 8. Invariants

| Invariant | Grade |
|---|---|
| `TyConApp` never reaches codegen. | Structural: the lifecycle's concreteness predicate rejects it at settlement. |
| Kind has one source, `type_params`. | Asserted with a named falsifier: a new consumer that inspects method signatures to decide kind. Evidence: the §7.2.1 and §7.3.5 rejection cells in `tests/spec_07_traits.rs`. |
| `hkt_param_index` is computed once, at declaration. | Asserted with a named falsifier: a dispatch or impl site recomputing it from signatures. |
| A head bind cannot capture a rigid variable. | Structural at the unification seam (`unify_var`). |

## 9. Edge cases

- **Nullary constructors.** `(deftype Color Red Green Blue)` has arity 0 and is
  rejected as a higher-kinded target by the Case 2 arity check.
- **Nested application.** `(f (g a))` unifies recursively; single-variable traits do
  not produce it, and the rules need no special case.
- **Bare constructor variable beside an applied use.** In a declaration that applies
  `f` somewhere, a bare `f` elsewhere resolves to `Var(f_id)`. Spec §7.2.1 rejects
  only the never-applied head; it does not address mixed use.
- **REPL.** Registration, impl checking and dispatch follow the batch path; the
  indexed `TraitDecl` persists in the module table.

## 10. Open leads

These are source-read leads, not executed reproductions. `qa` owns their intake.

| Lead | Observation | Owner of the next step |
|---|---|---|
| Result-only constructor variable | `find_hkt_param_index` falls back to index 0 when no parameter applies the variable, so a method such as `(pure [:a x] (f a))` would dispatch on its first argument's type. Spec §3.7.6 defines dispatch only by the first parameter that applies the constructor. | `spec` to state whether such a method is admissible; `qa` intake |
| Primitive test by spelling | The Case 2 primitive rejection compares the constructor's written name with `Int`, `Bool`, `String` and `Float` rather than its resolved identity. | `qa` intake |

---

## Former section numbers

The S122 rewrite removed the delivery plan; §5.1–§5.4 keep their numbers and cited
sub-anchors (§5.4 step 3, M2, Case 1 "Care").

| Former | Now |
|---|---|
| §1 Problem statement; §2 Sketch comparison | §1 and the introduction; the sketch comparison is in Git history |
| §3.1–§3.3 Unification rules and occurs check | §2 and §1 |
| §4.1–§4.6 Declaration handling | §3 and §4 |
| §5.1–§5.4 | unchanged |
| §6.1–§6.4 Method resolution | §6 |
| §7 Monomorphisation interaction | §7 |
| §8 Invariants | §8 (the "no default methods" item is §4 step 1: typecheck rejects it, not the frontend) |
| §9.1–§9.5 Edge cases | §9 (§9.2 single variable → §1) |
| §10 Changes required; §11 Implementation order | removed (landed; Git history) |
