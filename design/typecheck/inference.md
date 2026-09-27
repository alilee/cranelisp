# Inference — typecheck interior

Owner: `design` narrow-deployed to typecheck. Subordinate to
[`typecheck.md`](typecheck.md); where they disagree the master wins. The pass
structure that drives inference (register, body check, finalize) is
[`typecheck.md` §5](typecheck.md#5-pipeline-inside-check_forms) and is not
restated here. Required behaviour is `spec/03-types.md`.

This document owns Algorithm W as the crate realises it: the substitution,
unification, generalisation and instantiation, written type variables, and the
per-expression type record.

---

## 1. State and seams

- **One substitution per cluster.** `CheckState.subst` is shared by every body
  in the cluster, so a call in one body constrains the callee's registration
  variables (`typecheck.md` §5.2 item 3). There is no per-body substitution.
- **Fresh variables** come from the environment's atomic counter. The counter is
  monotonic and a failed cluster's ids are abandoned, never reused
  (`typecheck.md` §7.4).
- **One helper per expression variant.** `infer_expr` dispatches to a helper per
  `Expr` variant; `infer_var` is the reference-resolution chokepoint
  (`typecheck.md` §3.1).
- **One unification seam.** `unify::unify_with_rigid` (§2). `TypeCheckEnv::unify`
  threads the current body's rigid set and re-spans an error that carries
  `Span::SYNTHETIC` to the caller's span. `unify`, `bind_var` and `fresh_var` are
  free functions over `&mut Subst` / the counter so inference can hold the
  substitution and mint variables in one step without a `&mut self` borrow
  conflict.
- **Per-body state is one frame.** `CheckState.body_frame` (`BodyFrame`) holds the
  rigid set, the written-variable scope, the recursion binding and the body's
  deferred name and pattern uses. `check_defn_body` and
  `check_defn_body_with_types` swap a fresh frame in and restore the previous one
  at a single point on every exit, success or error. `infer_lambda` and
  `infer_annotate` take the shared written-variable scope and reinstall it on
  every exit. A frame or scope leaked by an error path would be installed for the
  next form; restoring on both paths keeps that structural rather than dependent
  on the whole call aborting.

## 2. Unification

```
unify(Var(a), t)        = unify_var(a, t)                    ;; symmetric
unify(Int, Int)         = ok                                 ;; likewise the other scalars
unify(Fn(ps1, r1), Fn(ps2, r2))
                        = arity equal; unify each (p1, p2); unify(r1, r2)
unify(ADT(n, as1), ADT(n, as2))
                        = unify each (a1, a2)                ;; nominal: same FQ name
unify(TyConApp(f, as1), ADT(n, as2))
                        = arity equal; unify_var(f, ADT(n, [])); unify each arg
unify(TyConApp(f1, as1), TyConApp(f2, as2))
                        = arity equal; if f1 != f2 then unify_var(f1, Var(f2)); unify each arg
unify(_, _)             = TypeError (rendered through render_type, typecheck.md §8.3)
```

`unify_var` carries the rigid-variable asymmetry (§4.2):

- a flexible variable binds to anything, including a rigid variable, subject to the
  occurs check;
- a rigid variable must not bind to a concrete type: that is a skolem escape and is
  rejected;
- two rigid variables merge, and both stay abstract.

Both `TyConApp` head binds go through `unify_var`, not a raw `bind_var`. HKT
constructor variables are never written skolems, but `apply` can rewrite a head
id along the substitution; routing the head through the rigid guard makes a
kind-confused signature a located error rather than a silent acquire.

Lookup follows the substitution transitively until it reaches a non-variable.

## 3. Generalisation and instantiation

- **Instantiation** replaces each quantified variable with a fresh one, so every
  reference gets its own copy. A scheme with no quantified variables is returned
  unchanged, so a reference to a sibling whose generalised scheme has not yet been
  written back unifies into that sibling's registration variables. This is
  ordinary monomorphic binding-group behaviour: sound, sometimes over-restrictive.
- **Generalisation** applies the substitution, quantifies the variables not free in
  the environment, and lifts trait constraints from `active_constraints` onto the
  quantified variables they resolve to ([`traits.md` §6](traits.md#6-constrained-polymorphism)).
- **Writeback order.** A body's unconstrained scheme is written back as soon as its
  check ends, so a later sibling instantiates a fresh copy (`typecheck.md` §5.2
  item 4). A caller checked before its callee can still generalise too early; the
  compensation and the linear cures are the generalisation-ordering debt in
  [`monomorphisation.md` §5.1](monomorphisation.md#51-generalisation-ordering-debt).
- **Recursion is monomorphic.** A definition's own name is bound to its
  monomorphic function type inside its body (`spec/03-types.md` §3.10). Considered: making the
  self-reference polymorphic to relieve the over-restriction above. Rejected:
  polymorphic recursion is undecidable in HM, and the spec generalises at the
  binding-group boundary. Any generalisation-order fix acts on cross-definition
  references, never on self-reference.

## 4. Written type variables

Required behaviour is `spec/03-types.md` §3.3.1–§3.3.5. A written variable takes
one of two paths, chosen by what is written.

### 4.1 A bare variable is flexible and named

`:a`, alone or nested as in `:(Box a)`, is an ordinary inference variable that
carries a display name. The name relates same-named occurrences and documents
the displayed scheme. It carries no rigidity and no checking obligation: the body
may narrow it to a concrete type (`(defn f [:a x] :a "hello")` is
`(Fn [String] String)`), and two bare variables tied by the body merge.

### 4.2 A constraint at a parameter position is rigid

`:C x`, where `C` names a trait, is a checkable claim (§3.3.2). The variable is
held abstract over `C` for the body check; narrowing it to a concrete type is a
skolem escape. Rigidity exists only on this path, because a caller relies on the
constraint and not on the name.

### 4.3 Realisation

- **Co-reference.** The written-variable scope is built at registration
  (`register_defn_signature`; the scope rides the body's registration in the
  body ledger, `checked-body-publication.md`), installed for the body by `check_defn_body`, and shared without reset into nested
  `fn` bodies by `infer_lambda`. A body `:a` therefore co-refers with a parameter
  `:a`, and an inner `(fn [:a y] …)` co-refers with the enclosing `a`.
- **Rigid seeding.** `check_defn_body` seeds the rigid set from parameter
  variables that already carry a constraint at body-check entry, which
  `resolve_bound_param` recorded from a written `:C x`. A bare parameter that only
  acquires a constraint from body use is not seeded, so it stays flexible: an
  inferred constraint is not an asserted one.
- **Transient.** Rigidity and the written-variable scope live on the body frame for
  one body check and are never serialised. No `cranelisp-types` type carries
  rigidity.
- **Explicit-type bodies.** `check_defn_body_with_types`, used for impl-method
  bodies and monomorphisation rechecks, receives concrete parameter types and
  installs an empty frame: no co-reference and no rigidity (see §6).

Considered and rejected, so neither is reintroduced:

- minting a fresh quantified variable for each written variable, which loses
  co-reference;
- treating every written variable as rigid, with a flag to suppress rigidity on
  rechecks and an eager escape check on lambdas. This rejected bodies that the
  spec admits and was deleted from the source.

### 4.4 Rank-1 polymorphic values need no eager check

A body that defines a rank-1 polymorphic function value, whether returned,
let-bound, passed or applied in place, is legitimate, and the written form is the
same as its unwritten twin (§3.3.4). No check is added for it. The genuine limits
are enforced elsewhere:

- one polymorphic instance used at two types, and a polymorphic argument used at
  two types inside a callee, are unification failures;
- a result-only variable left unresolved at a codegen-reaching use is refused by
  the ambiguity backstop ([`monomorphisation.md` §4](monomorphisation.md#4-the-ambiguity-backstop)).

### 4.5 Value-position annotations

`infer_annotate` handles `:T expr` (§3.3.3):

- a variable or concrete type annotation unifies with the expression's type,
  flexibly. It can pin a type or select a return-type dispatch;
- a bare name that resolves to a trait (`:Num 5`) is a satisfaction check only and
  changes nothing. A nominal concrete type must have an impl; a concrete
  non-nominal type such as a function is rejected, because impls are keyed by
  a nominal type's identity (`typecheck.md` §9.1.1). A still-variable type is
  left for the ambiguity backstop.

## 5. Expression types

Every inference helper records its node's type through `record_expr_type` into
`CheckState.expr_types`, keyed by span. Finalize drains the map into the
accumulator, resolves it through the final substitution and writes it onto the
AST ([`ast-annotation.md` §2–§3](ast-annotation.md#2-carriers-while-a-cluster-is-checked)).

### 5.1 Polymorphic type variables in expr_types

A template body legitimately records `Type::Var` entries: `(defn id [x] x)` types
`x` as a variable. Concrete bodies reach codegen only as monomorphised instances
([`monomorphisation.md` §1](monomorphisation.md#1-the-invariant-only-concrete-callables-are-realised)).
A residual variable in a concrete view is refused by the ambiguity backstop
unless the defaulting licence applies ([`non-concrete-producer-obligations.md`
§3.2](non-concrete-producer-obligations.md)).

## 6. Open item — constraint rigidity in impl-method bodies

`check_defn_body_with_types` installs an empty frame, so a constraint on a
non-`Self` type variable of a trait-method signature is not held abstract inside
an impl-method body. Whether spec §3.3.2 requires it to be held abstract there is
unsettled.

The parse gap that used to keep the question unreachable has closed:
`build_impl_method` now accepts a `:Type body` ascription (the frontend's
`build_body_to_end`). No test covers the cell. The question belongs to `spec`
and the evidence to `qa`; this design will follow the ruling. This is a
source-read lead that has not been executed.

---

## Former section names

| Former heading | Now |
|---|---|
| Architecture; Module Layout; Key Design Decisions | §1 and `typecheck.md` §3.1 |
| Two-Pass Pipeline; REPL Mode | `typecheck.md` §5. The REPL takes the same `check_forms` path |
| Cross-Defn Generalization Timing (FIXME 0344) | §3 and `monomorphisation.md` §5.1 |
| Written type variables, including the shipped hybrid and realisation | §4 |
| Structural hardening of the rigid-model invariants (FIXME 0595) | §1 (frame restore) and §2 (head binds). Both are landed |
| Rank-1 polymorphic returns | §4.4 |
| Value-position annotations | §4.5 |
| Open design note — constraint-path rigidity in trait-impl method bodies | §6 |
| Unification | §2 |
| Scheme Operations | §3 |
| Expression Type Recording; Polymorphic Type Variables in expr_types | §5, §5.1 |
| Per-Ring Evolution | Removed; Git history |
