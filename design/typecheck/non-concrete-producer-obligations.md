# The non-concrete producer obligations — typecheck's half of the release contract

**Status:** RULING — authored S119 Phase 3 round 2, `/design`(typecheck), against the
landed `design/backend/non-concrete-release-contract.md` (commit `65357390`).
**Subordinate to:** `typecheck.md` §9.3 / §9.4. Extends `monomorphisation.md` §1–§3
(the S84 slot-gate model) and `adt.md` §"Product Type Handling".
**Governed by:** `design/backend/non-concrete-release-contract.md` R-2, R-3, §5.2,
§5.4 — where this doc and that ruling disagree, the ruling wins.
**Resolves:** FIXME **0924** (the monomorphisation obligation), FIXME **0913**
(the lenient view). **Gates:** FIXME **0916** (×1 RED), rider **0867** (×3 RED).

---

## 0. The one sentence

Three frames in this crate present downstream gates with a type more concrete than
what typecheck actually knows. Each does it at a different altitude, and all three
are the same defect:

| # | Site | Fabricates | Altitude |
|---|---|---|---|
| **F1** | `adt.rs::synthesise_one_accessor` (`:618-637`) | `UserFnState::Concrete { got_slot }` over a scheme whose type is **not** `is_concrete()` | frame |
| **F2** | `traits/impl_check.rs::check_impl_method` (`:1043,1078-1090`) | `scheme::mono(fn_type)` — `type_vars: []` over a `fn_type` that still carries `Type::Var` — then `Concrete { got_slot }` | frame |
| **F5** | `MonoExpr::lenient_from_expr`'s `node_ty` (`mono_expr.rs:836-841`) | `ConcreteType::Int` for any node whose real type is not concrete | value |

R-2 ("no fabricated concreteness") is Principle 25 applied to the type channel, and
none of the three carries its check. This doc rules all three. F1 and F2 are FIXME
0924; F5 is FIXME 0913.

**The reduction that makes 0924 cheap.** The compiler already owns the mechanism both
frame-level fabrications need: the S84 structural slot gate (`monomorphisation.md` §1
— *a def has a GOT slot ⟺ its finalised type is `Type::is_concrete()`*), the slot-less
`UserFnState::Polymorphic` arm, `ParametricFn`, `SymbolTable::defined_symbols()`
excluding templates from codegen, and `pass4_monomorphise`'s worklist. F1 and F2 are
not a capability the compiler lacks. **They are two hand-mint sites that bypass the
gate `finalize_check_form` applies to every ordinary `defn`.** The obligation is to
stop exempting them — which is `/arch`'s own S84 invariant, enforced at two more
sites.

---

## 1. What was verified at source (the binding first act)

Read at `5520186d`, design-window only, no build run (the sprint reserves the
build/test slot; every claim below is a source reading, and every claim that would
need a run is marked **MEASURE** in §7).

### 1.1 F1 — the accessor mint

`crates/cranelisp-typecheck/src/adt.rs:618-637`. For **every** product type, including
a polymorphic one:

```rust
let accessor_ty = Type::Fn(vec![adt_type.clone()], Box::new(field.ty.clone()));
let scheme = Scheme { type_vars: type_var_ids.to_vec(), constraints: HashMap::new(), ty: accessor_ty };
…
let canonical_slot = self.current_symbol_table_mut(state).allocate_got_slot()?;
let canonical = ModuleEntry::def(scheme, DefKind::UserFn {
    fn_state: cranelisp_types::UserFnState::Concrete { got_slot: canonical_slot, mode_summary: None },
})
```

For `(deftype (Bx a) [:a v])` the scheme is `∀a. (Fn [(Bx a)] a)` — `type_vars`
non-empty, `ty` non-concrete — and it is minted `Concrete { got_slot }`
unconditionally. That is exactly the pairing `monomorphisation.md` §2.1 declares
**unconstructable**. The slot makes it a value-callable; `defined_symbols()`
(`module.rs:769-793`) admits it as a codegen target because the exclusion tests the
`fn_state` variant, not the scheme; backend compiles a frame whose parameter is
`ADT(ct/Bx, [Var])` and whose result is a bare `Var`. That frame is census A's
family F1 and census B's non-ctor-template bare-`Var` licence, and §2.4 of the ruling
shows it SIGSEGVs at payload 1024.

A **concrete** product (`(deftype Tally [:Int passed :Int failed])`) mints
`type_vars: []` over a concrete `ty` and is correct today. The exemption is
polymorphic-only — which is precisely why the four-line repro needs a type parameter
and nothing else.

### 1.2 F2 — the trait-impl method mint

`crates/cranelisp-typecheck/src/traits/impl_check.rs:1043` and `:1078-1090`:

```rust
let fn_type = apply(&state.subst, &Type::Fn(param_types.to_vec(), Box::new(ret_ty.clone())));
let concrete_scheme = crate::scheme::mono(fn_type);
…
fn_state: UserFnState::Concrete { got_slot, mode_summary: None },
```

`scheme::mono` (`scheme.rs:11`) sets `type_vars: vec![]` and copies `ty` verbatim. For
`(impl (Functor Option) (defn fmap [g o] …))` the applied `fn_type` is
`(Fn [(Fn [a] b) (Option a)] (Option b))` — `a`/`b` survive `apply`, because nothing
in the impl pins them. So the entry claims "monomorphic" while carrying two residual
variables. **The name `mono` is the fabrication**: it asserts an absence of
quantification, and the mint site reads that absence as concreteness.

Two downstream consequences, both measured in the ruling:

- `entry_is_monomorphisable_polymorphic` (`program/mono_collect.rs:695-716`) tests
  `!scheme.type_vars.is_empty()`, so an F2 entry answers **false** and no call site
  ever specialises it. F1 answers **true** (its `type_vars` are honest) yet is still
  compiled as a template because the slot exists — the two families reach the same
  bad frame by opposite routes.
- The instance name is `mangle_trait_method(trait, method, fq_type)`
  (`traits/mod.rs:74-80`) = `"{Trait}.{method}${fq_type}"` — keyed on the type
  **constructor's** `FQTypeName`, with its arguments erased. One body per
  `(trait, method, type-constructor)`, whatever the instantiation.

### 1.3 F5 — the lenient view

`crates/cranelisp-types/src/mono_expr.rs:836-841`:

```rust
let node_ty = |e: &Expr| -> ConcreteType {
    e.inferred_type().and_then(|t| ConcreteType::from_type(t).ok()).unwrap_or(ConcreteType::Int)
};
```

The single production producer of the lenient view is
`program/support.rs::build_concrete_codegen_view` (`:307-350`) — shared by the
single-sig, multi-sig-mangled and trait-impl-method population sites — on the
`ViewBuildError::NotConcrete` arm only. `adt.rs`'s synthetic bodies take
`synthetic_local_from_expr` instead and are outside this seam.

For a REPL turn the body is `__expr`'s, its root type is `(Result a String)`,
`ConcreteType::from_type` fails on the residual `a`, and the whole type is replaced
with `Int`. Int's `release_key` (`src/result_owner.rs:337-352`) then takes
`codegen_result_ty = Int` **by design** (§4.3 "take the key from the same read that
produced the code pointer"), backend requested no glue for an `Int` root, and the
result tree is never released. Int's behaviour is correct given what the producer
published; the producer published a fiction.

**`design/int/result-owner.md` §1.1.1's scope sentence is wrong and is not mine to
fix** — it records the gap as "an unpinned `[]` (or a bare polymorphic `None`)",
and `None` cannot leak (nullary tag, no allocation). The real axis is *any* residual
parameter in the result's displayed type, which is `(Ok x)` / `(Err x)` / `(vec)`.
`/design`(int) owns that correction in this same window (SPRINT.md §Skill plans,
round 1); this doc records the corrected scope as the acceptance axis.

---

## 2. FIXME 0924 — the monomorphisation obligation

### 2.1 The rule

> **P-1 (the gate is universal).** No site in `cranelisp-typecheck` may construct
> `UserFnState::Concrete { got_slot }` for an entry whose scheme type is not
> `Type::is_concrete()`. A non-concrete callable is `UserFnState::Polymorphic`,
> slot-less, and is a monomorphisation **source**, never a codegen target.

P-1 is not new policy. It is `monomorphisation.md` §1 stated as a *site-independent*
invariant instead of a property of one determination point in `finalize.rs`. The
correct enforcement is structural (Principle 18/20): the gate belongs at the one place
a `Concrete { got_slot }` is minted, not repeated at three call sites. §6.1 gives
`/dev` the shape.

> **P-2 (no second identity home).** A monomorphised accessor or trait-method
> instance is named by the ONE canonical mangler,
> `traits::monomorphise::build_mangled_name(home, bare_name, param_types)`
> (`monomorphisation.md` §3.5). No new grammar, no widened second mangle.

### 2.2 Why P-2 rejects the FIXME's own suggested spelling

FIXME 0924 item 2 and the ruling §5.2 both propose widening
`mangle_trait_method` from `…$primitives/Option` to `…$primitives/Option$Int` — "a
key widening on an existing mangle". **That spelling is rejected, and the disposition
it serves is adopted.** Three reasons, in order of weight:

1. **It is lossy on the axis that matters.** `Functor.fmap`'s instantiation is
   `(a, b)`, and `b` comes from the *function argument's* return type, not from the
   receiver. Widening the key by the receiver's type arguments yields
   `Functor.fmap$primitives/Option$Int` for both `(fmap show (Some 1))` and
   `(fmap inc (Some 1))` — two distinct instantiations, one name. That is exactly the
   0483/0508/0519 collision class the canonical mangler was built to close, re-minted
   one sprint later at a new site.
2. **`build_mangled_name` already carries the whole signature**, recursing every
   concrete parameter type through `program::mangle_type` (ADT args recursed, `Fn`
   params recursed rather than dropped). It is collision-free by construction and
   cache-safe, and it has the `is_concrete()` `debug_assert!` tripwire
   (`monomorphise.rs:1295-1300`) that catches a spurious partial mint.
3. **Principle 7.** Two grammars for "a concrete instance of a generic body" is the
   second identity home the release contract's reject criterion 5 forbids in the
   backend and that S110's alias-class close removed from the resolution channel.

`mangle_trait_method` **survives unchanged** as the *template* name — the discovery
and dispatch key, exactly as today. The instance is a different symbol under the
existing mono grammar. Restated:

| Role | Symbol | State |
|---|---|---|
| Impl-method template (as today, now slot-less) | `Functor.fmap$primitives/Option` | `Polymorphic(ParametricFn)` |
| Concrete instance (new, minted on demand) | `{impl_module}/Functor.fmap$primitives/Option$Fn(Int;primitives/String)+primitives/Option$Int` | `Concrete { got_slot }` |

The template's key is untouched, so trait *discovery* (`impl$…$…`,
`dispatch.rs:143`, `impl_check.rs:421`, the §7.3.5 conformance seams) is untouched.
Only the *call* is redirected, by rewriting the site's `ApplyRef::Dispatch(FQSymbol)`
to the instance — the same carrier value-source rule
(`backend-keyed-consumer.md` §1.1/§1.1.2) the mono path already obeys for constrained
fns. **No `cranelisp-types` delta, no public-API delta, no new carrier.**

### 2.3 F1's disposition — A-MINT: an accessor instance is re-synthesis, not re-check

`monomorphise_call`'s core instantiates a template by **re-checking its body** at
concrete argument types, in the defining module's scope (`monomorphisation.md` §3.7).
That is the right machinery for F2 — a user-written impl-method body with real spans,
real resolution carriers, and a real import context.

It is the **wrong** machinery for F1, and forcing it there would manufacture three
problems the synthesiser does not have:

- an accessor body is `Span::SYNTHETIC` throughout (`adt.rs:447-471`), so it is
  structurally outside span-keyed carrier transport — the recheck would produce
  `pattern_ctors` / `var_refs` / `apply_refs` maps keyed on one repeated synthetic
  span;
- the arm's constructor identity is supplied *directly* at synthesis
  (`adt.rs:600-606`), not resolved — re-checking would have to re-derive a fact
  already in hand (Principle 24);
- the body is **derived from the field list**, not authored. Re-checking a derivation
  to recover the types the derivation was computed from is a second derivation of a
  settled fact (Principle 7, Principle 26).

> **A-MINT.** A monomorphised field accessor is produced by **re-running the
> synthesiser at concrete type arguments** — the same
> `synthesise_one_accessor` computation with `adt_type` and `field.ty` substituted
> through the instantiation — keyed by `build_mangled_name`. It never re-checks a
> body, never consults a span-keyed sidecar, and builds its `codegen_view` with
> `MonoExpr::synthetic_local_from_expr` exactly as the template does today.

A-MINT is why F1 is the cheaper half of 0924 despite being the larger census share:
the instance is a pure function of `(fqtn, ctor, field, concrete type args)`, and the
substituted `accessor_ty` is concrete by construction whenever the demanded
instantiation is. Its `debug_assert!` is P-1 itself — the minted instance's scheme
`is_concrete()`.

Two consequences at the synthesis site, both deletions:

- when the substituted scheme is non-concrete, **no slot is allocated and no
  `codegen_view` is built** — the premature `synthetic_local_from_expr` call and the
  `allocate_got_slot()` move to the instance mint (Principle 6, and it removes a
  wasted GOT slot per polymorphic accessor);
- the bare-alias `Import` edge, the `Ambiguous` poison, the cross-cluster
  `committed_accessor_kind` classification and the §8.6.5 contest rules are
  **untouched**. They key on the canonical `Type.field` symbol, which still exists —
  it is now a template rather than a compiled body. Resolution, `/list`, `/exports`,
  display and the impl-time collision pre-flight (`fixme-0365-field-accessor-dotted.md`
  §2) all read the entry, not its `fn_state`.

### 2.4 F2's disposition — the ordinary mono path, with the scheme told the truth

Two changes, in this order:

1. **Stop calling `scheme::mono` on a non-concrete `fn_type`.** The impl-method
   scheme must quantify the residual variables it actually has —
   `type_vars = free_vars(fn_type)` after `apply` — so the entry answers `true` to
   `entry_is_monomorphisable_polymorphic` for the honest reason. This is the R-2 fix
   at F2: the scheme stops claiming an absence it does not have.
2. **P-1 then routes it to `Polymorphic(ParametricFn { variant, scheme })`**, whose
   payload is exactly the `(DefnVariant, Scheme)` pair `monomorphise_call` reads
   (`module.rs:2421-2445`) — and the annotated, subst-applied `ast_variant` the site
   already builds is that `DefnVariant`.

From there the existing core applies unchanged: instantiate at concrete argument
types, switch `state.current_module` to the impl-writer's module for the body
re-check (`monomorphisation.md` §3.7 facts 1–3 — the impl method's body resolves in
the writer's import context, which is what `impl_module` already records per
`backend-keyed-consumer.md` §1.1.1), verify, register with a slot.

**The collection seam is the part this ruling does not settle statically.** A
trait-dispatched `Apply` is not a bare-`Var` callee of a name in
`constrained_fn_names`, so `collect_constrained_calls` does not see it; the site
carries `ApplyRef::Dispatch(fq)` and `fq_is_trait_method_decl`
(`mono_collect.rs:977`) already exists to recognise the shape. The design intent is:

> **F2 collection** extends `collect_mono_call_sites` with one more trigger —
> an `Apply` whose `ApplyRef::Dispatch` target resolves to a `Polymorphic` entry and
> whose argument types are all concrete (`local_parametric_call_triggers`, reused
> verbatim) — feeding the **same** worklist and the **same** core. It is a
> successor-discovery widening, not a second entry point (`/arch`'s standing
> Principle-7 ruling, `monomorphisation.md` §3.1).

Whether the existing `drive_call_site_monomorphisation` already reaches some of these
sites once the entry becomes `Polymorphic` is **MEASURE-1** (§7).

### 2.5 The cost, against the measured census

The ruling's censuses partition cleanly by owner:

| Population | Total | Face 1 (backend, I-CT′) | **Faces 2+3 (this obligation)** |
|---|---:|---:|---:|
| Census A — release admissions | 2,497 | 2,216 (89%) | **281 (11%)** |
| Census B — bare `Type::Var` licences | 3,646 | 3,108 (85%) | **538 (15%)** |
| Census B — `ADT(concrete,[Var…])` licences | 1,776 | 1,296 | **480** |
| Census B — `Fn(…)` residual licences | 75 | 20 | **55** |

So this obligation owes **281 release admissions and 1,073 category licences** to
zero. Backend's own instrument (ruling §5.1) reads them, and *the census reading zero
is the acceptance criterion* — the same measure-before-binding discipline, applied to
the producer.

**Code-size cost.** Faces 2/3 trade one body per declaration for one body per
*distinct concrete instantiation*. Three grounds for believing the multiplier is
near 1 in practice, and one honest unknown:

- `Grid.cells`'s 164 measured admissions are 164 *compilations of the same frame*
  across the suite's programs, not 164 instantiations. A `Grid` in the exemplar is
  instantiated at one element type.
- Accessors are the extreme low end: an instance is a one-arm `match` that loads one
  field. A-MINT emits no more per instance than the template emits today.
- The language already pays this multiplier for every ordinary generic `defn`; the
  census's own frame list carries `ct/ap$Fn(Int;ct/Bx$Int)+Int` beside `Bx.v`.
- **MEASURE-2**: the distinct-instantiation count per F1/F2 frame across the corpus
  is not in either census. If some frame instantiates at many types, the growth is
  visible in object size and compile time, not in correctness.

**Precision gain, recorded because it is not free value.** Every F1/F2 call becomes a
statically-resolved call to a concrete instance, which is the exact precondition
`design/arch/ownership-inference.md` §3.1 sets for ABI-bearing per-parameter mode
vectors. Today an accessor call is a call into a frame with no derivable summary; the
`ModeSummary` on the instance is derivable. This is one class of the "advisory-only"
residue shrinking.

### 2.6 What must NOT change (the `/review` fence for this obligation)

1. **No `cranelisp-types` delta, no public-API delta.** `Polymorphic`,
   `ParametricFn`, `VarRef`, `ApplyRef`, `MonoDefn` all exist; the mangler exists;
   `mangle_trait_method` is unchanged. If `/dev` finds an unavoidable boundary need,
   that is a FIXME `target: /arch`, never a quiet edit (`monomorphisation.md` §3.6).
2. **No second mangle grammar** (P-2), and specifically no `$Type$Arg` widening of
   `mangle_trait_method`.
3. **No accessor body re-check** (A-MINT), and no routing of a real check-run body
   through `synthetic_local_from_expr` — the always-on synthetic-span assert exists
   to catch exactly that (`cranelisp-types/CLAUDE.md` §Public-surface mechanics).
4. **A concrete product's accessor and a concrete impl method are byte-identical to
   today.** The gate is a new *arm*, not a new path; `Tally.passed` and
   `Show.show$primitives/Int` keep their slot, their body, their view and their CLIF.
   A golden-CLIF diff outside the F1/F2 frames is a finding, not a re-baseline.
5. **The §8.6.5 bare-alias contest, the `Ambiguous` poison, and the impl-time
   collision pre-flight are untouched.** They read the canonical entry, not its
   `fn_state`.

---

## 3. FIXME 0913 — the lenient view stops fabricating (contract face 5)

### 3.1 What the ruling requires, and what it forbids

The ruling §5.4 is specific, and it is **not** what 0913's own text implies. The
lenient view must **default unconstrained parameters — explicitly and checkably —
and never substitute the node's type**:

- forbidden: `(Result a String)` ⇒ `Int`. That does not default a parameter; it
  discards the type constructor, and with it every concrete argument. Backend then
  sees a scalar and emits nothing.
- permitted: `(Result a String)` ⇒ `(Result <default> String)`. The constructor
  survives, `String` survives, and only the *position* nothing inhabits is filled.

### 3.2 The licence, and its fence

The ruling's soundness argument — *a parameter still free after inference is a
parameter no value in the released graph inhabits, because a value of that type would
have pinned it* — is correct **and is not universally applicable**. It has one
genuine counter-shape, and the fence must be stated before the rule, or the fix
converts a leak into a wrong release:

> A **multi-sig `f$Var` variant** body carries residual parameters that a *caller*
> instantiates. A value of that type demonstrably exists at runtime — it is the
> argument. Defaulting there would tell backend the parameter is a scalar while the
> caller passes a heap value, and the payload would be silently under-discharged.

The discriminator is *who can supply a value at that type*:

> **L-1 (the licence).** A residual type parameter of node `n` in frame `F` may be
> defaulted iff the residual variable **does not occur in any of `F`'s declared
> parameter types**. Nothing outside `F` can then supply a value inhabiting it, so
> no value of that type exists in the graph `F` releases.
>
> The guaranteed-covered subset, and the whole of 0913's measured population, is
> **`F` is nullary** — `__expr` (every REPL turn) and `main`. The general form is
> stated because it is the honest statement of the property; the nullary case is
> the one `/dev` must cover and the one `/qa` asserts.

L-1 also disposes of the interior-node worry. `(let [e (vec)] (Err "boom"))` binds
`e : (Vec a)` — residual, and `e` *is* a real allocation that must be released. It is
defaultable, and `(Vec Int)`'s glue frees the buffer with no element discharge, which
is correct because **a container at an un-unified element type is necessarily empty**:
inserting an element would have unified the parameter. That is the same argument, one
level in, and it is why the rule is about the parameter rather than about the root.

> **L-2 (the shape).** Defaulting is defined only for a type whose **root is a type
> constructor** (`Type::ADT` / `Type::Fn`). It replaces each residual argument
> position strictly *below* the root with the declared default, preserving the
> constructor and every concrete argument, recursively.
>
> A type whose **root is itself residual** (`Type::Var` / `Type::TyConApp`) is **not
> defaultable**: there is no constructor, therefore no category, therefore no glue —
> R-1 exactly. It is left for §3.5.

> **L-3 (the check the narrowing carries — Principle 25).** Defaulting refuses, with
> a **located error**, if the residual variable appears in the enclosing scheme's
> `constraints`. Choosing `Int` for a variable carrying `Eq a` is choosing a trait
> instance, which is fabrication of a different kind. This is the one case the
> ruling names as "a defaulting applied to a *constrained* parameter is a
> fabrication and must be a located error".

**The default itself** is `ConcreteType::Int` — a declared `NeverHeap` type, per the
ruling's own wording. The value is the same token the fabrication used; the
difference is everything about *where* it is applied and *what carries it*. To keep
that difference legible rather than a comment, the default is reached only through a
single named operation (§6.2) and never through an inline `unwrap_or`.

### 3.3 The mechanism — and the property that makes it self-checking

The defaulting is a **typecheck operation**, not a `cranelisp-types` walk change, for
one decisive reason: the checks L-1 and L-3 need the frame's declared parameter types
and the enclosing `Scheme`, and `lenient_from_expr` has neither. It has an `Expr` and
three sidecars. Putting the decision there would be a second derivation of a question
typecheck has already answered — the §4.1 rule that produced this defect in the first
place.

The seam is `program/support.rs::build_concrete_codegen_view`, the **single**
production producer of the lenient view (`:307`), on the `NotConcrete` arm:

```text
from_expr(variant.body, …)
  Ok(view)                  -> strict view                     (unchanged)
  Err(Unresolved{..})       -> located typecheck error         (unchanged)
  Err(NotConcrete(_))       -> NEW: defaulted = default_residual_parameters(variant, scheme)?
                               from_expr(defaulted.body, …)
                                 Ok(view)     -> strict view over defaulted types
                                 Err(NotConcrete(_)) -> lenient_from_expr(defaulted.body, …)
                                                        + census (§3.5)
                                 Err(Unresolved{..}) -> unreachable; defaulting touches types only
```

`default_residual_parameters` clones the annotated variant and rewrites the
`inferred_type` of every node whose type fails `ConcreteType::from_type`, under L-1 /
L-2 / L-3. **It rewrites the clone, never the stored `ast`** — the spec-required
residual-parameter displays (`repl/spec.md` §1.5 / §4.1) read the real type and stay
byte-identical. The ruling is explicit that the displays are right and the release
behind them is not.

> **The self-check.** Defaulting's success criterion is that **the strict builder
> then accepts the body**. That is Principle 25 realised structurally rather than
> asserted: a defaulting that left a residual anywhere does not silently pass — the
> strict walk rejects it and the residual falls to §3.5's counted arm. The
> narrowing carries its check because the check is the next line.

A second property worth naming: after this lands, the lenient walk's traffic is
**exactly** the population defaulting could not reach. That makes §3.5's census
cheap and exact, where today the lenient arm's traffic is a mixture of legitimate and
defective misses with no way to tell them apart.

### 3.4 Why this closes the leak end-to-end, with no other crate touched

`__expr`'s body type becomes `(Result Int String)` in the codegen view. Backend's
`compile_to_module` keys `result_roots` off that view's body type — so it now derives
canonical glue for `(Result Int String)`. Int's `release_key`
(`src/result_owner.rs:337`) takes the same `codegen_result_ty` it already takes,
narrows it identically, and requests the glue backend emitted. The `Err` arm's
`String` is discharged; the `Ok` arm carries the defaulted parameter and is
**unreachable for this value** — the tag says `Err`. The defaulted position is typed
out of the walk, not walked with a wrong type.

| Consumer | Delta |
|---|---|
| `cranelisp-types` | **none** — no new variant, no signature change; `lenient_from_expr` untouched |
| `cranelisp-backend` | **none** — it derives glue for whatever `ConcreteType` it is handed |
| `src/` (int) | **none** — `release_key`'s authority order is already right; only the value it reads changes |
| public API | **none** — `build_concrete_codegen_view` is `pub(crate)` |

### 3.5 The residual — counted, not hidden

An `L-2`-inadmissible node (residual **root**) keeps a placeholder, because
`lenient_from_expr` returns a total `MonoExpr` and widening it to a `Result` is a
`cranelisp-types` signature change this sprint does not authorize. The ruling forbids
papering that over, so it gets the treatment backend gave its own fabrication
(§5.1) — **the arm becomes the gate on its own removal**:

1. the lenient fallback records every admission it makes after defaulting, keyed by
   frame and type shape, in a permanent debug-profile census (the 0768 rule: an
   instrument is unverified until it has detected);
2. the census's expected population shrinks as faces 1–3 land — census B's 3,646
   bare-`Var` licences are exactly the frames that produce residual roots, and 85% of
   them are backend's face-1 deletion;
3. when the census reads zero across the corpus, `node_ty`'s `unwrap_or` and the
   lenient fallback arm both become located errors. That flip is a later sprint's,
   and it is a `cranelisp-types` change (`/arch`).

Recorded honestly: this leaves a bounded residual behind 0913's fix. It is strictly
smaller than today's (which is *every* non-concrete node), it is visible rather than
silent, and it has a stated removal criterion. `/review` reject criterion 6 of the
ruling applies — no `#[ignore]` on anything this leaves.

---

## 4. Rider 0867 — the gating answer

**The question `/arch` asked:** does 0867 become safe to land once the obligation is
*designed*, or must it wait for the obligation to be *implemented*?

**Ruled: it must wait for implementation — but only for the gate half, not the whole
obligation.**

### 4.1 Why the design alone is not enough

0867 widens accessor synthesis from the deftype-level field list to *every*
constructor arm — every sum type and every distinct-name product. `/stdlib`'s blast
radius (appended to 0867) names five stdlib types gaining 13 canonical accessors, and
**four of the five are polymorphic**: `collections.list/List`, `seq.lazy/Seq`,
`collections.either/Either`, plus the FIXME's own `(Pair a b)` shape. Every one of
those mints a new `Concrete { got_slot }` over a non-concrete scheme — a new member of
census B's bare-`Var` licence population and census A's F1 family, i.e. a new
memory-unsafe frame at the 1023/1024 boundary.

A design does not shut that door. The mint site does. Landing 0867 first manufactures
new members of a class whose disposition exists only on paper, which is precisely
what SPRINT.md §Must-not-interleave forbids.

### 4.2 Why the *whole* obligation is not required either

P-1 (§2.1) and the coverage widening (§2.4/§6.1) are separable, and the separation is
load-bearing:

> Once **P-1 alone** has landed at the accessor mint site, a polymorphic accessor is
> slot-less. A use the mono pass fails to reach then produces a **missing-slot
> located failure**, not a SIGSEGV. That is the S84 forcing-function property
> (`monomorphisation.md` §3): *a missed reachable instance is a hard failure, not a
> silent unsound fallback.*

So the memory-unsafety of 0867's widening is closed by the gate, independently of
whether coverage is complete. Coverage completeness is what turns a hard failure into
a working program — a functionality gate, not a safety gate.

**Ruling.** 0867 is safe to land as soon as **P-1 has landed at
`adt.rs::synthesise_one_accessor`** — a same-file, few-line change that can be the
first commit of 0924's change-set and can be the first commit of 0867's. It is
**not** safe to land before that, and it does not need to wait for F2, for the
collection widening, or for the census to read zero.

Recommended sequencing, which also removes an interleaving hazard the sprint plan
does not yet name: **land P-1-for-accessors and 0867 in the same change-set.** They
touch the same function; splitting them means two passes over
`synthesise_field_accessors` in one sprint, and the second would re-open the first's
review surface. The partial-accessor panic face 0867 owes its own cells for is on the
mono instance's body, which is exactly the code A-MINT produces.

### 4.3 What `/qa` should assert, either way

Three cells. The first is the corpus **extension clause** `/qa`'s plan already
carries; this section gives it a shape.

1. **The safety extension (extension clause, post-0867).** The four-line accessor
   repro `/testing` owes for §2.4 of the ruling, extended to a **sum-type arm**
   accessor — the family 0867 newly mints:

   ```lisp
   (import [primitives [IO Pure]])
   (deftype (Mb a) Nn (Jj [:a v]))
   (defn get [m] (v m))
   (defn main [] (Pure (get (Jj 1024))))
   ```

   A/B on the payload: `1023` exits 255, `1024` must not SIGSEGV. Before 0867 the
   program does not compile (nothing mints `v`), so the cell is *authored with*
   0867's change-set and is RED-then-GREEN in one commit — which is the correct
   shape, because 0867 is the thing that makes the surface reachable.

2. **The gate cell (typecheck unit tier).** Sibling to the existing slot-gate pins in
   `program/finalize/tests.rs`: a **polymorphic** product's / sum arm's accessor
   entry is `UserFnState::Polymorphic` and `callable_got_slot()` is `None`; a
   **concrete** product's accessor is `Concrete { got_slot }`. This is the assertion
   that survives 0867 landing early *and* the one that fails loudly if a future
   change re-opens the mint. It is cheap and it is the real fence.

3. **The stdlib widening cell** `/stdlib` asked for and that nothing else covers: one
   module `[*]`-importing **both** `collections.list` and `seq.lazy`, exercising the
   cross-module bare-alias contest on `head` (minted bare by both) and `rest` (minted
   bare by `seq.lazy`, already a `defn` in `collections.list`). Orthogonal to the
   memory-safety axis, but it is 0867's own regression risk and `stdlib_conformance`
   structurally cannot see it (it imports each module separately).

---

## 5. What `/arch` must take at the Phase-3 exit gate

**Zero public-API delta** for `cranelisp-typecheck`, as backend expected for Spine 1.
Confirmed by construction: every type this obligation needs (`UserFnState::Polymorphic`,
`ParametricFn`, `VarRef`, `ApplyRef`, `MonoDefn`, `ConcreteType`) is already public
and already carried; `build_concrete_codegen_view` and the mangler are `pub(crate)`;
`mangle_trait_method` keeps its grammar. **No `cranelisp-types` delta.**

**One thing `/arch` must rule, and it is not optional:**

> ### The schema window. Both halves of this obligation are cache-visible *meaning*
> changes, and a stale sidecar silently re-introduces the defect they fix.

- **0924.** An accessor / impl-method entry that used to serialise
  `Concrete { got_slot }` now serialises `Polymorphic`, and a new population of mono
  instances appears under new keys. A cache built by the pre-fix compiler restores an
  accessor as `Concrete { got_slot }` — the new compiler then compiles the template
  frame again, on a cache hit, with the residual types. **The memory-unsafety returns
  on warm cache.**
- **0913.** `Def.codegen_view` is serde-visible. A stale sidecar restores the
  `ConcreteType::Int` body types, backend derives no glue, and **the leak returns on
  warm cache.**

Per `crates/cranelisp-types/CLAUDE.md` §"The serde shape IS the cache contract", *"a
meaning change to what an existing field records"* bumps `CACHE_SCHEMA_VERSION` in the
same change-set. SPRINT.md §Must-not-interleave authorizes **exactly one window
(23→24), owned by 0869's change-set**. This is a genuine collision and I am not
authorized to resolve it.

**What `/design`(typecheck) recommends, with reasoning, for `/arch` to rule:**

| Option | Assessment |
|---|---|
| (a) 0924 + 0913 ride 0869's 23→24 window | Forces the typecheck producer work into 0869's `/dev`(src) change-set, which is rider 2 and sequenced *after* tranche A. It couples a memory-safety fix to a cache-restoration fix in one commit, and it is the interleaving the sprint forbids everywhere else. **Not recommended.** |
| (b) **One additional increment, shared by both typecheck producer changes** — whichever of 0924 / 0913 lands first takes it; `/arch` assigns the numbering relative to 0869 | The two typecheck changes are one producer surface and can share one bump. Cost is one extra wholesale cache invalidation. The one-window rule exists to prevent *silent* divergence between two change-sets each assuming it owns the bump — not to cap the count at one when two independent correctness fixes each require one. **Recommended.** |
| (c) Defer 0924's implementation to S120 | Also defers 0916 (×1 RED) and 0867 (×3 RED), i.e. four of the sprint's twenty-one. Available, and honest, if `/arch` judges the window contention worse than the carry. |

Nothing else in this ruling needs `/arch`. The IO tri-context seam (0923) and the
`safety-invariants.md` R-1/R-2 rows are backend's asks, already filed.

---

## 6. Implementation obligations for `/dev`(typecheck)

Ordered. Each change-set carries its unit rows (§6.4) and, per root `CLAUDE.md`
§Testing, the failing test(s) are written **first**.

### 6.1 CS-1 — P-1, the universal slot gate (safety; unblocks 0867)

- Hoist slot allocation + `Concrete { got_slot }` construction behind **one**
  helper — working name `determine_callable_state(scheme, variant, table) ->
  UserFnState` — that applies `scheme.ty.is_concrete()` and returns
  `Concrete { got_slot }` or `Polymorphic(ParametricFn { variant, scheme })`. Point
  `adt.rs:618-637` and `impl_check.rs:1078-1090` at it. The `finalize.rs`
  determination points already implement this decision; converging them onto the same
  helper is the Principle-7 half and is the shape that makes a *fourth* mint site
  structurally impossible to get wrong.
- At F2, replace `scheme::mono(fn_type)` with a scheme quantifying `fn_type`'s free
  variables (§2.4 item 1). `scheme::mono`'s other callers are unaffected; its rustdoc
  should say that it asserts absence of quantification, **not** concreteness.
- At F1, move `allocate_got_slot()` and the `synthetic_local_from_expr` view-build
  inside the concrete arm (§2.3).
- **Acceptance:** the §4.3 gate cell; zero golden-CLIF movement for concrete
  accessors and concrete impl methods; the previously-passing programs that call a
  polymorphic accessor or a generic impl method now fail **loudly** (missing slot) if
  coverage has not landed — that is expected, is the forcing function, and is why
  CS-1 and CS-2 land in the same wave even though they are separate commits.

### 6.2 CS-2 — coverage: A-MINT + the F2 trigger

- **A-MINT** (§2.3): an accessor-instance minter keyed by `build_mangled_name`, fed
  from the mono worklist, substituting through the instantiation and re-running the
  synthesiser's derivation. `debug_assert!` the minted scheme `is_concrete()`.
- **F2 trigger** (§2.4): extend `collect_mono_call_sites` with the
  `ApplyRef::Dispatch → Polymorphic` case, reusing `local_parametric_call_triggers`
  verbatim. Rewrite the site's `ApplyRef::Dispatch` to the instance's `FQSymbol`.
- **Cluster-level dedup** on the mangled key, unchanged (`monomorphisation.md` §3.5).
- **Cross-cluster / REPL:** an accessor is minted at `deftype` time in a *prior*
  cluster; the demanding call site is in a later one. That is the
  `collect_imported_constrained_calls` cross-module shape, and
  `monomorphisation.md` §3.7's three scoping facts apply verbatim to F2. A-MINT is
  immune (it re-derives rather than re-checks) — say so in the change-set so
  `/review` does not look for a home-switch that is deliberately absent.
- **Acceptance:** backend's census instrument reads **zero** for the F1 and F2
  partitions (281 admissions, 1,073 licences); **zero new refusals** across the
  16-program corpus; 0916's cell flips; the `f4_sudoku.clif::user::Grid.cells` golden
  re-baseline, scoped and attributed in this change-set per
  `ownership-inference.md` §6.2 (extension ≠ re-baseline).

### 6.3 CS-3 — 0913, the defaulting step

- `default_residual_parameters(variant, scheme) -> Result<DefnVariant, CranelispError>`
  in `program/support.rs` beside its one caller. L-1 / L-2 / L-3 as written.
  **One named home for the default value** — no inline `unwrap_or(Int)` anywhere.
- Wire it into `build_concrete_codegen_view`'s `NotConcrete` arm, followed by the
  strict re-run (§3.3).
- Land the lenient-fallback census (§3.5) in the same change-set, with its detection
  proof — per the 0768 rule the instrument is unverified until it has fired, and the
  residual-root population gives it something to fire on.
- **Acceptance:** `tests/residual_type_param_result_leak_0913.rs::unannotated_result_turn_releases_like_its_annotated_twin`
  reads an exact marginal 0. **Not** closed by adding an annotation anywhere.
  `repl/demos/memory-lifecycle.demo`'s narration flips (it is a demonstration, not the
  guard). The `(Ok x)`, `(Ok 1)` and `(vec)` rows of 0913's matrix follow the same
  seam; `None` needs no cell (nullary, cannot leak).

### 6.4 Unit-test design (typecheck tier)

Rows placed beside their production owner per the crate `CLAUDE.md` sibling
convention.

| Submodule | Complexity / positive | Edge | Negative |
|---|---|---|---|
| `adt::synthesise_one_accessor` | a concrete product's accessor is `Concrete{slot}` with a `codegen_view`, byte-identical to today | a polymorphic product's accessor is `Polymorphic`, **no slot allocated**, no view built | the bare-alias `Import`, the `Ambiguous` poison, and the cross-cluster `committed_accessor_kind` classification are unchanged for **both** arms — a `fn_state` change must not perturb the §8.6.5 contest |
| accessor A-MINT | one instance per distinct `(fqtn, field, concrete args)`; scheme `is_concrete()`; view built by `synthetic_local_from_expr` | two distinct instantiations of one accessor mint two distinct mangled keys; an identical re-reach dedups to one | the minter never consults a span-keyed sidecar; a non-concrete instantiation is **not** minted (it is deferred, per `monomorphisation.md` §3.3's residual-`Var` defer) |
| `traits::impl_check` scheme | a **concrete** impl method (`Show.show$primitives/Int`) is `Concrete{slot}`, identical to today | a residual impl method quantifies its free vars and is `Polymorphic(ParametricFn)` | `scheme::mono` is not called on a non-concrete `fn_type` at this site; `mangle_trait_method`'s output is **unchanged** for every input (the template key is stable) |
| F2 collection | a dispatched call at concrete arg types mints one instance under `build_mangled_name` and rewrites `ApplyRef::Dispatch` | the `b`-from-argument case: `(fmap show …)` and `(fmap inc …)` over the same receiver mint **distinct** names (the §2.2 collision the rejected spelling would have merged) | no second mangle grammar appears; no `$Type$Arg` key is minted anywhere |
| `support::default_residual_parameters` | `(Result a String)` ⇒ `(Result Int String)`; `(Result String a)` ⇒ `(Result String Int)`; `(Vec a)` ⇒ `(Vec Int)`; concrete arguments preserved at every depth | nested: `(Result (Vec a) String)` defaults only the inner position; a fully-concrete body is a no-op and the strict walk was already taken | **the type is never replaced** — no input yields a bare `Int` from a constructor-rooted type; a bare `Type::Var` root is **not** defaulted (L-2); a variable in `scheme.constraints` is a **located error** (L-3); a residual occurring in a declared parameter type is **not** defaulted (L-1) |
| lenient-fallback census | records a residual-root admission with frame + shape | the detection proof: a deliberately residual-rooted fixture makes it fire | after defaulting, a constructor-rooted residual **never** reaches the lenient arm |

---

## 7. What this ruling does not settle (measurement-gated)

Stated rather than guessed, per the sprint's measure-before-binding discipline. Each
needs a build/test slot `/sprint` sequences.

- **MEASURE-1 — F2 collection reach.** Once an impl-method entry is `Polymorphic`,
  how much of the F2 call population does the *existing*
  `drive_call_site_monomorphisation` already reach, and how much needs the §2.4
  trigger? The answer sizes CS-2. My reading of `mono_collect.rs` says the trait
  dispatch shape is not currently collected (the callee is not a bare `Var` in
  `constrained_fn_names`), but the `fq_is_trait_method_decl` helper's existing
  callers may already cover part of it.
- **MEASURE-1b — F1 collection reach, and why the four-line repro escapes today.**
  `entry_is_monomorphisable_polymorphic` already answers **true** for a polymorphic
  accessor (honest `type_vars`, `ast.is_some()`), so `collect_local_parametric_calls`
  ought to reach `(v b)` — yet the census shows `Bx.v` compiled with residual types.
  The likely explanation is that in the repro the accessor call sits *inside a mono
  instance's re-checked body*, where successor discovery is
  `monomorphise_inner_parametric_hops`'s narrower walk rather than the top-level
  collector. The discriminating A/B is cheap and worth running before CS-2 is
  written: pin `get`'s parameter (`(defn get [b :(Bx Int)] (v b))`) so the accessor
  call is collected at the ordinary pass-4 seam, and see whether the SIGSEGV
  disappears. If it does, CS-2's F1 half is a successor-discovery widening only, not
  a new collector.
- **MEASURE-2 — instantiation multiplier.** Distinct instantiations per F1/F2 frame
  across the corpus. Neither census carries it, and it is the only real cost axis
  (§2.5).
- **MEASURE-3 — the corpus gate.** Zero new refusals across the 16 programs named in
  FIXME 0903, per-program table recorded. The ruling was falsified twice by exactly
  this measurement; the producer half is not exempt from it.

---

## 8. Quality attributes

- **Simplicity.** Net deletion of decision sites. Retired: two hand-rolled
  `Concrete { got_slot }` mints, `scheme::mono` over a non-concrete type, one
  premature `allocate_got_slot()` per polymorphic accessor, one premature
  `codegen_view` build, and `node_ty`'s unconditional `unwrap_or`. **Added: one
  gate helper, one accessor-instance minter, one defaulting function, one census.**
  The gate helper is a *convergence* of three existing decision points, so the count
  of places that decide "is this callable concrete?" goes from four to one.
- **Maintainability.** A fourth mint site becomes structurally hard to get wrong:
  the only way to obtain a slot is through the gate. Today the invariant is a
  property of one function in `finalize.rs` that two other files quietly violate —
  which is how this class survived from S84 to S119.
- **Observability.** Two censuses, at both ends of the same question: backend's
  category-licence instrument reads the *consequence*, this crate's lenient-fallback
  census reads the *residue*. Both are permanent, debug-profile, and both are their
  own removal criterion. Before this sprint neither side could prove the fabrication
  had no traffic.
- **Testability (Principle 5).** The gate cell (§4.3 item 2) is a pure unit
  assertion on an entry's `fn_state` — no program run, no allocator counters, no
  1024-boundary. It is the cheapest possible guard for the most expensive possible
  defect, and it is what makes 0867's early landing assessable rather than hoped.
- **Performance.** One body per instantiation instead of one per declaration; the
  multiplier is MEASURE-2 and is expected near 1 for accessors. Offset: 2,216+ fewer
  compiled template bodies once faces 1–3 are complete, and the precision gain in
  §2.5 (statically-resolved calls acquire derivable mode summaries).
- **Concurrency-safety.** Untouched. No new shared state; A-MINT is a pure function
  of its inputs; the defaulting operates on a clone.

---

## 9. Cross-references

- `design/backend/non-concrete-release-contract.md` — R-2, R-3, §4 faces 2/3/5,
  §4.3 (the impossibility proof), §5.2, §5.4, §7 (staging), §8 (reject criteria)
- `monomorphisation.md` §1 (slot ⟺ concrete), §2 (the gate), §3.1/§3.3/§3.5/§3.7
  (the spine this extends), §4 (the ambiguity backstop, unchanged by this ruling)
- `adt.md` §"Product Type Handling"; `fixme-0365-field-accessor-dotted.md` §1.6/§2
  (the canonical/alias model this ruling does not touch)
- `design/int/result-owner.md` §1.1.1 — the mis-scoped record 0913 corrects
  (`/design`(int) owns the correction; the corrected axis is §1.3 above)
- `design/arch/ownership-inference.md` §3.1 — the precision gain in §2.5
- `design/arch/principles/{07,18,20,24,25,26}` — Principle 25 is the spine of §3.2's
  fence and §3.3's self-check

## Next skills

- **`/arch`** — Phase-3 exit gate, one item only: the **schema window** (§5). Zero
  public-API delta and zero `cranelisp-types` delta from this crate are confirmed by
  construction; the cache-meaning change is real and a stale sidecar re-introduces
  both the memory-unsafety and the leak.
- **`/qa`** — the three §4.3 cells (the sum-arm safety extension for the corpus
  extension clause, the gate cell, the stdlib cross-module bare-alias cell), plus the
  §6.2 acceptance form (census zero for the F1/F2 partitions, zero new refusals) and
  the §6.3 marginal-0 form for 0913.
- **`/testing`** — the §2.4-of-the-ruling four-line accessor repro (`1023` GREEN /
  `1024` SIGSEGV) is still unguarded and is the cheapest memory-safety cell in the
  class; it is the *precondition* for CS-1's acceptance, not a follow-on.
- **`/dev`(typecheck)** — CS-1 → CS-2 → CS-3 in §6, after `/arch` rules the window.
  CS-1 is what unblocks rider 0867, and §4.2 recommends landing them together.
- **`/sprint`** — three scheduling findings: 0867 unblocks on **CS-1**, not on the
  whole obligation (§4.2); the schema window is contended (§5); and MEASURE-1b is a
  cheap A/B worth a slot **before** CS-2 is written (§7).
