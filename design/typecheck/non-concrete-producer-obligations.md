# The non-concrete producer obligations — typecheck's half of the release contract

**Status:** CURRENT — authored S119 Phase 3 round 2, re-grounded S121 Phase 3 on the
adopted unified lifecycle, and verified as built in S122 on 2026-09-10. Sections 1–7
retain the implementation rationale; §8 records the current source-backed disposition.
**Subordinate to:** `typecheck.md` §9.3 / §9.4 / §9.8. Extends `monomorphisation.md`
§1–§3 and `adt.md` §"Product Type Handling".
**Governed by:** `design/arch/symbol-table-lifecycle.md` §§3–7 (the current
representation, enforcement and residual limits), and
`design/backend/non-concrete-release-contract.md` R-2, R-3,
§5.2, §5.4 (the release contract). Where this doc and either ruling disagree, the
ruling wins.
**Resolves (typecheck side):** FIXMEs **0924**, **0913**, **0935**. The former
rider **0867** is retired by the 2026-09-02 product-only accessor ruling;
supplies the producer gate for **0916** and the typecheck arm of the **0929** census.
**Consumes, does not decide:** the `Life`/`Realization`/`MonoDemand`/`InstanceLink`
shapes, the `retired_slots` authority, and the one `CACHE_SCHEMA_VERSION` 24→25 window
— all C1's.

---

## 0. The one sentence

Four sites in this crate hand a downstream gate a callable whose type is less concrete
than the state they mint claims, and one more does the same for a *value*. All five are
the same defect at different altitudes, and under the C1 machine four of them stop being
expressible at all.

| # | Site (verified at HEAD 2026-09-01) | What it fabricates | Altitude |
|---|---|---|---|
| **F0** | `adt.rs:172-181` — ctor slot pre-allocation inside `AdtCtorSpec::new` | a slot for a generic ADT's constructor, whose scheme is not `is_concrete()` | frame |
| **F1** | `adt.rs:617-637` — `synthesise_one_accessor`'s canonical mint | `UserFnState::Concrete { got_slot }` over `∀a. (Fn [(Bx a)] a)` | frame |
| **F2** | `impl_check.rs:1039-1043` + `:1078-1089` — `check_impl_method` | `scheme::mono(fn_type)` over a `fn_type` still carrying `Type::Var`, then the same pairing | frame |
| **F3** | `monomorphise.rs:667` + `:680-697` — `register_mono_entry` | `scheme::mono(fn_ty)` with **no** concreteness gate, then a hand-allocated slot | frame |
| **F5** | `mono_expr.rs:848-852` — `lenient_from_expr`'s `node_ty`, reached from `support.rs:321-328` | `ConcreteType::Int` for any node whose real type is not concrete | value |

R-2 ("no fabricated concreteness") is Principle 25 applied to the type channel, and none
of the five carries its check.

**What changed since S119, and why it makes this cheaper.** S119 named F1 and F2 and
proposed converging them, plus `finalize.rs`'s determination points, onto one typecheck
helper. Two things are now true that were not:

1. **The source census was incomplete.** F0 and F3 are two further literal mints of the
   same pairing. A helper convention that three sites opt into would have left two more
   outside it — the exact failure mode `monomorphisation.md` §1's S119 amendment was
   written about, repeated.
2. **C1 removes the convention.** `symbol-table-lifecycle.md` §4.4 makes `symbols`
   private and `Life::Concrete` constructible **only** by `settle_concrete`, which checks
   `is_concrete()`, accepts the view, and mints-or-rebinds the slot in one act. There is
   no longer a decision for a fifth site to get wrong, because there is no longer a way
   to construct the state. `allocate_got_slot()` as a free capability disappears.

So **P-1 stops being a typecheck rule and becomes a C1 representation.** This crate's
obligation shrinks accordingly, from *enforce the gate at N sites* to *route N
populations through the funnel and delete the hand-mints*. That is the whole of §2.

---

## 1. What was verified at source (the binding first act)

Read at HEAD 2026-09-01 (S121 Phase 3), design-window only, no build run. Every line
citation below was re-read this window; where S119's citation had drifted, the live line
is given and the drift noted. Claims that need a run are marked **MEASURE** in §8.

### 1.1 F0 — the constructor mint

`adt.rs:136` computes `is_product` (`ctor_infos.len() == 1 && ctor_infos[0].name == name`).
`adt.rs:172-181` then pre-allocates a GOT slot per constructor inside `AdtCtorSpec::new`,
unconditionally — a generic ADT's constructor is slotted exactly as a concrete one is.
This is FIXME **0931**'s subject and its disposition is C1's (the ctor is born settled
through the funnel, `symbol-table-lifecycle.md` §5.8: concrete ADT ⇒ `Concrete`, generic
ADT ⇒ `Template { body: Synth(SynthSpec) }`). C3 owns the *call site*: the
`allocate_got_slot()` here is deleted and the spec is handed to the funnel.

### 1.2 F1 — the accessor mint

`adt.rs:237-250` is the sole call site of `synthesise_field_accessors` (`adt.rs:405`),
guarded by `is_product` and applied to the product's lone constructor. Under the
2026-09-02 ruling this is the required semantic boundary: sum payload labels
mint no accessor and are extracted by `match` (§4).

Inside, `adt.rs:607-613` builds the accessor's `codegen_view` through
`MonoExpr::synthetic_local_from_expr` over a hand-seeded `pattern_ctors` map
(`:599-606`), and `adt.rs:617-637` allocates a slot and mints
`UserFnState::Concrete { got_slot: canonical_slot, mode_summary: None }` with
`Visibility::Public`. For `(deftype (Bx a) [:a v])` the scheme is `∀a. (Fn [(Bx a)] a)` —
`type_vars` non-empty, `ty` not concrete — minted `Concrete` unconditionally. A
**concrete** product mints `type_vars: []` over a concrete `ty` and is correct today; the
exemption is polymorphic-only, which is why the four-line repro needs a type parameter
and nothing else.

### 1.3 F2 — the trait-impl method mint

`impl_check.rs:1039-1043`:

```rust
let fn_type = apply(&state.subst, &Type::Fn(param_types.to_vec(), Box::new(ret_ty.clone())));
let concrete_scheme = crate::scheme::mono(fn_type);
```

`scheme::mono` sets `type_vars: vec![]` and copies `ty` verbatim; the adjacent rustdoc
(`:1048-1050`) *acknowledges* that the apply "can legitimately leave a residual var".
**The name `mono` is the fabrication** — it asserts an absence of quantification, and
`:1078-1089` reads that absence as concreteness and hand-allocates a slot.

Two downstream consequences, both measured in the release contract:

- `entry_is_monomorphisable_polymorphic` (`mono_collect.rs:695-716`) tests
  `!scheme.type_vars.is_empty()`, so an F2 entry answers **false** and no call site ever
  specialises it. F1 answers **true** (its `type_vars` are honest) yet is still compiled
  as a template because the slot exists — two families, opposite routes, one bad frame.
- The instance name is `mangle_trait_method(trait, method, fq_type)` (`traits/mod.rs:74`)
  = `"{Trait}.{method}${fq_type}"` — keyed on the type **constructor**, arguments erased.
  One body per `(trait, method, type-constructor)`, whatever the instantiation.

**Correction to S119's F2 reading.** S119 cited `impl_check.rs:1029`'s
`mangle_trait_method(&impl_.trait_name.to_string(), …)` — the as-written `TraitRef`
spelling. **That is gone.** The S117 qualified-trait-impl design landed: both mangle
sites (`:945-949`, `:1309-1313`) take `fq_trait_name.name`, and `:728`'s rustdoc states
*"the as-written `impl_.trait_name` is never a mangle input."* This is FIXME **0794**'s
central claim, falsified at source — see `qualified-trait-impl.md` §7.

### 1.4 F3 — the mono-instance mint

`monomorphise.rs:667` builds the instance scheme with `crate::scheme::mono(fn_ty)` and
**no** concreteness gate; `:680-697` reads any pre-existing `callable_got_slot()` and
otherwise hand-allocates. The instance *is* concrete on every path the §9 gate
(`monomorphisation.md` §9.3) admits, so this site is not a live defect — but it is a
fourth literal construction of the pairing, and it is the site a future partial mint
would land on. It routes through the funnel like the rest, and its `debug_assert!`
becomes the funnel's own check.

Adjacent, and deleted by C1 rather than fixed: `monomorphise.rs:1188-1197` synthesises a
`ConstrainedFn { variant, scheme }` out of a merely-*parametric* entry —
`ast.as_ref().unwrap()` — because there is no state that says "parametric template with a
body". `Life::Template { body: Ast(variant), kind: Parametric }` **is** that state, so the
synthesis and the `unwrap()` both go.

### 1.5 F5 — the lenient view

`crates/cranelisp-types/src/mono_expr.rs:848-852`:

```rust
let node_ty = |e: &Expr| -> ConcreteType {
    e.inferred_type().and_then(|t| ConcreteType::from_type(t).ok()).unwrap_or(ConcreteType::Int)
};
```

The single production producer of the lenient view is
`program/support.rs::build_concrete_codegen_view` (`:307-313`) — shared by the single-sig,
multi-sig-mangled and trait-impl-method population sites — on the
`Err(ViewBuildError::NotConcrete(_))` arm at `:321-328`. `adt.rs`'s synthetic bodies take
`synthetic_local_from_expr` instead and are outside this seam. The `Unresolved` arm
(`:329-345`) propagates a located error and is unchanged.

For a REPL turn the body is `__expr`'s, its root type is `(Result a String)`,
`ConcreteType::from_type` fails on the residual `a`, the whole type is replaced with
`Int`, backend requests no glue for an `Int` root, and the result tree is never released.
Int's behaviour is correct given what the producer published; the producer published a
fiction.

`mono_expr.rs:827-839`'s own rustdoc already schedules this builder's deletion —
*"(3) end state (S121, census-gated): this builder DELETES"*. It is a `cranelisp-types`
item, so the deletion is C1/`arch`'s, not C3's; §3.6 states the trigger C3 owes it.

**Two owned defects found in this crate while verifying, recorded rather than left:**

1. `support.rs:273-276` rustdoc claims the helper *"Always returns `Some(view)`"*, while
   its signature is `Result<Option<_>, _>` and callers (e.g. `impl_check.rs:1051-1060`)
   branch on `None`. The claim is false and it is the kind of claim §3.3 depends on.
2. `monomorphise.rs:1154` carries `#[allow(dead_code)]` on `get_constrained_fn`, which is
   called from `monomorphise.rs:91` on the live `monomorphise_call` path. A false
   dead-code attribute suppresses the warning that would notice a *real* death.

Both are `/dev`(typecheck) hygiene inside this visit's reservation (§7).

---

## 2. FIXME 0924 — the monomorphisation obligation, on the C1 machine

### 2.1 P-1, restated where it now lives

> **P-1 (the gate is universal and table-enforced).** `Life::Concrete { slot, … }` is
> constructed **only** by C1's `settle_concrete`, which checks `Type::is_concrete()`,
> accepts the realization, and mints-or-rebinds the slot in one act
> (`symbol-table-lifecycle.md` §§4.2 and 4.4; exact accepted states are in the
> `crates/cranelisp-types/src/module.rs::settle_concrete` rustdoc). A non-concrete callable is
> `Life::Template` — slot-less, view-less, **with no field for either capability** — and
> is a monomorphisation source, never a codegen target.
>
> **C3's obligation is consumption:** every population in this crate settles through the
> funnel, and the four literal mints (F0–F3) are deleted rather than gated.

This is not new policy. It is `monomorphisation.md` §1 — *a def has a slot ⟺ its type is
`is_concrete()`* — enforced at the table boundary instead of left as a caller
convention. [Lifecycle enforcement](../arch/symbol-table-lifecycle.md#6-enforcement)
prevents ordinary consumers from bypassing settlement and slot construction;
[Residual responsibilities](../arch/symbol-table-lifecycle.md#7-residual-responsibilities)
retain the clone/serde and copied-claim limits and their load/publication
validation. That qualified boundary is this obligation's end state.

> **P-2 (no second identity home).** A monomorphised accessor or trait-method instance is
> named by the ONE canonical context-bearing
> `InstanceLink::instance_key(&template_scheme)` contract
> ([S122 identity packet](../arch/s122-overload-reorder-publication.md)), and under C1
> that name is **derived once** at instance registration from the authored owner and
> complete concrete function signature, never re-composed at a probe site
> (`symbol-table-lifecycle.md` §5.2). No new grammar, no widened second mangle.

### 2.2 Why P-2 still rejects 0924's own suggested spelling

FIXME 0924 item 2 and the release contract §5.2 both propose widening
`mangle_trait_method` from `…$primitives/Option` to `…$primitives/Option$Int`. **That
spelling stays rejected, and the disposition it serves stays adopted.** Three reasons, in
order of weight:

1. **It is lossy on the axis that matters.** `Functor.fmap`'s instantiation is `(a, b)`,
   and `b` comes from the *function argument's* return type, not the receiver. Widening
   by the receiver's arguments yields one name for `(fmap show (Some 1))` and
   `(fmap inc (Some 1))` — the 0483/0508/0519 collision class re-minted at a new site.
2. **The shared key derivation carries the whole signature**, including ordered
   parameters and result, with recursive concrete types. Residual types fail key
   derivation instead of producing a partial spelling.
3. **Principle 7.** Two grammars for "a concrete instance of a generic body" is the second
   identity home the release contract's reject criterion 5 forbids in the backend and that
   S110's alias-class close removed from the resolution channel.

`mangle_trait_method` **survives unchanged** as the *template* name — the discovery and
dispatch key. Restated on the C1 machine:

| Role | Symbol | `Life` |
|---|---|---|
| Impl-method template (as today, now slot-less) | `Functor.fmap$primitives/Option` | `Template { body: Ast(variant), kind: Parametric }` |
| Concrete instance (minted on demand) | authored owner + full concrete function signature, in the canonical readable syntax | `Concrete { slot, realization: Body { view }, minted_from: Some(link) }` |

The template's key is untouched, so trait *discovery* (`impl$…$…`, `dispatch.rs:143`,
`impl_check.rs:421`, the §7.3.5 conformance seams) is untouched. Only the *call* is
redirected, by rewriting the site's `ApplyRef::Dispatch(FQSymbol)` to the instance — the
same carrier value-source rule (`backend-keyed-consumer.md` §1.1/§1.1.2) the mono path
already obeys.

### 2.3 F1's disposition — A-MINT, now with a place to keep the recipe

`monomorphise_call`'s core instantiates a template by **re-checking its body** at concrete
argument types, in the defining module's scope (`monomorphisation.md` §3.7). That is right
for F2 — a user-written impl-method body with real spans, real carriers, a real import
context. It is **wrong** for F1, and forcing it there manufactures three problems the
synthesiser does not have:

- an accessor body is `Span::SYNTHETIC` throughout (`adt.rs:447-471`), so it is
  structurally outside span-keyed carrier transport — the recheck would produce
  `pattern_ctors` / `var_refs` / `apply_refs` maps keyed on one repeated synthetic span;
- the arm's constructor identity is supplied *directly* at synthesis (`adt.rs:599-606`),
  not resolved — re-checking would re-derive a fact already in hand (Principle 24);
- the body is **derived from the field list**, not authored. Re-checking a derivation to
  recover the types it was computed from is a second derivation of a settled fact
  (Principles 7 and 26).

> **A-MINT.** A monomorphised field accessor is produced by **re-running the synthesiser
> at concrete type arguments** — the same `synthesise_one_accessor` computation with
> `adt_type` and `field.ty` substituted through the instantiation — keyed by
> the canonical authored-owner/full-concrete-signature identity. It never re-checks a
> body and never consults a span-keyed sidecar.

**What C1 adds, and it is the part S119 could not state.** Under the old shape the
polymorphic accessor template still had to *carry* something — a slot and a view it had no
right to. `Life::Template { body: TemplateBody::Synth(SynthSpec) }`
(`symbol-table-lifecycle.md` §5.8) is the missing state: the template stores the
**recipe** — the declaration payload A-MINT re-runs — and has no field for a slot or a
view. So the two S119 deletions at the synthesis site are no longer deletions of an
early-allocation habit; they are the absence of any place to put the result:

- when the substituted scheme is non-concrete, **no slot and no view exist to build**, and
  the premature `synthetic_local_from_expr` call (`adt.rs:607-613`) and
  `allocate_got_slot()` (`:617`) move into the instance mint (Principle 6, and it removes
  a wasted GOT slot per polymorphic accessor);
- the bare-alias `Import` edge, the `Ambiguous` poison, the cross-cluster
  `committed_accessor_kind` classification and the §8.6.5 contest rules are **untouched**.
  They key on the canonical `Type.field` symbol, which still exists — it is now a template
  rather than a compiled body. Resolution, `/list`, `/exports`, display and the impl-time
  collision pre-flight (`fixme-0365-field-accessor-dotted.md` §2) all read the entry, not
  its lifecycle state. `adt.rs:846-847`'s `UserFnState::Concrete { .. }` match in the
  accessor-kind reader is the one place that does read it, and it re-arms onto `Life`.

A-MINT stays the cheaper half despite the larger census share: the instance is a pure
function of `(fqtn, ctor, field, concrete type args)`, and the substituted `accessor_ty`
is concrete by construction whenever the demanded instantiation is.

### 2.4 F2's disposition — the ordinary mono path, with the scheme told the truth

Two changes, in this order:

1. **Stop calling `scheme::mono` on a non-concrete `fn_type`.** The impl-method scheme must
   quantify the residual variables it actually has — `type_vars = free_vars(fn_type)` after
   `apply` — so the entry answers `true` to `entry_is_monomorphisable_polymorphic` for the
   honest reason. This is R-2 at F2: the scheme stops claiming an absence it does not have.
   `scheme::mono`'s rustdoc says it asserts absence of quantification, **not** concreteness.
2. **The funnel then routes it to `Life::Template { body: Ast(ast_variant), kind: Parametric }`**,
   whose payload is exactly what `monomorphise_call` reads — and the annotated,
   subst-applied `ast_variant` the site already builds is that `DefnVariant`.

From there the existing core applies unchanged: instantiate at concrete argument types,
switch `state.current_module` to the impl-writer's module for the body re-check
(`monomorphisation.md` §3.7 facts 1–3; `impl_module` already records it per
`backend-keyed-consumer.md` §1.1.1), verify, settle concrete.

**The collection seam is the part this ruling does not settle statically.** A
trait-dispatched `Apply` is not a bare-`Var` callee of a name in `constrained_fn_names`,
so `collect_constrained_calls` does not see it; the site carries `ApplyRef::Dispatch(fq)`
and `fq_is_trait_method_decl` (`mono_collect.rs:977`) already recognises the shape. The
design intent is:

> **F2 collection** extends `collect_mono_call_sites` with one more trigger — an `Apply`
> whose `ApplyRef::Dispatch` target resolves to a `Template` entry and whose argument types
> are all concrete (`local_parametric_call_triggers`, reused verbatim) — feeding the
> **same** worklist and the **same** core. It is a successor-discovery widening, not a
> second entry point (`arch`'s standing Principle-7 ruling, `monomorphisation.md` §3.1).

The landed collector reaches these template sites through the ordinary typed-demand
worklist; §8 records the current source-backed disposition.

### 2.5 FIXME 0935 — absorbed by the demand carrier, not patched at the spelling

0935's fix shape item 1 says *"collectors record `resolved.storage_key` … never
`fq.symbol`"*. **C3 does not implement that as a spelling swap**, per the sprint's
no-refix rule and because the swap would leave the next collector free to get it wrong.

Verified at HEAD, the collectors push the **written/reference** identity at three sites,
not the two the filing names:

| Site | Push | Note |
|---|---|---|
| `mono_collect.rs:480-485` | `resolved.fq.symbol.clone()` | imported-call collector; the comment at `:474-478` states the intent explicitly |
| `mono_collect.rs:592` | `resolved.fq.symbol.clone()` | local-parametric collector — 0935's cited site |
| `mono_collect.rs:687` | `resolved.fq.symbol.clone()` | **not named in the filing** |

C1 supplies `MonoDemand { template: FQSymbol /*storage*/, args, site }` and
`InstanceLink { template, args }`, whose `template` field **is** the carrier-read storage
identity (`symbol-table-lifecycle.md` §5.2). So:

> **The 0935 close is a type, not a rule.** The three pushes converge on one
> `MonoDemand` constructor whose `template` is read from the recorded
> `VarRef::Global` / `Resolved::storage_fq()` — a value the collector *has*, not a name it
> composes. A collector cannot push a written spelling because the field will not take
> one, and the mint probes `template.module` by `template.symbol` — a keyed read that
> cannot land on a bare-alias `Import`, because the storage identity is by definition the
> terminal key.

The consumer half needs no separate fix. `get_constrained_fn` (`monomorphise.rs:1155`,
called from `:91`) raw-probes `state.current_module` by `name` at `:1171` and accepts only
a terminal `ModuleEntry::Def` (`:1173-1200`, two silent `_ => None` arms), which is why the
bare-alias `Import` yielded `None` → `Ok(None)` → a silent skip. Given a storage-keyed
demand the probe hits the terminal entry by construction. Its `Ok(None)` early return
**remains** the "not a mono target" signal — and under C1 a demand that finds no instance
is a loud missing-slot failure downstream, because the template has no slot for the call
to fall through (`symbol-table-lifecycle.md` §§4.2 and 6); §7 retains the
load/publication rechecks rather than claiming every bad restored value is
structurally impossible.

**0935's second finding is binding and is honoured:** the dotted spelling's minted
instance was itself unsound, because the generic mono path's recheck over the
`Span::SYNTHETIC` accessor body cannot concretise the field's category. So the identity
change and A-MINT **land together for the F1 family**; for ordinary generic fns behind
renamed imports the demand-carrier change alone is complete.

The S119 differential motivated the carrier change. Current acceptance is the canonical
bare-accessor and renamed-import carrier evidence recorded in §8; the historical dump is
not a continuing measurement gate.

### 2.6 The cost, against the measured census

The release contract's censuses partition cleanly by owner:

| Population | Total | Face 1 (backend, I-CT′) | **Faces 2+3 (this obligation)** |
|---|---:|---:|---:|
| Census A — release admissions | 2,497 | 2,216 (89%) | **281 (11%)** |
| Census B — bare `Type::Var` licences | 3,646 | 3,108 (85%) | **538 (15%)** |
| Census B — `ADT(concrete,[Var…])` licences | 1,776 | 1,296 | **480** |
| Census B — `Fn(…)` residual licences | 75 | 20 | **55** |

So this obligation owes **281 release admissions and 1,073 category licences** to zero,
and *the census reading zero is the acceptance criterion* (§5).

**Code-size cost.** Faces 2/3 trade one body per declaration for one body per *distinct
concrete instantiation*. Three grounds for a multiplier near 1, and one honest unknown:

- `Grid.cells`'s 164 measured admissions are 164 *compilations of the same frame* across
  the suite's programs, not 164 instantiations. A `Grid` in the exemplar is instantiated at
  one element type.
- Accessors are the extreme low end: an instance is a one-arm `match` loading one field.
  A-MINT emits no more per instance than the template emits today.
- The language already pays this multiplier for every ordinary generic `defn`; the census's
  own frame list carries `ct/ap$Fn(Int;ct/Bx$Int)+Int` beside `Bx.v`.
- The distinct-instantiation multiplier remains a performance characteristic, not a
  correctness or filing-retirement gate.

**Precision gain, recorded because it is not free value.** Every F1/F2 call becomes a
statically-resolved call to a concrete instance — the exact precondition
`design/arch/ownership-inference.md` §3.1 sets for ABI-bearing per-parameter mode vectors.
Today an accessor call is a call into a frame with no derivable summary; the `ModeSummary`
on the instance is derivable, and `Life::Concrete` has the field for it.

### 2.7 What must NOT change (the `review` fence)

1. **No new `cranelisp-types` item and no second lifecycle vocabulary.** Everything this
   obligation needs is in the C1 machine. A need it lacks is a filing to `arch`, never a
   local state grown beside it (`symbol-table-lifecycle.md` preamble).
2. **No second mangle grammar** (P-2), and specifically no `$Type$Arg` widening of
   `mangle_trait_method`.
3. **No accessor body re-check** (A-MINT), and no routing of a real check-run body through
   `synthetic_local_from_expr` — the always-on synthetic-span assert exists to catch that.
4. **A concrete product's constructor and accessor, and a concrete impl method, are
   byte-identical to today.** The gate is a new *arm*, not a new path; `Tally.passed` and
   `Show.show$primitives/Int` keep their slot, body, view and CLIF. A golden-CLIF diff
   outside the F0/F1/F2 frames is a finding, not a re-baseline.
5. **The §8.6.5 bare-alias contest, the `Ambiguous` poison and the impl-time collision
   pre-flight are untouched.** They read the canonical entry, not its lifecycle state.
6. **No spelling patch at `mono_collect.rs`.** A `storage_key` swap at the three push sites
   *without* the typed demand is a reject (§2.5).

---

## 3. FIXME 0913 — the lenient view stops fabricating (contract face 5)

### 3.1 What the ruling requires, and what it forbids

The release contract §5.4 is specific, and it is **not** what 0913's own text implies. The
lenient view must **default unconstrained parameters — explicitly and checkably — and never
substitute the node's type**:

- forbidden: `(Result a String)` ⇒ `Int`. That does not default a parameter; it discards the
  type constructor and every concrete argument with it. Backend then sees a scalar and emits
  nothing.
- permitted: `(Result a String)` ⇒ `(Result <default> String)`. The constructor survives,
  `String` survives, and only the position nothing inhabits is filled.

### 3.2 The licence, and its fence

The ruling's soundness argument — *a parameter still free after inference is a parameter no
value in the released graph inhabits, because a value of that type would have pinned it* —
is correct **and is not universally applicable**. It has one genuine counter-shape, and the
fence is stated before the rule or the fix converts a leak into a wrong release:

> A **multi-sig `f$Var` variant** body carries residual parameters that a *caller*
> instantiates. A value of that type demonstrably exists at runtime — it is the argument.
> Defaulting there would tell backend the parameter is a scalar while the caller passes a
> heap value, and the payload would be silently under-discharged.

The discriminator is *who can supply a value at that type*:

> **L-1 (the licence).** A residual type parameter of node `n` in frame `F` may be defaulted
> iff the residual variable **does not occur in any of `F`'s declared parameter types**.
> Nothing outside `F` can then supply a value inhabiting it, so no value of that type exists
> in the graph `F` releases.
>
> The guaranteed-covered subset, and the whole of 0913's measured population, is **`F` is
> nullary** — `__expr` (every REPL turn) and `main`. The general form is stated because it
> is the honest statement of the property; the nullary case is the one `dev` must cover and
> the one `qa` asserts.

L-1 also disposes of the interior-node worry. `(let [e (vec)] (Err "boom"))` binds
`e : (Vec a)` — residual, and a real allocation that must be released. It is defaultable,
and `(Vec Int)`'s glue frees the buffer with no element discharge, which is correct because
**a container at an un-unified element type is necessarily empty**: inserting an element
would have unified the parameter. Same argument, one level in, and it is why the rule is
about the parameter rather than the root.

> **L-2 (the shape).** Defaulting is defined only for a type whose **root is a type
> constructor** (`Type::ADT` / `Type::Fn`). It replaces each residual argument position
> strictly *below* the root with the declared default, preserving the constructor and every
> concrete argument, recursively.
>
> A type whose **root is itself residual** (`Type::Var` / `Type::TyConApp`) is **not
> defaultable**: no constructor, therefore no category, therefore no glue — R-1 exactly.
> §3.5 states its disposition.

> **L-3 (the check the narrowing carries — Principle 25).** Defaulting refuses, with a
> **located error**, if the residual variable appears in the enclosing scheme's
> `constraints`. Choosing `Int` for a variable carrying `Eq a` is choosing a trait instance,
> which is fabrication of a different kind.

**The default itself** is `ConcreteType::Int` — a declared `NeverHeap` type, per the
ruling's own wording. The value is the same token the fabrication used; the difference is
everything about *where* it is applied and *what carries it*. To keep that difference
legible rather than a comment, the default is reached only through a single named operation
(§7 CS-3) and never through an inline `unwrap_or`.

### 3.3 The mechanism — and the property that makes it self-checking

The defaulting is a **typecheck operation**, not a `cranelisp-types` walk change, for one
decisive reason: L-1 and L-3 need the frame's declared parameter types and the enclosing
`Scheme`, and `lenient_from_expr` has neither — it has an `Expr` and three sidecars. Putting
the decision there would be a second derivation of a question typecheck has already
answered, which is the rule that produced this defect in the first place.

The seam is `program/support.rs::build_concrete_codegen_view` (`:307`), on the
`NotConcrete` arm (`:321-328`):

```text
from_expr(variant.body, …)
  Ok(view)                  -> strict view                     (unchanged)
  Err(Unresolved{..})       -> located typecheck error         (unchanged, :329-345)
  Err(NotConcrete(_))       -> NEW: defaulted = default_residual_parameters(variant, scheme)?
                               from_expr(defaulted.body, …)
                                 Ok(view)            -> strict view over defaulted types
                                 Err(NotConcrete(_)) -> §3.5 disposition
                                 Err(Unresolved{..}) -> unreachable; defaulting touches types only
```

`default_residual_parameters` clones the annotated variant and rewrites the `inferred_type`
of every node whose type fails `ConcreteType::from_type`, under L-1 / L-2 / L-3. **It
rewrites the clone, never the stored `ast`** — the spec-required residual-parameter displays
(`repl/spec.md` §1.5 / §4.1) read the real type and stay byte-identical. The ruling is
explicit that the displays are right and the release behind them is not.

> **The self-check.** Defaulting's success criterion is that **the strict builder then
> accepts the body**. That is Principle 25 realised structurally rather than asserted: a
> defaulting that left a residual anywhere does not silently pass — the strict walk rejects
> it. The narrowing carries its check because the check is the next line.

After the strict retry, a remaining `NotConcrete` cannot reach backend: the
builder returns a located type error carrying the frame name and refusal reason.
That refusal is the safety mechanism. A separate aggregate counter on the same
erroring branch adds no protection or decision input.

### 3.4 Why this closes the leak end-to-end, with no other crate touched

`__expr`'s body type becomes `(Result Int String)` in the codegen view. Backend keys
`result_roots` off that view's body type, so it derives canonical glue for
`(Result Int String)`. Int's `release_key` (`src/result_owner.rs:337`) takes the same
`codegen_result_ty` it already takes, narrows it identically, and requests the glue backend
emitted. The `Err` arm's `String` is discharged; the `Ok` arm carries the defaulted
parameter and is **unreachable for this value** — the tag says `Err`. The defaulted position
is typed out of the walk, not walked with a wrong type.

| Consumer | Delta |
|---|---|
| `cranelisp-types` | **none in C3** — `lenient_from_expr` is untouched; its deletion is §3.6 |
| `cranelisp-backend` | **none** — it derives glue for whatever `ConcreteType` it is handed |
| `src/` (int) | **none** — `release_key`'s authority order is already right; only the value it reads changes |
| typecheck public API | **none** — `build_concrete_codegen_view` is `pub(crate)` |

`design/int/result-owner.md` §1.1.1's scope sentence records the gap as "an unpinned `[]`
(or a bare polymorphic `None`)"; `None` cannot leak (nullary tag, no allocation) and the
real axis is *any* residual parameter — `(Ok x)` / `(Err x)` / `(vec)`. That correction is
`design`(int)'s, in the C6 visit; this doc records the corrected axis as the acceptance
axis and does not edit int's record.

### 3.5 The residual — and what C1 changes about it

S119 ruled that an L-2-inadmissible node (residual **root**) keeps a *counted placeholder*,
because `lenient_from_expr` returns a total `MonoExpr` and widening it to a `Result` is a
`cranelisp-types` signature change. **The C1 machine removes the state that placeholder was
living in**, and the disposition changes accordingly:

`Realization::Body` carries its `view: MonoDefnVariant` **non-optionally**, and
the supported authoring path constructs `Life::Concrete` only with a
realization (`symbol-table-lifecycle.md` §§4.2, 4.4 and 4.6; exact states are in
the `crates/cranelisp-types/src/module.rs::settle_concrete` rustdoc). So that path cannot
produce "a concrete entry whose view was built over a placeholder"; lifecycle
§7 still records the clone/serde validation limit. A frame whose body still has a residual **root**
after defaulting therefore has exactly two admissible dispositions, and no third:

1. **It is not a codegen target** — it stays `Life::Template`, and any reachable use is a
   demand that mints a concrete instance. This is the correct disposition for a residual
   root that a use pins.
2. **It is a codegen-reaching value position with nothing pinning it** — which is spec
   §3.11.1 disposition 2, an ambiguity **type error**, located. Typecheck already owns that
   check (`monomorphisation.md` §4); this arm routes to it rather than inventing a second
   diagnostic.

Disposition 3 of §3.11.4 — a bare polymorphic value displayed at the REPL — never reaches
this seam at all, because it is not compiled.

No permanent census is required at this seam. A residual-rooted frame either
remains a template or reaches the located ambiguity error above; neither path
hands backend a fabricated view. The attempted debug counter discarded the
frame and `NotConcrete` reason, had no reset or corpus reader, and incremented
only immediately before that existing error. It therefore could neither prove
the arm empty nor change its safe disposition and is not part of the current
design.

### 3.6 The `lenient_from_expr` deletion remains out of scope

`lenient_from_expr` is a `cranelisp-types` public item, so its deletion does not
ride this typecheck visit. The current typecheck design establishes only:

- **stop feeding it.** `support.rs:322` is its only production caller in the workspace;
  after CS-3 that call is reached only by the §3.5 residual arm.
- **name its remaining consumers** for the C4 handoff: `cranelisp-backend`'s
  `test_support.rs:239` and `:755` (test-support only); `lib.rs:909` documents the already
  deleted backend production arm.
- **do not infer deletion authority from this refusal path.** A future types-owned
  deletion must establish its own complete consumer case; the retired aggregate
  neither licenses nor blocks it.

---

## 4. Rider 0867 retired — product accessors only

The S118 reproduction correctly observed that differently named constructor
arms mint no accessors, but its attribution treated those arms as alternate
product syntax. The 2026-09-02 language ruling resolves the premise: a product
has one same-name constructor; a differently named constructor is a sum variant
even when it is the only arm. Sum payload labels are positional metadata and
mint no callable name.

Therefore there is no all-constructor-arm widening. The existing product guard
is required. `qa` instead owns the two-sided boundary:

1. monomorphic and polymorphic products mint total canonical accessors and bare
   candidates, settling as `Concrete` or `Template` according to their scheme;
2. monomorphic and polymorphic sum arms mint no dotted or bare accessor, while
   positional `match` extracts their payloads successfully.

This removes the proposed partial-accessor runtime panic and the associated
stdlib surface widening. A-MINT remains necessary for polymorphic **product**
accessors only.

3. **The stdlib widening cell**, which nothing else covers: one module `[*]`-importing
   **both** `collections.list` and `seq.lazy`, exercising the cross-module bare-alias
   contest on `head` (minted bare by both) and `rest` (minted bare by `seq.lazy`, already a
   `defn` in `collections.list`). Orthogonal to the memory-safety axis, but it is the
   widening's own regression risk and `stdlib_conformance` structurally cannot see it — it
   imports each module separately. Its consequence lands in **U8**, not C3.

### 4.4 FIXME 0912 — resolved at the frontend boundary

Spec §5.2.4 requires explicit parameter and field declarations. A bare head is
monomorphic; a parenthesized head is its complete parameter list; every field
has a written type. The frontend exclusively rejects missing field types and
undeclared type variables before emitting entries
(`design/frontend/s116-syntax-and-annotation.md` §3.1).

> **Typecheck adds no compensating declaration-shape check.** What typecheck still owns is
> unchanged and different: a written field type naming a **concrete** type that does not
> resolve is its §8.5 failure, at its own seam, with its own message.

The positive obligation §5.2.4 places on this crate is 0924 plus the product/sum
boundary in §4: a valid explicit generic declaration such as `(deftype (B a)
(Mk [:a v]))` must support construction and pattern matching at each concrete
instantiation, and a product must additionally support its total accessor.
Typecheck must not fail merely because the declared field type is a parameter.

---

## 5. The observations — 0929, 0936, and the backend zero criterion

The backend instance census and the ownership seed observation answer different
questions. C4 retains the exact-zero release criterion it owns. Typecheck keeps
the keyed `residual_param_frames` observation for its conservative ownership
seed (`ownership-inference.md` §18.2); the already-erroring codegen-view path
requires no second instrument.

### 5.1 The instance census — the F0/F1/F2 gate C4 consumes

- **Instrument:** backend's existing category-licence counter — `signature_heap_category`'s
  `Err ⇒ HeapCategory::Mixed` arm (release contract §5.1), partitioned by the frame's
  `CallableOrigin` (`Ctor` / `Accessor` / `TraitMethod` / `Plain`).
- **Criterion, exactly:** across the full default suite **and** the 16-program corpus named
  in FIXME 0903, the licence count for the `Ctor`, `Accessor` and `TraitMethod` partitions
  is **0**, and the release-admission count for the same partitions is **0** — against the
  S119 baseline of 281 admissions and 1,073 licences. Additionally **zero new hard codegen
  refusals**: the corpus runs 893 programs at 8 failures today, and 24 was the measured cost
  of the rejected frame-keyed refusal, so any number above 8 is a finding.
- **Owner of the reading:** C4. C3's obligation is to make the count reach zero and to state
  the partition, so the reading is attributable rather than aggregate.
- **Detection proof:** the instrument is already live and already reads non-zero, so its
  positive leg is demonstrated. Its **negative leg is not**: nobody has shown it stays
  silent when the fault is absent. C4's change-set owes that leg — plant a concrete frame,
  confirm no licence is recorded.
- **The flip is census-gated, not review-gated.** Backend keeps the fabricating arm until
  the partitions read zero, and only then converts it to a located error. So this
  obligation's landing is observable from backend's own instrument rather than asserted by
  this crate.

### 5.2 The codegen-view refusal — no separate census

`program/support.rs::build_concrete_codegen_view` reruns the strict builder
after `default_residual_parameters`. A second `NotConcrete` result returns the
located refusal required by §3.5. The former view-refusal aggregate
did not retain its frame or reason, had no reset or corpus consumer, and ran
only before that error return. It added neither prevention nor actionable
observation, so the current design requires no counter, getter, zero-count flip
or detection-proof fixture at this seam.

This retirement does not affect `ownership/fixpoint.rs::residual_param_frames`.
That keyed set observes the separate conservative ownership-seed decision and
remains as specified in `ownership-inference.md` §18.2.

### 5.3 The fabrication census — FIXME 0929's typecheck arm

0929 found that the `ConcreteType::from_type` discard-and-substitute population is four
fabricating arms plus two correct refusal sites, and that **two arms lived outside every
census**. `arch` discharged asks 1–3 and routed the dispositions; the typecheck-owned one
is site 1.

| Site | Arm | Status at HEAD | Owner |
|---|---|---|---|
| 1 | `ownership/fixpoint.rs:221` — `ConcreteType::from_type(t).unwrap_or(ConcreteType::String)` | **live, ungraded** | **C3** |
| 2 | `backend/drop_glue.rs:398` — `args.first().cloned().unwrap_or(ConcreteType::Int)` | live, ungraded | C4 |
| 3 | `backend/compiler/context.rs:280` + the declaration channel | live | C4 (`CtorMeta` ruling) |
| 4 | `backend/compiler/fn_compiler.rs:1214` — defensive dead arm | live, low | C4 |
| 5 | the int-layer result/display trio | live, ungraded | C6 |
| — | **new, found this window:** `ownership/transfer.rs:830` — `arg_origins.get(k).cloned().unwrap_or(Origin::Fresh)` | **live, ungraded** | **C3** |

Sites 1 and the new `transfer.rs:830` arm are one class — an ungraded `unwrap_or` narrowing
in the ownership walk — and their grading is designed together in
`ownership-inference.md` §18, because the argument is about the ownership lattice's
conservative point, not about `ConcreteType`. C3 grades those two and no others; the C4 and
C6 rows are named here only so the census C3 hands on is complete rather than
crate-shaped.

**The structural-closure question stays answered as `qa` recommended and `arch` accepted:**
`ConcreteType`'s variants are **not** sealed (exhaustive matching across backend is
load-bearing and legitimate literal construction exists); the NC-2 pinned allow-list is the
enforcement mechanism; and the residual grade on register row R18 is
*asserted-with-a-named-falsifier*, the falsifier being the census pattern firing or a
fabricating literal outside `unwrap_or` position found by the next sweep.

### 5.4 The realization roster — FIXME 0936, evidence-only

0936 asks `qa` to re-label NC-R's rationale: the four by-name callables are the **backend
uniform-realization roster**, not a licence class. C3 supplies the derivation that makes the
relabel checkable, and decides nothing:

> Under C1 the roster is **a projection, not a set**: it is exactly the entries whose `Life`
> is `Template { body: TemplateBody::UniformRust { abi_name }, .. }`
> (`symbol-table-lifecycle.md` §5.5). NC-R's cell asserts that projection rather than a
> hand-maintained list, and a silent fifth member REDs because it appears in the projection.

Trajectory, as 0936 records it: `bind`/`race`/`select` **leave** the set at their inline
re-kind (C5); `catch-runtime-error` remains the standing member; `vec-len` joins only if
0932 chooses spelling (b), and `arch`'s recorded preference is (a) `Inline`, keeping the
roster at one. Every member of the projection is a **primitives** or **platform** entry, so
C3 owns none of them — the disposition is **evidence-only**, and the plan-row and cell
rustdoc edits are `qa`'s.

---

## 6. Public API, schema, and what `arch` must take

**Zero `cranelisp-types` delta from C3, and zero movement of
`crates/cranelisp-typecheck/public-api.txt` from this obligation.** Verified: the typecheck
baseline (145 lines) exports none of `MonoDemand`, `InstanceLink`, `CallableSlot`, `Life`,
`BindingBody` — those are consumed from `cranelisp-types` — and every item this obligation
needs is either C1-published or `pub(crate)`.

> The one C3 public-surface addition in the whole visit is FIXME 0553's
> `instantiate_demands` entry point, which is **not** part of this obligation. It is
> designed in `monomorphisation.md` §3.8 and carries its own `arch` approval, granted
> 2026-09-01 with the contract at `design/arch/bounded-contexts.md` §2.

**The schema question S119 left open for `arch` is answered and this section supersedes
it.** S119 §5 offered three options because SPRINT.md then authorised exactly one 23→24
window owned by 0869. The S121 contract settles it: **`CACHE_SCHEMA_VERSION` 24→25, exactly
once, in the C1 change-set** ([S121 lifecycle design at checkpoint
`dc78ddbe`](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/symbol-table-lifecycle.md)
§9). Both halves of this
obligation are cache-visible *meaning* changes and both are covered by that window's
wholesale pre-25 invalidation:

- **0924/0935.** A polymorphic product accessor or impl-method entry that used to serialise
  `Concrete { got_slot }` now serialises `Template`, and a new population of instances
  appears under new keys. A pre-fix cache restoring an accessor as concrete would make the
  new compiler compile the template frame again, on a cache hit, with residual types — the
  memory-unsafety returning on warm cache.
- **0913.** The view is serde-visible. A stale sidecar restoring `ConcreteType::Int` body
  types makes backend derive no glue — the leak returning on warm cache.

Two consequences C3 must not get wrong:

1. **C3 does not bump anything.** `CACHE_SCHEMA_VERSION` is defined in
   `crates/cranelisp-backend/src/cache/mod.rs:391` (value 24 at HEAD), so the bump is a
   *backend* edit that C1 coordinates. A second bump inside C3 is a plan violation to report.
2. **No cache baseline may be captured for acceptance between the C1 bump and the C4
   IO-layout flip** ([S121 lifecycle design at checkpoint
   `dc78ddbe`](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/symbol-table-lifecycle.md)
   §9), so C3's warm-cache evidence is taken
   after C4, not during this visit.

---

## 7. Implementation obligations for `dev`(typecheck)

Ordered. Each change-set carries its unit rows (§7.5) and, per root `CLAUDE.md` §Testing,
the failing test(s) are written **first**. The whole sequence is one visit to the reserved
paths in `typecheck.md` §9.8.

### 7.1 CS-1 — funnel consumption: delete the four hand-mints

- Route F0 (`adt.rs:172-181`), F1 (`adt.rs:617-637`), F2 (`impl_check.rs:1078-1089`) and F3
  (`monomorphise.rs:680-697`) through C1's `settle_concrete` / `settle_template`. Delete
  every `allocate_got_slot()` call in this crate; the capability is the funnel's interior.
- At F2, replace `scheme::mono(fn_type)` with a scheme quantifying `fn_type`'s free
  variables (§2.4 item 1), and correct `scheme::mono`'s rustdoc.
- At F1, move the `synthetic_local_from_expr` view-build (`adt.rs:607-613`) into the
  instance mint; the template stores its `SynthSpec` recipe instead.
- Delete `monomorphise.rs:1188-1197`'s `ConstrainedFn` synthesis and its `.unwrap()`
  (§1.4); read the template's own payload.
- Re-arm `adt.rs:846-847`'s accessor-kind read onto `Life`.
- **Acceptance:** the §4.3 gate cell; zero golden-CLIF movement for concrete constructors,
  concrete accessors and concrete impl methods; programs that call a polymorphic accessor or
  a generic impl method now fail **loudly** (missing slot) if coverage has not landed — that
  is expected, is the forcing function, and is why CS-1 and CS-2 land in the same wave even
  though they are separate commits.

### 7.2 CS-2 — coverage: the demand carrier, product A-MINT, the F2 trigger

- **The demand carrier (0935).** Converge `mono_collect.rs:480-485`, `:592` and `:687` on one
  `MonoDemand` constructor whose `template` is the carrier-read storage FQ. No spelling
  swap (§2.7 item 6).
- **A-MINT** (§2.3): an accessor-instance minter keyed by the context-bearing canonical
  instance key, fed from the
  mono worklist, substituting through the instantiation and re-running the synthesiser's
  derivation over the template's `SynthSpec`.
- **Product boundary** (§4): retain the `is_product`/lone-constructor source for
  total accessors; sum payload labels mint no entry. A-MINT re-synthesises only
  polymorphic product accessors.
- **F2 trigger** (§2.4): extend `collect_mono_call_sites` with the
  `ApplyRef::Dispatch → Template` case, reusing `local_parametric_call_triggers` verbatim;
  rewrite the site's `ApplyRef::Dispatch` to the instance's `FQSymbol`.
- **Cluster-level dedup** on the canonical realization key, unchanged
  (`monomorphisation.md` §3.5).
- **Cross-cluster / REPL:** an accessor is minted at `deftype` time in a *prior* cluster; the
  demanding call site is in a later one. That is the `collect_imported_constrained_calls`
  cross-module shape, and `monomorphisation.md` §3.7's three scoping facts apply verbatim to
  F2. A-MINT is immune — it re-derives rather than re-checks — and the change-set says so, so
  `review` does not look for a home-switch that is deliberately absent.
- **Acceptance:** §5.1's criterion; 0916's cell flips once C4 consumes it; the
  `f4_sudoku.clif::user::Grid.cells` golden re-baseline, scoped and attributed in this
  change-set per `ownership-inference.md` §6.2 (extension ≠ re-baseline).

### 7.3 CS-3 — 0913, the defaulting step

- `default_residual_parameters(variant, scheme) -> Result<DefnVariant, CranelispError>` in
  `program/support.rs` beside its one caller. L-1 / L-2 / L-3 as written. **One named home
  for the default value** — no inline `unwrap_or(Int)` anywhere.
- Wire it into the `NotConcrete` arm followed by the strict re-run (§3.3).
- Route the §3.5 residual-root arm to `Template`-or-located-error. A second
  `NotConcrete` returns the located refusal; no counter is required (§5.2).
- Repair `support.rs:273-276`'s false "always returns `Some(view)`" rustdoc (§1.5).
- **Acceptance:** `tests/residual_type_param_result_leak_0913.rs::unannotated_result_turn_releases_like_its_annotated_twin`
  reads an exact marginal 0. **Not** closed by adding an annotation anywhere.
  `repl/demos/memory-lifecycle.demo`'s narration flips (a demonstration, not the guard). The
  `(Ok x)`, `(Ok 1)` and `(vec)` rows follow the same seam; `None` needs no cell.

### 7.4 CS-4 — the ownership-walk grades

`ownership-inference.md` §18: grade `fixpoint.rs:221` and `transfer.rs:830`. Separable from
CS-1..3 and orderable anywhere in the visit; it shares no file with them.

### 7.5 Unit-test design (typecheck tier)

Rows placed beside their production owner per the crate `CLAUDE.md` sibling convention
(`program/*/tests.rs`, `traits/*`, `adt.rs`).

| Submodule | Complexity / positive | Edge | Negative |
|---|---|---|---|
| `adt` ctor + accessor mint | a concrete product's ctor and accessor are `Life::Concrete` with a slot and a `Realization::Body` view, byte-identical to today | a polymorphic product's ctor and accessor are `Life::Template`, **no slot allocated**, no view built | the bare-alias `Import`, the `Ambiguous` poison and the cross-cluster `committed_accessor_kind` classification are unchanged for **both** arms — a lifecycle change must not perturb the §8.6.5 contest |
| `adt` product/sum boundary (0867 retirement) | concrete and polymorphic products mint their canonical `Type.field` and bare candidate | differently named one-arm and multi-arm sums extract payloads by positional `match` | no sum payload label mints a dotted or bare accessor; no partial accessor or runtime variant check exists |
| accessor A-MINT | one instance per distinct authored accessor/full concrete signature; scheme `is_concrete()`; view built by `synthetic_local_from_expr` | two distinct concrete signatures mint two distinct canonical keys; an identical re-reach dedups to one | the minter never consults a span-keyed sidecar; a non-concrete instantiation is **not** minted (deferred per `monomorphisation.md` §3.3) |
| `traits::impl_check` scheme | a **concrete** impl method (`Show.show$primitives/Int`) is `Life::Concrete`, identical to today | a residual impl method quantifies its free vars and is `Life::Template` | `scheme::mono` is not called on a non-concrete `fn_type` at this site; `mangle_trait_method`'s output is **unchanged** for every input |
| `mono_collect` demand carrier | a bare-alias accessor call and its dotted spelling produce the **same** `MonoDemand` and dedup to ONE instance | a renamed-import generic call mints | no `MonoDemand` is constructible from a written spelling; all three collector sites take the same constructor |
| F2 collection | a dispatched call at a full concrete signature mints one instance under the canonical key and rewrites `ApplyRef::Dispatch` | the `b`-from-argument case: `(fmap show …)` and `(fmap inc …)` over the same receiver mint **distinct** names (§2.2) | no second key grammar appears; no `$Type$Arg` key is minted anywhere |
| `support::default_residual_parameters` | `(Result a String)` ⇒ `(Result Int String)`; `(Result String a)` ⇒ `(Result String Int)`; `(Vec a)` ⇒ `(Vec Int)`; concrete arguments preserved at every depth | nested: `(Result (Vec a) String)` defaults only the inner position; a fully-concrete body is a no-op and the strict walk was already taken | **the type is never replaced** — no input yields a bare `Int` from a constructor-rooted type; a bare `Type::Var` root is **not** defaulted (L-2); a variable in `scheme.constraints` is a **located error** (L-3); a residual occurring in a declared parameter type is **not** defaulted (L-1) |
| §5.2.4 explicit generic product | `(deftype (B a) [:a v])` registers a template constructor and product accessor | each accessor instance mints at a concrete use | typecheck does not invent or accept missing field types; the frontend boundary makes that state unrepresentable |

---

## 8. S122 as-built disposition

The former measurement gates are no longer implementation choices:

- **0924 is satisfied.** `adt.rs` settles residual constructors and product accessors as
  slotless `Life::Template { body: TemplateBody::Synth(..) }` entries. The concrete-use
  path in `traits/monomorphise.rs::monomorphise_synth` derives the instance from that
  recipe. `adt::tests::polymorphic_constructors_are_slotless_templates` pins the template
  boundary, while the mono-collector and synth-view units pin canonical concrete demand
  and view production. Trait-method templates use the same lifecycle and ordinary
  instance path; no second mangle grammar was added.
- **0935 is satisfied.** `program/mono_collect.rs::mono_demand_from_spans` receives
  `resolved.canonical` at the imported, local and dispatch collectors and constructs the
  typed `MonoDemand`. The bare-accessor and renamed-import carrier units in
  `program/mono_collect/tests/carriers.rs` assert the canonical storage identity. The
  nearby source comment now describes the live `resolved.canonical` input.
- **0913 is satisfied.** `program/support.rs::build_concrete_codegen_view` invokes
  `default_residual_parameters`, then retries the strict concrete view. The solution-level
  `tests/residual_type_param_result_leak_0913.rs::unannotated_result_turn_releases_like_its_annotated_twin`
  supplies the exact marginal-balance evidence recorded by the S122 inventory.
- **The typecheck arm of 0929 is satisfied.** `ownership/fixpoint.rs` records residual
  parameter frames, excludes them from the walkable ownership universe and publishes no
  summary for them. `ownership::fixpoint::tests::a_residual_parameter_frame_publishes_nothing_and_stays_in_the_keyed_set`
  pins both the refusal and the keyed observation. Other 0929 census arms remain with
  their owning contexts.

The historical corpus and multiplier measurements explain the original change, but they
are not continuing typecheck mechanisms or open filing gates.

---

## 9. Quality attributes

- **Simplicity.** Net deletion of decision sites, and more of them than S119 counted.
  Retired: four hand-rolled slot mints, `scheme::mono` over a non-concrete type at two
  sites, one `ConstrainedFn` synthesis with an `.unwrap()`, one premature
  `allocate_got_slot()` per polymorphic accessor, one premature view build, one
  `is_product`/`ctor_infos[0]` restriction, and `node_ty`'s unconditional `unwrap_or`.
  **Added: one accessor-instance minter, one defaulting function, and one
  `MonoDemand` constructor.** The gate helper S119 would have added is **not** added — C1's
  funnel is it, so the count of places deciding "is this callable concrete?" goes from five
  to zero in this crate.
- **Maintainability.** A fifth mint site is not merely hard to get wrong; it does not
  compile. Today the invariant is a property of one function in `finalize.rs` that four
  other sites quietly violate — which is how this class survived from S84 to S119, and why
  a convention-tier fix was the wrong grade.
- **Observability.** Backend's category-licence instrument retains its release
  criterion, while typecheck's keyed `residual_param_frames` reports which
  ownership frames took the conservative seed. The codegen-view refusal is
  already a located compile error and carries no duplicate aggregate counter.
- **Testability (Principle 5).** The gate cell (§4.3 item 2) is a pure unit assertion on an
  entry's `Life` — no program run, no allocator counters, no 1024 boundary. It is the
  cheapest possible guard for the most expensive possible defect.
- **Performance.** One body per instantiation instead of one per declaration; the historical
  multiplier estimate was near 1 for accessors. Offset: 2,216+ fewer compiled template
  bodies once the release contract's faces 1–3 are complete, and the §2.6 precision gain.
- **Concurrency-safety.** Untouched. No new shared state; A-MINT is a pure function of its
  inputs; the defaulting operates on a clone. The funnel's writes go through the same
  `SymbolTableAccess` staging seam as every other write (Decision 44).

---

## 10. Cross-references

- `design/arch/symbol-table-lifecycle.md` — §3 (outer layer), §4 (the `Life` machine, the
  funnels, `Realization`), §5.2 (`InstanceLink`/`MonoDemand`), §5.7 (trait impls), §5.8
  (synthesised ctors and accessors), §6 (current enforcement) and §7 (residual
  limits). The C1→C3 handoff and one schema window are S121 provenance in
  [the lifecycle design at checkpoint
  `dc78ddbe`](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/symbol-table-lifecycle.md)
  §9
- `design/backend/non-concrete-release-contract.md` — R-2, R-3, §4 faces 2/3/5, §4.3 (the
  impossibility proof), §5.1 (the instrument), §5.2, §5.4, §7 (staging), §8 (reject criteria)
- `monomorphisation.md` §1 (slot ⟺ concrete), §2 (the gate), §3.1/§3.3/§3.5/§3.7 (the spine
  this extends), §3.8 (the 0553 entry point), §4 (the ambiguity backstop this doc routes to)
- `adt.md` §"Product Type Handling"; `fixme-0365-field-accessor-dotted.md` §1.6 (the
  canonical/candidate model) and §1.6.7 (the product-only source ruling)
- `ownership-inference.md` §18 — the two ungraded `unwrap_or` narrowings (§5.3)
- `qualified-trait-impl.md` §7 — 0794's falsification, which corrects S119's F2 citation
- `design/frontend/s116-syntax-and-annotation.md` §3.1 — the §5.2.4 rejects typecheck must
  not compensate for (§4.4)
- `design/int/result-owner.md` §1.1.1 — the mis-scoped record 0913 corrects; the correction
  is `design`(int)'s in C6
- `spec/03-types.md` §3.11.1/§3.11.4; `spec/05-definitions.md` §5.2.4, §5.2.6
- `design/arch/principles/{06,07,18,20,24,25,26}` — Principle 25 is the spine of §3.2's
  fence and §3.3's self-check

## Current handoff

The 0924, 0913 and 0935 typecheck work is complete and their filings are retired. The
canonical-demand source comment is corrected. The separate 0779 polarity unit is complete
and recorded in `auto-curry.md` §3.
