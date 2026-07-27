# Concreteness Programme — Requirements Register

**Status**: DRAFT, user-commissioned 2026-07-27. Cross-check instrument for the revised
design. Owned by `/sprint` as a programme artefact (spans S119–S121+); `/arch` absorbs the
substance into `design/arch/total-concreteness.md` as it rules each item.

**Purpose**: a revised design is *confirmed* only when every row below is either addressed
or explicitly declined with a recorded reason. This document is the checklist, not the
design.

---

## The direction (user, 2026-07-27)

> "typecheck must emit fully concrete-typed syntax tree including calls to primitives. Poly
> or generic calls must be unrepresentable. How backend implements poly primitives and
> intrinsics is a backend concern. They may have to be generated as calls to rust closures
> (which have the details of the type closed) for example. I don't think we should tolerate
> any slotted-and-polymorphic."

Plus: REDs are not a constraint during this work; a large facade change is expected and will
drive change into the crates; **`cranelisp-types` is fixed first, then washed through**.

### Consequence for the landed ruling — flagged, not smoothed

`/arch`'s **I-ABI** (`design/arch/total-concreteness.md`, commit `d5723831`) permits a closed
roster of four hand-written polymorphic callables — `bind`, `race`, `select`,
`catch-runtime-error` — slot-less but **polymorphic at the typecheck boundary**. Requirement
**R-25/R-27** below overrides that: at a call site those types *are* known, so typecheck must
emit a concrete call and the polymorphism becomes a backend implementation detail (one body,
per-type closures, or per-instantiation emission — backend's choice). The roster, if it
survives at all, survives *inside* the backend and is invisible to the tree. `/arch` needs to
re-rule I-ABI on this basis; `/qa`'s **NC-R** roster-pin cell (committed `743126b5`) is
likely superseded and should not be built until that is settled.

---

## A — Representation: what must be unrepresentable

| # | Requirement | Evidence it is violated today |
|---|---|---|
| R-1 | A GOT slot cannot exist on a non-concrete entry. Not checked — **unrepresentable**. | Slotted-and-polymorphic today: every generic-ADT ctor (mandatory slot on `DefKind::Constructor`), `IO.Bind`, `vec-len`. |
| R-2 | The slot⟺concreteness relation must not be a `⟺` between two independent fields. | `ModuleEntry::Def { scheme, kind, .. }` — `UserFnState::Concrete { got_slot }` is constructible over any scheme; nothing joins them. |
| R-3 | One slot carrier, or all carriers gated by one fallible mint. | **Five** independent carriers (corrected 2026-07-27 — I under-counted): `UserFnState::Concrete`, `DefKind::Constructor`, `PrimitiveBody::Extern`, `SymbolTable::next_got_slot`, and **`src/platform.rs:351`, which writes `next_got_slot` directly**. Unified only on the *read* side by `callable_got_slot()` (`module.rs:1445`). |
| R-4 | No constructor may assert a property it does not check. | `scheme::mono` (`typecheck/src/scheme.rs:10-17`) sets `type_vars: vec![]` **without inspecting the type at all**. The name is the fabrication. |
| R-5 | `ConcreteType` must not be constructible except through a checked path. | Its variants are `pub`. `from_type` is "the only way to obtain one *from a `Type`*" — true, and no defence against direct literal construction, which is how four of the fabrication sites work. |
| R-6 | Backend metadata must carry concrete types, not `Type`. | `CtorField { ty: Type }` (`backend/compiler/context.rs:274-281`), populated from the ctor **declaration's** polymorphic scheme → `Type::Var(a)` permanently. |
| R-7 | The `MonoExpr` model — every node carries `ConcreteType`, no variable case — is the target shape and must be propagated, not weakened. | Already correct. `MonoExpr`/`MonoDefnVariant` are the reference implementation of this register. |
| R-8 | Templates must remain representable **as templates** (slot-less, non-codegen) while being unrepresentable **as callables**. | Cross-module monomorphisation requires the producer's `Polymorphic`/`Constrained` template + `ast` to persist and travel; the consumer mints the instance from it. Do not break this while closing R-1. |

## B — Fabrication: the boundary discards

Two families. **Family A** discards the `Result` from `ConcreteType::from_type`. **Family B**
fabricates a `Type` *upstream* so it then passes `from_type` cleanly — invisible to any check
built for family A. Both must close.

| # | Site | Family | Substitution |
|---|---|---|---|
| R-9 | `backend/compiler/fn_compiler.rs:1287` | A | `.is_err()` → threshold-guessing branch. **This is the wild write.** |
| R-10 | `typecheck/ownership/fixpoint.rs:221` | A | `unwrap_or(ConcreteType::String)` — ownership inference assumes a **heap pointer** for an unresolvable type. Its inline soundness claim covers only the Copy⊑Borrowed edge, not the Borrowed-vs-Owned axis that matters. |
| R-11 | `types/mono_expr.rs:836` | A | `unwrap_or(ConcreteType::Int)` — the lenient view (FIXME 0913). |
| R-12 | `backend/drop_glue.rs:398` | A | `unwrap_or(ConcreteType::Int)`. |
| R-13 | `backend/compiler/context.rs:280` | **B** | `unwrap_or(Type::Int)` when the field index exceeds the param list. **Launders** — the fabricated `Int` subsequently passes `from_type`. |
| R-14 | `backend/compiler/fn_compiler.rs:1214` | B | Defensive dead arm; unreachable by local construction. Wrong spelling; low severity; must not be left unscored. |
| R-15 | `src/eval.rs:586`, `src/repl/commands.rs:632`, `src/pipeline.rs:133` | B | Absent display/expr types default to `Int` on a path toward the result-release seam. **Severity ungraded** — grade, do not assume. |
| R-16 | **Preserve the model sites.** `types/heap.rs:310-334` refuses the whole constructor when any field is residual; `typecheck/program/support.rs:321` matches `NotConcrete` explicitly. The revised design must generalise these, not replace them. | — | — |

## C — Mint sites: where polymorphism acquires a slot

| # | Site | What it does |
|---|---|---|
| R-17 | `typecheck/adt.rs:617-628` | Synthesised field accessor minted `Concrete { got_slot }` from a scheme with `type_vars: [a]`. No `is_concrete()` test in the function; the unconditional mint is documented as intentional at `:592`. |
| R-18 | `typecheck/traits/impl_check.rs:1039-1043` | Trait-impl method laundered through `scheme::mono`. Compounding harm: zeroing `type_vars` makes the entry **permanently ineligible** for later monomorphisation, since `entry_is_monomorphisable_polymorphic` requires non-empty `type_vars`. |
| R-19 | `DefKind::Constructor` | Slot is a mandatory field, ungated. Every generic-ADT ctor is slotted-and-polymorphic. |
| R-20 | `vec-len` | The only slotted polymorphic primitive. (`vec-get`/`set`/`push` are `PrimitiveBody::Inline` and already concrete-per-use — the model.) |
| R-21 | `src/platform.rs:360-430` | `PlatformEffect` schemes are concrete at HEAD, but a lowercase manifest-sig leaf would smuggle a `Type::Var` through **unrefused**. Mint-side gate owed. |

## D — Monomorphisation: discovery vs construction

| # | Requirement |
|---|---|
| R-22 | Specialisation must be **forced by construction**, not opt-in by discovery. Today it is a walk with four collectors and a nine-condition chain (`typecheck/program/mono_collect.rs:567-583`); a missed call site silently falls through to a poly body wherever one is slotted. |
| R-23 | Synthesised bodies must be instantiable **and the instance must be sound**. ~~The generic mono path cannot produce an instance~~ — **corrected 2026-07-27**: it *can*. The dotted spelling `(Bx.v (Bx 5))` mints `user/Bx.v$user/Bx$Int`, and **that instance is unsound** — its CLIF carries the `<1024`-guarded `atomic_rmw` on the field word, and `(Bx.v (Bx 1024))` crashes. So monomorphisation alone is **not sufficient**: the mono body is still built through the declaration→`CtorMeta` channel (R-6). A-MINT is strengthened, not weakened — and R-6 and R-23 are one problem, not two. |
| R-24 | **RESOLVED 2026-07-27 — and my narrowing was wrong.** Both suspects *pass*: `checker.rs:1733-1737` records `VarRef::Global` for the bare alias, `checker.rs:2148-2155` succeeds. The actual cause is the **collector→mint identity handoff**: `mono_collect.rs:592` pushes `resolved.fq.symbol` — the *written spelling* `v` — and `get_constrained_fn`'s raw local probe (`monomorphise.rs:1171`) lands on the bare-alias `ModuleEntry::Import`, which its match rejects, returning `Ok(None)` **silently**. The 0620 alias class, one line below the comment stating the rule. Differential proof: bare `(v (Bx 5))` mints nothing; dotted `(Bx.v (Bx 5))` mints. Owned by FIXME **0935** (`/design` typecheck). |

## E — The concrete-tree requirement (user, 2026-07-27)

| # | Requirement |
|---|---|
| R-25 | Typecheck emits a fully concrete-typed syntax tree, **including calls to primitives**. `bind`, `race`, `select`, `catch-runtime-error` appear as concrete calls; their types are known at every call site. |
| R-26 | Poly/generic calls are **unrepresentable** in the emitted tree — a structural property, not a checked one. |
| R-27 | How the backend realises a polymorphic primitive or intrinsic is a **backend concern** — one shared body, per-type Rust closures with the types closed, or per-instantiation emission. Invisible to typecheck and to the tree. |
| R-28 | **Zero slotted-and-polymorphic entries.** No licence, no roster, no kind partition at the typecheck/types boundary. |

## F — Persistence and cross-crate

| # | Requirement |
|---|---|
| R-29 | Serde **bypasses smart constructors**. The cache load boundary must re-check restored entries, or a stale sidecar reintroduces every defect this programme closes. |
| R-30 | Schema-window discipline: each `CACHE_SCHEMA_VERSION` increment has exactly one owning change-set. The S120 witness mint was designed to need none (serde shape unchanged) — confirm that survives the revised design. |
| R-31 | `defined_symbols()` (the codegen manifest projection) admits no non-concrete scheme. It is a projection, not a second store — do not split the symbol table. |

## G — The IO existential

| # | Requirement |
|---|---|
| R-32 | `Bind` holds `(IO b, Fn [b] (IO a))`; the intermediate type is not recoverable from the outer type. Confirm the revised design makes this a **representation** concern (a payload-glue word stamped at the concrete construction site — the closure `DROP_GLUE_PTR` precedent, not the rejected R15 header word) and **not** a type-system residual. Under R-25/R-26 every construction site is concrete, so the stamp is always mintable. |

## H — Instruments that must exist

| # | Requirement |
|---|---|
| R-33 | NC-1 — universal slot sweep, `callable_got_slot().is_some() ⇒ scheme.ty.is_concrete()`, whole-table, kind-free, with the durable `_no_unattributed_violations` residual. |
| R-34 | NC-2 — fabrication census covering **both** families A and B. A family-A-only census is blind to R-13. |
| R-35 | NC-5 — `CtorMeta` concrete-or-refuse, two legs (behavioural + structural retirement of the hand-rolled `scheme.ty` walk). |
| R-36 | R17's census arm-flip must become **reachable**. It is gated on the census reading zero, and polymorphic-ctor field categorisation is permanent traffic until R-19 closes. |
| R-37 | Every instrument carries a **detection proof** — planted fault caught, and the negative leg (silent when the fault is absent). Per §Assurance and FIXME 0768. |

## I — Process requirements (root `CLAUDE.md` §Assurance)

| # | Requirement |
|---|---|
| R-38 | Every invariant is structurally unconstructable or continuously measured. "Graded by inspection" is not a grade. |
| R-39 | No invariant is stated universally with an unstated exception. Where an exception is representation-contingent, **eliminate it rather than partition the invariant**. |
| R-40 | Claims about source are verified **at source**, not by citing an authority that asserted them. Three claims in the S119 design conversation propagated two hops before anyone opened the file; the citation-drift gate (`scripts/verify-citations.py`) covers documents, not authority-laundering in prose. |

---

## Wash order

**`cranelisp-types` first** (user direction). Its share of the register: R-1, R-2, R-3, R-5,
R-6, R-7, R-8, R-11, R-16, R-29, R-31. Landing these first makes the illegal states
unrepresentable at the source of the vocabulary, so every downstream crate's fix is a
*compile error to resolve* rather than a discipline to remember — which is the whole thesis.

Then, in dependency order: `cranelisp-typecheck` (R-4, R-10, R-17, R-18, R-22, R-23, R-24,
R-25, R-26), `cranelisp-backend` (R-9, R-12, R-13, R-14, R-27, R-32), `cranelisp-primitives`
+ `cranelisp-intrinsics` (R-20, R-27), `src/` (R-15, R-21, R-30), `tests/` (R-33–R-37).

**REDs are not a constraint during the wash** (user direction). The suite's role here is
differential — what *changed* — not absolute.

## Open items — status 2026-07-27

The revised design is `design/arch/concreteness-types-first.md` (commit `c2783975`), whose §6
carries the 40-row cross-check. Disposition of the four items this register opened:

1. **R-24 — RESOLVED.** See the corrected row. My narrowing was falsified; the cause is the
   written-spelling handoff, FIXME 0935.
2. **I-ABI — RESOLVED as I-EMIT.** The emitted tree references no polymorphic callable. The
   shared Rust body survives *below* the tree as the backend-interior **realization roster**
   with declared representation dependencies — an enumerated contract, not an invariant
   exception, so R-39 is discharged rather than evaded. `/arch` recorded its own earlier
   "wrappers add names without soundness" argument as **overruled**: the name is where the
   type closes. **NC-R is not dead** — it survives mechanically (the assertion is still true
   at HEAD and buildable now) and mutates in meaning; FIXME 0936.
3. **R-15's severity — still open**, deliberately ungraded.
4. **Schema bump — ANSWERED: one bump.** Forced by `CtorState { Template, Concrete }`
   replacing the constructor's mandatory slot, and shared with the S120 window.

Still open beyond the above: **R-15**, and the whole register's *confirmation* — every row
now has a disposition in `concreteness-types-first.md` §6, but a disposition is a claim, and
the rows are confirmed only when their instruments (R-33–R-37) execute.
