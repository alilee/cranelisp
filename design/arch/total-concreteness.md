# Total concreteness at the end of typecheck — the re-ruling and its route

**Status:** NORMATIVE RULING (`/arch`, S119, 2026-07-28) — user-directed re-ruling.
**Supersedes in scope:** the S119 step-back ruling's *end-state* claim
(commit `f5d30808`: "the invariant is kind-partitioned, one licence per producer
class"). The kind-partitioned statement survives ONLY as the **transitional**
description of HEAD during S119; it is no longer the target architecture.
**Governs:** `design/arch/bounded-contexts.md` §7 (slot invariant),
`design/arch/safety-invariants.md` §4 R11, the S120+ producer work this document
stages, and the NC-1 assertion form (`tests/plan/s119-test-plan.md` §3.7 — `/qa`
re-routes per FIXME 0930).
**Does NOT supersede:** `design/backend/non-concrete-release-contract.md` faces
1–5 or `design/typecheck/non-concrete-producer-obligations.md` P-1/A-MINT/L-1..3
— every S119 obligation is a strict step toward this target and ships as
planned (§5).
**Archive trigger:** the S120 tranche (§5.2) and the S121 Bind tranche (§5.3)
land; the invariant statements fold into BC §7 + `module.rs` rustdoc + R11; this
file moves to `design/arch/archive/`.

> **AMENDED 2026-07-28 (`/arch`, the design commission): I-ABI is re-ruled.**
> The user's follow-on direction (R-25/R-27 of
> `sprints/concreteness-requirements.md` — "typecheck must emit fully
> concrete-typed syntax tree including calls to primitives … I don't think we
> should tolerate any slotted-and-polymorphic") overrides §2's I-ABI clause:
> the four-member roster does NOT survive as a typecheck-boundary licence.
> The replacement clause **I-EMIT** — no polymorphic callable is referenced by
> the emitted tree; per-member dispositions (`bind`/`race`/`select` re-kind to
> the inline model; `catch-runtime-error` gets per-instantiation concrete
> facades over its one uniform body); the roster survives only as the
> backend-interior **realization roster** — is ruled in
> `design/arch/concreteness-types-first.md` §1, which also carries the
> `cranelisp-types` representation design (`CallableSlot` witness mint,
> `CtorState`), the wash plan, and the 40-row register cross-check. §2's
> I-CONC and I-FRAME stand unchanged; read §2's I-ABI text and §3.3 as the
> superseded record.

---

## 0. The user's ruling, verbatim, and what it binds

> "I disagree with arch — we need concrete types at the end of typecheck. we
> need to eliminate edge cases that seem to need polymorphism. In the future
> when we have more sophisticated storage layouts, there will be no chances for
> generic functions."
>
> "we may also need to handle monomorphisation of polymorphic
> primitives/intrinsics if there are any."

The user arbitrates direction; this document rules the route. The direction is
accepted without dissent, for a reason the S119 census itself supplies: every
licence the step-back ruling granted to a non-concrete slot holder is a property
of the **uniform i64 tag-or-pointer representation**, not of the entry kind.
`design/arch/release-llvm-backend.md` §6/§8 (M5 escape-to-stack, M6 Perceus
reuse, the S83 §12.1 per-type-representation relaxation, Copy-flattening per
`ownership-inference.md` R5) schedules the demolition of exactly that uniformity.
A licence that dies with the representation is not an invariant; keeping it as
one guarantees a silent wrong-body failure at the moment layouts specialise —
`(Vec Int)` flat vs `(Vec String)` pointer-array is the textbook case, and it is
on the roadmap. The kind-partition also kept three licences where the two
unsanctioned S84→S119 mints demonstrated what licence-shadow costs. The user's
route deletes the shadow instead of documenting it.

---

## 1. The corrected census (read at source, 2026-07-28)

This corrects a **factual error in `f5d30808` and in `/qa`'s follow-up
`fdea7e29`**: both name `bind : ∀a b.…` and `catch-runtime-error : ∀a.…` as
*polymorphic slotted primitives*. **They are not slotted.** Both are
`DefKind::PrimitiveExtern` — slot-less, dispatched by ABI name as a
`Linkage::Import` (FIXME 0360, S83 Path 1; `src/bootstrap.rs:884-905`,
`:1129-1160`) — and `callable_got_slot()` answers `None` for them structurally
(`crates/cranelisp-types/src/module.rs:1446-1471`, the `PrimitiveExtern` arm of
the fall-through). A universal `slot ⇒ is_concrete()` sweep does **not** RED on
them. The entries it does RED on are below.

Every polymorphic (non-`is_concrete()`) callable at HEAD, with slot status:

| # | Entry | Kind | Scheme | Slotted? | Where |
|---|---|---|---|---|---|
| 1 | every generic-ADT constructor — user `deftype (T a…)` ctors + the bootstrap seeds `Option.Some`, `Result.Ok`/`Err`, `Pair.MkPair`, `SList.SNil`/`SCons`, `IO.Pure`/`Effect` | `Constructor` | `∀a…. Fn(fields…, T a…)` | **YES — mandatory** | `adt.rs` mint; `src/bootstrap.rs::register_synth_adt` |
| 2 | `IO.Bind` | `Constructor` | `∀a b. Fn([IO b, Fn [b] (IO a)], IO a)` — the **existential** (`b` not recoverable from the result type) | **YES** | `src/bootstrap.rs:760-830` |
| 3 | `vec-len` | `Primitive { body: Extern }` | `∀a. Fn([Vec a], Int)` | **YES** — the ONE slotted polymorphic primitive | `crates/cranelisp-primitives/src/declarations.rs:660-671` |
| 4 | `vec-get`, `vec-set`, `vec-push` | `Primitive { body: Inline }` | `∀a.…` | **NO — slot-less by construction** (unit-pinned, `primitives/src/tests.rs:75-99`); emitted inline at each concrete call site; value-position via the `__inlwrap_{bare}_{sig}__` per-concrete-sig wrappers | `declarations.rs:672-704` |
| 5 | `bind`, `race`, `select`, `catch-runtime-error` | `PrimitiveExtern` | `∀a[,b].…` | **NO — slot-less, by-name** | `src/bootstrap.rs` (876, 925-943, 1129-1160) |
| 6 | the two S119-censused hand-mints: synthetic accessors (F1), residual trait-impl methods (F2) | `UserFn { Concrete }` | non-concrete | **YES — the defects** | `adt.rs:618-637`; `impl_check.rs:1043,1078-1090` |
| 7 | `PlatformEffect` | — | all concrete at HEAD (`type_vars: vec![]` hard-coded, all shipped manifest sigs concrete) — but a lowercase manifest sig leaf parses to `TypeExpr::TypeVar` and would smuggle a `Type::Var` through `parse_and_check_platform_type_sig` unrefused | n/a (state unoccupied) | `src/platform.rs:360-430` |

Not in the census, verified: multi-sig `$Var` clauses register `Polymorphic`
slot-less (`program/finalize.rs:696`); `Overloaded` base entries, macro parents
and `discover-tests` carry no slot; `macros/Sexp` ctors are concrete;
`sconcat`/`quote-sexp`/Trace accessors are concrete `PrimitiveExtern`. The
intrinsics archive (`intrinsics_table()`) backs exactly **one** polymorphic
language callable: `catch-runtime-error`. `bind`/`race`/`select` have no archive
body — the backend intercepts them by name at the `BuiltinFn` apply arm and
lowers IO-node construction inline at the (concrete) call site.

**Consequence of the correction:** the population a universal slot sweep REDs on
at HEAD is rows 1, 2, 3, 6 — generic ctors, `Bind`, `vec-len`, and the two
hand-mints. Not `bind`, not `catch-runtime-error`. `/qa`'s NC-1 kind-partition
table was built on the wrong counterexamples (FIXME 0930).

---

## 2. The target invariant — stated once, no kind licences

Three clauses; each is assertable on its own.

> **I-CONC (the table).** For every `ModuleEntry` in every symbol table:
> `callable_got_slot().is_some() ⇒ scheme.ty.is_concrete()`.
> Universal, kind-free, whole-table. The S84 biconditional restored **as
> stated** — a def has a GOT slot ⟺ its type is fully concrete — with the
> reverse direction enforced behaviourally as today (a missed reachable
> instance is a loud missing-slot failure, never a silent fallback).

> **I-FRAME (the codegen domain).** Every frame the backend compiles, and every
> call, construction, or release site it emits, carries only concrete types.
> `defined_symbols()` admits no entry whose scheme fails `is_concrete()` —
> non-concrete entries are monomorphisation **sources** (templates), excluded
> exactly as `Polymorphic`/`Constrained` already are. Codegen never sees a
> `Type::Var`, at any seam, for any kind.

> **I-ABI (the boundary residual, closed and pinned). — SUPERSEDED 2026-07-28
> by I-EMIT (`concreteness-types-first.md` §1); retained as the record the
> re-ruling amends.** The only polymorphic
> callables that survive are **hand-written runtime bodies dispatched by ABI
> name** — never compiled by codegen, never slotted, never a codegen frame.
> The roster is closed and enumerated (at HEAD: `bind`, `race`, `select`,
> `catch-runtime-error`); a pinned unit cell enumerates it, so a new
> polymorphic import REDs until it is declared with its representation
> dependencies. Value-position use of a roster member or of an inline
> primitive always goes through a per-instantiation concrete wrapper
> (`__inlwrap` family / the mono mint) — the *dispatched* surface is concrete
> even when the *body* is shared.

Under I-CONC + I-FRAME the compiled-code domain reaches **zero polymorphism** —
no licences, no partition table, one predicate. I-ABI is the honest boundary:
a hand-written Rust body is below the type system and cannot be "made concrete"
by typecheck; it can only be (a) kept behind a uniform value ABI it explicitly
declares, or (b) split per layout class when the ABI stops being uniform. Every
language with native code has this seam (OCaml/GHC uniform-representation
externs); what the target adds is that the seam is **four entries, enumerated,
slot-less, and declared** — so when layouts specialise, the entire re-visit
surface is a pinned list, not an archaeology project.

**Why this is assertable where the S84 statement was not.** The S84 defect was
an unstated exception; the S119 partition stated the exceptions but kept three
licence classes to check by three different instruments. Under this target the
slot predicate has **no** exception: rows 1–3 of §1 stop holding slots, row 6
stops existing (P-1), row 7 is refused at mint. The lesson from `f5d30808`
survives with its conclusion inverted at the fork: *an invariant stated
universally with an unstated exception is unassertable — state the exception or
eliminate it*. S119 chose "state"; this ruling chooses "eliminate", and the one
genuine boundary (I-ABI) is stated as its own closed invariant rather than as an
exception to I-CONC.

---

## 3. The route, per census row

### 3.1 Constructors (rows 1–2): monomorphise per instantiation; the template slot retires

**Target.** A generic ctor's canonical entry (`Type.Ctor` member key) remains as
the **declaration-side template** — scheme, tag, `field_count`, `type_def`
facet, docstring, pattern/display/introspection identity — and **loses its
mandatory slot** when its scheme is non-concrete. It is excluded from
`defined_symbols()` like every other template. Concrete-ADT ctors (`Tally`)
keep their slot and are byte-identical to today. Demanded uses are served
concretely:

- **Direct construction** (`(Bx 5)`) is already inline emission at a concrete
  `MonoExpr::ConstrADT` site — no entry, no slot, no change.
- **Value-position use** (`(map Some xs)`) already mints an inline-constructing
  wrapper at the concrete type (`compile_data_constructor_as_value` +
  `compile_ctor_wrapper_body`, `fn_as_value/`). The S120 change is to make that
  wrapper the **instantiation-keyed ctor instance** under the ONE canonical
  mangler (`build_mangled_name` — P-2 of
  `non-concrete-producer-obligations.md` applies verbatim), minted from the
  mono worklist exactly as A-MINT re-runs the accessor synthesiser. A ctor
  instance is a pure function of `(fqtn, ctor, concrete type args)`; its
  `debug_assert!` is `is_concrete()` on the minted scheme.

**Why this is cheap — the measured fact that makes it so.** The release
contract §2.5 measured that the polymorphic ctor template's compiled body is a
**compiled-but-uncalled artifact on every path probed** — the value path mints a
wrapper, the direct path lowers inline. The template body and its slot are
already close to dead weight; census A counted 2,216 template-frame release
admissions per suite run for frames that exist only to be never called. Retiring
them is a deletion, not a build-out.

**Relation to face 1 / I-CT′ (the S119 sequencing question, answered).** Face 1
(delete the template's wild inc/dec pair under I-CT′) ships in S119 **as
planned**: it closes a live memory-unsafety (~89% of the censused class) with a
backend-only change and needs no producer. When the S120 ctor tranche lands,
template bodies stop being compiled at all, and face 1's deletion site vanishes
with them — face 1 is *subsumed, not contradicted*. I-CT′ itself survives as the
statement of why a ctor **instance** body also owes zero RC ops (Decision-24
transfer into the box holds at concrete types too), and — importantly — a
monomorphised ctor body is exactly what specialised layouts require: the frame
that stores fields must know their sizes, and after this tranche it does.

**Costs.**

- *Code size / compile time:* one tiny straight-line body per **value-position**
  instantiation actually demanded (the wrapper population that already exists
  today), minus one compiled template body per generic ctor declaration. Net
  expected ≈ zero or negative. MEASURE-C1: wrapper-mint count across the corpus
  before/after.
- *GOT pressure (`GotExhausted`, 1024 slots/module/session):* templates stop
  allocating one slot per generic ctor declaration; instances allocate only for
  value-position demand, which **already allocates wrapper slots today**. Net
  expected negative. The `primitives` module (home of `Option`/`Result`/`Pair`/
  `SList`/`IO`, all cross-module mono targets per FIXME 0355 home-keying) is the
  one table to watch; MEASURE-C2 records its slot high-water mark.
- *Cache/schema:* `DefKind::Constructor.got_slot: usize` (mandatory) becomes
  state-carried (absent on non-concrete templates) — a **serde shape change ⇒
  one `CACHE_SCHEMA_VERSION` bump**, shared with whatever S120 window `/sprint`
  designates. Note the S120 witness-mint item was ruled "no bump"; the ctor
  tranche forces the window, so the two land in the SAME window.
- *`Bind` specifically:* its slot retires with the class. `Bind` is internal;
  no user value-position use exists, and the existential means no concrete
  instance can be demanded — which is correct, because nothing may call it as a
  value. Its teardown story is §3.4.

### 3.2 The Vec family (rows 3–4): one de-slot; three already-model members

The addendum's instinct is right that the Vec family is the canonical
layout-exposure case — and the source shows the compiler already holds the
answer: **inline primitives are concrete-per-use by construction.** `vec-get`/
`vec-set`/`vec-push` have no shared compiled body: their "body" is emitted at
each call site from the site's concrete `MonoExpr` types (element category
drives the RC arm today; element size/stride would drive it under specialised
layouts), and value-position use goes through per-concrete-sig `__inlwrap`
wrappers. They are **not a residual** — they are the model the rest of the
family converges to, and they survive layout specialisation by construction
because every emission point knows the concrete element type.

`vec-len` is the outlier: the one slotted polymorphic primitive in the system,
`user_extern` with a hand-written body (`vec::vec_len`). Two legal spellings for
S120, `/design`(backend + runtime pair) chooses:

- **(a) Reclassify Inline** — a length-word load is a trivial inline emission,
  same shape as `vec-get` minus the element op. Deletes the extern body's
  language-facing role entirely. Preferred if the emission is genuinely
  element-independent under the current header contract.
- **(b) Reclassify `PrimitiveExtern`** — slot-less by-name, joining the I-ABI
  roster with a declared dependency ("Vec `LEN` field at fixed offset for every
  element type").

Either way `vec-len` stops holding a slot and I-CONC has no `Primitive`
exception. Note the honest layout point the addendum asked for: `vec-len` is
the one family member whose *body* may legitimately survive layout
specialisation (a common length-word is a layout-contract choice); `vec-get`/
`set`/`push` cannot — and they already don't share a body. The family's exposure
is therefore already discharged except for one entry.

### 3.3 The by-name imports (row 5): the I-ABI roster, pinned — SUPERSEDED 2026-07-28

> This subsection's treatment ("minting per-type wrapper symbols that call the
> same body would add names without adding soundness") is **overruled in
> direction by the user** (R-25/R-27): typecheck emits concrete calls for
> every member; the name IS where the type closes. The ruled dispositions —
> `bind`/`race`/`select` re-kinded inline, `catch-runtime-error` behind
> per-instantiation concrete facades, the roster demoted to the
> backend-interior realization contract, NC-R's re-label — are
> `concreteness-types-first.md` §1. The text below stands as the superseded
> record only.

`bind`, `race`, `select` — backend-intercepted by name, lowering **inline IO
node construction at concrete call sites**; no shared compiled body exists for
the construction half. What is shared is the runtime's trampoline/teardown
machinery, which is tag-directed (self-describing nodes). `catch-runtime-error`
— one hand-written C-ABI body (`cranelisp-intrinsics::panic`), passing the
thunk's result word through opaquely and wrapping it in a heap `Result`.

These cannot be monomorphised by typecheck (there is nothing of ours to
compile), and minting per-type wrapper symbols that call the same body would add
names without adding soundness. The target treatment is I-ABI: slot-less
(already true), never compiled (already true), **enumerated and declared** (new,
S120): a pinned unit cell asserts the roster membership exactly, and each
member's entry in the roster names the representation facts it assumes (uniform
value word; IO node tag discipline; closure `DROP_GLUE_PTR`; `Result` Ok/Err
tag order). When the layout regime changes, the roster is the re-visit list;
any member whose assumption breaks either gains a boxed-uniform convention at
the seam or splits per layout class — a decision that sprint takes with the
list in hand instead of discovering the list.

### 3.4 The IO existential (`Bind`): a representation question, and it dissolves

The dispatcher asked for the honest read; here it is. The existential is real —
`b` in `Bind { inner: IO b, cont: Fn [b] (IO a) }` is not recoverable from
`IO a`, so monomorphising every *caller* still leaves a runtime teardown walk
unable to name a nested `Pure b` payload's type. The S119 face-4 ruling
(runtime-directed teardown) is correct and ships as planned, with its **named
bounded residual**: an unrun `Bind` sub-tree's nested `Pure` payload is not
discharged.

But the residual is not permanent, and the cure is the architecture's own
standing pattern (closure `DROP_GLUE_PTR`, Decision 0011): **local
self-description, stamped at the concrete construction site.** Under I-FRAME,
*every* site that constructs an IO node is concrete post-mono — `(Pure x)`
knows `x`'s concrete type; the backend's inline `bind` lowering knows the
intermediate type at each call site. So:

> **S121 tranche (design owed, `/design`(backend)+(intrinsics)):** the `Pure`
> node (or the IO node header uniformly — `/design` chooses the narrower
> sound shape) gains a **payload-glue word**, stamped at construction with the
> canonical `drop<T>` address for the payload's concrete type. The intrinsics
> tag-walker (`free_io_node`, the 0923 split) calls through it when discharging
> a nested `Pure`. The face-4 residual guard (`/qa`'s failing-not-ignored leak
> cell) is the acceptance instrument: it flips GREEN when the word lands.

This makes the existential a **representation fact with local self-description**
— no type-system residual, no header type-word (R15 stands: this is one glue
pointer on one runtime-owned node family, the closure precedent, not a general
type word). It also survives layout specialisation by construction, because the
stamp is minted where the concrete type is known. ABI note: an IO node layout
change is version-gated (intrinsics/backend co-owned) and is why this is S121+,
not S120.

The `Bind` *entry*'s existential scheme survives indefinitely as a
checking/introspection artefact — schemes may quantify; that was never the
problem. Compiled code and slots are where polymorphism ends.

### 3.5 PlatformEffect (row 7): keep the class concrete by construction

One mint-side gate, S120, `/design`(int): `parse_and_check_platform_type_sig`
refuses a manifest sig whose parsed type contains any `Type::Var` (today a
lowercase leaf silently becomes one). A platform fn is a C-ABI body; a
polymorphic platform sig is a declared contract nothing can check and a
smuggling route into an otherwise-concrete class. Refusal message names the
offending leaf. This closes row 7's unoccupied-but-open state permanently.

---

## 4. What `/qa` builds to — NC-1 reverts to the universal predicate

The kind-partition table (`fdea7e29`) is superseded, and its premise examples
were factually wrong (§1). NC-1's corrected form:

> **NC-1 (universal):** walk every entry in every table:
> `callable_got_slot().is_some() ⇒ scheme.ty.is_concrete()`. One predicate, no
> partitions. At HEAD this REDs on: (a) the two `UserFn` hand-mints — open
> defect, flips with CS-1/P-1 (S119); (b) every generic-ADT ctor template incl.
> `Bind` — **intentional RED against the S120 ctor tranche** (FIXME 0931);
> (c) `vec-len` — **intentional RED against the S120 de-slot** (FIXME 0932).
> Each RED traces to its open item per the failing-not-ignored convention; a
> RED outside (a)–(c) is a genuine regression. Partner cell: the I-ABI roster
> pin (§3.3) — slot-less polymorphic imports are enumerated exactly.

This is a cleaner instrument than the partition table: the partition's three
per-kind instruments collapse into one predicate plus one roster enumeration,
and "someone simplified the table back to a universal quantifier" stops being a
failure mode because the universal quantifier is now the ruled form. `/qa` may
choose to land NC-1 with populations (b)/(c) expressed as a pinned expected-RED
allow-list (each entry citing 0931/0932) so the cell itself stays a sharp
regression instrument during the one-to-two-sprint window — that spelling is
`/qa`'s.

NC-5 (the declaration-channel `CtorMeta` sweep) is **unchanged** — it guards a
channel NC-1 structurally cannot see, and the ctor tranche makes its flip
criterion *reachable* (category/glue queries move to concrete instantiations;
the R17 census's ctor partition drains).

---

## 5. Sequencing

### 5.1 S119 — ships exactly as planned

No landed S119 ruling is invalidated as *S119 work*. P-1/CS-1..3, A-MINT, the
F2 mono trigger, L-1..3 defaulting, faces 1–5, 0917, the 0923 intrinsics split:
every one is a strict step toward §2 (they all move population toward
concreteness or delete fabrications). Phase 5 dispatches unchanged. The only
S119-window corrections are documentary: the `f5d30808` texts' factual error and
end-state claim (amended in this change-set: BC §7, `interfaces.md`,
`module.rs` rustdoc, R11), and `/qa`'s NC-1 form (FIXME 0930, before `/testing`
authors the cell).

### 5.2 S120 — the structural tranche

1. **Ctor monomorphisation + template slot retirement** (§3.1) — FIXME 0931,
   `/design`(typecheck) with backend adjacency; ONE schema window shared with:
2. **The types-owned witness mint + R6 load-boundary re-check** (already ruled
   in `f5d30808`, unchanged — it becomes the crate-boundary form of the now
   *universal* gate: with the Constructor exception gone, the fallible
   `Concrete{slot}` constructor and the ctor-instance mint enforce the same
   single predicate).
3. **`vec-len` de-slot** (§3.2) — FIXME 0932, `/design`(backend + runtime pair).
4. **Platform sig `Type::Var` refusal** (§3.5) — FIXME 0933, `/design`(int).
5. **I-ABI roster pin cell** (§3.3) — with 0932's change-set.
6. **NC-1 universal flip** (§4) — FIXME 0930, `/qa`.

### 5.3 S121+ — the Bind payload-glue word (§3.4) — FIXME 0934; retires the
face-4 bounded residual; version-gated IO-node layout change.

---

## 6. Register and principle consequences

- **R11** (`safety-invariants.md` §4): invariant cell restated to §2's
  I-CONC/I-FRAME/I-ABI with the staged populations; the kind-partition text
  demoted to the transitional record; the `bind`/`catch-runtime-error` factual
  error corrected. Done in this change-set.
- **R17/R18:** mechanisms unchanged. Note added to R17: the S120 ctor tranche
  is what makes the census's ctor partition drain to zero reachable.
- **Phase-7 candidate (amends the one recorded in `f5d30808`):** Principle 20's
  refinement is NOT "kind-partitioned scope" — it is: *when an invariant's
  universal statement is falsified by sanctioned exceptions, prefer eliminating
  the exceptions to partitioning the invariant; a partition is a transitional
  record, not an end state. State-or-eliminate, and eliminate when the
  exception is representation-contingent.* The unassertability lesson survives
  verbatim.
- **The I-ABI roster** is the durable manifestation of "declared contract":
  R3/R16 keep their per-member instruments; the roster adds the closed-world
  enumeration those instruments quantify over.
