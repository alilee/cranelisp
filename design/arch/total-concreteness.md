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
**Archive trigger:** the S120 tranche and the S121 Bind tranche (this document’s sections 5.2 and 5.3)
land; the invariant statements fold into BC §7 + `module.rs` rustdoc + R11; this
file moves to `design/arch/archive/`.

> **AMENDED 2026-09-01 (`/arch`, S121 Phase 3): the route's vehicle changed;
> the invariants did not.** The user adopted the unified symbol-lifecycle
> target (`symbol-table-lifecycle.md`, disposition 2026-09-01), so the
> "S120 tranche" staging in §5.2 is superseded as a schedule: the per-kind
> `CtorState` flip does not land first — the ctor template-slot retirement
> ([constructor retirement](total-concreteness.md#31-constructors-rows-12-monomorphise-per-instantiation-the-template-slot-retires), FIXME 0931), the `vec-len` de-slot (§3.2, 0932), and the platform
> `Type::Var` refusal (§3.5, 0933) all land as arms of the ONE S121 C1-led
> lifecycle wash (`Life::Template`/`Concrete`, the §5.5/§5.6 population
> installs, the manifest-order mint). §5.3's Bind payload-glue tranche
> (0934) is INCLUDED in S121, ruled below in §3.4. I-CONC/I-FRAME/I-EMIT
> stand unchanged; the lifecycle machine is their representation.

> **AMENDED 2026-09-21 (`/arch`, S122 Phase 5; user ruling): IO values are
> reusable descriptions of work.** Forcing a node never moves a field out of it:
> a `Pure` force retains the payload, and an `Effect` node owns a repeatable
> thunk that teardown discharges. This replaces the S121 once-only `Pure` claim,
> whose refusal on legitimate reuse was a compiler defect. Canonical contract and
> delivery status: §3.4; safety-register row R20.

> **AMENDED 2026-07-28 (`/arch`, the design commission): I-ABI is re-ruled.**
> The user's follow-on direction (R-25/R-27, preserved in
> `design/arch/concreteness-types-first.md` §6 — "typecheck must emit fully
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
| 4 | `vec-get`, `vec-set`, `vec-push` | `Primitive { body: Inline }` | `∀a.…` | **NO — slot-less by construction** (unit-pinned, `primitives/src/tests.rs:75-99`); emitted inline at each concrete call site; value-position via the backend's span-keyed `__wrap_…__` closure wrappers over the same inline lowering *(corrected 2026-09-01: the `__inlwrap_{bare}_{sig}__` per-concrete-sig family originally cited here never existed in source — §3.2)* | `declarations.rs:672-704` |
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
> (the value-position wrapper family / the mono mint) — the *dispatched*
> surface is concrete even when the *body* is shared. *(Corrected 2026-09-01,
> within this retained superseded record: the wrapper family this text named
> as `__inlwrap` was never a source name; the live family is the span-keyed
> `__wrap_…__` closure wrapper — §3.2.)*

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
layouts), and value-position use goes through the backend's span-keyed `__wrap_…__`
closure wrappers over the same inline lowering (§3.2's mechanism
correction). They are **not a residual** — they are the model the rest of the
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

> **SETTLED + GATE RULED (`/arch`, 2026-09-01, S121 Phase 3 — consumes the C5
> primitives design, `design/primitives/s121-c5-primitives-visit.md` §3, and
> answers its §3.8 gate / H1).**
>
> **Spelling (a) — `user_inline` today, `Life::Inline` under the lifecycle —
> is the ruling**, on that design's four source-backed §3.1 grounds: the
> applied path has been inline since S102 (`apply.rs:626-643`; the slot is
> already dead there); the closed three-variant `PrimitiveDecl` set is the
> crate's structural control and spelling (b) would widen it for one row; a
> by-name polymorphic extern is the only row shape that could present a bare
> `Type::Var` to the ABI-kind derivation; and spelling (b) grows the
> uniform-realization roster against the FIXME 0936 trajectory while
> preserving the Fact-A non-consuming-body anomaly. The only in-machine
> alternative under the adopted lifecycle —
> `Life::Template { body: UniformRust }`, the spelling-(b) analogue — is
> rejected on the same grounds.
>
> **Mechanism correction (the `__inlwrap` record — discharges C5 H5(a)).**
> Value-position use of an inline primitive does **not** ride a
> per-concrete-sig `__inlwrap` wrapper family: **no `inlwrap` symbol has ever
> existed in source** (the S102 wrapper-identity naming ruling was never
> realized). The live mechanism is the backend's span-keyed, unit-local
> closure wrapper `__wrap_{name}_{disc}{start}_{end}__`
> (`fn_as_value.rs:154-162`), routed to the inline arm by the kind-keyed
> `is_inline_primitive_at` test (`context.rs:244-255`) and delegating the
> wrapper *body* to `vec_codegen.rs::emit_vec_query_into` (`:1113-1213`) — a
> `(name, arity)` match with `vec-get`/`vec-set`/`vec-push` arms and a
> located-`CodegenError` fall-through. It has **no `("vec-len", 1)` arm**, so
> the de-slot needs exactly one backend edit, fully shaped at C5 §3.4
> (length-word load + the same rc-checked release the `vec-get` arm performs
> + return).
>
> **The gate: the arm is C4's, landed DORMANT before the flip.** Neither of
> C5 §3.8's two routes is taken as offered. The `("vec-len", 1)` arm is
> allocated to **C4's already-reserved backend visit** (its §11 reservation
> is the whole `crates/cranelisp-backend/src/` tree, with a
> `compiler/vec_codegen` module-test row already standing), landed **dormant**
> in C4's implementation wave: both `emit_vec_query_into` call sites
> (`fn_as_value.rs:591-596` value position, `:709-736` auto-curry) are gated
> on `is_inline_primitive_at`, which reads the entry's *kind* — so while
> `vec-len` remains `user_extern` the arm is unreachable and value position
> keeps the working GOT/extern path. C5 §3.8's "cannot be split" atomicity
> claim holds only in the flip-before-arm direction; arm-before-flip is safe
> at every intermediate state, and is the repository's standing dormant→flip
> template. Consequences: C5-primitives makes **zero backend edits** (its §9
> reject 9 tightens to "any backend edit"), the same source area is visited
> once, and no dispensation or C4 re-open is needed.
>
> **Historical S121 ordering (the original lifecycle stream plan is in Git):**
> C4's wave lands the dormant arm → C5's wave flips the declaration
> (`user_extern` → `user_inline`, P0) which makes the arm live → C5's P1
> typed-funnel slice then excludes `vec_len` (already removed). The flip is a
> **precondition of C5's born-settled install conversion**: under the adopted
> lifecycle the settlement funnel refuses a slot mint against a polymorphic
> scheme, so "defer P0, keep `vec-len` `user_extern`" is not an available
> S121 end-state — the only genuine fallback axis is *where the arm lands*,
> not *whether* the de-slot happens.
>
> **Acceptance evidence.** C4 (dormant arm): a `compiler/vec_codegen` unit
> row exercising the `("vec-len", 1)` emission directly, in the same
> change-set (the arm is otherwise landed-with-zero-consumers); dormancy
> proven by the golden-CLIF corpus staying byte-identical and the two
> `tests/vec_query_value_use.rs` `vec-len` cells (`:326`, `:341`) staying
> green via the GOT path. C5 (flip): the same two e2e cells stay green now
> through the inline arm (the acceptance cells, `qa`-owned per C5 H4); the
> projection fixture's one-line diff; the whole-table
> no-slot-with-`type_vars` negative; NC-1's `vec-len` expected-RED retires;
> applied-path golden rows unmoved (C5 §3.3).
>
> **If the C4 allocation proves unsound at wave planning** (e.g. C4's wave is
> already closed when this ruling is consumed), the fallback is C5 §3.8
> route 1 — a scoped dispensation to `dev`(runtime pair) for that one arm,
> atomic with the flip in P0's change-set. Route 2 (re-open C4's design)
> remains disproportionate and is not authorized.
>
> **Public-surface ruling (C5 §10 sign-off).** Deleting
> `crates/cranelisp-primitives/src/vec.rs` with the flip removes exactly one
> baseline line — `pub mod cranelisp_primitives::vec` — an item-free module
> name (`vec_len` is `pub(crate)`), with zero workspace consumers outside the
> crate (only comment references in `cranelisp-intrinsics`, C5-intrinsics'
> own surface). **Approved as a contraction**: the crate is
> workspace-internal, so the only compatibility requirement is the standing
> one — regenerate `public-api.txt` via the canonical command in the same P0
> change-set, diff included beside the source change
> (`design/arch/CLAUDE.md` §Baseline-diff discipline). No shim, no
> deprecation window.
>
> The two secondary `vec-len` declaration-site records move in their own
> already-reserved streams, not in a new visit (C5 H6): the
> `cranelisp-types/src/module.rs:2638` "one polymorphic `Primitive{Extern}`"
> rustdoc in C1's wash, and the independent scheme seed at
> `cranelisp-typecheck/src/builtins.rs:1157-1167` in C3's. The `qa`
> attribution of the `Mode`-keyed wrapper-adaptation ownership defect (C5
> §2.3 / H4) is **not** decided here and this gate does not depend on its
> repair — the flip removes `vec-len` from that population without touching
> `emit_d24_adaptation`.

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

The existential is real — `b` in `Bind { inner: IO b, cont: Fn [b] (IO a) }` is
not recoverable from `IO a`, so monomorphising every caller still leaves a
runtime teardown walk unable to name a nested `Pure b` payload's type. The cure
is the architecture's standing pattern (closure `DROP_GLUE_PTR`, Decision 0011):
**local self-description, stamped at the concrete construction site.** Under
I-FRAME every site that constructs an IO node is concrete post-mono, so the
existential becomes a representation fact — no type-system residual and no
header type-word (R15 stands: one glue pointer on one runtime-owned node
family). The `Bind` *entry*'s existential scheme survives as a
checking/introspection artefact; compiled code and slots are where polymorphism
ends.

#### Layout and stamp (produce side) — delivered S121

- The glue word is a hidden second field on the **`Pure` node only**:
  `[header | tag@16 | payload@24 | payload_glue@32]`. Every other IO node keeps
  its layout: `Effect`'s thunk and `EffectPoll`'s state closure are
  Rust/closure-owned, `Bind`'s continuation carries its own `DROP_GLUE_PTR`, and
  `Par`/`Select`/`Launch` children are IO nodes walked recursively. Pattern
  matching binds field 0; IO mints no accessor for the hidden word.
- The word is a **witness, written once before publication**: `0` (`Scalar`) —
  the payload owes no discharge — or the canonical `drop<T>` address
  (`Owned(glue)`), the same glue every other release site calls (release-contract
  reject criterion 5). The type is known at the stamp site, which closes the
  wild-write-on-scalar class by construction. `1` is reserved and emitted by
  nothing; its decode and report are intrinsics interior
  ([ownership and disposal §6.1](../intrinsics/ownership-and-disposal.md#61-the-pure-payload-witness--retain-on-force)).
- Stamp authority is the backend's alone, over the closed set its design
  enumerates ([backend release contract](../backend/non-concrete-release-contract.md)); the runtime allocates no
  `Pure`. The platform writes only `0`, and the platform-return seam below
  replaces it.

#### Ownership on force — IO values are reusable (user ruling, 2026-09-21)

`spec/10-io.md` §10.8.1 owns the language statement. The representation rule:
**a force never moves a field out of a published node.** The node keeps every
reference it owns until `free_io_node` discharges it at count zero, after the
zero decrement and its Acquire fence; a force hands its consumer a *new*
reference or a borrow. Two owners of one obligation therefore have no
representation (Principle 20), and nothing arbitrates between force and
teardown. Deleting the former once-only claim without the retain would restore a
double discharge; choosing a move from the node's count or freshness is rejected
(intrinsics invariant 5).

| Node | Rule | Status (2026-09-21) |
|---|---|---|
| `Pure` | Force reads the witness; `Owned(glue)` ⇒ one `rc_inc` of the payload for the consumer. Teardown discharges `Owned(glue)` under both dispositions. Private to intrinsics: no layout, stamp, public-API or ABI effect | Implemented in the working tree; reviewed with no blocking finding; **not accepted**. Sequential reuse and heap balance pass (IOR-1/IOR-2); the reserved-word cells and their detection proof pass. QA accepted the correction evidence; integration remains pending |
| `Effect` | The node owns a repeatable, thread-safe thunk. Force borrows it; teardown destroys it once under both dispositions. Changes `cranelisp-platform`'s public API and ABI — approved delta below | Producer and consumer implemented and reviewed; generated baseline matches the approval; **user confirmed the generated diff on 2026-09-21**. Sequential reuse (IOR-4) and module lifetime tests pass. The corrected composed unforced-capture fence passes and is proven to detect omitted teardown |
| `Launch` | Force still moves the sub-tree out through a non-atomic `0` sentinel | **No correction is approved or scheduled.** A second force is unmeasured; a measured fault enters through `qa` |
| `EffectPoll` | Node untouched; one state closure is re-entered | Re-entry unmeasured; no change approved |
| `Bind`, `Par`, `Select` | No mutation on force | Inherit their leaves' behaviour |

Cost of the `Pure` rule is derived, not measured (intrinsics design §6.1): one
atomic increment per heap-payload force and one glue call at teardown, replacing
an atomic exchange per force. Trigger for measurement: a `Pure`-dense regression
attributable to this seam.

#### `Effect` public API — approved by the user, ABI 11

Producer `cranelisp-platform`, `impl<CL: CLType> CLIO<CL>` and crate root:

```text
- pub fn effect(f: impl FnOnce() -> CL + 'static) -> Self
+ pub fn effect(f: impl Fn() -> CL + Send + Sync + 'static) -> Self
- pub fn effect_on_resource(token: i64, f: impl FnOnce() -> CL + 'static) -> Self
+ pub fn effect_on_resource(token: i64, f: impl Fn() -> CL + Send + Sync + 'static) -> Self
- pub fn effect_on_resource_with_capacity(token: i64, capacity: i64, f: impl FnOnce() -> CL + 'static) -> Self
+ pub fn effect_on_resource_with_capacity(token: i64, capacity: i64, f: impl Fn() -> CL + Send + Sync + 'static) -> Self
  pub unsafe fn call_effect_thunk(thunk_ptr: i64) -> EffectOutcome      // signature unchanged
+ pub unsafe fn drop_effect_thunk(thunk_ptr: i64)
- pub const ABI_VERSION: u32 = 10;
+ pub const ABI_VERSION: u32 = 11;
```

- `call_effect_thunk` borrows: valid any number of times, from any thread,
  concurrently, until discharge. `drop_effect_thunk` is valid exactly once,
  with no force in progress or to follow. Both live in the platform crate so one
  crate owns the boxed type (Principle 7); source rustdoc carries the caller
  obligations.
- `Send + Sync` is required, not defensive: token-0 `Par` branches run on rayon
  workers and a token with capacity above one admits concurrent holders, so one
  aliased node is called through `&self` from two threads and destroyed wherever
  its count reaches zero. The bound makes an unsafe capture fail to compile in
  the author's crate (Principle 20); a per-node lock would serialize effects the
  platform declared concurrent.
- Unchanged: the `CL: CLType` bound, `EffectOutcome`, `CLIO`, the 40-byte
  `Effect` layout, every `IO_EFFECT_*` offset, re-exports, cache schema.
  `ABI_VERSION` 11 is mandatory: a v10 `FnOnce` box cannot be called by
  reference, and the load gate must refuse it before a force.
- Author semantics: a captured `CLOwned` lives until the node is freed, and each
  force runs the closure again. A closure that moves a capture into a consuming
  call must clone per call; `Rc`/`RefCell`/`Cell` captures move to
  `Arc`/`Mutex`/atomics.
- **Conformance.** Independent review found the implemented surface equal to
  this delta with no extra signature; the stored-thunk alias and the
  capture-drop holder are private. The generated
  `crates/cranelisp-platform/public-api.txt` diff is exactly the three
  constructor lines plus the added `drop_effect_thunk(i64)` line; the
  `ABI_VERSION` line carries no value and does not move. The user confirmed
  that exact generated diff on 2026-09-21.
- **Consumers.** `cranelisp-intrinsics`: the unchanged
  `io_guard::force_effect_thunk_protected` call, and the new teardown edge from
  the `Effect` row of `free_io_node_with_disposition` to `drop_effect_thunk`
  ([design §6.2](../intrinsics/ownership-and-disposal.md#62-the-effect-thunk--borrowed-on-force-discharged-at-teardown)).
  Its fixtures now build through `CLIO::effect*`. The workspace and in-tree
  DLL build succeeds with the approved bounds. The `ABI_VERSION` literal pins
  and adjacent-version rejection fixture follow ABI 11 and pass the final integrated run.

#### Lifetime edges and residuals

A lane forces only while it holds a counted reference, teardown runs behind the
zero decrement's fence, and a `Par` worker's reads are ordered before the root's
teardown by the join its result already rides. These residuals are separate, and
none is cured by the rules above:

- **Severed join** (pre-existing; `qa` intake). A cancelled `Select` loser with a
  rayon bridge in flight detaches its worker: the dropped `run_blocking_branch`
  future abandons the `oneshot`, `pending_bridges` has no drop guard, and
  `block_on_reactor` drains the supervisor but not bridges. The detached
  worker's walk — now including a borrowed thunk call — can race the root's
  `consume_io_tree`: a use-after-free window. Falsifier: a `select` whose losing
  branch holds an in-flight blocking `Par` bridge at cancellation. The cure
  restores the join; it must not add an ownership channel.
- **Capture-destructor trap** (new with node-owned thunks; consciously
  unprotected). Teardown runs outside the signal guard, so a hardware trap
  inside a capture destructor is not contained. Known captures are `i64`s and
  `CLOwned` host references. Trigger: a platform capture owning a foreign
  resource whose destructor can trap. A *panicking* capture destructor is
  contained DLL-side; that containment across a real cdylib boundary is
  asserted, and `design`(platform) and `qa` own its falsifier and
  classification.
- **Abort-path leak** (pre-existing; read at source, unmeasured; `qa` intake). A
  runtime error or dispatch fault returns without releasing the fresh current
  node and un-popped continuations. Retention changes only magnitude — a leaked
  forced node now leaks its payload or thunk with it. Direction: leak, never a
  second owner.
The separate backend scope-result retain defect (IOR-5) is corrected in the
working tree ([backend design §8](../backend/s122-closure.md)). The extra retain
was observed before the change; both IOR-5 controls and IOR-2 now balance.

#### Grades

| Property | Grade |
|---|---|
| `Pure` force retains; teardown discharges once | **Measured** at the module tier: the retain cells were observed failing on a force without the mint. The public heap-reuse balance observation also passes (IOR-2) |
| No store to a published `Pure` or `Effect` node | **Asserted, with a falsifier** — a source fact read once at review, not structural. Falsifier: any non-construction store to such a node's field in intrinsics. The one known post-publication writer is the `Launch` sentinel |
| Reuse-safe thunk across threads | **Structural**: the `Fn + Send + Sync` bound, pinned by the executing baseline guard |
| One thunk discharge; no force overlaps discharge | Discharge-once is **measured** by the red-first intrinsics lifetime cells, including the shared-reference negative leg. Non-overlap is **asserted**; falsifier: the severed join |
| One `rc_inc` is the exact inverse of one `drop<T>` for every stamped payload category | **Asserted, with a falsifier** (source analysis; module cells cover the shallow and bare-nullary shapes only): a category whose glue is not count-gated |

#### The platform-return seam — stamps are tag-licensed (R19)

`compile_direct_call` is the one platform-call chokepoint. Its post-call stamp
dispatches on the **returned node's tag**, never the call target's kind — a
kind-keyed unconditional store is out of bounds whenever a platform fn returns
`CLIO::pure`, which is published author surface:

```
node = <GOT-indirect platform call>            # non-poll; the poll arm returns earlier
tag  = load.i64 [node + 16]
tag == IO_TAG_EFFECT ⇒ store fn_name_ptr → [node + 40]
tag == IO_TAG_PURE   ⇒ store glue        → [node + 32]   # in-bounds at ABI ≥ 10 only
otherwise            ⇒ no write                          # degrades like a null fn-name
```

- The `Pure` arm is the **adoption stamp**: the DLL cannot name a glue address
  (`HostCallbacks` is permanently two fields) and writes `0`; the backend knows
  `T` from the entry's `(Fn […] (IO T))` scheme and overwrites it with the
  canonical `drop<T>` (`DropGlueRegistry::request_if_owning`; `iconst 0` when
  the request declines; a residual `T` is a located refusal — R18). The store
  lands before the node can be forced or transferred. `CLIO` does not implement
  `CLType`, so a nested DLL `Pure` is unconstructable through the facade.
- The crossing datum is absolute byte offset **32**, pinned independently at
  compile time in each owning crate: backend's
  `const _: () = assert!(PURE_GLUE_ABS_OFFSET == 32);` and platform's
  `const _: () = assert!(HEAP_HEADER_SIZE + IO_PURE_GLUE_OFFSET == 32);`. No
  joint or root assertion is added: it would duplicate a relationship already
  structural and give it a second owner.
- Evidence: backend CLIF rows pin the tag load, both stores, the no-write
  fall-through and that the stores are branch-dominated by the tag compare
  (`(IO String)` materialises the same `drop<String>` `FuncId` the release path
  names; `(IO Int)` stamps `0`); a non-platform callee emits no stamp block. The
  `Pure`-returning platform fixture pair observes adoption, discharge and the
  scalar path end-to-end with a no-double-discharge control.

**ABI.** The IO-node family is a layout contract governed by
`cranelisp_platform::ABI_VERSION` (Principle 14): 9→10 carried the `Pure`
widening, 10→11 the `Effect` thunk contract.

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
> (c) `vec-len` — **intentional RED against the S121 de-slot** (FIXME 0932;
> settled + gated at §3.2 — the RED retires at C5's declaration flip).
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

### 5.2 The structural tranche — superseded as a schedule (see the 2026-09-01
amendment box): items 1–6 land as arms of the S121 C1-led unified-lifecycle
wash, not as a standalone S120 per-kind flip

1. **Ctor monomorphisation + template slot retirement** (§3.1) — FIXME 0931,
   `/design`(typecheck) with backend adjacency; ONE schema window shared with:
2. **The types-owned witness mint + R6 load-boundary re-check** (already ruled
   in `f5d30808`, unchanged — it becomes the crate-boundary form of the now
   *universal* gate: with the Constructor exception gone, the fallible
   `Concrete{slot}` constructor and the ctor-instance mint enforce the same
   single predicate).
3. **`vec-len` de-slot** (§3.2) — FIXME 0932; design settled (the S121 C5
   primitives visit + the §3.2 gate ruling): C4 lands the dormant backend arm,
   C5 flips the declaration.
4. **Platform sig `Type::Var` refusal** (§3.5) — FIXME 0933, `/design`(int).
5. **I-ABI roster pin cell** (§3.3) — with 0932's change-set.
6. **NC-1 universal flip** (§4) — FIXME 0930, `/qa`.

### 5.3 S121 — the Bind payload-glue word (§3.4, ruled) — FIXME 0934; retires
the face-4 bounded residual; C4 stamps + C5 discharges + C7 bumps
`ABI_VERSION` 9→10 and rebuilds fixtures.

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
