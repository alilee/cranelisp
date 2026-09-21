# Sprint 121 — the C5 primitives visit

**Status:** DESIGN — pre-implementation. The single `cranelisp-primitives`
design delta for Sprint 121's C5 stream (`sprints/SPRINT.md` §"Coherent work
inside each stream"). One visit, four ordered bundles.

**Scope.** `crates/cranelisp-primitives/src` only. C5 is an ordered runtime
pair; the `cranelisp-intrinsics` half — the handle vocabulary, the discharge
walk, the IO teardown slice — is `design/intrinsics/ownership-and-disposal.md`
and is named here only where this crate consumes it or hands it something.

**Authority.** Elaborates `design/arch/bounded-contexts.md` §4a and
`design/primitives/primitives.md`. Consumes, without re-deciding: the cross-pair
typed-handle contract (`design/runtime/s119-typed-consume-funnel.md`, held and
reconciled by the intrinsics pass — **this visit does not edit it**), the
structural-embedding contract (`design/runtime/s118-structural-embedding-ownership.md`),
the current unified symbol lifecycle (`design/arch/symbol-table-lifecycle.md`
§§4.2, 4.6 and 5.5), the historical C5 stream allocation in
[the S121 lifecycle design at checkpoint
`dc78ddbe`](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/symbol-table-lifecycle.md)
§9,
and `arch`'s `vec-len` ruling (`design/arch/total-concreteness.md` §3.2;
FIXME 0932).

**Verified against HEAD `18bca20d`.** Every "landed", "absent" and "reachable"
claim below was read in source and the reading is cited. Working-tree design
documents (`symbol-table-lifecycle.md`, the C3/C4 visits) are uncommitted and
are cited as design authority, not as source.

**Reconciled 2026-09-01 onto `arch`'s §3.2 ruling.** `arch` settled the
spelling, allocated the one backend arm to C4 as a dormant edit, ordered the
streams, and approved the public-surface contraction. Three consequences run
through this document: **P0 is mandatory and its ordering is fixed** (C4's
dormant arm → C5's flip); **C5 makes zero backend edits**; and the inline
value-position mint question is closed against a table entry. No gate, no
dispensation and no refusal branch survives — the sections that carried them
state the settled order instead.

---

## 1. What this visit settles

| # | Obligation | Bundle | Class |
|---|---|---|---|
| 1 | `vec-len` de-slot: spelling, applied and value-position behaviour, declaration/table/GOT/harvest effects, lifecycle realization, roster projection, tests | **P0** | live implementation, **mandatory and ordered** (§3.8) |
| 2 | The typed consume funnel's primitives half — A3/A2 body flips | **P1** | live implementation (inside the pair's I2) |
| 3 | The shim-fact derivation — one declaration fact, two manifestations | **P2** | live implementation (inside the pair's I2) |
| 4 | Source-backed disposition of 0835, 0848, 0859, 0928, 0932, 0934 | **P3** | retirement / evidence-only / current-state |
| 5 | The `Mode`-keyed wrapper adaptation vs Decision-24 extern shims | §2.3 | **`qa` attribution handoff** with an executable falsifier |

**The through-line.** Obligations 1 and 2 are not independent. `vec-len` is the
one row in the funnel's A2 slice whose typed flip is **not** arithmetic-neutral
(§2.2, §2.3), so de-slotting it first is what keeps I2 a types-only change-set —
the acceptance property the funnel document's own §7 Class-2 screen depends on.
Ordering P0 before P1 is a correctness ordering, not a preference (§6), and P0
itself is unconditional: the born-settled install conversion cannot mint a slot
against `vec-len`'s polymorphic scheme, so an S121 end-state that leaves the row
`user_extern` does not exist (§3.8).

### Document map

| Section | Contents |
|---|---|
| §2 | Consumed contracts, and the three source facts that bind this design |
| §3 | Bundle P0 — the `vec-len` de-slot, fully designed, with its order and its zero-backend-edit boundary |
| §4 | Bundle P1/P2 — the typed funnel, primitives half |
| §5 | Bundle P3 — per-filing disposition and the current-state wash |
| §6 | Bundles in order; wave shape |
| §7 | Source and module-test reservations |
| §8 | Unit-test design (primitives tier) |
| §9 | `review` reject criteria |
| §10 | Public API, schema and ABI effects |
| §11 | Handoffs, collisions, blockers |
| §12 | Next roles |

---

## 2. Consumed contracts, and the three source facts that bind this design

### 2.1 Consumed, not restated

- **The typed handle vocabulary** — `Owned` (not `Copy`, not `Clone`,
  `#[must_use]`, debug drop bomb) and `Borrowed<'a>` (`Copy`, no discharge
  operation), their closed operation sets, the counted trusted base, and the
  `from_abi`/`into_raw` raw entry and exit. Nothing in tranche A exists in source
  at HEAD; this crate's half lands with the intrinsics half in one wave.
- **The derivation axis is `ParamFlow`, never `Mode`.** The S102 CS-B split is
  deliberate: an only-read heap parameter carries the *analysis* fact
  `Mode::Borrowed` while the extern ABI still consumes. The funnel contract
  states the rule and the one named exemption (`sconcat`); this visit
  implements it and does not restate it.
- **C1's unified lifecycle** replaces `PrimitiveBody` with one callable machine.
  Primitives' rows are **born settled**: a concrete extern is
  `Life::Concrete { slot, realization: Realization::ExternShim { .. } }`, an
  inline operation is `Life::Inline`, a uniform polymorphic Rust body is
  `Life::Template { body: TemplateBody::UniformRust { abi_name } }` whose
  instances are `Realization::FacadeOf`. **A polymorphic extern cannot retain a
  slot** — the settlement funnel mints against the declared scheme, so the
  construction does not compile. This crate selects no second lifecycle
  vocabulary; a missing state is a filing to `arch`.
- **The structural-embedding contract** (RE-1/RE-2/RE-3) — one inc on the node
  stored, independent of the embedded structure's size and depth; copied items
  one inc each. `marshal.rs::sconcat` implements it at HEAD and this visit
  spells it in types (§4.3), never re-decides it.

### 2.2 Fact A — the extern shims' consuming convention is not uniform at HEAD

`primitives.md` invariant 7 and the crate's `CLAUDE.md` both state the
Decision-24 rule: *every extern fn decs every heap-typed argument it does not
return.* Read against source, **one user-callable row breaks it**:

| Row | Declared `ParamFlow` | Body | Site |
|---|---|---|---|
| `str-len`, `str-eq`, `neq-string`, `starts-with?`, `ends-with?`, `contains?` | `Consumed` | `rc::consume_shallow` on every heap param | `string.rs:76-77, 88-89, 103-104, 114, 250-251, 262-263, 274-275` |
| `string-identity` | `IntoResult` | `rc_inc`, returns, never decs | `string.rs:121-126` |
| **`vec-len`** | **`Consumed`** | **no discharge of any kind** | **`vec.rs:22-25`** |

`vec.rs` contains no `consume_*` and no `rc_*` call at all. `vec-len`'s
declaration says its parameter is consumed
(`ownership_facts::uniform_for_type(.., Mode::Borrowed)` produces
`param_flow: [Consumed]`); its body does not consume it.

This is the fact that makes `vec-len` special in the funnel's A2 slice. Under
the derivation, `ParamFlow::Consumed` on a heap-carried parameter yields
`Owned`, so the typed body becomes `fn vec_len(v: Owned) -> i64` and the drop
bomb fires unless a discharge is added. Adding one is an **arithmetic change**,
not churn — the mirror image of the `string-identity` case the funnel document
names, and it interacts with Fact B in the dangerous direction.

### 2.3 Fact B — the value-position wrapper adaptation reads `Mode`, and its premise is false for extern shims

`fn_as_value.rs::emit_d24_adaptation` (`:424-474`) emits a **post-call dec for
every `Mode::Borrowed` parameter** of a wrapper's target. Its stated premise
(`:433-436`) is: *"the wrapper owns its params (closure protocol) but the moded
callee borrowed (did not dec) the `Borrowed` positions, so the wrapper releases
them."* That premise holds for a backend-compiled user function, whose
parameters are bound borrowed from the same summary. It is **false for an
extern primitive shim**, which consumes by Decision-24 whatever its `Mode` says.

The path is reachable and kind-blind. For a primitive used as a value:
`emit_wrapper_call` misses the same-unit `func_ids` arm (`:521`), misses the
constructor arm (`:543`), misses the inline-primitive arm (`:591`, which tests
`DefKind::Primitive { body: Inline }` and so excludes every extern row), and
lands on the GOT arm (`:598-648`); `callee_summary_at` (`context.rs:233-236`)
reads the `ModeSummary` off **any** entry including `DefKind::Primitive`, and
`is_abi_conservative` (`ownership.rs:247-249`) is false for
`params=[Borrowed], result=Fresh`. So the adaptation runs.

Consequence, in value and auto-curry position only — the applied path is
unaffected, because a primitive call compiles its args through the uniform
`compile_consuming_arg_list` (`apply.rs:1198-1246`), never the moded variant,
which `compile_moded_user_call` (`:899-913`) reserves for user callees:

- the six `Mode::Borrowed` string rows dec in the shim **and** in the wrapper —
  a double discharge;
- `vec-len` decs in the wrapper and nowhere else — balanced, but only because
  Fact A's missing dec cancels the adaptation's extra one.

**At most one of the two body conventions can be right, and today neither row
set matches its own declaration.** That is the discriminating statement: this is
not a judgment about which convention is nicer, it is an inconsistency inside
one declaration class.

**Authority direction.** The declaration is the authority: Decision-24 fixes the
extern ABI, and the funnel's `ParamFlow` axis is the settled derivation of it.
The emission is the lower carrier and must match. This visit therefore does
**not** weaken any declaration to fit the adaptation, and does not design the
repair, which is backend-interior. It routes the finding with its falsifier
(§11, H4).

**Falsifier — exact, executable, discriminating.** In an agent-owned scratch
directory, under `--run --no-cache` with `CRANELISP_RC_STATS=1` and
`CRANELISP_RC_DEC_CHECK=1`:

```
(defn call1 [f s] (f s))
(defn main [] (add-i64 (call1 str-len "abcd") (call1 str-len "efgh")))
```

Prediction if Fact B holds: a located `STALE RC DEC` report, or a glibc
double-free, from the wrapper's dec of an already-freed `HeapString`. The
**control** is the same shape with `vec-len` over a Vec literal, which must stay
clean and balanced — that is precisely the pair `tests/vec_query_value_use.rs`
already runs green at `:326` and `:341`, and its greenness is the evidence that
the control leg is sound. A second control, `(call1 string-identity "abcd")`
(declared `IntoResult`, so no adaptation), isolates the `Mode::Borrowed`
population.

Grade: **confirmed by reading the complete path, unexecuted.** No probe was run —
this dispatch names no scratch directory and Phase 3 authorizes no product
execution (`sprints/METHOD.md` §2.2).

### 2.4 Fact C — the live value-position mechanism is `emit_vec_query_into`

An inline primitive's value position is served by
`__wrap_{name}_{disc}{start}_{end}__` (`fn_as_value.rs:154-162`), a span-keyed
unit-local closure wrapper, whose inline arm delegates the wrapper *body* to
`vec_codegen.rs::emit_vec_query_into` (`:1113-1213`) — a match on
`(name, params.len())` carrying arms for `("vec-get", 2)`, `("vec-set", 3)`,
`("vec-push", 2)` and a `_ =>` **located `CodegenError`**. **No `inlwrap`
symbol occurs anywhere in source**; the per-concrete-sig `__inlwrap` family
several records once named was never realized, and `arch` corrected its own
records to the live mechanism on 2026-09-01 (`total-concreteness.md` §3.2,
discharging this visit's H5(a)).

This is the fact the de-slot turns on, and §3.4 is where it is discharged.

---

## 3. Bundle P0 — the `vec-len` de-slot

### 3.1 The ruling

**Spelling (a): `vec-len` is reclassified as an inline operation** —
`user_inline` in the declaration inventory today, `Life::Inline` under C1's
lifecycle. Spelling (b) (slot-less by-name extern) is rejected, as is the
in-machine spelling-(b) analogue `Life::Template { body: UniformRust }`.
**Ruled by `arch` on 2026-09-01** (`total-concreteness.md` §3.2) on the four
grounds this section supplied; they are restated because they are also the
reject criteria of §9.

Four independent grounds, each source-backed:

1. **The applied path is already inline; the slot is already dead there.**
   `apply.rs:626-643` intercepts every `is_vec_primitive` name before dispatch,
   and `is_vec_primitive` (`:2580-2582`) already contains `"vec-len"`;
   `vec_codegen.rs:425-431` emits the length-word load and the temporary
   release. No applied call site has reached `shim_vec_len` since S102.
   Spelling (a) is mostly deletion of an unreached path.
2. **Spelling (b) needs a fourth declaration variant, and the closed three are
   the crate's structural control.** `PrimitiveDecl` admits exactly
   `UserExtern` (table entry + shim + slot), `UserInline` (table entry, no slot)
   and `HarvestExtern` (shim, no table entry). A user-callable row with a shim
   and no slot is unrepresentable — deliberately, because extern-without-shim
   and harvest-only-inline are the states the closed set exists to forbid
   (`primitives.md` §2.1, invariant 3; Principles 18 and 20). Spelling (b)
   widens that set for one row, against Principle 6.
3. **Spelling (b) keeps a `Type::Var` inside the ABI derivation's domain.**
   §4.1's `abi_kinds_for` classifies a declared parameter type as scalar or
   heap-carried. That question is answerable for every ground type and for
   `(Vec a)` (always heap-carried), but a by-name polymorphic extern is the only
   row shape that could later present a bare `Type::Var` parameter, where the
   answer differs per instantiation. Keeping the derivation's domain free of
   type variables is worth more than the row it costs.
4. **Spelling (b) preserves Fact A's defect and adds a roster member.** It
   would require adding a discharge to a hypothetical `vec-len` Rust shim —
   which, under Fact B, would convert today's accidental balance into a double
   dec — and it puts `vec-len`
   on the backend uniform-realization roster, against `arch`'s recorded
   preference and the trajectory FIXME 0936 records (`bind`/`race`/`select`
   leave; the roster shrinks to one).

Spelling (a) instead **dissolves** Fact A for this row: with no shim there is no
extern body and no consuming obligation to state, and the value-position
wrapper's ownership discipline becomes explicit and single-sited (§3.4) rather
than an accidental cancellation.

### 3.2 Declaration, table, GOT and harvest effects

One row moves from `user_extern` to `user_inline`, keeping its name, scheme,
`type_vars: vec![A]`, parameter names, docstring and ownership summary
verbatim. The shim clause and its implementation path go.

| Projection | Effect |
|---|---|
| Table entry | unchanged in identity; body becomes the inline arm, so `callable_got_slot()` is `None` and `is_callable_target()` stays `true` — the "resolvable but not slot-callable" kind, not a phantom NULL slot |
| GOT | one fewer allocation and one fewer `store_slot`. `vec-len` is the **last** `user_extern` row in the inventory (`declarations.rs:660`, followed only by inline and harvest-only rows), and `allocate_got_slot` is a monotone cursor over declaration order, so **no other primitive's slot index moves** — no baked relocation in any cached object shifts |
| Harvest | one fewer entry; `harvest_shims` takes only `UserExtern \| HarvestExtern` |
| Export symbol | the generated `#[unsafe(export_name = "vec-len")]` wrapper is no longer emitted. Nothing links `vec-len` by name: `--link` primitive dispatch is GOT-indirect against `__cranelisp_got_primitives`, and by-name `Linkage::Import` is the `HostPromised` class, which `vec-len` never joined |
| `vec.rs` | `vec_len` loses its only non-test caller. The module is **deleted** — body, inline tests, and `pub mod vec;` in `lib.rs`. Keeping an item with no consumer is the state the repository's assurance doctrine names as not-landed |
| Ownership summary | unchanged and still required — an inline row carries a finished `ModeSummary` exactly as the vec trio does |

Deleting `vec.rs` removes one line from `public-api.txt` (§10); it is the only
public-surface consequence anywhere in this visit.

### 3.3 Applied-call behaviour

Unchanged, byte-identical. The interception at `apply.rs:626` is a bare-name
test independent of the entry's kind, so it fires today and after. The emitted
CLIF for `(vec-len v)` — length-word load plus `emit_vec_drop_if_temporary` — is
untouched, and the golden-CLIF corpus rows that cover it must not move. That is
a `review` screen (§9.4), and it is the reason P0 can be graded
behaviour-identical everywhere except value position.

### 3.4 Value-position behaviour — the one arm, landed before the flip

Today `vec-len` as a value takes the GOT arm (`fn_as_value.rs:598-648`) because
`is_inline_primitive_at` (`context.rs:244-255`) tests the entry's *kind*. P0
flips the kind and the same carrier-keyed test routes it to the inline arm
(`:591-596`) **with no backend edit in P0's change-set** — the discrimination is
already kind-keyed, not a name list, and the wrapper body it routes to is
already present by then.

The wrapper body is the `("vec-len", 1)` arm of `emit_vec_query_into`
(`vec_codegen.rs:1113-1213`). It is **C4's**, landed dormant in C4's bundle B8
before P0 runs (§3.8). Without it the flip would reach the match's `_ =>` and
refuse with a located `CodegenError` — the safe failure direction, never a wrong
body or a wild call, but a refusal that would take `tests/vec_query_value_use.rs`
`:326` and `:341` RED. The ordering removes that state rather than tolerating it.

**The arm's complete cost is one match arm**, shaped by the `("vec-get", 2)` arm
it sits beside, minus the bounds check and the element load:

```
("vec-len", 1) =>
    read the length word from params[0]
    release the owned Vec — the same rc-checked release vec-get performs
                            (vec_drop id + the per-element dec fn ptr resolved
                             from the site's element type)
    return the length
```

C4's `dev` owns the spelling. Three properties make this the right shape rather
than a patch, and C4 consumed them unchanged (`design/backend/s121-c4-visit.md`
§8.5):

- **It is Decision-24 conformant by construction.** The inline arm returns
  before `emit_d24_adaptation` is reached (`:595` vs `:645`), so an inline
  primitive's wrapper owns its own ownership discipline — which is exactly why
  `vec-get`'s arm performs its own release. `vec-len` joins that discipline
  instead of relying on Fact B's cancellation.
- **It removes one row from the Fact-B population** without touching the
  adaptation, so it neither depends on nor pre-empts that repair.
- **It completes an existing match** whose fall-through is already a located
  error. It introduces no mechanism, no name list and no second dispatch.

**The arm is in `crates/cranelisp-backend/src/compiler/vec_codegen.rs` — C4's
reserved surface, and it stays C4's.** C5-primitives neither reserves nor edits
it, and `fn_as_value.rs` is edited by nobody: its inline arm is already
kind-keyed. Adding a name test at either call site is a `review` reject on both
sides (§9 item 9; C4 §13 item 11).

### 3.5 Lifecycle realization

Under C1's machine the row is `Life::Inline` — no slot field, no `Realization`,
no view. That is a settled concrete state, so the row stays inside the
born-settled install path with the rest of the inventory, and the universal
`slot ⇒ is_concrete()` invariant loses its last `Primitive`-kind exception:
after P0 the primitives table holds **no polymorphic slotted entry**, and the
`vec-len` row of the NC-1 expected-RED allow-list retires.

**Value position mints no table entry.** `symbol-table-lifecycle.md` §5.5 rules
the inline family's value position to be served **below the table**: the
backend's span-keyed unit-local `__wrap_…__` closure wrapper, routed by the
kind-keyed `is_inline_primitive_at` test, with `emit_vec_query_into` as its body
for the Vec family — an emission artifact like `__lambda_…`, never a symbol-table
entry, so the lifecycle machine stays total over table entries with no state owed
for `vec-len`. An inline name whose wrapper body has no arm is a located
`CodegenError` refusal, never a wrong body; §3.8's ordering is what keeps
`vec-len` out of that state.

P0 therefore depends on no minting story and asks for no new `Realization`
producer. (This is the settled successor to the earlier
`Concrete { minted_from }` reading, which `arch` corrected on 2026-09-01 on this
visit's H5(b) finding: §5.2's machinery is template-keyed end to end — the demand
carries `template: FQSymbol`, the mint probes the template's table — and
`Life::Inline` carries no `TemplateBody` and no `abi_name`. If a table-entry
representation for these wrappers is ever wanted, it is a new `Realization`
producer designed by C1 with its backend consumer, and a filing to `arch`.)

### 3.6 Roster projection and catalog

**`vec-len` joins neither.**

- The **backend uniform-realization roster** is a projection over the callables
  with one hand-written body serving multiple concrete instantiations — under
  the lifecycle, over `Life::Template { body: UniformRust }`. An inline
  operation has no body to share, so the ruled spelling keeps the roster at its
  standing single member. The roster pin must be that projection, never a
  hand-maintained allow-list inherited from the retired I-ABI framing: a
  hand-kept list is a second authority that can disagree with the table, which
  is the failure the pin exists to catch. The pin's home is the stream that owns
  the by-name callables' registration, not this crate (§11, H3).
- The **intrinsics catalog** stays closed against `vec-len`, and a row there is a
  `review` reject on the intrinsics side. Nothing
  in P0 changes that; the representation dependency `vec-len` carries — the Vec
  `LEN` word at a fixed offset for every element type — is intrinsics-owned and
  already structurally pinned by its layout assert.

### 3.7 Exact tests

Primitives tier, `dev`-owned. Existing rows to re-author, and what each must
assert after P0:

| Row | Today | After |
|---|---|---|
| `tests.rs::vec_trio_is_inline_no_slot_and_vec_len_is_extern` | asserts the trio inline/slot-less and `vec-len` extern with a populated slot (`:73-128`) | renamed to the family; asserts **all four** are inline, slot-less by construction, and callable targets. The `expect("vec-len must carry a populated got_slot")` leg is the row that must be observed RED against the unflipped declaration before the flip lands |
| `tests.rs::extern_shims_harvest_covers_full_inventory` | allow-list includes `vec-len` among harvested names (`:565`) | `vec-len` leaves the harvest; the allow-list shrinks, and the row asserts it is **absent** |
| `tests.rs::got_slots_hold_extern_ptrs_for_harvested_shims` | skips slot-less entries (`:156-176`) | unchanged logic; passes with one fewer slot |
| `declarations/tests.rs::full_pre_migration_projection_fixture_is_unchanged` | golden row `vec-len\|user-extern\|…\|shim_vec_len` | the fixture's one row regenerates to `user-inline`; every other line byte-identical — that byte-identity is the evidence the flip touched one row |
| `declarations/tests.rs::all_three_legal_variants_have_the_expected_got_shape` | variant × GOT shape | unchanged; the population of the inline arm grows by one |
| `tests.rs::every_heap_param_primitive_carries_a_declared_summary` | completeness contract | unchanged and must stay green — an inline row still carries its summary |
| `vec.rs`'s two inline tests | pin the offset-16 read | **deleted with the module.** The behaviour they pin is the backend's `compile_vec_len` plus intrinsics' `LEN_OFFSET` layout assert, both of which have their own owners' coverage. Retaining a test for a deleted body is the anti-pattern |

Negative direction, which the pre-flip rows do not cover: a row asserting that
**no** entry in `PRIMITIVES_TABLE` carries both a GOT slot and a non-empty
`type_vars` — the whole-table form of the property P0 discharges, so a future
polymorphic extern REDs it rather than silently reinstating the exception. This
row is cheap, is a projection of the declaration inventory, and is the one new
instrument P0 adds.

E2e acceptance — the two value-use cells at `tests/vec_query_value_use.rs:326`
and `:341` (`vec_len_as_value_two_instantiations_of_one_hof_control`,
`vec_len_as_value_through_hof_returns_length_control`) and any balance evidence —
is `qa`'s and `test`'s (§11, H4). The observation is their **path**, not merely
their greenness: both paths return the same length, so acceptance for the flip is
that they stay green *through the inline arm*.

### 3.8 The order, and the zero-backend-edit boundary

`arch` ruled this on 2026-09-01 (`total-concreteness.md` §3.2, consuming §3 of
this visit and closing the gate this section formerly carried). Neither route the
gate offered was taken; the arm moved to C4 instead.

**The order, binding:**

1. **C4's wave** lands the `("vec-len", 1)` arm in
   `vec_codegen.rs::emit_vec_query_into` **dormant**, inside C4's own reserved
   backend surface as its bundle B8, after C4's B4 so the arm is written once
   against the settled absent-element-type refusal
   (`design/backend/s121-c4-visit.md` §8.5).
2. **C5's wave** flips the declaration (`user_extern` → `user_inline`, P0),
   which makes the arm live.
3. **P1** then runs the typed-funnel slice with `vec_len` already gone from it
   (§2.2, §4.2).

**Dormancy is structural, not scheduled.** Both `emit_vec_query_into` call sites
(`fn_as_value.rs:591-596` value position, `:709-736` auto-curry) are gated on
`is_inline_primitive_at`, which reads the entry's *kind*. While `vec-len` is
`user_extern` the gate is false, the arm is unselectable, and value position
keeps the working GOT/extern path. **Arm and flip therefore need no atomicity in
this direction**: every intermediate state between C4's B8 and C5's P0 serves
value-position `vec-len` correctly, which is the repository's standing
dormant→flip template. Atomicity is required only in the *opposite* order — a
flip that preceded the arm would sit on a refusal — and that order is excluded
by the sequence above.

**Consequences, and the boundary they set:**

- **C5-primitives makes zero backend edits.** P0's change-set is the declaration
  flip, the `vec.rs` deletion, the re-authored pins, and the regenerated
  `public-api.txt` (§10) — nothing under `crates/cranelisp-backend/`. §9 reject 9
  is "any backend edit", with no granted exception.
- **No dispensation is issued and C4 is not re-opened.** The same source area is
  visited once.
- **P0 is mandatory.** Under the adopted lifecycle the settlement funnel refuses
  a slot mint against a polymorphic scheme, so "defer P0, keep `vec-len`
  `user_extern`" is not an available S121 end-state. The former refusal branch —
  exempting `vec_len` from the A2 slice by name and carrying the anomaly into a
  later sprint — is retired; §4.2's `vec-len` row states the settled position
  instead.
- **The only genuine fallback axis is *where the arm lands*, not *whether* the
  de-slot happens.** If the C4 allocation proves unsound at wave planning — for
  example C4's wave is already closed when this ruling is consumed — the fallback
  is a scoped dispensation to `dev`(runtime pair) for that one arm, atomic with
  the flip in P0's change-set. `arch` did not authorize re-opening C4's design.
  Either way P0 lands, and taking the fallback is `sprint`'s to route back to
  `arch`, not this visit's to assume.

---

## 4. Bundles P1 and P2 — the typed consume funnel, primitives half

The contract is the cross-pair document; this section states only what is this
crate's and what live source adds to it.

### 4.1 P2 — the derivation: one declaration fact, two manifestations

For every user-callable row the ownership fact appears in three places, and
after this bundle all three are mechanically tied:

1. **The implementation signature** — enforced by rustc against the body. An
   `Owned` that is neither discharged nor returned bombs; a `Borrowed` cannot be
   discharged at all.
2. **The shim's declared Rust parameter type**, written once in the row —
   enforced by rustc against (1) at the macro's call expansion. A row whose shim
   token disagrees with its implementation does not compile.
3. **The declared Cranelisp type plus `ParamFlow`** — tied to (2) by one unit
   row over the inventory.

The macro consumes the row's type token **twice from the same token**: once to
emit the wrapping at the shim boundary, once to emit the corresponding ABI-kind
datum onto the declaration record. There is no second hand-written assertion
anywhere, which is the whole point (Principle 7).

The two-axis rule — scalar if the declared parameter type is not heap-carried,
borrowed-handle if the declared `ParamFlow` is `IntoResult`, owned-handle
otherwise — is computed by one function, and the heap-carried predicate is
**hoisted out of the two places `ownership_facts.rs` open-codes it today**
(`:24-26` and `:41-42`, each spelling `matches!(ty, Int | Bool | Float)`
inline). That hoist is not incidental tidying: those two copies are the same
fact as the ABI axis, and leaving them separate is how the derivation and the
summaries could later disagree.

**Coverage and the one exemption.** Every `user_extern` and `user_inline` row
is covered — the whole user-callable surface. The three scalar `harvest_only`
rows carry no declared type and the check asserts exactly that they are
all-scalar. `sconcat` is the single genuine exemption, seeded outside the pair;
its shim kinds are tied by legs (1) and (2) only. It is a **named allow-list of
one**, on the existing allow-list precedent in this crate's harvest test, and
growing it past one name is a `review` reject.

**The compile-fail leg.** This crate already proves its macro's illegal shapes
by compiling three UI cases and matching the expected diagnostic
(`declarations/tests.rs:203-231`: extern-without-shim, harvest-only-inline,
callable-without-ownership). Leg (2) of the derivation is a rustc-enforced
property and is therefore unverified until it is proven to reject: **a fourth UI
case** — a row whose shim token contradicts its implementation's handle type —
belongs in the same change-set. It is cheap, it reuses the established harness,
and without it leg (2) is an assertion about a compiler behaviour nobody has
observed here.

### 4.2 Decision-24 semantics, preserved exactly

Four properties the bundle must not perturb, each with what preserves it:

- **Only-read analysis facts stay `Mode::Borrowed`; consumed extern parameters
  stay `ParamFlow::Consumed`.** The derivation reads `ParamFlow` only. A
  `Mode`-keyed derivation would flip the six only-read string rows to `Borrowed`
  handles and silently delete six decs — a real arithmetic change presented as a
  type change. This is the single most important negative property of the
  bundle, and §8 gives it a row.
- **`string-identity` is the one retained-and-returned row.** Its
  `ParamFlow::IntoResult` assigns it `Borrowed`, and its typed body is one mint
  and no dec — arithmetic identical to today's inc-and-return. It is also the
  proof the check is not a tautology: under a flow-blind derivation it would be
  `Owned`, and the typed body would be forced either to leak the incoming handle
  or to delete the inc.
- **The structural-embedding fences hold and become types.** `read_slist`
  returns borrowed elements (they are owned by the chain), each copied item takes
  one mint, and the structural embed takes exactly one — so a walk minting
  references no owner holds produces one drop bomb per surplus reference at the
  frame that minted it. The committed inc-tally fence and the RE-1 cells assert
  the *rule*, not a point, and their assertions must be byte-identical across
  the flip.
- **`vec-len` is out of the slice.** Per §2.2 and §6, P0 removes it before P1
  runs, taking the A2 population from 23 implementation functions to 22. P0 is
  mandatory and ordered ahead of P1 (§3.8), so the slice has no `vec_len` row and
  needs no by-name exemption for one.

### 4.3 P1 — the body flips, interior first

The marshal interior flips before the shim-reached bodies, because that is where
the embedding contract becomes a signature and the rest of the crate's typed
bodies read through it. Nine interior functions carry heap handles
(`alloc_adt_2`, `alloc_adt_3`, `build_runtime_list`, `read_slist`,
`alloc_runtime_string`, `make_sexp_sym`, `shallow_rc_inc`, `quote_sexp_build`,
`quote_slist`); `read_i64`/`write_i64` stay raw as the mechanical accessor layer,
taking a base and an offset rather than a handle.

Then the shim-reached implementations: sixteen in `string.rs`, two in `int.rs`,
two in `marshal.rs`, one each in `float.rs` and `bool.rs`, plus `vec.rs`'s one
only if P0 did not remove it. The scalar `ring0.rs` bodies never flip — they
take `i64` as `Int`/`Float`/`Bool`, never as a handle, and counting them as
un-flipped declarations is the difference between the syntactic and semantic
counts the funnel document's gate turns on.

**Churn safety.** The design move that keeps the test tier a types-only diff is
to flip the fixtures' return types rather than the call expressions, so a
`consume_*(result)` line survives verbatim. Any hunk in this crate's instrument
files that changes a numeric literal, a comparison operator, or the text inside
an assertion is a `review` reject (§9.6). The deliberately-illegal rows —
those that assert a double discharge or discharge a stale pointer — re-express
through the raw entry or through the legal two-reference form; **no new
operation is added to the handle vocabulary to make one compile**, and a row
that appears to need one is a design gap that returns to the cross-pair
contract's owner.

---

## 5. Bundle P3 — per-filing disposition, evidence and the current-state wash

Every C5-allocated filing, classified by its **primitives arm** against live
source. An open filing is not evidence that source work remains: three of the
six have no primitives implementation arm at all.

| FIXME | Primitives arm | Class | Evidence read at HEAD |
|---|---|---|---|
| **0835** slist/sexp heap corruption | **the marshal fix, already landed** | **retirement** | The RE-1 seams are in place: `deep_rc_inc_slist` is deleted (only comment references survive, in `marshal/tests.rs:254,752,761` and the committed repro's `defect:` provenance lines), and `marshal.rs::sconcat` (`:195-221`) takes the head-only embed inc with the contract stated in its rustdoc. The negative guard that a successor walk has not reappeared is committed at `marshal/tests.rs:752-761`. All seven cells in `tests/slist_sconcat_ownership_0835.rs` are present and none is `#[ignore]`d. The remaining faces were re-attributed away from this crate — the abort face to backend match codegen, the prelude-load residue to the `src/`-side marshal boundary (C6). The file's `status: open` and its `refers_to` pointing at the deleted function are documentary residue |
| **0848** diagnostic-mode detection proofs | **none** | **retirement** | Entirely intrinsics-side: the fault-plant hook, the eight detection triplets and the e2e cell are all in `cranelisp-intrinsics` and `tests/`. This crate holds no diagnostic mode, no plant and no detector, and invariant 12 says it holds none by design |
| **0859** ownership facts vs production witnesses | **evidence-only → accepted** | **retirement** | The user accepted disposition 2 on 2026-09-01: R-2 closes on the existing evidence — the typecheck transfer units distinguishing projection provenance, the direct inline-body guards, and the nine committed production witnesses in `tests/s117_ownership_witnesses.rs` — with a named revival trigger for when projection provenance becomes emission-live. **No primitives source work, and none owed.** The declaration facts are complete and unit-pinned in `ownership_facts.rs`. The master's §5 "R-2 evidence limitation" is rewritten from an open obligation to that closed record in this bundle; the plan-row half of the trigger is `qa`'s |
| **0928** S119 gate outcomes | **none** | **absorbed elsewhere** | All four items are recorded in the cross-pair contract by the intrinsics pass. The only one that touches this crate is item 1's constraint on the element-consume callback type, which this crate does not name |
| **0932** `vec-len` de-slot + roster pin | **the declaration flip and its projections** | **live implementation, ruled and ordered** | §3. The spelling and the stream order are `arch`'s 2026-09-01 ruling (§3.8); the backend arm is C4's B8; the roster pin is a projection over the lifecycle state and its home is elsewhere (§3.6). 0932's own text still cites the phantom `__inlwrap` mechanism (§11, H5r) |
| **0934** `Pure` payload glue | **none** | **not this crate's** | The node layout, the witness and the teardown walk are all intrinsics- and backend-side. Primitives holds no IO node and no glue word |

**Current-state records this crate's design owns that live source has
falsified**, repaired in this bundle:

| Record | Falsified by | Action |
|---|---|---|
| `primitives.md` invariants 7, 13 and 14 state the typed-handle discipline in the present tense | no handle type exists at HEAD; nothing in tranche A has landed | re-tense to the ratified target with its landing bundle named — the repository's own doctrine is that a record asserting landed state it does not have is a defect |
| `primitives.md` §5 "R-2 evidence limitation" defers 0859 to Sprint 118 | the 2026-09-01 user disposition | rewrite to the closed record plus the revival trigger |
| `primitives.md` §7 and §9 cite FIXME 0850; §10 cites FIXME 0861 | neither file exists | remove the citations |
| `primitives.md` §10 "Next skills" directs Sprint 117 W6 | four sprints stale | rewrite to current routing |
| `primitives.md` §2.2 represents the extern/inline distinction as `PrimitiveBody` | C1 replaces it with the unified lifecycle | state the distinction and cite the lifecycle for its representation |

Three further stale records are **outside this invocation's boundary** and are
routed rather than edited (§11, H2/H6): the crate `CLAUDE.md`'s citation of
`insert_vec_query_entries` at `lib.rs:291` (the symbol does not exist and the
file is 219 lines), the same phantom symbol in two comments at `tests.rs:518`
and `:546`, and `cranelisp-types/src/module.rs:2638`'s rustdoc calling `vec-len`
"the one polymorphic `Primitive{Extern}`".

---

## 6. Bundles in order

Dependency order, not size. Each is a reviewable change-set.

| # | Bundle | Depends on | Closes | Behaviour class |
|---|---|---|---|---|
| **P0** | `vec-len` de-slot: the declaration flip, `vec.rs` deletion, the re-authored pins, the regenerated `public-api.txt` | C4's dormant B8 arm landed (§3.8); C1's schema-25 window landed (§10) | 0932's primitives arm; the last `Primitive` exception to `slot ⇒ is_concrete()` | applied path **byte-identical**; value position gains an explicit release in place of an implicit one, served by C4's now-live arm |
| **P1** | The marshal interior, then the shim-reached bodies | the pair's handle vocabulary and the flipped `consume_*` signatures; **P0** | the funnel's A2/A3 primitives half | behaviour-identical; signatures only |
| **P2** | The derivation, the macro's two manifestations, the check row and its compile-fail case | P1 | the funnel's G4 half; `string-identity` becomes borrowed | behaviour-identical |
| **P3** | Filing dispositions, the master's current-state repair, the crate's count record | all | 0835, 0848, 0859 primitives arms | no behaviour |

**Wave shape, for `sprint`.** P1 and P2 are the primitives half of the pair's
typed-funnel bundle: the intrinsics signature flip does not compile without
them, so they land **in that bundle's wave**, not in a wave of their own, and
that wave shares no wave with the backend concreteness work. P0 is independent
of the IO and `Sexp` teardown work and may land in the C5 opening wave, but it
must precede P1 (§2.2) and must follow the wave carrying C4's B8 (§3.8).

---

## 7. Source and module-test reservations

**Writable by C5-primitives**: `crates/cranelisp-primitives/src/` (whole tree).

**Requested outside the crate: nothing.** The `("vec-len", 1)` arm in
`crates/cranelisp-backend/src/compiler/vec_codegen.rs::emit_vec_query_into` is
C4's and lands before P0 (§3.8), so C5-primitives edits no backend path at all —
`fn_as_value.rs` included, whose inline arm is already kind-keyed and needs no
change.

**Reserved elsewhere, named so they are not touched:**

| Path | Owner |
|---|---|
| `crates/cranelisp-intrinsics/src/` | C5's intrinsics invocation |
| `crates/cranelisp-backend/src/` (whole tree, **including** the `("vec-len", 1)` arm) | C4 |
| `crates/cranelisp-types/` (incl. `module.rs`'s `vec-len` rustdoc) | C1 |
| `crates/cranelisp-typecheck/src/builtins.rs` (the second `vec-len` scheme seed) | C3 |
| `src/` | C6 |
| `crates/cranelisp-platform/` | C7 |
| `tests/`, `tests/plan/` | `test` / `qa` |
| `crates/cranelisp-primitives/CLAUDE.md` | `dev`, narrow-deployed here |
| `design/runtime/s119-typed-consume-funnel.md` | C5's intrinsics invocation, all sprint |
| `design/arch/`, `design/intrinsics/`, `design/backend/`, `design/typecheck/` | their owners |
| `design/arch/fixmes/` | owning roles delete |

**Design documents this invocation writes**: this file, and
`design/primitives/primitives.md`. Nothing else.

**Module-test reservations**, per the crate's seam map:

| Submodule | Test module | Bundle |
|---|---|---|
| crate root (`lib.rs`) | the crate-root `tests.rs` harness — the inline/slot-less family row, the harvest allow-list, the new whole-table polymorphic-slot negative | P0 |
| `declarations` | `declarations/tests.rs` + `declarations/pre_migration_projection.txt` + `declarations/ui/` — the projection fixture, the variant shapes, the fourth compile-fail case | P0, P2 |
| `ownership_facts` | `ownership_facts/tests.rs` — the summary pins across the heap-carried hoist | P2 |
| `marshal` | `marshal/tests.rs` — the RE-1 fences and the inc-tally fence, types-only diff | P1 |
| `string` | `string/tests.rs` — the extern-boundary balance rows, types-only diff | P1 |
| `vec` | **deleted with the module** | P0 |

---

## 8. Unit-test design (primitives tier)

`dev` owns every row; e2e acceptance is `qa`'s.

| Submodule | Positive | Edge | Negative |
|---|---|---|---|
| declarations — the de-slot (§3) | the four Vec operations are inline, slot-less by construction, and callable targets; the projection fixture differs in exactly one line | the inventory's GOT allocation count drops by one and **no other row's slot index moves** | **no table entry carries both a GOT slot and a non-empty `type_vars`** — the whole-table form, so a future polymorphic extern REDs rather than reinstating the exception; `vec-len` is **absent** from the harvest |
| declarations — the derivation (§4.1) | every `user_extern` row's emitted ABI kinds equal the kinds derived from its own declared type and `ParamFlow` | the all-scalar `harvest_only` rows assert exactly that; the `sconcat` allow-list has **one** name | a row whose shim token contradicts its implementation's handle type **does not compile**, proven by the fourth UI case with its expected diagnostic — leg (2) is unverified until it is observed rejecting |
| ownership_facts (§4.1) | the hoisted heap-carried predicate produces the same summaries for every row as the two open-coded copies did | the `(Vec a)` and ADT parameter types classify as heap-carried | the derivation reads `ParamFlow`, **never `Mode`** — a row asserting that the six only-read string rows derive **owned** handles, which is the exact mis-derivation that would delete six decs |
| string (§4.2) | each typed body's discharge count is unchanged from its raw form; the `string-identity` body is one mint and no dec | empty inputs and caller-owned reuse, verbatim from today | the deliberately-illegal double-discharge rows re-expressed through the legal two-reference form, assertions byte-identical |
| marshal (§4.2) | the embed takes exactly one mint whatever the embedded chain's size and depth; copied items take one each | a nullary-tag tail is skipped inside the mint | the inc tally asserts the **rule** across sizes, not a point; a surplus reference produces one located bomb at the minting frame |

**Detection obligations.** Two rows in this visit are instruments and land with
their proof in the same change-set: the compile-fail case (proven by observing
the expected rejection, and by observing that a *correct* row still compiles),
and the de-slot's whole-table negative (proven by observing it RED against the
unflipped declaration). Asserting either capability without the observation is
not a grade.

---

## 9. `review` reject criteria

1. **A fourth `PrimitiveDecl` variant**, or any user-callable row carrying a
   shim without a slot. The closed three-variant set is the structural control
   (§3.1 ground 2).
2. **An allocated-but-null GOT slot** for any inline row.
3. **A second ownership authority** — a name-keyed classifier, a parallel shim
   map, or a hand-maintained roster list beside the declaration inventory.
4. **A golden-CLIF corpus movement attributable to P0.** The applied path is
   byte-identical (§3.3); a moved frame means the de-slot reached the applied
   emission, which it must not.
5. **A `Mode`-keyed ABI derivation**, or any second hand-written assertion of a
   row's ABI kinds beside the token the macro already consumes twice.
6. **Any hunk in this crate's instrument files that changes a numeric literal, a
   comparison operator, or assertion text** during P1/P2. The flip is a
   types-only diff for those files, and that property is the acceptance
   criterion for churn masking a behaviour change.
7. **A new operation on the handle vocabulary** added to make a primitives-side
   instrument compile. That is a design gap and returns to the cross-pair
   contract's owner.
8. **`vec.rs` retained with no consumer**, or its tests retained for a deleted
   body.
9. **Any backend edit** in a C5-primitives change-set — no exception is granted,
   because the one arm P0 depends on is C4's and lands before it (§3.8). A name
   test at either `emit_vec_query_into` call site is a reject on both sides.
10. **A weakened declaration** — a `ParamFlow` or `Mode` changed to accommodate
    the wrapper adaptation of §2.3. The declaration is the authority; the
    emission is the lower carrier.

---

## 10. Public API, schema and ABI effects

| Surface | Effect | Owner |
|---|---|---|
| `cranelisp-primitives/public-api.txt` | **one line, and only from P0**: `pub mod cranelisp_primitives::vec` is removed with the module. The module exposes no items (`vec_len` is `pub(crate)`) and has no workspace consumer outside the crate, so this is a name leaving the surface, not a capability. P1 and P2 are **zero** — every implementation function and every generated shim is `pub(crate)`, and the funnel's handle types appear only inside shim bodies | C5-primitives; **the contraction is approved** (`total-concreteness.md` §3.2, 2026-09-01) — no shim, no deprecation window |
| `cranelisp-intrinsics/public-api.txt` | the additive handle module and the changed discharge signatures | C5-intrinsics |
| `cranelisp-types` | **zero.** No type crosses from this crate | C1 |
| `CACHE_SCHEMA_VERSION` | **untouched by C5.** The single S121 window is C1's. The de-slot changes a primitive's persisted kind, and pre-window sidecars are invalidated wholesale by that window — so P0 requires no separate bump, but it **must land inside or after** C1's window, never before it | C1 |
| `ABI_VERSION` | **untouched by primitives.** | C7 |
| Emitted-call ABI | **one removal**: the `vec-len` export symbol and its GOT slot. No other primitive's export name, arity or slot index changes. Every surviving generated shim keeps its C-ABI signature; the handle types are Rust-side only | C5-primitives |

**Baseline regeneration** happens **in P0's own change-set**, with the diff
committed beside the source change, using the one canonical command and tool
floor recorded at `design/arch/CLAUDE.md` §Baseline-diff discipline. `dev`
regenerates; `design` keeps the crate-root rustdoc matching; `review` confirms
both are in the same diff.

---

## 11. Handoffs, collisions and blockers

### 11.1 Handoffs out

**H1 and H5 are closed** by `arch`'s 2026-09-01 ruling
(`total-concreteness.md` §3.2; `symbol-table-lifecycle.md` §5.5). Their
identifiers are retired, not reused, because both the ruling and C4's visit cite
them. H5 leaves one residual, carried below.

| # | To | Content |
|---|---|---|
| **H2** | `dev`(primitives) | Crate `CLAUDE.md` current-state, in the implementing visit: the phantom `insert_vec_query_entries` / `lib.rs:291` citation; §"The inline vec trio has NO GOT slot" becomes the family of four; §"Declared ownership facts" keeps `vec-len` in the only-read list but drops the extern framing; §"Submodule seam map" loses the `vec.rs` row. Also the same phantom symbol in `tests.rs:518` and `:546` |
| **H3** | `qa` + the by-name registration stream | The **roster pin must be a projection** over the lifecycle's uniform-body templates, not a hand-maintained allow-list inherited from the retired I-ABI framing (§3.6). `vec-len` does not join it once P0 lands; a hand-kept list is a second authority that can disagree with the table |
| **H4** | `qa` | **The §2.3 finding, for attribution**, with the falsifier, the two controls and the source path already read. Primitives supplies the shape; `qa` attributes and directs the minimal repro, and decides whether the six string rows' value-position double dec is a current-sprint safety prerequisite. Also: 0859's revival trigger into the plan, and **the de-slot's e2e acceptance** — `tests/vec_query_value_use.rs:326` and `:341` are the acceptance cells, and the observation is their *path*: green through the GOT/extern path before P0 (which is also C4's dormancy control for B8, `design/backend/s121-c4-visit.md` §8.5) and green through C4's now-live inline arm after it. Their pre-P0 greenness is additionally the control leg of §2.3's falsifier. Both readings share one pair of cells; `qa` owns them |
| **H5r** | `sprint` → `arch`, C4 | **The residual of closed H5.** `arch` corrected its own records, but two non-arch records still describe value-position inline dispatch as riding a minted `__inlwrap` instance: `design/arch/fixmes/0932` (the filing's own text) and `design/backend/s121-c4-visit.md` §4.1's `Inline` row, whose "ordinary `Concrete × Body` entry" clause is the reading `symbol-table-lifecycle.md` §5.5 now rejects ([lifecycle realization](#35-lifecycle-realization)). Both are their owners' to repair; neither blocks P0. `design/backend/ownership-codegen.md` §13.3 is **not** in this set — it names `__inlwrap_{bare}_{sig}__` as a *planned* wrapper-identity scheme, which `interfaces.md` already dispositions as binding-when-introduced |
| **H6** | `sprint` → C1, C3 | Two second homes for the `vec-len` fact that move with P0: `cranelisp-types/src/module.rs:2638`'s rustdoc calling it "the one polymorphic `Primitive{Extern}`" (C1), and the independent scheme seed at `cranelisp-typecheck/src/builtins.rs:1157-1167` (C3). Neither is a primitives edit |
| **H7** | C5-intrinsics `dev` | Once P0 lands, `catalog.rs`'s note that `vec-len` "rides the GOT via `PRIMITIVES_TABLE`" becomes false. The catalog exclusion itself is unchanged |

### 11.2 Blockers

**None.** Every P0 change-set is inside this crate. What the backend arm creates
is an **ordering dependency** owned by `sprint`, not a blocker: C4's B8 wave
precedes C5's P0 wave (§3.8). The one other sequencing dependency is C1's
schema-25 window, which P0 must land inside or after (§10).

### 11.3 Collisions and findings

1. **`vec-len` has three declaration sites, not one.** The primitives inventory
   (`declarations.rs:660-671`), the typecheck fixture seed
   (`builtins.rs:1157-1167`), and the types-crate rustdoc that describes its
   kind. Only the first is authoritative; the other two must move with it, and
   both are other streams' (H6). This is the shape `primitives.md` invariant 11
   claims does not exist ("adding a primitive changes one declaration row") —
   the claim is true of *adding*, and false of *re-kinding*, and the invariant
   is precise enough that the difference is legible rather than misleading.
2. **§2.3's finding is not created by this visit and is not cured by it.** It is
   pre-existing, it is value-position-only, and the typed funnel makes it
   structural rather than latent — which is the argument for attributing it now
   rather than after I2.
3. **`design/CLAUDE.md` calls `design/runtime/` "historical"** while three live
   cross-pair contracts are homed there and one is being edited this sprint.
   Outside this invocation's boundary; already routed by the intrinsics pass and
   recorded here only so the duplicate is visible.

### 11.4 Open, and owned elsewhere

- **The Fact-B repair** — backend-interior, `qa`-attributed (H4). This is the one
  substantive question this visit raises and does not answer; it is preserved as
  an attribution handoff, not designed around.
- **The by-name roster's membership pin** — no `.rs` asserts closure today, so a
  fifth polymorphic by-name callable would land green. Not this crate's (H3).
- **Two stale mechanism records** in their owners' documents (H5r).

**No user-owned, spec or architecture decision remains open in this design.** The
one that was — the backend arm's allocation — is ruled (§3.8), and the Fact-B
repair is a defect attribution, which is `qa`'s to make and not an architecture
decision this design is waiting on.

---

## 12. Next roles

- **`sprint`** — the §6 wave shape under §3.8's order (C4 B8 wave → C5 P0 wave →
  P1), and H3/H5r/H6's routing.
- **`qa`** — H4: the §2.3 attribution with its falsifier and controls, 0859's
  revival trigger, and P0's acceptance cells read by path.
- **`dev`(runtime pair)** — P0 … P3 in order, each with its §8 rows, its
  declared behaviour class, and (for the two instruments) its detection proof in
  the same change-set.
- **`dev`(primitives)** — H2, the crate `CLAUDE.md` current-state, in the
  implementing visit.
