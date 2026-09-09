# The S121 C4 backend visit — one interior change

**Status:** DESIGN — authored S121 Phase 3, `/design`(`cranelisp-backend`).
Every claim below was verified against live source in this window; where a
filing's central claim is already discharged, that is recorded as a
disposition rather than re-designed (§9). Reconciled 2026-09-01 onto arch's
completed `Pure` ownership-witness contract (`design/arch/total-concreteness.md`
§3.4): the payload is field 0 and the witness field 1; C4 construction and
platform adoption initialise the fresh, unpublished word with `0` or canonical
glue through ordinary stores, and C5 exclusively owns every post-publication
access as the three-state atomic `Scalar(0) | Claimed(1) | Owned(glue)` claim.
Force and teardown both exchange to `Claimed` before payload access; duplicate
force refuses without touching field 0. The backend producer implementation is
unchanged by that re-ruling.
Reconciled 2026-09-01 onto arch's `vec-len` gate ruling
(`design/arch/total-concreteness.md` §3.2, which answers the C5 primitives
design's §3.8 gate): the dormant `("vec-len", 1)` arm is C4's, lands as bundle
B8 (§8.5), and C5's declaration flip activates it with no backend edit.
Reconciled 2026-09-01 onto arch's inline value-position correction
(`design/arch/symbol-table-lifecycle.md` §5.5, standing on the C5 finding at
`design/primitives/s121-c5-primitives-visit.md` §3.5): `Life::Inline` mints no
table entry, so §4.1's `Inline` row states the live below-the-table wrapper
mechanism instead of a minted `Concrete` instance. Discharges C5's handoff H5r.
Reconciled 2026-09-01 onto arch's **platform-return seam** ruling
(`design/arch/total-concreteness.md` §3.4, discharging C7's H2 and closing its
§4.2 residual): the fn-name stamp becomes tag-dispatched at the one chokepoint
and gains a `Pure` adoption arm, allocated to bundle B5 in this same visit. The
stamp set is therefore **four**, not three (§6.3, §6.7); §13 reject 10 reads
accordingly. Discharges C7's handoff H8, and answers its H2′ with the
zero-revisit detector: C4 owns the backend's `PURE_GLUE_ABS_OFFSET == 32`
compile-time pin, while C7 owns its independent platform composition pin
(§6.7.3); neither stream edits the other's crate.
**Subordinate to:** `backend.md`.
**Consumes, does not decide:** `design/arch/symbol-table-lifecycle.md` §§4–5, §9
(the `Life`/`Realization` machine, the one `CACHE_SCHEMA_VERSION` 24→25 window);
`design/arch/total-concreteness.md` §3.4 + `design/arch/interfaces.md`
§"IO Tag Constants" (the `Pure` payload-glue layout, the ABI 9→10 gate, the
platform-return tag dispatch and its window residual — register row R19,
and the once-only-force allocation — register row R20,
`design/arch/safety-invariants.md` §4);
`design/platform/s121-c7-platform-visit.md` §4.1, §4.4, §4.5 (the DLL-side
sentinel, the platform half of the offset pin, the `Pure`-returning fixture);
`design/arch/total-concreteness.md` §3.2 + `design/primitives/s121-c5-primitives-visit.md`
§§3.3–3.4 (the `vec-len` de-slot, the arm's shape and its Decision-24 grounds);
`design/typecheck/non-concrete-producer-obligations.md` §2, §5 (the concrete,
canonically named entries and the partitioned zero census); `design/int/int.md`
§9.1 (the int half of the 0915 subject presentation).
**Re-rules within backend:** `non-concrete-release-contract.md` §5.1–§5.3, §7
(staging), §4 faces 1–4; `s115-carrier-and-rc-sweep.md` §6 (W-B5);
`io-trampoline.md` §1.1/§3.1 (the `Pure` node).
**Carries:** FIXMEs 0747, 0761, 0781, 0782, 0811, 0891, 0900, 0903, 0906, 0907,
0915, 0916, 0917, the backend twin of 0898, the C4 construction half of 0934,
the C4 dormant-arm half of 0932, and the C4-owned rows of the 0929 census.
**Also absorbs:** QA finding R3, the Decision-24 value-wrapper double discharge
(`tests/plan/s121-test-plan.md` §3.3), without adding a second backend visit.

---

## 1. The one sentence

Every RC operation this crate emits is licensed by two facts asked in a fixed
order — **the value's heap category, from its own concrete type; then its
provenance, from the one lattice** — and is emitted through one of exactly three
mechanisms; every item in this visit is a place where a decision escaped that
order, and the visit puts it back rather than adding a guard beside it.

That sentence is not new. What S121 makes available for the first time is the
ability to *finish* it: C1's settlement funnel removes the channel through which
a non-concrete type reaches a compiled frame at all, so the category question
stops having an unanswerable case, and the fabrications that existed to paper
over that case become deletable rather than merely deprecated.

---

## 2. What changed upstream, and why this is not the S119 plan re-run

`non-concrete-release-contract.md` (S119) is the class ruling and its §2
measurement record stands. Three upstream facts landed since, and each moves a
face's disposition from "backend edits an emission arm" to "the state stops
being constructible". Reconciling onto them is the substance of this visit.

| S119 statement | S121 fact | Consequence for C4 |
|---|---|---|
| §7 piece 1: **0917 is the first backend-only piece** | 0917 **landed at S120** (`cbb3be9e`): `ValueProvenance::NoReference` is in `fn_compiler.rs`, the fold seeds at the identity, both thresholds moved, `CtorValueShape` is the three-state probe | Piece 1 is **retirement**, not implementation (§9, 0917) |
| §5.1 step 2: **face 1 first, backend-only** — the ctor template's pair deletes under I-CT′ | Under C1, `Life::Template` has **no slot and no view**, and FIXME 0931 retires the generic-ctor template's slot; ctor instances are minted per concrete instantiation. **A ctor-template frame with a residual parameter is no longer a codegen target at all** | Face 1 is **producer-discharged**. C4 emits no I-CT′ deletion; it *observes* the ctor partition reading zero. The pair's deletion site vanishes with the frames (0931's own acceptance says exactly this) |
| §5.3: `drop<IO T>` tests the tag and calls `drop<T>` for a root `Pure`, and a nested `Pure` in an unrun `Bind` is a **named bounded residual** | Arch ruled 0934 into S121: `Pure` carries a payload-glue word stamped at construction | The residual **never ships**. `drop<IO T>` loses its tag test and its `drop<T>` call: it is a fixed four-instruction body handing the node to the runtime walker (§6). The `/qa` residual leak guard §7.1 owed becomes a GREEN acceptance cell, not a RED |
| §5.1 step 4: flip the `Err ⇒ Mixed` arm when the census reads zero | C3 owns the reading's partition (`Ctor`/`Accessor`/`TraitMethod`/`Plain`) and hands C4 a zero census | The flip is C4's, unchanged in discipline — but §5 below adds the arming leg S119 did not specify, and §7 closes the one channel that would have kept the census permanently non-zero regardless of C3 |

A fourth upstream fact is a **blocker on the S119 criterion as written** and is
this visit's principal technical finding: FIXME 0929 row 3, the *ctor
declaration channel*. `CtorMeta`'s field types are materialised from the ctor
declaration's scheme, so a polymorphic product's field type is `Type::Var(a)`
permanently, and `signature_heap_category`'s `Err` arm licences a guarded RC
path off it — at every use site, no matter how thoroughly C3 monomorphises the
*frames*. The census cannot read zero while that channel stands. §7 closes it.

---

## 3. The mechanism, stated once

### 3.1 The gate order

> **Category, then provenance, then emitter.** A seam asks the value's own
> concrete type for its `HeapCategory`; `NeverHeap`/`Value` emit nothing and
> the seam stops. Only then does it ask `value_provenance` *whose* reference it
> is. Provenance never answers *whether* a reference exists.

This is R-1 (`non-concrete-release-contract.md` §3.1) and it is already the
as-built shape at every seam — the match seam ANDs its plan with `scrut_is_heap`,
the three Vec seams take a Vec-typed operand, the `BorrowRoot` consumer matches
on `signature_heap_category` with empty `NeverHeap | Value` arms. What is new is
that after §7 the *category* question is total: a residual type can no longer
reach it, so "the absence of a category" stops being an answer the gate has to
have a policy for.

### 3.2 The three emitters, and nothing else

| Emitter | Home | What it is for |
|---|---|---|
| the nullary-skip prologue | `heap::emit_nullary_skip_guard` | the ONE tag-vs-pointer decision, for every guarded inc and every guarded dec, in any Cranelift context |
| the canonical typed release | `rc_emission::emit_typed_rc_dec` → `drop<T>` from `DropGlueRegistry` | releasing a heap value, which is a function of its **type**, never of its site |
| the two sanctioned runtime dispatches | the closure's embedded `DROP_GLUE_PTR`; the intrinsics IO tag-walker | releasing a value whose structure only the runtime can see |

A fourth mechanism is a `/review` reject (§11). The 0934 payload-glue word is
**not** a fourth mechanism, at either of the two seams that write it — the three
construction stamps (§6.3) and the platform-return adoption stamp (§6.7): the
word each writes is a `func_addr` of the *same* `drop<T>` the second emitter
calls, obtained from the *same* registry, so no release identity is minted
(`non-concrete-release-contract.md` §8 reject 5). **Four sanctioned stamp sites,
one release identity** — the count that grows is write sites, not mechanisms.

### 3.3 What "one mechanism" absorbs

Each allocated item is the same escape at a different seam. Naming them together
is what stops the next one being fixed with a sibling guard:

| Escape | Seam | Item |
|---|---|---|
| a node kind stands in for provenance | `emit_vec_drop_if_temporary`'s `matches!(Var)` | 0781 — **closed S115 W4c**, kept here as the family's name |
| a pattern kind stands in for the release owner | `compile_var_pattern_arm`'s alias registration + the merge-block dec | 0782 — **closed S118**, resolution (a) |
| a *type* stands in for the frame's licence | `emit_heap_binding_decs`'s `from_type(ty).is_err()` arm | 0903 / 0891 |
| a fabricated category stands in for an absent one | `signature_heap_category`'s `Err ⇒ Mixed` | 0903 / 0916 / 0929 row 1 |
| a *declaration* stands in for an instantiation | `CtorMeta`'s field types | 0929 row 3 (§7) |
| the prologue is re-spelled per context | two copies in `vec_codegen.rs` | 0906 (§8.2) |
| an `unwrap_or` stands in for a refusal | `drop_glue.rs:398`, `fn_compiler.rs:1214`, `resolve_elem_inc_fn_ptr`'s `None` arm | 0929 rows 2 and 4, plus one found this window (§7.3) |
| a name-finder is re-spelled per return seam | `return_var_in_scope` / `return_cow_source_in_scope` / `operand_live_binding_root` | 0747 (§8.3) |
| a strip rule is spelled twice | `compile_to_module`'s `result_roots` | 0898 backend twin (§8.1) |

---

## 4. Bundle B1 — consume the lifecycle, exhaustively

C1 replaces the per-kind `UserFnState` vocabulary with one machine. Backend's
obligation is to consume it **totally**, so that a state combination backend
cannot lower is a compile error in this crate rather than a runtime surprise.

### 4.1 The realization-to-lowering disposition

The disposition is total over `Life<C>` and, within `Concrete`, over
`Realization<C>`. There is no `_ =>` arm anywhere in it; that exhaustiveness is
the instrument (the `classify_auto_curry_target` precedent, crate `CLAUDE.md`
§RC-emission gates row 5).

| State | Backend lowers | Slot populated by | Refusal |
|---|---|---|---|
| `Concrete { realization: Body { view, .. } }` | the view, into the claimed slot. **This projection *is* `defined_symbols()`** — the Decision-22 `ast.is_some()` conjunction and the S120 `is_concrete()` conjunct are subsumed | codegen | — |
| `Concrete { realization: ExternShim { borrowed_sibling } }` | nothing; call sites emit an import against the shim. A `Borrowed`-moded call site selects `borrowed_sibling` when present, and when absent takes the ordinary consuming path | registration | — |
| `Concrete { realization: Dll }` | nothing; call sites are GOT-indirect against the manifest-order slot | the platform loader | — |
| `Concrete { realization: FacadeOf { abi_name } }` | nothing per instance: the slot is populated with the address of the one uniform hand-written body named by `abi_name` (I-EMIT §1.2; `catch-runtime-error`). **No per-instantiation body is emitted and no per-instantiation glue identity is minted** | codegen, as a name-alias | — |
| `Inline` | inline lowering at concrete call sites (`primitives_inline`, and the `bind`/`race`/`select` interceptions). **Value position mints no table entry**: backend emits a span-keyed unit-local closure wrapper (`__wrap_{name}_{disc}{start}_{end}__`, `fn_as_value.rs:157-162`) whose body is the same inline lowering, selected by the kind-keyed `is_inline_primitive_at` (`context.rs:244`) — an emission artifact like `__lambda_…`, below the table (`symbol-table-lifecycle.md` §5.5). B8 supplies that body's `("vec-len", 1)` arm (§8.5) | — (slot-less; the wrapper is not a table entry) | located `CodegenError` when the wrapper body carries no arm for the name — the existing `emit_vec_query_into` fall-through, never a wrong body (§8.5) |
| `HostPromised` | nothing; by-name `Linkage::Import` against the key | the host | — |
| `Template { .. }` | **nothing — a template is not a codegen target.** A value-position reference to one reached codegen without a mint | — | located refusal naming the symbol and that no instantiation was demanded (the 0585 loud backstop, retained and re-keyed off `Life` instead of `UserFnState`) |
| `Declared { .. }` | nothing | — | located refusal: settlement did not run for this symbol before codegen. A compiler-invariant breach, reported as one |
| `Broken { slot, error }` | nothing; the retained slot carries its trap stub | int's session transaction | — (the trap is the behaviour) |

Two consequences worth stating because they are the point of the change:

- **`defined_symbols()` stops being a predicate and becomes a projection.**
  Nothing in backend re-derives "is this compilable" from a kind, an
  `ast.is_some()`, or a concreteness re-check. One filter over one state.
- **`defn_param_types` stops being a residual channel.** It reads the entry's
  `Scheme.ty`; under C1 a `Life::Concrete` entry's scheme has passed the
  settlement witness, so every parameter type reaching `signature_heap_category`
  from this path is concrete **by construction**. That is the grade-1 half of
  §5's close; §7 is the other half.

### 4.2 Cache-load validation

The load boundary re-derives slot authority and validates, per entry:
uniqueness of the claim; `slot ⇒ scheme.is_concrete()`; origin × state legality;
tombstone conservation. Every arm **diagnoses and recompiles** as a
`CacheStale` class — cache bytes are external data and never `assert!`ed
(crate `CLAUDE.md` §"Cache-load validation is ONE loop"). The new arms join that
single per-entry loop in `cache/serialize.rs`; a parallel walk is a reject.

### 4.3 The schema constant — an explicit cross-stream reservation

`CACHE_SCHEMA_VERSION` is defined at `crates/cranelisp-backend/src/cache/mod.rs`
(value 24 at HEAD) — physically backend's file, but the **24→25 edit belongs to
C1's change-set** and is the sole S121 window
(`symbol-table-lifecycle.md` §9).

> **Reservation.** For the whole of S121 the *value* of `CACHE_SCHEMA_VERSION`
> is reserved to C1. C4 does not bump it, does not re-bump it, and does not
> re-write the line C1 edited. C4 remains free to edit the rest of
> `cache/mod.rs` and `cache/serialize.rs` (the §4.2 validation arms).

**C4 needs no schema window of its own**, and this is checkable rather than
asserted: the two candidate movers are not sidecar-shaped. `Realization`'s serde
presence is a `cranelisp-types` shape owned by C1; the `Pure` layout change
(§6) is *emitted code*, governed by `cranelisp_platform::ABI_VERSION` 9→10 in
C7's visit. A serde-shape change discovered inside C4 is a plan violation to
report to `sprint`, not to fix locally with a second bump.

**Stale cached objects that construct one-field `Pure` nodes** are excluded on
two independent legs, and it is worth recording both so the sequencing worry is
retired rather than carried: durably by the 24→25 window's wholesale pre-25
invalidation, and within any developer tree by `BUILD_ID`
(`CacheStale::BuildIdMismatch` fires on any recompiled compiler). The binding
obligation that remains is arch's: **no acceptance cache baseline is captured
between the C1 bump and the C4 layout flip.**

---

## 4A. Bundle B9 — Decision-24 wrapper discharge follows realization

QA R3 (`tests/plan/s121-test-plan.md` §3.3) is confirmed by the live path. The
closure wrapper receives owned parameters, calls the target, and
`emit_d24_adaptation` currently emits a post-call dec for every
`Mode::Borrowed` parameter. That is correct only when the called body actually
uses the moded native ABI. It is false for a consuming Rust extern shim: the six
surviving Borrowed string rows discharge in the shim under Decision 24, then the
wrapper discharges the same references again. Ordinary applied calls do not
take this path; value position and auto-curry do.

The repair is one target-effect classification, not a population patch.
`emit_wrapper_call` already holds the resolved storage `FQSymbol`; after B1 it
reads the target's `Life` and, for `Concrete`, its `Realization` and declared
`ModeSummary` in the same keyed operation used for dispatch. The wrapper derives
one positional discharge plan before emitting the call:

| Target realization and declared parameter fact | Owner after the call | Wrapper post-call action |
|---|---|---|
| `Body`, heap `Mode::Borrowed` | wrapper; the backend-compiled body borrowed and emitted no param dec | canonical typed post-dec, as today |
| `Body`, `Mode::Owned` | body | none |
| any realization, `Mode::Copy` / non-heap parameter | no RC obligation | none |
| `ExternShim`, `ParamFlow::Consumed` | shim, under Decision 24 | none, regardless of analysis `Mode` |
| `ExternShim`, `ParamFlow::IntoResult` | result path | none; preserve the result and its existing materialisation rules |
| `ExternShim`, `ParamFlow::Retained` | target may retain the transferred reference | none — the conservative safe direction; C5's whole-inventory derivation proves no surviving heap extern relies on this fallback |
| `Dll` or `FacadeOf` | their Decision-24 target ABI | none; a non-trivial future convention needs a new explicit realization/flow case rather than inheriting the `Body` arm |

The match is exhaustive over `Realization` and `ParamFlow`, with no wildcard.
`ParamFlow` is read through `ModeSummary::param_flow`, never by indexing its
vector. The first row deliberately still consults `Mode`: it is the ABI fact
that makes a backend-emitted `Body` genuinely borrowed. The extern rows instead
consult their declaration flow because their analysis `Mode::Borrowed` means
"only-read" while their Rust shim ABI remains consuming. `Realization` selects
which of those two meanings is operative; origin, bare name and module name do
not.

For `Body + Borrowed`, the plan carries the parameter's concrete type from the
settled callable scheme and requests its canonical `drop<T>` `FuncId` from the
same `DropGlueRegistry` before emitting the post-call release into the
wrapper's separate Cranelift context. B9 does not preserve
`heap::emit_rc_dec_guarded` as a wrapper-only fourth release mechanism; it
conforms to B4's `emit_typed_rc_dec` outcome. A missing or non-concrete
parameter type is the existing located C4 refusal, never a shallow-dec
fallback.

`string-identity` is the `IntoResult` control. Its declaration remains
`ParamFlow::IntoResult` / `ResultMode::AliasOf(0)`, its shim still mints the
returned reference and performs no dec, and B9 emits no wrapper post-dec or
result-side compensation. No `Mode` or `ParamFlow` declaration changes in this
bundle. Result adaptation stays exactly as built after FIXME 0522: B9 changes
only parameter discharge ownership and adds no result inc.

### 4A.1 One wrapper seam, including auto-curry

The positional plan replaces the parameter loop inside
`emit_d24_adaptation`; both value-position wrappers and auto-curry consume that
same plan exactly once. A table-backed `ResolvedCall::BuiltinFn` in
`emit_curry_target_call` reaches the keyed lifecycle/realization dispatch
instead of selecting a user-callable extern through
`is_extern_primitive_in_wrapper`'s name roster. Opportunistic scalar inline
lowering remains unchanged, and `emit_extern_call_in_wrapper` remains available
for backend-internal runtime helper imports; neither is a second ownership
classifier. The auto-curry wrapper is still the Decision-24 adapter for its
chain — it does not call through a value wrapper and does not stack plans.

A closure wrapper always invokes the `ExternShim` realization's primary
Decision-24 entry. `borrowed_sibling`, when present, remains a static
Borrowed-call optimisation selected by the ordinary moded call path; selecting
it from an owned closure protocol would change which side owns the post-call
discharge and is a reject. The disposition and the selected entry are therefore
derived together from the same realization, rather than classifying after a
call target has already been chosen.

This folds the repair onto the lifecycle representation C4 already consumes:
there is no six-name test, no `DefKind::Primitive` proxy, and no second summary
lookup. A future `Realization` variant fails the exhaustive match at compile
time; a future extern row obtains its disposition from its own `ParamFlow`.

### 4A.2 The transient `vec-len` edge and exact order

At the start of C4, `vec-len` is the seventh live
`ExternShim × Mode::Borrowed × ParamFlow::Consumed` row, but its Rust body is
the one declaration/body inconsistency: it does not discharge. The generic B9
rule therefore removes the wrapper dec that accidentally balances it. That is
the safe-direction (one leaked reference, never a stale dec), but it is not an
accepted state and must not be hidden with a name exception.

Consequently **B9 is the last emission bundle in C4**, after B8's dormant
inline arm and B7's wash, and C5 P0 follows under the retained W3 reservation:
P0 re-kinds `vec-len` to `Inline`, deletes the extern shim, and activates B8's
own Decision-24 release. No integrated acceptance, warm-cache capture or wave
promotion occurs between B9 and P0. The two existing `vec-len` HOF cells may be
read before P0 only as the QA path/no-stale-dec control; they are not an
exact-balance acceptance of that intermediate tree. If the retained braid
cannot preserve this ordering, W3 remains blocked — backend does not add a
`vec-len` exception and C5 does not reopen `fn_as_value.rs`.

### 4A.3 Evidence and surface effects

Backend unit evidence lives in a new
`compiler/control_flow/fn_as_value/d24_adaptation_tests.rs` sibling:

- the pure exhaustive classifier pins every table row above, including
  `ExternShim + Borrowed + Consumed ⇒ no wrapper dec`,
  `Body + Borrowed ⇒ one wrapper-owned typed dec`, `IntoResult ⇒ no dec`, and
  `ExternShim + Retained ⇒ no unsafe guessed dec`;
- CLIF probes compare a synthetic consuming `ExternShim` and a synthetic
  genuinely-borrowing `Body` with the same heap signature, proving the former
  has no post-call dec and the latter has exactly one;
- direct value-position and auto-curry probes for the same target produce the
  same positional plan once, while the auto-curry control proves no stacked
  adapter; and
- a `string-identity`-shaped `IntoResult/AliasOf(0)` probe preserves the live
  result and emits no new inc or dec.

Acceptance is QA's closed matrix, not the mechanism: enumerate exactly
`str-len`, `str-eq`, `neq-string`, `starts-with?`, `ends-with?`, and
`contains?` in ordinary applied and `call1`/`call2` value positions; add the
representative binary auto-curry row; retain `string-identity` as the
`IntoResult` control and the pre-P0/post-P0 `vec-len` pair as the path control.
Each surviving value wrapper returns the correct value with exactly one shim
discharge under `CRANELISP_RC_STATS=1` and no stale dec under
`CRANELISP_RC_DEC_CHECK=1`. The ordinary applied rows prove the shim remains
the discharger; the synthetic `Body` unit proves a kind-blind deletion would
leak a backend user function.

B9 changes no Rust public item, lifecycle carrier, serialized field, slot,
extern symbol, function signature or platform layout. Backend public API,
`CACHE_SCHEMA_VERSION`, emitted-call ABI and `ABI_VERSION` all remain
unchanged. Its only emitted-code delta is removal of the redundant post-call
dec from the affected extern value/auto-curry wrapper bodies; those frames get
one scoped, attributed golden re-baseline. User-function wrapper frames and
`IntoResult` frames are byte-identical controls.

---

## 5. Bundle B3 — the category census, armed

The `Err ⇒ HeapCategory::Mixed` arm at `rc_emission.rs:493` is the single seam
at which a residual type acquires an RC licence, and it is the gate on its own
removal. S119 §5.1 specified the instrument; this section specifies its
**arming**, which S119 did not, and which the stream order makes load-bearing.

### 5.1 Shape

A permanent debug-profile census of every `Err` licence, keyed by the requesting
frame's `CallableOrigin` partition (`Ctor` / `Accessor` / `TraitMethod` /
`Plain`) and the type shape (bare `Type::Var`; `ADT(<concrete>, [Var…])`;
`Fn(…)` residual). The partition is C3's requirement, and it is what makes the
reading attributable instead of aggregate.

It is a **developer instrument, not a user diagnostic.** Its output names
compiler-internal frames and type shapes, which are exactly the nouns R-4
forbids in a public error (§8.4). It is therefore debug-profile only and never
reaches a release build's stderr; a release build carrying census output is a
reject.

### 5.2 The arming problem, and its resolution

S119 recorded "the instrument is already live and already reads non-zero, so its
positive leg is demonstrated" — that was true of the throwaway scaffold, and it
is *not* available to C4. C3 runs before C4, so by the time this instrument is
authored the corpus traffic C3 removed is already gone. An instrument first
armed against an absent fault is indistinguishable from one that cannot fire
(root `CLAUDE.md` §Assurance).

> **Both detection legs are planted, in the instrument's own change-set, and
> neither depends on corpus history.**
>
> - **Positive leg.** A unit fixture plants a frame whose entry `Scheme.ty`
>   carries a residual parameter (`insert_user_fn_stub_typed` — the crate's
>   documented way to put a spelled type on a probe entry). The census records
>   exactly one licence, in the expected partition, with the expected shape.
> - **Negative leg.** The same fixture with a concrete parameter type leaves
>   the census silent. This leg is as load-bearing as the first.
>
> The corpus reading zero is then the **acceptance criterion for the flip**
> (§5.3), not the instrument's proof of life. The two are separated on purpose.

### 5.3 The flip criterion

Across the full default suite and the 16-program `spec_*` corpus named in FIXME
0903: the licence count for the `Ctor`, `Accessor` and `TraitMethod` partitions
is **0**, the release-admission count for the same partitions is **0**, and the
corpus failure count is **8** — the S119 baseline. Any number above 8 is a
finding, because 24 was the measured cost of the rejected frame-keyed refusal
and this visit must not reproduce it.

The census reading zero is the criterion. A code reading is not
(`non-concrete-release-contract.md` §8 reject 4).

---

## 6. Bundle B5 — IO: runtime-directed teardown, the stamp that dissolves the residual, and the tag-licensed platform return

Face 4, 0934 and R19's backend arm are one bundle because they are one node
family, one teardown lane, and one ABI change. Splitting face 4 from 0934 would
ship a named leak and then patch it in the same sprint; splitting the
platform-return arm out would leave the seam kind-selected across a wave
boundary while the node it writes into has already changed size. §6.8 states the
internal order.

### 6.1 The `Pure` node

`Pure` becomes the two-field allocation
`[header | tag@16 | payload@24 | payload_glue@32]`
(arch, `total-concreteness.md` §3.4; `interfaces.md` §"IO Tag Constants").
Every other IO node is byte-identical. The payload stays at field 0, so every
existing *read* — the trampoline's `FIELD_0_OFFSET`, `consume_io_tree`,
`io_observer` — is untouched, and pattern matching binds field 0 as today. The
run lane's field-0 address is unchanged, but its access protocol is not
byte-identical: it first performs C5's atomic claim at field 1 (§6.2). The
hidden word is never a language-visible field (IO mints no accessors); it is the
closure-`DROP_GLUE_PTR` precedent (Decision 0011), not a header type-word, so
R15 stands.

### 6.2 What the word means — the design's load-bearing choice

The word is one three-state ownership/force witness after publication:

| Bits | State | Meaning |
|---|---|---|
| `0` | `Scalar` | the payload is non-heap and owes no deep discharge |
| `1` | `Claimed` | force or teardown has already claimed this node's payload obligation |
| any other value | `Owned(glue)` | the node owns one heap-payload obligation, discharged through that canonical glue address |

`1` is reserved. Backend construction emits only `0` or a canonical `drop<T>`
address; platform construction emits `0`, and backend adoption replaces it with
`0` or that same canonical address. No producer emits `1`, and supported
targets do not map executable code at address `1`.

**Producer/publication split.** C4 owns only initialisation: each construction
or platform-adoption site writes `0`/glue with the existing ordinary aligned
store while the fresh node is exclusively owned and unpublished. Publication
ends backend's authority over field 1. After publication, C5 is the sole owner
of every field-1 access and treats the aligned word as `AtomicI64`; neither
backend nor platform reads, clears or maintains it.

**The atomic claim is required by Decision 24 and by aliasable IO values.** The
run lane executes `swap(Claimed, AcqRel)` before reading field 0. A claimant that
observes `Scalar` or `Owned(glue)` wins and may read and transfer the payload; a
claimant that observes `Claimed` is a duplicate force, records
`Pure node forced more than once` through the existing runtime-error/ferry
path, and must not read, return, inc, dec or otherwise touch field 0. Scalar
payloads obey the same once-only rule: representation category does not weaken
effect-node semantics.

`free_io_node` performs the same exchange at the sole field-discharge seam. An
observed `Owned(glue)` calls glue with field 0 and then deallocates; `Scalar` or
`Claimed` calls nothing. Thus force and teardown contend for one obligation in
one atomic modification order, and exactly one claimant can observe the
initial state. There is no duplicate-transfer data race and no second ownership
flag.

This is live in today's Decision-24 sequencing even with one force lane:
`cranelisp_run_io` forces the caller's tree non-consumingly and then hands that
same tree to `consume_io_tree` (`crates/cranelisp-intrinsics/src/io.rs:84-94`).
The one teardown walk covers extracted `Pure`s and unforced `Pure`s in the same
tree; only the per-node claim says which obligation remains. Ordinary
backend-emitted pattern reads of field 0 are non-transferring and never access
field 1.

**Publication and lifetime ordering.** The atomic exchange linearises competing
claimants; its Acquire observes the payload and initial stamp published with
the node, and its Release publishes the claim before later RC release or joined
teardown. The existing three edges remain the node-lifetime boundary (arch's
`total-concreteness.md` §3.4 is canonical):

1. **Same-strand program order** — the claim precedes the extractor's shallow
   dec of a trampoline-fresh node, and precedes the terminal `consume_io_tree`
   of a caller's non-fresh tree claimed on the strand that later tears it down.
2. **The Release-dec/Acquire-fence pair** — where the claiming strand
   subsequently decs the node, the claim is sequenced before its Release dec and
   the teardown walk runs only behind the zero-observing dec's Acquire fence
   (`free_io_node`'s stated precondition), the argument that already licenses
   any drop-glue field read.
3. **The structured fork-join edge** — a `Par` worker that claims a non-fresh
   `Pure` inside its branch never decs that node (the branch is caller-owned;
   the root strand performs every non-fresh dec in its own later teardown walk),
   so edge 2 does not reach it. The publishing edge is the join the branch
   *result* already rides — the worker→reactor `oneshot` bridge on the async
   path, the rayon `collect` join on the synchronous dispatcher — which is
   already what publishes that worker's fresh-node frees and RC decs to the
   root.

Edge 2 alone does not cover the `Par` branch, whose strand never decs the node.
The atomic claim closes R1's double-force race; the rule still requires the
path's publication/lifetime edge to remain intact. One pre-existing residual
remains (arch, `total-concreteness.md` §3.4):

- **Severed join.** A cancelled `Select` loser with an in-flight rayon bridge
  detaches its worker, so edge 3's join never happens and the detached branch
  walk can race the root's `consume_io_tree` — a use-after-free window present
  at HEAD independent of the witness (the branch's field reads race today; the
  claim rides the same broken edge). Falsifier: a `select` whose losing branch
  holds an in-flight blocking `Par` bridge at cancellation.

R1 is no longer an open residual: C5 I0b owns the atomic helper, duplicate-force
error/ferry, winner cleanup, observer and evidence. R2 remains QA intake and
must restore the join rather than weaken this state machine.

### 6.3 The stamp — produce side, a closed set of four

Backend stamps the witness at a **closed set of four sites**: three where it
*constructs* the node, and one where it *adopts* a node the DLL constructed.
Three plus one, not four alike — the adoption site differs in kind and is §6.7;
this subsection is the construction three, and the two rules below govern all
four.

All four are producer initialisation before publication. They use ordinary
aligned stores and may write only `Scalar(0)` or `Owned(canonical glue)`. They
never write `Claimed(1)`, perform an atomic RMW or read a prior field-1 state.
The R1 amendment therefore changes no C4 instruction here; it changes the
contract C5 implements after publication.

Every `Pure` **construction** site is concrete post-mono (I-FRAME) and every one
is compiled code; the runtime only reads `Pure` nodes. They funnel through one
tag-and-fields emitter:

1. the inline concrete `ConstrADT` lowering (`compile_constr_adt` →
   `emit_adt_construct`);
2. the resolved-constructor `Apply` path (`emit_adt_construct_stackable`);
3. the value-position constructor wrapper body
   (`fn_as_value::emit_adt_construct_into`) — which under FIXME 0931 becomes
   the minted concrete ctor instance.

The fourth is the **platform-return adoption stamp** (§6.7): a post-call store
into a node `CLIO::pure` allocated with the sentinel `0`, at the one ABI
crossing. It is a store rather than a field value because the node already
exists, and it is licensed by the returned node's *tag* rather than by a
constructor identity — which is why it gets its own subsection rather than a
fourth row here.

> **The emitter is not changed and is not given a type.** It already takes a
> field-value list. The stamp is expressed as **one additional field value**,
> computed by the lowering site, which already holds the constructed value's
> concrete type. `HeapAdt::payload_size(2)` then follows with no layout code
> anywhere.

Two rules make that safe rather than convenient. **Both bind all four sites**,
which is what keeps the count a bookkeeping fact rather than a growth in
mechanism:

- **One derivation, three readers — never three `matches!` on a constructor
  name.** The question "does this constructor carry a hidden self-description
  field, and what is its value?" has one home, beside the keyed `ctor_meta_at`
  read that already answers every other per-constructor question. Today it
  answers non-`None` for exactly `primitives/IO.Pure`; every other constructor
  answers `None` and emits byte-identically. Spelling the test at three sites is
  the `matches!(callee_name, "vec-set" | "vec-push")` family that has cost this
  crate two sprints (0752), and it is a reject here. The adoption site has no
  constructor to key on at all — it keys on the returned tag (§6.7), which is
  the same rule one level out: the discriminator is read from the value, never
  re-spelled per site.
- **The value is obtained from the registry, not composed.** The lowering site
  asks `DropGlueRegistry::request_if_owning` for the payload's concrete type —
  the same call every release site makes — and materialises `func_addr` of the
  returned `FuncId`, or `iconst 0` when the request declines (non-owning
  payload). No new identity, no new naming scheme, no second home. The adoption
  site makes the identical call against the `T` of the callee's
  `(Fn […] (IO T))` scheme.

**Stack placement.** A `NoEscape` scalar-payload ADT may be stack-placed with an
immortal-RC header. A stack-placed `Pure` therefore carries a scalar payload,
so its word is `0` and the teardown lane discharges nothing — and an immortal
header means it is never freed. The invariant to pin is the conjunction:
**a stack-placed `Pure` always carries the sentinel `0`.** Falsifier: a
stack-placement verdict that admits a heap-typed payload; if that is ever true,
stack placement for `Pure` must be refused rather than stamped.

### 6.4 The discharge — consume side, teardown lane only

`drop<IO T>` becomes a fixed body, the same for every `T`:

```
drop<IO T>(p):
    if p < NULLARY_TAG_THRESHOLD: return
    old = atomic_rmw sub [p+RC_OFFSET], 1
    if old != 1: return
    fence
    call runtime/free_io_node(p)
```

No tag test, no `drop<T>` call, no per-`T` specialisation. This is strictly
simpler than `non-concrete-release-contract.md` §5.3's two-part body, and the
reason is exactly arch's: **backend contributes its type knowledge at
construction, where it is certain for every node, instead of at teardown, where
it is certain only for the root.** The nested-`Pure`-in-an-unrun-`Bind` residual
is not mitigated; it does not arise.

Three properties `/review` checks:

- `drop_glue::ctor_shapes` is **not reached** for `primitives/IO` — the registry
  classifies `ADT(primitives/IO, [_])` as runtime-owned before shape derivation.
  The identity check at `drop_glue.rs:497-505` is therefore unchanged, and stays
  a correct check on a precondition IO structurally cannot meet;
- **no IO-specific payload releaser symbol is minted** — every discharge goes
  through a `drop<T>` the ordinary registry already owns;
- the per-concrete-type glue *name* is retained even though the bodies coincide
  across `T`. `drop_glue_symbol_name` stays the sole identity authority; minting
  one shared `IO`-family name would be a second identity scheme for no gain.

### 6.5 The runtime entry point, and the ordering collision

Backend emits `call runtime/free_io_node(p)` — an ordinary intrinsic import,
declared by name like every other. The body is `cranelisp-intrinsics`': the tail
half of `consume_io_tree`, split at the dec (tag-walk + branch release +
dealloc; no dec, no fence; precondition: the caller has dec'd to zero and
fenced). Its `Pure` arm reads the witness at **field 1 (offset 32)** and, when
its atomic exchange observes `Owned(glue)`, calls through that glue with the
**field-0 payload value** as the argument, then deallocates. Observed `Scalar`
or `Claimed` calls nothing. Field 0 is the payload, not the glue: a discharge
that called through it would execute the payload as code. The split is already
approved and classified (FIXME 0928 item 4); R1 allocates the exchange and
duplicate-force half to C5 I0b.

> **Collision, stated plainly for `sprint`.** The stream order is C4 → C5, but
> C4's IO bundle cannot *execute* without C5's `free_io_node` and C5's
> atomic claim. Both halves are load-bearing, not one plus a defensive extra:
> without the claim, Decision-24 sequencing lets force transfer the payload and
> teardown discharge the same obligation, and aliases can force it twice
> (§6.2). Preferred resolution: land the intrinsics split as an early
> C5 sub-step ahead of C4's visit — which is where arch already placed it
> (I0a before C4, with I0b's claim + discharge after C7 P0). C4 may run its
> **emission tier** in isolation (the CLIF shape of `drop<IO T>`, the four
> unpublished stamps, the stack sentinel), but no integrated IO execution is
> accepted until I0b lands claim + discharge together. If the reservation
> cannot retain that braid, W3 is blocked; C4 must not compensate by growing a
> backend-side teardown walk or a temporary clear interpretation.

### 6.6 The `Bind` seed rider

Whatever C6 does to `Bind`'s manual bootstrap seed in this window must leave it
introspectable (`/info Bind`, `/info IO`). One cause, two symptoms: `Bind` is
seeded outside `register_synth_adt`, which is why the refusal named a
constructor the REPL then denied existed. R-4 requires a refusal's nouns to be
lookup-able. Not backend's edit; named here because it is this bundle's rider
and it must not be lost when 0907's refusal disappears.

### 6.7 The platform-return seam — the fourth stamp site

`arch` ruled this seam into B5 on 2026-09-01
(`total-concreteness.md` §3.4, "the platform-return seam"), discharging C7's H2
and rejecting C7 §4.6's platform-local footprint absorber. The ruling leaves no
interior design freedom, so C4 **consumes** it: this subsection states what B5
emits, what the arm's evidence is, and where the offset authority lives. It
re-opens nothing and adds no second predicate.

#### 6.7.1 What is wrong today, and why it is the same class

The existing fn-name stamp is selected by the **call target's kind**, not by the
returned node's tag. `compile_direct_call` stamps whenever the fetched entry is
`DefKind::PlatformEffect` (`crates/cranelisp-backend/src/compiler/apply.rs:1546-1549`)
and `stamp_platform_fn_name` performs an unconditional 8-byte store at
`EFFECT_FN_NAME_ABS_OFFSET` = `HeapHeader::SIZE + IO_EFFECT_FN_NAME_OFFSET` = 40
(`apply.rs:39-40`, `:1636-1641`). `CLIO::pure` allocates a two-word payload at v9
and a three-word payload at v10 (`crates/cranelisp-platform/src/lib.rs:908-920`),
so for a `Pure` return that store is **out of bounds at both ABI versions**.

It is latent — every in-tree platform fn returns `CLIO::effect*`, and the load
gate forces an `IO _` return, so the tag read is always in-bounds — but
`CLIO::pure` and its `From` lifts are published author surface. This is §3.3's
family one level out: **a narrowing carried in a comment rather than in a check**
(P25). The stamp's own comment states the premise ("the call returned an
`IO_TAG_EFFECT` node") and nothing tests it.

#### 6.7.2 The ruled lowering, and its one chokepoint

The dispatch is on the **returned node's tag**, at the S7 GOT-indirect call arm
of `compile_direct_call` — the one place a blocking platform call's result value
is in hand. The S6 poll arm returns earlier (`apply.rs:1497-1498`) and is
untouched.

```
node = <GOT-indirect platform call>
tag  = load.i64 [node + HeapAdt::TAG_OFFSET]                    # 16
tag == IO_TAG_EFFECT ⇒ store fn_name_ptr → [node + EFFECT_FN_NAME_ABS_OFFSET]  # 40
tag == IO_TAG_PURE   ⇒ store glue        → [node + PURE_GLUE_ABS_OFFSET]       # 32
otherwise            ⇒ no write
```

- **The Effect arm is value-identical to today** for every existing platform
  call. The only emission delta on live traffic is the guard itself, which is
  why B5's declared acceptance class covers it under one scoped attributed
  re-baseline rather than a behavioural change.
- **The Pure arm is the adoption stamp.** The DLL structurally cannot name a
  glue address — `HostCallbacks` is permanently two fields (S98) — so
  `CLIO::pure` writes the sentinel `0` and the crossing replaces it. Backend
  knows `T` concretely from the entry's `(Fn […] (IO T))` scheme (kept concrete
  by the manifest-sig `Type::Var` refusal, `total-concreteness.md` §3.5 /
  FIXME 0933, C6's) and makes the **same**
  `DropGlueRegistry::request_if_owning` call §6.3 rule 2 requires: `func_addr`
  of the returned `FuncId`, or `iconst 0` when the request declines. A residual
  `T` is a located refusal, never a default (R18, and §7.3's disposition) — so
  this arm carries **no ordering edge onto 0933**: today the `PlatformEffect`
  state is unoccupied (every shipped manifest sig is concrete), C6's refusal
  keeps it so, and the refusal here is what makes the arm correct if neither
  held.
- **The fall-through writes nothing.** An unexpected tag degrades exactly as a
  null fn-name already does (`"<unknown>"`); it never stores.

**Why this is still construction-time stamping.** The store lands before the
node can be forced or transferred — the call has just returned and the value is
unaliased — so the witness discipline of §6.2 is unchanged: stamped at
construction or adoption by an ordinary store while unpublished, then accessed
only by C5's atomic claim helper on the force and teardown lanes. Nothing here
adds a post-publication maintenance point (§13 reject 10).

**What it closes.** C7 §4.2's platform-edge under-claiming residual: the
sentinel is no longer a claim about ownership, it is an initial value the
crossing replaces. No DLL-minted `Pure` reaches the host by another route —
`CLIO<T>` does not implement `CLType`, so `pure(pure(…))` is unconstructable
(C7 §4.2, and that unconstructability is C7's to hold, not backend's to check).
Register row **R19** (`design/arch/safety-invariants.md` §4) moves from
`unasserted` to structural-with-a-standing-detector on this arm.

#### 6.7.3 Offset authority and the local compile-time pin

The architectural crossing datum is the absolute byte offset **32**. This crate
composes it from its own field vocabulary; `cranelisp-platform` composes it as
`HEAP_HEADER_SIZE + IO_PURE_GLUE_OFFSET`. Each vocabulary owns an independent
compile-time pin to 32, so either composition drifting fails constant evaluation
while compiling the crate that owns it.

> **One composition site in backend.** B5 introduces a single named constant
> beside the existing `EFFECT_FN_NAME_ABS_OFFSET`, composed from the types-owned
> field placement the construction emitter already uses —
> `PURE_GLUE_ABS_OFFSET: i64 = HeapAdt::field_offset(1) as i64`, field 1 — the
> same type and the same `as i32` at the store site as its `Effect` sibling, so
> both arms of §6.7.2 read identically. The crate rule at
> `heap.rs:149` (named constants, never a bare numeric literal) is the reason,
> and the three construction stamps need no offset at all: they pass a field
> *value* to the tag-and-fields emitter. So the glue word has **exactly one
> explicit-offset expression in this crate**, and the pin has one subject.
>
> **C4 owns the backend pin in B5**, beside that sole composition:
> `const _: () = assert!(PURE_GLUE_ABS_OFFSET == 32);`, following the
> `heap.rs:71-72` idiom. The literal is the architecture-owned crossing datum;
> it is not a second layout expression.
>
> This keeps the layout-confinement rule (crate `CLAUDE.md` §"Heap layout"): the
> constant is composed from `HeapAdt` **re-exported through `heap.rs`**, which is
> what `apply.rs` already does for its `HeapAdt::field_offset(0)` /
> `TAG_OFFSET` / `payload_size` uses. No new cross-crate layout import.

**Zero-revisit packaging.** C7 P0 independently lands
`const _: () = assert!(HEAP_HEADER_SIZE + IO_PURE_GLUE_OFFSET == 32);` beside
the platform constant. There is no later C7 edit to backend source, no backend
reservation for a joint assertion, and no root integration assertion. Those
forms duplicate a relationship the two owner-local pins already make
structural, while adding a second owner or a cross-stream carve-out without
detecting another failure. C4 owns the backend expression and pin; C7 owns the
platform expression and pin; neither imports the other's offset vocabulary for
this detector.

The C7 fixture pair exercises the crossing without redefining it: compiling
both crates exercises both owner-local pins, and the heap/scalar pair observes
the adoption and sentinel paths. A correctly pinned value used at the wrong
store remains the emission tier's job (§6.7.4), not a reason to duplicate the
constant relationship at a third site.

#### 6.7.4 Evidence, and its grade

Tier is C4's (emission); execution acceptance stays where C7 and `qa` placed it.

- **Direct.** A CLIF row over a seeded `DefKind::PlatformEffect` entry pins the
  tag load, both stores and the no-write fall-through, at **two
  instantiations**: `(IO String)` materialises the **same `drop<String>`
  `FuncId` the release path names** — the discriminator against a minted second
  identity — and `(IO Int)` stamps `0`.
- **Arming / negative.** The two stores are asserted **branch-dominated by the
  tag compare**, by a control-flow walk in the
  `ctor_template_admission_tests::assert_threshold_guarded_rmws` idiom, so
  reverting to today's unguarded store REDs the row. A non-platform callee
  emits no stamp block at all. Both legs are load-bearing: a guard that cannot
  fail to be present is indistinguishable from no guard
  (root `CLAUDE.md` §Assurance).
- **Execution.** C7 H3's F4 cell over the `Pure`-returning fixture pair
  (`platforms/test-capture::pure-string` / `pure-int`, C7 §4.5), with the
  no-double-discharge negative control. It gates on C5's walker and C7's
  rebuild; the fixture is C7-surface work and C4 authors none of it.

**Grade.** Structural for the licence (no store is emittable outside its tag arm
at the one chokepoint), measured for the arm's identity and dominance (the two
unit rows), and the discharge half stays measured at C7's acceptance leg.

#### 6.7.5 The window residual, and its falsifier

The Pure arm's store is in-bounds only against the two-field node, so between
C4's B5 and C7's P0 the emission exists against a v9 layout. **In that window it
has zero traffic** — no in-tree platform fn returns `Pure` (verified at source
2026-09-01), C7 adds none before P0 (C7 §3.4, §15 reject 14), and the `From`
lifts are DLL-author surface with no in-tree caller.

> **Falsifier:** a `Pure`-returning platform fn landing before C7's P0. That is
> the one observation that turns this from a dormant emission into an
> out-of-bounds heap write. `sprint` sequences the exclusion alongside the
> standing C4 → C5 → C7 ordering constraints; it is not a condition backend can
> assert away, and a backend-side ABI check would be the second gate C7 §3.5
> rules out. Register row R19 carries the same falsifier.

### 6.8 B5, in order

B5 is one reviewable change-set (§10). These are its ordered rows inside it, and
the order is forced by what each row's predecessor makes true rather than chosen:

| # | Work | Why here |
|---:|---|---|
| 1 | The three construction stamps (§6.3) and `payload_size(2)` | the node must be two-field at every site backend constructs before anything reads or adopts field 1 |
| 2 | The stack-placement conjunction (§6.3): a stack-placed `Pure` always carries `0` | same change-set as 1 — it is a property of the construction path, not a follow-up |
| 3 | `drop<IO T>` reduced to guard + dec + fence + `call runtime/free_io_node` (§6.4) | after 1, because the runtime walker it hands to reads the word 1 writes |
| 4 | `PURE_GLUE_ABS_OFFSET` + C4's `== 32` compile-time pin (§6.7.3) | the offset authority must exist before the only site that spells an offset |
| 5 | The tag dispatch: the guard, the Effect arm re-sited under it, the Pure adoption arm, the no-write fall-through (§6.7.2) | after 4; it is the only row that touches `apply.rs`'s stamp seam, and it lands as one edit so the Effect arm is never guarded twice |

Rows 1–3 are the 0934 construction half; rows 4–5 are the platform-return half.
They are one bundle because they are one node family and one ABI change:
splitting 5 out would leave the seam kind-selected across a wave boundary while
the node it writes into has already changed size.

**Two ordering constraints leave this bundle**, both `sprint`'s (§15):
C5's `free_io_node` and atomic claim for row 3's *execution* (§6.5), and
C7's P0 for row 5's Pure arm to be in-bounds (§6.7.5).

---

## 7. Bundle B4 — the R-1 structural close

Gated on §5.3 reading zero. Four edits, one rule.

### 7.1 The ctor declaration channel — the ruling S119 could not have made

`CtorMeta`/`CtorField` is materialised from the *constructor declaration's*
scheme, so a polymorphic product's field type is `Type::Var(a)` permanently and
`signature_heap_category`'s `Err` arm licences a guarded RC path off it at every
use site. **No amount of frame monomorphisation closes this**; it is a carrier
shape, and R17's arm-flip criterion is unreachable while it stands. `/arch`
routed the carrier question here (FIXME 0929 ask 4: the derivation seam is
types', the carrier shape is backend-interior).

> **Ruling. A constructor's field types are an instantiation fact, not a
> declaration fact.** `CtorField` carries a `ConcreteType`, so a residual field
> type is **unrepresentable in the carrier**. Materialisation is
> instantiation-keyed: backend's constructor read is already per-reference and
> the reference already carries the constructed value's concrete arguments, so
> the read substitutes them into the declaration scheme and refuses if the
> result is not concrete.

The derivation is **already published and has zero consumers**:
`cranelisp_types::ctor_field_types_at(table, ctor_key, args) ->
Result<Vec<ConcreteType>, CtorFieldsAtError>` does exactly this — positional
unification of the result-ADT parameters against the instantiation, then a
typed `NotConcrete` refusal. This ruling gives it its first consumer, which is
the point: a published, statically-reviewed, never-executed projection is not
landed (root `CLAUDE.md` §Assurance).

- **Zero `cranelisp-types` delta.** No new types API, no baseline movement, no
  ask on C1's window. Verified in this window.
- `CtorFieldsAtError::NotConcrete` becomes a **located refusal at the
  reference's span** (§8.4), not a fabricated `Type::Int`. `NotACtor` and
  `ParamArity` stay what they are: keying bugs, distinct from refusals.
- This deletes `context.rs`'s `unwrap_or(Type::Int)` twice over — the
  arity-mismatch fabrication and the residual channel are the same expression.
- **Emergent convergence, in scope because it is the third duplicate.**
  `drop_glue::ctor_shapes` builds its own substitution. With IO routed to the
  runtime (§6) its remaining traffic is ordinary user types, and it materialises
  per-constructor field types through the same types projection. Its cross-ctor
  result-parameter agreement check survives as an **explicit stated
  precondition** with its existing diagnostic — the check is not deleted, it
  stops being a side effect of how the substitution happened to be built.
  Falsifier: a user type whose constructors' result parameters disagree must
  still refuse with the same message.

### 7.2 The two fabrications that were the class

- `signature_heap_category`'s `Err(_) => HeapCategory::Mixed`
  (`rc_emission.rs:493`) becomes a **located error**. This restores D2's
  no-fallback rule to the retain side as well as the release side, and it is
  what closes 0903's families and 0916's mechanism.
- `emit_heap_binding_decs`'s type-keyed shallow-dec arm
  (`fn_compiler.rs:1287`) **deletes**. It is not re-keyed to the frame: that
  narrowing was measured at +16 hard refusals, twice, one sprint apart, and
  re-landing it is a standing reject. It deletes because after C1/C3 the arm has
  no traffic — the ctor-template frames it served are no longer codegen targets
  and the accessor/trait-instance frames are monomorphised. `emit_typed_rc_dec`
  is then the sole release path at every seam, with no fallback anywhere.

With both gone, invariant **I-CT retires** together with its standing
`Borrowed`-mode obligation, and **I-CT′ is discharged structurally rather than
by the deletion S119 designed**: there is no ctor-template frame left to emit an
RC operation in. `transitive-drop-glue.md` §4.1 records the subsumption.

### 7.3 The remaining `unwrap_or` arms — exact dispositions

| Site | Today | Disposition |
|---|---|---|
| `drop_glue.rs:398` — `args.first().cloned().unwrap_or(ConcreteType::Int)` in the Vec arm of `shape()` | a Vec glue request with no element argument mints Int-element glue, freeing heap elements as scalars | **located refusal**, the `:497-505` pattern. Believing the arm dead is "graded by inspection", the named failure state |
| `vec_codegen::resolve_elem_inc_fn_ptr` — the `None` element-type arm, "assume `NeverHeap` (safe default)" | **found this window; in no prior census.** An unknown element type is asserted non-owning — R-2's exact shape ("refusing to own a type in order to pass the gate fabricates the false fact *this type owns nothing*"), in the leak direction | **located refusal.** Its sibling `resolve_elem_dec_fn_ptr` takes the same disposition; a Vec whose element type is unknown at an RC seam is a producer defect, not a default |
| `fn_compiler.rs:1214` — `variable_types.get(name).cloned().unwrap_or(Type::Int)` | a defensive dead arm: the preceding filter already guarantees `Some` | **delete the arm.** The collection becomes one lookup that cannot fail, spelled as what is true. Low severity, but it is a live `unwrap_or` in the census family and leaving it costs the census its exactness |

Rows 1 and 3 are FIXME 0929's C4-owned rows 2 and 4; row 2 is new and should be
recorded on that filing by its owner.

### 7.4 Grade

After this bundle the class's grade improves from **measured** to
**structural, with a measured detector**:

- structural: `Life::Concrete` requires a witness-checked concrete scheme, so
  the parameter channel cannot deliver a residual; `CtorField { ty:
  ConcreteType }` makes the declaration channel unrepresentable; the release
  fallback arm does not exist to be reached;
- measured: the census remains, permanently, as the detector that the
  structural claim holds — and, per §5.2, as an instrument proven to fire.

Named falsifier for what remains asserted: **a provenance-licensed RC emission
not preceded by a category gate on the value's own type**
(`non-concrete-release-contract.md` §6.2.2). Converging the seam-by-seam gates
into one is a larger reshape than this visit and is not attempted; the §12
negative cell is where the falsifier is observed.

---

## 8. Bundle B6 — the convergences

§8.1–§8.3 are B6. §8.4 and §8.5 sit here because they are seam-level items of
the same size, but they carry bundles **B2** and **B8**; §10 is the authority on
bundle membership.

### 8.1 One result-root rule (0898, backend twin)

`compile_to_module`'s inline `result_roots` map re-implements the IO-head-strip
rule that `ConcreteType::result_root()` already owns (landed at S119 with its
unit battery). The map re-expresses over the method and the literal encoding
deletes. Byte-identical semantics — one hop, `primitives/IO` with non-empty
args. The int twin (`src/result_owner.rs::strip_io_head`) is C6's; the filing
deletes when both are collapsed.

### 8.2 One nullary-skip prologue (0906, re-scoped)

0906 named one hand-rolled copy of the skip prologue, in the Vec element
inc-adapter body. **Re-measured this window: there are two**, both in
`vec_codegen.rs` — the adapter body, and `emit_guarded_rc_inc`, which has four
call sites of its own. `heap::emit_nullary_skip_guard`'s two consumers are the
guarded RC halves; the crate `CLAUDE.md` row claiming those are the only ones is
correspondingly incomplete.

Both fold onto `heap::emit_nullary_skip_guard` (a free function over `builder`,
`ptr`, `cont_block`, so the separate-Cranelift-context constraint is not a
barrier; it becomes `pub(crate)`). The reason is R-1's whole content: the
tag-vs-pointer decision has one home *because* this class's memory-unsafety is
that decision being mistaken for a scalar-vs-pointer test, and a hand-rolled
copy is a place that mistake can be re-made silently.

**Not byte-identical** — both copies create the RC block before the continuation
block, and the shared helper requires the continuation first; block creation
order is CLIF block numbering, so the two labels swap. Lands with a **scoped,
attributed golden re-baseline for the covered bodies only** (extension ≠
re-baseline). The absolute-polarity pin reuses
`ctor_template_admission_tests::assert_threshold_guarded_rmws`, which walks
arbitrary CLIF text, so no new machinery.

**The `guarded` flag must come from the category, not from a boolean the caller
carried.** It already does at `resolve_elem_inc_fn_ptr` (via
`signature_heap_category`) — the fold must not re-introduce a local
`guarded: bool` that a future caller can set independently of the element type's
category. This is the same gate order as §3.1, one level down.

### 8.3 One binding-root finder (0747 — W-B5, ruled)

**The contradiction, restated.** W-B5 asks for two things: collapse the
three fn-return patches onto one contract, and accept only a byte-identical-off
refactor. The patches disagree by construction —
`return_var_in_scope` matches an immediate `Var` in the *current scope frame*,
while `operand_live_binding_root` traces through `let` bodies and forwarding
`match` scrutinees against *any* live binding — so collapsing them onto the
second changes emission, and 0747 offered a choice between narrowing the
mechanism and re-writing the acceptance.

**Both offered options are declined, because the fork is manufactured.** Read at
source, the three finders differ on **two independent axes**, not one:

| Finder | Reach | Liveness |
|---|---|---|
| `return_var_in_scope` | the node **is** a `Var` | in the current scope frame |
| `return_cow_source_in_scope` | the node is a tail COW site whose source is a `Var` | in the current scope frame |
| `operand_live_binding_root` | `Var`, or forwarded through `Let` body / forwarding `Match` scrutinee | any live binding |

A single traversal can answer both: liveness is already a caller-supplied
predicate at the third finder, and reach is a property the traversal *observes*
rather than a policy it needs told.

> **Ruling.** One binding-root finder over `MonoExpr`, with **one node-kind
> list**, returning the root binding together with the **reach class** by which
> it was found — the node itself; through binding indirection (`Let`/`Match`
> forwarding); or as the source of a tail COW site. The three consumers are
> three **thresholds** on that one answer, exactly as `is_fresh_construction`
> and `yields_owned_temporary` are two thresholds on `value_provenance`. The
> liveness predicate stays the caller's.
>
> Thresholds: the fn-return skip is the direct class; the COW-return source is
> the COW class; the provenance trace admits direct **or** binding-indirection.

This satisfies both of W-B5's clauses instead of trading them:

- **the mechanism collapses** — one traversal, one node-kind list, one place the
  `Let`/`Match` forwarding rule lives, which is the "three ad-hoc patches for one
  flow" complaint 0668 raised;
- **the acceptance holds unchanged** — byte-identical-off *by construction*,
  because each consumer's threshold reproduces its current predicate exactly.
  No golden re-baseline, no RC-neutrality argument, no per-frame drift review.

**The widening is separated, not smuggled.** Letting the fn-return seam accept
the binding-indirection class is a real improvement (it removes a redundant
inc/dec pair and its teardown branch on `(defn f [v] (let [x 1] v))`) and it is
**not** part of this ruling. It is a potential extension with a stated trigger
and a stated hazard: the return path asserts that the skipped variable is not a
`Borrowed` parameter, and the wider class can reach one through a `let`. Trigger:
a measured frame where the redundant pair is worth a scoped re-baseline, taken
with that assertion re-proved first. Recorded so the next reader does not
re-derive the fork.

FIXME 0696's re-keying, which rode W-B5, was independently resolved at S115 W3;
nothing of it is owed here.

### 8.4 The refusal's frame (0915)

R-4 makes this part of the release contract, not a cosmetic rider: "a located
refusal the user can act on" is one of the dispositions the contract assigns,
and this visit converts **more** sites to located refusals (§7.1, §7.2, §7.3), so
the frame must be right **before** those flips, not after.

Three backend-side obligations:

- **One category prefix per diagnostic.** `CompilationError::CodegenFailed`
  carries a structured `ErrorLocation` but its cause is a pre-rendered string
  that already embeds the inner located prefix, so `codegen error at 0..0:`
  renders twice. The fix is structure at the wrapping construction — never
  downstream re-parsing of a rendered message.
- **A real span.** `drop_glue.rs`'s error helper hard-codes
  `ErrorLocation::from_span(Span::SYNTHETIC)`, which is the direct cause of
  every `0..0` in this class. Every error raised in the glue registry carries
  the **requesting frame's or reference's** span; the spans are on the
  `MonoExpr` nodes, so this is a raise-site obligation, not a plumbing problem.
- **A subject the user can look up.** `"codegen failed for {module}/{symbol}"`
  is composed over a `Symbol` that already carries its module path for a
  monomorphised instance, producing `user/user/then$primitives/IO$Int+…`. The
  composition must not double an already-qualified symbol.

**The audience is the program author, and that is what fixes the noun set.** A
compiler diagnostic's permitted nouns are source-level: the user's symbol as
written, the form's span, the type as the user would spell it. Compiler-internal
identities — `$` mangles, `__expr`, doubled module composition, a degenerate
`0..0` — are not redaction candidates; they are simply the wrong nouns for this
reader, and they are also the census's nouns (§5.1), which is why the census is
debug-profile and separate. There is no protected data class here and nothing is
suppressed for confidentiality: safe diagnostic value is kept in full.

The **subject presentation** half (`__expr` → the entered form; `f$T1+T2` → its
base `f`; an already-qualified symbol → itself) is int's, already ruled at
`design/int/int.md` §9.1 as one projection applied once at `Sess::format_error`.
Backend supplies correct data; int renders it. `repl/spec.md` §5.5 is the
normative surface and is `spec`'s.

Once this lands, a refusal at span `0..0` against a mangled subject is a
`/review` reject (`non-concrete-release-contract.md` §8 item 7).

### 8.5 The dormant `vec-len` value-position arm (bundle B8)

`arch` ruled the `vec-len` de-slot's one backend edit into this visit
(`total-concreteness.md` §3.2, answering the C5 primitives design's §3.8 gate):
**the arm is C4's, landed dormant, before C5 flips the declaration.** Neither of
C5 §3.8's two offered routes is taken, no dispensation is issued, and the same
source area is visited once. C4 consumes that ruling and the arm's shape; it
re-opens neither, and it designs no part of the primitives de-slot.

**The edit, entire.** `emit_vec_query_into` (`vec_codegen.rs:1113`) is a
`(name, arity)` match carrying `("vec-get", 2)`, `("vec-set", 3)` and
`("vec-push", 2)` over a located-`CodegenError` fall-through. It gains a fourth
arm, `("vec-len", 1)`: read the Vec's length word from `params[0]`, then perform
**the release the `("vec-get", 2)` arm already performs** — the same
`vec_drop_func_id` with the per-site element dec pointer from
`resolve_elem_dec_fn_ptr_into`, through `emit_vec_rc_dec_with_drop` — and return
the length. `dev` owns the spelling. It introduces no mechanism, no release
identity, no name list and no second dispatch: it completes a match whose
fall-through is already a refusal. Why the wrapper body owes that release at all
is C5's and is ruled at its §3.4 — the inline arm returns before
`emit_d24_adaptation`, so an inline primitive's wrapper owns its own Decision-24
discipline — and is consumed here rather than restated.

**Dormancy is structural, and B8 does not construct it.** Both call sites —
`fn_as_value.rs:595` (value position) and `:729` (auto-curry) — are gated on
`is_inline_primitive_at` (`context.rs:244`), which reads the *entry's kind*.
While `vec-len` is `user_extern` the gate is false, the arm is unreachable, and
value-position `vec-len` keeps the working GOT/extern path byte-for-byte. So
**B8 edits neither `fn_as_value.rs` nor `is_inline_primitive_at`** — the
discrimination is already carrier-keyed and needs no name test, and adding one
would be the `matches!(callee_name, …)` family this crate has paid for twice
(§6.3, 0752). B9 later edits `fn_as_value.rs` for its realization/flow
discharge plan (§4A), but leaves this kind gate and the dormant inline route
unchanged.

**It inherits B4's refusal and must not grow a second default.** `elem_type` is
an `Option`, and its `None` case degrades today to the no-element-RC shape —
the "safe default" §7.3 row 2 rules into a located refusal. B8 therefore lands
after B4, so the new arm is written once, against the settled disposition: a
value-position `vec-len` whose element type is unknown at the seam refuses,
exactly as its three siblings then do. A local degrade for this arm alone is
R-2's shape in the leak direction and a reject (§13 item 12).

**Evidence, and its grade.**

- **Direct — the arm's own execution.** A `compiler/vec_codegen` unit row
  exercises the `("vec-len", 1)` emission *directly*, in the same change-set.
  This is not optional coverage: an arm no caller can reach is landed with zero
  consumers, which is not landed (root `CLAUDE.md` §Assurance), and this row is
  the only thing that executes it before C5's flip.
- **Dormancy — graded structural, confirmed measured.** The structural leg is
  the kind-keyed gate above: C4 cannot select the arm because the kind it tests
  is `user_extern` until C5's P0. The measured confirmation that no *reachable*
  emission moved is the golden-CLIF corpus staying byte-identical and the two
  `vec-len` value-use cells in `tests/vec_query_value_use.rs`
  (`vec_len_as_value_two_instantiations_of_one_hof_control`,
  `vec_len_as_value_through_hof_returns_length_control`) staying green **through
  the GOT path**. Those cells are `qa`'s acceptance for C5's flip (C5 H4); C4
  reads them as its dormancy control, and their path — not merely their
  greenness — is the observation, since both paths return the same length.
  Falsifier: a golden-CLIF row moving under B8, or either cell taking the inline
  arm before the flip.

**Surface accounting: zero on every axis C4 owns.** The arm is `pub(crate)` code
inside an existing `pub(crate)` function, so there is no `cranelisp-backend`
public-API delta and no baseline regeneration. It is emitted code and not a
persisted shape, so it moves no `CACHE_SCHEMA_VERSION` (the 24→25 window is
C1's, §4.3) and no `ABI_VERSION` (9→10 is C7's, §6.1). The one `public-api.txt`
line the de-slot removes — `pub mod cranelisp_primitives::vec` — is C5's,
already approved by `arch` as a contraction and regenerated in P0's change-set.

**What activation costs C5: nothing.** P0 flips the declaration `user_extern` →
`user_inline`; the same kind-keyed gate then routes value position to the arm
with no backend edit at all (§10, H9).

---

## 9. Per-record disposition

Verified against live source in this window. An open filing is not evidence that
implementation remains; five of the twelve allocated FIXMEs are already
discharged in source. The last row is an `arch` register row rather than a
filing, carried here because it allocates implementation to a C4 bundle.

| # | Target | Live state at HEAD | Disposition | Bundle |
|---|---|---|---|---|
| **0747** | `/design` | all three finders live and separate (`fn_compiler.rs:1751`, `:2148`, `:3294`) | **live implementation** — ruled §8.3; `s115-carrier-and-rc-sweep.md` §6 restated | B6 |
| **0761** | `/qa` | the exact-balance lane landed: `tests/gen_ownership_flows.rs` asserts absolute balance across the owning-type × position matrix, `balance_exclusion` retired | **filing retirement, evidence-only.** C4 contributes nothing; `qa` verifies and deletes | — |
| **0781** | `/qa` | backend half landed S115 W4c — `value_provenance` is the one derived answer; `emit_vec_drop_if_temporary` reads it | **evidence-only + QA handoff** (§10 H4). No backend implementation | — |
| **0782** | `/dev` | resolution (a) landed: the var-pattern binder is marked borrowed and the arm's lifetime plan is the sole release owner; unit pins present at `match_codegen/{arm_lifetime_plan,scrutinee_ownership}_tests.rs` | **filing retirement.** Re-confirm one release in the repro's CLIF once inside C4's evidence, then delete | B7 |
| **0811** | `/qa` | a process rule; no backend source claim | **evidence-only handoff** (§10 H5). C4 adopts it for its own attributions: 0917's exemplar cell is an observer, and a surprising reading there is new intake, not a re-opening | — |
| **0891** | `/dev`(backend), deferred | items 2 and 3 shipped; item 1 (the frame key) is retired by I-CT′, which §7.2 discharges structurally | **filing retirement**, subsumption recorded in `transitive-drop-glue.md` §4.1 and the contract §4 face 1 | B7 |
| **0900** | `/test` | test-corpus `// defect:` token grain | **handoff to `test`** (§10 H6); `qa` records. No backend work, and no test-policy decision taken here | — |
| **0903** | `/design`(backend) | `Err ⇒ Mixed` live at `rc_emission.rs:493`; type-keyed arm live at `fn_compiler.rs:1287`; census absent | **live implementation** — §5 then §7 | B3, B4 |
| **0906** | `/dev`(backend) | live, **and under-scoped**: two hand-rolled copies in `vec_codegen.rs`, not one | **live implementation, re-scoped** (§8.2) | B6 |
| **0907** | `/design`(backend) | `ctor_shapes` identity check live at `drop_glue.rs:497-505`; 7 e2e REDs | **live implementation** (§6); execution gated on C5 | B5 |
| **0915** | `/design`(backend) | doubling and `Span::SYNTHETIC` both live | **live implementation** (§8.4); **precondition** for §7's flips | B2 |
| **0916** | `/design`(backend) | producer-gated on C3's `TraitMethod` monomorphisation | **producer-gated.** No backend lowering change: `compile_match` already types its scrutinee from the mono view (`scrutinee.ty()`), so there is nothing to fabricate and nothing to compensate. Closes when the census's `TraitMethod` partition reads zero | B4 |
| **0917** | `/design`(backend) | **fixed at S120** (`cbb3be9e`): `NoReference` in the lattice, the fold seeded at the identity, the three-state `CtorValueShape` probe, both repro cells green | **filing retirement** — the first confirmed stale-status record, as `SPRINT.md` notes | B7 |
| **0898** (C6-primary) | `/dev` | types half landed (`ConcreteType::result_root`); backend twin live at `lib.rs:672-683` | **live implementation, backend twin only** (§8.1). C6 removes the int twin and deletes the filing | B6 |
| **0932** (C5-primary) | `/design`(backend + runtime pair) | `emit_vec_query_into` carries three arms and no `("vec-len", 1)`; both call sites are kind-gated (`fn_as_value.rs:595`, `:729`) | **live implementation, C4 dormant-arm half** (§8.5), allocated here by `total-concreteness.md` §3.2. C5's P0 flips the declaration and closes the primitives arm | B8 |
| **0934** (C5-primary) | `/design` | approved by the user; layout ruled by arch | **live implementation, C4 construction half** (§6.1–§6.3). C5 discharges, C7 bumps ABI 9→10 and rebuilds fixtures | B5 |
| **R19** (arch register row, not a FIXME) | `/dev`(backend) | the fn-name stamp is kind-selected and stores base+40 unconditionally (`apply.rs:1546-1549`, `:1636-1641`, `:39-40`); `CLIO::pure` allocates 32 bytes at v9 / 40 at v10 (`platform/src/lib.rs:908-920`) — out of bounds for a `Pure` return at both. Zero in-tree traffic | **live implementation, ruled** (§6.7). Arch's `total-concreteness.md` §3.4 allocated the tag dispatch here; C7's H2 is discharged and its §4.6 fallback rejected. C4 consumes and does not re-open. Window residual + falsifier at §6.7.5 | B5 |
| **0929** rows 2–4 (C3-primary) | `/design`(backend) | all live; row 3 is the census blocker | **live implementation** (§7.1, §7.3), plus one arm found this window | B4 |

---

## 10. Bundles, in order

Ordering is by dependency, not by size. Each bundle is a reviewable change-set.
The labels are identities carried from the S119 face numbering, not ranks: B8
was allocated last (§8.5) and lands before the wash.

| # | Bundle | Depends on | Closes | Emission acceptance class |
|---:|---|---|---|---|
| **B1** | Lifecycle consumption (§4): the exhaustive realization-to-lowering disposition, `defined_symbols` as a projection, cache-load validation arms | C1 landed | — (the wash) | byte-identical (a representation change with no emission consequence) |
| **B2** | The refusal frame (§8.4) | B1 | 0915 backend half | byte-identical (diagnostics only) |
| **B3** | The category census, armed (§5) | B1 | — (the instrument) | byte-identical, debug-profile only |
| **B4** | The R-1 structural close (§7): `CtorField { ty: ConcreteType }`, the two fabrications retire, the three `unwrap_or` arms | B2, B3 reading zero, C3 landed | 0903, 0891, 0916 backend arm, 0929 rows 2–4 | **census-gated**; zero new refusals; `f4_sudoku.clif::user::Grid.cells` scoped attributed re-baseline (0903's binding addendum, unchanged) |
| **B5** | IO teardown + the `Pure` stamp + the platform-return tag dispatch (§6; internal order §6.8) | B4; C5 I0a makes `free_io_node` importable for emission; **C5 I0b is required for execution**; **C7 P0 makes the Pure adoption store in-bounds** (§6.7.5) | 0907 (×7), 0934 C4 half, R19's backend arm | scoped attributed re-baseline for IO-releasing frames **and for the blocking platform-call sites** (the tag guard is the only emission delta on live traffic — §6.7.2); ABI 9→10 is C7's |
| **B6** | The convergences (§8.1–§8.3): result-root, nullary prologue, binding-root finder | B4 | 0898 backend twin, 0906, 0747 | 0898 and 0747 **byte-identical**; 0906 **scoped attributed re-baseline, covered bodies only** |
| **B8** | The dormant `vec-len` value-position arm (§8.5): the fourth `emit_vec_query_into` arm, unreachable until C5's declaration flip | B4 (so the arm is written once against the settled absent-element-type refusal) | 0932's C4 half | **byte-identical** — the arm is unselectable while `vec-len` is `user_extern`; its own unit row is the only thing that executes it, and **no re-baseline is declared** |
| **B7** | Retirement and current-state wash (§9) | all | 0782, 0891, 0917 deletions; design and crate current-state records | no emission |
| **B9** | R3 realization-directed wrapper discharge (§4A): one keyed `Life`/`Realization` read, exhaustive per-param plan, value and auto-curry consume it once | B1, B7, B8; **C5 P0 is the immediate next primitive step before integrated acceptance** | QA R3 — six surviving Borrowed string extern rows | scoped attributed re-baseline of affected extern wrapper bodies only; backend `Body` and `IntoResult` controls byte-identical |

**Handoffs out.**

| # | To | Content |
|---|---|---|
| H1 | `/design`(intrinsics) → C5 | `free_io_node`: the tail half of `consume_io_tree`, split at the dec. C5 I0b owns the one aligned-`AtomicI64` claim helper over field 1: force and teardown both `swap(Claimed, AcqRel)` before payload access; teardown calls an observed `Owned(glue)` with field 0, while `Scalar`/`Claimed` calls nothing; duplicate force refuses through the existing runtime-error/ferry path before touching field 0. Construction/adoption are C4's ordinary unpublished `0`/glue stores and do not change. The existing three publication/lifetime edges remain as §6.2 states; the atomic modification order closes the former duplicate-transfer race, while R2's severed join remains separately owned. Site, cleanup, observer and evidence are C5's; the contract is §6 |
| H2 | `/design`(platform) → C7 | `ABI_VERSION` 9→10 and platform test-fixture rebuilds for the two-field `Pure` (§6.1); the DLL-side sentinel `0` and the `Pure`-returning fixture pair the adoption stamp is measured on (C7 §4.1, §4.5). **Plus the answer to C7's H2′**: C7 P0 owns its local `HEAP_HEADER_SIZE + IO_PURE_GLUE_OFFSET == 32` compile-time pin (§6.7.3). C4 B5 independently owns `PURE_GLUE_ABS_OFFSET == 32`; C7 makes no backend edit, and no root-test fallback is reserved |
| H2″ | `/design`(platform) → C7 | **C7's H8 is discharged in this change-set.** §6.3's "closed set of three" now reads four sanctioned stamp sites, §13 reject 10 reads accordingly, and the adoption site has its own subsection (§6.7). No contradiction remains between this contract and its reject list for `dev`(backend) to hit |
| H3 | `/design`(int) → C6 | the int twin `strip_io_head` deletes with 0898; the §9.1 subject projection lands with B2 so R-4 is discharged end-to-end; `Bind`'s bootstrap seed leaves the constructor introspectable (§6.6) |
| H4 | `/qa` + `/test` | 0781's three residual items: re-point the two `let`-mediated cells' `// defect:` notation as resolution records; land Q3/Q1 with their Q2/Q4 negative controls as GREEN regression guards; place the three `match_codegen` faces, currently unit-pinned only |
| H5 | `/qa` | 0811's rule, and its application here: 0917's exemplar residue cell is a **downstream observer**, not an acceptance witness for any C4 bundle. A surprising reading is new intake |
| H6 | `/test` | 0900: whether to tighten cell #15's `locus=` token to a no-space seam form. `test`'s call; crate-grain is established practice either way |
| H7 | `/qa` | the acceptance classes in the table above — which bundles are byte-identical and which carry a scoped attributed re-baseline — and the §5.3 corpus-gate assertion form. **This is where 0747's "byte-identical vs RC-neutral" question goes**; §8.3's ruling means no choice is needed, but the class statement is QA's to hold |
| H8 | `/qa` | the face-4 residual guard §7.1 of the contract owed is **re-specified**: not a failing-not-ignored leak cell, but a GREEN acceptance cell (a nested `Pure` inside an unrun `Bind` sub-tree is discharged), with the double-discharge negative as its discriminating control |
| H9 | `/design`(primitives) → C5 | **The §3.8 gate is answered and C5 needs no dispensation.** The `("vec-len", 1)` arm lands dormant in B8, inside C4's own reserved surface (§8.5); after B9, C5 P0 immediately flips the declaration and activates that arm with **no backend edit**. C5 P2 keeps the declaration truth B9 consumes: the six only-read string rows remain `Mode::Borrowed + ParamFlow::Consumed`, while `string-identity` remains `IntoResult`; its typed derivation may strengthen the producer check but must not alter those facts. C5's `tests/vec_query_value_use.rs` cells are the shared pre-P0 path/post-P0 balance control |
| H10 | `/qa` + `/test` | R3's closed acceptance matrix (§4A.3): all six surviving string extern rows in applied and value positions, the representative binary auto-curry row, `string-identity` as the `IntoResult` control, and `vec-len` as the pre-P0 path/post-P0 balance control. The implementation is realization/flow-derived; the six-name enumeration exists only in acceptance. QA owns exact-once attribution and the scoped wrapper-frame re-baseline |

---

## 11. Source and module-test reservations

**Writable by C4** (`crates/cranelisp-backend/src/`, whole tree) with one
cross-stream carve-out:

| Path | Reservation |
|---|---|
| `cache/mod.rs` — the `CACHE_SCHEMA_VERSION` **value** | **C1, all sprint** (§4.3). C4 edits the rest of the file freely |

`compiler/apply.rs` is wholly C4-reserved: B5 lands
`PURE_GLUE_ABS_OFFSET`, its local `== 32` pin, and the tag-dispatched stamp in
the one backend visit. C7 has no later line reservation in this crate, and no
root-test offset assertion is planned (§6.7.3).

`crates/cranelisp-backend/CLAUDE.md` remains `/dev`(backend)'s, updated in the
same visit — the release-gate row's stale "five gates" count, the 0906 prologue
row's incomplete consumer list, and the §"Canonical drop glue" bullets naming
I-CT as live. B9 additionally replaces `emit_d24_adaptation`'s stale
Mode-only premise with the realization/flow rule (§4A).

**The `("vec-len", 1)` arm is inside this reservation and is C4's** (§8.5,
bundle B8). The C5 primitives visit §7 *requests* that one arm without reserving
it, and `total-concreteness.md` §3.2 answers the request by allocating it here;
no dispensation is issued and C5 makes no backend edit. Two files stay untouched
by C5: `compiler/control_flow/fn_as_value.rs` is C4-reserved for B9, while
`compiler/context.rs::is_inline_primitive_at` stays untouched by **both**
streams because the inline route is already carrier-keyed. Any general keyed
entry projection B9 needs in `compiler/context.rs` is C4's; it must not alter
the inline predicate or add a name classifier.

**Not C4's, named so they are not touched:** `crates/cranelisp-types/`
(C1 — and §7.1 confirms **zero delta is needed**),
`crates/cranelisp-intrinsics/src/drop.rs` (C5),
`crates/cranelisp-platform/` incl. `ABI_VERSION` (C7),
`src/result_owner.rs` and `src/bootstrap.rs` (C6),
`tests/` and `tests/plan/` (`test` / `qa`),
`design/arch/fixmes/` (owning roles delete).

**Module-test reservations**, per submodule, per the crate's sibling convention:

| Submodule | Test module | Bundle |
|---|---|---|
| `compiler/context` | the existing `ctor_value_shape_tests.rs` sibling, plus a new `ctor_field_instantiation_tests.rs` | B4 (§7.1) |
| `compiler/rc_emission` | a `signature_heap_category` sibling carrying the census's two detection legs and, post-flip, the located error | B3, B4 |
| `compiler/fn_compiler` | `ctor_template_admission_tests.rs` **re-pointed** (§12 row 2); a binding-root sibling for §8.3 | B4, B6 |
| `drop_glue` | the existing `vec_arm_rc_gate_tests.rs`, plus the IO arm rows | B4, B5 |
| `compiler/apply` + `compiler/control_flow/fn_as_value` | the `Pure` stamp rows at all three construction sites; **the platform-return tag-dispatch rows extend the existing `apply/platform_fn_name_stamp_tests.rs` sibling** (§6.7.4) — the tag load, both guarded stores, the no-write fall-through, the two-instantiation glue-identity cell, the branch-dominance walk and the non-platform-callee negative. That file already owns the Effect arm's rows, so the guard is proven where the unguarded store is currently pinned | B5 |
| `compiler/control_flow/fn_as_value` | new `d24_adaptation_tests.rs`: exhaustive realization/flow classifier, consuming-extern vs borrowing-Body CLIF pair, `IntoResult` control, and direct-value/auto-curry parity | B9 (§4A) |
| `compiler/vec_codegen` | the folded-prologue polarity pin, the refusing element-type arms, and the dormant `("vec-len", 1)` arm's direct-emission row | B4, B6, B8 |
| `error` | the diagnostic-frame rows | B2 |
| `cache/serialize` | the load-boundary validation arms | B1 |

---

## 12. Unit-test design (backend tier)

Replaces `non-concrete-release-contract.md` §9 for the rows this visit moves.
E2e acceptance is `qa`'s.

| Submodule | Positive | Edge | Negative |
|---|---|---|---|
| lifecycle disposition (§4.1) | each `Concrete × Realization` arm lowers as the table says; `defined_symbols` equals the `Concrete × Body` projection exactly | `FacadeOf` populates the slot as a name-alias and emits no per-instance body | the match over `Life × Realization` is **exhaustive, no `_ =>`**; a `Template` in value position is a located refusal naming the symbol; a `Declared` entry reaching codegen is a located refusal |
| `rc_emission::signature_heap_category` (§5, §7.2) | each concrete shape maps to its category; the census records a licence with frame partition and type shape | a concrete sum with a nullary ctor is `Mixed`; a concrete product is `AlwaysHeap` | **both census legs**: a planted residual-typed parameter frame fires it in the right partition; a concrete frame leaves it silent. Post-flip, a residual `Type::Var` is a **located error naming the frame**, never `Mixed`, and no RC op is emitted |
| `compiler/context` ctor materialisation (§7.1) | field types at a concrete instantiation come from the one types projection and agree with the declaration at concrete positions | a nullary ctor yields zero fields at any well-formed instantiation; an arity mismatch is a keying error, distinct from a refusal | **`CtorField` cannot hold a residual type** (unrepresentable); a residual instantiation is a located refusal at the reference's span, not a fabricated `Int`; no second field-type read exists |
| `fn_compiler` ctor frames (replaces the §9 row 2 / §10 row 4 lineage) | a concrete-instantiation ctor frame emits the ordinary `drop<T>` path | a multi-field concrete ctor discharges every owning field once | **no ctor frame with a residual parameter is a codegen target** (the C1/0931 structural claim, asserted here so its falsification is loud); `assert_threshold_guarded_rmws` finds no rmw traceable to a residual slot |
| `drop_glue` IO arm (§6.4) | `ADT(primitives/IO, [T])` classifies runtime-owned and emits exactly guard + dec + fence + `call runtime/free_io_node`, identically for two distinct `T` | nested `Bind` over `IO (IO Int)` requests one body, not two | `ctor_shapes` is **not** called for `primitives/IO`; no IO payload releaser symbol is minted; the `:497-505` identity check is unchanged and still fires for a genuinely divergent user type |
| `Pure` construction stamp (§6.3) | all three construction sites stamp; a heap payload stamps the **same `FuncId`** the release path would call; a scalar payload stamps `0` | the hidden word occupies field 1 (offset 32) and the payload's field-0 offset is unchanged by it, so every existing field-0 read still resolves; `payload_size(2)`; construction/adoption use ordinary stores only while unpublished | exactly one constructor answers non-`None` to the self-description question (closed-set pin); a stack-placed `Pure` always carries `0`; no per-site `matches!` on a constructor name exists; **backend emits no store to field 1 outside the four sanctioned stamp sites, never emits `1`, and never reads or calls through the word** — every post-publication access is C5's atomic helper (§6.2) |
| platform-return tag dispatch (§6.7) | over a seeded `DefKind::PlatformEffect` entry: the tag loads from `HeapAdt::TAG_OFFSET`; the `IO_TAG_EFFECT` arm stores the fn-name at `EFFECT_FN_NAME_ABS_OFFSET` value-identically to today; the `IO_TAG_PURE` arm stores at `PURE_GLUE_ABS_OFFSET`; **two instantiations** — `(IO String)` names the same `drop<String>` `FuncId` the release path names, `(IO Int)` stamps `0` | a tag outside `{EFFECT, PURE}` emits **no store**; the S6 poll arm still returns before the stamp block and emits none; `PURE_GLUE_ABS_OFFSET` is the crate's only explicit offset expression for the glue word | **both stores are branch-dominated by the tag compare**, by control-flow walk (`assert_threshold_guarded_rmws` idiom) — reverting to today's unguarded store REDs the row; a non-platform callee emits no stamp block; no second identity is minted for the Pure arm; no ABI-version test is emitted (the gate is C7's one number) |
| binding-root finder (§8.3) | the direct, binding-indirection and COW reach classes are each produced by the one traversal | a `Match` that does not forward its scrutinee yields no root; a producing node yields no root | each of the three thresholds reproduces its pre-collapse predicate **on the same corpus** — the byte-identity claim, pinned rather than asserted; exactly one node-kind list exists |
| `vec_codegen::emit_vec_query_into` — the dormant `vec-len` arm (§8.5) | the `("vec-len", 1)` arm is exercised **directly** and emits the length-word load plus the `vec-get` arm's rc-checked Vec release — the same `vec_drop` id and the same per-element dec pointer | a heap element type resolves the same dec pointer the `vec-get` arm resolves at that element type; the arm returns the length, never an element | **the arm is unselectable before C5's flip**: a value-position `vec-len` probe whose entry kind is `user_extern` still emits the GOT/extern path, and the golden-CLIF corpus does not move; an absent element type is §7.3's located refusal, not a local degrade; no name test is added at either call site |
| `fn_as_value` wrapper discharge (§4A) | exhaustive realization/flow plan: `Body + Borrowed` emits one typed wrapper dec; `ExternShim + Consumed` emits none | `IntoResult/AliasOf(0)` preserves `string-identity`; `ExternShim + Retained` takes the no-dec conservative direction; direct value and auto-curry consume the same plan once | no six-name, primitive-kind or module-name classifier; a kind-blind deletion fails the borrowing-Body CLIF row; no stacked auto-curry adapter; C5's whole-inventory derivation proves no surviving heap extern relies on `Retained` |
| `heap::emit_nullary_skip_guard` (§8.2) | both former `vec_codegen` copies now route through it | the adapter's separate Cranelift context is served by the free-function form | absolute polarity by control flow (each `atomic_rmw` traced to its guarding compare and branch arm), not by counting `iconst 1024`; no third spelling of the prologue exists in the crate |
| `error` frame (§8.4) | one category prefix, a real span, an unmangled subject | a refusal from inside a monomorphised instance renders the instantiation as types | no `0..0` from the glue registry; no `module/module/` doubling |
| category-before-provenance (§3.1, §7.4) | — | — | **the standing falsifier cell**: no provenance-licensed RC emission is reachable without a preceding category gate on the value's own type |

---

## 13. `/review` reject criteria

`non-concrete-release-contract.md` §8 and `transitive-drop-glue.md` §11 stand.
Added by this visit:

1. **A second bump of `CACHE_SCHEMA_VERSION`, or an edit to the value C1 set**
   (§4.3). A serde-shape change discovered in C4 is reported, not absorbed.
2. **A `_ =>` arm in the lifecycle disposition** (§4.1). The exhaustive match is
   the instrument; a catch-all is how the next unlowerable state arrives
   silently.
3. **A per-site constructor-name test for the `Pure` stamp** (§6.3). One
   derivation, three readers.
4. **A backend-side IO teardown walk.** If C5's entry point is not available,
   the bundle waits; it does not grow a second tag-walker (§6.5).
5. **Re-landing the frame-keyed release narrowing** (§7.2). Measured at +16 hard
   refusals twice, one sprint apart.
6. **A new `unwrap_or`/`unwrap_or_default` narrowing a `Type` or `ConcreteType`
   at any RC, glue, or category seam** (§7.3). The disposition for an absent
   type is a located refusal.
7. **A census instrument reachable in a release build** (§5.1).
8. **A widening of the fn-return skip to the binding-indirection class inside
   B6** (§8.3). It is a separate, separately-measured change.
9. **A golden re-baseline outside the three bundles that declare one** (§10),
   or one taken without scoped attribution.
10. **A backend-emitted write to, or call through, the `Pure` glue word outside
    the four sanctioned stamp sites** — the three construction stamps (§6.3)
    and the platform-return adoption stamp (§6.7). A **fifth** site is a reject
    (`total-concreteness.md` §3.4). Backend performs ordinary `0`/glue
    initialisation while the node is unpublished and never emits `Claimed(1)`;
    C5 alone performs post-publication atomic reads/mutations on force and
    teardown. A backend maintenance/read point re-opens the ownership channel
    the one atomic state exists to close.
11. **Anything that makes the `("vec-len", 1)` arm reachable inside C4** (§8.5)
    — an edit to `is_inline_primitive_at`, a B9 edit to `fn_as_value.rs` that
    changes that kind gate or selects the inline route, or any name-keyed route
    into the arm. The declaration flip is C5's and is the only activation.
12. **The dormant arm landed without its direct unit row, or carrying its own
    absent-element-type default** (§8.5). Zero consumers under static review is
    not landed, and a per-arm degrade is R-2's shape one seam down.
13. **A stamp store not dominated by its tag compare**, or a stamp still
    selected by the callee's `DefKind` alone (§6.7.2). The kind-selected store
    is the defect R19 records; re-landing it, or guarding only the Pure arm and
    leaving the Effect arm unconditional, reproduces it.
14. **A second backend offset expression or a cross-owner restatement of the
    glue-word offset** (§6.7.3) — a bare `32` other than C4's local pin, a
    per-site `HeapHeader::SIZE + …` recomposition, importing
    `IO_PURE_GLUE_OFFSET` to assert a joint form in backend, or a root-test
    duplicate. One backend composition, one owner-local pin, zero crate revisit.
15. **A backend-side ABI-version test, footprint absorber, or "v9 mode" at this
    seam** (§6.7.5; C7 §3.5, §15 reject 15). The window residual is `sprint`'s
    ordering constraint, not a runtime branch, and the platform-local absorber
    was rejected by `arch` because it removes the symptom and keeps the
    mechanism.
16. **A name list, `DefKind::Primitive` proxy, module-name test or six-row
    branch for R3** (§4A). Wrapper discharge is a function of the keyed
    `Life::Concrete` realization and the declaration's `ParamFlow`; the six
    names belong only to acceptance enumeration.
17. **Deleting every Borrowed wrapper post-dec.** A backend `Body` whose moded
    ABI genuinely borrows leaves the closure-owned argument for its wrapper to
    release; the synthetic Body/Extern pair must discriminate.
18. **An auto-curry-only ownership path, a direct `BuiltinFn` extern bypass of
    the realization plan, or a stacked value-wrapper adapter** (§4A.1). Direct
    value and curry wrappers consume one shared positional plan once; neither
    selects an `ExternShim.borrowed_sibling` from the owned closure protocol.
19. **Changing a `Mode`, `ParamFlow`, result mode or primitive declaration to
    accommodate B9.** The declaration is authority; this bundle repairs the
    lower emission carrier and preserves `IntoResult`/`string-identity`.

---

## 14. Quality attributes

- **Simplicity.** The class shrinks. Retired in this visit: I-CT and its
  standing `Borrowed`-mode obligation, the `Err ⇒ Mixed` fabrication, the
  type-keyed release arm, three `unwrap_or` narrowings, the ctor declaration
  channel, two hand-rolled prologue copies, two duplicated name-finders, one
  duplicated strip rule, and `drop<IO T>`'s tag test and payload call. Added:
  one lattice-free reach class on an existing traversal, one hidden field on one
  node family, one call to an already-published types projection, one C5 atomic
  claim helper shared by force and teardown, one tag guard and adoption arm at
  an existing store site, one arm completing an existing four-way match, and
  one exhaustive realization/flow wrapper plan replacing a Mode-only loop.
  **Net mechanism count for release is
  unchanged at one plus the two sanctioned runtime dispatches** — the `vec-len`
  arm reuses the `vec-get` arm's release seam, and the adoption stamp reuses the
  construction stamp's registry call; neither mints a release identity. The
  stamp *site* count goes three → four; the mechanism count does not move.
- **Testability.** Every disposition has a negative cell that fails if the
  fabrication returns, and the one instrument this visit introduces is armed
  against a planted fault in its own change-set — the leg S119's plan would have
  had to borrow from corpus history it no longer has.
- **Observability.** The census is permanent, partitioned by frame origin, and
  is its own removal criterion. It is the only thing in this class that can
  *prove* the fabrication has no traffic left.
- **Safety.** The one class this visit *adds* an emission for is the one it
  closes: R19's kind-selected out-of-bounds store becomes tag-licensed at a
  single chokepoint (§6.7), so the store that could land outside its node stops
  being emittable rather than being made unreachable by inspection. Its residual
  is a scheduling window with zero traffic and a named falsifier (§6.7.5), not
  an unprotected path.
- **Concurrency-safety.** C4's producer emission is unchanged by R1: each
  ordinary `0`/glue store occurs on a fresh unpublished node. The complete
  runtime contract is stronger: after publication C5 exclusively accesses the
  word atomically, and force/teardown share one `swap(Claimed, AcqRel)` helper.
  Its modification order closes double force; the existing same-strand,
  Release-dec/Acquire-fence and structured-join edges remain the node-lifetime
  boundary. Release-dec alone still does not cover the worker branch, and R2's
  severed join remains the one premise failure (§6.2).
- **Performance.** Faces 1–3 remove thousands of guarded inc/dec pairs from the
  measured corpus at zero behavioural cost, via the producer rather than via
  backend. `Pure` grows by one word per node; the teardown lane loses a tag test
  and a per-`T` glue body. **The run lane is not free**: every `Pure` force gains
  one atomic exchange before its payload read. B9 removes one redundant guarded
  dec per affected Borrowed extern parameter; backend-Body and `IntoResult`
  controls are byte-identical.
- **Maintainability.** The blast radius of the next non-concrete frame is
  bounded by construction: it cannot settle `Concrete`, its field types cannot
  enter a `CtorField`, there is no fallback arm to absorb it, and the census
  names it on the first run.

---

## 15. Open, and owned elsewhere

- **The IO ordering collision** (§6.5) — `sprint`'s to resolve; the preferred
  resolution is already arch's stated placement.
- **The C4 → C7 window for the Pure adoption arm** (§6.7.5) — `sprint`'s, the
  same class as the collision above and sequenced with it: no `Pure`-returning
  platform fn may land before C7's P0. Zero traffic today, verified at source;
  falsifier stated; register row R19.
- **A `Select` loser's severed fork-join** (§6.2) — the one pre-existing named
  publication/lifetime residual, with its falsifier. R1's double force is ruled
  and allocated to C5 I0b; it is not carried as an open C4 residual.
- **Converging the seam-by-seam category gates into one** (§7.4) — a larger
  reshape than this visit; the falsifier cell is the standing detector until
  someone takes it.
- **The fn-return widening** (§8.3) — a potential extension with its trigger and
  its re-proof obligation recorded.

No user-owned, spec or architecture decision remains implicit in this design.
Every input it consumes was ruled before this window: the lifecycle target, the
IO node layout, the ABI and schema windows, the 0553 facade, 0934's inclusion,
and the `vec-len` de-slot's spelling with the allocation of its one backend arm
to C4 as a dormant landing — and, added 2026-09-01, the platform-return tag
dispatch with its allocation to B5, the rejection of the platform-local
absorber, and the zero-revisit owner-local offset pins.

## Next skills

- **`/design`(intrinsics)** — handoff H1: the `free_io_node` split and the
  shared atomic force/teardown claim, duplicate-force outcome, cleanup and
  observer, against §6.
- **`/design`(platform)** — handoffs H2 and H2″: ABI 9→10, the sentinel, the
  `Pure`-returning fixture, and C7's own `== 32` compile-time pin; C7's H2′ is
  answered without a backend edit, and its H8 is discharged (the stamp set
  reads four).
- **`/design`(primitives)** — handoff H9: the §3.8 gate is answered; the arm is
  C4's and dormant, and P0's flip activates it with no backend edit.
- **`/qa`** — handoffs H4, H5, H7, H8 and H10: the acceptance classes per
  bundle, R3's closed six-row matrix and wrapper re-baseline, the §5.3
  corpus-gate form, the re-specified face-4 cell, and 0781's residual items.
- **`/dev`(backend)** — bundles B1…B9 in the §10 order, each with its §12 rows
  and its declared emission acceptance class; the census's detection proof lands
  with B3, not after it, B8's direct-emission row lands with B8, and B9 lands
  last with its realization/flow units.
- **`/sprint`** — the §6.5 ordering collision; the §11 reservation of
  `CACHE_SCHEMA_VERSION` to C1; and one wave-order fact: **B8 lands in C4's
  implementation wave, before C5's P0**, since P0's flip is what makes the arm
  live. C5's §6 wave note ("its backend arm must not share a wave with C4's own
  bundles") was written for the dispensation route and no longer describes the
  ruled allocation — the arm *is* a C4 bundle. **Added 2026-09-01:** the
  §6.7.5 window constraint (no `Pure`-returning platform fn before C7's P0),
  and B9→C5 P0 with no integrated acceptance between them (§4A.2).
