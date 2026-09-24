# The non-concrete release contract

**Owner:** `design`, narrow-deployed to `cranelisp-backend`. **Subordinate to:**
[backend.md](backend.md).

**Status:** the adopted contract for how the backend licenses every RC
operation it emits, the disposition of each non-concrete face, and the open
backend work that completes it. It absorbed the S121 C4 visit design; that
visit's delivered bundles are recorded here as current mechanism and its open
bundles as §7. Source was re-verified on 2026-09-21.

**Architecture inputs, cited rather than restated:**
[concrete-boundary-type.md](../arch/concrete-boundary-type.md) §3.1.1 (the
signature-driven codegen target);
[total-concreteness.md](../arch/total-concreteness.md) §3.2 (the `vec-len`
de-slot), §3.4 (the `Pure` ownership witness, the reusable-IO ownership rule on
force, and the platform-return seam), §3.5 (platform-effect signatures stay concrete);
[symbol-table-lifecycle.md](../arch/symbol-table-lifecycle.md) §4 (the callable
state machine) and §5.5 (inline primitives mint no table entry);
[safety-invariants.md](../arch/safety-invariants.md) §4, rows R17 (R-1), R18
(R-2) and R19 (the platform-return stamp).

**Producer obligations** for faces 2, 3 and 5 are typecheck's, in
[non-concrete-producer-obligations.md](../typecheck/non-concrete-producer-obligations.md).

---

## 1. The fact the contract rests on

The backend releases a heap value by calling the canonical glue for its concrete
type ([transitive-drop-glue.md](transitive-drop-glue.md) §1). That requires
codegen to name the concrete type. This document states what happens when it
cannot.

> **A word whose static type is a residual type variable has no heap category.**
> It may hold a heap pointer, a bare nullary tag, or a raw scalar. The
> `NULLARY_TAG_THRESHOLD` guard separates tags from pointers; it cannot separate
> scalars from pointers. Therefore no RC operation — inc or dec, guarded or
> not — is legal on such a word, and no shallow release of it is "merely a leak".

---

## 2. The measurement record (S119)

This evidence cannot be re-derived: the census scaffold was reverted and the
corpus has since moved. The ruling was measured before it bound.

### 2.1 Method

A throwaway instrument recorded every admission at the two seams below across
`cargo nextest run --no-fail-fast` on the S119 Phase-3 tree (`5520186d`), with
the baseline RED set reconciled name-for-name and no untraced RED.

### 2.2 Census A — the release seam (`emit_heap_binding_decs`)

2,497 admissions of the type-keyed non-concrete arm, **all** from
`pop_scope_with_cleanup` in a parameter frame; the two tail-jump flushes
admitted **none**. 2,216 were constructor-template frames. The other **281**
were exactly two families, both compiled once per declaration:

| Family | Frame | Parameter shape | Examples |
|---|---|---|---|
| **F1** synthetic field accessor of a generic or undeclared-field product | `Type.field` | `ADT(<concrete>, [Var…])` | `Grid.cells`, `Box.v`, `Pair.first` |
| **F2** generic trait-method instance | `Trait.method$Type` | `Fn([Var…], Var)` or `ADT(<concrete>, [Var…])` | `Functor.fmap$primitives/Option` |

No escapee's own type was a bare `Type::Var` at this seam: the outer constructor
was known, so the shallow dec was category-correct on the outer word and wrong
only in field-discharge depth.

### 2.3 Census B — the retain seam (`signature_heap_category`'s `Err ⇒ Mixed`)

That arm is the single point at which a residual type acquires an RC licence:
5,499 licences, of which **3,646 were a bare `Type::Var`** (3,108 in
constructor-template frames, 538 in F1/F2 frames), 1,776 `ADT(<concrete>,
[Var…])` and 75 residual `Fn`. The bare-`Var` licences are the class's
memory-unsafety surface.

### 2.4 F1 is memory-unsafe, not merely leaky

```lisp
(import [primitives [IO Pure]])
(deftype (Bx a) [:a v])
(defn get [b] (v b))
(defn main [] (Pure (get (Bx 1024))))
```

`--run --no-cache` exits correctly for payloads 100 and 1023 and **SIGSEGVs at
1024 and above** — the `NULLARY_TAG_THRESHOLD` boundary, on the first call. The
accessor's CLIF carries a guarded `atomic_rmw add` at `field+8` on the extracted
`Var` field (a wild write on a scalar) and a shallow, field-discharge-free
dealloc of `self`. F1 and F2 are one severity.

### 2.5 The constructor template's own licence

Constructor-template frames carried the identical guarded inc/dec pair on a
residual parameter. The guard makes both halves wild together on a scalar
payload ≥ 1024. No corpus execution of a template *body* was observed — the
constructor-as-value path lowers construction at the concrete type — which is a
reachability observation, not a soundness argument.

### 2.6 Frame-key falsification

Re-keying the admission to the frame (admit constructor templates, refuse the
rest) was measured twice, one sprint apart: the `spec_*` corpus went from
8 to 24 failures. The 16 new hard refusals are the F1/F2 frames — legal
programs whose producer handed the backend a frame it cannot compile. The
narrowing is not landable alone (§8 reject 4).

---

## 3. The contract

### 3.1 Rule R-1 — category before operation

> No RC operation (inc or dec, guarded or unguarded, at any seam) may be emitted
> on a word whose **heap category** codegen cannot name from the word's own
> static type. `HeapCategory::Mixed` is a nameable category, derivable only from
> a **concrete** sum type's constructor set; a residual type variable is not
> `Mixed`, it is the absence of a category.

`signature_heap_category`'s `Err(_) => HeapCategory::Mixed` arm
(`compiler/rc_emission.rs`) still violates R-1; retiring it is §7.4.

### 3.2 Rule R-2 — no fabricated concreteness

> No component may present a downstream gate with a type, category, shape or
> mode more concrete than what it actually knows in order to pass a gate that
> would otherwise refuse. An unsatisfiable gate is a **producer obligation**,
> never a licence to invent the missing fact.

This is Principle 25 (Narrowing carries its check) applied to the type channel.
The backend fabrications still in source are listed with their dispositions in
§7.4.

### 3.3 Rule R-3 — a non-concrete frame is not a legal codegen target

> A frame whose parameter or result types are not fully concrete cannot emit
> correct release code by any disposition available to it. Where the pipeline
> presents one, the defect is the frame's existence, not the backend's handling
> of it.

The proof is §4.3.

### 3.4 Rule R-4 — the refusal must be actionable

> Where the disposition is a located refusal, the diagnostic must name a real
> source span, a subject the user can look up, and one category prefix. A
> refusal at span `0..0` against a `$`-mangled internal name does not discharge
> this contract.

The normative surface is
[repl/spec/05-error-presentation.md](../../repl/spec/05-error-presentation.md)
§5.5. The backend obligation is §7.2.

### 3.5 The gate order

> **Category, then provenance, then emitter.** A seam asks the value's own
> concrete type for its `HeapCategory`; `NeverHeap` and `Value` emit nothing and
> the seam stops. Only then does it ask `value_provenance` *whose* reference it
> is. Provenance never answers *whether* a reference exists.

This is the as-built shape at every seam: the match seam ANDs its plan with
`scrut_is_heap`, the Vec seams take a Vec-typed operand, and the `BorrowRoot`
consumer matches on `signature_heap_category` with empty `NeverHeap | Value`
arms. The gates are asserted seam by seam rather than converged. **Named
falsifier:** a provenance-licensed RC emission not preceded by a category gate
on the value's own type. Converging the gates is a larger reshape, not scheduled
(§10).

### 3.6 Three emitters, and no fourth

| Emitter | Home | Purpose |
|---|---|---|
| The nullary-skip prologue | `heap::emit_nullary_skip_guard`, reached through the guarded RC helpers | the one tag-vs-pointer decision for every guarded inc and dec, in any Cranelift context |
| The canonical typed release | `rc_emission::emit_typed_rc_dec` → `drop<T>` from `DropGlueRegistry` | releasing a heap value as a function of its type, never its site |
| The two sanctioned runtime dispatches | the closure's embedded `DROP_GLUE_PTR`; the intrinsics IO tag-walker (§5.4) | releasing a value whose structure only the runtime can see |

The `Pure` payload-glue word (§5) is not a fourth mechanism: every site that
writes it materialises the address of the same `drop<T>` from the same registry.
A new release mechanism is a reject regardless of what it fixes (§8 reject 1).

---

## 4. The five faces

Every measured face has exactly one disposition.

| # | Face | Disposition | State |
|---|---|---|---|
| **1** | Constructor template's own residual parameter | The template frame emits nothing on it (I-CT′, §4.1) | **Structural:** `Life::Template` carries no slot and no view, so a residual-parameter constructor frame is not a codegen target. Evidence reconciliation of the constructor census partition stays open under FIXME 0931 |
| **2** | Synthetic accessor of a generic product (F1) | Canonical glue after the frame is monomorphised per concrete instantiation | Producer obligation (typecheck). The backend fallback arms it relies on retire in §7.4 |
| **3** | Generic trait-method instance (F2) | Same as face 2: the instance key widens to the full concrete instantiation | Producer obligation (typecheck); its backend arm closes with §7.4 (FIXME 0903) |
| **4** | IO's existential `Bind` | Runtime-directed teardown, with the `Pure` payload stamped at construction | **Delivered** (§5) |
| **5** | Typecheck's lenient-view result root | Canonical glue once the view carries the node's real type, with unconstrained parameters explicitly defaulted | Producer obligation (typecheck) |

FIXME 0917 is not a face: its types are concrete throughout. It is §6.

### 4.1 Face 1 — why the pair deletes (I-CT′)

The S118 ruling kept the template's guarded inc/dec pair under invariant I-CT
("the count balances"); [transitive-drop-glue.md](transitive-drop-glue.md) §4.1
retains that record. I-CT is silent on whether the word is a reference at all,
and §2.5 shows it is not always one. The replacement:

> **I-CT′.** A constructor template's body is straight-line and only moves each
> parameter word into the box it returns. Under the Decision-24 consuming
> convention the caller has already transferred one reference per argument, and
> storing the word transfers it to the box. The frame owes neither a retain nor a
> release for any parameter type.

I-CT′ is now discharged by representation rather than by a deletion in the
frame: no residual-parameter constructor frame reaches codegen. The
`Borrowed`-mode standing obligation that I-CT carried retires with it.

### 4.2 Faces 2 and 3 are one face

Both censuses place F1 and F2 in the same rows, with the same type shapes, at
the same seams, and §2.4's threshold boundary appears in both. They differ only
in which producer exempted the frame from monomorphisation. The compiler already
monomorphises ordinary generic functions; the disposition is to stop exempting
these two frame kinds.

### 4.3 No in-frame disposition exists (R-3)

Take `(impl (Functor Option) (defn fmap [g o] (match o [None None (Some x) (Some (g x))])))`
compiled once with `x : Var`:

| In-frame policy | Scalar payload `(Some 1024)` | Heap payload `(Some "s")` | Duplicating arm `(Pair x x)` |
|---|---|---|---|
| Count it | wild atomic write → SIGSEGV | correct | correct |
| Do not count it | correct | leak | two boxes, one count → UAF |
| Discover it at runtime | impossible: a raw scalar has no header (a header type-word is rejected architecture) | | |

Every policy fails on a different axis. The payload's category exists only at the
call site, so monomorphisation is the only sound disposition. "Sanction a wider
frame set" and "withdraw the retain licence for F2 only" are rejected on this
proof.

### 4.4 Why face 4 alone is runtime-directed

`IO T` is concrete; the failure was glue *derivation*. `ctor_shapes` builds one
substitution across a type's constructors and correctly refuses when they
disagree, and `Bind`'s existential keeps its inner type free by construction.
The runtime can nevertheless see the structure without a header type-word: IO
nodes carry a tag, and `Bind`'s continuation is a closure carrying its own
`DROP_GLUE_PTR`. The one field only the type knows — `Pure`'s payload — is
known with certainty at every *construction* site post-mono, so the backend
supplies it there (§5.3) instead of at teardown, where it is certain only for
the root. For faces 1–3 no such runtime self-description exists.

### 4.5 Rejected: refusing to own IO

Restoring the pre-S116 behaviour (the registry declines IO) compiles again and
restores the silent leak measured at ~68 bytes per call through
`(impl (Functor IO))`. It also fabricates the fact "this type owns nothing"
(R-2). Rejected.

---

## 5. The IO node and its release (face 4, delivered)

The node layout and the trampoline's reads are
[io-trampoline.md](io-trampoline.md) §1.1. IO values are reusable: a force
of a `Pure` or `Effect` node moves no field out of it, and teardown discharges
each owned field once ([total-concreteness.md](../arch/total-concreteness.md) §3.4;
`spec/10-io.md` §10.8.1). How intrinsics forces and tears down a `Pure` is
[Pure ownership contract](../intrinsics/ownership-and-disposal.md#61-the-pure-payload-witness-retain-on-force). This
section owns the backend's side: construction, the stamp and the release call.

### 5.1 The `Pure` node

`Pure` is the two-field allocation `[header | tag@16 | payload@24 |
payload_glue@32]`. Every other IO node is unchanged. The payload stays at field
0, so existing field-0 reads and pattern binds are untouched. The hidden word is
never a language-visible field; it follows the closure `DROP_GLUE_PTR`
precedent, not a header type-word.

### 5.2 What the backend may write, and when

The word is a witness written once, before publication, and immutable
afterwards: `0` (`Scalar` — the payload owes nothing) or the payload's canonical
`drop<T>` address (`Owned(glue)`). `1` is reserved and emitted by nothing.

- **The backend only initialises.** Each stamp site writes `0` or a canonical
  `drop<T>` address with an ordinary aligned store while the fresh node is
  exclusively owned and unpublished. It never writes `1`, never performs an
  atomic operation on the word, and never reads or calls through it.
- **Publication ends backend authority.** After publication the word is only
  read, by the intrinsics force and teardown lanes: each force of an
  `Owned(glue)` payload mints the consumer's own reference, and teardown calls
  the glue once. A backend read, maintenance store or post-publication write
  would add a second ownership channel to a word the reuse rule keeps immutable
  (§8 reject 10).

### 5.3 The stamp — a closed set of four sites

Three sites construct the node — the inline concrete `ConstrADT` lowering, the
resolved-constructor `Apply` path, and the value-position constructor wrapper
body — and one adopts a node the platform constructed (§5.5). Two rules bind all
four:

- **One derivation, never a per-site name test.** Whether a constructor carries
  a hidden self-description field, and its value, is answered once beside the
  keyed `ctor_meta_at` read; it answers non-`None` only for `primitives/IO.Pure`,
  so every other constructor emits byte-identically. The adoption site keys on
  the returned node's tag, the same rule applied to a value that already exists.
- **The value comes from the registry.** The site asks
  `DropGlueRegistry::request_if_owning` for the payload's concrete type — the
  same call every release site makes — and materialises `func_addr` of the
  returned `FuncId`, or `iconst 0` when the request declines. The tag-and-fields
  emitter is unchanged and never given a type; the stamp is one more field value.

**Stack placement.** A stack-placed `Pure` (`NoEscape` with a scalar payload,
[ownership-codegen.md](ownership-codegen.md) §4) always carries `0` and, with an
immortal header, is never freed. **Falsifier:** a stack-placement verdict that
admits a heap-typed payload; stack placement for `Pure` must then be refused,
not stamped.

### 5.4 The discharge — `drop<IO T>`

The registry classifies `ADT(primitives/IO, [_])` as runtime-owned before shape
derivation, and `drop<IO T>` is the same body for every `T`:

```
drop<IO T>(p):
    if p < NULLARY_TAG_THRESHOLD: return
    old = atomic_rmw sub [p+RC_OFFSET], 1
    if old != 1: return
    fence
    call runtime/free_io_node(p)
```

`free_io_node` is the intrinsics tail of `consume_io_tree` split at the dec
(tag-walk, branch release, dealloc; precondition: the caller has decremented to
zero and fenced). It discharges every `Pure` in the tree, nested ones included,
through the stamped word. Three properties hold:

- `ctor_shapes` is not reached for `primitives/IO`, so its cross-constructor
  identity check stays exactly as strict for every other type;
- no IO-specific payload releaser is minted; every discharge is a `drop<T>` the
  registry already owns;
- the per-concrete-type glue *name* is kept although the bodies coincide:
  `drop_glue_symbol_name` stays the sole identity authority.

### 5.5 The platform-return adoption stamp

A platform DLL cannot name a glue address, so `CLIO::pure` writes `0` and the
backend replaces it at the one crossing where a blocking platform call's result
is in hand — the GOT-indirect platform-call arm of `compile_direct_call`. The
stamp dispatches on the **returned node's tag**, never on the callee's kind:

```
tag == IO_TAG_EFFECT ⇒ store fn_name_ptr → [node + EFFECT_FN_NAME_ABS_OFFSET]
tag == IO_TAG_PURE   ⇒ store glue        → [node + PURE_GLUE_ABS_OFFSET]
otherwise            ⇒ no write
```

`T` comes from the callee's concrete `(Fn […] (IO T))` scheme and the glue from
the same registry call as §5.3; a residual `T` is a located refusal, never a
default. The poll arm returns before this block and is untouched.

**Offset authority.** The crossing datum is absolute offset 32.
`PURE_GLUE_ABS_OFFSET` in `compiler/apply.rs` is the backend's only explicit
offset expression for the word, composed from `HeapAdt::field_offset(1)`, with
the owner-local pin `const _: () = assert!(PURE_GLUE_ABS_OFFSET == 32);`. The
platform crate pins its own composition independently; neither crate imports
the other's vocabulary for this check.

**Grade.** Structural for the licence (no store is emittable outside its tag arm
at the one chokepoint); measured for the arm's identity and branch dominance by
`compiler/apply/platform_fn_name_stamp_tests.rs`. The S121 window in which the
`Pure` arm existed against the one-field layout closed when the platform ABI
passed version 10.

### 5.6 `Bind` introspection

R-4 requires a refusal's nouns to be lookup-able. `Bind` is seeded outside the
ordinary synthetic-ADT registration, so whoever changes that seed must keep
`/info Bind` and `/info IO` working. This is int's bootstrap, recorded here so
the requirement is not lost.

---

## 6. FIXME 0917 — the provenance classification (delivered)

All types are concrete here; the seam is the protect licence in
`rc_emission::protect_return_value`, which fires when
`value_provenance(body) <= Fresh`. A bare nullary constructor reference is a
`MonoExpr::Var`, not a `ConstrADT`, and used to classify at the lattice top, so
one nullary arm poisoned a whole match's provenance and left a fresh boxed arm's
protect unbalanced.

### 6.1 The lattice

`ValueProvenance` has a bottom below `Fresh`: `NoReference ⊏ Fresh ⊏
OwnedTemporary ⊏ NotOwnedHere`, with `join = max`. **"Carries no reference" is
the join's identity, not its absorbing element.** Consequences:

- `is_fresh_construction` is `<= Fresh`; `yields_owned_temporary` is
  `matches!(p, Fresh | OwnedTemporary)`;
- the `Match` fold seeds at `NoReference`, so an all-nullary match reads
  `NoReference`, not a false `Fresh`;
- the explicit arm-less guard stays: ⊤ for a match yielding no value on any path
  is distinct from the empty fold's identity, and deleting the guard would swap
  one for the other.

No emission site gains a branch; this is a classification correction, not a new
licence arm.

### 6.2 Verdicts

| Node | Verdict |
|---|---|
| `Var`, global, zero-field constructor | `NoReference` |
| `Var`, global, constructor with fields | `NotOwnedHere` (a constructor value mints a wrapper; ⊤ stays conservative) |
| `Var`, any other | `NotOwnedHere` |
| `Apply` of a zero-field constructor | `NoReference` |
| `Apply` of a constructor with fields | `Fresh` |
| `ConstrADT`, no fields / with fields | `NoReference` / `Fresh` (probe-free: the field list is in the node) |
| Scalar literal | `NoReference` |

`NoReference` is a claim about the value that only the zero-field constructor
and scalars earn. A value-flattened one-field constructor is a different fact
with a different owner (`HeapCategory::Value`).

#### 6.2.1 The constructor probe — one determinant, one read

`value_provenance`'s context input is a **three-state closed classification of
a global reference** (`CtorValueShape`): not a constructor; a constructor whose
value is the tag itself (zero fields); a constructor whose use mints or moves a
payload. "Not a constructor" is the probe declining, not a constructor answer.

The producer is `CompileContext::ctor_meta_at`, the one keyed constructor read —
the same fact `literals::nullary_constructor_tag` uses to choose the bare-tag
lowering. A second read, or a second `is_nullary_ctor` probe beside the first,
could disagree with what was emitted, recreating 0917 one level down.
Pre-classifying at call sites is rejected for the same reason: it pushes the
rule back out to the sites `value_provenance` consolidates.

#### 6.2.2 Scalar bottom at probeless consumers

Scalar-literal bottom is probe-independent, so it reaches every consumer:
`protect_return_value` (with the real probe) and four probeless ones — the
match-arm lifetime plan, `cow_source_has_separate_owner`, `is_vec_last_use` and
`emit_vec_drop_if_temporary`. A scalar leaf is verdict-identical; at a join a
scalar arm is now absorbed rather than poisoning to ⊤.

This is inert at every release seam by the gate order (§3.5): no RC operation is
licensed by provenance alone. A scalar literal is only ever absorbed into a
scalar-typed join. The nullary constructor reference is the one bottom value
that can sit in a heap-typed join, and it is probe-dependent, so the probeless
seams keep their conservative reading — the leak-safe direction.

**Named residual.** `Trace`, `ParBind` and `LaunchContinue` cap their forwarded
value at `OwnedTemporary`, lifting a `NoReference` inner value to a false
ownership claim. The cap is uniform, only weakens, and is inert under the
category gate. **Revisit trigger:** a seam that consumes provenance without a
preceding category gate, or a `NoReference` value reaching a release through one
of these wrappers.

### 6.3 The monotonicity pin

The probe may only move a node's provenance **down** the lattice:
`value_provenance(n, real_probe) ⊑ value_provenance(n, no_probe)` for every
node, so probeless gates never over-claim ownership. The pin's corpus must
include nodes the probe actually moves — a bare nullary-constructor `Var` and a
mixed nullary/boxed match — and assert the strict move there; otherwise the pin
is vacuous.

### 6.4 Byte identity and acceptance

Only the constructor half can move emission, and only at `protect_return_value`.
The scalar half is claimed emission-neutral; a scalar-body or scalar-typed-join
golden difference is a **finding** (a seam consuming provenance without its
category gate), not a re-baseline. Acceptance was the two reduced
`nullary_arm_beside_boxed_arm_0917` cells at exact marginal zero; exemplar
residue cells observe and cannot reopen it.

---

## 7. Open backend work

Each item below is designed and not yet implemented, verified against source on
2026-09-21. None is accepted as residual. Order and dependencies are §7.7.

### 7.1 Consume the lifecycle exhaustively (partial)

The backend consumes `Life`/`Realization` at scattered sites; the target is one
disposition, exhaustive with no `_ =>` arm, so a state combination the backend
cannot lower is a compile error in this crate.

| State | Backend lowers | Refusal |
|---|---|---|
| `Concrete { Body { view } }` | the view, into the claimed slot. This projection **is** `defined_symbols()` | — |
| `Concrete { ExternShim { borrowed_sibling } }` | nothing; call sites import the shim | — |
| `Concrete { Dll }` | nothing; call sites are GOT-indirect against the manifest-order slot | — |
| `Concrete { FacadeOf { abi_name } }` | nothing per instance; the slot is the one hand-written body named by `abi_name`; no per-instance body or glue identity | — |
| `Inline` | inline lowering at concrete call sites; value position emits a span-keyed unit-local wrapper selected by `is_inline_primitive_at`, below the table | located error when the wrapper body has no arm for the name |
| `HostPromised` | nothing; by-name import | — |
| `Template` | nothing — not a codegen target | located refusal naming the symbol: no instantiation was demanded |
| `Declared` | nothing | located refusal: settlement did not run (a compiler-invariant breach) |
| `Broken { slot, error }` | nothing; the retained slot carries its trap stub | — |

`defn_param_types` then reads a witness-checked concrete scheme, so the
parameter channel cannot deliver a residual type — the structural half of §7.4.

**Cache-load validation.** The load boundary additionally validates, per entry,
claim uniqueness, `slot ⇒ scheme.is_concrete()`, origin × state legality and
tombstone conservation. Every arm diagnoses and recompiles as a `CacheStale`
class inside the existing single per-entry loop in `cache/serialize.rs`; a
parallel walk is a reject. None of these legality arms exists yet.

### 7.2 The refusal frame (0915, open)

R-4 must hold before §7.4 converts more sites to located refusals.

- **One category prefix.** `CompilationError::CodegenFailed` carries a
  pre-rendered cause that already embeds the inner located prefix, so the prefix
  renders twice. Fix the structure at the wrapping construction, never by
  re-parsing a rendered message.
- **A real span.** The glue registry's error helper uses
  `ErrorLocation::from_span(Span::SYNTHETIC)` (`drop_glue.rs`), the direct cause
  of `0..0`. Every registry error carries the requesting frame's or reference's
  span; the spans are on the `MonoExpr` nodes.
- **A lookup-able subject.** `"codegen failed for {module}/{symbol}"`
  (`cranelisp-backend/src/error.rs`) doubles an already-qualified monomorphised symbol. The backend
  supplies correct data; the presentation projection (`__expr` → the entered
  form, `f$T1+T2` → `f`) is int's, at [int.md](../int/int.md) §9.1.

The audience is the program author, so the permitted nouns are source-level.
Mangles, `__expr`, doubled modules and `0..0` are the wrong nouns for that
reader, not redaction candidates; nothing is suppressed for confidentiality.

### 7.3 The category census, armed (open)

A permanent debug-profile census of every `Err` licence at
`signature_heap_category`, keyed by the requesting frame's `CallableOrigin`
partition (`Ctor` / `Accessor` / `TraitMethod` / `Plain`) and the type shape
(bare `Var`; `ADT(<concrete>, [Var…])`; residual `Fn`). It is a developer
instrument whose nouns R-4 forbids in user output, so it never reaches a release
build.

**Both detection legs are planted in the instrument's own change-set**, because
the corpus traffic that proved S119's scaffold is gone:

- positive — a unit fixture plants a frame whose entry scheme carries a residual
  parameter; the census records exactly one licence in the expected partition
  and shape;
- negative — the concrete twin leaves the census silent.

**Flip criterion (for §7.4):** across the full default suite and the `spec_*`
corpus, zero licences and zero release admissions in the `Ctor`, `Accessor` and
`TraitMethod` partitions, with the corpus failure count not above the S119
baseline of 8. The census reading zero is the criterion; a code reading is not.

### 7.4 The R-1 structural close (open)

Gated on §7.2 and on §7.3 reading zero.

**The constructor declaration channel.** `CtorMeta`'s field types are
materialised from the constructor *declaration's* scheme, so a polymorphic
product's field type is permanently a `Type::Var` that licenses a guarded RC
path at every use site. No frame monomorphisation closes this, and the census
cannot read zero while it stands.

> **Ruling.** A constructor's field types are an instantiation fact. `CtorField`
> carries a `ConcreteType`, making a residual field type unrepresentable.
> Materialisation substitutes the reference's concrete arguments into the
> declaration scheme through the published
> `cranelisp_types::ctor_field_types_at(table, ctor_key, args)`, which today has
> no consumer. Its `NotConcrete` refusal becomes a located refusal at the
> reference's span; `NotACtor` and `ParamArity` remain keying bugs.

`drop_glue::ctor_shapes` materialises per-constructor field types through the
same projection, keeping its cross-constructor agreement check as an explicit
precondition with its existing diagnostic (falsifier: a user type whose
constructors' result parameters disagree must still refuse with that message).
No `cranelisp-types` change is needed.

**The two fabrications that are the class.**

- `signature_heap_category`'s `Err(_) => HeapCategory::Mixed` becomes a located
  error, restoring the no-fallback rule to the retain side.
- `emit_heap_binding_decs`'s type-keyed shallow-dec arm (`fn_compiler.rs`) is
  **deleted**, not re-keyed to the frame (§2.6). `emit_typed_rc_dec` is then the
  sole release path with no fallback.

**The remaining narrowings, by site:**

| Site | Current source | Disposition |
|---|---|---|
| `drop_glue.rs`, Vec arm of `shape()`: `unwrap_or(ConcreteType::Int)` | live | located refusal |
| `vec_codegen::resolve_elem_inc_fn_ptr` and its `_into` twin: missing element type "assume `NeverHeap`" | live | located refusal |
| `vec_codegen::request_elem_dec_adapter`: missing element type | **delivered** — located refusal (`element_release_tests.rs`) | — |
| `compiler/context.rs`: `unwrap_or(Type::Int)` on the constructor field read | live | deleted by the channel ruling above |
| `fn_compiler.rs`: the dead `variable_types` `unwrap_or(Type::Int)` arm | **delivered** — absent from source | — |

The `("vec-len", 1)` value-position arm of `emit_vec_query_into` is live and
must share its siblings' refusal for an absent element type, never a local
default (§8 reject 6).

**Grade after the close:** structural (a `Concrete` entry requires a
witness-checked concrete scheme; `CtorField` cannot hold a residual; no fallback
arm exists), with the census as a permanently measured detector. §3.5's
falsifier remains the one asserted property.

### 7.5 Typecheck producer obligations

Faces 2, 3 and 5 close when typecheck stops handing codegen a type it has not
got: accessors and trait-method instances are monomorphised per concrete
instantiation, and the lenient view carries each node's real type with an
explicit, checked defaulting step for unconstrained parameters. The obligations
and their checks are
[non-concrete-producer-obligations.md](../typecheck/non-concrete-producer-obligations.md).
FIXME 0913 must not be closed by pinning annotations in tests or docs.

### 7.6 Decision-24 wrapper discharge follows realization (open)

The closure wrapper's `emit_d24_adaptation` (`control_flow/fn_as_value.rs`) emits
a guarded post-call dec for every `Mode::Borrowed` parameter. That is correct
only when the target body genuinely uses the borrowing ABI. A consuming Rust
extern shim discharges its argument itself under Decision 24, so the wrapper
discharges it a second time. Ordinary applied calls are unaffected; value
position and auto-curry take this path. The only-read string externs
(`str-len`, `str-eq`, `neq-string`, `starts-with?`, `ends-with?`, `contains?`)
are the affected population.

The repair is one target-effect classification derived from the same keyed
`Life`/`Realization` read used for dispatch, exhaustive with no wildcard:

| Target realization, declared parameter fact | Wrapper post-call action |
|---|---|
| `Body`, heap `Mode::Borrowed` | canonical typed `drop<T>` post-dec (the body borrowed and emitted no dec) |
| `Body`, `Mode::Owned` | none |
| any, `Mode::Copy` or non-heap | none |
| `ExternShim`, `ParamFlow::Consumed` | none, regardless of `Mode` |
| `ExternShim`, `ParamFlow::IntoResult` | none; result handling unchanged |
| `ExternShim`, `ParamFlow::Retained` | none (the safe direction) |
| `Dll`, `FacadeOf` | none; a future non-trivial convention needs its own explicit case |

- `ParamFlow` is read through `ModeSummary::param_flow`, never by indexing.
- The `Body + Borrowed` dec uses the parameter's concrete type and the canonical
  `drop<T>`; it does not preserve `heap::emit_rc_dec_guarded` as a wrapper-only
  release. A missing or non-concrete parameter type is the located refusal.
- Value-position wrappers and auto-curry consume one positional plan exactly
  once; a table-backed builtin reaching `emit_curry_target_call` goes through the
  keyed realization dispatch, not a name roster. The auto-curry wrapper remains
  its chain's Decision-24 adapter and never stacks a value wrapper.
- A closure wrapper always calls the shim's primary Decision-24 entry; a
  `borrowed_sibling` is a static Borrowed-call optimisation only.
- `string-identity` (`IntoResult`, `ResultMode::AliasOf(0)`) is the control: no
  post-dec and no result compensation. No `Mode`, `ParamFlow` or result
  declaration changes to accommodate this.

Surface effect: no public item, carrier, serialized field, slot, symbol,
signature, cache schema or ABI changes. The only emitted delta is removal of the
redundant post-call dec from affected extern wrapper bodies, under one scoped
attributed golden re-baseline; `Body` and `IntoResult` wrapper frames are
byte-identical controls.

### 7.7 Order

| Item | Depends on | Emission acceptance class |
|---|---|---|
| lifecycle disposition + cache-load arms | — | byte-identical |
| refusal frame | §7.1 | byte-identical (diagnostics only) |
| census | §7.1 | byte-identical, debug-profile only |
| structural close | §7.2; §7.3 reading zero; typecheck's face 2/3 obligations | census-gated; zero new refusals; scoped attributed re-baseline of the monomorphised accessor frames (e.g. `f4_sudoku` `Grid.cells`) |
| wrapper discharge | §7.1 | scoped attributed re-baseline of affected extern wrapper bodies only |

---

## 8. `/review` reject criteria

In addition to [transitive-drop-glue.md](transitive-drop-glue.md) §11:

1. **A new emission licence arm or release mechanism.** Every disposition reuses
   the canonical glue call, an existing runtime dispatch, or emits nothing.
2. **Fabricated concreteness** (R-2): a new `Err ⇒` default category, an
   `unwrap_or(ConcreteType::Int)`, a "refuse to own this type" exclusion, or
   defaulting a *constrained* type parameter.
3. **An RC operation on an uncategorised word**, however guarded. Citing the
   nullary threshold as a pointer test is the defect, not the mitigation.
4. **A frame-keyed release narrowing landed alone** (§2.6: +16 refusals, twice).
5. **A second glue identity home**, including an IO-specific payload releaser.
6. **A new `unwrap_or`/`unwrap_or_default` narrowing a `Type` or `ConcreteType`
   at any RC, glue or category seam**, including a per-arm default on the
   `vec-len` value-position arm.
7. **A refusal at span `0..0` or against a `$`-mangled subject** once §7.2 lands.
8. **`#[ignore]` on a leak this contract knowingly leaves.**
9. **A `_ =>` arm in the lifecycle disposition** (§7.1).
10. **A backend write to, read of, or call through the `Pure` glue word outside
    the four stamp sites**, a stamp that writes `1`, or a fifth stamp site (§5).
11. **A per-site constructor-name test for the `Pure` stamp**, or a stamp store
    not dominated by its tag compare, or a platform-return stamp selected by the
    callee's `DefKind` (§5.3, §5.5).
12. **A second backend offset expression for the glue word** — a bare `32` other
    than the pin, a per-site recomposition, or importing the platform constant
    (§5.5).
13. **A backend-side IO teardown walk** (§5.4).
14. **A census reachable in a release build** (§7.3).
15. **A name list, `DefKind::Primitive` proxy, module-name test or per-row branch
    for wrapper discharge**, deleting every `Borrowed` wrapper post-dec, an
    auto-curry-only path, a builtin bypass of the realization plan, a stacked
    adapter, or changing a declaration to accommodate it (§7.6).
16. **A golden re-baseline outside the items that declare one** (§7.7), or one
    taken without scoped attribution.

---

## 9. Unit-test design (open items)

Rows sit beside their production owner per the crate's sibling convention. The
delivered rows (0917, the IO arm, the `Pure` stamp and the platform-return tag
dispatch, the shared nullary guard) are in source and are not repeated.

| Submodule | Positive | Edge | Negative |
|---|---|---|---|
| lifecycle disposition (§7.1) | each `Concrete × Realization` arm lowers as tabled; `defined_symbols` equals the `Concrete × Body` projection | `FacadeOf` is a name-alias with no per-instance body | exhaustive, no `_ =>`; `Template` in value position and `Declared` at codegen are located refusals |
| `cache/serialize` (§7.1) | a legal restored entry loads | tombstones conserve | each legality violation is a `CacheStale` recompile, never an `assert!` |
| `error` frame (§7.2) | one prefix, real span, unmangled subject | a refusal inside a monomorphised instance renders the instantiation as types | no `0..0` from the glue registry; no `module/module/` doubling |
| `rc_emission::signature_heap_category` (§7.3, §7.4) | each concrete shape maps to its category; the census records frame partition and shape | a concrete sum with a nullary constructor is `Mixed` | both census legs; after the flip, a residual `Var` is a located error naming the frame and emits no RC op |
| `compiler/context` constructor materialisation (§7.4) | field types at a concrete instantiation come from the one types projection | a nullary constructor has zero fields; arity mismatch is a keying error | `CtorField` cannot hold a residual; a residual instantiation is a located refusal at the reference's span; no second field-type read |
| `vec_codegen` element inc pointer (§7.4) | a concrete element resolves its adapter | a scalar element needs none | a missing element type is a located refusal |
| `fn_as_value` wrapper discharge (§7.6) | `Body + Borrowed` emits one typed dec; `ExternShim + Consumed` emits none | `IntoResult` preserves `string-identity`; value position and auto-curry consume the same plan once | the synthetic consuming-extern and borrowing-`Body` CLIF pair discriminates a kind-blind deletion; no name classifier; no stacked adapter |
| category before provenance (§3.5) | — | — | no provenance-licensed RC emission is reachable without a preceding category gate |

E2e acceptance is `qa`'s.

---

## 10. Open and owned elsewhere

- **Converging the seam-by-seam category gates into one** (§3.5) — not
  scheduled; the falsifier cell is the standing detector.
- **A `Select` loser's severed fork-join.** A cancelled loser with an in-flight
  blocking `Par` bridge detaches its worker, so the join that publishes its
  branch reads never happens and the detached walk can race the root's teardown.
  Pre-existing and independent of the witness; `qa` intake, to be cured by
  restoring the join rather than adding an ownership channel (arch,
  [total-concreteness.md](../arch/total-concreteness.md) §3.4).
- **Widening the fn-return skip to the binding-indirection class** — a
  potential extension, not scheduled. It would remove a redundant inc/dec pair on
  `(defn f [v] (let [x 1] v))`. **Hazard:** the return path asserts the skipped
  variable is not a `Borrowed` parameter, and the wider class can reach one
  through a `let`. **Trigger:** a measured frame where the pair is worth a scoped
  re-baseline, with that assertion re-proved first. The three binding-root
  finders stay separate ([s122-closure.md](s122-closure.md) §5.1).
- **The §6.2.2 wrapper cap residual**, with its revisit trigger.

## 11. Cross-references

- [transitive-drop-glue.md](transitive-drop-glue.md) §1 (canonical glue), §4.1
  (the superseded I-CT record), §11 (the no-interim list this extends)
- [io-trampoline.md](io-trampoline.md) §1.1 — IO node layout
- [ownership-codegen.md](ownership-codegen.md) §4 — stack placement
- [s122-closure.md](s122-closure.md) — the current delivered selected slice
- [total-concreteness.md](../arch/total-concreteness.md) §3.2, §3.4, §3.5
- [symbol-table-lifecycle.md](../arch/symbol-table-lifecycle.md) §4, §5.5
- [safety-invariants.md](../arch/safety-invariants.md) §4 — R17, R18, R19
- [non-concrete-producer-obligations.md](../typecheck/non-concrete-producer-obligations.md)
- [int.md](../int/int.md) §9.1 — subject presentation
- [repl/spec/05-error-presentation.md](../../repl/spec/05-error-presentation.md) §5.5
