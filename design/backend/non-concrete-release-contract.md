# The non-concrete release contract

**Owner:** `design`, narrow-deployed to `cranelisp-backend`. **Subordinate to:**
[backend.md](backend.md).

**Status:** the adopted contract for how the backend licenses every RC
operation it emits, the disposition of each non-concrete face, and the open
backend work that completes it. It absorbed the S121 C4 visit design; that
visit's delivered bundles are recorded here as current mechanism and its open
bundles as §7. Source was re-verified on 2026-11-15, for §7 on 2026-11-16,
for §5.3 on 2026-11-17 at `1a3ab46e`, and for §4, §7.3, §7.4, §7.7 and §9 on
2026-11-18 at `1db7b1d8`. *When* a reference is
moved, duplicated or dropped is [uniform counting](uniform-counting.md), built
at S123 W2; this contract governs whether an RC operation may be emitted on a
value at all. §6 and §7.6 are retired with the provenance classification and
the entry-convention derivation.

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

> **Category, then counting, then emitter.** A seam asks the value's own
> concrete type for its `HeapCategory`; `NeverHeap` (and `Value`, until row D4
> retires it) emit nothing and the seam stops. Only then does the ownership plan's move, duplicate or drop
> apply. The plan never answers *whether* a reference exists.

As built, the plan's duplicates and drops pass through two helpers, the
duplicate emitter and `FnCompiler::emit_release`, and each gates on the value's
category first. The match seam ANDs its release with `scrut_is_heap`, and the
Vec seams take a Vec-typed operand. **Named falsifier:** an RC emission not
preceded by a category gate on the value's own type.

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
| **2** | Synthetic accessor of a generic product (F1) | Canonical glue after the frame is monomorphised per concrete instantiation | Producer obligation (typecheck), met: an accessor instance is minted at the demanded concrete instantiation, and the CEN-4 reading compiled `Accessor` frames with no record from a program (§7.3). The backend fallback arms retire in §7.4 step 2 |
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

Every `Pure` node is allocated on the RC heap. Stack placement and its
stack-placed `Pure` refusal were deleted at S124 B1
([ownership-codegen.md](ownership-codegen.md) §4), so no placement verdict
reaches a stamp site.

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

## 6. FIXME 0917 — the provenance classification

Retired at S123 W2 with §6.1–§6.4: no emission reads a value's provenance,
because every position consumes ([uniform counting](uniform-counting.md) §1).
One rule from it stays live.

#### 6.2.1 The constructor probe — one determinant, one read

A global reference to a constructor has a **two-state closed value shape**
(`CtorValueShape`): the value is the tag itself (zero fields), or its use mints
or moves a payload. The one producer is `CompileContext::ctor_meta_at`, the one
keyed constructor read, through `CtorMeta::value_shape`; the bare-tag lowering
(`literals::nullary_constructor_tag`) reads it. A second field-list read could
disagree with what a constructor carries, so none exists.

---

## 7. Open backend work

§7.3 and §7.4 deliver the end state of
[the S124 close](../arch/concrete-boundary-type.md#312-the-s124-close-no-rc-operation-on-a-word-without-a-category).
The census (§7.3) and close step 1 (§7.4) are built; close step 2 (§7.4) is
designed and licensed, not built. §7.1 and §7.2 are not on that path and stay
open; §7.6 is retired. None is accepted as residual. Order and dependencies
are §7.7. Source read for this section: `main` at `4b58ab93`, 2026-11-16;
§7.3, §7.4 and §7.7 again at `1db7b1d8`, 2026-11-18.

### 7.1 Consume the lifecycle exhaustively (partial)

The backend consumes `Life`/`Realization` at scattered sites; the target is one
disposition, exhaustive with no `_ =>` arm, so a state combination the backend
cannot lower is a compile error in this crate.

| State | Backend lowers | Refusal |
|---|---|---|
| `Concrete { Body { view } }` | the view, into the claimed slot. This projection **is** `defined_symbols()` | — |
| `Concrete { ExternShim }` | nothing; call sites dispatch through the shim's slot and consume every heap argument. The unproduced `borrowed_sibling` field leaves with S124 packet row D6, and with it the cache loader's sibling-slot validation arm and its `CacheStale` variant (row D9) | — |
| `Concrete { Dll }` | nothing; call sites are GOT-indirect against the manifest-order slot | — |
| `Concrete { FacadeOf { abi_name } }` | nothing per instance; the slot is the one hand-written body named by `abi_name`; no per-instance body or glue identity | — |
| `Inline` | inline lowering at concrete call sites; value position emits a span-keyed unit-local wrapper selected by `is_inline_primitive_at`, below the table | located error when the wrapper body has no arm for the name |
| `HostPromised` | nothing; by-name import | — |
| `Template` | nothing — not a codegen target | located refusal naming the symbol: no instantiation was demanded |
| `Declared` | nothing | located refusal: settlement did not run (a compiler-invariant breach) |
| `Broken { slot, error }` | nothing; no production path constructs it, and no trap stub exists to fill the slot ([ownership codegen](ownership-codegen.md) §8.1) | — |

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

**Status: built.** The heading's "(open)" stays only because other documents
cite its anchor.

A permanent census of every point at which codegen emits, or silently skips,
an RC operation on a word whose category it cannot name, and of every
constructor field read whose instantiation is not concrete. §7.4 adds a
refusal or deletes an arm only once the census measures zero traffic through
it. It is a developer instrument whose nouns R-4 forbids in user output, so it
is compiled into debug builds only (§8 reject 14). Built at S124 B2 and B2′
(`compiler/census.rs`; `1a3ab46e`, frame record `3ca6086e`).

**Record points — one per arm, the field read, and the frame.**

| Point | Where it is recorded | What one record means |
|---|---|---|
| Retain | `rc_emission::signature_heap_category`'s `Err` arm. Every categorisation passes through it: duplicates, `is_heap_type`, Vec elements, captures, dependent-spark and apply-site results | a residual type licensed as `Mixed` |
| Release | the shallow guarded decrement in `FnCompiler::emit_release` | a residual-typed value released without its glue. The release first asks `is_heap_type` (the §3.5 gate order), so each release record comes with one retain record for the same word |
| Absent | the two parameter-typing fallbacks, when they yield no type: a defn parameter whose selected scheme supplies none, and a lambda parameter whose `Lambda` node type is not a function type, after the body-derived type is also absent | a binder introduced untyped, which every later duplicate and drop of it then skips |
| Field | `CompileContext::ctor_field_types`, the match lowering's one field-type read, once per call; and its pattern-constructor read, when that read refuses a short declaration | a constructor's field types read at an instantiation of the class below |
| Frame | `census::Frame::of_target`, where the codegen target is selected and its partition assigned, once per target compiled | one frame compiled under the census, in its partition: the denominator a zero reading is read against |

**Field-read instantiation class.** Each field record carries one of three
classes, decided from the declaration and the scrutinee's type before any
substitution:

- **concrete** — the declaration has no parameters, or the scrutinee is an ADT
  carrying exactly as many arguments as the declaration has parameters, each
  convertible to `ConcreteType`;
- **residual** — the argument count matches and at least one argument is not
  concrete;
- **absent** — the declaration is parametric and the scrutinee is not an ADT
  carrying that many arguments, including no scrutinee type at all.

A declaration whose scheme supplies fewer field types than its field count is
**short**, and is recorded in the field record's shape. Step 1 made each of
these a refusal (§7.4), so a record in the residual or absent class or the
short shape is now a compile error at the same site. The drop-glue shape
builder reads field types only at concrete arguments it is given, and so has
no record point. Concrete records are counted in the tally only; the census
file receives a line for the residual and absent classes and the short shape.

**Which classes the match lowering can produce.** The match passes the field
read its scrutinee's counted type: the binder's recorded type when that is
concrete, otherwise the scrutinee node's type. Both are concrete by
construction, because a `MonoExpr` node carries a `ConcreteType`. So:

- **residual** cannot arise through the match lowering. Its fixture plants it
  at the field-read seam directly, where step 1 refuses it at the reference's
  span;
- **absent** arises only when the counted type is a node's placeholder — the
  `Int` a view builder writes for a type it does not have (safety register
  R18) — or an ADT carrying the wrong number of arguments. A residual binder
  falls through to that placeholder, which is why an accessor matching on its
  own residual parameter (family F1) lands in the absent class, not the
  residual one. No real codegen target has a residual parameter: a
  `Concrete` arm's scheme must be concrete (the types crate's arm
  validation), and a residual-parameter constructor or accessor is a slotless
  `Template`. In production, absent-class traffic therefore means a view node
  carrying the placeholder, which is typecheck's R-2 correction.

The absent arm is recorded where the absence is created, not at the early
returns of `emit_dup` and `emit_release`. A match-field binder is stored
untyped on purpose when its field owns no heap (`match_codegen::heap_field_type`),
so a count at the early return would include every scalar field. A capture
inherits its binder's type and creates no absence of its own.

**Key.** Each record carries the requesting frame's `CallableOrigin`
partition (`Ctor`, `Accessor`, `TraitMethod` or `Plain`), the point, the type
shape (bare `Var`; `ADT(<concrete>, [Var…])`; residual `Fn`; absent), for a
field record its instantiation class, and the frame's symbol. The partition is handed to the body compiler where the codegen
target is selected and is inherited by every inner compiler of that frame:
lambdas, spark thunks and wrappers. A minted instance carries its template's
origin, so an accessor or trait-method instance records in its template's
partition. No new carrier is needed
([the S124 close](../arch/concrete-boundary-type.md#312-the-s124-close-no-rc-operation-on-a-word-without-a-category)).

**Output.** In a debug build an in-process tally counts every record.
`CRANELISP_CATEGORY_CENSUS=<path>`, read once, additionally appends one line
per reported record to that file. A suite run therefore aggregates across every child
process it spawns without writing to any process's standard streams, which
tests observe. Every record point is host code, so emitted code is
byte-identical whether the variable is set or not.

**The frame record is the liveness signal.** The file is opened at its first
reported record, and every compiled target reports a frame record, so:

- a missing file means the census did not run, and the reading is void;
- a partition's zero is meaningful only against a non-zero frame count in that
  partition. A partition with no frames has a vacuous zero, whatever its
  record count.

Concrete field records stay in the tally only. They would show that the field
point executes, which its negative detection leg already proves, and they give
no denominator for a frame that contains no match.

**What the reading counts.** Records are made when a frame is compiled, not
when it runs:

- a frame restored from the object cache is not compiled and records nothing.
  A reading is valid only when no frame was restored from a cache written
  before the run, for example under `--no-cache` or from an empty cache. A
  restore inside the run is covered by the compilation that wrote it;
- with the cache on, a frame is compiled twice, once for the JIT and once for
  its cached object, and records twice. Counts are compilations, so attribute
  by frame symbol. The duplication does not change whether a count is zero;
- the population is the programs the suite compiles from source. A module
  test that builds a frame or node by hand is not a program, so its records
  are excluded from the reading: the census's own detection legs, step 1's
  refusal fixtures, and any other hand-built input. A record carries no test
  name, so each excluded record must be attributed to the named test that
  produced it, for example by running the module tests alone under the
  census and bisecting them. A record not attributed to a named test counts.

**Both detection legs, for each point, land in the instrument's change-set.**
The corpus traffic that proved the S119 scaffold is gone, so each leg is a
planted unit fixture through the production per-body path
(`test_support::probe_defn_clif` and its siblings), observed as a change in the
in-process tally:

- positive — a directly constructed frame plants the arm: a residual-typed
  parameter that is duplicated (retain) and dropped (release, recording one
  retain and one release), and a `Lambda` node whose type is not a function
  type, with an unused parameter (absent). For the field point: a match on a
  generic product whose scrutinee carries no arguments (absent), and a
  residual instantiation planted at the field-read seam (residual), which the
  match cannot produce. The no-arguments fixture records its field read and
  is then refused by the scrutinee's release, whose glue needs the arguments.
  It plants the point; it is not a program that reaches emission. Each records
  exactly once, in the expected partition, point, shape and class;
- negative — each fixture's concrete twin leaves the arm tallies and the
  residual and absent field classes unchanged; the field twin records once in
  the concrete class, which is also the proof that the point executes.

**Step 1's criterion** was zero field records in the residual and absent
classes and zero short shapes. The first reading (CEN-3, on the B2 tree) met
it, and step 1 landed directly after the census. The design had expected
family F1, `Grid.cells` among it, in that reading; the expectation was
refuted, because an accessor of a generic product is a template and each
instance a program demands is compiled at a concrete instantiation.

**Flip criterion for §7.4 step 2.** Across the full default suite and the
`spec_*` corpus there must be zero records from programs at **every** point
and in every partition, in a reading that:

- is valid under the cache condition above;
- carries frame records, showing a non-zero frame count in the `Plain`,
  `Accessor` and `TraitMethod` partitions. The `Ctor` partition may have no
  frames, because face 1 is closed by representation (§4);
- comes from a run in which the ACT-1034 cells pass. Before typecheck row T4
  (`3a2692e3`) those programs were refused before emission and contributed no
  `TraitMethod` traffic, so a `TraitMethod` frame count above zero is
  necessary but not sufficient;
- comes from a run whose every failing test traces to an open filing or an
  approved S124 row and fails on that row's own assertion: no untraced RED,
  in the root `AGENTS.md` §Testing sense of a genuine regression. The failing
  set need not equal the opening tree's, because S124 adds filed RED cells by
  design. The clause exists because an untraced failure can be a regression
  that stops frames compiling, which empties the population without
  producing a record.

**What the zero does not cover.** A filed RED cell whose program is refused
before emission compiles no frame for the refused definition, so its traffic
is outside the reading. This is accepted, not a gap in the criterion: after
step 2 an untyped binder in such a program is a located refusal, not a silent
skip, so the exposure is a compile error on a cell that is already RED, and
the census counts it when that program first compiles.

Step 2 refuses in every partition, so a `Plain` record is a legal program that
step 2 would break. The census reading zero is the criterion; a code reading
is not. The absent-arm records in `Plain` before W4 (600 in 39 frames on the
T4 tree) were ACT-1050's subject: the binary's bind-chain pass rewrote node
spans, so the inline `bind` continuation's `Lambda` node lost its function
type. That was corrected at `32e434dc` (W4), upstream of the backend.

**Met by CEN-4** (`dev`'s full run at `8667a868`, read by `qa` in the
[evidence delta](../../tests/plan/s124-evidence-delta.md) §14.5): every
partition compiled frames, no program produced a record, the ACT-1034 cells
passed, and no failing test lacked a filing. Step 2 is licensed. The two
records the run did contain are backend module fixtures, excluded under
*What the reading counts*; step 2's change-set adapts one of them (§7.4
step 2, *Fixtures*).

**After the close** the arms are gone and the record points become the located
refusals that replace them (§7.4 steps 1 and 2). The census keeps counting there, so a
producer regression shows as traffic in its partition as well as a compile
error. That is the permanently measured detector the close's grade relies on.

### 7.4 The R-1 structural close (open)

**Status: step 1 built, step 2 open.**

Two change-sets, each gated on its own §7.3 criterion: step 1 on zero
residual and absent field reads, step 2 on zero records at every point. Both
criteria are met.

**The refusal frame is not a precondition.** §7.2 (FIXME 0915) governs how a
refusal reads, and it carries past S124 by the user's ruling. Each step adds a
refusal only where the census measured zero traffic, so no suite program
reaches one. Each new refusal carries the span of the node or reference it
refuses, never `Span::SYNTHETIC`; the doubled prefix and the mangled subject
remain §7.2's. *Falsifier:* any suite program that reaches a refusal the close
added.

#### Step 1 — the constructor field channel (S124 packet row D1, built)

Built at `3deee350`, with the short-declaration correction `24c42430`. It
closed two defects of the hand-rolled substitution it replaced: a generic
product's field could reach classification as a `Type::Var` (unsubstituted
when the scrutinee carried no arguments, or defaulted to `Int` when the
scheme was short), and arguments were paired with type variables in order of
first appearance rather than with the declared parameters, so a binder could
record another parameter's type (ACT-1062, whose match and accessor legs
step 1 corrected).

> **Ruling.** A constructor's field types are an instantiation fact. Every read
> of field types that feeds classification, release or glue goes through one
> backend accessor that delegates to the published
> `cranelisp_types::ctor_field_types_at(table, ctor_key, args)` with the
> reference's concrete type arguments, and it yields `ConcreteType`s. Its
> `NotConcrete` refusal becomes a located refusal at the reference's span.
> `NotACtor`, `ParamArity` and `InstantiationMismatch` remain keying errors.

- **Readers.** The match lowering's field binders and
  `drop_glue::ctor_shapes`. `ctor_shapes` keeps its cross-constructor
  agreement check as an explicit precondition with its existing diagnostic
  (falsifier: a user type whose constructors' result parameters disagree must
  still refuse with that message).
- **A parametric constructor reached without type arguments is a keying
  error** (`ParamArity`), not a declaration read.
- **A short declaration builds no `CtorMeta`.** The keyed constructor read
  (`CompileContext::ctor_meta_at`) refuses it for every reader, never
  presenting a constructor with fewer fields. A reader with a reference
  locates the refusal there: the pattern read, which also records it as a
  field read (§7.3), and the constructor-application, constructor-value and
  bare-tag reads. The
  declaration-level read `constructor_metas`, whose one production reader is
  the trace descriptor baker, has no reference and refuses at
  `Span::SYNTHETIC`; locating it is §7.2's span obligation.
- **Declaration field types stay in `CtorMeta`** for two readers that feed no
  RC seam: the trace descriptor baker (`trace_codegen::build_adt_subst`) and the
  platform schema walk (`schema.rs`). Both substitute through the shared
  helper `schema::subst_for_ctor_fields`, which still pairs arguments by first
  appearance: the defect step 1 removed from the match, and ACT-1062's
  remaining backend reader (signal 11 on an out-of-order product under
  `trace`). The correction pairs each argument with the declaration's
  parameter in its position, as `ctor_field_types_at` does, once in the
  helper for both callers (Principle 7). The schema walk's output is hashed
  into the platform layout hash, so that change-set reports whether any
  platform-visible type mentions its parameters out of declaration order;
  if none does, the hash is unchanged. Neither reader can reach a category
  once step 2 lands, because the classifier accepts only a `ConcreteType`.

**Why step 1 preceded step 2.** Step 2 types every match field through step
1's accessor (the step 2 table), so it could not be built first.

#### Step 2 — binder types are concrete, and the arms are deleted

> **Ruling.** Every binder's recorded type in a compiled frame — a body binder,
> a scope-chain slot and a capture — is a `ConcreteType`, never an optional
> `Type`. The RC entry points (`emit_dup`, `emit_release`, `emit_typed_rc_dec`,
> `is_heap_type` and every categorisation) take `&ConcreteType` and call
> `HeapCategory::classify` directly.

Each source is already concrete, so the representation records what it is
handed:

| Binder | Type source |
|---|---|
| defn parameter | the selected arm's concrete scheme, converted once where the codegen target is selected. A scheme that is not a function type for a defn with parameters is a located invariant error |
| lambda parameter | the `Lambda` node's `ConcreteType::Fn`. A `Lambda` node whose type is not a function type is a located producer refusal |
| `let` binder | the initializer node's type |
| match variable | the scrutinee's type |
| match field | step 1's accessor, scalar fields included. "Untyped" no longer encodes "owns no heap" |
| capture | the denoted binder's type. A capture that denotes nothing is the existing hard error for a missing binder ([backend.md](backend.md) §2) |
| par-bind result, forced dependency | the node types they use today |

`derive_param_type_from_body` is deleted with its two uses: an occurrence is
not an admissible source of a parameter's type
([uniform counting](uniform-counting.md) §3.4 item 1). `counted_type` reads the
binder's type for an owned or captured occurrence and the node's type
otherwise, with no concreteness filter.

The three arms then have nothing to match and are **deleted, not re-keyed**
(§2.6):

1. **Retain:** `signature_heap_category` and its `Err ⇒ Mixed` arm. Its input
   can no longer fail to convert.
2. **Release:** the shallow guarded decrement in `FnCompiler::emit_release`.
   `emit_typed_rc_dec` is the only release path.
3. **Absent:** the `ty: None` early returns of `emit_dup` and `emit_release`.

`Type` remains in the backend only for declaration facts read for layout and
display (step 1), for trace discovery's slotted signatures, and at the
conversion points above. None of these reaches a category.

**The remaining narrowings, by site:**

| Site | Current source | Disposition |
|---|---|---|
| `drop_glue.rs`, Vec arm of `shape()`: `unwrap_or(ConcreteType::Int)` | live | located refusal |
| `vec_codegen::resolve_elem_inc_fn_ptr` and its `_into` twin: missing element type "assume `NeverHeap`" | live | located refusal |
| `vec_codegen::request_elem_dec_adapter`: missing element type | **delivered** — located refusal (`element_release_tests.rs`) | — |
| `compiler/context.rs`: `unwrap_or(Type::Int)` on the constructor field read | **delivered** — deleted by step 1 | — |
| `fn_compiler.rs`: the dead `variable_types` `unwrap_or(Type::Int)` arm | **delivered** — absent from source | — |

With concrete Vec types an element type is missing only for a `Vec` carrying no
argument, which is a malformed `ConcreteType`. The `("vec-len", 1)`
value-position arm of `emit_vec_query_into` must share its siblings' refusal,
never a local default (§8 reject 6).

**Emission acceptance:** step 2 is byte-identical. Every site it changes was
measured at zero traffic, and every other binder records the type it already
used. A non-empty golden diff from step 2 is traffic the census missed. It
contributes zero new refusals.

**What the representation cannot see.** A concrete but wrong type: the
lenient builders' `Int` placeholder on synthetic-body nodes (safety register
R18, instance 3) or a defaulted *constrained* parameter. That is a fabrication
by the producer (R-2), typecheck's to correct; no backend instrument observes
it.

**Fixtures.** A module test that builds a frame by hand in a shape no
producer emits is malformed input once step 2 lands, and is refused like a
producer's. Step 2's change-set gives each such fixture its producer's shape
and leaves its assertion unchanged. The one known instance is
`compiler::control_flow::lambda::tests::lambda_returning_its_capture_hands_the_caller_a_live_reference`,
whose `Lambda` node carries no type: it gets a function-typed node. It is the
source of CEN-4's one absent-arm record, so after the change the module tests
alone under the census produce no arm record outside the census's own legs.
Step 1's short-declaration
negative keeps its record: it is a refusal fixture, and its record is the
refusal's census line.

**Grade after the close:** structural for the three arms and the field
channel. No RC entry point accepts a value without a concrete type, a
`Concrete` entry requires a witness-checked concrete scheme, and no fallback
arm exists. The census is the permanently measured detector. §3.5's falsifier
remains the one asserted property, and a wrong concrete type is R18's.

**Cost.** Step 2 changes the binder record and the RC entry points across the
body compiler's ownership stratum, which carries the crate's largest review
cost ([backend.md](backend.md) §3). It migrates callee-first: change the record
and the entry points' parameter type, and the broken build is the checklist.

### 7.5 Typecheck producer obligations

Faces 2, 3 and 5 close when typecheck stops handing codegen a type it has not
got: accessors and trait-method instances are monomorphised per concrete
instantiation, and the lenient view carries each node's real type with an
explicit, checked defaulting step for unconstrained parameters. The obligations
and their checks are
[non-concrete-producer-obligations.md](../typecheck/non-concrete-producer-obligations.md).
FIXME 0913 must not be closed by pinning annotations in tests or docs.

### 7.6 The entry convention is derived once, from realization

Retired at S123 W2. Every call position consumes its arguments, so no entry
convention is derived and no declared `Mode` or `ParamFlow` reaches emission
([uniform counting](uniform-counting.md) §1, §5). An extern primary entry
consumes every heap argument
([BC §4a invariant 8](../arch/bounded-contexts.md#4a-primitives-cratescranelisp-primitives));
the declaration corrections ACT-0974 made are primitives'.

### 7.7 Order

The backend change-sets of the S124 close, in order. Landed: stack-placement
retirement with row D5 (`b0f48914`, `8f44040e`), the census (`1a3ab46e`) and
its frame record (`3ca6086e`), and close step 1 (`3deee350`, `24c42430`). The
producer corrections the zero read waited on landed on other surfaces: typecheck
row T4 for ACT-1034 (`3a2692e3`) and ACT-1050's in the binary (`32e434dc`).
The zero read is CEN-4 (§7.3).

| # | Change-set | Depends on | Emission acceptance class |
|---|---|---|---|
| 4 | Close step 2: concrete binder types, the three arms deleted, the remaining narrowings, the hand-built fixture adapted (§7.4) | the zero read, met | byte-identical; zero new refusals |
| 5 | Value-flattening retirement, row D4 ([ownership codegen](ownership-codegen.md) §7) | 4 | attributed re-baseline; `CACHE_SCHEMA_VERSION` bump |

The lifecycle disposition with its cache-load arms (§7.1) and the refusal frame
(§7.2) are not on this path. They stay open, byte-identical when they land.

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
14. **A census reachable in a release build** (§7.3), or one that writes to a
    process's standard streams.
15. **A borrowing position, or an RC action selected by a declared `Mode` or
    `ParamFlow`** ([uniform counting](uniform-counting.md) §1).
16. **A golden re-baseline outside the items that declare one** (§7.7), or one
    taken without scoped attribution.
17. **After §7.4 step 2: an optional or `Type`-typed binder record or RC entry
    point**, a parameter type read off an occurrence, or any field-type read
    for classification, release or glue that does not go through the step 1
    accessor.

---

## 9. Unit-test design (open items)

Rows sit beside their production owner per the crate's sibling convention. The
delivered rows (the IO arm, the `Pure` stamp and the platform-return tag
dispatch, the shared nullary guard, the census with its frame record, and
step 1's field channel) are in source and are not repeated.

| Submodule | Positive | Edge | Negative |
|---|---|---|---|
| lifecycle disposition (§7.1) | each `Concrete × Realization` arm lowers as tabled; `defined_symbols` equals the `Concrete × Body` projection | `FacadeOf` is a name-alias with no per-instance body | exhaustive, no `_ =>`; `Template` in value position and `Declared` at codegen are located refusals |
| `cache/serialize` (§7.1) | a legal restored entry loads | tombstones conserve | each legality violation is a `CacheStale` recompile, never an `assert!` |
| `error` frame (§7.2) | one prefix, real span, unmangled subject | a refusal inside a monomorphised instance renders the instantiation as types | no `0..0` from the glue registry; no `module/module/` doubling |
| binder types (§7.4 step 2) | every binder kind records its source's `ConcreteType` (the step 2 table) | an unused heap parameter of a defn and of a lambda is released at introduction | a `Lambda` node whose type is not a function type is a located refusal; a defn with parameters and a non-function scheme is a located invariant error |
| census after step 2 (§7.3) | where step 2 replaces an arm with a located refusal, the point keeps recording there and its planted fixture asserts the refusal and one record in its partition | a point step 2 makes unconstructable loses its planted fixture with its arm | each concrete twin is neither refused nor recorded |
| `vec_codegen` element inc pointer (§7.4) | a concrete element resolves its adapter | a scalar element needs none | a missing element type is a located refusal |
| category before counting (§3.5) | — | — | no RC emission is reachable without a preceding category gate |

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

## 11. Cross-references

- [transitive-drop-glue.md](transitive-drop-glue.md) §1 (canonical glue), §4.1
  (the superseded I-CT record), §11 (the no-interim list this extends)
- [io-trampoline.md](io-trampoline.md) §1.1 — IO node layout
- [ownership-codegen.md](ownership-codegen.md) §4 — stack placement, retired
- [total-concreteness.md](../arch/total-concreteness.md) §3.2, §3.4, §3.5
- [symbol-table-lifecycle.md](../arch/symbol-table-lifecycle.md) §4, §5.5
- [safety-invariants.md](../arch/safety-invariants.md) §4 — R17, R18, R19
- [non-concrete-producer-obligations.md](../typecheck/non-concrete-producer-obligations.md)
- [int.md](../int/int.md) §9.1 — subject presentation
- [repl/spec/05-error-presentation.md](../../repl/spec/05-error-presentation.md) §5.5
