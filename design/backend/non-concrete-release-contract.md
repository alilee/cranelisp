# The non-concrete release contract

**Status:** NORMATIVE RULING — authored S119 Phase 3, `/design`(backend), Spine 1.
Measured before binding (§2); the measurement record is part of the ruling.
**Subordinate to:** `backend.md`.
**Supersedes in scope:** `transitive-drop-glue.md` §4.1, which ruled one face of
this class ("the ONE sanctioned non-concrete release site") on a premise this
document's measurement falsifies. §4.1 survives as the *record* of face 1's
history and defers here for its disposition.
**Architecture inputs:** `design/arch/concrete-boundary-type.md` §3.1.1 (the
signature-driven codegen target; template-path `Err` classifies `Mixed`);
`design/arch/safety-invariants.md` §4 R-register + Principle 25;
`design/arch/ownership-inference.md` §2.1 (monotone soundness), §3.1 (mode
vectors on statically-resolved calls).
**Carries:** FIXMEs 0903, 0907, 0916, 0917, 0891, 0913 (producer face), 0915
(the refusal's quality bar), 0906 (rider).

---

## 1. The question, and why it has never been answered

Backend releases a heap value by calling the canonical per-concrete-type drop
glue (`transitive-drop-glue.md` §1). That contract has one precondition:
**codegen can name the value's concrete type.** The stratum has never stated
what happens when it cannot, and five places hit the gap, each behaving
differently. Two of them are memory-unsafe; one is a hard refusal with no legal
re-spelling; two leak silently.

This document states the contract, assigns every face exactly one disposition,
and binds the *producers* that hand backend a non-concrete frame.

The ruling rests on one fact that this window measured and that no prior
document states:

> **A word whose static type is a residual type variable has no heap category.
> It may hold a heap pointer, a bare nullary tag, or a raw scalar. The
> `NULLARY_TAG_THRESHOLD` guard discriminates tags from pointers; it cannot
> discriminate scalars from pointers. Therefore no RC operation — inc or dec,
> guarded or not — is legal on such a word, and no shallow release of it is
> "merely a leak".**

Everything below follows from that sentence.

---

## 2. The measurement record (S119 Phase 3, `/design`(backend))

A ruling that has not survived the corpus does not bind (`sprints/SPRINT.md`
§Sequencing item 1; the S118 §4.1 falsification is the precedent). The
measurement ran **inside** this design window, on the Phase-3 tree at
`5520186d` + concurrent design-only edits, with a throwaway instrumentation
scaffold that was reverted before authoring (backend tree byte-identical to
`HEAD`, verified).

### 2.1 Baseline

`cargo nextest run --no-fail-fast`: **5,660 run / 5,640 passed / 20 failed /
1 skipped.** Reconciled name-for-name against `SPRINT.md` §Baseline: 0907×7,
0917×3, 0867×3, 0863×2, 0868/0869×2, 0916×1, 0913×1, 0694×1. The 21st cell —
the `nullary_return_dispatch_method_only_import` 0694 flap member — was **green
on this run**, consistent with its flap classification. **No untraced RED.**

### 2.2 Census A — the release seam (`emit_heap_binding_decs`)

Every admission of the type-keyed non-concrete arm, recorded with its seam,
frame and type. **2,497 admissions across the whole suite.**

| Partition | Count |
|---|---:|
| `pop_scope_with_cleanup`, parameter frame (`scope_stack.len() == 1`) | **2,497 (100%)** |
| `flush_let_scopes_before_tail_jump` | **0** |
| `flush_superseded_heap_params_before_tail_jump` | **0** |
| …of which the frame IS a ctor template (`MonoExpr::ConstrADT` body) | 2,216 |
| …of which it is NOT | **281** |

Two findings, both load-bearing:

1. **Neither tail-jump flush ever admits.** §4.1's "the exception must stay
   unreachable from the two flushes" is not merely a rule to enforce — it is
   already a measured fact, and the negative cell 0903 held back
   (`the_admission_is_unreachable_from_the_tail_jump_flush_neg`) pins a
   property that holds at HEAD.
2. **The 281 escapees are exactly two families, and nothing else.** Every one
   is a *signature-driven, compiled-once-per-declaration* frame:

| Family | Frame shape | Parameter type shape | Examples measured |
|---|---|---|---|
| **F1 — synthetic field accessor** of a generic / undeclared-field product | `Type.field` | `ADT(<concrete FQ>, [Var…])` | `Grid.cells` (×164 across `program`/`grid`/`f4`/`user`), `Box.v`, `Box.val`, `Pair.first`, `Pair.second`, `Pair2.x`, `Pair2.y`, `Pz.v`, `Bx.val`, `Box.cells`, `Pair.fst`, `Pair.snd` |
| **F2 — generic trait-method instance** | `Trait.method$Type` | `Fn([Var…], Var)` or `ADT(<concrete FQ>, [Var…])` | `Functor.fmap$primitives/Option`, `Functor.fmap$user/Box`, `Functor.fmap$m/Option`, `Functor.fmap$30-parallel-map-reduce/Pair`, `Functor.fmap$26-functor/Option` |

**No escapee has a bare `Type::Var` as the released binding's own type at this
seam.** The outer type constructor is always known (a named ADT, or `Fn`); only
its *arguments* are residual. That is why the shallow dec is category-correct on
the outer word and wrong only in the field-discharge depth — i.e. at this seam
the escapees leak, they do not crash.

### 2.3 Census B — the retain seam (`signature_heap_category`'s `Err ⇒ Mixed`)

This is the seam no prior document names, and it is where the memory-unsafety
lives. `signature_heap_category` is consulted at **~25 emission sites**; its
`Err(_) => HeapCategory::Mixed` arm is the **single** point at which a residual
type acquires an RC licence. **5,499 licences across the suite:**

| Type shape at the licence | ctor-template frame | other frame | total |
|---|---:|---:|---:|
| **bare `Type::Var`** (no category exists) | 3,108 | **538** | 3,646 |
| `ADT(<concrete>, [Var…])` (outer category known) | 1,296 | 480 | 1,776 |
| `Fn(…)` residual (always heap) | 20 | 55 | 75 |

The 3,646 bare-`Var` licences are the class's memory-unsafety surface. The 538
in non-ctor-template frames are the F1/F2 frames again (`Box.v` ×116,
`Grid.cells` ×198, `Functor.fmap$…` ×40+, `Pair2.x/y`, `Box.val`); the 3,108 in
ctor-template frames are I-CT's *inc* half (`List.Cons` ×1,272,
`Maybe.Some` ×222, `Option.Some` ×172, `Box` ×140, …).

### 2.4 New finding — family F1 is memory-unsafe, not merely leaky

0903 and 0916 record F1 as a *silent leak* and F2 as leak-plus-wild-write. That
asymmetry is false. Four-line free-standing repro, `PrimitivesOnly`,
`--run --no-cache`:

```lisp
(import [primitives [IO Pure]])
(deftype (Bx a) [:a v])
(defn get [b] (v b))
(defn main [] (Pure (get (Bx 1024))))
```

| payload | result |
|---:|---|
| 100 | exit 100 (correct) |
| **1023** | exit 255 (correct — `1023 mod 256`) |
| **1024** | **SIGSEGV (139)** |
| 5000 | **SIGSEGV (139)** |

The `NULLARY_TAG_THRESHOLD` boundary exactly, on the *first* call — the same
1023/1024 boundary `/qa` measured for F2 (0916), on a different family, with no
trait and no HKT in sight. CLIF of the accessor makes the mechanism unarguable:

```clif
function %Bx.v(i64) -> i64 system_v {
block6:
    v6 = load.i64 notrap aligned v1+24      ; the field — static type Var(0)
    v7 = iconst.i64 1024
    v8 = icmp ult v6, v7
    brif v8, block7, block8
block8:
    v9  = iadd_imm.i64 v6, 8
    v11 = atomic_rmw.i64 add v9, v10        ; WILD ATOMIC WRITE at scalar+8
    jump block7
...
block2(v2: i64):                            ; the release half, on `self`
    v18 = icmp.i64 ult v1, 1024
    brif v18, block9, block10
block10:
    v21 = atomic_rmw.i64 sub v19, v20
    v22 = icmp eq v21, v20
    brif v22, block11, block9
block11:
    fence
    v23 = call fn1(v1)                      ; SHALLOW dealloc — no field discharge
```

One frame, both faces: a wild atomic write on the extracted field (census B,
bare `Var`) and a shallow field-discharge-free dealloc of `self` (census A,
`ADT(_, [Var])`).

**Consequence for the ruling:** F1 and F2 are one severity, not two. `/dev`
owes 0916's title correction *and* a severity correction on 0903's family 1.

### 2.5 The ctor template's own licence carries the same shape

Census B shows 3,108 bare-`Var` licences inside ctor-template frames, and
`%Bx.MkBx`'s CLIF carries the identical `icmp ult v1, 1024` → `atomic_rmw add
v1+8` prologue plus a matching guarded sub whose last-ref branch calls
`dealloc(v1)`. **I-CT does not license those instructions.** I-CT
(`transitive-drop-glue.md` §4.1) proves that the *reference count* balances; it
says nothing about whether the word is a reference at all, and its "ONE runtime
predicate" exactness argument is precisely the argument that both halves are
wild together.

Measured mitigation, recorded honestly: no corpus execution of a ctor-template
*body* was observed. `(defn ap [f x] (f x))` + `(ap MkBx 5000)` returns the
correct value with no fault, because the ctor-as-value path mints a wrapper that
lowers the construction at the concrete type; the template `Def`'s own body is a
compiled-but-uncalled artifact on every path probed. **That is a reachability
observation, not a soundness argument**, and §5.1 turns it into a named
obligation rather than a licence.

### 2.6 Frame-key falsification, re-run at S119 HEAD

The 0903 paste (frame-keyed admission, verdict threaded to the shared body, both
flushes rejecting) was applied and measured, as the dispatch required:

| Run | Command | Result |
|---|---|---|
| baseline | `cargo nextest run --no-fail-fast -E 'binary(/^spec_/)'` | 893 run, **8** failed |
| ruled frame key | same | 893 run, **24** failed |

**+16 hard `CodegenError` refusals — reproducing the S118 falsification exactly,
one sprint later, on a tree that has moved.** The refusals are the F1 and F2
frames of §2.2. The narrowing is confirmed unlandable on its own, and the census
explains why in one line: the frame key admits 2,216 of 2,497 and refuses the
other 281, but the 281 are legal programs whose *producer* handed backend a
frame it cannot compile.

---

## 3. The contract

### 3.1 Rule R-1 — category before operation

> No RC operation (inc or dec, guarded or unguarded, at any seam) may be emitted
> on a word whose **heap category** codegen cannot name from the word's own
> static type.
>
> `HeapCategory::Mixed` is a *nameable* category: "bare nullary tag or heap
> pointer", derivable only from a **concrete** sum type's own constructor set.
> A residual type variable is not `Mixed`; it is the **absence** of a category.

The one seam that violates R-1 today is `signature_heap_category`'s
`Err(_) => HeapCategory::Mixed` arm (`rc_emission.rs:486-495`). It is the sole
producer of every wild write in §2.4 and §2.5, and every one of the 3,646
bare-`Var` licences in census B flows through it.

### 3.2 Rule R-2 — no fabricated concreteness (binds producers, including backend)

> No component may present a downstream gate with a type, category, shape or
> mode **more concrete than what it actually knows**, in order to pass a gate
> that would otherwise refuse. A gate that cannot be satisfied is a **producer
> obligation**, never a licence to invent the missing fact.

Three measured instances, in two crates:

| Fabrication | Home | Invents | Consequence |
|---|---|---|---|
| `Err(_) => HeapCategory::Mixed` | backend `rc_emission.rs:493` | a heap category | memory-unsafe (§2.4/§2.5) |
| the type-keyed shallow-dec arm | backend `fn_compiler.rs:1287` | a release licence | leak (§2.2) |
| `ConcreteType::Int` for a residual result root | typecheck `MonoExpr::lenient_from_expr` | a concrete type | leak (0913) |

R-2 is the generalisation of Principle 25 ("Narrowing carries its check") to the
*type* channel: a component that narrows an unknown to a workable value must
carry the check that the narrowing is legal, and none of the three do.

### 3.3 Rule R-3 — a non-concrete frame is not a legal codegen target

> A frame whose parameter or result types are not fully concrete cannot emit
> correct release code, by **any** disposition available to it. The pipeline
> must present backend with concrete frames; where it does not, the defect is
> the frame's existence, not backend's handling of it.

R-3 is not a preference. §4.3 proves it: for a generic trait-method instance,
counting the residual word crashes on scalars and not counting it double-frees
on duplication, and no third behaviour is expressible from inside the frame.

### 3.4 Rule R-4 — the refusal must be actionable

> Where the contract's disposition is a located refusal, the diagnostic MUST
> name a real source span, a subject the user can look up, and one category
> prefix. A refusal reported at span `0..0` against a `$`-mangled internal
> instance name (`user/user/then$primitives/IO$Int+primitives/IO$Int`) is not a
> located refusal; it is a leak of the compiler's call structure and does not
> discharge this contract.

This is FIXME 0915, folded in as this contract's quality bar rather than left as
an adjacent cosmetic rider: "located refusal the user can act on" is one of the
four dispositions, and 0915 is the measurement that today's refusals do not meet
it. `repl/spec.md` §5.5 is the normative surface; the backend-side obligation is
in §5.5 below.

---

## 4. The five-face disposition table

Every face gets **exactly one** disposition. The table is total over the
measured class (§2.2 + §2.3): faces 1–3 are the whole of censuses A and B, face
4 is the `ctor_shapes` identity refusal, face 5 is the producer face.

| # | Face | Today | **Disposition** | Mechanism | Closes |
|---|---|---|---|---|---|
| **1** | Ctor template's own parameter (`ConstrADT` body, residual field param) | I-CT-licensed guarded inc + shallow guarded dec; **the inc is a wild write on a scalar payload** (§2.5) | **Canonical glue, at the frame that can name the type** — the template frame emits *nothing* on a residual parameter; the Decision-24 consuming transfer is already correct without the pair | delete the inc/dec pair under R-1; §4.1 + I-CT + its standing obligation **retire** | 0891, §4.1's `/review` reject criterion |
| **2** | Synthetic accessor of a generic / undeclared-field product (F1) | shallow field-discharge-free dealloc of `self` **plus** a wild atomic write on the extracted field (§2.4) | **Canonical glue, after the frame is monomorphised** — the accessor `Def` joins ordinary monomorphisation, keyed on the full concrete instantiation | remove the compile-once-per-declaration exemption (producer obligation, §5.2) | 0903 family 1; the `f4_sudoku.clif::user::Grid.cells` static re-baseline |
| **3** | Generic trait-method instance (F2) | shallow dealloc of both params **plus** a wild atomic write on the residual payload | **Canonical glue, after the frame is monomorphised** — the instance mangle widens from the type *constructor* to the full concrete instantiation | same mechanism as face 2 (producer obligation, §5.2) | 0903 family 2, **0916** ×1 |
| **4** | IO's existential `Bind` | hard refusal at `drop_glue.rs::ctor_shapes` (:497-505); no legal re-spelling exists | **Runtime-directed teardown** — the registry classifies `primitives/IO` as runtime-owned and emits a call to the intrinsics tag-walker; backend contributes only the one field the existential does not hide (`Pure`'s payload at the concrete arg) | `consume_io_tree`'s existing tag-directed walk, split at the dec (§5.3) | **0907** ×7 |
| **5** | Typecheck's lenient-view result root | a fabricated `ConcreteType::Int` unhooks glue entirely | **Canonical glue, after the producer stops fabricating** — the view carries the node's real type; unconstrained residual parameters are *defaulted*, explicitly and checkably, never replaced | producer obligation on typecheck (§5.4) | **0913** ×1 |

**Face 0917 is not in this table, deliberately.** 0917 is a distinct axis —
concrete types throughout, no residual anything — and folding it into the class
would be the framing error this ruling exists to fix. It is ruled separately in
§6.

### 4.1 Why face 1's pair deletes rather than survives

`transitive-drop-glue.md` §4.1 rejected "delete the pair" (its option (b)) on
two grounds, both of which the measurement removes:

- *"it needs a template-shaped special case at TWO independent seams."* It needs
  **no** template-shaped special case at all. R-1 is category-shaped, not
  frame-shaped: both seams already consult `signature_heap_category`, and both
  stop emitting for the same reason, in the same one-line change to that
  function's `Err` arm. The mechanism count goes **down** by one exception, not
  up by two special cases.
- *"it converts a branch that is behaviour-identical to pre-migration HEAD into
  an emission change buying two guarded branches per constructor."* The branch
  is **not** behaviour-identical: on a scalar payload ≥ 1024 it is two wild
  atomic writes and a wild `dealloc` (§2.5). Deleting it is the memory-safety
  fix, and **Complexity has a budget** now cuts the other way.

Soundness of the deletion, stated as the invariant that replaces I-CT:

> **I-CT′.** A ctor template's body is straight-line and its only effect is to
> move each parameter word into the box it returns. Under the Decision-24
> consuming convention the caller has already transferred one reference per
> argument; storing that word into the returned box transfers it to the box.
> The frame therefore owes neither a retain nor a release, for *any* parameter
> type — concrete or residual. The inc/dec pair was always redundant; it was
> only ever safe because the pair cancelled, and it is only ever unsafe because
> the pair's two halves are wild together.

I-CT′ is strictly simpler than I-CT: it needs no runtime-predicate-sharing
argument, no publication argument, and no standing obligation about `Borrowed`
modes reaching ctor templates — because there is no pair left to unbalance.

### 4.2 Why faces 2 and 3 are one face wearing two names

Census A and census B put F1 and F2 in the same two rows with the same two type
shapes and the same two seams. §2.4 shows the same 1023/1024 boundary on both.
`concrete-boundary-type.md` §3.1.1 already pairs the ctor and accessor signature
paths in one sentence. The only structural difference is *which* producer
exempted the frame from monomorphisation — `adt.rs`'s accessor synthesis for F1,
the trait-instance mangle for F2 — and the disposition is identical.

Their disposition is therefore stated once: **stop exempting them.** The
compiler already monomorphises ordinary generic functions; the census's own
frame list carries `ct/ap$Fn(Int;ct/Bx$Int)+Int` next to `Bx.v`. F1 and F2 are
not a capability the compiler lacks — they are two frames it declines to apply
an existing capability to.

### 4.3 The proof that no in-frame disposition exists (R-3)

This is the load-bearing negative result, and it is why "sanction a wider frame
set" (0903's cheapest candidate) is rejected rather than costed.

Take `(impl (Functor Option) (defn fmap [g o] (match o [None None (Some x) (Some (g x))])))`
compiled once for `primitives/Option`, with `x : Var`.

| In-frame policy | Scalar payload (`(Some 1024)`) | Heap payload (`(Some "s")`) | Duplicating arm (`(Pair x x)`) |
|---|---|---|---|
| **Count it** (today) | wild atomic write → SIGSEGV | correct | correct |
| **Do not count it** | correct | leak (outer shallow-freed, payload stranded) | **two boxes, one count → UAF** |
| **Runtime-discover it** | impossible — a raw scalar carries no header; R15 (header type-word) is rejected architecture | | |

Every column has a failing row, and the failures are on *different* axes, so no
combination of in-frame tests separates them. The missing fact — the payload's
category — exists only at the call site. **Monomorphisation is not one option
among several; it is the only sound one.** That is R-3.

### 4.4 Why face 4 is genuinely different, and genuinely runtime-directed

The IO face is not a residual-type face. `IO Int` **is** concrete; the failure is
in glue *derivation*: `ctor_shapes` builds one substitution over all of a type's
constructors and hard-errors when two disagree (`drop_glue.rs:497-505`), and
`Bind`'s manual seed (`src/bootstrap.rs:767-783`) uses fresh `bind_a`/`bind_b`
precisely because HM cannot express the existential. Per-ctor substitution does
not rescue it: `Bind`'s `inner: IO b` and `cont: Fn [b] (IO a)` keep `Var(bind_b)`
free by construction.

But the existential *is* discoverable dynamically, and — uniquely in this class —
**without a header type-word**, because the two things that would need one are
already self-describing:

- an IO node carries a **tag**, and `cranelisp-intrinsics::consume_io_tree`
  already walks every tag (`Pure`/`Effect`/`Bind`/`Par`/`EffectPoll`/`Select`),
  recursing into `Bind`'s inner tree and releasing `Par`/`Select` branch sets
  through `free_io_branches`;
- `Bind`'s continuation is a **closure**, and a closure carries its own
  `DROP_GLUE_PTR` at offset 24 — the `transitive-drop-glue.md` §1.1 M5
  runtime dispatch this design already sanctions as a standing exception.

So face 4's disposition consumes two mechanisms that already exist and adds
none. This is why "runtime-directed teardown" is available here and nowhere else
in the table: for faces 1–3 the unknown word may be a raw scalar with no runtime
self-description at all.

**The one field the runtime must not own.** `Pure`'s payload has type `a`, which
*is* determined by the concrete `IO T` the release is keyed on — and
`consume_io_tree`'s `IO_TAG_PURE` arm deliberately leaves it alone ("the
trampoline returns the payload's ownership to the caller",
`crates/cranelisp-intrinsics/src/drop.rs:340-344,395-399`). So the split is:

> **Backend owns what only the type knows; the runtime owns what only the value
> knows.** `drop<IO T>` decrements; on last reference it discharges a
> `Pure`-tagged payload by calling `drop<T>` — the ordinary canonical glue for
> `T`, no new identity — and then hands the node to the intrinsics tag-walker
> for the structural teardown and the deallocation.

§5.3 states the exact shape and the one intrinsics entry point it needs.

**The named residual, recorded rather than hidden.** A `Pure` node *nested inside
an unrun `Bind` sub-tree* has payload type `b` — the existential — which neither
side can name: backend does not have it, and the runtime sees an opaque word. Its
payload is not discharged. This is a **bounded leak on unrun IO trees only**, and
it is a strict improvement on today's hard refusal, but it is a leak and §6.3
gives it a guard rather than silence. R-2 forbids papering it over with a
fabricated `b`.

### 4.5 Why 0907's "admission exclusion" option is rejected

0907 offers three directions; the third — `HeapCategory`/registry refuses to own
IO, restoring the S116-era behaviour — restores compilation and **restores the
silent leak**. Weighed as the FIXME's own text and `/stdlib`'s appendix demand:

- it is the option that makes `core.io`'s six combinators reachable again, which
  is real value (`/stdlib` §1: `core.io` + its parent `core`, two named modules
  in the conformance report, both flipping together);
- but `/examples`' appendix §3 already measured what "compiles and leaks" costs
  on this exact type: the `(impl (Functor IO))` spelling compiles today, returns
  the right answer, and retains ~68 bytes per call, linear to 82.7 MB at 800k
  iterations. It is **not a workaround — it is the leak**, and it removes the
  diagnostic while keeping the defect;
- and R-2 forbids it directly: refusing to own a type in order to pass the
  release gate is fabricating a fact ("this type owns nothing") that is false.

Rejected. The runtime-directed disposition costs one intrinsics entry point and
one glue arm, and it is the only one that leaves the class smaller than it found
it.

---

## 5. Producer obligations

The contract binds producers. Each obligation below is stated so it can be
implemented from, and each names the crate that owns it. Cross-crate obligations
are filed as FIXMEs (§8); this section is the specification they point at.

### 5.1 Backend — retire the fabricated category (R-1, R-2)

`signature_heap_category`'s `Err(_) => HeapCategory::Mixed` arm is the single
seam. Its end state is a **located error**, restoring D2's no-fallback rule to
the retain side as well as the release side. It cannot flip while faces 1–3 have
traffic (§2.6: +16 refusals), so it flips **per family, gated on measured zero
traffic**:

1. **Instrument the arm** (permanently, not as scaffold): a debug-profile census
   of every `Err` licence, keyed by frame and type shape. The scaffold this
   window used is the prototype; `/dev` lands the production form. This is the
   `0768` rule applied to a classifier — an instrument is unverified until it
   has detected, and this one has (§2.3).
2. **Face 1 first** (backend-only, no producer needed): a ctor-template frame
   emits no RC op on a residual parameter (I-CT′, §4.1). Expected census delta:
   −3,108 bare-`Var` licences and −2,216 release admissions, ≈89% of the class,
   with **zero** emission change for any concrete parameter.
3. **Faces 2 and 3 next**, as their producer obligations land (§5.2). Expected
   census delta: −538 and −480 and −55, to zero.
4. **Flip the arm to a located error** only when the instrument reads zero
   across the corpus. Same for `emit_heap_binding_decs`'s type-keyed arm, which
   at that point has no traffic at all and deletes rather than re-keys.

**The census reading zero is the acceptance criterion, not a code review.** This
is measure-before-binding institutionalised: the arm is the gate on its own
removal.

### 5.2 Typecheck — remove the monomorphisation exemption (R-3)

Owner: `/design`(typecheck) → `/dev`(typecheck). Filed as FIXME (§8).

> Synthetic field accessors and generic trait-method instances are compiled once
> per *declaration*. They must instead be monomorphised per concrete
> instantiation, exactly as ordinary generic `defn`s already are, so that every
> parameter and result type reaching backend is concrete.

Precise form:

- **F1 (accessors).** `adt.rs`'s accessor synthesis mints a `Def` whose `self`
  parameter is `ADT(T, [Var…])` and whose result is the declared field type,
  possibly a bare `Var`. The mint must be instantiation-keyed: one `Def` per
  concrete `T <args>` actually demanded, under the existing monomorphic mangle,
  with `self` and the result substituted. *Interaction with rider 0867*: 0867
  widens accessor minting to every sum type and distinct-name product, i.e. it
  **widens this family's surface**. `SPRINT.md` §Must-not-interleave already
  gates 0867 behind this disposition; this ruling is that gate's content.
- **F2 (trait-method instances).** The instance name is keyed on the type
  *constructor* (`Functor.fmap$primitives/Option`). It must be keyed on the
  full concrete instantiation (`…$primitives/Option$Int`), which is a **key
  widening on an existing mangle**, structurally the same change as S110's
  alias-class close (`backend-keyed-consumer.md` §1.1.2) — not a new naming
  scheme, not a second identity home.
- **Neither is a `cranelisp-types` delta**, and neither changes any extern name
  or ABI. Both change how many bodies are emitted and under what names.

**Note for the typecheck round.** This obligation and 0913's (§5.4) are the same
rule at two altitudes: *do not hand codegen a type you have not got*. The
lenient view fabricates at the value level; the declaration-once exemption
fabricates at the frame level.

### 5.3 Intrinsics — split `consume_io_tree` at the dec (face 4)

Owner: `/design`(intrinsics) + `/arch` (public surface). Filed as FIXME (§8).

`consume_io_tree(ptr)` today does dec → tag-walk → dealloc in one body. Backend
needs the tail half alone, because it must interpose the `Pure`-payload
discharge between "we know this is the last reference" and "the node's fields go
away". The requested shape — a **split of one existing function, not a second
mechanism**:

```
// existing, unchanged in behaviour:
consume_io_tree(ptr)  ==  { if !last_ref(dec(ptr)) { return } ; fence ; free_io_node(ptr) }

// new public entry point, the tail half:
free_io_node(ptr)     // tag-walk + branch release + dealloc; NO dec, NO fence
                      // precondition: caller has dec'd to zero and fenced
```

Backend's registry then classifies `ADT(primitives/IO, [T])` as **runtime-owned**
and emits, in place of a derived `ctor_shapes` body:

```
drop<IO T>(p):
    if p < NULLARY_TAG_THRESHOLD: return
    old = atomic_rmw sub [p+8], 1
    if old != 1: return
    fence
    if load(p, TAG_OFFSET) == IO_TAG_PURE:
        drop<T>(load(p, FIELDS_START))        // canonical glue for T — no new identity
    call runtime/free_io_node(p)
```

Three properties `/review` should check against this shape:

- `ctor_shapes` is **not reached** for `primitives/IO`, so the identity check at
  `drop_glue.rs:497-505` stays exactly as it is — it is a correct check on a
  precondition IO structurally cannot meet, and weakening it would weaken it for
  every other type;
- the `Pure` arm calls `drop<T>` — the *same* canonical glue every other site
  calls. Face 4 adds **no new release identity**, satisfying G2;
- `guard_nullary` for `IO` follows the ordinary rule (IO has no nullary ctor, so
  the guard is present only for uniformity with the runtime's own contract).

**The `Bind` introspection rider.** `/repl`'s appendix item 5 shows one cause
behind two symptoms: `Bind` is seeded manually and is not enrolled the way
`Pure`/`Effect` are, so the diagnostic names a constructor the REPL then denies
exists. Whatever `/dev` does to `Bind`'s seed in this window must leave it
introspectable (`/info Bind`), because R-4 requires a refusal's nouns to be
lookup-able and the same seed is the reason they are not.

### 5.4 Typecheck — the lenient view stops fabricating (face 5, 0913)

Owner: `/design`(typecheck), Round 2 of this Phase, against this landed contract.
Stated here as the obligation, precise enough to implement from.

> **`MonoExpr::lenient_from_expr` must carry each node's real type.** Where the
> real type contains a residual type parameter, the view must apply an explicit,
> recorded **defaulting** step — never a wholesale substitution of the node's
> type.

The distinction is the whole obligation, so it is stated as three parts:

1. **What is forbidden.** Replacing `(Result a String)` with `ConcreteType::Int`
   is a fabrication under R-2: it does not default a *parameter*, it discards
   the type. Backend then sees a scalar, emits no glue, and the result root
   leaks — measured by `/repl` at 2–6 blocks per turn on the single most common
   result shape in the language (`(Ok x)`/`(Err x)`), with `deallocs +0` and
   `live` growing linearly in session length.
2. **What is permitted, and why it is sound.** An **unconstrained** residual
   parameter may be defaulted to a declared `NeverHeap` type, per parameter
   position, leaving the type constructor and every constrained argument intact:
   `(Result a String)` → `(Result <default> String)`. The soundness argument is
   exact and checkable: a parameter that is still free after inference is a
   parameter no value in the released graph inhabits — if a value of that type
   were present, unification would have pinned it. The canonical glue for
   `(Result <default> String)` branches on the runtime tag; the arm carrying the
   defaulted parameter is unreachable for this value, and the `Err` arm's
   `String` is discharged correctly. The defaulted position is *typed out of the
   walk*, not walked with a wrong type.
3. **The check the narrowing carries** (Principle 25). The defaulting step must
   assert its own precondition — the parameter is genuinely unconstrained at the
   point of defaulting — and must be visible as a distinct operation with its
   own name, not an inline `unwrap_or(Int)`. A defaulting applied to a
   *constrained* parameter is a fabrication and must be a located error.

Two acceptance constraints carried from the FIXME, both binding:

- **0913 must not be closed by pinning annotations** in tests or docs. "Annotate
  your `Result` and it stops leaking" is not a user-facing contract, and the
  residual-parameter *displays* are spec-required (`repl/spec.md` §1.5/§4.1) and
  correct — the displays are right; the release behind them is not.
- `design/int/result-owner.md` §1.1.1's scope sentence is wrong in the same
  window (`/design`(int)'s side): the axis is the `Result` family and parameter
  position-independence, not the `[]`/`None` corner, and its `None` example is
  impossible (nullary, bare tag, cannot leak).

### 5.5 Backend — the refusal's frame (R-4, 0915)

Owner: `/dev`(backend), `crates/cranelisp-backend/src/error.rs:121-132`
(`CompilationError::CodegenFailed`'s `Display`). Not cosmetic: R-4 makes it part
of the contract, because "located refusal" is a disposition this table assigns.

- **One category prefix per diagnostic.** The nested `codegen error at 0..0:`
  doubling surfaces the compiler's own call structure; the inner wrapper's
  category/span must not re-render when it is nested.
- **A real span.** A refusal raised at a release site knows the binding's span
  and the frame's span. `ErrorLocation::from_span(Span::SYNTHETIC)` at
  `drop_glue.rs:539-544` is the current default and is the direct cause of
  `0..0`; every error raised in the glue registry should carry the requesting
  frame's span.
- **A subject the user can look up.** `user/user/then$primitives/IO$Int+…`
  doubles the module and exposes the mono mangle. The rendered subject should be
  the user-visible symbol, with the instantiation shown as types rather than as
  a `$`-mangle.

`repl/spec.md` §5.5 is the normative surface and is `/repl`'s; this section is
the backend-side obligation only.

---

## 6. FIXME 0917 — the distinct axis (provenance classification)

Ruled here because it shares the window, kept out of the table because it shares
nothing else: all types are concrete, no residual anything, and the seam is the
protect licence rather than the release contract. Folding it in was the framing
error `/arch`'s restructuring corrected.

### 6.1 The mechanism, read at source

`/qa`'s attribution names `protect_return_value` — actually at
`crates/cranelisp-backend/src/compiler/rc_emission.rs:156`, in `impl FnCompiler`
(**0917's FIXME cites `fn_compiler.rs`; `git log -S` shows it was never there**;
the type-qualified reading `FnCompiler::protect_return_value` is the correct
one). Call sites: `match_codegen.rs:322,574`, `control_flow/lambda.rs:554`,
`control_flow/launch.rs:261`.

The licence is `is_fresh_construction` = `value_provenance(body, is_ctor) ==
ValueProvenance::Fresh` (`fn_compiler.rs:2366,2438`). A **bare nullary
constructor reference is not a `MonoExpr::ConstrADT`** — `Expr::ConstrADT` is
synthesised only for constructor `Def` bodies, so user-written `None` in an arm
is a `MonoExpr::Var { resolution: VarRef::Global(None) }`, and the `Var` arm
returns `NotOwnedHere` unconditionally (`:2508-2511`). `NotOwnedHere` is the
lattice's ⊤ and `join` is `max`, so **one nullary arm poisons the whole match's
provenance**, the protect fires on a fresh boxed arm, and nothing balances it.

### 6.2 The ruling — one lattice point, no new licence arm

The conflation is in ⊤ itself. `ValueProvenance::NotOwnedHere`'s own rustdoc
describes two different things: "a scope binding (whose own scope cleanup decs
it), **a non-heap scalar (no reference at all)**". Those are not the same fact,
and the second one is not a top element — **"carries no reference" is the join's
identity, not its absorbing element.**

> **Ruling.** `ValueProvenance` gains a **bottom** point below `Fresh`:
> `NoReference` — the value carries no heap reference at all. A bare nullary
> constructor reference (a `Var` resolving to a zero-field constructor, lowered
> to a bare `iconst` tag below `NULLARY_TAG_THRESHOLD`) classifies `NoReference`,
> as do scalar literals. Ordering: `NoReference ⊏ Fresh ⊏ OwnedTemporary ⊏
> NotOwnedHere`; `join` stays `max`, so a nullary arm is now absorbed by its
> sibling arms instead of poisoning them.
>
> Thresholds: `is_fresh_construction` becomes `<= Fresh`; `yields_owned_temporary`
> becomes `matches!(p, Fresh | OwnedTemporary)`.

This is a **classification correction, not a new emission licence arm** (G2): no
emission site gains a branch, the exhaustive `value_provenance` match gains one
arm's answer, and `protect_return_value` is untouched.

### 6.3 The pin that must be amended, and how

`provenance_owned_threshold_is_probe_independent` asserts the owned threshold is
identical under `|_| true` and `|_| false`, so the five probeless release gates
need no symbol-table access. A nullary-ctor `Var` is only distinguishable from an
ordinary `Var` *with* the probe, so equality cannot survive. Replace it with the
strictly stronger **monotonicity** pin:

> The constructor probe may only move a node's provenance **down** the lattice
> (toward stronger ownership): `value_provenance(n, real_probe) ⊑
> value_provenance(n, |_| false)` for every node. The probeless gates therefore
> never over-claim ownership; where they differ they take the leak-safe verdict,
> never the UAF one.

Equality was a proxy for "the probeless gates are safe"; monotonicity states it
directly and keeps the instrument's real content. `/dev` re-derives it over the
same node corpus the existing pin walks.

### 6.4 Byte-identity obligation

Moving scalar literals to `NoReference` is the honest classification but must be
proven emission-neutral: `HeapCategory::classify` already makes a scalar body's
protect a no-op, so the golden CLIF corpus is expected byte-identical for that
half. `/dev` verifies against `tests/fixtures/clif_baseline/golden/` and reports;
a non-identity is a finding, not a re-baseline.

### 6.5 Acceptance

`nullary_arm_beside_boxed_arm_0917` ×2 (`--run` and `--link`) plus cell #21
(`exemplar_ownership_residue_s116::sudoku_warm_serial_solve_residue_at_most_1400`
— re-attributed here by `/qa`, `s118-test-plan.md` §11.8.1). Three REDs, no
producer dependency, no cross-crate delta.

---

## 7. Staging, and the honest scope statement

**The contract converges as a unified statement** — the table in §4 is total over
the measured class and every face carries one disposition. **Its implementation
severs**, and it severs in exactly the order `/arch` named as the fallback, for
reasons the measurement supplies rather than for capacity reasons:

| Order | Piece | Crates | REDs | Depends on | Corpus gate |
|---:|---|---|---:|---|---|
| 1 | **0917** — provenance classification (§6) | backend only | **3** | nothing | full suite byte-identity for the scalar half |
| 2 | **Face 4** — IO runtime-directed teardown (§5.3) | backend + intrinsics entry point | **7** | one intrinsics split (FIXME) | full suite; `core.io` + `core` flip together; `21-hello-io` exit 243, `23-io-sequence` exit 178 in all four cold/warm × run/link cells |
| 3 | **Face 1** — retire the ctor-template pair (§4.1) | backend only | 0 directly | nothing | census A −2,216 / census B −3,108; **zero** emission change on any concrete parameter |
| 4 | **Faces 2+3** — monomorphise the exempted frames (§5.2) | typecheck (producer) + backend | **1** (0916) | §5.2 | census to zero; **zero new refusals**; `f4_sudoku.clif::user::Grid.cells` re-baseline |
| 5 | **Face 5** — the lenient view (§5.4) | typecheck | **1** (0913) | §5.4 ruling | `residual_type_param_result_leak_0913` marginal 0 |

Pieces 1–3 are backend-only and land inside this sprint's backend waves;
**10 of the 11 spine REDs (0917×3 + 0907×7) close without any producer change.**
Piece 4 carries 0916's single RED and **does not close without §5.2**, which is
a typecheck change. `/sprint` should treat 0916 as producer-gated rather than
assume it rides the backend wave — that is this window's principal scheduling
finding and it is stated plainly rather than optimistically.

Rejected explicitly: closing 0916 inside the frame by withdrawing the retain
licence for F2 only. §4.3 proves it converts a SIGSEGV into a UAF on a
duplicating arm, and §2.6 shows refusing instead costs the same 16 programs.

### 7.1 Acceptance witnesses named

- **`f4_sudoku.clif::user::Grid.cells` static re-baseline** (0903's binding
  addendum). Under face 2 the frame is monomorphised, so the golden's shallow
  release is replaced by a canonical `drop<Grid Cell>` call. `/dev` plans the
  scoped, attributed re-capture **in the fixing change-set**, per
  `ownership-inference.md` §6.2 (extension ≠ re-baseline). It is a **static**
  witness — `/port` proved the exemplar never calls that accessor — and it stands
  as written.
- **The 0907 trait-instance leak cell** (`/examples` rider §5). The
  `(impl (Functor IO) (defn fmap [g io] (bind io (fn [x] (Pure (g x))))))`
  instance must **balance**. Note this cell sits at the intersection of faces 3
  and 4: it is an F2 frame *over* `IO`, so it needs piece 4 (monomorphisation)
  as well as piece 2 (IO glue). It is therefore an acceptance cell for the
  *class*, not for either piece alone, and `/qa` should place it accordingly.
- **The face-4 residual guard** (§4.4). A nested `Pure` payload inside an unrun
  `Bind` sub-tree is not discharged. `/qa` owes a failing-not-ignored leak guard
  for that shape, so the residual is visible rather than silent — the same rule
  0907's option-3 already carried, applied to the disposition actually taken.
- **`repl/demos/archive/ring4s.demo`** — the archive's only red, at its
  `(defn then [a b] (bind a (fn [_] b)))` segment, flips with piece 2. Its shape
  is the S61 double-free idiom, so it is load-bearing history and its flip is
  evidence, not incidental.

### 7.2 Rider 0906 — the third hand-rolled nullary guard

Owner `/dev`(backend). Fold the `guarded` arm of the Vec element inc-adapter
(`vec_codegen.rs` ≈:986) onto `heap::emit_nullary_skip_guard`. It is
polarity-correct today and lives in a separate Cranelift context, but it is the
same decision spelled a third time, and R-1's whole content is that this decision
has one home. **Not byte-identical** — the adapter creates `inc_block` before
`ret_block` while the shared helper requires the continuation block first, so the
two block labels swap. Lands with a **scoped** golden re-baseline for the covered
bodies only, and reuses `ctor_template_admission_tests::assert_threshold_guarded_rmws`
(it walks arbitrary CLIF text) for the absolute-polarity pin.

---

## 8. What this contract forbids (`/review` reject criteria)

Binding, in addition to `transitive-drop-glue.md` §11's list, which stands:

1. **No new emission licence arm.** Every disposition in §4 either reuses the
   canonical glue call, reuses an existing runtime dispatch (`consume_io_tree`,
   the closure `DROP_GLUE_PTR`), or emits nothing. A change-set that adds a
   release mechanism is a reject regardless of what it fixes (G2).
2. **No fabricated concreteness anywhere** (R-2). Specifically: no new `Err ⇒`
   default-category arm, no `unwrap_or(ConcreteType::Int)`, no "refuse to own
   this type" admission exclusion, and no defaulting of a *constrained* type
   parameter.
3. **No RC operation on an uncategorised word** (R-1), at any seam, however
   guarded. The `NULLARY_TAG_THRESHOLD` guard is not a pointer test and citing it
   as one is the defect, not the mitigation.
4. **No frame-keyed narrowing landed alone.** §2.6 measured it twice, one sprint
   apart, at +16 refusals. A change-set that re-keys the admission without the
   producer obligation having landed is a reject; the census (§5.1) is the
   evidence, not a code reading.
5. **No second glue identity home**, and specifically: face 4 must call
   `drop<T>` for the `Pure` payload, never mint an IO-specific payload releaser.
6. **No `#[ignore]` on the face-4 residual** (§4.4) or on any leak this ruling
   knowingly leaves. Hiding a known leak behind `#[ignore]` is itself a defect
   (root `CLAUDE.md` §Testing).
7. **No refusal at span `0..0`** against a `$`-mangled subject once §5.5 lands
   (R-4).

---

## 9. Unit-test design (backend tier)

Extends `transitive-drop-glue.md` §10. Rows are placed beside their production
owner per the crate `CLAUDE.md` sibling convention.

| Submodule | Complexity / positive | Edge | Negative |
|---|---|---|---|
| `rc_emission::signature_heap_category` | each concrete shape maps to its category; the census instrument records a licence with frame + shape | a concrete sum with a nullary ctor is `Mixed`; a concrete product is `AlwaysHeap` | **a residual `Type::Var` yields NO category and NO RC op** — not `Mixed`; the census instrument fires (detection proof, per the 0768 rule); after the flip, a located error naming the frame |
| `fn_compiler` ctor template (replaces §10 row 4) | a generic-ctor template and an undeclared-field template each emit **zero** RC ops on their residual parameters; a concrete-field template still takes the ordinary `drop<T>` path | multi-field template: zero ops on every residual field, ordinary path on every concrete one | no guarded inc and no guarded dec survive on a residual parameter at any seam; `ctor_template_admission_tests::assert_threshold_guarded_rmws` finds no rmw traceable to a residual slot |
| `drop_glue` IO arm | `ADT(primitives/IO, [T])` classifies runtime-owned and emits dec + tag test + `drop<T>` + `free_io_node`; `IO Int` emits the same shape with `drop<Int>` elided as non-owning | nested `Bind` over `IO (IO Int)` requests one body, not two | `ctor_shapes` is **not** called for `primitives/IO`; no IO-specific payload releaser symbol is minted; the identity check at `:497-505` is unchanged and still fires for a genuinely divergent user type |
| `fn_compiler::value_provenance` | `NoReference` for a bare nullary ctor `Var` and for scalar literals; `Fresh` for every minting kind | `join(NoReference, Fresh) == Fresh`; `join(NoReference, NotOwnedHere) == NotOwnedHere`; a match with N nullary arms and one boxed arm is `Fresh` | **probe monotonicity** (§6.3) over the existing node corpus; a borrowing kind never reaches an owned point under any probe; the match stays exhaustive (no `_ =>`) |
| `error` / diagnostic frame | a codegen refusal renders one category prefix, a real span, and an unmangled subject | a refusal from inside a monomorphised instance renders the instantiation as types | no `0..0` span from the glue registry; no `module/module/` doubling |

E2e acceptance is `/qa`'s (`tests/plan/s119-test-plan.md`); §7.1 names the
witnesses this design owes it.

---

## 10. Quality attributes

- **Simplicity.** The class shrinks rather than grows. Retired: §4.1's sanctioned
  exception, invariant I-CT, I-CT's standing `Borrowed`-mode obligation, the
  `Err ⇒ Mixed` fabrication, the type-keyed release arm, and (via §5.2) two
  monomorphisation exemptions. **Added: one intrinsics entry point that is a
  split of an existing body, and one lattice point.** Mechanism count for
  release stays at one plus the two sanctioned runtime dispatches
  (`transitive-drop-glue.md` §1.1 M5 and, now explicitly, the IO tag-walker).
- **Observability.** The census instrument (§5.1) is the first thing in this
  class that can *prove* the fabrication has no traffic left, which is what
  turned this window's ruling from an argument into a measurement. It is
  permanent, debug-profile, and its own removal criterion.
- **Concurrency-safety.** Unchanged. The wild atomic writes this ruling removes
  were the class's only interaction with the atomicity policy; the RC atomicity
  decision itself is untouched.
- **Performance.** Face 1 removes 3,108 guarded inc/dec pairs and 2,216 guarded
  decs from the measured corpus at zero behavioural cost. Faces 2/3 trade one
  body per declaration for one body per instantiation — a code-size increase
  proportional to distinct instantiations, which is the price the language
  already pays for every other generic function. No new runtime cost.
- **Testability.** Every disposition has a negative cell that fails if the
  fabrication returns (§9), and the census is a standing detector rather than a
  one-shot experiment.
- **Maintainability.** The blast radius of the next non-concrete frame is
  bounded by construction: R-1 makes it emit nothing, R-3 makes it a producer
  defect, and the census names it on the first run.

---

## 11. Cross-references

- `transitive-drop-glue.md` §4.1 (face 1's history; defers here), §10 row 4
  (superseded by §9 row 2), §11 (its no-interim list stands; §8 extends it)
- `design/arch/concrete-boundary-type.md` §3.1.1 — the signature-driven codegen
  target; the ctor/accessor pairing this ruling completes
- `design/arch/safety-invariants.md` §4 — R-1 and R-2 are new rows for the
  register (`/arch`'s to add; filed)
- `design/arch/ownership-inference.md` §2.1, §3.1 — monotone soundness; §6.3's
  monotonicity pin is the same shape one level down
- `design/int/result-owner.md` §1.1.1 — the scope sentence 0913 corrects
- `repl/spec.md` §5.5 — the normative surface for R-4

## Next skills

- **`/design`(typecheck)** — Round 2 of this Phase, against this landed contract:
  §5.4 (0913, the lenient view) and §5.2 (the monomorphisation exemption, which
  is the producer half of faces 2 and 3 and gates 0916 and rider 0867).
- **`/arch`** — Round 3 exit gate: the IO tri-context seam (§5.3 needs one new
  `cranelisp-intrinsics` public entry point and its `public-api.txt` delta), and
  two new rows for `safety-invariants.md` §4 (R-1 category-before-operation, R-2
  no-fabricated-concreteness).
- **`/dev`(backend)** — pieces 1, 2, 3 and rider 0906 of §7, in that order, each
  with its §9 unit row; the census instrument (§5.1) lands with piece 1 and its
  detection proof is part of that change-set.
- **`/qa`** — the §7.1 witnesses, the face-4 residual guard, and the corpus-gate
  assertion form for §5.1's zero-traffic criterion.
- **`/testing`** — the §2.4 four-line accessor repro (`1023` GREEN / `1024`
  SIGSEGV) as a failing-not-ignored A/B pair; it is currently unguarded and is
  the cheapest memory-safety cell in this class.
