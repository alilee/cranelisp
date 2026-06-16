---
number: 0379
target: /arch
filed_by: /review
filed_at: 2026-06-16
sprint_filed: 84
refers_to: crates/cranelisp-typecheck/src/program.rs §find_ambiguous_let_binding (~1522) + §is_ambiguous_codegen_reaching_type (~1584), crates/cranelisp-backend/src/heap.rs §HeapCategory::classify (~446) + §classify_adt (~471), sprints/SPRINT.md §"Cluster A re-shape", spec/03-types.md §3.11
status: open
---

# §3.11.1 ambiguity heuristic is positionally incomplete — a Mixed-ADT-with-free-var reaches codegen through non-`let` value positions

> **ARCH-DESIGN-COMPLETE (S84 Wave 2, /arch, 2026-06-16) — LEFT OPEN for the /dev relay.**
> The user ruled "belt-and-braces" (2026-06-16): close 0379 with BOTH sides
> position-complete, agreeing via ONE shared predicate. /arch has landed the
> shared predicate and specified both consumption seams; the FIXME stays OPEN
> until both consumers land green, when the /dev relay `git rm`s it.
>
> **Landed this session (`crates/cranelisp-types/`):** `Type::is_representation_undetermined(&self) -> bool`
> (`crates/cranelisp-types/src/types.rs`) — THE single source of truth. TRUE for
> bare `Type::Var`, `Type::TyConApp`, and a non-`Vec` `Type::ADT` carrying a free
> var (the `Mixed`-family case the bare-`Var` panic missed); FALSE for `Type::Fn`,
> `(Vec a)` (uniformly heap → `classify` `AlwaysHeap`), fully concrete types, and a
> `Type::ADT` with no free var (the legitimate type-known nullary-tag case).
> Table-free/structural (the "carries a free var in a representation-bearing
> position" half); backend supplies the "is `Mixed`-shaped" half from tables → the
> two crates agree on the dangerous core by construction. 9 unit tests (Option-a /
> Box-a / bare-Var / TyConApp TRUE; Vec-a / Fn-a / Option-Int / Int FALSE; nested
> TRUE). `public-api.txt` regenerated — one additive line, no cache bump.
>
> **Seam 1 — typecheck position-complete §3.11.1 check (/dev on cranelisp-typecheck).**
> Generalise `find_ambiguous_let_binding` / `is_ambiguous_codegen_reaching_type`
> (`crates/cranelisp-typecheck/src/program.rs`) so the per-node check calls the
> shared predicate on the resolved type at EVERY value position `for_each_child_expr`
> already visits — `Expr::Apply.args`, `Expr::Match` scrutinee + arm bodies,
> `Expr::If` branches, `Expr::VecLit` elements, `Expr::ConstrADT` fields,
> `Expr::ParBind` bindings, nested/return positions — not only `let` bindings (and
> `find_ambiguous_top_level_form` walks the same generalised scanner). Replace the
> inline `is_ambiguous_codegen_reaching_type` body with a `Type::is_representation_undetermined()`
> call (retire the local heuristic). Error: the existing `CheckError`/`TypeError`
> "ambiguous type; add an annotation" with a source location. The predicate is
> directly the verdict (conservative `true` = correct rejection under
> mono-from-roots; not a false positive). Unit + e2e: the FIXME's empirical non-`let`
> repros (match scrutinee `(Pure (match (id Non) …))`, vec element `(first-tag [(id Non)])`).
>
> **Seam 2 — backend 0375 WIDENED total backstop (/dev on cranelisp-backend).**
> Per `design/backend/ring2-rc.md` §1.6: widen the panic so the RC-emit path trips
> on ANY type satisfying the shared predicate at an RC site — gated behind the
> existing `Mixed` verdict: `panic iff classify(ty, tables) == Mixed && ty.is_representation_undetermined()`
> (covers both bare `Type::Var` AND `Mixed`-ADT-with-free-var — the family
> `classify(Type::Var)→unreachable!` alone misses, because a `Mixed` ADT routes to
> `classify_adt` by ctor shape and never reaches the `Type::Var` arm). The `Mixed`
> gate excludes a table-determined `NeverHeap`/`AlwaysHeap` ADT carrying a free var
> (no panic on a representation-determined ADT). Retire the `<1024` guard from this
> representation-undetermined path; KEEP it for the type-known nullary-tag
> `Mixed`-ADT discrimination (no free var: `classify == Mixed && is_representation_undetermined() == false`),
> its sound origin. Still gated strictly after 0374 (already green). This is the
> reshaped-0375 from SPRINT §"Cluster A re-shape" (mechanism→backstop), now WIDENED
> per the ruling.
>
> **Manifestation sites updated (arch-owned, this session):** BC §3 invariant 9
> (belt-and-braces paragraph); BC §2 (position-complete note); `interfaces.md`
> §"Callability is structural" (the predicate as a cross-crate surface item);
> Principle 20 cross-ref list. **0375's SPRINT-§"Cluster A re-shape" entry +
> `design/backend/ring2-rc.md` are /design(backend)'s to refine for the widening —
> a small note may suffice; not re-grounding here.** Original review finding below.

---


## Severity
Important (Wave-2 design input). NOT a Blocker for the Wave 1/1b change-set itself:
the change-set is internally coherent and the 2 Wave-0 `(Box a)`-HOF SIGSEGV guards
flip green. This finding is about the *joint completeness* of the heuristic + mono
that the re-shape's soundness story rests on, and is the right input for the Wave-2
0375 backstop design (the 0375-as-specified does NOT close it).

## Issue

The S84 re-shape (SPRINT.md §5) makes the structural slot gate the PRIMARY
SIGSEGV-prevention mechanism and names two backstops for the residual
"`Mixed`-ADT-carrying-a-free-`Type::Var`-reaches-codegen" case:

1. the typecheck-side §3.11.1 ambiguity check (`is_ambiguous_codegen_reaching_type`);
2. the planned Wave-2 0375 backstop (`classify(Type::Var) → unreachable!`).

**Backstop (2) cannot catch a `Mixed` ADT.** `HeapCategory::classify`
(`heap.rs:446`) routes `Type::ADT(fqtn, _)` to `classify_adt`, which inspects
ONLY the constructor shape (`fqtn`) and **ignores the type args entirely** (the
`_` is dropped). A `(Option a)` / `(Box a)` / `(Opt a)` carrying a free var
classifies by its ctor shape — nullary `None` + data `Some` ⇒ `Mixed` — and never
reaches the `Type::Var` arm where the 0375 panic lives. The free var rides
invisibly in the unused args. So (1) is the SOLE guard for this family, and the
"no unsound `Type::Var` reaches codegen" invariant is total only if (1) +
monomorphisation are JOINTLY complete for every codegen-reaching position.

**They are not jointly complete: (1) is positionally incomplete.**
`find_ambiguous_let_binding` (`program.rs:1522`) only fires its CHECK on
`Expr::Let { bindings }` binding VALUES. It recurses into all children via
`for_each_child_expr` (recursion is complete), but the per-node check only
triggers on a `let`-binding value. Every other codegen-reaching value position is
reached-but-not-checked: function-call arguments (`Expr::Apply.args`), match
scrutinees and arm bodies (`Expr::Match`), `if` branches, `Expr::VecLit`
elements, `Expr::ConstrADT` fields, and `Expr::ParBind` bindings (the check
matches `Expr::Let`, not `ParBind`). `find_ambiguous_top_level_form` likewise only
walks `defn.variants[].body` through the same `let`-only scanner.

When monomorphisation pins the var (a concrete arg/field/sibling unifies it),
none of this matters — the value is concrete and sound. The hole is exactly the
case the heuristic exists for: the var stays **genuinely free** (nothing pins it)
AND it sits in a non-`let` position.

## Reproduced (empirical, HEAD = 77c634a)

Bare prelude; inline `Mixed` ADT `(deftype (Opt a) (Non []) (Som [:a v]))`;
`(defn id [x] x)`:

- **CHECKED (correct):** `(let [x (id Non)] (Pure 0))` →
  `error: ambiguous type; add an annotation … bound in main`, exit 1. ✓
- **UNCHECKED (hole):** `(Pure (match (id Non) [Non 0 (Som v) 1]))` — the SAME
  ambiguous value `(id Non)` as a **match scrutinee** → compiles and runs
  **silently, exit 0**. The free var reaches codegen.
- **UNCHECKED (hole):** `(first-tag [(id Non)])` — `(id Non)` as a **Vec literal
  element** (direct fn arg, no `let`) → compiles, exit 0.

These exit 0 (not SIGSEGV) only because the specific shapes discriminate on the
nullary tag and never deref a `≥1024` field. That is luck-of-shape, not soundness:
the same positional bypass with a data-ctor value whose field is dereferenced at
`≥1024` is the exact `Mixed`-RC-guard path the re-shape set out to close. The
invariant holds by accident of which arm runs, not by construction.

## Divergence from ground truth (heuristic vs backend `classify`)

`is_ambiguous_codegen_reaching_type` (`program.rs:1584`) approximates the
backend's `Mixed` verdict but cannot call it, and the two DISAGREE in both
directions:

- **Heuristic too narrow (under-fire, the dangerous direction):** it only inspects
  `Type::ADT` args for a free var and excludes `Vec`. The backend's `Mixed`
  verdict comes from *ctor shape* (`(has_nullary, has_data) == (true, true)`),
  computed for `Type::ADT` regardless of position. The heuristic never runs on the
  non-`let` positions above, so a backend-`Mixed` value escapes.
- **`Vec`/`Fn` exclusion — SOUND as far as it goes.** Confirmed against
  `classify`: `Type::Fn → AlwaysHeap` (`heap.rs:449`) and `Vec → AlwaysHeap`
  (`classify_adt` short-circuit `heap.rs:480`). Both are uniformly heap-represented
  ⇒ RC is element-type-independent ⇒ never the unsound `Mixed`/`<1024` path. The
  exclusion is sound, not merely convenient. (Caveat: the exclusion is keyed on the
  bare name string `"Vec"` in BOTH the heuristic and `classify_adt` — a
  stringly-typed coupling across the crate boundary; if a second uniformly-heap
  builtin is ever added, both sites must be updated in lockstep. Minor, noted under
  Suggestions in the review, not part of this hole.)

## Proposed resolution (Wave-2 design input — /arch to direct /backend + /dev)

The re-shape's own principle is the fix: **make it sound-by-construction, not
heuristic.** Two coherent options for /arch to weigh:

1. **Mono guarantees concretisation (preferred — belt-not-mechanism).** If
   monomorphisation-from-roots genuinely concretises every codegen-reaching
   instance (the stated Cluster-A goal), then a residual free var in a
   codegen-reaching position is by definition an *ambiguous program* (no root pins
   it) — and the ambiguity check should reject it **by a position-complete scan**,
   not a `let`-only one. Resolution: generalise `find_ambiguous_let_binding` to
   check the resolved type at EVERY value-producing node `for_each_child_expr`
   already visits (arg, scrutinee, arm body, if-branch, vec element, ctor field,
   ParBind binding), not only `let` bindings. This makes (1) actually total and
   keeps it a typecheck-side error rather than a codegen crash.

2. **0375 also handles `Mixed`-with-residual-var (backend backstop made real).**
   Have `classify`/the RC-guard path detect a `Type::ADT` whose ARGS still carry a
   free `Type::Var` and route it to the same `unreachable!`/panic as the
   `Type::Var` arm — so the backstop the SPRINT plan claims actually covers the
   `Mixed` family it currently misses. This turns a silent-or-SIGSEGV into a
   located compiler-bug panic (Principle 18). Weaker than (1) — it converts a UAF
   into a panic rather than a clean typecheck rejection — but it closes the
   "backstop (2) can't catch `Mixed`" gap the SPRINT §5 text overlooks.

(1) and (2) are complementary: (1) is the clean typecheck-side rejection; (2) is
the structural tripwire. The SPRINT §5 claim that 0375's `classify(Type::Var)`
assert is the codegen-side complement to the §3.11.1 check is **incomplete as
written** — for the `Mixed` family the codegen-side assert never fires, so the
typecheck-side check must be position-complete (1) OR 0375 must be widened (2).

## Operational implication / Context

- Wave 1/1b lands as a net improvement (the `(Box a)`-HOF SIGSEGV is fixed; the
  `let`-position ambiguity is now caught). This FIXME does not block that.
- The 0375 Wave-2 design (`design/backend/ring2-rc.md` §1.5/§1.6) should be
  updated to record that `classify(Type::Var)→unreachable!` does NOT cover the
  `Mixed`-ADT-with-residual-var case, and to choose (1)/(2)/both. Without this, the
  sprint will close believing "no unsound `Type::Var` reaches codegen" is total
  when it is total only for the `let`-position and pinned-var subsets.
- A unit/e2e test pinning the negative for a NON-`let` position (match scrutinee /
  fn arg) should land with the resolution — there is currently no such guard, which
  is why the hole is invisible to the suite (route to /qa for the e2e, /dev for the
  typecheck unit test).
