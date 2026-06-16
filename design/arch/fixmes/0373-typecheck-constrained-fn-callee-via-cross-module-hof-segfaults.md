---
number: 0373
target: /backend
filed_by: /stdlib
filed_at: 2026-06-16
sprint_filed: 83
refers_to: crates/cranelisp-backend/src/heap.rs (HeapCategory::classify, emit_rc_inc_guarded), crates/cranelisp-backend/src/compiler/apply.rs (result-RC after indirect call), spec/07-traits.md §7.8, tests/regression.rs::fixme_0373_polymorphic_result_fn_value_two_hops_no_crash
status: open
---

> **TIER-1 PARTIAL RESOLUTION LANDED (S83 /dev typecheck, 2026-06-16).**
> The /arch-ruled (A) monomorphisation fix for the **polymorphic-result-hop**
> half is DONE. `pass4_monomorphise` now also collects LOCAL (same-module)
> pure-parametric polymorphic callees whose call-site result resolves to a bare
> unbound `Type::Var` (`collect_local_parametric_calls`, gated to that signature
> to preserve the 0344 generalize-and-keep fold), and `monomorphise_call`
> recursively monomorphises inner polymorphic-result hops
> (`monomorphise_inner_parametric_hops`, with the inner recursion's `state.subst`
> isolated so the 0349 call-result unification cannot re-collapse a parent's
> accumulator var). This propagates the concrete instantiation through a CHAIN of
> hops (2- and 3-hop chains verified), so each hop's mono instance carries a
> CONCRETE result type → `classify` sees `NeverHeap` → no RC guard → no crash.
> **GREEN:** the /qa free-standing repro
> `tests/regression.rs::fixme_0373_polymorphic_result_fn_value_two_hops_no_crash`
> now exits 251 (= neg(5) = -5). Unit guard:
> `cranelisp-typecheck program::tests::polymorphic_result_hops_monomorphise_with_concrete_result_type`.
>
> **RESIDUAL — STILL OPEN, RE-POINTED /backend.** The ORIGINAL /stdlib
> manifestation (`(vec-map my-abs xs)` where `my-abs` wraps a cross-module
> CONSTRAINED `abs`) still SIGSEGVs. This is a DISTINCT bug from the
> polymorphic-result hop: `my-abs` is already CONCRETE (`:Int → :Int`), so there
> is nothing to monomorphise on it. The crash is that the GENERIC `my-abs`
> closure (the fn-value passed to the imported HOF) calls the constrained `abs`
> through a GOT slot that is not wired to `abs$Int` in the cross-module-HOF
> dispatch context. Isolation (this phase): N8 (local HOF + `my-abs` fn-value)
> exit 9 ✓; lambda / named-non-constrained through `vec-map` ✓; only
> `my-abs`(constrained-callee) through a CROSS-MODULE HOF ✗. The crash fires even
> when the `vec-map` result is bound-and-dropped (so it is the constrained-callee
> GOT wiring, not result classification). This is the FIXME's original
> hypothesis — a GOT-slot / mono-variant wiring gap for an indirectly-reached
> constrained mono Def — and is a backend concern (`cranelisp-typecheck` cannot
> fix a GOT-wiring gap; `my-abs` is concrete and the typecheck-side mono of
> `abs$Int` is already created). **0373 stays OPEN for this residual; target
> /backend.**
>
> ---
>
> **TARGET RE-POINTED /typecheck → /backend (S83 /qa investigation, 2026-06-16).**
> The root cause is a backend RC-classification misfire, NOT a typecheck
> monomorphisation gap (though a typecheck-side monomorphise-the-hops fix is a
> valid alternative resolution — see the root-cause section). The defect is also
> far broader than the FIXME title: it is NOT trait-specific, NOT
> constraint-specific, and NOT cross-module-specific. See
> `## Root cause (S83 /qa investigation)` below. Original /stdlib report (the
> trait + cross-module-HOF composite) retained verbatim as one *instance* of the
> defect.

# Constrained-fn callee reached through a CROSS-MODULE higher-order fn SIGSEGVs (0355-adjacent)

## Issue

S83's 0355 fixed the *direct* cross-module call of a trait-constrained
(monomorphised) fn — `(cmp 1 1)` / `(assert-eq 7 7)` across a module boundary now
run to clean exit (verified end-to-end this phase). But a closely-related composite
shape still SIGSEGVs:

**A function value whose body transitively calls a cross-module constrained
(monomorphised) fn, when passed as a higher-order argument to a CROSS-MODULE HOF,
segfaults at run time.**

Minimal stdlib-based repro (6 lines, `--run`, SIGSEGV / exit 139):

```clojure
(import [primitives [IO Pure Int vec-len sub-i64]])
(import [collections.vec [vec-map]])   ; cross-module HOF
(import [num.int [abs]])               ; cross-module Num-constrained fn
(defn my-abs [:Int x] :Int (abs x))    ; local fn whose body calls the constrained abs
(defn main [] :(IO Int)
  (Pure (vec-len (vec-map my-abs [(sub-i64 0 1) 2 3]))))   ; SIGSEGV
```

The defect requires ALL THREE of: (a) the HOF is cross-module/imported
(`vec-map`); (b) the fn value passed to it transitively calls a constrained /
monomorphised fn (`abs`, which is `Num`-bound); (c) it is invoked. Drop any one
and it works.

## Isolation (this phase, narrowing on the prebuilt binary)

Each of these PASSES; only the combination above fails:

| # | Shape | Result |
|---|---|---|
| N2 | `vec-map` (cross-mod HOF) + a local **lambda** `(fn [x] (add-i64 x 1))` | exit 3 ✓ |
| N3 | `abs` (cross-mod constrained) called **directly** | exit 5 ✓ (this is 0355) |
| N5 | `vec-map` + `identity` (cross-mod **parametric**, non-constrained) | exit 3 ✓ |
| N7 | local `my-abs` (wraps `abs`) called **directly** | exit 7 ✓ |
| N8 | local `my-abs` through a **LOCAL** HOF `apply1` | exit 9 ✓ |
| N9 | `vec-map` + a local **named non-constrained** fn `inc1` | exit 3 ✓ |
| **N6** | **`vec-map` + local `my-abs` (wraps constrained `abs`)** | **SIGSEGV (139)** ✗ |

So: the cross-module HOF dispatch (N2/N5/N9 ✓) is fine, the local-HOF + constrained
callee (N8 ✓) is fine, and the direct cross-module constrained call (N3/N7 ✓, =
0355) is fine — but routing the constrained callee through a cross-module HOF
fn-value corrupts. The crash is at run time (codegen succeeds, JIT executes, then
SIGSEGV) — smells like a GOT-slot / mono-variant wiring gap for the
indirectly-reached `abs$Int` mono Def when its caller flows as a fn-value into an
imported HOF, rather than a typecheck rejection.

A free-standing (no-stdlib) reduction was attempted with a user `deftrait
Doubler` + hand-rolled `sum-map` HOF; it instead surfaced "no impl of trait
Doubler for type Int" from the wrapper's scope — a SEPARATE cross-module
trait-impl-resolution wrinkle (the helper-module impl isn't discoverable from the
caller when reached through the wrapper). That is likely a second layered bug; the
stdlib repro above is the clean SIGSEGV. Per the cross-skill defect-handoff
discipline (CLAUDE.md §"Cross-Skill Changes"), the visible SIGSEGV and the
free-standing trait-resolution error may be two distinct defects — /qa should
reduce each separately rather than assume one masks the other.

## Proposed resolution

/typecheck (likely with /backend on the GOT/mono-wiring half) to extend the 0355
`collect_imported_constrained_calls` / mono-variant GOT registration so a
constrained-fn callee that is reached INDIRECTLY (the caller is a fn-value passed
to a cross-module HOF) is monomorphised + GOT-slotted in the right scope, the same
way the direct call site already is. Confirm both `--run` and `--link`.

## Operational implication / Context

- **/qa owes a narrow failing-not-ignored repro** (per CLAUDE.md §"Usability
  Findings and Defects" — defects are not closed until /qa authors the test).
  Annotate `// spec: spec/07-traits.md §7.8.2` and `FIXME(/typecheck)`. The
  stdlib-based N6 shape above is the cleanest current repro; a free-standing
  reduction (tests/ may not depend on stdlib) needs a user `deftrait` + impl + a
  hand-rolled HOF, and should be split from the secondary trait-resolution error
  noted above.
- **stdlib impact:** stdlib's own self-tests do NOT hit this (the runner folds use
  hand-rolled loops, not `vec-map`-over-a-constrained-fn). It bites a *user* who
  writes the natural `(vec-map abs xs)` against the stdlib. No stdlib code change
  is warranted until the compiler fix lands; this is a language defect surfaced by
  composing stdlib at scale.

---

## Root cause (S83 /qa investigation, 2026-06-16)

### Minimal repro (free-standing, 5 lines, single file, NO trait / NO constraint / NO cross-module / NO Vec)

```clojure
(import [primitives [IO Pure Int sub-i64]])
(defn neg [:Int x] :Int (sub-i64 0 x))
(defn h1 [f] (h2 f))     ; hop 1 — result type is unbound type var `a`
(defn h2 [f] (f 5))      ; hop 2 — result type is unbound type var `a`
(defn main [] :(IO Int) (Pure (h1 neg)))   ; SIGSEGV (exit None / signal)
```

`--run` SIGSEGVs. The original /stdlib report's three-part precondition
(cross-module HOF + constrained callee + Vec) is **none of them load-bearing**.
The actual load-bearing condition is much narrower and broader at once:

> **A function value reaching its invocation site through TWO function hops,
> where the intervening function(s) have a POLYMORPHIC (unbound-type-variable)
> RESULT type, SIGSEGVs whenever the returned value is `>= 1024` unsigned —
> which is EVERY negative Int, and every positive Int `>= 1024`.**

### The mechanism (codegen — confirmed by CLIF + value-sweep)

The intervening hops `h1`/`h2` are compiled **once, generically** (template
`%h1$` with NO type arguments — `/clif` confirms there is no `h1$Int`
monomorphised specialisation). Their result type stays the unbound `Type::Var`
`a` (REPL `/sig h2` → `(Fn [(Fn [Int] a)] a)`).

For a result of type `Type::Var`, **`HeapCategory::classify`**
(`crates/cranelisp-backend/src/heap.rs:456-459`) returns **`Mixed`**:

```rust
Type::Var(_) | Type::TyConApp(_, _) => {
    // Unresolved type variable: might be anything
    HeapCategory::Mixed
}
```

`Mixed` causes the result-RC site after the indirect call
(`crates/cranelisp-backend/src/compiler/apply.rs:112-118`) to emit the guarded
inc **`emit_rc_inc_guarded`** (`heap.rs:191-219`):

```
v4 = call_indirect ...        ; (f 5) = neg(5) = -5
v5 = iconst.i64 1024          ; NULLARY_THRESHOLD_I64 (= NULLARY_TAG_THRESHOLD)
v6 = icmp ult v4, v5          ; is result < 1024 unsigned?
brif v6, <skip>, <rc>
<rc>:
v7 = iadd_imm.i64 v4, 8       ; HeapHeader::RC_OFFSET — treat result AS A POINTER
v9 = atomic_rmw.i64 add v7    ; RC-increment at [result + 8]  <-- SIGSEGV
```

The `< 1024` guard is the immediate-vs-pointer heuristic: values below the
nullary-tag threshold are treated as small immediates (RC skipped), everything
else as a heap pointer (RC'd). **A negative Int `neg(5) = -5 = 0xFFFF…FFFB` is
`>= 1024` unsigned, so the guard fires and `atomic_rmw add` dereferences
`0xFFFF…FFFB + 8` → SIGSEGV.** A concrete `Type::Int` classifies as `NeverHeap`
(heap.rs:447) → no RC, no guard, no crash.

### Why it's value-dependent (the smoking gun)

Sweeping the returned value against the SAME source confirms the threshold
exactly (binary at HEAD 7de2254):

| Returned value | `>= 1024` unsigned? | Result |
|---|---|---|
| `neg(0) = 0` | no | exit 0, clean |
| `neg(1..8) = -1..-8` | yes (huge) | SIGSEGV |
| `add3(1000) = 1003` | no | exit 235, clean |
| `add3(2000) = 2003` | yes | SIGBUS |

Source control flow is identical across all rows — a value-dependent crash is
the signature of a non-pointer being dereferenced as a pointer.

### Reduction ladder (each rung confirmed)

| Shape | Result |
|---|---|
| ONE hop `(defn h [f] (f 5))`, neg result | exit 251 (= -5), **clean** |
| TWO hops, neg(5) = -5 | **SIGSEGV** |
| TWO hops, neg(0) = 0 | exit 0, clean (0 < 1024) |
| TWO hops, EITHER hop result annotated `:Int` | exit 251, **clean** |
| TWO hops, NO trait / NO constraint (plain `(sub-i64 0 x)`) | **SIGSEGV** |
| TWO hops, ALL in one file (no cross-module) | **SIGSEGV** |
| TWO hops, non-constrained `plain` fn | **SIGSEGV** |
| Original stdlib `vec-map`+`abs`+`Num` composite | **SIGSEGV** |

So: the constraint, the trait, the cross-module split, the Vec, and the wrapper
fn are all **incidental** — they merely happen to produce a polymorphic-result
intervening hop and a negative/large return value. Annotating any hop's result
`:Int` resolves the type var → `NeverHeap` → no crash, which is the cleanest
confirmation of the root cause.

### Is the /stdlib "second layered bug" real?

The /stdlib free-standing reduction surfaced "no impl of trait Doubler for type
Int" — a cross-module trait-impl-resolution error from the wrapper's scope.
**That is a separate trait-resolution issue and is NOT on the critical path to
the SIGSEGV.** This /qa reduction removed the trait entirely and still
reproduces the crash, so the SIGSEGV and the trait-resolution wrinkle are
indeed distinct, as /stdlib suspected. The trait-resolution error is NOT
reproduced here (it would need its own repro if it is to be tracked as a
defect); it is plausibly the ordinary "impl must be in the trait's defining
module or chain-reachable" rule (Decision 0045) biting an ad-hoc reduction,
rather than a compiler bug. Recommend /stdlib re-confirm whether the
trait-resolution error survives a *correct* impl placement before filing it
separately.

### Owning crate(s) — one bug, one owner

**ONE bug. Owner: `/backend` (`cranelisp-backend`).** The crash is entirely in
backend RC codegen (`heap.rs` + `apply.rs`). Re-pointed from `/typecheck`.

There are two candidate resolutions; either closes the crash:

1. **Backend (the no-crash / soundness fix):** the `Mixed` guard's
   `< 1024`-means-immediate heuristic is **unsound for unboxed `Int`** — a
   negative or large Int is a valid immediate that exceeds the threshold and is
   misread as a pointer. The clean structural fix is to never emit a
   maybe-pointer RC for a value whose unboxed representation can collide with
   the pointer range. With the current untagged i64 representation, an unboxed
   `Int` is genuinely indistinguishable from a pointer at runtime, so the guard
   CANNOT be made sound by inspecting the value — the type must be known. That
   pushes the real fix to (2), OR to a representation change (tagging
   immediates), which is a large feature, out of scope for a no-crash fix.

2. **Typecheck (the monomorphise-the-hops fix):** ensure that a polymorphic
   function reached as / containing a fn-value whose concrete instantiation is
   known at the outer call site is **monomorphised** so the result type is
   concrete (`Int`) at codegen, classifying as `NeverHeap`. This is the same
   mono-wiring the FIXME originally hypothesised, but generalised beyond
   constrained/trait fns to *all* polymorphic-result hops. This is the correct
   long-term fix and matches how single-hop already behaves correctly when the
   call monomorphises.

### Fix-shape estimate (for the user's fix-depth decision)

- **Bounded no-crash-now (0354-style structural → clean behaviour):**
  **NOT cleanly available at the backend layer with the current untagged
  representation.** Unlike 0354 (a null GOT slot → emit a friendly error
  instead of calling null), here the corrupted value IS the legitimate result;
  there is no null sentinel to gate on. A backend-only mitigation would have to
  suppress the `Mixed` guarded-RC entirely for any value that *could* be an
  unboxed scalar — i.e. treat `Mixed` results conservatively as NeverHeap —
  which would **leak memory** for genuinely-heap polymorphic results (the RC
  inc that balances a later dec would be dropped). That is a correctness
  trade, not a clean no-crash. So the honest read: there is **no bounded
  no-crash backend fix** that is also leak-free.

- **Deep fix (monomorphise polymorphic-result hops — typecheck + backend
  mono-wiring):** the durable correct fix. Medium-to-large depth: it extends
  monomorphisation to fire for fn-value-carried polymorphic functions reached
  through HOF hops (the call site's concrete instantiation must propagate to
  the intervening template). This is the "deep mono-wiring feature" the FIXME
  anticipated, generalised. Estimated multi-day.

- **Carry recommendation:** because neither a clean no-crash nor a small fix
  exists, this is a genuine "carry as a known-defect guard" candidate unless
  the user wants the mono-wiring feature now. The failing-not-ignored repro
  (`tests/regression.rs::fixme_0373_polymorphic_result_fn_value_two_hops_no_crash`)
  guards it either way.

### Test (durable repro)

`tests/regression.rs::fixme_0373_polymorphic_result_fn_value_two_hops_no_crash`
— failing-not-ignored e2e. Asserts the 5-line free-standing repro exits 251
(= neg(5) = -5 as u8); currently fails with "expected exit 251, got None"
(signal-killed). `// spec: spec/07-traits.md §7.8`.
