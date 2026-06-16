---
number: 0373
target: /typecheck
filed_by: /stdlib
filed_at: 2026-06-16
sprint_filed: 83
refers_to: crates/cranelisp-typecheck/src/program.rs (pass4_monomorphise / collect_imported_constrained_calls), spec/07-traits.md §7.8.2, design/arch/test-discovery.md
status: open
---

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
