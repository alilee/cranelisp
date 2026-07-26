---
number: 0916
target: /qa
filed_by: /examples
filed_at: 2026-07-26
sprint_filed: 118
refers_to: tests/trait_method_tail_s116.rs (adjacent, different subject — tail
  CLASSIFICATION, not tail CALLS); tests/tco_tail_arg_alias_uaf.rs;
  design/arch/fixmes/0907-*.md §3 (found while building a non-IO control);
  spec/05-functions.md (TCO guarantee)
status: open
---

# A self tail call in a `match` arm SIGSEGVs at ~1,000 depth when the scrutinee is a trait-method call

## Severity

Important — silent stack exhaustion (SIGSEGV, no diagnostic) at a depth 400×
below the plain-function control, on an ordinary shape: "transform the value,
match the result, recurse." Not reached by any committed example or test today,
which is why it has not been seen; found by `/examples` while constructing a
non-IO control for FIXME 0907.

## Minimal repro (9 lines, PrimitivesOnly, verified at HEAD `a1f5b2b7`)

```
(import [primitives [IO Pure sub-i64 eq-i64]])
(deftype (Option a) None (Some [:a val]))
(deftrait (Functor f)
  (fmap [:(Fn [a] b) func :(f a) x] (f b)))
(impl (Functor f) (Functor Option)
  (defn fmap [g o] (match o [None None (Some x) (Some (g x))])))
(defn go [n acc]
  (if (eq-i64 n 0)
    (Pure acc)
    (match (fmap (fn [z] z) (Some n))
      [(Some v) (go (sub-i64 n 1) acc)
       None     (Pure 0)])))
(defn main [] (go 2000 7))
```

`cranelisp --run --no-cache` → **SIGSEGV** (rc `-11`), no output, maxRSS flat
(~27.9 MB) — a stack fault, not a heap exhaustion.

## The A/B — one token apart

The control replaces the trait method with a plain `defn` of the **same body**;
everything else is byte-identical.

```
(defn fmapo [g o] (match o [None None (Some x) (Some (g x))]))
...
    (match (fmapo (fn [z] z) (Some n))
```

| Scrutinee | 100 | 800 | 1200 | 2000 | 20,000 | 400,000 |
|---|---|---|---|---|---|---|
| trait-method `fmap` | ok | ok | **SIGSEGV** | SIGSEGV | SIGSEGV | SIGSEGV |
| plain `defn fmapo` | ok | ok | ok | ok | ok | **ok** |

A third control with **no call at all** in the scrutinee (`(match (Some n) …)`)
is also fine at 20,000. So the discriminator is precisely *trait-dispatched call
in the scrutinee position of a `match` whose arm holds the self tail call*.

Threshold ~1,000 frames against an 8 MB default stack is consistent with TCO
being lost and each retained frame costing several KB in the debug profile —
but that is inference, not measurement; the locus is unattributed here on
purpose.

## Why `/examples` is not attributing it

Two plausible loci with no evidence to separate them: backend (the tail-call
transform declines when the arm's dominator contains a dispatched call) and
typecheck/mono (the trait instance is not resolved to a direct callee, so the
call is not recognised as tail-eligible). Per root `CLAUDE.md`
§"Cross-Skill Changes", cross-skill handoff needs the repro — which is above —
and contested attribution routes to `/qa`.

## Asks

1. `/qa` attribute; `/testing` land the A/B above as a failing-not-ignored
   pair (trait scrutinee RED at n=2000, plain-fn control GREEN at n=400000 —
   the pair is what makes the finding legible; a lone RED reads as "deep
   recursion overflows", which is exactly what it is not).
2. The guard should assert on the exit **status** (not just a value), since the
   failure mode is a signal.

## Not this FIXME

The trait-instance **leak** over `IO` measured in the same session belongs to
FIXME 0907 §3 (appended there). This file is only the SIGSEGV.
