---
number: 0805
target: /testing
filed_by: /docs
filed_at: 2026-07-21
sprint_filed: 115
refers_to: spec/07-traits.md §7.1.1 ("The occurrence rule is broad, not a nullary
  corner" [S115], user ruling 2026-07-21) vs tests/nondispatchable_trait_method_0709.rs
  (nullary column only)
status: open
---

# The §7.1.1 occurrence rule is enforced only in its nullary column — the non-nullary variant is silently accepted, and no test covers it

## Severity

Defect (spec MUST unenforced; the fault leaks to a confusing downstream
diagnostic instead of being caught at the declaration)

## Issue

Spec §7.1.1 [S115] is explicit that the occurrence rule is scoped by
**occurrence, not by parameter count**: a method that mentions the implementing
type nowhere MUST be rejected *whatever its arity*, with reason string **"no
occurrence of the implementing type"**, and it names
`(deftrait Convertible (convert [:String s] Int))` as rejected on exactly the
same ground as `(deftrait Zeroable (zed [] Int))`.

Verified live against `target/debug/cranelisp` (2026-07-21, `/docs` Phase-6a
probes):

```
user> (deftrait Zeroable (zed [] Int))
Error: type error at 19..31: trait `Zeroable` method `zed`: no occurrence of the implementing type to dispatch on — a nullary method signature MUST return the implementing type (`(zed [] self)`), or take a parameter of it (a bare name `[x …]` or a `:self` annotation)   ← correct

user> (deftrait Conv (cvt [:String s] Int))
:user/Conv ; deftrait                                                            ← ACCEPTED, must be rejected
user> (deftrait Conv2 (cvt2 [:String s :Int n] Bool))
:user/Conv2 ; deftrait                                                           ← ACCEPTED, must be rejected
```

The acceptance then leaks. The impl is accepted too, and the fault surfaces
only at the call site as an unrelated-looking no-impl error:

```
user> (deftype Dog [:Int n])
user> (impl Conv Dog (defn cvt [s] 1))
impl user/Conv for user/Dog                                                      ← accepted
user> (cvt "hi")
Error: type error at 0..10: no impl of trait user/Conv for type primitives/String
```

That last message is actively misleading: there *is* an impl, and no impl of any
type could ever be selected, because the signature has nothing to dispatch on.

Note also that the emitted nullary message hard-codes "a **nullary** method
signature MUST …" — wording that will be wrong once the broad rule is enforced.

## Why this is a coverage-matrix miss

`tests/nondispatchable_trait_method_0709.rs` covers the family only in its
nullary column (`(zed [] Int)`), plus two accepted controls. The variant family
the spec names is *occurrence* × *arity*:

| | mentions `self` | mentions it nowhere |
|---|---|---|
| **0 params** | accepted (`(zed [] self)`) — covered green | rejected — covered RED→green |
| **1+ params, bare** | accepted (`(dsc [self] String)`) — covered green | n/a |
| **1+ params, all annotated non-self** | — | **rejected — NOT COVERED, silently accepted today** |

## Requested

A narrow failing-not-ignored repro for the uncovered cell — declaration-site
reject of `(deftrait Conv (cvt [:String s] Int))` carrying the reason string
"no occurrence of the implementing type" — plus the leak negative (an accepted
impl + call must not be reachable). Annotate `// spec: spec/07-traits.md §7.1.1`.
Extending `tests/nondispatchable_trait_method_0709.rs` with the arity column is
the natural home.

`/docs` will not teach the broad rule as enforced until the repro is green; the
6b guide text states the rule and marks the non-nullary case as not yet caught.
