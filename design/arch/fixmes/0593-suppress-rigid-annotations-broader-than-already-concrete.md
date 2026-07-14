---
number: 0593
target: /design
filed_by: /review
filed_at: 2026-07-14
sprint_filed: 109
refers_to: crates/cranelisp-typecheck/src/traits/impl_check.rs::check_defn_body_with_types (suppress_rigid_annotations) + FIXME 0591 parse gaps
status: open
---

# `suppress_rigid_annotations` covers first-and-only checks (trait-impl method bodies), not just already-concrete re-checks — latent acquire once 0591's parse gaps close

## Severity
Important (latent — currently fenced by a parse gap, no live unsoundness).

## Issue

The W6.2 rationale for `suppress_rigid_annotations` is "re-checking a body
against ALREADY-CONCRETE types — the caller has chosen the types (MUST-1)".
That is exactly right for `recheck_body_for_mono` (monomorphise.rs:714): the
template body already passed the rigid check as an ordinary defn, so the
suppressed re-check can only be sound.

It is NOT accurate for the other two call sites (impl_check.rs:505, :768):

1. **Trait-impl method bodies are FIRST-and-ONLY checked** under
   `check_defn_body_with_types` — there is no prior rigid pass. A written-var
   ascription in an impl method body (`(impl Doubler Int (defn twice [n]
   :a "hello"))`) would resolve FLEXIBLY and silently acquire, while the same
   text in an ordinary defn is a skolem-escape error (spec §3.3 MUST-3's
   worked negative). Divergence per definition-form variant — the
   variant-family uniformity lens.
2. **HKT impl param/ret types are not concrete**: `check_impl_method_hkt`
   builds `concrete_self = ADT(target, [fresh_vars…])` — the element
   positions are fresh FLEXIBLE vars, so "already-concrete" is false and a
   body written var could acquire an impl-scheme element var.

**Why this is latent, verified live at HEAD:** body annotations do not parse
inside impl-method defn bodies (`(impl Doubler Int (defn twice [n] :a
"hello"))` → `parse error: annotation missing expression` — a 0591-class
position gap not in 0591's list of four). The suppression is therefore only
reachable today through the sound mono-recheck path. The moment 0591 (or a
sibling fix) makes impl-method body annotations parse, the acquire becomes
live with no test guarding it.

Set/clear hygiene itself is correct and was verified: set at exactly one site
(impl_check.rs:819), restored unconditionally (:839, result captured in a
closure — error-safe), never active during `check_defn_body` (no call path
from `check_defn_body_with_types` back into the Pass-2 form driver).

## Proposed resolution

`/design` records the intended semantics of a written type var in a
trait-impl method body (is the impl method a "definition" for MUST-3? its
param/ret types are dictated by trait sig + impl head, but a body-only fresh
written var co-refers with nothing chosen by any caller). Likely shape:
suppression stays for the mono re-check; impl-method first-checks either get
their own written-var scope with body-annotation vars rigid, or the ruling
carves impl bodies out of MUST-3 explicitly (then `/spec` scribes it).
Coordinate with 0591 (the parse-gap closure is the trigger that makes this
live) and add the impl-method-body row to the §L matrix (`/qa`). Fold into the
0590 S110 convergence round if convenient — same file family.

## Context

Found by `/review` on b2bfb760 (S109 W6.2), dispatch priority 3 (the
suppress flag as the soundness-sensitive switch). The flag's stated invariant
("ONLY already-concrete rechecks") is what the crate CLAUDE.md and the
CheckState rustdoc now claim; this FIXME records where the claim and the call
sites diverge so the claim does not calcify into a trusted falsehood.
