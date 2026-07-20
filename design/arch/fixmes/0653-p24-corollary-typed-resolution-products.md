---
target: /arch
status: open
filed: 2026-07-19
filed_by: /sprint (quoting /review, S113 W2a close verdict)
---

# P24 corollary: resolution products travel typed — bare name past its resolution seam is a defect marker

## Evidence (S113, three instances in one sprint)

Three W2a defects shared one shape: a resolution *product* carrying FQ identity was
narrowed to its bare name, and the bare name later re-resolved in whatever scope
happened to be ambient:

1. D2 — `method_to_trait_with_state` discarded `trait_origin`'s module (dispatch impl-lookup).
2. `verify_constraints` (`monomorphise.rs:743`) — held `FQTraitName`, re-resolved `.name` bare.
3. `try_resolve_trait_method` dispatch-type — re-resolved the written sig type in caller scope.

All three were found by grepping for the signature `(&CheckState, &bare-name)` — every
helper with that shape is an open invitation to ambient re-resolution. P24 names the
rule but nothing makes violations unrepresentable.

## Recommendation (/review, verbatim in substance)

Make resolved identity the only currency past the resolution seam:

- Post-resolution paths take `FQTraitName`/`FQTypeName` (both types exist already).
- Audit typecheck's remaining bare-name+state helpers into two explicit camps:
  legitimate pre-resolution seams vs. re-resolvers to delete. The now-`dead_code`
  `has_impl_with_state` is the template — production couldn't reach it, so the
  compiler said so. (`resolve_trait`, `resolve_type` to be classified; diagnostics-only
  renderers get a pass.)
- Scribe the P24 corollary: "resolution products travel typed; a bare name past its
  resolution seam is a defect marker" — so instance 4 is a compile error, not a
  review find.

## Strengthened evidence (S113 W2 close, /review — six confirmed instances, two seam-families)

The class is one structural defect, not scattered bugs:

**Identity-from-written-name**: (1) backend TCO fp1 name-match (deleted); (2) the
mono-recheck self-call classifier (fixed — the carrier-presence consumption is the
template); (3) the drain's `mangle_sig(base_name…)` at `register.rs:851` (qualified
`(mlib/h 1)` → doubled-key miss); (4–5) the inner scanners
(`resolve_inner_constrained_calls`, `monomorphise_inner_parametric_hops`) + pass-4
collectors (`collect_local_parametric_calls` siblings) — these SILENTLY redirect
§4.6 shadows of poly/constrained callees to wrong values.

**Resolve-once-home-discarded**: D2 dispatch, `verify_constraints`, caller-scope
type resolution (all fixed W2a).

## Second prong (added per /review): scan discipline

Any body-scan that mints or records dispatch may use the AST name only as a
*trigger for a keyed read* of the per-span recorded verdict
(`resolved_targets`/`resolved_calls`) — never as the identity itself. Fix 1
(carrier-presence consumption) is the canonical shape. The 0632 battery enumerates
all six sites so the sweep is checkable. /review recommends this as a NAMED /arch
work item, not just a battery row.

## Third prong (USER-DIRECTED, 2026-07-19): the phase-boundary completeness gate

User statement (verbatim in substance, during the 0655 root-cause review): *"the backend
is supposed to have all names resolved to FQ canonical — otherwise unrepresentable."*

Today that invariant is enforced by convention + loud keyed-miss (a dropped carrier
surfaces as a codegen-time `undefined function` — wrong phase), not by construction.
The check-gate-leak class (two instances this sprint: D2's original leak; 0655 face 3 /
MC-X3) is precisely "typecheck completed while a non-local reference was carrier-less."

Required: an **exhaustive resolved-ness gate at typecheck exit** — every Var/Apply in
the checked program proves (a) local-slot-bound or (b) FQ-carrier-present; anything
else is a LOCATED TYPECHECK error, never reaching codegen. Same enumeration-completeness
shape as the RT-4 section guard and the mono-harvest totality assert. With the gate,
a future producer bug that drops a carrier fails at the correct phase, and the
malformed "checked but unresolved" program state becomes unrepresentable downstream.

**Prong-3 refinement (USER-DIRECTED, second statement): the dichotomy must be enforced
IN THE TYPE, not by a checking sweep.** Audit result: `FQSymbol`/`FQTypeName` are clean
(no sentinel-module convention; test-asserted non-empty). The guilty encoding is
`MonoExpr::Var/Apply { resolved_target: Option<FQSymbol> }` — `None` conflates
"local by design" with "unresolved by producer bug"; the backend disambiguates by
convention (`variables` consult, hard-error on double miss since W2b). Required shape:
a closed sum at the checked-program boundary — `Ref::Local(slot) | Ref::Global(FQSymbol)`
— constructed only by typecheck; "unresolved" has NO constructor. The gate then isn't a
sweep, it's the constructor. Also flag for the same S114 audit: the `mono_expr.rs:664`
"no concrete type" sentinel comment, and the `{home}/{bare}${sig}` string-embedded
mangle identities (already fenced in the 0632 register) — the remaining
convention-in-value candidates.

/arch: ratify as P24 corollary prong 3 (typed enforcement, sweep as migration aid only);
S114 work item alongside the helper-classification sweep (it IS the sweep's acceptance
check). This is a `cranelisp-types` carrier-shape change → /arch authors; schema impact
assessed at design time.

## Suggested disposition

S113 Phase-7 principle scribe (corollary text) + the helper-classification sweep as an
S114 slot (pairs naturally with the parked P26 full typecheck sweep and the 0590
resolver-mirror convergence, both already S114-scheduled).
