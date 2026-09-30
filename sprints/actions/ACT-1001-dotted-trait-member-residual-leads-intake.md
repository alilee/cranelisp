---
id: ACT-1001
title: Guard the confirmed ambiguous-parent wrong accept; route the unreproduced dispatch-index hazard
status: deferred
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-27
refers_to:
  - crates/cranelisp-typecheck/src/checker.rs
  - crates/cranelisp-typecheck/src/traits/dispatch.rs
  - crates/cranelisp-typecheck/src/traits/impl_check.rs
  - tests/spec_08_modules.rs
  - crates/cranelisp-types/src/resolve.rs
  - spec/08-modules.md
  - spec/07-traits.md
---

## S122 disposition (user-approved 2026-09-30)

Under the [approved S122 disposition](../../tests/plan/s122-evidence-delta.md#final-disposition-proposal-2026-09-30):

- **P-3 (K5, N2) and P-2 (K5, N3) are carried to S123.** First deferral. P-1 is closed; its evidence below stands.

## Request

Two leads came out of the ACT-1000 correction. Neither was introduced by
ACT-1000. The adequacy record is
[S122 evidence](../../tests/plan/s122-evidence-delta.md#act-1001-basket--classification-2026-09-27).

- **P-1** is corrected and accepted by QA; see
  [P-1 final adequacy](#p-1-final-adequacy--2026-09-28). What remains open
  here is P-2 and P-3.
- **P-2** did not reproduce. `design` owes a ruling on the index source, and
  the user decides whether the §7.4.2a selection gap gets cells.

### P-1: an ambiguous parent still resolves its dotted member — confirmed

- **Requirement.** Spec §8.6.4 and §8.8.1 merge prelude candidates with
  explicit-import candidates; neither takes precedence. Spec §8.5.2: "If the
  parent spelling … is itself ambiguous, its canonical module qualification
  is required first."
- **Observed.** `a1/subject` imports trait `T` from `tm` under a prelude
  that defines its own `T`, then calls `T.m`. It exits 104, so the prelude
  impl ran. The spec requires rejection.
  - Control `a1/ctl_prelude` (no import) exits 104: the prelude route is live.
  - Control `a1/ctl_qualified` (`tm/T.m`) exits 5: the import route is live.
  - The subject's 104 therefore picks the prelude route, not the import.
    The recorded falsifier (exit 5, silent import precedence) did not occur.
- **Mechanism: symptom confirmed; one candidate refuted; the other
  source-predicted.** See [P-1 readiness](#p-1-readiness--2026-09-28).
- **Type heads.** A prelude-defined type's literal `Type.member` key is
  predicted to reach past an ambiguous parent the same way. This is
  unobserved and has no cell.

#### P-1 allocation — `test`

One cell in `tests/spec_08_modules.rs`, failing and not ignored:
`dotted_member_under_ambiguous_trait_parent_is_rejected_neg`.

- **Annotations.**
  - `// spec: spec/08-modules.md §8.5.2 — an ambiguous parent spelling needs
    its module qualification before a dotted member resolves; §8.6.4 prelude
    and import candidates merge`
  - `// defect: class=wrong-accept locus=crates/cranelisp-typecheck/src/checker.rs::dotted_member_identity found=S122 owner=/dev`
  - Put the provisional locus in the comment, and correct it if the
    discriminating control points elsewhere.
- **Fixture.** Use `.prelude("(export [primitives [*]])\n(deftrait T (m [x]
  self))\n(impl T Int (defn m [x] (add-i64 x 100)))\n")`, and `tm.cl` as in
  `imported_trait_dotted_method_resolves_via_import_and_prelude_reexport`.
  Its impl adds 1.
- **Controls.** Assert both first. Either failing invalidates the cell.
  - Prelude only: `(defn main [] (Pure (T.m 4)))` exits 104.
  - Qualified: `(import [tm [T]])` plus `tm/T.m 4` exits 5.
- **Subject.** `(import [tm [T]])` plus `(T.m 4)`. The
  [readiness repair](#diagnostic-assertion) supersedes the original
  `ambiguous` assertion. On the current binary the subject exits 104, and
  the failure message names that exit.
- **Discriminating control.** Record the result in the cell comment or the
  test report. It gates nothing.
  - In the same fixture, a bare, non-dotted use of `T` resolves its trait
    head; for example, `(impl T Float (defn m [x] x))` with a trivial `main`.
  - If it rejects with an ambiguity, bare `T` is ambiguous and only the
    dotted route bypasses it, so the locus stands.
  - If it accepts, the prelude wins bare resolution, and the locus moves to
    `cranelisp-types/src/resolve.rs`. Return that to QA for attribution.
- **Test only.** A unit cell comes with the fix under METHOD §2.2.

### P-2: the dispatch index is found by bare member name — not reproduced

- **Source.** `traits/dispatch.rs::try_resolve_trait_method_decl` takes the
  dispatch argument index from the canonical signature's `hkt_param_index`.
  That field is `None` for every conventional method, so
  `hkt_param_idx_for_method` runs for every conventional call. It scans
  visible trait declarations for the first method with the same bare name.
- **Observed.** Conventional `T` meets higher-kinded `A` (sorts before `T`)
  or `U` (sorts after), in both import orders.
  - `ctl_no_u`, `qualified_ta`, `qualified_tu`, `subject_ta`, `subject_tu`
    and `subject_ut` all exit 5.
  - No ordering dispatched on the wrong argument.
- **Limits of the negative.** The basket has no positive detection leg.
  - Nothing shows that the scan ever visits `A` or `U`.
  - "Not reproduced" is therefore evidence about these orderings, not about
    the fallback.
  - The hazard stays in source, graded asserted-with-a-named-falsifier. The
    falsifier is a same-named HKT method that the scan reaches before the
    conventional one.
- **Routed.**
  - `design` (`cranelisp-typecheck`) rules whether the index is read only
    from the canonical declaration. That would make the hazard structural.
  - The user decides whether §7.4.2a's same-named selection gap gets cells.

### A2 partial application — observed, not a lead

- `a2/subject_dotted_full` and `a2/subject_dotted_partial` exit 5. Their
  independent control `a2/ctl_qualified_partial` also exits 5.
- Partial application through `T.m` reaches the ACT-1000 dispatch seam
  correctly. This is not intake.
- `a2/ctl_bare_partial` is an invalid fixture: `undefined variable: m`.
  - `(import [tm [T]])` does not bring the member `m` into bare scope; spec
    §8.3 imports members by name or `T.*`.
  - The leg tested nothing. It invalidates only itself, because the other
    a2 legs do not depend on it.
  - The bare auto-curry route is unmeasured and has no named wrong outcome.

## Completion evidence

- P-1: met, with the conditions listed under
  [P-1 final adequacy](#p-1-final-adequacy--2026-09-28).
- P-3: the user rules fix or defer.
- P-2: `design`'s ruling on the index source is recorded, and the user
  rules on §7.4.2a selection cells.

## Permanent reproduction — 2026-09-27

Test records `tests/spec_08_modules.rs::dotted_member_under_ambiguous_trait_parent_is_rejected_neg`
as an unignored RED on binary `e8c43e58…29bbf3`: the subject exits 104,
after the prelude-only and qualified controls pass with 104 and 5. The
ACT-1000 neighbour passes in the same focused run (one pass, one intended
failure). No production code changed and no full suite was repeated.

The non-gating bare-head control `(impl T Float (defn m [x] x))` exits 0
without the import. With `(import [tm [T]])` it exits 1 with
`unknown trait: T`. It does not silently select the prelude, and it does
not report ambiguity (P-3 below).

## P-1 readiness — 2026-09-28

The user ruled fix. This settles the locus and the diagnostic assertion.

### Attribution

- **Refuted: the prelude wins bare resolution.** The bare-head control
  succeeds without the import and rejects with it, so bare `T` is not
  silently resolved to the prelude. The locus does not move to
  `cranelisp-types/src/resolve.rs`.
- **Retained, provisional: the dotted route bypasses the parent's
  ambiguity.** In source:
  - `checker.rs::dotted_member_identity` resolves the parent with
    `scope_resolve(...).ok()?`, so the parent's `ResolveError::Ambiguous`
    becomes `None`.
  - The literal `T.m` spelling then resolves through ordinary scope. In
    dispatch, `traits/dispatch.rs::try_resolve_trait_method` tries
    `resolve_terminal_fq_scoped` before the dotted core. Only the prelude
    has a literal `T.m` key in `main`'s scope.
  - This mechanism is read from source and has not been observed at its
    seam. The locus token stays `checker.rs::dotted_member_identity`,
    marked provisional.
- **Falsifier.** At the seam, the dotted core returns the prelude
  declaration, or the literal route does not answer `T.m`. Either one
  returns the attribution to QA before any fix lands.

### Diagnostic assertion

- **What the spec requires.**
  - §8.5.2 and §8.6.5 require rejection: an ambiguous parent must be
    canonically qualified.
  - §8.6.5: "Diagnostics for ambiguity MUST list the surviving canonical
    alternatives." Rule 1 writes a canonical name as `home/name`.
  - The spec does not require the word `ambiguous`.
- **The current cell is miscalibrated.** It is stricter than the spec in
  one way and weaker in another.
  - The exit-status clause is vacuous. A successful program exits with
    `main`'s value, so 104 and 5 are both "not success".
  - All of the cell's discrimination therefore rests on the unspecified
    word `ambiguous`.
  - An `ambiguous` message with no alternatives would pass, although it
    violates §8.6.5.
- **Repaired condition** (acceptance evidence, §8.5.2 and §8.6.5):
  - The subject exits with neither 0, 104 nor 5.
  - Its combined output contains both `prelude/T` and `tm/T`, the
    surviving canonical alternatives for the parent.
  - This is satisfiable without new wording: the existing
    `ResolveError::Ambiguous` rendering lists candidates as
    `module/symbol`.
  - It stays RED for a fix that reports `unknown trait: T`, and for one
    that says "ambiguous" but lists no alternatives.

### `test` — mechanical handoff to `tests/spec_08_modules.rs`

Applies to `dotted_member_under_ambiguous_trait_parent_is_rejected_neg`.

1. Append `; §8.6.5 ambiguity diagnostics list the surviving canonical
   alternatives` to the `// spec:` line.
2. Keep the `// defect:` line unchanged. Its comment continues to mark the
   locus provisional.
3. Replace the subject assertion with `code != Some(104) && code != Some(5)
   && !subject.status.success() && text.contains("prelude/T") &&
   text.contains("tm/T")`, where `code = subject.status.code()` and `text`
   is not lowercased.
4. The failure message names the two alternatives and keeps the 104 and 5
   explanations.
5. Rerun the focused pair. Expect the cell RED at the subject, on exit 104,
   with both controls passing, and the ACT-1000 neighbour GREEN. Rerun
   `tests/plan/spec_link_check.py`.

### `dev` (`cranelisp-typecheck`) — module evidence and gates

- **U1, mechanism and fix, required.** Write this in
  `crates/cranelisp-typecheck/src/checker/tests.rs`, and observe it RED
  before the fix.
  - Setup: prelude trait `T` with method `m`, and an imported distinct
    trait `T`.
  - The dotted `T.m` must not resolve through either the dotted core or
    the literal-key route.
  - The surfaced error lists both canonical parents.
  - The pre-fix observation is also the seam observation. Stop and return
    to QA if it contradicts the attribution.
- **U2, type-head twin, required.** Build the same shape with a type parent,
  for example a prelude type and an imported type sharing a spelling, each
  owning a constructor `C`.
  - `dotted_member_identity` shares one arm for type parents, and the
    type-head route is predicted but unobserved.
  - Report whether U2 is RED before the fix. If it is GREEN, the prediction
    is refuted: keep U2 as a guard and report it to QA.
- **Placement.** If the fix does not sit in the one shared dotted core,
  each consumer it touches needs its own unit leg. The consumers are value
  position (`infer.rs` dotted leg), pattern position (`checker.rs` dotted
  arm) and trait dispatch (`traits/dispatch.rs`).
- **Over-reject guards (existing; must stay green).**
  - Deduplication of the same terminal:
    `tests/spec_08_modules.rs::imported_trait_dotted_method_resolves_via_import_and_prelude_reexport`.
  - Dotted access when only the bare member is ambiguous:
    `same_named_ctors_dotted_value_position_both_resolve` and
    `tests/spec_06_pattern_matching.rs::same_named_ctors_dotted_pattern_position_disambiguates`.
  - Unit:
    `crates/cranelisp-typecheck/src/checker/tests.rs::dotted_trait_method_resolves_through_imported_trait_head`
    and `dotted_trait_method_needs_its_trait_in_bare_scope`.
  - The cell's own qualified and prelude-only controls.
- **Gates.**
  - `cargo nextest run --no-fail-fast -p cranelisp-typecheck`.
  - `--test spec_08_modules --test spec_08_name_shadowing --test
    spec_08_prelude_outer_scope --test spec_07_traits --test
    spec_06_pattern_matching`.
  - The full suite belongs to the phase gate.
- **Out of scope.** The P-3 mapping stays out of scope. The P-1 fix must not
  route dotted rejection through `resolve_impl_trait_ref`'s error mapping.

### P-3: ambiguous impl head reported as an unknown trait — intake

- **Source.** `traits/impl_check.rs::resolve_impl_trait_ref` maps every
  `scope_resolve` error except `PrivateInaccessible`, including `Ambiguous`,
  to `unknown trait: {name}`. The alternatives that §8.6.5 requires are
  dropped.
- **Observed.** The bare-head control above produces this. The rejection
  is correct; its diagnostic violates §8.6.5.
- **Class and owner.** Provisional class `error-swallow`; owner `/dev`.
- **Evidence.** This is outside the P-1 fix. It owes a committed repro
  under the defect rule once the user rules fix or defer.

P-2 (the HKT index source) is excluded from this readiness.

## P-1 final adequacy — 2026-09-28

**Verdict: accepted.** P-1 and the review corrections F1 and F3 are
corrected, and the evidence is adequate. The record is in
[S122 evidence](../../tests/plan/s122-evidence-delta.md#act-1001-p-1-final-adequacy-2026-09-28).

- **Acceptance cell.** `dotted_member_under_ambiguous_trait_parent_is_rejected_neg`
  is GREEN in the full run. It was recorded RED at exit 104 beforehand; no commit has been made.
- **Locus confirmed.** `dev`'s U1 and U2 observed the seam before the fix:
  the literal key answered after the parent's ambiguity was swallowed.
- **F1-b split.** `resolve_constructor_entry` now resolves `Qtok.Qa`
  correctly. The pattern then fails in `instantiate_ctor`, which is an
  existing defect, filed as ACT-1002 (fixed in `63605970`; retired
  2026-09-30).
  The F1-b cell stays RED as that defect's guard.
- **Condition still open.** One narrow core cell for the pattern leg must
  pass in a focused run. It needs no further QA or review cycle.
- **P-3 and P-2.** Neither is affected by the fix, and neither is fixed.

### P-1 final handoff complete — 2026-09-28

QA's supplied pattern-head core cell passes in the focused run. The paired
ACT-1002 pattern-instantiation guard remains RED for the separate known
reason. This closes the last P-1 acceptance condition. The fixed stamp and
QA-supplied coverage bands are applied; P-2 and P-3 remain open. No commit
or further fix is included.
