---
id: ACT-1002
title: Route the rejected constructor pattern of a type whose name another type's constructor shares
status: open
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-28
refers_to:
  - crates/cranelisp-typecheck/src/infer.rs
  - crates/cranelisp-typecheck/src/checker.rs
  - crates/cranelisp-typecheck/src/infer/tests.rs
  - spec/08-modules.md
---

## Request

The user ruled fix (2026-09-28). `design` (`cranelisp-typecheck`) shapes the
private correction, then `dev` realizes it. The evidence allocation is
[ACT-1002 fix readiness](../../tests/plan/s122-evidence-delta.md#act-1002-fix-readiness--evidence-allocation-2026-09-28).

## Defect

- **Requirement.** Spec §8.6.4 lets a type and another type's constructor
  share a spelling, and registration accepts it. §8.5.2 says `Type.Ctor`
  names the type's constructor. A match on that type's constructors is a
  conforming program.
- **Observed.** The world is `(deftype Qtok (Qa [:Int n]) Qb)` with
  `(deftype Qwrap (Qtok [:Int x]))`.
  - The pattern `(match Qb [(Qtok.Qa n) n _ 0])` is rejected with
    `unknown type in constructor: test/Qtok`.
  - The bare pattern `(Qa n)` fails identically. It never reaches the
    dotted core.
  - In the same world the call `(Qa 1)` succeeds, typed `test/Qtok`.
- **Class.** `wrong-reject`, confirmed by M0.
- **Locus.** `crates/cranelisp-typecheck/src/infer.rs::instantiate_ctor`,
  where the error is raised (observed).
- **Mechanism: observed at its seam by M0**
  (`.local/s122-act1002-dev/m0-seam-probe.log`).
  - `instantiate_ctor` already holds the canonical `FQTypeName`.
  - It re-resolves the bare spelling through
    `checker.rs::lookup_type_def_in_module`, which reaches the unique-candidate
    `scope_resolve_in`.
  - The type and the constructor's bare projection make that lookup
    `Ambiguous`, and `.ok()` turns the error into "unknown type".
  - **Falsifier.** At that seam, the lookup returns the type while the
    pattern still fails.
- **Not introduced by ACT-1001.**
  - No S122 hunk touches `instantiate_ctor`, `lookup_type_def_in_module`,
    `resolve_terminal_entry_and_home` or `scope_resolve_in`, and
    `cranelisp-types` is unchanged against `0272a5d9`.
  - The bare-pattern arm changed only by an `Ok(..)` wrap.
  - Limit: the bare probe ran on the post-fix tree only. Independence rests
    on the probe plus that hunk census.
- **Unmeasured.** Other `lookup_type_def_in_module` readers, such as
  exhaustiveness, may share the mechanism. The end-to-end face is predicted
  and has not been run.

## Evidence

- **Guard.** `crates/cranelisp-typecheck/src/infer/tests.rs::dotted_pattern_under_type_parent_contested_by_constructor_resolves`
  stays RED and unignored. Its candidate control passes, and the failure is
  the message above.
  - It carries
    `// defect: class=wrong-reject locus=crates/cranelisp-typecheck/src/infer.rs::instantiate_ctor found=S122 owner=/dev`.
  - Its ACT-1001 core leg is asserted separately; see
    [S122 evidence](../../tests/plan/s122-evidence-delta.md#act-1001-p-1-final-adequacy-2026-09-28).
- **Discriminating control.** The bare-pattern probe is recorded in
  `.local/s122-act1001-f1-dev/probe-bare-pattern.log` and is not committed.
  A fix lands its bare-pattern unit cell under METHOD §2.2.
- **Full suite.** Run on `0272a5d9` plus the dirty tree: 6251 run, 6249
  passed, 1 skipped. The two failures are DT-1 and this guard.

## Final adequacy — 2026-09-28

- `qa` judged the correction **adequate**. `review` raised no blocking
  finding. See
  [ACT-1002 final adequacy](../../tests/plan/s122-evidence-delta.md#act-1002-final-adequacy-2026-09-28).
- M0 confirmed the mechanism at its seam, so the attribution is no longer
  provisional. The guard, M2, M3 and T1 went from RED to GREEN.
- **Retire this action** (delete the file) in the change-set that commits the
  fix, once all of these hold:
  - the `fixed=S122/<sha>` stamps and the §8.5.2 and §8.6.4 bands are applied;
  - review's A1 is either recorded by `design` in `typecheck.md` §11 or
    converged by `dev`;
  - A2 and A3 are either done or filed as actions to their owners.
- Retiring it leaves nothing untracked:
  - The M4 gate and the type-position residuals live in
    `design/typecheck/typecheck.md` §11.
  - The warm-REPL echo lead is
    [ACT-1003](ACT-1003-contested-type-deftype-echo-intake.md).

## Completion evidence

- The observed seam (M0) confirms or refutes the mechanism.
- The guard, the bare-head and exhaustiveness module cells, and the one
  required e2e cell (T1) go from RED to GREEN, per the readiness allocation.
- The readers are assessed there; any left uncorrected is recorded as a
  residual with its falsifier.
- The allocated gates pass and `qa` records final adequacy.

### Acceptance handoffs applied — 2026-09-28

A1's residual and A3's named falsifier are recorded in the typechecker
design; A2's comment-only repairs pass crate check and formatting. The
§8.5.2/§8.6.4 bands and T1's `fixed=S122` stamp are applied. The correction
is accepted. Appending the actual commit hash and retiring this action await
an authorized checkpoint commit; no commit has been made.
