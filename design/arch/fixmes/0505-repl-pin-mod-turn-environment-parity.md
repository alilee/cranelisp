---
number: 0505              # 0503/0504 were used and resolved in S102 Phase 3 (see sprints/SPRINT.md §FIXME debt); next free is 0505
target: /repl
filed_by: /qa
filed_at: 2026-07-03
sprint_filed: 102
refers_to: repl/spec.md §3.1 (/mod row) + §8 (module demo scenarios), spec/08-modules.md §8.8, design/arch/fixmes/0487-int-module-namespace-redefinition-scope-gaps.md
status: open
---

# Pin the `/mod` turn-environment parity invariant as a normative spec row

## Issue

FIXME 0487's underlying invariant — **"a module-namespace turn (`/mod M` +
form) compiles in the same environment the module's file body was compiled
in"** (implicit prelude values, prelude type aliases, and the module's own
imports all in scope) — is not stated anywhere in `repl/spec.md` in testable
form. The S101 coverage audit classified this as part of the 0487 miss
(pattern P5: nothing pinned it, so no parity test could exist), and the S102
qa plan (`tests/plan/s102-test-plan.md` §1.3) committed to flagging the
spec-side row if neither /spec nor /repl pinned it in Phase 3 — neither did.

The S102 L-S3 lane (`tests/repl_mod_devloop.rs`) now tests the invariant
anchored to `spec/08-modules.md §8.8` (implicit prelude for module bodies)
as the nearest normative statement, plus `repl/spec.md §3.8`/§3.6/§17.6.1
for the FQ-introspection-argument half. Once /repl pins the invariant (and
the FQ-argument grammar for `/sig`//`/info`//`/refs`//`/source`//`/doc`) in
`repl/spec.md`, those tests re-anchor to the new section.

## Proposed resolution

Add to `repl/spec.md` (likely as a subsection under the `/mod` command or a
new §3.x): (1) the turn-environment parity MUST; (2) the introspection
commands' argument grammar MUST accept module-qualified names (the
transaction's own reports print them); (3) `/sig` on an imported name prints
the full §3.8 primary line, not only the `; imported from` note. Then
annotate with the L-S3 test citations and notify /qa for the re-anchor pass.

## Operational implication / Context

Fix-side owner is /int (Block A4, CS-D3a/b + CS-0487 per
design/int/s102-defect-wave.md); this FIXME is only the missing normative
pin, so the tests stop citing an adjacent spec.
