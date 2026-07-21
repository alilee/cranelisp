---
number: 0793
target: /design (int)
filed_by: /review
filed_at: 2026-07-21
sprint_filed: 115
refers_to: src/session_v4/lifecycle.rs:254 (the PRIMITIVES_TABLE session-init
  install) vs design/int/prelude-table-write-isolation.md §2.1/§2.4 census +
  src/imports.rs census-comment mirror — rider on FIXME 0740.
status: open
---

# Census rider — the third session-init public-entry seam is `PRIMITIVES_TABLE`, not covered by the bootstrap sweep

## Severity
Suggestion (benign by construction; disposition-completeness only — fold into
the 0740 census-row edit rather than scheduling a separate pass)

## Issue

The W6 `/dev`(src) change-set closes the code half of 0740: `platform.rs` ROUTES,
`bootstrap.rs::mount_synthetic_modules` is a named legal-skip carrying an
asserting sweep. Applying 0740's own standard once more surfaces one further
session-init seam that the census does not name and the sweep does not reach:

`src/session_v4/lifecycle.rs:254` installs
`(*cranelisp_primitives::PRIMITIVES_TABLE).clone()` into the session
`symbol_tables` at init — a whole live-module table of **public** entries,
mounted immediately before `mount_synthetic_modules` (`:270`). The new sweep
`bootstrap::tests::bootstrap_seeds_pass_the_terminal_closure_gate` runs against
`fresh_tables()`, which pre-creates an EMPTY `primitives` table, so none of
those entries is swept. That is correct for what the test *claims* (it asserts
over "every entry the bootstrap seeds"), but it means the census's closure
claim, once the two 0740 rows land, is still one seam short of total.

It is benign for the same reason the other two are: every `PRIMITIVES_TABLE`
entry is `primitives`' own definition (non-`Import`), so
`check_terminal_closure`'s own-def arm admits it with no map read, and the
install is single-threaded at init before any worker spawns. It is also
arguably a different *shape* — a whole-module table install rather than an entry
insert into an existing live table — which may be the right disposition wording.

## Proposed resolution

When `/design`(int) writes the §2.1/§2.4 census rows 0740 asks for, add a third
row (or extend the scope-boundary statement to cover it):

`session_v4/lifecycle.rs::PRIMITIVES_TABLE install` — public, LEGAL-SKIP,
whole-table mount at session init, pre-worker-spawn, own-definitions only
(own-def arm). Then the §2.4 structural grep resolves for all three
session-init seams instead of two, and `/dev` re-syncs the `src/imports.rs`
census-comment mirror in the same pass.

## Context

`/review`(src) S115 W6, change-set `fab0b9ac`; rider on FIXME 0740, which is
already open and `/design`(int)-targeted. Filed separately only so the row is
not lost inside 0740's long correction thread — it should be actioned in the
same edit and both files retired together.

The bootstrap legal-skip itself was reviewed adversarially and is **sound**:
the sweep iterates `module.value().symbols` (the full `HashMap`, not the
`defined_symbols()` view) across every module `mount_synthetic_modules` touches,
so its coverage of that seam is total, not a sample; `D(M) = {}` is genuinely the
strictest closure (the unknown-`D` permit arm is unreachable, and the own-def /
intra-module-self-alias arms bypass `D` entirely, so no stricter `D` exists);
and the skip is detection-equivalent to routing — routing would only differ in
enforcing at the write site rather than in CI, which is the disclosed and
correct tradeoff for an init path made fallible for an unreachable rejection
(Principle 6/8).
