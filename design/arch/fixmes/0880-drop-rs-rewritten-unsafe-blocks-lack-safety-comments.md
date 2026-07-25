---
number: 0880
target: /dev
filed_by: /review
filed_at: 2026-07-25
sprint_filed: 118
refers_to: crates/cranelisp-intrinsics/src/drop.rs (heap_access::read_i64 call sites rewritten in 64b4f1dd)
status: open
---

# Rewritten unsafe blocks in `drop.rs` lack per-block `// SAFETY:` comments

## Severity

Blocker

Per `.claude/commands/review.md` §Unsafe code audit: "`// SAFETY:` comment on
every `unsafe` block — explains why the invariants the unsafe operation
requires are upheld at this call site." The rules are absolute — a failed rule
is a Blocker until `/dev` responds. This is a delegated-review finding
(Codex, S118 W2a) verified against source by the adjudicating `/review`.

## Issue

Commit `64b4f1dd` (the §9/0850 convergence) rewrote the raw heap reads in
`drop.rs` onto `heap_access::read_i64` without adding the mandatory per-block
`// SAFETY:` justification. The touched-and-unjustified blocks at HEAD:

- `consume_slist` — lines 154, 155
- `consume_sexp` — lines 191, 192
- `consume_vec_with` — the aggregate block at line 243 (three reads + the
  element loop)
- `consume_io_tree` — lines 295, 298, 302
- `free_io_branches` — lines 420, 423, 430
- `dec_shallow_io` — lines 479, 481
- `consume_closure` — line 536

Each enclosing `pub fn` carries `# Safety` doc prose stating the CALLER's
contract, but that names the requirement, not why it is upheld at the exact
call site (e.g. "fields are read before the dec, so on the non-last-ref path
the block is still live"). The blocks were touched in this change-set, so the
unsafe audit applies to them even though the same shape predates it (the old
private `read_i64` sites were equally bare — the convergence was the moment to
carry the check).

Not in scope: `seam_precheck_armed` (diagnostics.rs) and the
`drop/rc_balance.rs` fixture helpers DO carry `// SAFETY:` comments; the
untouched `atomic_dec_rc`/`dealloc`/`transmute` sites in `drop.rs` predate the
change-set and were not rewritten by it (opportunistic coverage welcome but
not this finding's demand).

## Proposed resolution

Add a `// SAFETY:` comment to each listed block stating why validity,
alignment, and the readable range hold at that site (live-until-dec argument,
tag-dispatch precondition, `vec_new` buffer contract, Decision-11 closure
layout). Mechanical; no behavior change; no test impact.

## Context

S118 W2a delegated review of the three-commit Track A change-set
(`cd935cae`/`09c7f81e`/`64b4f1dd`), reject-criteria brief per
`design/intrinsics/diagnostic-modes.md` §7.4/§9.6. Reviewer: codex-cli
0.145.0. The reviewer judged the convergence itself behavior-preserving
(offsets unchanged); the block is documentation-of-unsafe only.
