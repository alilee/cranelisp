---
number: 0884
target: /dev
filed_by: /review
filed_at: 2026-07-26
sprint_filed: 118
refers_to: crates/cranelisp-primitives/src/marshal/tests.rs (rc_of, nodes_and_elements)
status: open
---

# marshal test helpers: safe fns wrap raw derefs whose SAFETY claims are unsound

## Severity
Blocker

## Issue

The S118 W2b RE-1 change-set (commit `959833ea`) added two *safe* test
helpers in `crates/cranelisp-primitives/src/marshal/tests.rs` that
dereference integer-derived raw pointers:

- `rc_of(ptr: i64)` — `// SAFETY: ptr cleared the nullary-tag guard, so it
  is a base pointer from alloc_with_rc; RC_OFFSET (8) is inside the header
  every such allocation carries.`
- `nodes_and_elements(ptr: i64)` — `// SAFETY: ptr is a live SCons base
  (nullary-tag guard above); both field offsets are inside its three-slot
  payload.`

Both SAFETY comments infer provenance/liveness/shape from the
`NULLARY_THRESHOLD` guard alone. That inference is unsound: any i64 above
the threshold clears the guard; it establishes neither provenance, nor
liveness, nor that the value is an SCons node. The *actual* precondition —
callers pass only values freshly built by `heap_slist`/`alloc_adt_*`/
`build_runtime_list` in the same test and not yet released — is a caller
property that the safe signatures do not encode, so a future test can reach
UB through a safe function. The `/review` unsafe-audit rules are absolute
("SAFETY explains why the invariants are upheld"; the pre-existing file
convention is call-site SAFETY comments with local provenance, which these
helpers departed from).

Delegated-review origin: Codex finding (codex-cli, sandboxed read-only
review of `7f9c762f..HEAD`), verified against source by the adjudicator.

## Proposed resolution

Either (a) mark both helpers `unsafe fn` with a `# Safety` doc stating the
real precondition (live, unreleased heap value built by this module's
allocators; for `nodes_and_elements`, a well-formed SCons chain), moving
justification to call sites; or (b) keep them safe but rewrite the SAFETY
comments to state the caller contract honestly and keep the assert as the
bare-tag misuse tripwire only. Option (a) matches the crate's existing
call-site-SAFETY convention. Test-code-only change; no production code
moves.

## Context

The helpers themselves are legitimate (they test the RC/heap boundary — the
one case test unsafe is licensed for). The finding is about the soundness of
the stated justification, not the existence of the unsafe. Fix is small and
should land before sprint close per the Blocker rule.
