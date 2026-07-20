---
number: 0689
target: /arch
filed_by: /sprint
filed_at: 2026-07-20
sprint_filed: 114
refers_to: crates/cranelisp-typecheck/src/ownership/fixpoint.rs:170 (body_is_strict_concrete); crates/cranelisp-types/src/mono_expr.rs (from_expr TYPE gate); W2 review Important-1 + Minor-1
status: open
---

# Single-source the strict type-concreteness predicate (the unfenced fixpoint mirror)

From the W2 carrier-flip review (Important-1, approve-with-required-fixes). The
post-flip `from_expr` couples resolution + type gates, so leg 2 correctly
decoupled `collect_universe`'s membership probe into a local
`body_is_strict_concrete` walk (faithful today — replicates exactly the TYPE
gate: Annotate erased, every other node's `inferred_type` must convert, children
via the shared `for_each_child_expr`). But the mirror is **unfenced**: no test
pins equivalence, nothing structural ties it to `mono_expr.rs`'s node handling;
a future `Expr` variant or erasure change drifts them, and drift is not always
conservative (a wrong universe ENTRY perturbs every cluster summary — the W0.b
byte-identity hazard).

Ask (/arch): export ONE strict type-concreteness predicate from
`cranelisp-types` beside `from_expr` (shared by the strict walk and the
fixpoint probe), plus a unit test pinning the three universe populations
(ctor/accessor/lenient-fallback excluded; mono instances + genuine concrete
defns retained). Fold in Minor-1: the misattached rustdoc (`fixpoint.rs:137-169`
narrative now documents the bool predicate; `collect_universe` undocumented).

Violates P7 (single source) and the arch doc's own mirror-fence expectation.
Land before Phase 5 close (review condition).
