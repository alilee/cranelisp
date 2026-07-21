---
number: 0751
target: /dev
filed_by: /review (cranelisp-backend, S115 W3)
filed_at: 2026-07-21
sprint_filed: 115
refers_to: crates/cranelisp-backend/src/compiler/fn_compiler.rs::scrutinee_cow_retains_reused (the FIXME-0693 debug_assert_eq! fence)
status: open
---

# The 0693 fence's RELEASE-build behaviour on disagreement takes the UAF direction, while the sibling ambiguity path correctly takes the leak-safe one

## Severity
Important — narrow reachability (synthetic spans only), one-line fix, and the
rustdoc's stated safety property is materially wrong as written.

## Issue

The consolidated seam reads:

```rust
match self.cow_retain_decisions.get(span).copied() {
    Some(Some(recorded)) => { debug_assert_eq!(recorded, derived, "…"); recorded }
    Some(None) => false,   // ambiguous span ⇒ leak-safe
    None => derived,
}
```

The rustdoc argues: *"Release builds take the RECORDED verdict, so a disagreement
degrades to the producer's truth rather than to a guess."* That is only true when
the record belongs to the SAME site. The disagreement case that survives to
release is precisely the one where it does not:

- two COW sites share a span (reachable for `Span::SYNTHETIC` bodies);
- site A ran the producer and recorded `Some(true)`;
- site B — the node the R3 seam is asking about — did not record (it was not
  lowered by this frame's producer, or its lowering took the non-last-use copy
  path, which never calls `cow_source_ownership`), so no collapse to the
  ambiguous marker `None` occurred;
- `derived(B) = false`, `recorded = true` ⇒ debug builds assert; **release
  builds return `true`, the R3 dec fires, and there is no producer inc behind
  it — the spurious dec / UAF channel 0693 was opened to close.**

The change-set already made the correct call one arm down: the ambiguous marker
resolves to `false` "never a spurious dec, i.e. never the UAF direction". The
disagreement arm should have the same polarity for the same reason.

## Proposed resolution

`/dev`(backend): keep the `debug_assert_eq!` as the loud development fence, but
make the release path leak-safe on disagreement:

```rust
Some(Some(recorded)) if recorded == derived => recorded,
Some(Some(recorded)) => { debug_assert!(false, "…{recorded}…{derived}…"); false }
```

and correct the rustdoc claim accordingly (a disagreement means the seam does not
know which site the record belongs to — the safe verdict is "suppress", not "trust
the record"). Add the disagreement cell to `cow_gate_tests` alongside the existing
matrix.

## Context

`/review`(backend), S115 W3. Related structural finding filed separately as 0752
(two surviving name-keyed derivations of the same COW-site identity question).
