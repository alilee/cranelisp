---
number: 0898
target: /arch
filed_by: /review
filed_at: 2026-07-26
sprint_filed: 118
refers_to: src/result_owner.rs::strip_io_head (:398-409) + crates/cranelisp-backend/src/lib.rs:672-683 (result_roots)
status: open
---

# The IO result-root strip rule now has two literal encodings (backend + int)

## Severity

Important

## Issue

W4's `release_key` correctly keys the program-result release on the entry's
`codegen_view` body `ConcreteType` — the same value backend computed its
`result_roots` from — with the `IO` head stripped "by the same rule". But the
rule itself is a second literal encoding: `src/result_owner.rs::strip_io_head`
and the inline map in backend's `compile_to_module`
(`crates/cranelisp-backend/src/lib.rs:673-683`) each independently match
`primitives/IO` ADT with non-empty args and take `args[0]`. They agree at HEAD
by text, not by shared derivation — either side can drift, and a drift here
means int demands glue under a key backend never published (Principle 7 —
single source of truth; the same class as the three-copy quote classifier,
FIXME 0789).

With two concrete users the shared-helper bar (Principle 6's two-user rule) is
now met.

Found by the delegated Codex reviewer (codex-cli 0.145.0); the adjudicator
independently confirmed the two sites are textual twins.

## Proposed resolution

`/arch` rules where the single statement lives — the natural home is
`cranelisp-types` beside `drop_glue_symbol_name` (the strip rule is part of
the same result-root grammar), e.g. a `ConcreteType`-level
`strip_io_head`/`result_root_of` helper — then both backend's `result_roots`
map and int's `release_key` call it. This is a cross-crate/public-surface
question, hence `target: /arch` rather than `/dev`.

## Context

Complementary to the /dev-filed FIXME 0892 (renumbering to 0896 rides the
/design(int) dispatch): 0892 asks `/design` to ratify the release-key
*semantics* (codegen-view key, observed-type fallback); this FIXME is about
the *mechanical* single-sourcing of the strip rule that both producers of that
key apply. Resolving 0892 without this leaves the duplication in place.
