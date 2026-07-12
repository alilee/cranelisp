---
number: 0567
target: /arch
filed_by: /arch
filed_at: 2026-07-12
sprint_filed: 108
refers_to: crates/cranelisp-types/src/resolve.rs::resolve_with_prelude (L523–531); design/arch/prelude-import-convergence.md §3.5.2; spec/08-modules.md §8.8.1
status: open
---

# `resolve`'s prelude-retry I-1 filter tests the chain-followed TERMINAL's visibility, not the prelude HEAD's

## Severity

Minor (latent — unreachable through the stock prelude).

## Issue

`resolve_with_prelude`'s step-3 I-1 filter accepts the prelude retry when
`resolved.entry.is_public()` — but `Resolved.entry` is the CHAIN-FOLLOWED
TERMINAL, not the binding in prelude's own table. A **private `(import …)`
edge inside the prelude** whose chain terminates at a PUBLIC `Def` in
another module therefore leaks through `ResolutionScope::resolve` as a bare
name in every fallback-ON module.

Spec §8.8.1 provides "the prelude's **public** names" — the implicit glob
imports prelude's public *bindings*, so the visibility that matters is the
prelude HEAD's (the binding), not the terminal's. Precedents already on the
head side: `find_trait_method_decl`'s `public_only` head filter (typecheck),
`prelude_implicit_names`' `is_public()` head filter (int), the E8
`impls_for_type_in_view` public-head post-filter, and the §3.5.2 display-gate
fix (head filter). Once that display fix lands, this residual is the
mirror-image divergence: display hides what resolve leaks.

Unreachable today: the stock stdlib prelude is a pure re-export shell
(public `export` edges only; no private imports, no `defn-`), so no live
program observes the leak. Constructible in a unit test with a synthetic
prelude table carrying a private `Import` edge to a public terminal.

## Proposed resolution

In `resolve_with_prelude` (cranelisp-types — `/arch`-owned code), filter the
retry on the **prelude head binding's** visibility: probe prelude's table for
the head entry and require `is_public()` before (or in addition to) the
terminal check. Failing unit pin FIRST (private-import-in-prelude → bare name
does NOT resolve; reports the original current-module not-found), per METHOD
§2.2. Behaviour-invariant for the stock prelude. No public-API shape change
(internal walk body only); no serde/cache impact. Update the
`crates/cranelisp-types/CLAUDE.md` §"Resolution primitive traps" gotcha and
`prelude-import-convergence.md` §3.5.2's residual paragraph when closed.

## Context

Surfaced during the S108 Inc3 §3.5.2 I-1 display-divergence ruling
(`prelude-import-convergence.md`). Pairs with the `/dev` display-gate fix
named there (repl.rs `lookup_with_prelude_fallback_opt` + eval.rs bare-symbol
hop head filters) — the two together make display and resolution agree on the
spec's head-visibility reading.
