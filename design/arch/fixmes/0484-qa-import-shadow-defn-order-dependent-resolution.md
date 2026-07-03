---
number: 0484
target: /qa
filed_by: /stdlib
filed_at: 2026-07-03
sprint_filed: 101
refers_to: spec/08-modules.md (import/definition precedence), repl/spec.md §3.6 (/info), design/int/session-transaction.md §9.2, tests/ (0475 pins — builtin-shadowing precedence, adjacent)
status: open
---

# Shadowing an imported name with a user defn is order-dependent — and `/info` disagrees with call resolution

## Issue

When a user defines a function whose name was previously **imported**, which
definition subsequent bare calls resolve to depends on whether the imported
name was *used before* the shadowing defn. Same 4 forms, different results:

**Variant 1 — import, call, defn, call** (import sticks):

```
user> (import [collections.vec [count]])
user> (count [1 2 3])                       ; ⇒ 3
user> (defn count "user shadow" [v] :Int 99)
:(Fn [a] primitives/Int) user/count ; defn - user shadow
user> (count [1 2 3])                       ; ⇒ 3   ← import still wins
```

**Variant 2 — import, defn, call** (user defn wins):

```
user> (import [collections.vec [count]])
user> (defn count "user shadow" [v] :Int 99)
user> (count [1 2 3])                       ; ⇒ 99  ← shadow wins
```

In BOTH variants `/info count` reports `user/count ; defn - user shadow`
(with source, and `? bytes` for size) — so in variant 1 the introspection
surface describes a function that bare `count` does not call. The
self-documenting-REPL principle is violated: the user cannot discover from
the REPL which `count` their next call will hit.

No cascade/redefinition report is printed in either variant (arguably
correct — different FQ symbol, not a redefinition — but then variant 1's
sticky import is the surprise; the S101 machinery treats `user/count` as a
fresh def, while call-site resolution behaves as if the import is
irrevocable once exercised).

Related: FQ `(user/count [1 2 3])` after the shadow fails
`undefined function: user/count` — that is the generic-FQ-call defect
(FIXME 0483), which removes the one unambiguous workaround a user would
reach for.

## Proposed resolution

/spec (or /arch) may need to pin the normative precedence first
(spec/08-modules.md is the anchor: does a module-local defn shadow an
explicit import, or is defining an imported name an error/warning as in
Clojure?). Whichever way it is pinned, /qa authors the repro pair — the two
variants above MUST agree with each other and with `/info`. The 0475 pins
cover builtin-vs-user shadowing (direct call takes user body); this is the
*import*-vs-user cell, unpinned.

## Operational implication / Context

Surfaced exercising S101 Phase 6a mandate ("what happens when a user
redefines a stdlib name — is the experience coherent?"). Answer today: no —
resolution is history-dependent and introspection disagrees with it.
Redefining stdlib-INTERNAL behavior is unaffected (stdlib callers keep
their own bindings — correct), so the blast radius is the user's own
session surface.

## /qa guard batch (S101 6b, 2026-07-03): guards LANDED — this file is now redundant as a record

Reduced stdlib-free (local `util` module, fn `measure`). 1 RED guard + 1
green order-control in `tests/spec_08_modules.rs`
(`import_used_then_shadowed_by_defn_subsequent_call_takes_shadow` — pins
shadow-wins per §8.6.1 layer 2 AND /info agreement;
`import_shadowed_by_defn_before_first_call_takes_shadow_control`). If /spec
pins a different normative precedence, the guard's expected values re-anchor.
Ledger: `tests/plan/ledger.md` §"Sprint 101 Phase 6a/6b defect set".
