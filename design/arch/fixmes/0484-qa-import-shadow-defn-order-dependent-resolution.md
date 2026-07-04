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

## /sprint addendum (S102 Wave 10a, 2026-07-04): fix ATTEMPTED, reverted — needs a /spec glob-exemption ruling FIRST

The /int rejection fix (commit-gate: pre-scan staged Defs against live `Import` entries, reject the later-arriving conflicting form per /spec's §8.6.4 "definition-over-explicit-import is a compile-time ERROR" ruling) **flipped both 0484 guards but regressed ~30 prelude-dependent tests** (`stdlib_trait_impls`, `trait_imports` → `undefined variable: =`). Root cause (traced live): the universal prelude pattern `(export [primitives [*]])` (GLOB re-export of seeded ctors) + `(deftype (Option a) None …)` (shadowing `None`/`Some`) is **legitimate** shadowing — consistent with the standing "prelude-provided names stay shadowable" principle — but at the commit gate **glob and specific imports are shape-identical `ModuleEntry::Import` entries**, so the rejection cannot distinguish "shadowing a glob-re-exported seeded ADT ctor" (must be ALLOWED) from "defining over a specific explicit import" (the §8.6.4 error). Both 0484 commits were REVERTED; guards stay RED as documented carries.

**The gating question is /spec's**: does the "definition-over-import is a compile-time error" rule apply to **glob** imports, or is glob-of-seeded-ADTs (the prelude pattern) exempt? The prelude's own dependence on shadowing `Some`/`None` strongly implies glob shadowing must stay legal while specific-import shadowing is the error. Once /spec pins that:
- If glob is exempt: /int distinguishes at **import-processing time** (the `(export [m [*]])` vs `(import [m [x]])` spec form carries the glob/specific bit BEFORE the entries become shape-identical) — likely NO `cranelisp-types` change needed.
- If a persisted glob/specific flag on `ModuleEntry::Import` is required: that is an /arch `cranelisp-types` change (schema cascade).

Routing: **/spec** (glob-exemption ruling) → **/int** (import-time rejection) [→ **/arch** only if a persisted provenance flag proves necessary]. Orthogonal to increment I (module resolution, not ownership) — does NOT gate the mechanism ladder.

## /qa guard batch (S101 6b, 2026-07-03): guards LANDED — this file is now redundant as a record

Reduced stdlib-free (local `util` module, fn `measure`). 1 RED guard + 1
green order-control in `tests/spec_08_modules.rs`
(`import_used_then_shadowed_by_defn_subsequent_call_takes_shadow` — pins
shadow-wins per §8.6.1 layer 2 AND /info agreement;
`import_shadowed_by_defn_before_first_call_takes_shadow_control`). If /spec
pins a different normative precedence, the guard's expected values re-anchor.
Ledger: `tests/plan/ledger.md` §"Sprint 101 Phase 6a/6b defect set".
