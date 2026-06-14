---
number: 0352
target: /int
filed_by: /qa
filed_at: 2026-06-14
sprint_filed: 82
retargeted_at: 2026-06-14
retargeted_reason: "S83 Phase-3 design found the scheme renderer migrated to src/display.rs in Sprint 66; cranelisp-backend has no scheme-display renderer. The fix (route /list through the normalize+qualify renderer) is wholly an /int change at src/repl.rs::handle_list + src/display.rs. Re-pointed /backend -> /int by /sprint orchestration."
refers_to: src/repl.rs (handle_list ~:670 — the `format!(\"{}\", scheme.ty)` raw-Display bug; format_def_entry ~:1751 — the correct path), src/display.rs (format_type_qualified, format_scheme_display — int-owned since S66; extract shared format_scheme_type)
status: open
---

# `/list` renders RAW internal type variables (`t1`) for polymorphic defns

## Issue

The REPL `/list` command renders polymorphic function schemes with raw
internal type-variable ids instead of the normalized `a`/`b`/… letters that
the definition-display line (and `/sig`) correctly produce.

Observed (isolated e2e, `repl_prims_capture`):

```
user> (defn id [x] x)
:(Fn [a] a) user/id ; defn        <-- definition display: CORRECT (normalized)
user> /list
Fns:
  id : (Fn [t1] t1)               <-- /list: WRONG (raw internal var `t1`)
```

Other observed leaks in the same `/list` output: `konst : (Fn [t10 t9] t10)`,
`wrap : (Fn [t13] (primitives/Option t13))`. Monomorphic fns render fine
(`double : (Fn [Int] Int)`), so the bug is specific to the type-var
normalization step being skipped on the `/list` rendering path.

This violates repl/spec.md §1.4 ("Polymorphic type schemes MUST display
quantified variables as consecutive lowercase letters starting from `a`").
The definition-display path already satisfies this; the `/list` path does not
re-use the same normalizing renderer.

Note also that `/list` renders `Int`/`Bool` UNQUALIFIED in the same lines
(`double : (Fn [Int] Int)`), whereas §1.4 requires fully-qualified type names
(`primitives/Int`). Whether `/list` is intentionally abbreviated is a §1.4 /
repl-spec question — flag to `/repl`/`/spec` if the abbreviation is by design;
if not, the same renderer fix covers both.

## Proposed resolution

Route the `/list` per-symbol scheme rendering through the same normalize +
qualify renderer the definition-display / `/sig` paths use (the
`cranelisp-backend` scheme display that produces `(Fn [a] a)` and
`primitives/Int`), rather than a separate raw `Scheme`→string formatter.

## Operational implication / Context

Surfaced during the S82 FIXME-0124 harvest (`tests/legacy/repl_negative_old.rs`
→ `tests/repl_negative.rs`). The legacy file only exercised the (already
covered, green) definition-display path via the Rust-internal `format_result`;
it never exercised `/list` rendering, so this is a NEW finding, not a regression
the harvest introduced. Per the `/qa` defect protocol a failing e2e repro is
owed once the fix is scheduled (it was deliberately NOT added as a red guard in
the S82 harvest to keep that change-set green; the acceptance gate for the
harvest was "only the 2 intentional 0351 repros red"). When `/backend` picks
this up, the failing repro lands in `tests/repl_negative.rs` in the same
change-set as the fix:

```rust
// spec: repl/spec.md §1.4 — /list normalizes type variables, no raw tN
#[test]
fn list_neg_no_raw_type_vars() {
    let out = repl("(defn id [x] x)\n/list\n");
    assert!(!out.stdout.contains("t1"), "/list leaked raw var; got:\n{}", out.stdout);
}
```
