---
number: 0356
target: /arch
filed_by: /sprint
filed_at: 2026-06-14
sprint_filed: 82
refers_to: crates/cranelisp-types/src/module.rs (ModuleEntry::Def, got_slot, DefKind::UserFn{constrained_fn}, callable_got_slot/mark_constrained_template), design/arch/bounded-contexts.md §7, design/arch/interfaces.md, design/arch/principles/18-*.md, design/arch/decisions/0035-*.md, design/arch/fixmes/0355-typecheck-cross-module-monomorphise-constrained-fn.md
status: open
---

# Make `ModuleEntry` callability STRUCTURAL — the facade should express the fundamental intent, not enforce it by accessor convention

## Issue (user directive, S82 close)

FIXME 0354 (cross-module constrained-fn call SIGSEGV) was fixed in S82 with an
**SSOT-accessor** shape: `ModuleEntry::callable_got_slot()` returns `None` for a
constrained template regardless of the stored field, and `mark_constrained_template()`
is the sole atomic writer (flips `kind` + clears `got_slot`). This is correct *enforcement*
— it eliminated the crash — but it is **not the fundamental fix**.

The illegal state — a constrained *template* (not directly callable; only its
monomorphised variants are) carrying a callable `got_slot` — is **still representable**:
`got_slot: Option<usize>` on `ModuleEntry::Def` and `constrained_fn` inside
`kind: DefKind::UserFn` are independent sibling fields set at different pipeline stages
(`register_defn_signature` allocates the slot in Pass 1, *before* constraint detection
flips `kind` in Pass 2). Nothing in the type prevents constructing
`Def { got_slot: Some(_), kind: UserFn { constrained_fn: Some(_) } }`. The accessor
*reads around* the illegal state; it does not *forbid* it. The bug recurs the moment a
new construction or write site forgets the accessor — exactly the drift that caused 0354.

**User directive:** "Take the pain on facade changes early. We want the facade to express
the fundamental intent." The canonical types surface (crate-root `//!` + per-item `///`
rustdoc in `module.rs` + `bounded-contexts.md §7` + `interfaces.md` — the `types.md` facade
was retired S69) should make **callability a property of the shape**: a constrained
template structurally *cannot hold* a callable slot. Illegal-state-unrepresentable
(Principle 18's strongest form), not invariant-by-accessor-discipline.

## Proposed resolution (the "option B" /arch's 0354 investigation deferred)

`/arch` restructures `DefKind`/`ModuleEntry` so `got_slot` lives **only** on the
concrete / monomorphisable shape; a constrained template is a slot-less variant — so
`Def{got_slot:Some} + constrained_fn:Some` is unconstructable. The facade (source rustdoc
+ BC §7 + interfaces.md) then states the intent structurally and the `callable_got_slot()`
accessor becomes a trivial field read (or disappears).

`/arch`'s 0354 investigation deferred this on three grounds — they must be addressed, not
used to re-defer indefinitely:
1. **~180 `Def { got_slot, .. }` read sites** churn (Principle 6 cost) — mechanical but real.
2. **Reverses Decision 0035** (the flat single-`got_slot`-field SSOT) — needs a Decision
   amendment, not a silent reversal.
3. **The timing wall** — Pass 1 allocates the slot before constraint status is known. The
   structural shape forces resolving this: detect constrained-ness at/before slot
   allocation, or stage allocation after detection.

## Operational implication / Context

**Bundle with FIXME 0355** (S83 cross-module-mono feature) — it touches the same
`DefKind`/monomorphisation surface, so doing the structural reshape *with* the feature
avoids restructuring twice (and 0355's `cmp$Int+Int`-gets-its-own-slot model is the
natural place the concrete-shape-owns-the-slot invariant lands). The S82 SSOT-accessor
holds the line until then (no SIGSEGV ships); this FIXME is the paydown to the
fundamental, facade-expressed form.
