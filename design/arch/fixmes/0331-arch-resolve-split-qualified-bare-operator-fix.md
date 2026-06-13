---
number: 0331
target: /arch
filed_by: /dev (typecheck)
filed_at: 2026-06-13
sprint_filed: 81
refers_to: crates/cranelisp-types/src/resolve.rs (split_qualified ~488, canonical_symbol ~580), design/arch/principles/16-punctuation-symbols-are-not-special.md, design/arch/fixmes/0316
status: open
---

# `cranelisp-types::resolve` slash-split fix (FIXME 0328 root cause) — landed in types; ratify

## What changed (and why it had to land in `cranelisp-types`)

FIXME 0328 (S81 bite-1 regression: the `resolve_with_fallback` migration made the bare `/`
division operator resolve as `undefined variable: /`) was root-caused to two PRIVATE helpers
in `crates/cranelisp-types/src/resolve.rs`:

1. `split_qualified(name)` used a bare `name.split_once('/')`, so `"/"` → `("","")` was treated
   as a qualified `module/symbol` reference and routed to `resolve_qualified` against the empty
   root module → not found. Fixed to require BOTH parts non-empty (`.filter(|(m,s)| !m.is_empty() && !s.is_empty())`); a bare punctuation operator (`/`, `//`) or a leading/trailing
   `foo/`/`/bar` is now a literal bare name (Principle 16).

2. `canonical_symbol(name)` used `name.rsplit_once('/')`, so even on the corrected unqualified
   path `"/"` → canonical symbol `""` — the `Resolved.fq.symbol` field would be empty. Fixed
   with the same non-empty-remainder guard so a bare `/` is its own canonical symbol.

A typecheck-side-only fix was NOT sufficient: the four `checker.rs` chokepoints delegate the
`/`-split to `cranelisp_types::resolve`, and `canonical_symbol` corrupts the FQ symbol on the
unqualified SUCCESS path (which a checker guard cannot intercept). Per FIXME 0328 §"Proposed
resolution" option 1 (the single-seam fix). Both helpers are PRIVATE (`fn`, not `pub`) —
**zero public-API / `public-api.txt` impact** (verified: not present in the baseline; the
`public_api_relocations` test passes unchanged), so no baseline regen was needed.

## Why filed rather than left silent

`crates/cranelisp-types/` is `/arch`-owned and outside `/dev`-on-typecheck's edit boundary.
The S81 bite-1 deployment brief named TASK 1 (0328) mandatory and the fix genuinely required a
types edit; the edit is the minimal, behaviour-restoring change (matches pre-migration literal
lookup). Filing for `/arch` ratification per the cross-crate protocol. If `/arch` prefers the
fix elsewhere, the seam is these two helpers.

## Verification

- `arithmetic_div_int` GREEN; `every_example_runs_with_documented_exit` GREEN (15-traits.cl,
  19-threading.cl `(/ ...)` now resolve).
- Full suite: 1232 passed / 4 failed / 1 skipped — the 4 failures are unrelated (2× FIXME 0329
  bare-primitive-type top-level parsing, routed to /spec; 2× FIXME 0316 int-side terminal-dedup,
  out of bite scope). No regression from the types edit.

## Proposed resolution

Ratify the change (or relocate per /arch preference) and close.
</content>
