---
number: 0263
target: /qa
filed_by: /dev
filed_at: 2026-06-05
sprint_filed: 76
refers_to: tests/fixtures/preludes/primitives-only.cl, tests/fixtures/preludes/test-standard.cl, tests/fixtures/prelude.cl
status: open
---

# QA prelude fixtures use `(import [primitives [*]])` where spec requires `(export …)` — 279 e2e failures (`undefined variable: <primitive>`)

## Issue

The dominant Wave-2 e2e failure class — ~279 of 404 failing tests showing
`undefined variable: add-i64` (and `sub-i64`, `str-concat`, `eq-i64`, …) — is
**not an int wiring defect**. The int bootstrap mount (`src/bootstrap.rs`) and
import/export installer (`src/imports.rs`) are spec-compliant; verified
end-to-end (below). The root cause is the QA prelude fixtures.

`tests/fixtures/preludes/primitives-only.cl` is a single line:

```clojure
(import [primitives [*]])
```

and `tests/fixtures/preludes/test-standard.cl` opens with the same line.

These are written to `prelude.cl` in the test tmpdir, so they are loaded as the
**prelude module**, then the user module receives them via the implicit prelude
glob (`(import [prelude [*]])`, spec §8.8).

Per spec §8.7.3 and §8.4: **a glob (`[*]`) imports/exports only PUBLIC names.**
`(import [primitives [*]])` brings the primitives into the prelude module as
`ModuleEntry::Import { visibility: Private }`. Private names are excluded from
the prelude's public surface, so the user's implicit prelude glob picks up
**nothing**. The bare name `add-i64` never reaches the user module → typecheck
emits `undefined variable: add-i64`.

This was correct in the **old** harness because the old path injected
`tests/fixtures/preamble_primitives.cl` (same `(import [primitives [*]])` line)
**directly into the user/test module** — see `design/stdlib/examples-run-path.md`
§1.2, which documents exactly this: the line "glob-imports every Ring-0/1
primitive with bare names **into the test module**." The Wave-1 harness
(`tests/helpers/e2e.rs::with_prelude`, commit 9db1c3e) changed it to write the
line as `prelude.cl`, which routes through the implicit-prelude-glob path where
Private imports are (correctly) invisible.

The spec's own prelude example (08-modules.md §8.4, lines 483–487) uses
**`export`**, not `import`, for exactly this reason.

## Proposed resolution

In the QA-owned prelude fixtures, change the primitive line from `import` to
`export` (re-export → Public → flows through the user's implicit prelude glob):

```clojure
;; primitives-only.cl
(export [primitives [add-i64 sub-i64 mul-i64 div-i64
                     eq-i64 lt-i64 gt-i64 le-i64 ge-i64
                     add-f64 sub-f64 mul-f64 div-f64
                     eq-f64 lt-f64 gt-f64 le-f64 ge-f64
                     not eq-bool
                     str-concat str-eq str-len char-at contains? ends-with? join
                     int-to-string float-to-string bool-to-string
                     vec-len vec-get vec-set vec-push]])
```

`(export [primitives [*]])` glob also works if a full re-export is desired
(verified). Use whichever name set the assertions need; `[*]` is simplest.

`test-standard.cl` needs the same change for its bare-primitive line. NOTE it
ALSO carries the §0264 `[self self]` defect — fix both together. Its
`deftype`/`deftrait`/`impl` forms are already Public (default) and flow through
the glob fine, but its impl **bodies** reference bare `add-i64` etc.; those
resolve within the prelude only if the primitives are imported (Private is fine
for in-prelude bodies) — so test-standard needs BOTH `(import [primitives [*]])`
(for its own impl bodies — Private is fine) AND, separately, an
`(export [primitives […]])` line if any test expects bare primitives at the
**user** site. If no test expects bare primitives under TestStandard, the import
line alone suffices for the bodies; verify against the assertions.

`tests/fixtures/prelude.cl` (the `PreludeVariant::TestPrelude` legacy fixture)
carries the same `(import [primitives [*]])` pattern at line 9 — same disposition.

## Operational implication / Context

- Verified spec-compliant int behavior, all three modes, with a conformant
  prelude (`(export [primitives […]])` + `(import [primitives [Int]])` for the
  impl type refs):
  - bare primitive: `(add-i64 3 4)` → `:primitives/Int 7`
  - trait operator: `(+ 3 4)` → `:primitives/Int 7`
  - `--run`: `(defn main [] (add-i64 (+ 3 4) 1))` → exit 8
- A prelude that defines `impl Num Int` must also reach the **type** `Int` (it
  lives in `primitives`); add `(import [primitives [Int …]])` for the type refs
  the impls use, or qualify them. The current fixtures rely on this implicitly.
- This is NOT a Wave-2 regression in int. `src/bootstrap.rs` and
  `src/imports.rs` are unchanged-in-behavior w.r.t. glob visibility; the rule
  (`public_symbols()` for glob) matches the deleted typecheck `collect_glob_imports`
  byte-for-byte (recovered from `cee8152^`).
- Spec refs: 08-modules.md §8.4 (export example uses `export`), §8.7.3 (glob
  excludes private), §8.8 (implicit prelude glob brings PUBLIC names).
- The compiler-skill side of this is closed: int is correct. This FIXME is the
  durable record + trigger for the fixture fix. Once the fixtures are corrected,
  the ~279 `undefined variable` failures should clear (modulo the §0264 parse
  error which gates test-standard.cl entirely).
