---
id: ACT-1055
title: A selective member import entry Type.member binds nothing in bare scope
status: open
priority: required
from: qa
to: qa
sprint: 123
filed_at: 2026-11-16
refers_to:
  - spec/08-modules.md
  - src/imports.rs
  - tests/plan/s123-evidence-delta.md
---

## Observation

`docs` found this while writing the modules guide (S123 Phase 6b). `qa`
reproduced it on `target/debug/cranelisp` at `640d2ec7`, 2026-11-16, in
scratch projects. The fixture and cells are K-7 in the
[S123 evidence delta](../../tests/plan/s123-evidence-delta.md#810-phase-6b-intake-from-docs).

- **Requirement.** [§8.3.11](../../spec/08-modules.md#8311-accessibility-after-import):
  an entry of the form `Symbol.member` MUST bring `member` into bare scope
  and MUST NOT bring `Symbol`.
- **Signature.** With `mathx` defining `(deftype Shade Red Blue)`,
  `(import [mathx [Shade.Blue]])` and then bare `Blue` fails with
  `undefined variable: Blue`, exit 1. A bare `Blue` pattern fails with
  `unknown constructor in pattern: Blue`. The REPL gives the same result.
  A trait method behaves the same way: `[lib [Seven.seven]]` leaves `seven`
  undefined.
- **Controls.** `[Shade.*]` gives 7, as do `[Seven.*]` and `[seven]`.
  `mathx/Shade.Blue` resolves after the selective import. `[Shade.Green]`
  reports `'Shade.Green' not found in module 'mathx'`, so the entry is
  resolved in the source module; only its local binding is missing.
- **Class:** `wrong-reject`.

## Attribution

- **Mechanism: confirmed at source.** `src/imports.rs::collect_specific`
  installs each entry under its written spelling (`local_name: name`), so a
  dotted entry is bound as `Shade.Blue`. `collect_member_glob` projects the
  same candidates through `cranelisp_types::bare_member_name` and binds
  `Blue`. The two paths differ only in that projection, and only the member
  glob binds the bare name. *Refuted if* a `collect_specific` that projects
  the bare member name still leaves bare `Blue` undefined.
- **Entry point:** implementation, `src/` (binary crate). No public type
  changes: `ImportNames::Specific` already carries the dotted entry.
- **Coverage:** no cell writes a `Symbol.member` entry. The §8.3.11 heading
  carried `[Tested+Neg]` with no named test; it is re-graded.

## Next

1. `test` commits K-7 as a failing-not-ignored RED with its negatives.
2. `dev` on `src/` corrects `collect_specific` with the K-7 unit row.
   The fix is small enough to pull into S123 if the user accepts it;
   otherwise it carries to S124.
3. `docs` removes the modules guide's statement of this limit once the fix
   lands.
