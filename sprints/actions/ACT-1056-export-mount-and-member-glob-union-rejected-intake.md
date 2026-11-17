---
id: ACT-1056
title: Export module mounts are rejected and member-glob entries drop their neighbours
status: open
priority: required
from: qa
to: qa
sprint: 123
filed_at: 2026-11-16
refers_to:
  - spec/08-modules.md
  - crates/cranelisp-frontend/src/module_extract.rs
  - crates/cranelisp-types/src/module.rs
  - audits/cranelisp-frontend-s123.md
  - tests/plan/s123-evidence-delta.md
---

## Observation

Two of the three cases in the frontend audit's R2, both now executed. The
export-mount case is also the `docs` Phase 6b observation. `qa` reproduced
them on `target/debug/cranelisp` at `640d2ec7`, 2026-11-16, in scratch
projects. The fixtures and cells are K-8 in the
[S123 evidence delta](../../tests/plan/s123-evidence-delta.md#810-phase-6b-intake-from-docs).
R2's third case, renamed entries, stays with
[ACT-0997](ACT-0997-renamed-import-entries-rejected-intake.md).

- **Export mount.** [§8.4](../../spec/08-modules.md#84-export)
  applies the full §8.3 `module_spec` to exports, and §8.4.4 defines
  `(export [(m alias) [names]])` as re-export plus mount.
  `(export [(mathx math) [square]])` fails with
  `expected symbol for export module path, got (mathx math)`, exit 1. The
  mount-only form `(export [(mathx math) []])` fails the same way.
  Controls: `(export [mathx [square]])` gives 49, and the import form
  `(import [(mathx math) [square]])` with `math/square` gives 49.
- **Member-glob union.** §8.3.11 requires each entry to be classified
  independently, and states that `(import [m [Option Option.*]])` MUST NOT be
  an error. `[mathx [Shade Shade.*]]` drops `Shade`, so `Shade.Blue` is
  undefined. `[mathx [Shade.* square]]` drops `square`. Control: the same
  entries as two module specs, `[mathx [Shade] mathx [Shade.*]]`, give 7.
- **Class:** `wrong-reject`, for both: each rejects a conforming program.

## Attribution

- **Mechanism: confirmed at source.** In
  `crates/cranelisp-frontend/src/module_extract.rs`, `parse_export_entries`
  calls `expect_symbol(…, "export module path")`, which is the observed
  message. Imports use `parse_module_spec`. `parse_names_list` returns
  `ImportNames::MemberGlob` as soon as any entry ends in `.*`, discarding the
  rest. The two-spec control separates the union loss from the
  installation path. *Refuted if* a parser that keeps every entry still
  loses one at installation.
- **Entry point: carrier.** `ExportSpec` has no alias field, and
  `ImportNames` is one whole-list classification, so neither the mount nor a
  mixed list is representable. The correction changes
  `crates/cranelisp-types` and needs `arch` and the inter-crate public-API
  user gate. Pairing it with ACT-0997's `ImportNames` packet avoids two
  passes over the same type.
- **Coverage:** no cell writes an export mount or a mixed member-glob list.

## Next

1. `test` commits K-8 as failing-not-ignored REDs.
2. `arch` frames the `ExportSpec` and `ImportNames` delta with ACT-0997 for
   the user gate. This is not an S123 fix.
3. `docs` revisits the modules guide's statement of the mount limit when it
   lands.
4. **S124 (qa, 2026-11-16):** the six cells cover audit R2's two cases. One
   variant is added, T-R2-a of the
   [S124 evidence delta](../../tests/plan/s124-evidence-delta.md#35-frontend-audit-r1-r2-r3):
   `[mathx [Shade.* Hue.*]]` drops the second member glob, a loss no
   committed cell reaches.
