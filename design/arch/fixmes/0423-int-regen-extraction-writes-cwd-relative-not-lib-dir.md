---
number: 0423
target: /int
filed_by: /sprint
filed_at: 2026-06-21
sprint_filed: 87
refers_to: src/ (source-regen / `(mod …)` extraction write path), spec/08-modules.md §8.2.5 (mod-body extraction), stdlib/ self-test backing files, the S87 "D-regen" note in stdlib/plan-stdlib.md §26.6
status: open
---

# Source-regen / `(mod …)` extraction writes backing files CWD-relative, not to the lib-dir

## Issue

When the in-language stdlib self-test runner is invoked with the working
directory at the repo **root** (not inside `stdlib/`), the compiler's `(mod …)`
body extraction / source-regen wrote the extracted backing files **CWD-relative**
— producing stray `./collections/`, `./compare/`, `./fn/`, `./num/`, `./text/`
trees at the repo root that mirror the `stdlib/` module layout but contain only
`…/<stem>/test.cl` files.

Concretely: a parent module `stdlib/num/int.cl` declares a bare `(mod test)`
(body in the extraction-stable backing file `stdlib/num/int/test.cl`). Running the
runner from the repo root caused the extractor to (re)emit the body to
`./num/int/test.cl` (CWD-relative) instead of recognizing/targeting the lib-dir
copy under `stdlib/`. 14 such files were generated and accidentally committed in
the S87 checkpoint (`66a4d41`); removed in the S87 close sweep + guarded by a
`.gitignore` entry (interim band-aid — the real fix is below).

This is the **"D-regen" class** the S87 repro pass had dismissed as a
test-isolation artifact; the root cruft is concrete evidence the CWD-relative
write does happen (non-destructively, but it rots the repo root).

**Secondary symptom (same regen path):** the extracted copies differ from the
hand-authored `stdlib/` backing files not only by a stripped header comment but
by **annotation spacing** — the regen pretty-printer emitted `: (Option String)`
where the source has `:(Option String)`. Per `memory/annotation-reader-macro-binds-following-form`,
`:Type` binds the immediately-following form with **no space**; the regen
inserting a space after `:` is a latent formatting divergence worth checking in
the same pass.

## Proposed resolution

`/int` (the source-regen / extraction owner):

1. **Resolve the extraction/regen output path against the lib-dir (or the source
   module's own directory), never the process CWD.** A `(mod …)` body's backing
   file belongs next to its parent module file (`<module-file-dir>/<stem>/…`),
   which for stdlib is under `stdlib/`. Determine the parent module's on-disk
   location and write relative to that, independent of CWD.
2. **Prefer recognizing an existing extraction-stable backing file** over
   re-emitting it (the `stdlib/` copies already exist and are canonical; the
   runner should read, not rewrite, them).
3. **Check the regen annotation spacing** — emit `:Type` (no space) consistent
   with the reader-macro semantics, not `: Type`.

## Verification / Context

- A narrow repro is encodable (and ideal — request `/qa`): run the binary / the
  in-language test runner with `CWD` = a fresh tmpdir ≠ the lib-dir, exercise a
  `(mod test)` module, and assert **no stray backing files appear outside the
  lib-dir**. Currently they do.
- Interim guard in place: `.gitignore` ignores `/collections/ /compare/ /fn/
  /num/ /text/` at the repo root so a stray runner-from-root can't re-commit them.
  This is a band-aid; the durable fix is the lib-dir-relative write above.
- Surfaced during S87 hygiene close (user spotted the stray root dirs).
