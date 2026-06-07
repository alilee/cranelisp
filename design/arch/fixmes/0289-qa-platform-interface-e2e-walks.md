---
number: 0289
target: /qa
filed_by: /arch
filed_at: 2026-06-07
sprint_filed: 76
refers_to: design/arch/platform-interface.md §4 §7.2 §7.2a §7.3, design/arch/fixmes/0235, design/arch/bounded-contexts.md §5 §6
status: open
---

# Platform-interface — e2e round-trip + hash-gate integration tests

## Issue

The platform-interface design (`design/arch/platform-interface.md`, user-ratified
2026-06-07; **normative**) needs e2e coverage of its walks. This supersedes the old
schema-validation-mismatch coverage in FIXME 0235 (re-pointed) — the layout-hash gate
replaces `validate_schema`.

## Scope

Per `platform-interface.md` §4 (author experience) + §7.2/§7.2a/§7.3 (the sequences):

1. **FQ-named-ADT round-trip** — a test platform (test-DLL authored by `/platform`) whose
   sigs reference an ADT defined in an ordinary `.cl` module (`shapes/Rectangle`); cranelisp
   source constructs the ADT and passes it to the platform fn; assert the value crosses
   correctly (rectangle {w=3,h=4} → 12). Works in `--run` and `--link`.
2. **The build-load-generate-embed-rebuild walk** — `/platform-schema <name>` emits the
   artifact; the platform embeds it; `--run`/`--link` ACCEPT on hash match.
3. **The dual hash-gate** — a stale/typo'd schema (sig or `deftype` edited after the DLL
   was built): **REPL warns-and-loads**; **`--run` refuses**; **`--link` refuses** (the
   startup-stub baked-hash comparison) — each with both hashes + rebuild guidance. (This is
   the re-target of old 0235 item 4 — `validate_schema` mismatch → layout-hash mismatch.)
4. **Cache-restore round-trip** — re-load from cache; ADTs cross correctly (platform types
   cache as ordinary `.cl` modules; no `schema_literal` field).

## Acceptance

- `tests/spec_platforms_adt.rs` (or sibling) lands the round-trip + hash-gate + cache walks,
  failing-first then green as 0286/0287/0288 land. Per the two-tier discipline the test-DLL
  is `/platform`'s; the `tests/`-side e2e file is `/qa`'s.

## Context

QA half of the platform-interface cascade (0286 platform, 0287 backend, 0288 int).
Re-points + absorbs FIXME 0235.
