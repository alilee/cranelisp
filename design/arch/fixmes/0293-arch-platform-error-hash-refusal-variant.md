---
number: 0293
target: /arch
filed_by: /dev
filed_at: 2026-06-08
sprint_filed: 76
target_sprint: 77
refers_to: crates/cranelisp-types/src/error.rs (PlatformError enum), decisions/0042-platform-error-adopts-error-location.md, design/arch/platform-interface.md §5.5.4 §6.4, design/arch/fixmes/0288-dev-int-platform-interface-load-path-and-platform-schema-command.md
status: partially-resolved
---

## Resolution status (S76 W4b, /dev cranelisp-types)

- **DONE — the `PlatformError::LayoutHashMismatch` variant landed** in
  `crates/cranelisp-types/src/error.rs` with the proposed shape (`dll`,
  `platform`, `expected`, `found`, `location: ErrorLocation`), wired into
  `PlatformError::location()` / `message_static()` / `Display` (the Display
  message names the platform + both hashes + `run /platform-schema <name> and
  rebuild the platform`), and surfaces via `CranelispError::Platform`. Unit
  tests cover the message guidance, the static message, the location accessor,
  and the `CranelispError` delegation. `public-api.txt` regenerated (additive
  diff: the new variant + 5 fields). Workspace check green. **0288's
  `--run`/`--link` refusal sites can now consume this variant.**
- **DEFERRED — `schema_literal` removal stays with the backend consumer.**
  Removing `SymbolTable.schema_literal` from `cranelisp-types` would break the
  ONLY consumers, which live OUTSIDE types: the backend cache
  (`cache/mod.rs` v2 rustdoc + the two `cache/serialize.rs` round-trip tests).
  Removing it from types takes the workspace red. Per the load-path rule
  (keep `cargo check --workspace` green), the field is **left in place with a
  precise RETIREMENT-PENDING note** on its rustdoc pointing at
  `platform-interface.md` §6.5/§6.6 and the backend cascade (FIXME 0287). The
  backend fire (0287) deletes the field + its cache round-trip, then the three
  construction sites in `module.rs` drop. This FIXME stays OPEN to track that
  residue.

# cranelisp-types: add the `PlatformError` layout-hash-refusal variant (Decision 0042)

## Issue

The platform-interface design (`platform-interface.md` §5.5.4 / §6.4, user-ratified
2026-06-07) gates platform loading on a layout-hash check: the host regenerates
the schema from its live tables and compares the canonical hash to the DLL's
exported `__cranelisp_layout_hash_<name>`. **REPL warns-and-loads; `--run` and
`--link` REFUSE.** The refusal must surface as a **new `PlatformError` variant**
carrying `ErrorLocation` per Decision 0042 (the enum is `cranelisp-types`-hosted;
authoring the variant is `/arch`'s — cascade-when-actioned residue named in both
`platform-interface.md` and the `CLAUDE.md` Decisions-drain entry for 0042).

FIXME 0288 (`/dev` int — the platform load-path rewrite) consumes this variant at
the `--run`/`--link` refusal sites; it cannot land the refusal path until the
variant exists. This is the blocking dependency for 0288's hash-gate.

## Proposed resolution

Add to `cranelisp_types::PlatformError` (mirroring the existing variants'
`{ dll, …, location: ErrorLocation }` shape):

```rust
/// The host-regenerated schema layout hash does not match the DLL's exported
/// `__cranelisp_layout_hash_<name>`. Refused in `--run` / `--link`
/// (REPL warns-and-loads instead). Carries both hashes + rebuild guidance.
LayoutHashMismatch {
    dll: std::path::PathBuf,
    platform: String,
    expected: String,  // host-regenerated (canonical) hash
    found: String,     // DLL-exported hash
    location: ErrorLocation,
},
```

Regenerate `crates/cranelisp-types/public-api.txt` in the same change-set; the
variant is a new public surface line (named in `bounded-contexts.md` §7 if a
narrative entry is warranted, per the retired-types-facade convention).

## Context

Cascade-when-actioned residue of the platform-interface cascade (Decision 0042).
Pairs with FIXMEs 0286 (platform macro — landed), 0287 (backend — landed), 0288
(int load path — S77), 0289 (qa e2e). The `schema_literal` removal in
`cranelisp-types` (also named in the platform-interface §7 cascade) is the other
types-crate residue — fold into this change-set or a sibling at /arch's discretion.
