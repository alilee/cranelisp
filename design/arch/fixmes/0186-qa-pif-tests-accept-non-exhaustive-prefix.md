---
number: 0186
target: /qa
filed_by: /dev (backend)
filed_at: 2026-05-15
sprint_filed: 67
refers_to: tests/facade_pif_rows.rs row_01_code_enum_named_in_backend_pub_api, row_05_linker_error_enum_named_in_backend_pub_api, rows_02_03_compilation_error_enum_named_in_backend_pub_api, rows_03_04_linker_and_object_artefact_named_in_backend_pub_api, design/arch/facades/backend.md §"`#[non_exhaustive]` DTOs"
status: open
---

# qa — PIF test row parsers must accommodate `#[non_exhaustive]` prefix on pub-api lines

## Issue

Sprint 67 Wave 3 row 1 (Code enum relocation) + row 2-5 (typed error / artefact DTOs) lands the relocated/new types in `crates/cranelisp-backend/public-api.txt`. Per `facades/backend.md` §"`#[non_exhaustive]` DTOs", every one of `Code`, `LinkerArtefact`, `ObjectArtefact`, `CompilationError`, `LinkerError` carries `#[non_exhaustive]`. `cargo public-api`'s simplified output prefixes the line accordingly:

```
#[non_exhaustive] pub enum cranelisp_backend::Code
#[non_exhaustive] pub enum cranelisp_backend::CompilationError
#[non_exhaustive] pub enum cranelisp_backend::LinkerError
#[non_exhaustive] pub struct cranelisp_backend::LinkerArtefact
#[non_exhaustive] pub struct cranelisp_backend::ObjectArtefact
```

The PIF tests at `tests/facade_pif_rows.rs` lines 60, 85, 102, 121, 126 assert each line `starts_with("pub enum ")` or `starts_with("pub struct ")`. Lines prefixed with `#[non_exhaustive]` fail the prefix check; the tests panic with "not found in public-api.txt" even though the items DO appear.

Affected tests:
- `row_01_code_enum_named_in_backend_pub_api` (Code)
- `rows_02_03_compilation_error_enum_named_in_backend_pub_api` (CompilationError)
- `rows_03_04_linker_and_object_artefact_named_in_backend_pub_api` (LinkerArtefact, ObjectArtefact)
- `row_05_linker_error_enum_named_in_backend_pub_api` (LinkerError)

## Proposed resolution

Relax each `starts_with` check to also accept the optional `#[non_exhaustive] ` prefix. A small helper would centralise the parse:

```rust
fn matches_pub_decl(line: &str, kind: &str /* "enum" | "struct" | ... */, suffix: &str) -> bool {
    let stripped = line.strip_prefix("#[non_exhaustive] ").unwrap_or(line);
    stripped.starts_with(&format!("pub {kind} "))
        && stripped.contains("cranelisp_backend::")
        && stripped.trim_end().ends_with(suffix)
}
```

Alternative: drop the `starts_with` constraint and just check `contains("pub enum") && contains("::Code")`. Less precise; would false-positive on a hypothetical `pub fn ... -> ... pub enum ...::Code`-shaped doc-string (unlikely in practice).

## Operational implication / Context

This is purely a test-parser fix, not a substantive PIF row. The items exist in the baseline post-Wave-3 row 1 + rows 2-5; the test assertions just don't recognise them. The `/dev (backend)` Wave 3 work is complete from the source-of-truth side (facade + baseline); only the test parsers lag.

Wave gate: this does NOT block /dev (backend) Wave 3 close. The PIF test mismatch is a /qa-side parser issue, not a backend-side facade-compliance gap.
