---
number: 0131
target: /qa
filed_by: /qa
filed_at: 2026-05-04
sprint_filed: 64
refers_to: tests/legacy/sprint60_observability.rs
status: open
---

> **S81 W-C (backend filter-grammar coverage confirmed → RE-TARGET /qa for file
> deletion):** The `CRANELISP_CODEGEN_DUMP` filter grammar is already exhaustively
> unit-tested backend-internal in `crates/cranelisp-backend/src/lib.rs`
> `#[cfg(test)] mod clif_dump_tests` (6 tests), which IS the
> backend-crate-internal home this FIXME asked for:
> - `filter_unset_or_empty_never_matches` — covers legacy tests #3 (unset → no
>   CLIF) and #4 (empty value → no CLIF): `clif_dump_matches(None, ..)` and
>   `clif_dump_matches(Some(""), ..)` both `false`.
> - `filter_wildcard_matches_every_function` — covers legacy test #1 (`=*` matches
>   every fn).
> - `filter_module_only_matches_any_symbol_in_that_module` +
>   `filter_module_colon_symbol_matches_that_exact_function` — cover legacy test #2
>   (`=user` filters to that module; literal dotted paths, not prefixes).
> - `write_clif_dump_frames_header_and_trailer` +
>   `write_clif_dump_adds_trailing_newline_when_body_lacks_one` — the frame-render
>   shape the legacy stderr assertions checked.
>
> The 4 legacy tests are subprocess `--run` smoke proving the env var *plumbs
> through* to stderr — the parse/grammar half (the only backend-internal half) is
> already collapsed to the 6 unit tests above; the subprocess-plumbing half is
> e2e and not backend-crate-internal. No further backend port needed.
>
> **Disposition: RE-TARGET → /qa.** Owed work is the legacy-file deletion +
> `tests/legacy/README.md` row removal.

# Harvest tests/legacy/sprint60_observability.rs into cranelisp-backend unit tests

## Issue

The Sprint 64 test-port quarantined `tests/legacy/sprint60_observability.rs`
(182 LOC, 4 tests). The file subprocess-launches `cranelisp --run` with
`CRANELISP_CODEGEN_DUMP={*,user,<unset>,<empty>}` and asserts on stderr
CLIF dump frames.

The subject under test is the `CRANELISP_CODEGEN_DUMP` env-var filter, a
backend debugging aid. It is NOT a spec'd language behaviour —
`CRANELISP_*_TRACE` and similar env vars are debugging aids per
`tests/CLAUDE.md` §"Diagnostic Logging". Stderr is reserved for traces
per the spec; there's no normative requirement that the binary emit CLIF
under any env var setting.

The four assertions:

1. `CRANELISP_CODEGEN_DUMP=*` emits CLIF for every freshly-compiled fn.
2. `CRANELISP_CODEGEN_DUMP=user` filters to that module only (negative
   guard: other modules absent).
3. `CRANELISP_CODEGEN_DUMP` unset emits no CLIF (silent-by-default).
4. `CRANELISP_CODEGEN_DUMP=` (empty value) treated as disabled.

## Proposed resolution

Unit tests for the filter grammar already live with `/backend` (see
`clif_dump_matches_*` and `write_clif_dump_*` `#[cfg(test)]` modules in
`crates/cranelisp-backend/src/lib.rs`). Extend that suite with one or
two additional integration tests inside the backend crate that
subprocess-launch the binary (the backend's `[dev-dependencies]` already
imports `tempfile`; adding `Command::new(binary_path)` is a one-line
addition).

Recommended shape:

- A single helper `run_with_codegen_dump(env_value: Option<&str>) ->
  String /* stderr */` inside the existing `clif_dump_*` test module.
- Four small tests collapsing the four assertions:
  - `=*` produces CLIF frames + body for the trivial source.
  - `=user` filters to user; absent for unrelated module paths.
  - unset → no CLIF.
  - empty value → no CLIF.

Or, since the env var → filter parse is already unit-tested in
`clif_dump_matches`, the four tests collapse to a single integration test
per file that proves the env var actually plumbs through to stderr (the
"silent by default + matching prefix appears under filter" smoke).

## Operational implication / Context

This harvest is a coverage-preservation commitment from S64. Until it
lands, the file is inert. The CLIF-dump filter is exercised every time a
`/backend` developer enables `CRANELISP_CODEGEN_DUMP` for debugging — a
regression that broke the env-var pipeline would surface during their
next debug session.

When complete, delete `tests/legacy/sprint60_observability.rs` and
remove its row from `tests/legacy/README.md`. Git history preserves
provenance.
