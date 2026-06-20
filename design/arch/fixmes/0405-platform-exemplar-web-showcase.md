---
number: 0405
target: /platform
filed_by: /port
filed_at: 2026-06-17
sprint_filed: 86
refers_to: exemplar/plan-exemplar.md §"Web Platform DLL", §"Two IO Models", §"Module Decomposition"
status: open
---

# Author the Sudoku exemplar's web-platform DLL (browser showcase stretch)

## Issue

The Sudoku exemplar's headline target is now the **stdio CLI** (S86 Phase 6b
rebaseline): `exemplar/user.cl` tells the full story end-to-end —
`parse-form-body` → `make-grid` → `solve` → ASCII board + HTML page — entirely
through `(platform stdio)`. That is the committed showcase.

`plan-exemplar.md` also specifies a **web platform** (a Rust `cdylib` embedding
a small HTTP server, exporting `listen`/`accept`/`send` for Model A and `serve`
for Model B via `declare_platform!`, plus the `Request`/`Response` opaque
accessors). The pure handler (`handle :: Request → Response`), HTML generation
(`html/solution-page`, `form-page`, `error-page`), and form parsing
(`form/parse-form-body`) are **already implemented and tested** in the exemplar
— only the platform DLL and the IO wiring (`exemplar/main.cl`, routing) are
missing. `exemplar/platforms/web/` is net-new and has never been built.

This was scoped OUT of the user-facing S86 sprint (it needs `/platform` to
author a Rust DLL — outside `/port`'s reach and not on the de-leak critical
path). It is preserved here as a deliberate future stretch, not dropped.

## Proposed resolution

When `/platform` has capacity, author `exemplar/platforms/web/` per
`plan-exemplar.md` §"Web Platform DLL":

- `Cargo.toml` + `src/lib.rs` `cdylib` embedding `tiny_http` (or similar).
- Export `listen`/`accept`/`send` (Model A) and `serve` (Model B) plus the
  pure data accessors (`request-method`/`request-path`/`request-body`/
  `response`) via `declare_platform!`.
- `Request`/`Response` as opaque heap values (alloc via `HostCallbacks`,
  pointer passed as `i64`), same pattern as ADT field access.
- Add `exemplar/main.cl`: `(platform web)`, the `handle` router (already
  sketched in plan-exemplar.md §"Request Routing"), and BOTH serve models.

The pure core is ready to wire — this is a platform-authoring + IO-integration
task, not a language-feature task.

## Operational implication / Context

- The exemplar already validates ADTs, traits, pattern matching, closures,
  modules, the curated stdlib surface, and stdio IO without the web platform.
  The web DLL adds: (a) a compelling browser demo, (b) end-to-end validation
  of `declare_platform!` + opaque-heap-value accessors at application scale,
  (c) the "purity enables concurrency" teaching moment (Model B).
- Until this lands, `plan-exemplar.md` documents the web platform as a future
  stretch (the stdio CLI is the committed showcase). `exemplar/main.cl` remains
  unwritten by design — do not stub it.
- No blocking dependency on any other S86 wave; this is independent stretch
  work for a future sprint.
