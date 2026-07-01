---
number: 0493
target: /dev
filed_by: /sprint
filed_at: 2026-07-01
sprint_filed: 97
refers_to: CLAUDE.md §Skills table, src/CLAUDE.md (dep graph), design/backend/io-trampoline.md, crates/cranelisp-primitives/src/{bool,int,float,ring0,operator}.rs, crates/cranelisp-intrinsics/src/alloc.rs, crates/cranelisp-types/src/marshal.rs, src/repl.rs, src/observability/tests.rs, audits/{cranelisp-primitives-s87.md,primitives-2026-06-14.md} (LOW-1)
status: open
---

# Repo-wide doc/code sweep — retire stale `cranelisp-runtime` references (D43-split debt)

## Issue

`cranelisp-runtime` was split into `cranelisp-primitives` + `cranelisp-intrinsics` at S73 Decision-43, but stale references to the gone crate persist in **live** docs + code (excluding historical archives/review-reports/audits, which correctly record past state). Surfaced during the S97 ownership tidy — the `reactor.md` relocation fixed the doc *placement* + path cross-refs but did NOT sweep the `cranelisp-runtime` *crate-name* references. Part of this is already the open audit finding **LOW-1** (`audits/cranelisp-primitives-s87.md` §LOW-1 / `audits/primitives-2026-06-14.md`), scoped there to the `primitives` rustdocs; this FIXME widens it to the whole live surface.

**Priority (ownership-directing / contradicts the S97 tidy):**
- `design/backend/io-trampoline.md` (lines ~13/237/402/459) — "the trampoline lives in `cranelisp-runtime`" → it lives in `cranelisp-intrinsics` (see `design/intrinsics/reactor.md`, BC §4b). Doubly-wrong post-tidy.
- `CLAUDE.md` §Skills table (line ~67) — "/platform … `cranelisp-runtime/`" → `cranelisp-platform/` + (the runtime crates are backend-paired, not /platform-owned).
- `src/CLAUDE.md` (lines ~269-270) — dep graph lists `cranelisp-runtime` → `cranelisp-primitives` + `cranelisp-intrinsics`.

**Code rustdoc / comments (LOW-1 class — mechanical, past-tense the migration narrative per the `marshal.rs:25` model):**
- `crates/cranelisp-primitives/src/{bool,int,float,ring0,operator}.rs` (+ `ring0.rs` also cites retired `facades/backend.md` → BC §3).
- `crates/cranelisp-intrinsics/src/alloc.rs:185`, `crates/cranelisp-types/src/marshal.rs:6`, `src/repl.rs:230`, `src/observability/tests.rs:515`.
- Minor: `design/int/concurrency-test-strategy.md:339` (a `rg` example naming the crate).

## Proposed resolution

Mechanical doc-only sweep (per-crate `/dev` where the file is code; the design-doc + CLAUDE.md edits go to their owners — `/design` backend for `io-trampoline.md`; the project `CLAUDE.md` skill-table + `src/CLAUDE.md` are int/governance). Replace live `cranelisp-runtime` references with the correct successor (`cranelisp-intrinsics` for runtime internals / `cranelisp-primitives` for the callable surface), past-tense any migration narrative (the `crates/cranelisp-primitives/src/marshal.rs:25` "lifted from the pre-D43 runtime crate" one-liner is the model), and swap retired `facades/backend.md` → BC §3. Verify: `rg 'cranelisp-runtime|cranelisp_runtime' <live-dirs>` → 0 (archives/audits/review-reports excepted). Supersedes/absorbs audit LOW-1.
