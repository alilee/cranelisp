---
number: 0635
target: /design
filed_by: /sprint
filed_at: 2026-07-17
sprint_filed: 111
refers_to: design/backend/audit-drain-s111.md §1.2;
  crates/cranelisp-backend/src/exe.rs:54 (dead generate_startup_object) vs src/exe.rs:50 (live int copy, S76 §4.4);
  design/backend/implementation-slice-s66.md (unarchived executed one-shot);
  S111 CS-1 /review findings I3 + I4
status: open
---

# Two design/backend doc-currency corrections from CS-1 review

## I3 — `audit-drain-s111.md §1.2` exe.rs premise is factually wrong

§1.2 states backend's `generate_startup_object` is "production-live … called via
`src/exe.rs:50` → `session_v4/lifecycle.rs`". This **conflates int's own live copy with a
re-export**. Verified (CS-1 /dev + /review): the production `--link` startup emission was
relocated to int at **S76 §4.4** (`src/exe.rs:50`, called from `session_v4/lifecycle.rs:2015`);
backend's copy (`crates/cranelisp-backend/src/exe.rs:54`, + `_checked`/`define_cstr_data`) has
**no production caller** — only `exe/tests.rs` reaches it. CS-1 kept an honest
`#[allow(dead_code)]` and fixed only the stale marker text; the design doc still stands wrong
with nothing driving its correction.

**Action:** correct §1.2, and decide the real disposition of backend's orphaned copy —
delete it, or keep it as a test-validated reference (with a rustdoc note that int owns the
production path). A `/design` call.

## I4 — the CS-1 R8 archive-move rider was not executed

SPRINT.md CS-1 said "R8 archive moves … execute in CS-1", but `design/backend/implementation-slice-s66.md`
is still live/unarchived (CS-1 touched no design files). (The paired `git rm FIXME 0096`
reference is stale — 0096 was already deleted at S75 close; only the archive move remains.)
Now that CS-1 deleted `compile_defn`, `implementation-slice-s66.md` is cleanly archivable.

**Action:** move `implementation-slice-s66.md` → `design/backend/archive/` (honouring the
`archive/README.md` cite-with-care curation — do NOT move the two docs it deliberately keeps live).
