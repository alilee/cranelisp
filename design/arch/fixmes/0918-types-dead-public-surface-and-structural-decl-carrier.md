---
number: 0918
target: /arch
filed_by: /sprint
filed_at: 2026-07-26
sprint_filed: 119
refers_to: crates/cranelisp-types/src/module.rs:2497,2566,728,724 + crates/cranelisp-types/src/pipeline.rs:23-93 + crates/cranelisp-types/src/lib.rs:130-132,304,352 + src/process_form/form_dispatch.rs:86,96
status: open
---

# Delete the five zero-consumer public types and resolve the Decision-39 structural-decl append carrier

## Provenance

`audits/cranelisp-types-s118.md` recommendation **R1**, **ACCEPTED** at Sprint 119
Phase 1 (user disposition 2026-07-26). Filed by `/sprint` per METHOD §2.6.

The assessment's framing, quoted: this is the recurring **S87 Finding 2 dead-surface
class** — what a second implementation "would *not* reproduce". The auditor grades the
crate's design **Strong** and its realisation **Adequate**, and states the priority as
*truth-restoration of the facade, not redesign*. Half-measures explicitly fail the bar.

## Issue

Verified against source 2026-07-26 (METHOD §3.3 verify-first). All claims hold; three
corrections and one addition are recorded below.

**Five zero-consumer public types**, all re-exported and all dead:

| Type | Site | Consumers |
|---|---|---|
| `ImplSexp` | `module.rs:2497` | none repo-wide; only the re-export at `lib.rs:304`. Not a field type anywhere, including inside the crate. |
| `CompileResult` | `pipeline.rs:23` | none outside the crate |
| `CallEdge` | `pipeline.rs:75` | referenced only by `CallInfo`/`CallGraph` |
| `CallInfo` | `pipeline.rs:86` | referenced only by `CallGraph` |
| `CallGraph` | `pipeline.rs:93` | none |

The call-graph cluster is entirely self-referential — dead as a unit. `lib.rs:130-132`
narrates all of them as live.

**The Decision-39 append carrier is bypassed and, in fact, wholly unused.** Stronger than
the audit recorded: `append_structural_decl` (`module.rs:728`) has **zero callers
repo-wide**, and `StructuralDeclEntry` (`module.rs:2566`) is **constructed nowhere** — its
only use is the match inside its own consumer method. The production bypasses are two
direct pub-Vec pushes:

- `src/process_form/form_dispatch.rs:86` — `st.platforms.push(spec.clone())`
- `src/process_form/form_dispatch.rs:96` — `st.submodules.push(decl.clone())`

**Correction to the audit's third cited bypass**: `src/save.rs:1971` is inside
`#[test] fn should_regenerate_false_when_submodule_retains_inline_body` — test code, not
production. Every other direct push in the tree is likewise test-only
(`src/worker/tests.rs:1125,1131,1136,1223,1229,1533,1546`;
`crates/cranelisp-backend/src/cache/serialize/tests.rs:249`).

**Addition — a sixth phantom in the same rustdoc neighbourhood.** `module.rs:724` and
`crates/cranelisp-frontend/src/module_extract.rs:47` both cite
`SymbolTable::write_structural_decls` as the bulk-load API. **No such method exists
anywhere in the tree.** It belongs in this change-set, not 0919's, because it is the same
carrier's documentation.

## Proposed resolution

1. Delete the five types and the `lib.rs:130-132` narrative that describes them as live;
   drop the re-exports at `lib.rs:304,352`.
2. Resolve the append carrier **one way** — the audit is explicit that half-measures fail:
   either int routes through `append_structural_decl` (and the two `form_dispatch.rs`
   direct pushes become a standing review flag), or carrier + method + `StructuralDeclEntry`
   are deleted and the `pub` Vec fields are recorded as the contract. Given the helper has
   zero callers today, the second option is the smaller truth.
3. Delete or correct the `write_structural_decls` citations at `module.rs:724` and
   `module_extract.rs:47`. The latter is outside `/arch`'s files — file a rider FIXME to
   `/design`(frontend) or fold it if `/arch` holds the pen on that line.
4. Regenerate `public-api.txt` in the **same change-set**.

A `/dev`(int) rider is needed only if the route-through option is chosen.

**Cost/risk**: small, per the assessment.
