---
number: 0919
target: /arch
filed_by: /sprint
filed_at: 2026-07-26
sprint_filed: 119
refers_to: crates/cranelisp-types/src/module.rs:146-151,622,1193,1836,2510,2518,2529 + crates/cranelisp-types/CLAUDE.md + design/arch/facades/int.md:281 + design/arch/facades/frontend-audit-s70.md:309 + crates/cranelisp-types/src/view.rs:16
status: open
---

# Facade-truth pass over `cranelisp-types` rustdoc — retract the phantom narratives, compact the history, re-anchor the citations

## Provenance

`audits/cranelisp-types-s118.md` recommendations **R2 + R4 + R5**, all **ACCEPTED** at
Sprint 119 Phase 1 (user disposition 2026-07-26). Filed as one FIXME because the
assessment itself states R2/R4/R5 are *"one coherent facade-truth pass if accepted
together"* — same files, same pass. Filed by `/sprint` per METHOD §2.6.

The assessment's verdict, quoted: the architecture would be reproduced "very nearly
verbatim" by a second implementation; what it would *not* reproduce is "inline archaeology
making the canonical facade partly fictional". Priority is **truth-restoration, not
redesign**.

## Issue

Verified against source 2026-07-26 (METHOD §3.3 verify-first). Every claim holds; one is
stronger than recorded.

### R2 — the facade describes things that do not exist

**The phantom `dll` narrative — four sites, all verified phantom:**

- `module.rs:622` — "the DLL handle lives on the platform module's own `SymbolTable.dll`"
- `module.rs:1193` — "retained on that platform module's own `SymbolTable.dll: Option<D>`
  field (via the `D: DllStore` generic)"
- `module.rs:1836` — "loaded into the platform module's `SymbolTable.dll`"
- `module.rs:2518` — "`SymbolTable.dll` retains the loaded DLL handle"

The struct is `pub struct SymbolTable<C: CodeStore = (), L: LinkerStore = ()>`
(`module.rs:100`) — **two** generics, no `D`, and **no `dll` field**. `DllStore` occurs
exactly once in the entire repo: inside the `:1193` comment that invents it. The handles
actually live in the int binary (`src/platform.rs:22`, retained in
`SharedState::kept_dlls` at `:34`/`:53`).

**Stronger than the audit recorded**: `module.rs:2510` already states the *opposite* of
`:2518` four lines earlier — "loaded DLL handle) is NOT carried here". The file is
self-contradictory as well as stale, so a reader cannot resolve it by reading more.

**The 31-sprint concurrency limbo** (S87 Finding 3, still open): `module.rs:146-151`
documents a DashMap-inner / atomic / `&self`-write "facade target" pointing at a facade
retired ~50 sprints ago. The audit's demand is **"no third state"** — either formally
retract it (one line in BC §7 recording why the simpler model is the end-state) or give it
a live design home with a sprint.

**Retired-doc citations**: `design/arch/facades/int.md:281`,
`design/arch/facades/frontend-audit-s70.md:309`, and the malformed `view.rs:16`
self-citation.

**`PlatformSpec.name: String`** (`module.rs:2529`) — narrow to `ModuleName` in a small
change-set, or record a standing decision with a **real trigger** in its rustdoc.

### R4 — over-documentation as decay-in-waiting

`module.rs` is roughly two-thirds comment mass. The `ModuleEntry::Macro` retirement is
narrated in four places; sprint and submission numbers are load-bearing anchors; the
Decision-45 placement narrative is duplicated.

### R5 — drifted citations in the crate `CLAUDE.md`

`callable_got_slot` 1318→1445, `is_callable_target` 1354→1485, `defined_symbols` 676→782,
`not_found` `resolve.rs:803`→1097, `mode_summary` 1377→1549, `PlatformSpec.name` 2348→2529,
plus the `PlatformSpec` note's dead-brief pointer.

## Proposed resolution

1. **R2**: rustdoc describes only the as-built model. Cut or correct the four `dll`
   mentions and reconcile the `:2510`/`:2518` contradiction. Retract the concurrency target
   in BC §7 **or** give it a design home and a sprint — no third state. Fix the three
   retired/malformed citations. Settle `PlatformSpec.name`.
2. **R4**: each item's rustdoc states the current contract plus **at most a one-line
   provenance pointer** (git / BC §7 / the ruling doc); retired-shape narratives compress to
   one line; no citation targets a retired document. **Doc-only** — `public-api.txt`
   unchanged, S20/S21 behaviour pins untouched. The audit's explicit guard: do **not** thin
   genuinely load-bearing contract notes (serde discipline, accessor read-throughs,
   exception classes). The test is *"would a new reader find the live contract without
   sifting history"*, not raw line count.
3. **R5**: citations name **symbols** (optionally file-only) rather than line numbers, or
   numbers refreshed with a preference note. Every pointer must resolve.

**Cost/risk**: R2 small-to-medium, R4 medium, R5 small — one pass over the same files.

## Relationship to other S119 work

- **R3** of the same assessment is **not filed here** — it is scheduling weight on the
  existing **FIXME 0748** (injective GOT data-symbol mint), which rides the S119 types
  window opened by 0869's `CACHE_SCHEMA_VERSION` 23→24 bump and 0898's `result_root()`
  collapse.
- **R1** is filed separately as **0918** (dead public surface + the Decision-39 append
  carrier), which also carries a `write_structural_decls` phantom found in the same
  neighbourhood.
