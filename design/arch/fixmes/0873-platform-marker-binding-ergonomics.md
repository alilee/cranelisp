---
number: 0873
target: /design
filed_by: /sprint
filed_at: 2026-07-25
sprint_filed: 118
refers_to: audits/cranelisp-platform-s117.md §R4;
  crates/cranelisp-platform/src/adt.rs;
  platforms/shapes/src/lib.rs;
  platforms/shapes-badabi/src/lib.rs;
  exemplar/platforms/web/src/lib.rs
status: open
blocked_on: /dev(platform) implementation window (S119+) — /arch gate PASSED 2026-07-25
---

# Decide marker-binding ergonomics — deferral trigger has fired (audit R4)

Crate in scope: `cranelisp-platform` (design decision; `/arch` review required
if the chosen mechanism changes public API).

User-accepted S117 platform-audit recommendation R4, **explicitly pulled into
S118 by the user** (2026-07-25, S118 Phase 1). Quoting the assessment:

> A focused design compares keeping explicit marker impls, a derive, and a
> macro/generated binding. It chooses the smallest shape that either makes
> schema-name agreement structural or explicitly accepts runtime failure with
> a production-path negative witness and clear diagnostics. If explicit impls
> remain, the rationale and trigger for reconsideration are recorded; merely
> adding another positive test does not cure the mismatch risk.

Context: platform ADT bindings hand-write `CLAdtType::TYPE_NAME` as a string
that must agree with the generated schema; nothing checks it before runtime.
The S87 assessment deferred a mechanism until a real multi-ADT platform
existed; the web platform now hand-writes four marker types
(`exemplar/platforms/web/src/lib.rs:89-115`).

Cost: medium (design only this sprint; any implementation is a follow-on).
Scheduled: S118 platform slice (with 0870/0874).

## Progress — 2026-07-25, `/design`(platform), S118 Phase 3

**Design delivered: `design/platform/adt-marker-binding.md`** (cited from
`design/platform/platform.md` §12). The FIXME stays OPEN because two things
remain: the `/arch` selection gate and the implementation.

Comparison outcome — the three shapes were compared and the smallest that makes
schema-name agreement **structural** was selected:

- **Recommended (Option 3):** an optional `adts:` key on `declare_platform!`'s
  `schema:` arm that emits each marker (`struct` + `impl CLAdtType`, author
  rustdoc preserved via `$(#[$attr:meta])*`) **and** a `const _: () = assert!(…)`
  against a new `pub const fn schema_declares_type(artifact, key)` — a
  paren-depth-tracking const byte-scanner in `declare.rs` beside
  `extract_layout_hash`. A name mismatch becomes a **build error**, including for
  construct-only markers that runtime never checks. No new crate, no new
  dependency, no `CLAdtType` contract change.
- **Rejected (Option 2, derive):** a proc-macro crate is a build dependency for
  every out-of-tree DLL author and a second public surface, and it still cannot
  check the name without introducing a second, non-compiler-tracked source of
  truth for the artifact path.
- **Rejected as primary (Option 1, keep explicit impls):** retained only as the
  fallback if `/arch` rejects Option 3, with its compensation package recorded
  (design §11). Decisive finding: on the production path the trigger fired for,
  three of web's four markers are dereferenced inside `PollFn` `extern "C"`
  frames that have **no** fault containment (unlike `CLIO::effect` thunks, which
  carry a DLL-local `catch_unwind`), so a mismatch there is a **process abort**,
  not a diagnosable runtime failure. "Explicitly accept runtime failure with
  clear diagnostics" would therefore first require adding poll-boundary
  containment — strictly more work than the structural cure.

**`/arch` gate applies (S118 arch ruling 5).** Public-surface delta to approve:
one added `public-api.txt` line (`schema_declares_type`) + the new `adts:` macro
key as external-author surface. `CLAdtType`, `CLAdt`, `Schema`, `cranelisp-types`,
the cache schema, the artifact grammar and the host load path are all unchanged.

Also carried by this FIXME (crate-internal, lands with the implementation, no
gate): `resolve_field`'s miss diagnostic at `adt.rs:359-370` misattributes a
**type-key** miss as a field miss — the exact message an author debugging this
mismatch would read. Probe `lookup_type` first and report the type-key miss
distinctly.

Next: `/arch` reviews the selection; on approval, `/dev`(platform) implements in
a follow-on wave (S119+). No test cells this sprint per
`tests/plan/s118-test-plan.md` §7.

## `/arch` selection gate — APPROVED (2026-07-25, S118 Phase-3 exit)

**Option 3 is APPROVED as designed** (`design/platform/adt-marker-binding.md`).
Grounds: it is the Principle-18 structural form — schema-name agreement becomes
a build error across every marker, including construct-only markers runtime
never checks — at Principle-6 minimum cost (one `pub const fn` + one macro arm,
no new crate, no build dependency, no `CLAdtType`/`CLAdt`/`Schema`/types/cache/
artifact-grammar change). The two rejections are sound: the derive (Option 2)
adds a build dependency and a second public surface on the external facade and
STILL needs a second non-tracked source of truth for the artifact path (a
Principle-7 violation by construction); keep-explicit-impls (Option 1) founders
on the call-path asymmetry the design isolated — poll-shape `extern "C"` frames
have no fault containment, so a marker mismatch there is an unattributable
process abort, and "accept runtime failure with diagnostics" would first
require poll-boundary containment, strictly more work than the cure. Option 1
stands as the documented fallback (design §11) only if implementation
falsifies the const-scanner premise.

**Approved public-surface delta** (lands S119+ with the implementation, per
baseline-diff discipline): one `crates/cranelisp-platform/public-api.txt` line
(`pub const fn schema_declares_type`) + the `adts:` key on `declare_platform!`
as external-author surface. Conditions on the implementing change-set:

1. **Grammar coupling is named at both sites.** The const byte-scanner is a
   second reader of the schema-artifact text (beside the runtime parser). That
   is acceptable on the `extract_layout_hash` precedent (const context cannot
   reach the runtime parser), but the rustdoc of `schema_declares_type` AND of
   the runtime parser's grammar home must each cite the other, so an
   artifact-grammar change is a named two-site change, not a silent drift.
2. Baseline regeneration + source-rustdoc surface record + the BC §5 note ride
   the same change-set (no pre-implementation BC edit — the design doc is the
   record until then).
3. The adjacent `resolve_field` type-key-miss diagnostic fix (`adt.rs:359-370`)
   rides the implementation as designed (crate-internal, no gate).

FIXME stays OPEN for the S119+ implementation; the selection question is
CLOSED.
