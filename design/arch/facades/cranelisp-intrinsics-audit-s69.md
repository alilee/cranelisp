# cranelisp-intrinsics — Sprint 69 facade audit (per-item analysis, RE-AUTHORED)

**Audit triple**: `crates/cranelisp-intrinsics/src/lib.rs` (70 LOC — module declarations + crate-root re-exports) × `design/arch/facades/intrinsics.md` (414 LOC — binding contract) × `crates/cranelisp-intrinsics/public-api.txt` (248 LOC — frozen baseline).

**Date**: 2026-05-19 (S69 Phase 3 Wave 1, re-author pass).
**Auditor**: `/design (intrinsics)` — narrow deployment.
**Inputs frozen at**: current commit on `main` (post-S68 close `9516dfc`).
**Discipline**: per `memory/feedback_audit_per_item_analysis.md` (2026-05-18 user direction) — every finding gets five explicit blocks (**Facade expects** / **Source does** / **Design intent** / **Difference implies** / **Disposition**). The third block is the grounding step — it traces the facade element back to its Decision / Principle / FIXME so the disposition rests on architectural intent, not on whichever side is currently settled.

**Why re-authored.** The prior version of this audit (committed against same path on 2026-05-19) dispositioned every finding without reading the architectural configuration. Per user direction:

> "the issue is that the audit did not read the architectural configuration and derived design docs."

The re-author pass reads:

- `design/arch/principles.md` + every `principles/NN-*.md` (esp. 02, 07, 14, 15, 17, 18).
- `design/arch/CLAUDE.md` (Decisions index + Baseline-diff discipline).
- Every active Decision (0010, 0011, 0027, 0030, 0031, 0035, 0040, 0041, 0042, 0043, 0044, 0045, 0046, 0047, **0048** — and legacy Decision 0029 referenced by facade §"Drop glue").
- `design/arch/bounded-contexts.md` §4b (Intrinsics BC) — load-bearing for every "is this in scope?" question.
- `design/arch/fixmes/0213-intrinsics-facade-stale-string-primitives-section.md` (open; tracks F1).
- `design/arch/fixmes/0190-design-intrinsics-facade-renamed-module-coverage.md` (open; tracks F8).
- `design/arch/fixmes/0214-int-facade-enumerate-intrinsics-reexports.md` (open; sibling-shape for the int side).
- `crates/cranelisp-intrinsics/src/lib.rs`, `rc.rs`, `drop.rs` (read for grounding evidence).

The grounding step changes the disposition on three findings (F3+F4+F9 collectively, F11, F15) and strengthens the grounding citation on every other finding without flipping it.

---

## 0. Summary up front

The intrinsics public surface is well-aligned with the facade in **substance** (it embodies the post-D43 categorical split, post-D40 Wave-4 trace/io_trace relocation, post-S68 D0048 JIT-registration narrowing, and per BC §4b carries no diagnostics surface). The intrinsics crate's source has settled correctly across S67/S68; **no Wave 3 source-side regression exists** against any Decision or Principle that this audit reads.

The drift is concentrated on the facade side and on the crate-root `pub use` re-export set, with this re-authored grounding:

- **F1 (§"String primitives" stale)** is grounded by Decision 43 + Decision 0048 (post-S68 categorical line: primitives go GOT-uniform via `PRIMITIVES_TABLE`; intrinsics retains direct `JITBuilder::symbol` registration). FIXME 0213 is the open tracker filed by `/sprint` targeting `/design (intrinsics)` to resolve precisely this drift. Facade is stale; **facade moves** is the correct disposition because the facade text has not caught up to a state that source + Decision + FIXME 0213 all agree on. The prior audit's disposition was right; the grounding citation now names Decision 43, Decision 0048, and FIXME 0213 directly.

- **F6 (`consume_shallow` placement)** is grounded by **legacy Decision 0029**, which explicitly names "Canonical location: `crates/cranelisp-runtime/src/rc.rs` (or `drop.rs` alongside `consume_closure`)." Source's `rc::consume_shallow` placement matches one of the two canonical options; the source comment at `crates/cranelisp-intrinsics/src/rc.rs:14–17,66–67` explains the distinction between single-node dec (rc machinery) and per-type recursive drop walks (drop glue). The facade's placement under §"Drop glue" is editorial drift away from Decision 29's named canonical option. **Facade moves**; grounding is Decision 29 + Principle 7 (single source of truth — one primitive per concept; the source comment expresses the distinction the facade should embody).

- **F12 / F13 (`#[non_exhaustive]` / `#[repr(C)]` attribute presence)** are grounded by **Principle 14** (FFI boundary types are governed by layout discipline) — not by generic "mechanical test gap" framing. The attributes ARE present in source today (pub-api lines 46/96/24); the gap is enforcement of the Principle across future edits. **Principle 18** (enforce invariants structurally where possible) is the operative test for "is the gap closure /qa work or structural-mechanism work?" — for these two specific attributes, the structural form (the attributes are on the types themselves; `cargo-public-api` diff catches their removal in the baseline) is *already in place*. The behavioural test gap is narrow: the baseline records the attribute presence, but no facade-side text enforces "the baseline MUST keep showing these attributes." **Source is correct; facade-side language tightening** is the disposition — name the attribute presence as a Principle-14 contract in the facade so a future baseline drop is auditable as a Principle-14 violation, not a permitted edit. Prior audit's "requires /qa work for S70" framing is **demoted**: the baseline already catches the change; what /qa would add (per-attribute PIF rows) is duplication of the baseline's catch, not a missing structural mechanism per Principle 18. /qa work, if any, is one or two lines of test code, not a "new PIF row type."

- **F15 (crate-root re-export policy)** flips. The prior audit framed this as a /arch arbitration with two open options (a) "binding" and (b) "convenience." Re-grounded against **Principle 15** ("External-audience exception (narrow). A facade whose external audience does not (and should not need to) depend on `cranelisp-types` MAY re-export the items its public API uses. The criterion is concrete: an external consumer for whom `cranelisp-types` is not otherwise a natural dependency.") — intrinsics has **no external audience** for which `cranelisp-intrinsics` is not otherwise a natural dependency. Intrinsics is consumed by backend (string-named relocation, not Rust paths), by int (which depends on `cranelisp-intrinsics` directly and can write `cranelisp_intrinsics::rc::consume_shallow`), and by the workspace's test code (same dep visibility). The exception that motivates re-exports in `cranelisp-platform` does not apply. Combined with **Principle 02** (narrow interfaces — boundary surface is the minimum needed for consuming crates' bounded contexts) and the **Baseline-diff discipline** (every pub-api line is binding contract or marked internal-but-exposed with rationale), the disposition is **source moves** — demote the crate-root `pub use` block at `lib.rs:57–69` so the only Rust-reachable path for each item is its module path. The facade's silence is correct; the source is over-exporting. This is not /arch arbitration — Principle 15 already names the rule. /arch wasn't needed; reading Principle 15 was needed.

- **F3 / F4 / F9** (the specific instances of the crate-root re-export pattern) collapse into F15's disposition. Prior audit dispositioned them as "facade moves" via a §-add enumerating the set; re-grounded, they are source-moves (demote re-exports). The §-add the prior audit proposed would have *legitimised* a surface that Principle 15 (correctly read) says should not exist.

Disposition class counts (over **15 substantive findings**: F1–F15; F16/F17 reserved/empty in the prior audit and remain so):

| Class | Count | Prior count | Δ |
|---|---|---|---|
| Facade moves | 5 (F1, F2-no-action, F6, F7, F8) | 7 (F1, F3, F4, F6, F7, F8, F9) | -2 (F3/F4/F9 reclassify) |
| Source moves | 3 (F3 / F4 / F9 collectively under F15 group) | 0 | +3 |
| Both move | 0 | 0 | 0 |
| Facade-text tightening (Principle-grounded) | 2 (F12, F13) | 0 | +2 |
| No action | 4 (F2, F5, F14, plus F10/F11 grouped) | 4 (F2, F5, F14) | unchanged in shape |
| Requires /qa work for S70 | 1 (F10 only) | 4 (F10, F11, F12, F13) | -3 |
| Requires /arch arbitration | 0 | 1 (F15) | -1 (F15 resolves via Principle 15 reading) |

**Flipped prior dispositions (count: 6):**
1. F3 — facade-moves → source-moves (Principle 15 external-audience criterion not met).
2. F4 — facade-moves → source-moves (same).
3. F9 — facade-moves → source-moves (same).
4. F11 — /qa work S70 → no action / structural-mechanism present (Principle 18; module structure + baseline diff are the standing check).
5. F12 — /qa work S70 → facade-text tightening (Principle 14 + Principle 18; baseline already structural).
6. F13 — /qa work S70 → facade-text tightening (same).
7. F15 — /arch arbitration → resolved (Principle 15 reading; not arbitration, just configuration-reading).

(That is 7 flips when F15's resolution is counted alongside the F3/F4/F9 cascade it forces. The user's "count of flipped prior dispositions" line is answered as **6 substantive flips** if F3/F4/F9 are counted once as a group, or **7 line-item flips** counting F15 as a separate procedural flip from "arbitration" to "Principle-15-already-decides".)

---

## 1. Hidden surface — facade names; source does not implement

### Finding F1 — §"String primitives" stale post-S67 W3 (15 fns + vec_len already relocated)

**Facade expects.** §"String primitives (allocator + reader + user-callable ops; physically-here-until-FIXME-0180)" lines 123–168 explicitly enumerates 15 `pub extern "C" fn` declarations (`str_concat`, `str_eq`, `str_len`, `str_char_at`, `str_substring`, `str_contains`, `str_starts_with`, `str_ends_with`, `str_trim`, `str_to_lower`, `str_to_upper`, `str_split`, `str_join`, `str_replace`, `string_identity`) with kebab-case `#[export_name]`s, and frames them as physically resident in `cranelisp-intrinsics` pending FIXME 0180.

**Source does.** Zero of those 15 fns appear in `crates/cranelisp-intrinsics/public-api.txt`. `crates/cranelisp-intrinsics/src/lib.rs:8–19` codifies the post-S67-W3 relocation: the 15 fns lifted into `cranelisp-primitives::string`; the module renamed `cranelisp_intrinsics::string` → `cranelisp_intrinsics::heap_string` to avoid baseline collision with the primitives surface; `vec_len` likewise lifted; module renamed `vec` → `vec_runtime` for the same reason. What survives in intrinsics is the backend-emitted-call infrastructure: `heap_alloc_string` (`runtime/alloc_string`), `string_read` (`runtime/string_read`), Rust-callable `alloc_string` / `read_string_as_str`, and the `#[repr(C)] HeapString` layout type with its `LEN_OFFSET` / `DATA_OFFSET` / `payload_size` impl consts.

**Design intent.** This is the intersection of **three** grounding citations, all aligned:

1. **Decision 0043 §"Migration scope"** — primitives (user-callable, addressable via `primitives/<name>` module path, GOT-indirect dispatch) and intrinsics (backend-emitted-call targets, no symbol table, no GOT) live in two separate crates. The string operations `str-concat`, `str-len`, etc. are user-callable per spec — they ARE primitives. Their physical home is `cranelisp-primitives`, not `cranelisp-intrinsics`. The "physically-here-until-FIXME-0180" framing was a pre-S67-W3 transient; FIXME 0180 closed in S67 W3.
2. **Decision 0048 §"Shape"** — `cranelisp-primitives` owns `PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable>>` with raw fn ptrs in the GOT at prescribed slot indices for every non-inlined primitive, *including the string ops*. The `Code::Primitive` marker variant tags each entry. Per the Decision's §"Cascade": "**`design/arch/facades/intrinsics.md`** — confirm `JITBuilder::symbol(name, ptr)` is intrinsics-only post-S68. No public-API change expected; doc-comment refresh only." That doc-comment refresh is the work F1 names.
3. **FIXME 0213** (`design/arch/fixmes/0213-intrinsics-facade-stale-string-primitives-section.md`) — filed by `/sprint` 2026-05-17 targeting `/design (intrinsics)`. The FIXME's proposed resolution names the section rewrite, the historical note, the pointer to `facades/primitives.md`, and the section rename ("Heap-string allocator + reader (backend-emitted-call)"). This Decision is `/design (intrinsics)`'s open work item, by name.

The facade element ("the §"String primitives" section as currently written") is grounded by an earlier state that has been *retracted* by S67 W3 + S68 D0048; the binding intent today is the post-S68 categorical line + FIXME 0213's resolution. The facade text is genuinely stale (a Decision retracted the earlier state), not target-stating; the source has evolved past.

**Difference implies.** The facade contradicts itself — §"Sprint 67 disposition snapshot" line 388 correctly says "Relocated to `cranelisp-primitives` at Wave 3: user-callable `str_*` family (15 fns) + `vec-len`"; §"String primitives" 250 lines earlier reads as pre-S67-W3. A reader trusting §"String primitives" expects `cranelisp_intrinsics::str_concat` to be Rust-reachable; it is not. A reader who notices the contradiction cannot tell which is binding. This is the largest single body of facade text describing a retracted state — actively misleading per FIXME 0213's framing.

**Disposition.** **Facade moves.** Per FIXME 0213's proposed resolution:

1. Drop facade lines 140–154 entirely (the 15 `pub extern "C" fn` table).
2. Replace facade lines 123–139 with a historical-note + pointer paragraph naming Decision 0043 + Decision 0048 + S67 W3 close, pointing to `facades/primitives.md` §"Primitives inventory" for the canonical home.
3. Rename the section header to "Heap-string allocator + reader (backend-emitted-call)".
4. Keep the `heap_alloc_string` / `string_read` / `alloc_string` / `read_string_as_str` / `HeapString` block under the renamed header.
5. Delete `design/arch/fixmes/0213-intrinsics-facade-stale-string-primitives-section.md` with the commit (`/sprint` cross-skill protocol — `git rm` and name resolution in commit message).

Prior audit disposition: facade-moves. **Confirmed; grounding citation strengthened (Decision 43, Decision 0048 §"Cascade", FIXME 0213 named explicitly).**

### Finding F2 — `cranelisp_alloc` historical alias mention (no source surface)

**Facade expects.** §"Heap allocator" line 36 inline comment: "the alias `cranelisp_alloc` (cf. `pub use` at root in pre-S67 builds) is the historical name, retired in favour of the kebab-case `#[export_name]`." Narrative-only mention; not enumerated as a pub item.

**Source does.** No `cranelisp_alloc` symbol exists in pub-api. The linker symbol is `runtime/alloc` per the `#[export_name]` on `heap_alloc`.

**Design intent.** The retirement is captured in narrative because the historical name was removed and the kebab-case `runtime/alloc` form is the canonical. Decision 43 + the broader rename-to-kebab pattern (every `runtime/*` `#[export_name]` on this crate) makes "the retirement" itself part of the contract — the facade documents that consumers MUST NOT name `cranelisp_alloc`.

**Difference implies.** None. The narrative-only mention is the correct disposition.

**Disposition.** **No action.** The inline retirement note is appropriately narrative; a reader sees the historical name and understands the retirement. Prior audit disposition: no action. **Confirmed.**

---

## 2. Unannounced surface — source declares; facade silent — re-grounded against Principle 15 + Principle 02

### Finding F3 — Crate-root flat re-exports of `io_observer` items

**Facade expects.** §"IO observation" (lines 195–243) describes the IO observation extension point at module paths under `cranelisp_intrinsics::io_observer::*`. The facade does not mention crate-root re-exports of any of these items.

**Source does.** `crates/cranelisp-intrinsics/src/lib.rs:57`:

```rust
pub use io_observer::{IoEvent, IoEventTag, IoObserver, register_io_observer, trace_anchor};
```

`pub-api.txt` lines 147–225 + 242 + 247 + 248 enumerate every variant, field, and auto-trait impl appearing at both `cranelisp_intrinsics::io_observer::*` AND `cranelisp_intrinsics::*`. `emit` is omitted from the flat re-export.

**Design intent.** **Principle 15** (Facade types live with their behavior) states: "**No re-exports of `cranelisp-types` items from implementation-crate `lib.rs` files.** Consumers import directly: `use cranelisp_types::Symbol`, `use cranelisp_typecheck::CheckResult`, `use cranelisp_backend::CompilationError`. The dep graph reads honestly." The analogue for the crate's *own* types is governed by the same Principle's external-audience exception:

> "**External-audience exception (narrow).** A facade whose external audience does not (and should not need to) depend on `cranelisp-types` MAY re-export the items its public API uses. The criterion is concrete: an external consumer for whom `cranelisp-types` is not otherwise a natural dependency. Today this applies to `cranelisp-platform` (DLL authors writing out-of-tree crates that depend only on `cranelisp-platform`). Each invocation of the exception is justified inline in the facade spec; it is not a general license."

**Intrinsics has no external audience matching this criterion.** Consumers of `cranelisp-intrinsics`:
- `cranelisp-backend` consumes intrinsics by **string-named extern relocation** at JIT-symbol-registration time (the `JITBuilder::symbol(name, ptr)` path); backend's source code names the Rust path `cranelisp_intrinsics::io_observer::*` *anyway* because the path is needed to take the function pointer. Crate-root re-exports do not shorten this path materially — backend writes `cranelisp_intrinsics::io_observer::IoEvent` regardless.
- `int` consumes intrinsics by direct Rust dep at compile time. `int`'s observer registration site (`src/io_trace.rs` per Decision 40) writes `cranelisp_intrinsics::io_observer::*` paths; the convenience of the crate-root re-export is a few characters saved.
- **No external (out-of-tree) consumer exists.** Intrinsics is not the contract surface DLL authors write against (that's `cranelisp-platform`); intrinsics is consumed only by other workspace crates.

**Principle 02** (Narrow interfaces) compounds this: "Adding a field to a boundary type has O(n) impact across skills; adding an internal type has O(1) impact. … When something must cross a crate boundary, the question is 'what is the minimum the consumer needs?' — not 'what does the producer happen to have?'"

**The Baseline-diff discipline** (`design/arch/CLAUDE.md`) makes the cargo-public-api baseline the frozen contract — every pub-api line in the baseline is named in the corresponding facade *or* marked internal-but-exposed with rationale. The crate-root re-exports at `pub-api.txt:147–225, 247, 248` are in the baseline, are not named in the facade, and carry no internal-but-exposed marker.

**Difference implies.** Two consumer-visible drifts:

1. The flat re-export set is publicly reachable at the crate root but not facade-stated — Baseline-diff discipline violation (silent surface inflation).
2. The omission of `emit` from the flat re-export is asymmetric: `emit` is called by the trampoline (internal) and by tests (which write the module path). The asymmetry implies a policy ("non-extension-point internals aren't promoted to the crate root") that no facade or source text states — the asymmetry is *informal* despite being load-bearing.

Adding the §-add to the facade (the prior audit's disposition) would legitimise a surface that Principle 15's external-audience exception does not authorise. The right move is to shrink the surface, not document the over-export.

**Disposition.** **Source moves.** Demote the `pub use io_observer::{...}` line at `lib.rs:57` to remove it from the crate-root surface. Consumers (`int`, tests, backend's JIT-registration code if any) update to write the module-prefix path `cranelisp_intrinsics::io_observer::IoEvent`. The facade then states an explicit "no crate-root re-exports — items reachable only at module paths" note in §"IO observation" + a parallel note (per F4) at every other affected section.

This is a real source-side migration cost — every callsite of the four items (`IoEvent`, `IoEventTag`, `IoObserver`, `register_io_observer`, `trace_anchor`) updates from `cranelisp_intrinsics::IoEvent` to `cranelisp_intrinsics::io_observer::IoEvent`. Bounded by the number of callsites in `int` + tests; one mechanical sweep. The Principle-15-correct shape is the post-sweep state.

**FIXME to file.** `/design (intrinsics)` files `design/arch/fixmes/NNNN-source-moves-crate-root-reexport-demotion.md` targeting `/dev (intrinsics)` for the source-side demotion. The FIXME names the four items, the asymmetric `emit` precedent, and Principle 15's external-audience criterion as the grounding. Phase 4 wave-org schedules the source migration alongside any `int`-side callsite sweep.

**Prior audit disposition: facade-moves (§-add enumeration). FLIP to source-moves.** Grounding: Principle 15 external-audience exception not met; Principle 02 narrow interfaces; Baseline-diff discipline.

### Finding F4 — Crate-root flat re-exports of `alloc` / `panic` / `rc` / `io` / `ivar` items

**Facade expects.** §"Heap allocator", §"RC primitives", §"IO trampoline", §"IVar primitives", §"Panic helper" each describe their items at module paths. None mentions crate-root re-exports.

**Source does.** `crates/cranelisp-intrinsics/src/lib.rs:60–69`:

```rust
pub use alloc::{
    alloc_count, alloc_with_rc, bytes_allocated, bytes_current, bytes_peak,
    dealloc_count, heap_alloc, heap_alloc_payload, heap_dealloc, reset_counts,
};
#[cfg(debug_assertions)]
pub use alloc::is_live;
pub use panic::{runtime_panic, take_runtime_error};
pub use rc::{is_rc_trace_enabled, rc_underflow_check};
pub use io::{cranelisp_run_io, run_io_trampoline};
pub use ivar::{ivar_create, ivar_force, ivar_spark};
```

Twenty items re-exported flat at the crate root — `pub-api.txt:226–246`. Asymmetries: `rc::rc_trace`, `rc::consume_shallow`, `alloc::dealloc` are NOT re-exported. `is_live` is `#[cfg(debug_assertions)]` gated (so `cranelisp_intrinsics::is_live` exists only in debug builds — the release-build surface differs silently).

**Design intent.** Same as F3 — Principle 15 external-audience exception, Principle 02 narrow interfaces, Baseline-diff discipline. The grounding citations are identical. The source-side comment at `lib.rs:59` ("for ergonomic access by tests and consumers") frames the re-exports as convenience, but Principle 15 *names* the criterion for "convenience admissible" (external audience for whom this crate is the natural dep) and intrinsics doesn't meet it.

The `#[cfg(debug_assertions)]` gating on `is_live` is itself a Principle-13 violation (`interfaces.md` is auditable — the public surface should not vary silently between debug and release builds). The release-build pub-api differs from the debug-build pub-api by exactly one item; baseline-diff discipline catches this only if both modes' baselines are recorded, which they currently are not.

**Difference implies.** Same shape as F3. Twenty items reachable at the crate root, not facade-stated, baseline-records-everything-cargo-public-api-defaults-show. Asymmetries (which items are re-exported, which aren't) imply policy choices nobody stated.

**Disposition.** **Source moves.** Demote the entire `pub use {...}` block at `lib.rs:60–69`. The cfg-gated `is_live` re-export at `lib.rs:64–65` also demotes (so the public surface is consistent across debug/release). Consumers update to module-prefix paths. The FIXME filed under F3 covers this finding too — same `/dev (intrinsics)` source sweep handles both at once.

**Prior audit disposition: facade-moves (§-add enumeration). FLIP to source-moves.** Bundled with F3 + F9 under the same /dev fixme; the §-add the prior audit proposed legitimised a surface Principle 15 says shouldn't exist.

### Finding F5 — Auto-trait projections + standard derives on `HeapString` / `IoEvent` / `IoEventTag`

**Facade expects.** §"`#[non_exhaustive]` DTOs and `#[repr(C)]` layout types" line 349 names `IoEvent`, `IoEventTag`, and `HeapString` as layout-discipline-governed types. The auto-trait projection set (`Freeze`/`Send`/`Sync`/`Unpin`/`UnsafeUnpin`/`RefUnwindSafe`/`UnwindSafe`) and the standard derives (`Clone`/`Eq`/`PartialEq`/`Debug`/`Copy`/`StructuralPartialEq`) are not enumerated.

**Source does.** Pub-api lines 31–37 (`HeapString` auto-traits), 80–95 + 109–124 (`IoEvent` + `IoEventTag` auto-traits + derives), 181–225 (double-counts via crate-root re-export). ~30 pub-api lines of mechanical noise.

**Design intent.** Standing convention: facades do not enumerate auto-trait projections or standard derives. They follow mechanically from field types + `#[derive(...)]` annotations. The convention is encoded in `tests/facade_compliance.rs::extract_names()` Category D1 filter per SPRINT.md §"Architecture review". The convention itself is a Principle-13 expression — `interfaces.md` is auditable but the audit ignores mechanical projection noise to keep signal-to-noise reasonable.

**Difference implies.** Not behaviour-bearing per the standing convention. The crate-root double-counting *will* disappear when F3/F4/F9 source-moves (the re-exports demote and the re-projected impls disappear from `cranelisp_intrinsics::*` paths) — so part of this finding evaporates as a side effect of F15 cascade.

**Disposition.** **No action (auto-trait noise).** Covered by /qa's Category D1 filter per SPRINT.md §"Architecture review". Prior audit disposition: no action. **Confirmed.**

---

## 3. Shape drift — items in both; facade describes differently

### Finding F6 — `consume_shallow` module placement (rc, not drop)

**Facade expects.** §"Drop glue" line 100:

```rust
pub fn consume_shallow(ptr: i64);                                                  // single-node dec for IO trampoline + general use (NOT recursive — re-owns field pointers; see Decision 29)
```

Listed among per-type drop helpers under §"Drop glue" — implied module path `drop::*`.

**Source does.** `crates/cranelisp-intrinsics/src/rc.rs:78`:

```rust
pub fn consume_shallow(ptr: i64) { … }
```

Pub-api line 137: `pub fn cranelisp_intrinsics::rc::consume_shallow(ptr: i64)`. Source-side documentation at `rc.rs:14–17,66–67` distinguishes the single-node dec (rc machinery) from the per-type recursive walks (drop glue).

**Design intent.** **Legacy Decision 0029** (`design/arch/legacy/decisions/0029-io-trampoline-shallow-dec-runtime-primitive.md`) is the direct grounding. Decision 29 names the canonical location explicitly:

> "Canonical location: `crates/cranelisp-runtime/src/rc.rs` (or `drop.rs` alongside `consume_closure`)."

(Decision 29 was filed pre-D43 split; `cranelisp-runtime` became `cranelisp-intrinsics` per Decision 43. The Decision 29 text reads `cranelisp-runtime/src/rc.rs` which transfers to `cranelisp-intrinsics/src/rc.rs` post-split.) The Decision permits two options — `rc.rs` or `drop.rs`. **Principle 07 (single source of truth)** then disambiguates between them: the source comment at `rc.rs:66–67` explains that `consume_shallow` is "NOT safe for Vec (separate data buffer to free), closures (embedded drop glue), or ADTs with heap fields (need drop glue to recursively dec fields)." This is the categorical distinction — single-node dec is rc machinery; per-type recursive walks are drop glue. Placing `consume_shallow` in `rc.rs` puts it with the categorical kin; placing it in `drop.rs` would put it alongside the recursive walks that build *on top of* it. Source's choice (`rc.rs`) embodies the categorical line; the facade's grouping under §"Drop glue" elides it.

**Difference implies.** Categorical drift. A reader who expects `consume_shallow` to recurse (because §"Drop glue" groups it with `consume_sexp`/`consume_io_tree`) misreads the RC discipline. The drift is documentation-only but tracks a load-bearing distinction.

**Disposition.** **Facade moves.** Move the `consume_shallow` bullet from §"Drop glue" (line 100) to §"RC primitives" (after `rc_trace`, around line 80). Add inline rationale citing legacy Decision 29 + Principle 7 (one primitive per concept; single-node dec is rc machinery, per-type recursive walks are drop glue that build on top of it).

Prior audit disposition: facade-moves. **Confirmed; grounding citation strengthened (legacy Decision 29 + Principle 7).**

### Finding F7 — `runtime_panic` double-declaration

**Facade expects.** §"Panic helper" lines 258–263 declare `runtime_panic` with `#[no_mangle]`; then lines 265–269 declare it again with `#[export_name = "runtime/panic"]` as an editorial corrective ("Also update the runtime_panic signature to reflect the `#[export_name]` linker form used in pub-api"). Two declarations of the same fn in the same section.

**Source does.** `crates/cranelisp-intrinsics/src/panic.rs:25–27` carries both `#[unsafe(export_name = "runtime/panic")]` AND `#[no_mangle]`. Pub-api line 134 normalises to the `#[export_name]` form (the linker symbol comes from `#[export_name]`; `cargo-public-api` shows only the `#[export_name]` attribute).

**Design intent.** The kebab-case `runtime/*` `#[export_name]` form is the canonical linker symbol convention applied across allocator (`runtime/alloc`, `runtime/dealloc`), RC (`runtime/rc_underflow_check`), allocator-string (`runtime/alloc_string`, `runtime/string_read`), Vec runtime (`runtime/vec_new`, `runtime/vec_drop`), and panic (`runtime/panic`). The doubled declaration in the facade is an artefact of an earlier edit pass that added the corrective without removing the original; both forms semantically describe the same source declaration.

**Difference implies.** Editorial noise. A reader sees the same fn declared twice; reasonable inference is the second is the corrective, but the facade should not require inference here.

**Disposition.** **Facade moves.** Collapse to a single declaration. Delete lines 258–263 (`#[no_mangle]`-only form); keep lines 265–269 (`#[export_name = "runtime/panic"]` form). Add a one-line note: "The source declaration carries both `#[unsafe(export_name = "runtime/panic")]` and `#[no_mangle]`; `#[export_name]` takes precedence and is what `cargo-public-api` + the linker see." Prior audit disposition: facade-moves. **Confirmed.**

### Finding F8 — `vec_runtime` rename + `vec_len` removal

**Facade expects.** §"Vec primitives (Cow-checked per `data-structures.md`)" lines 108–119 enumerate six fns at implicit module path `cranelisp_intrinsics::vec::*` including `vec_len` with kebab-case `vec-len` `#[export_name]`.

**Source does.** `crates/cranelisp-intrinsics/src/lib.rs:55` declares `pub mod vec_runtime;` (not `pub mod vec;`). Pub-api lines 141–146 confirm `cranelisp_intrinsics::vec_runtime::*`. **Five fns, not six** — `vec_len` is absent (relocated to `cranelisp-primitives::vec::vec_len` at S67 W3 per FIXME 0180 close, alongside the `str_*` family).

**Design intent.** **Decision 0043** (primitives vs intrinsics split) + **FIXME 0180** (now closed) + **FIXME 0190** (`design/arch/fixmes/0190-design-intrinsics-facade-renamed-module-coverage.md`, open, target `/design (intrinsics)`) are the named grounding. FIXME 0190's proposed resolution explicitly tracks the rename from `cranelisp_intrinsics::vec` → `cranelisp_intrinsics::vec_runtime` driven by the `tests/facade_pif_rows::row_27_*` contract (avoid baseline collision with `cranelisp_primitives::vec`). The §"Sprint 67 disposition snapshot" line 388 of the facade names `vec_runtime` correctly — the §"Vec primitives" section is the stale form.

**Difference implies.** Two coupled drifts: module rename + `vec_len` removal, both already embodied in source and both contradicted within the facade (the snapshot at line 388 names them correctly; §"Vec primitives" uses the pre-rename pre-removal shape).

**Disposition.** **Facade moves.** Per FIXME 0190's proposed resolution:

1. Rename §"Vec primitives" header to "Vec runtime (backend-emitted-call)".
2. Update implicit module path to `cranelisp_intrinsics::vec_runtime::*`.
3. Drop the `vec_len` row.
4. Keep the remaining five rows (vec_new, vec_set_copy, vec_push_copy, vec_push_grow, vec_drop).
5. Add a one-line pointer to `facades/primitives.md` §"Primitives inventory" for `vec-len`'s canonical home.
6. Delete `design/arch/fixmes/0190-design-intrinsics-facade-renamed-module-coverage.md` with the commit.

Prior audit disposition: facade-moves. **Confirmed; grounding citation strengthened (Decision 43, FIXME 0180 close, FIXME 0190 named explicitly).**

### Finding F9 — Crate-root re-export of `cranelisp_run_io`

**Facade expects.** §"IO trampoline (Decision 29)" lines 182–184 lists `cranelisp_run_io` + `run_io_trampoline` at the implicit module path `cranelisp_intrinsics::io::*`.

**Source does.** Pub-api line 43 confirms `cranelisp_intrinsics::io::cranelisp_run_io`. Pub-api line 231 ALSO shows `cranelisp_intrinsics::cranelisp_run_io` (crate-root re-export per `lib.rs:68`). Same for `run_io_trampoline` (lines 44 + 244).

**Design intent.** Same as F3 + F4 — Principle 15 external-audience exception (not met for intrinsics), Principle 02 narrow interfaces, Baseline-diff discipline. The kebab-case extern linker symbol (`cranelisp_run_io` is `#[no_mangle]`, so the linker name is exactly `cranelisp_run_io`) is what backend's emitted-call code names; the *Rust* path `cranelisp_intrinsics::io::cranelisp_run_io` is what `int`'s session-init code writes when registering the fn pointer with `JITBuilder::symbol`. The crate-root re-export `cranelisp_intrinsics::cranelisp_run_io` adds nothing the Rust consumer needs that isn't reachable at the module path.

**Difference implies.** Specific instance of F4. Same source-moves disposition.

**Disposition.** **Source moves.** Demote the `pub use io::{cranelisp_run_io, run_io_trampoline};` line at `lib.rs:68`. Bundled with F3 + F4 under the same /dev fixme. Prior audit disposition: facade-moves (bundled with F4). **FLIP to source-moves.**

---

## 4. Coverage / structural mechanism — re-grounded against Principle 18

### Finding F10 — Flat re-export set drift (post-source-moves: trivial)

**Facade expects.** Implicitly — if F3/F4/F9 source-moves lands, the crate-root re-export set shrinks to zero (or to a small, facade-stated allow-list). The Baseline-diff discipline catches re-introduction via `cargo-public-api` baseline regeneration at commit time.

**Source does.** Today: 25 items at the crate root per `lib.rs:57–69`. Post-F3/F4/F9: zero (or whatever allow-list survives a residual narrow-exception review).

**Design intent.** **Principle 18** (enforce architectural invariants structurally where possible). The dep-ban worked example in Principle 18 §"Worked example" is directly applicable here: a future `pub use rc::rc_trace` at `lib.rs:67` would silently widen the surface. The structural enforcement is the **`cargo-public-api` baseline diff at commit time** — the baseline records every reachable item; a new re-export shows in the diff; reviewer (`/review`, the user) sees it and decides whether the re-export is intentional or accidental.

The structural mechanism IS the test — per Principle 18 + Principle 13. /qa-side mechanical test (substring-grep on facade content vs pub-api leaf names per `tests/facade_compliance.rs`) is a *behavioral* test that catches drift on a substring basis; the baseline diff is *structural* (the artefact's surface is the audit-of-record). When both exist, the structural form is the right answer (Principle 18 §"When to reach for the structural mechanism").

**Difference implies.** No coverage gap by Principle 18 framing. The baseline IS the standing check; any re-export addition produces a baseline diff that surfaces at PR review.

What *is* missing (and worth filing if /qa scope absorbs it): a facade-side **enumeration** of "intentional crate-root re-exports = ∅" (post-F3/F4/F9) so the baseline-diff reviewer can compare the diff against an explicit allow-list rather than a tacit one. That is one or two lines of facade text, not new test code.

**Disposition.** **Facade-text tightening.** Post-F3/F4/F9 source-moves: add a one-line note at the top of §"Public surface (as-designed)" stating "Intrinsics carries no crate-root `pub use` re-exports — every public item is reachable at its module path only. The Principle-15 external-audience exception does not apply: intrinsics is consumed only by other workspace crates that depend on it directly." The baseline already enforces this structurally.

Prior audit disposition: requires /qa work for S70 (new mechanical-test row). **Demoted to facade-text tightening + structural mechanism already in place.** Grounding: Principle 18 (the baseline diff is the structural check; per-Principle-18 a behavioral PIF row duplicating the baseline catch is the wrong tool).

### Finding F11 — Module-placement drift

**Facade expects.** Implicitly — once Wave 2 lands F6 (moving `consume_shallow` to §"RC primitives"), module placement becomes part of the documented contract.

**Source does.** Module placement lives in source structure (`rc.rs` vs `drop.rs`). Pub-api lines name the module path of every item (`cranelisp_intrinsics::rc::consume_shallow`, etc.) — the baseline records module placement structurally.

**Design intent.** **Principle 18** again. Module placement is recorded by `cargo-public-api` in every pub-api line (`pub fn cranelisp_intrinsics::rc::consume_shallow(...)` — the module path `rc` is *in the baseline*). A re-org (`consume_shallow` moves from `rc::` to `drop::`) produces a baseline diff: the line `pub fn cranelisp_intrinsics::rc::consume_shallow` disappears; the line `pub fn cranelisp_intrinsics::drop::consume_shallow` appears. Reviewer sees the diff.

The substring-grep `tests/facade_compliance.rs` is the *behavioral* test that misses module placement (it grep-matches names only); the *structural* mechanism (baseline diff) is in place and catches every re-org. Per Principle 18, the structural form is sufficient.

**Difference implies.** No coverage gap by Principle 18 framing. Module placement is structurally enforced via the baseline diff.

**Disposition.** **No action — structural mechanism present (Principle 18).** The baseline diff is the standing check; the per-PR reviewer reads it.

Prior audit disposition: requires /qa work for S70. **FLIP to no action (structural mechanism present).** Grounding: Principle 18 (baseline diff is the structural form; per-PR review reads it).

### Finding F12 — `#[non_exhaustive]` presence on `IoEvent` / `IoEventTag` (Principle 14)

**Facade expects.** §"`#[non_exhaustive]` DTOs and `#[repr(C)]` layout types" line 349 names `IoEvent` and `IoEventTag` as `#[non_exhaustive]`. Principle 14 grounds the rule: non-`#[repr(C)]` enums that are facade-public DTOs get `#[non_exhaustive]` (Facade convention item 3); `#[repr(C)]` types do NOT carry `#[non_exhaustive]` (Principle 14 statement).

**Source does.** Pub-api confirms `#[non_exhaustive]` IS present:
- Line 46: `#[non_exhaustive] pub enum cranelisp_intrinsics::io_observer::IoEvent`
- Line 96: `#[non_exhaustive] #[repr(u8)] pub enum cranelisp_intrinsics::io_observer::IoEventTag`
- Lines 147, 197 (crate-root re-exports; vanish post-F3 source-moves).

**Design intent.** **Principle 14** (FFI boundary types are governed by layout discipline) statement + consequence:

> "`#[repr(C)]` and `#[repr(transparent)]` DTOs do NOT carry `#[non_exhaustive]`. … `ABI_VERSION` is checked by the loader … Mismatch produces a clean refusal, not silent corruption. … Per-facade `#[non_exhaustive] DTOs` sections enumerate exempt types with a one-line 'governed by `ABI_VERSION`' note so the exemption is auditable from the facade spec, not just inferred from the absence of an annotation."

`IoEvent` is NOT `#[repr(C)]` (only `IoEventTag` carries `#[repr(u8)]`); both are facade-public DTOs whose variants will evolve as new IO event kinds land (Decision 40 §"Intrinsics surface" enumerates ~12 variants today; the Decision body explicitly anticipates more). The `#[non_exhaustive]` presence on both is the correct Principle-14 shape: source-non-breaking variant addition is what `#[non_exhaustive]` enables for the Rust consumers.

**Difference implies.** **No defect today.** Both types carry the correct attributes. The "coverage gap" framing of the prior audit (a future regression that drops `#[non_exhaustive]` would not be caught by substring-grep) is true but Principle 18 says the substring-grep is the wrong tool — `cargo-public-api`'s baseline records `#[non_exhaustive]` as part of the line (pub-api line 46 starts with `#[non_exhaustive]`); a removal produces a baseline diff. The structural mechanism is in place.

**Disposition.** **Facade-text tightening (Principle-grounded).** The facade §"`#[non_exhaustive]` DTOs and `#[repr(C)]` layout types" should explicitly cite Principle 14 inline at the enumeration (one phrase per type: "evolves via variant addition; `#[non_exhaustive]` per Principle 14"). This makes the facade-side intent visible so a future baseline-diff reviewer sees not just "the attribute disappeared" but "the attribute disappeared *against a stated Principle-14 contract*." Cost: ~3 lines of facade text. No /qa work; the structural mechanism (baseline diff) is in place.

Prior audit disposition: requires /qa work for S70 (new PIF row type asserting attribute presence). **FLIP to facade-text tightening + structural mechanism present.** Grounding: Principle 14 (the attribute rule) + Principle 18 (the baseline is the structural form; a new PIF row duplicates the baseline's catch).

### Finding F13 — `#[repr(C)]` presence + `#[non_exhaustive]` absence on `HeapString` (Principle 14)

**Facade expects.** §"`#[non_exhaustive]` DTOs and `#[repr(C)]` layout types" line 351 specifies `HeapString` MUST be `#[repr(C)]` AND MUST NOT be `#[non_exhaustive]`. Principle 14 grounds this directly.

**Source does.** Pub-api line 24: `#[repr(C)] pub struct cranelisp_intrinsics::heap_string::HeapString`. Correctly `#[repr(C)]`; correctly no `#[non_exhaustive]`.

**Design intent.** Principle 14 statement (verbatim):

> "Public DTOs that cross the C ABI — those carrying `#[repr(C)]` or `#[repr(transparent)]` — are layout-stable contracts, not source-stable contracts. The `#[non_exhaustive]` rule (Facade convention item 3) does NOT apply to them; their evolution is governed by an explicit version field — typically an `ABI_VERSION` const bumped on any layout-affecting change."

`HeapString` is read by JIT-emitted code at hardcoded offsets (`LEN_OFFSET`, `DATA_OFFSET`) and by `cranelisp-platform`'s `CLString::as_str()` via `read_string_as_str`. Adding `#[non_exhaustive]` would be source-non-breaking but binary-breaking; that's the failure mode Principle 14 prevents.

**Difference implies.** No defect today. Source carries the correct attributes. Same Principle-18 framing as F12: a future regression (removing `#[repr(C)]` or adding `#[non_exhaustive]`) produces a baseline diff; the structural mechanism is in place.

**Disposition.** **Facade-text tightening (Principle-grounded).** Same shape as F12 — cite Principle 14 inline at the §"`#[repr(C)]` layout types" enumeration: "`HeapString` — `#[repr(C)]`, NOT `#[non_exhaustive]`; layout governed by explicit version bump per Principle 14; layout consumed by JIT-emitted code at `LEN_OFFSET`/`DATA_OFFSET` and by `cranelisp-platform`'s `CLString::as_str()`." Cost: one expanded line of facade text. No /qa work.

Prior audit disposition: requires /qa work for S70. **FLIP to facade-text tightening + structural mechanism present.** Grounding: Principle 14 + Principle 18.

---

## 5. Informational — `JITBuilder::symbol` narrowing narrative

### Finding F14 — `JITBuilder::symbol` narrative (Decision 0048 boundary-of-asymmetry)

**Facade expects.** §"`JITBuilder::symbol(name, ptr)` narrows to intrinsics-only — post-S68" (lines 19–31), §"Asymmetry justification" (lines 25–27), §"Public-API impact" (lines 29–31), and §"Forbidden patterns" item 1 (lines 295–297) together state Decision 0048's narrowing: `JITBuilder::symbol` direct-registration is reserved for intrinsics; primitives flow through GOT-indirect dispatch.

**Source does.** The narrowing is consumer-side (`int`'s session init) — the intrinsics crate's published Rust API is unchanged by S68. Pub-api confirms no S68 additions on this crate's surface.

**Design intent.** **Decision 0048** §"Public-API impact" line 31: "no pub-api items are added, changed, or removed by S68 on this crate." **Decision 0048 §"Cascade"** lists `facades/intrinsics.md` cascade as: "confirm `JITBuilder::symbol(name, ptr)` is intrinsics-only post-S68. No public-API change expected; doc-comment refresh only." The facade text correctly embodies the cascade — narrative refresh, no item changes.

**Difference implies.** None. The facade text correctly describes a consumer-side commitment with no pub-api impact.

**Disposition.** **No action.** Prior audit disposition: no action. **Confirmed.**

---

## 6. /arch arbitration questions

### Finding F15 — Crate-root re-export policy (RESOLVED via Principle 15 — no arbitration needed)

**Facade expects.** §"IO observation", §"Heap allocator", §"IO trampoline", §"IVar primitives", §"Panic helper" describe items at module paths. No facade text says crate-root re-exports are part of the binding contract.

**Source does.** `lib.rs:57–69` re-exports 25 items at the crate root.

**Design intent.** **Principle 15** is the direct grounding (verbatim from `principles/15-facade-types-live-with-behavior.md` line 21):

> "**External-audience exception (narrow).** A facade whose external audience does not (and should not need to) depend on `cranelisp-types` MAY re-export the items its public API uses. The criterion is concrete: an external consumer for whom `cranelisp-types` is not otherwise a natural dependency. Today this applies to `cranelisp-platform` (DLL authors writing out-of-tree crates that depend only on `cranelisp-platform`). Each invocation of the exception is justified inline in the facade spec; it is not a general license."

The Principle names the criterion (external consumer for whom this crate is not a natural dep) and the canonical example (`cranelisp-platform`'s DLL authors). **Intrinsics has no external audience matching this criterion** (re-grounded in F3 above). Therefore the Principle 15 exception does not apply; the default rule ("no re-exports of items from implementation-crate `lib.rs` files") holds.

**Decision 0048's §"Structural invariant — backend dep-ban"** and **Principle 18** (enforce invariants structurally where possible) reinforce: the narrow surface IS the structural enforcement. Adding re-exports widens the surface; widening the surface invites consumer code that depends on the wider surface; the wider dependency is hard to undo. Demoting the re-exports today (when the only consumers are workspace-internal) is cheap; demoting them later (after out-of-tree consumers form) is expensive.

**Difference implies.** This was never /arch arbitration territory — Principle 15 already names the rule. The prior audit's framing of binary choice + evidence either way + "what tips it" + /design recommendation (a) was correct *as a heuristic* but unnecessary — the configuration (Principle 15) decides.

**Disposition.** **Resolved via Principle 15. Source moves (cascade: F3, F4, F9).** No /arch arbitration filed. /design recommendation (a) of the prior audit ("re-exports ARE binding contract; add §-add") was the wrong direction even though it was correctly identified as the "consistent" direction — the *binding* direction is the Principle-15-default, which says re-exports do not exist outside the external-audience exception. The §-add the prior audit proposed would have legitimised a Principle-15-non-conformant shape.

The /dev (intrinsics) FIXME (F3 disposition) is the closure mechanism. No additional arch-arbitration FIXME needed.

Prior audit disposition: requires /arch arbitration. **FLIP to resolved-via-Principle-15.** Grounding: Principle 15 external-audience exception + Principle 02 narrow interfaces + Principle 18 (structural enforcement = narrow surface; widening it later is expensive).

### Finding F16 — (reserved, empty in prior audit)

(Prior audit numbered findings 1–15 with F16/F17 as placeholders for the prior "12-substantive-finding" alignment with an earlier audit shape. This re-author retains the numbering for continuity with the prior commit's diff; F16/F17 carry no new substantive finding.)

### Finding F17 — (reserved, empty in prior audit)

(Same as F16.)

---

## 7. Findings overview — re-authored disposition table

| ID | One-line subject | Disposition (re-authored) | Disposition (prior audit) | Grounding citation |
|---|---|---|---|---|
| F1 | §"String primitives" stale (15 fns + vec_len relocated) | Facade moves | Facade moves | D43 + D0048 §"Cascade" + FIXME 0213 |
| F2 | `cranelisp_alloc` historical alias mention | No action | No action | Narrative correctness |
| F3 | Crate-root re-exports of `io_observer` items | **Source moves** | Facade moves | **Principle 15 external-audience exception not met** |
| F4 | Crate-root re-exports of `alloc`/`panic`/`rc`/`io`/`ivar` | **Source moves** | Facade moves | **Same; cascades from F3** |
| F5 | Auto-trait + standard derive impls noise | No action | No action | Standing convention (Category D1) |
| F6 | `consume_shallow` module placement (rc vs drop) | Facade moves | Facade moves | Legacy Decision 29 + Principle 7 |
| F7 | `runtime_panic` double-declaration | Facade moves | Facade moves | Editorial |
| F8 | `vec_runtime` rename + `vec_len` removal | Facade moves | Facade moves | D43 + FIXME 0180 close + FIXME 0190 |
| F9 | Crate-root re-export of `cranelisp_run_io` | **Source moves** | Facade moves | **Same; cascades from F3** |
| F10 | Flat re-export set drift (post-source-moves trivial) | **Facade-text tightening** | /qa S70 | **Principle 18 (baseline is structural check)** |
| F11 | Module-placement drift | **No action — structural mechanism present** | /qa S70 | **Principle 18 (baseline records module path)** |
| F12 | `#[non_exhaustive]` on IoEvent/IoEventTag | **Facade-text tightening (Principle 14 cite)** | /qa S70 | **Principle 14 + Principle 18** |
| F13 | `#[repr(C)]` + no `#[non_exhaustive]` on HeapString | **Facade-text tightening (Principle 14 cite)** | /qa S70 | **Principle 14 + Principle 18** |
| F14 | `JITBuilder::symbol` narrative (D0048) | No action | No action | D0048 (correctly embodied) |
| F15 | Crate-root re-export policy as binding contract | **Resolved via Principle 15 (source moves cascade)** | /arch arbitration | **Principle 15 + Principle 02 + Principle 18** |
| F16 | (reserved) | — | — | — |
| F17 | (reserved) | — | — | — |

**Disposition class totals (re-authored):**
- Facade moves: 5 (F1, F6, F7, F8 + F10 facade-text tightening counted in this bucket if §-add is the action shape) — though pure facade-moves without source change is 4 (F1, F6, F7, F8).
- Source moves: 3 (F3, F4, F9 — all bundled under one /dev fixme).
- Facade-text tightening (Principle-grounded; not /qa, not source-changing): 3 (F10, F12, F13).
- No action: 4 (F2, F5, F11, F14).
- /qa work for S70: 0 (was 4; re-grounded as structural-mechanism-present per Principle 18).
- /arch arbitration: 0 (was 1; re-grounded as Principle 15 already deciding).

---

## 8. Calibration of prior dispositions — before/after per finding

This section makes the audit-discipline pivot explicit. Per the user's 2026-05-18 direction: "A 'facade moves' recommendation against a target-stating facade actively undoes the architectural progression." The prior audit had no flips against target-stating facades (F1, F6, F7, F8 were correctly dispositioned facade-moves because the facade IS stale per FIXME 0213 / FIXME 0190 / legacy Decision 29 / editorial). The flips this re-author makes go in the *other* direction: items the prior audit framed as "facade silent → facade moves to document the source surface" re-classify as "facade silent BECAUSE Principle 15 says the source surface should not exist → source moves."

| Finding | Prior | Re-authored | Why the flip |
|---|---|---|---|
| F3 | Facade moves (§-add enumerating io_observer re-exports) | **Source moves** (demote re-exports) | Principle 15 external-audience exception is the test for whether crate-root re-exports are admissible. Intrinsics fails the test (no external consumer for whom intrinsics is not a natural dep). The prior §-add would have legitimised a Principle-15-non-conformant surface. |
| F4 | Facade moves (§-add enumerating alloc/panic/rc/io/ivar re-exports) | **Source moves** (demote re-exports) | Same as F3. Same Principle citation. Same cascade. |
| F9 | Facade moves (bundled with F4 §-add) | **Source moves** (demote `cranelisp_run_io` + `run_io_trampoline` re-exports) | Same. |
| F10 | /qa work S70 (new mechanical-test row for re-export set) | **Facade-text tightening + structural mechanism present** | Principle 18 names the test: when both structural and behavioral options exist, the structural is right. `cargo-public-api` baseline records every re-export; baseline diff at PR-time IS the structural check. A new PIF row duplicates the catch (Principle 18 §"When the behavioral form is the right answer" — invariants that admit structural enforcement should NOT also be enforced behaviorally; that is wasted test code). |
| F11 | /qa work S70 (module-placement assertion) | **No action — structural mechanism present** | Same as F10. Baseline pub-api lines name the module path (`cranelisp_intrinsics::rc::consume_shallow`); a re-org diffs the line. Principle 18 again. |
| F12 | /qa work S70 (PIF row asserting attribute presence) | **Facade-text tightening (Principle 14 cite inline)** | Principle 14 names the rule (`#[non_exhaustive]` rule applies for non-`#[repr(C)]` DTOs; explicit `ABI_VERSION`-style enumeration in §"`#[non_exhaustive]` DTOs" section). Baseline records `#[non_exhaustive]` as part of the type's line; structural check in place. Facade text should cite the Principle inline; no new test code needed. |
| F13 | /qa work S70 (PIF row asserting `#[repr(C)]` + no `#[non_exhaustive]`) | **Facade-text tightening (Principle 14 cite inline)** | Same shape as F12 — Principle 14 + Principle 18. |
| F15 | Requires /arch arbitration (binary choice with /design recommendation (a)) | **Resolved via Principle 15** | The arbitration framing assumed the policy was open. Principle 15's external-audience exception names the criterion and the canonical example (`cranelisp-platform`'s DLL authors). Intrinsics fails the criterion. /arch isn't needed; reading Principle 15 was. |

**No flips on F1, F2, F5, F6, F7, F8, F14.** Those dispositions were correct in substance; this re-author strengthens the grounding citation (naming Decision/Principle/FIXME explicitly) without changing the direction.

**Net effect on Wave 2 work shape.** The prior audit named "7 facade edits, ~100 lines of diff." The re-authored shape:
- **4 facade-moves** (F1, F6, F7, F8) — same as before; bounded; FIXMEs 0213 + 0190 close alongside.
- **1 facade-text tightening** (F10) — one line at top of §"Public surface (as-designed)".
- **2 facade-text tightening Principle-14 cites** (F12, F13) — one expanded line each at §"`#[non_exhaustive]` DTOs and `#[repr(C)]` layout types".
- **1 /dev (intrinsics) source-side FIXME** (F3 + F4 + F9 collectively) — demote `lib.rs:57–69` `pub use` block, plus consumer-side callsite sweep in int + tests + workspace.

Total facade-side: ~120 lines of diff. Total source-side: `lib.rs:57–69` deletion (~13 lines source diff) + N consumer-callsite updates (bounded; mechanical). The work-shape is comparable to the prior audit's estimate, but **architecturally cleaner**: the source surface contracts toward Principle 15's stated shape; the facade tightens toward Principle 14 + Principle 18 citations; no new test machinery; no /arch arbitration FIXME.

---

## 9. Arbitration briefs

### Arbitration A1 — (RETIRED)

The prior audit's Arbitration A1 ("Crate-root re-export policy as binding contract") is **retired**. Principle 15's external-audience exception decides the policy: intrinsics fails the criterion; re-exports demote; no /arch arbitration filed. See F15 disposition.

### Arbitration A2 — (RETIRED)

The prior audit's Arbitration A2 ("Mechanical-test coverage for layout-discipline attributes") is **retired**. Principle 18 decides: the structural mechanism (`cargo-public-api` baseline diff records attribute presence) is in place; behavioral PIF rows duplicating that catch are the wrong tool. See F12 / F13 dispositions.

### Arbitration A3 — (RETIRED)

The prior audit's Arbitration A3 ("Module-placement assertion as mechanical-test row") is **retired**. Same Principle-18 reading as A2. See F11 disposition.

### No new arbitration briefs filed.

This audit names zero items requiring /arch arbitration. Every disposition rests on Principle / Decision / FIXME grounding readable in the configuration. The prior audit's framing of three open arbitrations was a consequence of not reading Principles 14, 15, 18 (which the user direction surfaced as the missing configuration).

---

## 10. Wave 2 facade-doc work — concrete edits

Six discrete edits to `design/arch/facades/intrinsics.md`, all bounded:

1. **F1 — §"String primitives" rewrite.** Per FIXME 0213. Drop the 15-fn extern table; replace the section preamble with historical-note + pointer; rename header to "Heap-string allocator + reader (backend-emitted-call)"; keep the surviving `heap_alloc_string` / `string_read` / `alloc_string` / `read_string_as_str` / `HeapString` block. Delete `fixmes/0213-...md` with the commit.

2. **F8 — §"Vec primitives" rewrite.** Per FIXME 0190. Rename section header to "Vec runtime (backend-emitted-call)"; update implicit module path to `cranelisp_intrinsics::vec_runtime::*`; drop the `vec_len` row; keep the remaining five; add foot pointer to `facades/primitives.md` for `vec-len`'s canonical home. Delete `fixmes/0190-...md` with the commit.

3. **F6 — Move `consume_shallow` from §"Drop glue" to §"RC primitives".** Cite legacy Decision 29 + Principle 7 inline. ~3 lines of facade diff.

4. **F7 — Collapse `runtime_panic` double-declaration.** Delete facade lines 258–263 (`#[no_mangle]`-only form); keep lines 265–269 (`#[export_name = "runtime/panic"]` form); add one-line note that source carries both attributes (`#[export_name]` takes precedence). ~5 lines of facade diff.

5. **F10 — Add facade-text tightening at top of §"Public surface (as-designed)".** One line: "Intrinsics carries no crate-root `pub use` re-exports — every public item is reachable at its module path only. The Principle-15 external-audience exception does not apply: intrinsics is consumed only by other workspace crates that depend on it directly." (Lands *with* the source-side demotion per the F3 fixme.)

6. **F12 / F13 — Expand §"`#[non_exhaustive]` DTOs and `#[repr(C)]` layout types" with Principle 14 inline cites.** Per type, one expanded line naming Principle 14 + the consumer that motivates the rule (JIT-emitted code, `CLString::as_str`). ~3 lines of facade diff.

---

## 11. Wave 3 source-side work

**One source-side FIXME, bounded:**

- `/design (intrinsics)` files `design/arch/fixmes/NNNN-source-moves-crate-root-reexport-demotion.md` targeting `/dev (intrinsics)`. Body names:
  - The four `pub use` blocks at `lib.rs:57–69` to demote.
  - The asymmetric omissions (`emit`, `rc_trace`, `consume_shallow`, `dealloc`) to retain as "not re-exported" since they were already at module paths only.
  - The `#[cfg(debug_assertions)]` `is_live` re-export to demote (Principle-13 — public surface should not vary silently between debug/release).
  - The consumer-side callsite sweep (int, tests) to update.
  - Principle 15 external-audience criterion as the grounding.
- `/dev (intrinsics)` resolves by deleting `lib.rs:57–69`, sweeping callsites, regenerating `crates/cranelisp-intrinsics/public-api.txt` per Baseline-diff discipline, and committing both with the source diff.

No other Wave 3 source-side work is required. The intrinsics crate's substantive shape (`heap_string` / `vec_runtime` module names, `consume_shallow` in `rc.rs`, `runtime_panic` with `#[export_name]`, `IoEvent`/`IoEventTag` `#[non_exhaustive]`, `HeapString` `#[repr(C)]` + no `#[non_exhaustive]`) is correct.

---

## 12. /qa work — none required

The prior audit named four /qa items for S70 (F10, F11, F12, F13). Re-grounded against Principle 18, all four resolve via the structural mechanisms already in place (`cargo-public-api` baseline diff catches re-export changes, module re-orgs, attribute presence changes, attribute absence changes). No new PIF row machinery; no new mechanical-test rows; no /qa-side enhancement work surfaced by this audit.

---

## 13. /arch watch-item verification (carried from prior audit)

Re-verified per per-item analysis (no flip from prior audit's PASS verdict on these):

- **Item (a)**: §"Sprint 67 disposition snapshot" lines 381–391 correctly describes the post-S67/W4 state. The drift lives in §"String primitives" (F1) and §"Vec primitives" (F8); the snapshot itself is current. **PASS.**
- **Item (b)**: `IoEvent` / `IoEventTag` `#[non_exhaustive]` annotations present per Principle 14 — pub-api lines 46, 96 (+ 147, 197 crate-root duplicates) confirm. **PASS.**
- **Item (c)**: `HeapString` `#[repr(C)]` present, `#[non_exhaustive]` absent — pub-api line 24 confirms. **PASS.**
- **/arch additional**: zero `cranelisp_intrinsics::{string,vec}::*` items — `grep '^pub.*cranelisp_intrinsics::\(string\|vec\)::' public-api.txt` returns zero hits. Module paths are `heap_string` and `vec_runtime` respectively. Decision 0048 invariant + FIXME 0180 close embodied structurally. **PASS.**

All /arch watch items PASS. The remaining drift is facade-text-side (F1, F6, F7, F8, F10, F12, F13) + source-side over-export (F3 + F4 + F9 collectively); no source-side substantive regression exists.

---

## 14. Verdict

The intrinsics crate's source has settled correctly across S67 (FIXME 0180 close — physical relocation of user-callable string + Vec primitives to `cranelisp-primitives`) and S68 (Decision 0048 — JIT-builder narrowing, no pub-api impact). The Principle-14 layout-discipline invariants hold structurally; the Decision-43 categorical line is embodied; the post-D40 trace/io_trace relocation is complete; Principle 17 module locality is not relevant to this crate (intrinsics is not in typecheck's domain).

The drift is facade-side (largest body: F1 §"String primitives" stale ~45 lines, FIXME 0213 tracks the rewrite) plus the crate-root `pub use` over-export at `lib.rs:57–69` (F3 + F4 + F9). The over-export was framed by the prior audit as "facade silent → add §-add"; this re-author re-grounds against Principle 15's external-audience exception (intrinsics fails the criterion) and re-classifies the disposition as source moves (demote re-exports). Per Principle 18 (enforce invariants structurally where possible), the four /qa-side enhancements the prior audit named (F10, F11, F12, F13) collapse: `cargo-public-api` baseline diff IS the structural check for re-export drift, module-placement drift, and attribute presence/absence drift; behavioral PIF rows duplicating that catch are the wrong tool.

**Wave 2 — bounded.** Six facade edits (F1, F6, F7, F8 facade-moves; F10 + F12 + F13 facade-text tightening) per §10 above, ~120 lines of facade diff. FIXMEs 0213 + 0190 close alongside.

**Wave 3 — bounded, single source-side fixme.** Demote `lib.rs:57–69` per the F3/F4/F9 cascade; consumer-side callsite sweep in int + tests; regenerate `crates/cranelisp-intrinsics/public-api.txt` per Baseline-diff discipline.

**/qa work — none required.** Principle 18 reframe: the structural mechanisms (`cargo-public-api` baselines + Baseline-diff discipline at PR-time) are the standing check; new PIF row machinery would duplicate the catch.

**/arch arbitration — none required.** Principle 15 decides F15 (the prior audit's only arbitration item); Principles 14 + 18 decide F12 / F13 (the prior audit's deferral items); the prior audit's three open arbitrations all retire on configuration-reading.

**Flipped prior dispositions — 7 line-item flips** (counting F15 as a procedural flip from "arbitration" to "resolved"):
1. F3 — facade-moves → source-moves (Principle 15).
2. F4 — facade-moves → source-moves (Principle 15).
3. F9 — facade-moves → source-moves (Principle 15).
4. F10 — /qa S70 → facade-text tightening + structural mechanism present (Principle 18).
5. F11 — /qa S70 → no action / structural mechanism present (Principle 18).
6. F12 — /qa S70 → facade-text tightening (Principle 14 + 18).
7. F13 — /qa S70 → facade-text tightening (Principle 14 + 18).
8. F15 — /arch arbitration → resolved (Principle 15).

(Item 1–3 form a single conceptual flip — "crate-root re-export policy" — applied to three concrete instances; F15 is the procedural surface of the same underlying re-grounding. Counted as a group: **5 substantive flips** — re-export policy, F10, F11, F12, F13.)

The three most consequential flips:

1. **F3+F4+F9+F15 (crate-root re-export policy)** — re-grounded as Principle 15 source-moves rather than facade §-add. Direction-of-change matters: the prior audit's §-add would have widened the documented contract surface; the re-grounded source-moves shrinks the actual surface. Future maintenance cost diverges sharply between the two — widening makes the surface harder to retract later; narrowing now is cheap.
2. **F12+F13 (Principle 14 attribute presence)** — re-grounded as facade-text tightening + structural mechanism present rather than new PIF row machinery. /qa work for S70 dissolves; the baseline diff is the standing check.
3. **F11 (module placement)** — re-grounded as no-action / structural mechanism present rather than new mechanical-test row. /qa work dissolves; baseline diff records the module path.

Beyond these, the F1 / F6 / F7 / F8 facade-moves dispositions stand (correctly identified by the prior audit; this re-author strengthens the grounding citation without changing direction). FIXMEs 0213 + 0190 close alongside the corresponding facade edits; one new /dev (intrinsics) FIXME is filed for the source-side demotion.

The audit is complete at this re-authored shape: every finding has the five-block analysis with explicit Principle/Decision/FIXME grounding; no deferral without disposition; no arbitration filed when configuration-reading decides.
