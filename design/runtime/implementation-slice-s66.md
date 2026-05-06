# Sprint 66 implementation slice — `cranelisp-runtime` (retiring)

**Status.** draft
**Author.** /design (runtime), 2026-05-06
**Reads.** `design/arch/decisions/0043-runtime-split-into-primitives-intrinsics.md` (D43, the retirement spec); `design/arch/decisions/0040-runtime-trace-io-trace-relocate-to-int.md` (D40, the trace/io_trace relocation); `design/arch/legacy/substance-scoping.md` §1.1 + §1.7 (substance source — the table of what moves where); `design/arch/fixmes/0150-runtime-split-primitives-intrinsics.md` (D43 implementation tracker, target `/dev`); `design/arch/fixmes/0103-dev-runtime-int-trace-io-trace-relocation-and-io-observer.md` (companion FIXME for trace/io_trace); `design/runtime/runtime.md` (master design — historical record); `design/arch/sprint-65-reshape-phase-2-review.md` §3 (slice template authority); `sprints/SPRINT.md` Wave Phase 4 W4a; `crates/cranelisp-runtime/src/` (current source layout).

This is a **retirement slice**, not a forward-implementation slice. After S66 lands, `crates/cranelisp-runtime/` no longer exists in the workspace. The slice scopes the migration of every file in `crates/cranelisp-runtime/src/` into its new home — primitives, intrinsics, `src/` (int), or deleted outright — and the coordinated deletions in dependents.

The slice consumes the post-S65 final-state facades for `primitives.md`, `intrinsics.md`, `backend.md`, and `int.md`. It is consumed by `/sprint` as input to S66's wave plan; it is not itself a wave allocation.

---

## 1. Source-to-destination table

Every file in `crates/cranelisp-runtime/src/` is mapped to its new home. The mapping follows the D43 migration table (`design/arch/decisions/0043-*.md` §"Migration scope") and the D40 / FIXME 0103 split (trace + io_trace relocate to `src/`, not into intrinsics — this slice's headline intersection with FIXME 0103).

Action classes:
- **migrate-to-primitives** — file body moves to `crates/cranelisp-primitives/src/`
- **migrate-to-intrinsics** — file body moves to `crates/cranelisp-intrinsics/src/`
- **migrate-to-src** — file body moves to `src/` (int) per D40 / FIXME 0103
- **delete-content** — content (a subset of a file) deletes outright (no destination)
- **retire** — file dissolves entirely; no destination, no replacement (lib.rs goes here once everything else has moved)

| # | Source file (`crates/cranelisp-runtime/src/`) | LOC | Destination | Action | FIXME closed | Acceptance |
|---|---|---:|---|---|---|---|
| 1 | `alloc.rs` | 304 | `crates/cranelisp-intrinsics/src/alloc.rs` | migrate-to-intrinsics | 0150 (D43 Phase 2) | `cranelisp_alloc`, `heap_alloc`, `heap_alloc_payload`, `heap_dealloc`, `alloc_with_rc`, counters, `LIVE_ALLOCS` arrive in intrinsics; backend's emitted-symbol declarations point at `cranelisp-intrinsics`; LOC unchanged |
| 2 | `rc.rs` | 199 | `crates/cranelisp-intrinsics/src/rc.rs` | migrate-to-intrinsics | 0150 (D43 Phase 2) | `consume_shallow`, `rc_underflow_check`, `is_rc_trace_enabled`, `CRANELISP_RC_TRACE` arrive in intrinsics; backend's RC-emit codegen names extern fns under intrinsics |
| 3 | `drop.rs` | 864 | `crates/cranelisp-intrinsics/src/drop.rs` | migrate-to-intrinsics | 0150 (D43 Phase 2) | All `consume_*` per-shape recursive consumers + `dec_shallow_io` arrive in intrinsics. **Carve-out**: `consume_trace_call` (the trace-ADT walker, currently 60–80 LOC inside `drop.rs`) follows trace.rs to `src/` per D40 / FIXME 0103 — extract during the migration into a `consume_trace_call` callsite that lives in `src/trace/drop.rs` (or absorbed by trace.rs's new home as a private helper). Master design §3 documents this carve-out. |
| 4 | `string.rs` | 717 | `crates/cranelisp-intrinsics/src/string.rs` | migrate-to-intrinsics | 0150 (D43 Phase 2) | `HeapString`, `heap_alloc_string`, `string_read`, ~15 string primitives (`str_concat`, `str_eq`, `str_len`, `str_substring`, `str_split`, `str_join`, `str_replace`, `str_trim`, `str_starts_with`, `str_ends_with`, `str_contains`, `str_to_upper`, `str_to_lower`, etc.) arrive in intrinsics. **Note**: per `design/arch/interfaces.md` lock surfaced in S65 W2.5 (canonical-doc drain), `HeapString`'s home is intrinsics — confirms this row's destination |
| 5 | `vec.rs` | 666 | `crates/cranelisp-intrinsics/src/vec.rs` | migrate-to-intrinsics | 0150 (D43 Phase 2) | `vec_new`, `vec_len`, `vec_set_copy`, `vec_push_copy`, `vec_push_grow`, `vec_drop` (two-allocation Vec runtime + COW discipline) arrive in intrinsics |
| 6 | `io.rs` | 966 | `crates/cranelisp-intrinsics/src/io.rs` | migrate-to-intrinsics | 0150 (D43 Phase 2) | IO trampoline (`run_io_trampoline`, `cranelisp_run_io`, `dispatch_par_branches_with_trace`, `Pure | Effect | Bind | Par` reducer, `is_fresh` discipline) arrives in intrinsics. **Subordinate change** within this row: the ~17 `io_trace::record_event` call sites swap to invoke a registered `IoObserver` per D40 — but the observer registration site lives in intrinsics (per D43 + cross-reference in D40 `decisions/0040-*.md` line 11), not in runtime; no separate FIXME closure here, just call-site rewiring at migration time |
| 7 | `io_trace.rs` | 952 | `src/io_trace/` (new directory under int) | migrate-to-src | 0103 (Phase 2) | Per-thread `VecDeque<IoEvent>` ring buffers, `dump_all_buffers`, `dump_thread_buffer`, `flush_to_stderr`, `install_panic_hook`, `publish_thread_buffer`, `record_event`, `trace_instant_anchor`, `IoTraceEvent`, `IoTracePayload`, `IoTraceTag`, `TraceFilter`, `FlushGuard` arrive in `src/io_trace/`. Int's session startup registers the observer when REPL/trace mode is on or `CRANELISP_IO_TRACE=1`. The eight `cranelisp_runtime::io_trace_*` callers in `src/main.rs` and `src/observability.rs` rewire to local module paths |
| 8 | `ivar.rs` | 314 | `crates/cranelisp-intrinsics/src/ivar.rs` | migrate-to-intrinsics | 0150 (D43 Phase 2) | `ivar_create`, `ivar_spark`, `ivar_force` (write-once cells for spec §12.4.3 lenient evaluation; rayon `spawn` for sparked thunks) arrive in intrinsics |
| 9 | `marshal.rs` | 389 | `crates/cranelisp-intrinsics/src/marshal.rs` | migrate-to-intrinsics | 0150 (D43 Phase 2) | `quote_sexp`, `sconcat` arrive in intrinsics. **Open question (§6 below)**: marshaling primitives are user-callable in the same sense as `add-i64` (they appear in user-visible Sexp construction). D43's §"Migration scope" table places them in intrinsics implicitly (not enumerated in the language-level callable category). Slice's tentative read: intrinsics, per the table; flag for `/arch` confirmation |
| 10 | `trace.rs` | 740 | `src/trace/` (new directory under int) | migrate-to-src | 0103 (Phase 2) | `cranelisp_trace_swap_got`, `cranelisp_trace_restore_got`, `cranelisp_trace_enter`, `cranelisp_trace_exit`, `cranelisp_collect_trace`, `cranelisp_trace_first_child_nanos`, `cranelisp_trace_format`, `cranelisp_trace_name/params/result/children/nanos` arrive in `src/trace/`. The two `session_v4.rs` callers (`cranelisp_trace_format` symbol-name registrations at lines 1965, 2029) update to local paths |
| 11 | `panic.rs` | 95 | `crates/cranelisp-intrinsics/src/panic.rs` | migrate-to-intrinsics | 0150 (D43 Phase 2) | `runtime_panic` thread-local sentinel, `take_runtime_error`, `RUNTIME_ERROR` per-thread state arrive in intrinsics. Per D42 §"Scope clarification", `runtime_panic` stays flat-`String` (not enriched with `ErrorLocation`); migration preserves the flat-String shape |
| 12 | `primitives/int.rs` | 254 | **split**: `int_to_string` + `parse_int` to `crates/cranelisp-primitives/src/int.rs`; `cranelisp_op_*` (10 fns) **delete-content** | migrate-to-primitives + delete-content | 0150 (D43 Phase 2 + Phase 4) | `int_to_string` and `parse_int` arrive in primitives (language-level callable per the D43 categorisation — symbol-table entries at `primitives/int-to-string` etc.). The 10 `cranelisp_op_*` extern fns DELETE outright per D43 Phase 4 (they were Decision-14-implementation duplicates of the named primitives `add-i64`, `sub-i64`, etc.); `add-i64` etc. arrive in primitives via the same path |
| 13 | `primitives/float.rs` | 68 | `crates/cranelisp-primitives/src/float.rs` | migrate-to-primitives | 0150 (D43 Phase 2) | `float_to_string` arrives in primitives |
| 14 | `primitives/bool.rs` | 47 | `crates/cranelisp-primitives/src/bool.rs` | migrate-to-primitives | 0150 (D43 Phase 2) | `bool_to_string` arrives in primitives |
| 15 | `primitives/mod.rs` | 5 | retire | retire | 0150 (D43 Phase 5) | The mod declaration is a side effect of the runtime crate's module structure; primitives crate restructures around individual files (per the frontend slice's pattern) — no carryover |
| 16 | `lib.rs` | 110 | retire (no destination) | retire | 0150 (D43 Phase 5) | The crate-level `pub mod` declarations + ~80 lines of `pub use` re-exports retire entirely. **No `pub use` re-export ceremony left over** — the new crates declare their public surfaces independently per their facades. `cranelisp-runtime`'s lib.rs has no successor file |
| 17 | `Cargo.toml` (`crates/cranelisp-runtime/Cargo.toml`) | — | delete file | retire | 0150 (D43 Phase 5) | Crate manifest deletes alongside the workspace member entry |
| 18 | Workspace `Cargo.toml` `members = […, "crates/cranelisp-runtime", …]` | — | remove line | retire | 0150 (D43 Phase 5) | Workspace member entry deletes; corresponding `[dependencies] cranelisp-runtime = { path = … }` entry in root `Cargo.toml` (currently line ~26) deletes; `cranelisp-primitives` + `cranelisp-intrinsics` workspace member entries land alongside (these land in the **primitives slice** + **intrinsics slice** — coordinated commit) |
| 19 | `crates/cranelisp-runtime/CLAUDE.md` (per FIXME 0102) | — | not authored | n/a | 0102 (closes-by-vacuum) | FIXME 0102 (proposed `crates/cranelisp-runtime/CLAUDE.md`) closes when the crate retires. The CLAUDE.md never authored; instead `crates/cranelisp-primitives/CLAUDE.md` + `crates/cranelisp-intrinsics/CLAUDE.md` are authored by the primitives + intrinsics slices |

**Total source rows: 16 source files (rows 1–16) + 3 workspace/manifest rows (17, 18, 19) = 19 rows.**

By destination:
- **migrate-to-primitives**: 4 rows (12 partial, 13, 14, 15) — the language-level callable surface (Cat 1 per D43 §"Migration scope")
- **migrate-to-intrinsics**: 9 rows (1, 2, 3, 4, 5, 6, 8, 9, 11) — the backend-emitted-call targets + RC + drop + heap + IO trampoline + IVars + marshaling + panic (Cat 2 per D43 §"Migration scope")
- **migrate-to-src**: 2 rows (7, 10) — trace + io_trace per FIXME 0103 / D40
- **delete-content**: 1 row (12 partial, 10 `cranelisp_op_*` extern fns) — Decision-14-implementation duplicates that delete outright per D43 Phase 4
- **retire**: 4 rows (15, 16, 17, 18) — the runtime crate's module-declaration + lib re-export + manifest + workspace-member rows that retire when the crate is gone

---

## 2. Ordering within the slice

The retirement is sequenced as a **multi-phase coordinated migration**, not a single atomic move. Phases align with FIXME 0150's Phase plan (D43 Phase 1 → Phase 5) and intersect with FIXME 0103's two-phase plan. Because the slice's commits are spread across four sister slices (primitives, intrinsics, src/, backend), this slice's "ordering" is mostly a coordination contract that names what blocks what; the actual phase-by-phase commits land in the destination slices' work.

### 2.1 Phase 1 — Workspace skeleton lands (NOT in this slice; lives in primitives slice + intrinsics slice + arch)

Empty `crates/cranelisp-primitives/` + `crates/cranelisp-intrinsics/` skeletons land first. Workspace `Cargo.toml` adds the two new members. `cranelisp-runtime` retains all symbols at this point — no deletions yet — so the workspace builds cleanly through Phase 1. **Blocks**: rows 1–14 of this slice depend on Phase 1 having landed.

### 2.2 Phase 2 — Source migration (interleaved across primitives + intrinsics + src/ slices)

Rows 1, 2, 3, 4, 5, 6, 8, 9, 11 (intrinsics destinations) move in lockstep with Phase 2 of the **intrinsics slice**. Rows 12–14 (primitives destinations) move in lockstep with Phase 2 of the **primitives slice**. Rows 7, 10 (`src/` destinations) move per **FIXME 0103 Phase 2** as scheduled by `/sprint` — see §2.4 below for the choice point.

Within Phase 2:
- Files migrate one-at-a-time or in small clusters; intermediate states keep `cranelisp-runtime` building (e.g., during the migration of `string.rs` → intrinsics, `cranelisp-runtime/src/lib.rs` could `pub use cranelisp_intrinsics::*` as a trampoline until all callers update). FIXME 0150 Phase 1 explicitly calls out this trampoline pattern.
- The IO observer rewiring (row 6 subordinate) lands as part of `io.rs`'s migration, NOT as a separate change. Pre-D43, the observer registration site was specified to live in `cranelisp-runtime` (D40's original phrasing); D43 moves it with the trampoline into intrinsics. The intrinsics slice's row for `io_observer.rs` is the landing site.

### 2.3 Phase 3 — Backend cleanup (NOT in this slice; lives in backend slice)

Per FIXME 0150 Phase 3: backend deletes `operators.rs:323–394` (the `(TraitName, Symbol, TypeName) → PrimitiveOp` map), `compiler/literals.rs:327–332` (the `"+" → "cranelisp_op_add"` map), renames `operators.rs` → `primitives_inline.rs`, updates `jit.rs::IntrinsicSymbol` array (drops `cranelisp_op_*`, keeps `int-to-string`), and revises `Cargo.toml` to depend on `cranelisp-intrinsics` + `cranelisp-primitives` instead of `cranelisp-runtime`. **Coordinated with this slice's row 12 delete-content**: the `cranelisp_op_*` extern fns in `cranelisp-runtime/src/primitives/int.rs` cannot delete until backend's `IntrinsicSymbol` array stops registering them — see §4 cross-crate dependencies.

### 2.4 Phase 2 sequencing choice — FIXME 0103 vs FIXME 0150 (handed to /sprint)

FIXME 0150 §"Coordinate with FIXME 0103" surfaces two options:

- **Option (a) — sequential**: FIXME 0103 lands first (per current S66 W4 scope expectation); IoObserver lives in `cranelisp-runtime` until D43's wave; then migrates to `cranelisp-intrinsics` as part of D43 Phase 2. The trace + io_trace files land in `src/` first; the observer-registration-site relocation happens later.
- **Option (b) — bundled**: both FIXMEs land in the same wave; IoObserver lands directly in `cranelisp-intrinsics`; FIXME 0103 closes within FIXME 0150's wave.

This slice does NOT pre-allocate the choice. `/sprint` decides at the wave-plan boundary per FIXME 0150's directive. The slice's source-to-destination table is correct under both options — only the **order of commits** differs. Slice records: **option (b) is conceptually cleaner** (one IO observer move instead of two) and the slice tentatively prefers (b) but does not bind.

### 2.5 Phase 4 — Stdlib audit (NOT in this slice; lives in stdlib work, picked up by /dev narrow to stdlib)

FIXME 0150 Phase 4: audit `(impl Num Int)`, `(impl Display Int)`, `(impl Eq Int)`, `(impl Ord Int)`, `(impl Num Float)` for impls that relied on backend's collusion (i.e., the impl method was empty + intercepted by the trait-knowledge map). Each impl body must call the primitive directly: `(defn + [a b] (add-i64 a b))`. **Blocks**: Phase 3's deletion of the trait-knowledge maps cannot go red — the audit must catch impls that delegate back to the operator (`(defn + [a b] (+ a b))` — circular under the corrected model). This slice mentions but does not author.

### 2.6 Phase 5 — Crate retirement (rows 15, 16, 17, 18 — atomic close)

Once Phases 1–4 have landed and every source has moved, this slice's terminal commit:
1. Deletes `crates/cranelisp-runtime/` directory wholesale (rows 1–17 — the contents are by then either gone or trampolines that no caller hits).
2. Workspace `Cargo.toml` removes `"crates/cranelisp-runtime"` from `members` and removes `cranelisp-runtime = { path = "crates/cranelisp-runtime" }` from `[dependencies]`.
3. Backend's `Cargo.toml`, `crates/cranelisp-exe-bundle/Cargo.toml`, root `Cargo.toml` `[dependencies]` rows for `cranelisp-runtime` delete.
4. `bounded-contexts.md` §4 retirement (already drafted in S65 W1) becomes effective in code; §4a + §4b cite live crates.
5. `design/arch/facades/runtime.md` archive (already executed S65 W1; commit `d576c36`) is a no-op at this point — for record.
6. `design/runtime/runtime.md` (master design) retires alongside; `design/runtime/` directory remains for slice + retirement record. Slice tentatively suggests moving `runtime.md` to `archive/` with a single-line redirect to `design/intrinsics/intrinsics.md` + `design/primitives/primitives.md`; final disposition is `/arch`'s call.
7. `cargo public-api` baseline file at `crates/cranelisp-runtime/cargo-public-api.txt` (if present at S66 time) deletes.

**Atomic-close acceptance**: workspace builds clean with no `cranelisp-runtime` references in any `Cargo.toml`, no `cranelisp_runtime::` paths in any source, no `cranelisp-runtime` strings in `crates/cranelisp-backend/src/jit.rs::IntrinsicSymbol` registrations.

### 2.7 Dependencies between phases (concise)

```
Phase 1 (skeletons) — NO blocker
   │
   ├──► Phase 2a (primitives migration, rows 12–14)         ──┐
   │                                                          │
   ├──► Phase 2b (intrinsics migration, rows 1,2,3,4,5,6,8,9,11) ─┼──┐
   │                                                          │   │
   ├──► Phase 2c (src/ migration via FIXME 0103, rows 7,10)   ──┘   │
   │     [option (a) before Phase 2b, or (b) bundled]               │
   │                                                                │
   ▼                                                                │
Phase 3 (backend cleanup; deletes trait-maps + jit.rs registrations) ◄┤
   │                                                                │
   ▼                                                                │
Phase 4 (stdlib audit; impl bodies call primitives directly)      ◄─┘
   │
   ▼
Phase 5 (this slice's atomic close: rows 15, 16, 17, 18)
```

Phase 2a, 2b, 2c are independent (can interleave); Phase 3 follows 2b (because backend depends on intrinsics existing); Phase 4 follows 3 (because the audit must catch circular impls before backend's trait-knowledge map deletes); Phase 5 follows all.

---

## 3. Estimated effort

**Multi-wave; this slice's work is the migration coordination + Phase 5 atomic close.** Distributed effort:

- **Phase 1 (skeletons)**: ~2 hours of `/dev` work (Cargo.toml + empty `lib.rs` for the two new crates; workspace member entries). Lands in primitives + intrinsics slices, not here.
- **Phase 2a (primitives migration, rows 12–14)**: ~0.5 day. The four primitives files are small (369 LOC total). Mechanical port. Lands in primitives slice.
- **Phase 2b (intrinsics migration, rows 1,2,3,4,5,6,8,9,11)**: **~3–4 days** — the bulk. Of this:
  - `string.rs` (717), `vec.rs` (666), `drop.rs` (864), `io.rs` (966) are the four big files (~3200 LOC together).
  - `io.rs` migration includes the IO observer rewiring (row 6 subordinate change) — ~17 call sites + new `io_observer.rs` module.
  - `drop.rs` migration includes the `consume_trace_call` carve-out to `src/trace/`.
  - Test-port effort: every file ships `#[cfg(test)]` blocks; tests port with their files. ~estimate 60–80 unit tests across the migrated files.
  Lands in intrinsics slice.
- **Phase 2c (src/ migration, rows 7, 10)**: **~2 days** per FIXME 0103 (`io_trace.rs` 952 LOC + `trace.rs` 740 LOC). Lands in src/ work (int slice or as FIXME 0103's standalone wave).
- **Phase 3 (backend cleanup)**: ~0.5 day. Map deletions are bounded (~70 lines + ~6 lines + `IntrinsicSymbol` array trim). `Cargo.toml` dep update is mechanical. Lands in backend slice.
- **Phase 4 (stdlib audit)**: ~0.5–1 day. Audits ~5 trait-impl files; refactors where impls relied on backend collusion. Lands in stdlib work.
- **Phase 5 (this slice's atomic close)**: ~1 hour. Directory delete + workspace Cargo.toml lines + master-doc archival. Mechanical once Phases 1–4 are green.

**Sized as ~6–7 days total work distributed across primitives, intrinsics, src/, backend, and stdlib slices, with ~1 hour of standalone effort attributed to this retiring slice (the Phase 5 atomic close).**

If `/sprint` schedules the migration as a single mega-wave, the wave envelope is ~one full S66 wave. If `/sprint` schedules in sub-waves (e.g., Phase 2a + 2b + 2c as parallel sub-waves, then Phase 3 + 4 sequentially, then Phase 5), the migration absorbs ~2 wave-equivalents of S66 capacity.

This slice's natural fissure: **Phase 5 cannot be deferred past S66** without leaving the workspace half-migrated. Phases 2a/2b/2c can split across S66 + S67 if the wave envelope is tight (intermediate state is `cranelisp-runtime` as a trampoline crate `pub use`-ing from `cranelisp-primitives` + `cranelisp-intrinsics`), but `/sprint` should treat this as a "land all together" preference.

---

## 4. Dependencies on other crates' slices

The migration is bilaterally coupled across five other slices: primitives, intrinsics, src/ (int), backend, and the qa S66 test plan slice. Each row below pairs an item in this slice with the corresponding entry in the other slice.

| This slice's item | Depends on | In the other crate's slice |
|---|---|---|
| Rows 1, 2, 3, 4, 5, 6, 8, 9, 11 (migrate-to-intrinsics) | The intrinsics crate skeleton + facade exists; intrinsics slice receives these files | **intrinsics slice** (Phase 1 + Phase 2): land `crates/cranelisp-intrinsics/{Cargo.toml,src/lib.rs}`; receive each migrated file with its tests; expose backend-emitted-call extern surface per `facades/intrinsics.md` |
| Rows 12, 13, 14 (migrate-to-primitives) | The primitives crate skeleton + facade exists; primitives slice receives these files; primitives crate adopts symbol-table-entry registration at `primitives/<name>` | **primitives slice** (Phase 1 + Phase 2): land `crates/cranelisp-primitives/{Cargo.toml,src/lib.rs}`; receive `int_to_string`, `parse_int`, `float_to_string`, `bool_to_string`, plus the surviving `add-i64`/`sub-i64`/etc. user-callable arithmetic primitives per `facades/primitives.md` |
| Rows 7, 10 (migrate-to-src) | `src/` (int) gains `src/io_trace/` + `src/trace/` directories per FIXME 0103 Phase 2 | **int slice** (FIXME 0103 Phase 2): create `src/io_trace/` (per-thread VecDeque + observer registration callback); create `src/trace/` (trace ADT walker, GOT-swap orchestration, slash-command dispatch); rewire `src/main.rs` lines 45 + 73 (`io_trace_install_panic_hook`, `io_trace_flush_to_stderr`) to local module paths; rewire `src/observability.rs` doc-comment cross-references; rewire `src/session_v4.rs` lines 1965, 2029 (`cranelisp_trace_format` symbol-name registrations) to int-side symbol names |
| Row 12 (`cranelisp_op_*` 10 fns delete-content) | Backend's `IntrinsicSymbol` array stops registering them; backend's trait-knowledge map deletes (FIXME 0150 Phase 3) | **backend slice** (FIXME 0150 Phase 3): delete `operators.rs:323–394`; delete `compiler/literals.rs:327–332`; rename `operators.rs` → `primitives_inline.rs`; update `jit.rs::IntrinsicSymbol` array — remove `cranelisp_op_*` entries; depends-on shifts: `cranelisp-runtime` → `cranelisp-intrinsics` + `cranelisp-primitives` |
| Row 6 subordinate (IO observer registration site relocates from runtime to intrinsics) | D40's call-site contract retains, but the registration host moves | **intrinsics slice**: lands `cranelisp-intrinsics/src/io_observer.rs` (~50 LOC carrying `IoEventTag`, `IoEvent`, `IoObserver`, `register_io_observer`, `trace_anchor`); **int slice** (FIXME 0103 Phase 2): registers observer from int's session startup against the **intrinsics-side** API per D40's amended target (`int::io_trace::record` registered via `cranelisp_intrinsics::register_io_observer`) |
| Row 18 (workspace `Cargo.toml` member entry remove) | Coordinated commit that adds `cranelisp-primitives` + `cranelisp-intrinsics` member entries | **primitives slice + intrinsics slice + this slice**: the workspace `Cargo.toml` member-list update is a **single coordinated commit** at Phase 5 atomic close — adds the two new members and removes the old one in the same commit, alongside the directory delete (this slice's responsibility) |
| Row 18 (root `Cargo.toml` `[dependencies]` rewires) | Backend, exe-bundle, and root binary all currently depend on `cranelisp-runtime` | **backend slice**: `crates/cranelisp-backend/Cargo.toml` swaps `cranelisp-runtime` for `cranelisp-intrinsics` + `cranelisp-primitives`; **exe-bundle slice** (or coordinated within this slice if `cranelisp-exe-bundle` is `/dev` narrow scope): `crates/cranelisp-exe-bundle/Cargo.toml` similar swap; **this slice**: root `Cargo.toml` line ~26 (`cranelisp-runtime = { path = … }`) deletes; corresponding `cranelisp-primitives` + `cranelisp-intrinsics` rows added |
| Row 17 (delete `cranelisp-runtime/Cargo.toml`) | All three above (rows 6 subordinate + 12 + 18) have landed | n/a — terminal-step in this slice; no outgoing dependency |
| Test-surface dependencies (see §5) | `/qa` S66 test plan slice enumerates conformance tests against the new crate boundaries | **qa S66 test plan slice**: tests/ refers to `cranelisp_intrinsics::*` and `cranelisp_primitives::*` paths post-migration; existing `tests/spec_10_io.rs` + `tests/spec_12_runtime.rs` adapt to new symbol homes (these tests reference `cranelisp_runtime::*` paths today) |

**Cross-slice count**: 9 dependency rows naming **5 distinct sister slices** (primitives, intrinsics, int, backend, qa). All bilateral: each row identifies the corresponding entry in the other slice.

The dependency graph is **multi-fan**, not linear: this slice depends on primitives + intrinsics + int + backend slices having landed their respective phases; this slice's atomic close (Phase 5) consumes the success of all four. Per Principle 3 (dependency flows toward stability), the retirement is a coordinated inversion — the unstable surface (`cranelisp-runtime`) dissolves, and the stable surfaces (primitives + intrinsics + intrinsified int) absorb its content.

**Coordinated commit at Phase 5**: backend's depends-on shift and this slice's directory delete must commit together. If they split, the workspace temporarily can't build (backend depends on a deleted crate). `/sprint` should call out the coordinated-commit requirement explicitly in the wave plan.

---

## 5. Test surface impact

The migration's test surface impact is **predominantly path-rewiring**, not new-test authoring. The runtime's existing test density is high (every file ships `#[cfg(test)]` with `// spec:` annotations); tests port with their files.

### 5.1 Existing runtime unit tests touched

Each migrated file's `mod tests` block ports verbatim with the file. Because the crate boundary changes (extern symbols now live in `cranelisp-intrinsics` instead of `cranelisp-runtime`), **no test bodies change** — but the test target crate changes (tests run inside `cranelisp-intrinsics` and `cranelisp-primitives` after the migration, not inside `cranelisp-runtime`). Specific items:

- `decision24_run_io_pure_rc_balanced`, `run_io_trampoline_rc_balanced`, `run_io_trampoline_deep_bind_chain_rc_balanced`, `decision24_consume_shallow_*` (RC-balance tests in `io.rs` + `rc.rs`) port to intrinsics with no body change.
- `LIVE_ALLOCS` debug-assertion tests in `alloc.rs` port to intrinsics.
- HeapString layout + roundtrip tests in `string.rs` port to intrinsics.
- IVar PENDING → EVALUATING → RESOLVED CAS tests in `ivar.rs` port to intrinsics.
- `quote_sexp` + `sconcat` round-trip tests in `marshal.rs` port to intrinsics.
- Trace + io_trace tests in `trace.rs` + `io_trace.rs` port to `src/` per FIXME 0103.

### 5.2 Existing integration tests touched (in `tests/`)

Three integration tests directly reference `cranelisp_runtime::*` paths and adapt:

- `tests/spec_10_io.rs` — references `cranelisp_runtime::run_io_trampoline`, `cranelisp_runtime::IoTraceTag` etc. Path rewiring: `cranelisp_runtime::run_io_trampoline` → `cranelisp_intrinsics::run_io_trampoline`; `cranelisp_runtime::IoTraceTag` → (new home in `src/io_trace/`, accessed via `cranelisp::io_trace::IoTraceTag` or moved into a re-exported public path). **Each `cranelisp_runtime::*` use line in this file rewrites.**
- `tests/spec_12_runtime.rs` — same pattern; identifies as a test of the **runtime contract**, which under D43 splits into **primitives contract** + **intrinsics contract**. The test file may split into `tests/spec_12_primitives.rs` + `tests/spec_12_intrinsics.rs` per the new structure, OR remain a single file referencing both new crates' paths. **`/qa` slice's call.** This slice flags as an open question for `/qa` (§6 below).
- `tests/legacy/*` — multiple legacy tests reference `cranelisp_runtime` paths but are gated behind `#[ignore]` or live in `tests/legacy/`. Per memory `feedback_failing_not_ignored.md`, ignored tests are a failure mode; this slice does not enable them but flags the path-rewiring need to `/qa` if any legacy test gets re-enabled.

### 5.3 `src/` callers rewire (existing src/ code, not tests)

Per the §1 search:

- `src/main.rs:45` — `cranelisp_runtime::io_trace_install_panic_hook()` → `cranelisp::io_trace::install_panic_hook()` (or whatever local path the int slice picks).
- `src/main.rs:73` — `cranelisp_runtime::io_trace_flush_to_stderr()` → `cranelisp::io_trace::flush_to_stderr()`.
- `src/observability.rs:283, 595, 1226` — doc-comment cross-references; update to point at `src/io_trace/` (or whatever the int slice names the new module).
- `src/session_v4.rs:1965, 2029` — `"cranelisp_trace_format"` symbol-name strings registered with the JIT; update to whatever symbol name the int-side trace.rs registers under (post-migration).

These rewires land in the **int slice**, not this slice; this slice flags them.

### 5.4 New tests to author

**No new unit tests are intrinsic to this slice** — the migration is structure, not behavior. The primitives slice + intrinsics slice author any new unit tests for the new crate boundaries (e.g., a smoke test that `cranelisp_primitives::add_i64(2, 3) == 5`).

**Integration test for the migration's invariance** (`/qa` S66 test plan slice's call): one regression test asserting that pre-migration program behaviour matches post-migration. Specifically: a small Cranelisp program exercising primitives + intrinsics paths produces identical output before and after Phase 5. **Filed as a request to `/qa`** per the cross-slice protocol (memory: cross-skill defect handoff needs minimal repro — but here there's no defect, just a structural regression-guard request).

If during S66 implementation a circular-impl bug surfaces in the stdlib audit (Phase 4) — e.g., `(defn + [a b] (+ a b))` recurses infinitely once the trait-knowledge map deletes — the stdlib slice is responsible for the failing-test repro that joins the suite per memory `feedback_repros_join_suite.md`.

### 5.5 `cargo public-api` baseline impact

The runtime crate's `cargo-public-api` baseline (if it exists at S66 time per S65 W4 / W5 schedule) deletes. Two new baselines land for `cranelisp-primitives` + `cranelisp-intrinsics`. The `src/` int crate's baseline (if any) acquires the new `src/io_trace/` + `src/trace/` symbols.

---

## 6. Open questions

The retirement spec (D43 + FIXME 0150 + FIXME 0103) is unambiguous on the migration's shape. The slice surfaces five narrow questions where authoring met an edge.

1. **Marshaling primitives (`quote_sexp`, `sconcat`) — primitives or intrinsics?** Row 9 places `marshal.rs` in intrinsics per D43 §"Migration scope" table (which lists `marshal.rs` in the Cat 2 / `cranelisp-intrinsics` column implicitly — by absence from the Cat 1 row). But `quote_sexp` and `sconcat` are user-facing in the same sense as `int-to-string` (they appear as the implementation of macro-time Sexp construction in user code). **Slice's tentative read**: intrinsics, per the table; the macro-expander invokes them through the `macros/quote-sexp` symbol-table entry which points at the intrinsics implementation via GOT-indirection. **If `/arch` regards them as Cat 1 (primitives) the row reclassifies — file as same-sprint `/arch` revision FIXME.**

2. **`consume_trace_call` carve-out — extract during drop.rs migration, or absorb into trace.rs's new home?** Row 3 carves `consume_trace_call` (the trace-ADT walker) out of `drop.rs`'s migration to intrinsics, sending it instead to `src/trace/` per its single-consumer relationship to trace.rs. **Slice's tentative implementation**: extract the function body into `src/trace/drop.rs` (or absorb as a private helper inside trace.rs) at FIXME 0103 Phase 2 time. Two questions: (a) Does the function need to remain `extern "C"` for backend-emitted call invocation, or is it Rust-only after the trace machinery moves int-side? (b) If `extern "C"` is needed, does backend's emitted code reference it under a primitives-style name, an intrinsics-style name, or a new src-side intrinsic registration? **Tentative read**: trace runtime functions are `extern "C"` callable from JIT code per `crates/cranelisp-runtime/src/lib.rs:93–100`'s `cranelisp_trace_*` registrations; FIXME 0103 Phase 2 already plans to handle the `cranelisp_trace_*` registrations from int's side via the existing JIT-symbol-registration path. `consume_trace_call` follows the same pattern. **Filed as question for `/arch` confirmation, not blocking.**

3. **`design/runtime/runtime.md` (master design) — archive, redirect, or split?** Row in §2.6: tentatively suggested moving `runtime.md` to `archive/` with a single-line redirect to `design/intrinsics/intrinsics.md` + `design/primitives/primitives.md`. Alternatives: split the master-doc content into the two new directories (more work, but more accurate); leave in place as historical record (simplest, but creates a stale-doc smell). **Slice's tentative preference**: archive with redirect; the historical record is `design/runtime/runtime.md` itself (already exists), and the redirect is sufficient navigation aid. **Final disposition is `/arch`'s call** at the S66 close gate.

4. **`tests/spec_12_runtime.rs` — split or rewire?** §5.2 surfaces the choice: split the test file along the new crate boundary (`tests/spec_12_primitives.rs` + `tests/spec_12_intrinsics.rs`) for clarity, or keep one file referencing both. **Slice's tentative read**: `/qa`'s call at the S66 test plan slice; the split is more honest but the rewire is cheaper. Slice does not bind.

5. **Phase 2 sequencing — option (a) vs option (b)** — see §2.4 above. Slice tentatively prefers (b) (bundled FIXME 0103 + FIXME 0150) for cleanliness; `/sprint` decides at the wave-plan boundary.

If `/arch` regards any of these as substantive (i.e., not editorial), the slice files as `design/arch/fixmes/0152-name.md` (sequential allocation; collision-resolved at wave gate). **Tentative count: 0–2 FIXMEs may be filed during S66 implementation depending on `/arch`'s read.** Per the architectural-question protocol (uninvented answers — slices surface, don't unilaterally resolve), the slice does not pre-bind.

---

## 7. Cross-references

- `design/arch/decisions/0043-runtime-split-into-primitives-intrinsics.md` — D43 (the retirement spec)
- `design/arch/decisions/0040-runtime-trace-io-trace-relocate-to-int.md` — D40 (trace + io_trace relocation; intersects this slice via FIXME 0103)
- `design/arch/legacy/substance-scoping.md` §1.1 + §1.7 — substance source (the table of what moves where)
- `design/arch/fixmes/0150-runtime-split-primitives-intrinsics.md` — D43 implementation tracker (target `/dev`); this slice executes against its Phase plan
- `design/arch/fixmes/0103-dev-runtime-int-trace-io-trace-relocation-and-io-observer.md` — companion FIXME for trace + io_trace; intersects rows 7 + 10
- `design/arch/fixmes/0102-dev-runtime-claude-md-missing.md` — closes-by-vacuum when `cranelisp-runtime` retires (row 19)
- `design/runtime/runtime.md` — runtime master design (the historical record this slice retires)
- `design/arch/facades/primitives.md` — destination facade for rows 12–14
- `design/arch/facades/intrinsics.md` — destination facade for rows 1, 2, 3, 4, 5, 6, 8, 9, 11
- `design/arch/facades/backend.md` — depends-on shift (primitives + intrinsics, not runtime); IntrinsicSymbol array trim
- `design/arch/facades/int.md` — receives trace + io_trace per FIXME 0103
- `design/arch/bounded-contexts.md` §4 retirement → §4a (primitives) + §4b (intrinsics) — already drafted S65 W1; becomes effective at Phase 5
- `design/arch/sprint-65-reshape-phase-2-review.md` §3 — slice template authority
- `sprints/SPRINT.md` Wave Phase 4 W4a — slice-authoring wave
- `crates/cranelisp-runtime/src/` — current source under retirement (see §1 source-to-destination table)
- `src/main.rs:45,73` — `io_trace_install_panic_hook` + `io_trace_flush_to_stderr` callers (rewire per FIXME 0103)
- `src/observability.rs:283,595,1226` — doc-comment cross-references (update post-migration)
- `src/session_v4.rs:1965,2029` — `cranelisp_trace_format` symbol registrations (update per FIXME 0103 Phase 2)
- `tests/spec_10_io.rs`, `tests/spec_12_runtime.rs` — integration tests requiring path-rewiring (open question §6.4)
