# cranelisp-intrinsics — S87 Stage-B deep audit

> **Point-in-time, delta + currency assessment (2026-06-20).** Per `sprints/SPRINT.md`
> Stage B depth model: this is a **delta + currency check** against the named baseline
> `audits/intrinsics-2026-06-14.md`, not a from-zero look. It reconciles every prior
> finding (still-open / regressed / resolved) on the same instrument, then walks the
> fixed 7-lens checklist with emphasis on the unsafe audit (this is the highest
> test-density / most `unsafe`-bearing crate) and RC-symmetry (the crate holds the
> runtime RC helpers). `/review` files no FIXMEs itself; findings below are proposed
> for `/sprint` wave-gate disposition. Canonical as-designed surface remains
> `bounded-contexts.md` §4b + the crate-root `//!` + `design/arch/tracing.md`.

**Crate**: `crates/cranelisp-intrinsics/src/` (17 files; corrected prod LOC **2,065**,
59% inline-test — the workspace's highest test density; `audits/loc-s87.md`).
**Companion diagram**: `audits/cranelisp-intrinsics-s87-current-state.mmd` (fresh — no predecessor).

---

## 1. Baseline reconciliation (every prior finding)

The crate has been **substantially refactored since 2026-06-14**: a `heap_access.rs`
module now exists, `trace_format.rs` was split out of `trace.rs`, and the dead Par
stub was deleted — i.e. most of the baseline's Phase-2/Phase-3 plan landed (the close
notes cite FIXME 0370 as the carrier). The catalog count was also reconciled to 29.

| Baseline finding | Status | Evidence |
|---|---|---|
| **HIGH-1** — three-way catalog count disagreement (27/28/29) | **RESOLVED** | `lib.rs:128-133` now cites the test constant (`EXPECTED_NAMES` / `name_set_is_exactly_the_expected_29`) as the single authority and says "16 core + 12 trace + `catch-runtime-error`"; `catalog.rs:73-76` says 29. The literal-restated counts are gone. *BC §4b reconciliation (the `/arch` half) is out of this crate's scope — confirm separately.* |
| **HIGH-2** — BC §4b inv 11/13/14 stale "TARGET/pending/owed" | **OUT-OF-CRATE** (cannot verify here; targets `/arch` + `design/arch/bounded-contexts.md`). The as-built side is confirmed present: catalog (`catalog.rs`), combinator (`panic.rs:404`), ferry (`ivar.rs:220/289`, `io.rs` worker-take), fault guard (`io_guard.rs`). Carry as `/arch` synthesis input. |
| **HIGH-3** — `trace.rs` 2,297 + `io.rs` 1,254 mini-monoliths; overlong fns | **LARGELY RESOLVED** | `trace.rs` now 924 raw / 409 corrected; the pure formatter is split into `trace_format.rs` (the highest-leverage split the baseline named). `io.rs::run_io_trampoline_inner` is now decomposed by arm (`force_effect_node`, `run_par_node`, `feed_continuation`; `io.rs:305-390` ≈ 85 lines) — under the ~100-line budget. **No production fn exceeds 100 lines.** Residual: see NEW-2 (io.rs is still 791 raw, the largest file). |
| **MED-1** — heap read/write open-coded across modules | **MOSTLY RESOLVED** | `heap_access.rs` (`read_i64`/`write_i64`) is the single owner; `trace.rs`/`io.rs`/ADT paths route through it. **Residual open-coded sites remain** (NEW-3): `drop.rs:204-206` (Vec fields), `ivar.rs:171,289` (error field), `heap_string.rs:91`, `alloc.rs:154`. |
| **MED-2 / LOW-3** — `IntrinsicEntry::is_runtime` pub field, no consumer | **STILL OPEN** | `catalog.rs:96-100` field still present, rustdoc still says "no dispatch consumer today"; `is_runtime_classification` test (`catalog.rs:289-308`) still derives it from the name prefix. Re-filed as F4. |
| **LOW-1** — dead `dispatch_par_branches` no-trace stub | **RESOLVED** | Deleted; only `dispatch_par_branches_with_trace` remains (`io.rs:485`). The deletion is recorded in a comment at `io.rs:482-484`. Two stale doc mentions linger in `io_observer.rs:60,64` (NEW-5, trivial). |
| **LOW-2** — `io_observer::emit` data→fn transmute | **RESOLVED** | `io_observer.rs:183` now uses the blessed `usize`→fn transmute via `AtomicUsize`/`OBSERVER_SLOT`; the SAFETY comment (`:176-182`) correctly distinguishes integer→fn (blessed) from the prior data→fn (boundary) form. |
| **Hidden coupling: trace ⇄ panic** | **PRESERVED + correct** | `panic.rs:430` still calls `crate::trace::clear_trace_guard_on_panic()`. Cross-module thread-local dependency intact. |
| **Hidden coupling: io ⇄ io_guard ⇄ panic ⇄ platform** | **PRESERVED + correct** | Single force site (`io_guard::force_effect_thunk_protected`) wired into the Effect arm. |

**Count: 5 RESOLVED, 2 STILL-OPEN (MED-2/LOW-3 collapse to one), 1 OUT-OF-CRATE.**
The crate's structural-health verdict from the baseline ("good structural health; no
Blockers; documentation drift the main problem") **holds and improved** — the
documentation drift (HIGH-1) is fixed, the monoliths are carved down, and `unsafe`
discipline remains exemplary.

---

## 2. Unsafe-code audit (dedicated subsection)

Per the LOC pre-pass directive, the unsafe audit runs here regardless of size. Every
`unsafe` block / `unsafe fn` / `transmute` was inspected for (a) a `// SAFETY:`
comment that *actually* justifies the invariant, (b) raw-pointer encapsulation, (c)
fn-pointer cast validation, (d) containment.

**Verdict: PASS, with one Important gap (NEW-1).** No `unsafe impl Send`/`Sync`
anywhere (the crate deliberately uses `pub fn intrinsics_table()` over a `pub static`
precisely to avoid one — `catalog.rs:22-31`). Raw-pointer arithmetic is now contained
behind `heap_access` + per-module layout helpers. RC dec sequences are uniform
(Release + Acquire fence; IVar's SeqCst divergence is documented, FIXME 0397).

| Site | Operation | SAFETY verdict |
|---|---|---|
| `io.rs:407-408` `call_continuation` | `transmute(code_ptr) -> extern "C" fn(i64,i64) -> i64` | **MISSING SAFETY comment** → NEW-1 |
| `ivar.rs:213` `ivar_force` | `transmute -> extern "C" fn(i64) -> i64` (closure code) | OK — surrounding doc covers ABI/arity |
| `ivar.rs:246` `ivar_force` | `transmute -> extern "C" fn(i64) -> i64` (drop glue) | OK |
| `drop.rs:397` `consume_closure` | `transmute -> extern "C" fn(i64)` (drop glue) | OK — SAFETY at `:379-380` |
| `panic.rs:271` `cranelisp_run_program` | `transmute(main_ptr) -> extern "C" fn() -> i64` | OK — SAFETY at `:269-270` |
| `panic.rs:415-417` `catch_runtime_error` | `transmute -> extern "C" fn(i64) -> i64` (thunk) | OK — SAFETY at `:412-413` |
| `io_observer.rs:183` `emit` | `transmute::<usize, IoObserver>` | OK — blessed integer→fn idiom, SAFETY at `:176-182` |
| `layout.rs:76` | `*(linked as *const &'static str)` fat-ptr read | OK — SAFETY at `:69-75` |
| `io_guard.rs:189/192` | `sigsetjmp`/`siglongjmp` FFI | OK — SAFETY at `:182-186` |
| `heap_access.rs:31,40` | `*((base+off) as *const/*mut i64)` | OK — the encapsulated single owner |
| RC dec: `rc.rs:86`, `drop.rs:81`, `ivar.rs:129,251` | `fetch_sub(Release/SeqCst)` + Acquire fence | OK — uniform; canonical = `rc::consume_shallow` |
| ADT/heap reads: `alloc.rs`, `heap_string.rs`, `vec_runtime.rs`, `trace_format.rs` | layout-const offset reads | OK — all SAFETY-commented (open-coding is NEW-3, not a soundness gap) |

`call_continuation`'s transmute is the **only** fn-ptr cast without a local `// SAFETY:`
— and it is the most-invoked one (every IO continuation). The crate's rule (`/review`
unsafe-audit: "`// SAFETY:` on every `unsafe` block") is otherwise 100% honoured, so
this is a one-line correctness-of-discipline gap, not a soundness Blocker.

---

## 3. Findings (severity-ranked)

### NEW-1 (Important) — `call_continuation` transmute lacks a `// SAFETY:` comment
**File**: `crates/cranelisp-intrinsics/src/io.rs:407-408`
The fn-pointer transmute `transmute(code_ptr as *const ()) -> extern "C" fn(i64,i64) -> i64`
has no `// SAFETY:` comment, while every other transmute in the crate (and the
`/review` unsafe-audit rule "`// SAFETY:` on every `unsafe` block") does. The invariant
*is* documented prose-style in the fn's outer doc-comment (`:392-404`: closure layout,
`code_ptr` signature) — but the unsafe-audit rule wants it at the block. This is the
hottest fn-ptr cast in the crate (every IO continuation routes through it).
**Fix** (`target: /dev`): add a `// SAFETY:` block above `:407` stating that `code_ptr`
was read from a finalized HeapClosure's `CLOSURE_CODE_PTR_OFFSET` slot, is non-null by
the closure-construction invariant, and has the `extern "C" fn(env, val) -> i64` ABI
the backend emits. (`design/arch/principles.md` — unsafe discipline.)

### NEW-2 (Important) — `vec_set_copy` RC asymmetry: the intrinsics half of the S86 seed
**File**: `crates/cranelisp-intrinsics/src/vec_runtime.rs:220` (the `call_elem_fn(elem_inc_fn, val)`
that inc's the *new* value), in `vec_set_copy` (`:187-228`).
**This is the S86 `vec_set_copy` RC-asymmetry seed, characterized on the intrinsics side.**
`vec_set_copy` inc's the replacement value **unconditionally** (`:220`), with a comment
saying it "mirrors the COW mutate-in-place codegen path". The **backend then compensates**:
`vec_codegen.rs:272-277` and `:388-395` call the `vec-set-copy` extern and immediately
emit a *dec* on `new_val` for the temporary (non-Var) case via
`emit_vec_set_copy_temp_compensation` (`vec_codegen.rs:404-456`). So the runtime inc's,
then the backend dec's it back for temporaries — an inc-then-compensate dance.

The **asymmetry is with `vec_set_copy`'s own sibling** `vec_push_copy` (`vec_runtime.rs:238-265`):
that fn copies existing elements with inc but does **NOT** inc the appended `val` — the
backend manages the appended-element inc itself (`vec_codegen.rs:474-500`). The two COW
copy paths thus split responsibility for the new element differently: `set` inc's in the
runtime + compensates in the backend; `push` inc's in the backend only.

The symmetric design the seed proposes: **stop the runtime inc at `vec_runtime.rs:220`**
(mirroring `vec_push_copy`), letting the backend own the new-element inc on both paths —
which eliminates `emit_vec_set_copy_temp_compensation` entirely.
**Disposition**: this is a **cross-crate RC-model alignment** (intrinsics `vec_runtime.rs:220`
⟷ backend `vec_codegen.rs:272-277,388-456`). It is NOT a defect today (the inc + dec net
out correctly — tests `test_vec_set_copy_incs_new_value` + the backend compensation guard
both pass); it is a duplication/Principle-7 coupling. **Route to `/arch` synthesis** to
pair with the backend-side audit; do **not** change either side in isolation (changing the
runtime inc without removing the backend compensation is a use-after-free regression of
FIXME 0296). `/review` flags it as the named seed, not a unilateral fix.

### NEW-3 (Medium) — heap reads still open-coded at 6 sites despite `heap_access`
**Files**: `crates/cranelisp-intrinsics/src/drop.rs:204-206` (Vec len/cap/data_ptr),
`ivar.rs:171` + `ivar.rs:289` (error field), `heap_string.rs:91`, `alloc.rs:154`.
MED-1 introduced `heap_access::read_i64`/`write_i64` as the single owner, but these six
sites still re-derive `*((base+off) as *const i64)` inline. Each is SAFETY-commented, so
this is a Principle-7 duplication residue, not a soundness gap. The `drop.rs:204-206` Vec
read is the most pointed: it duplicates `vec_runtime`'s own `read_len`/`read_cap`/`read_data_ptr`
private helpers using a *separate* set of `VEC_*_OFFSET` consts in `drop.rs` — two
layout-accessor families over the same Vec layout.
**Fix** (`target: /dev`): route the bare offset reads through `heap_access`; or, for the
Vec triple, document why `drop.rs` cannot reuse `vec_runtime`'s helpers (cross-module
`pub(crate)` exposure) and consolidate. Lower-leverage than NEW-1/2 — the bulk of MED-1
already landed.

### NEW-4 (Medium) — `IntrinsicEntry::is_runtime` pub field still has no consumer
**File**: `crates/cranelisp-intrinsics/src/catalog.rs:96-100`; test `:289-308`.
Unchanged from baseline MED-2/LOW-3. The field is `pub` on the published catalog
(`public-api.txt`), its own rustdoc admits "no dispatch consumer today", and the
`is_runtime_classification` test proves it is fully derivable from the name prefix
(`runtime/` | `cranelisp_ivar_` | `cranelisp_trace_` | `cranelisp_collect_trace`). A
public-ABI field carried for an un-arrived future, validated only by a test that
re-derives it — the `/review` premature-abstraction trigger (Principle 6) + unjustified
`pub` (public-surface-drift check).
**Fix** (`target: /arch` — it touches `public-api.txt`): name the prospective consumer
in the rustdoc + a BC sentence, or drop the field (the catalog re-derives the split from
the name, as the test already does).

### NEW-5 (Low) — stale `dispatch_par_branches` doc references after the stub deletion
**File**: `crates/cranelisp-intrinsics/src/io_observer.rs:60,64`.
LOW-1's dead stub was deleted, but two `IoEventTag` doc-comments still say
"`dispatch_par_branches` launched a single branch" / "completed". The live fn is
`dispatch_par_branches_with_trace`. Cosmetic doc drift.
**Fix** (`target: /dev`): update the two doc lines to the `_with_trace` name.

### NEW-6 (Low) — `panic!` on unknown IO tag in a production path
**File**: `crates/cranelisp-intrinsics/src/io.rs:366` —
`_ => panic!("cranelisp_run_io: unknown IO tag {tag}")`.
A defensive panic in the trampoline's tag dispatch. With well-typed input the arm is
unreachable, so this is a guard, not a live failure mode — but it is the
`sketch/audits/codegen.md` "panics in non-test code" pattern the audit-vigilance list
flags. It is in the runtime crate where a panic unwinds across the JIT/FFI boundary
(UB-adjacent on `extern "C"`).
**Fix** (`target: /dev`, Suggestion-leaning): downgrade to the crate's
sentinel-return-on-fault convention the Effect/error arms already use
(`return 0` per `io.rs:329,382`), or document why an unknown tag is genuinely
unrecoverable (it indicates a codegen/ABI corruption, not a runtime condition) and a
panic is the intended fail-fast. The `alloc.rs:94/162` + `drop.rs:217` `unreachable!`s
are layout-calculation invariants (acceptable — true unreachables).

---

## 4. Lens checklist coverage

| Lens | Result |
|---|---|
| (i) duplicated code paths / mirrors | NEW-3 (heap reads), NEW-2 (vec_set_copy runtime/backend mirror — the named seed). The `drop.rs` Vec-accessor family mirrors `vec_runtime`'s. |
| (ii) dead paths | Clean — LOW-1 stub deleted; only NEW-5 stale docs remain. |
| (iii) function-budget overruns | Clean — no production fn > 100 lines (HIGH-3 resolved; `run_io_trampoline_inner` decomposed). |
| (iv) RC-symmetry (Decision 24/13) | RC dec sequences uniform (Release + Acquire; IVar SeqCst documented). The one asymmetry is the `vec_set_copy` new-val inc (NEW-2) — cross-crate, routed to `/arch`. Consuming-inc convention honoured at the extern boundary. |
| (v) resolution-seam consolidation | Catalog is the single owner of the name-agreement contract (29 entries, guardrail tests). No N-chokepoint drift in this crate. |
| (vi) interim-architecture residue (P8) | None — the `JITBuilder::symbol` narrowing (Decision 0048), flat-catalog-not-GOT, and consuming convention are all convergent as-built vs as-designed. |
| (vii) cross-crate / host-callback hygiene (R5b) | The `vec_set_copy` runtime/backend coupling (NEW-2) is the chief cross-crate item — a runtime helper and a backend codegen path that each manage one half of the same RC obligation. Paired with the backend audit + FIXME 0407 family for `/arch`. The IO Effect funnel (io → io_guard → platform → panic) is the single force site — clean. |

---

## 5. Proposed FIXMEs (for `/sprint` wave-gate; `/review` files none)

| # | Target | Severity | Summary |
|---|---|---|---|
| F1 | `/dev` (intrinsics) | Important | Add `// SAFETY:` to the `call_continuation` transmute (`io.rs:407-408`) — NEW-1 |
| F2 | `/arch` | Important | `vec_set_copy` runtime/backend RC-asymmetry alignment: stop runtime inc (`vec_runtime.rs:220`) + drop backend compensation (`vec_codegen.rs:404-456`) as a paired change — NEW-2. **Pair with the backend audit; do not split.** |
| F3 | `/dev` (intrinsics) | Medium | Route the 6 residual open-coded heap reads through `heap_access`; consolidate the `drop.rs` Vec-accessor family — NEW-3 |
| F4 | `/arch` | Medium | Justify or drop the unused `IntrinsicEntry::is_runtime` pub field — NEW-4 (carried from MED-2) |
| F5 | `/dev` (intrinsics) | Low | Fix the two stale `dispatch_par_branches` doc references (`io_observer.rs:60,64`) — NEW-5 |
| F6 | `/dev` (intrinsics) | Low | Replace or justify the `panic!` on unknown IO tag (`io.rs:366`) — NEW-6 |

No Blocker findings. The crate's structural health is strong and improving against the
baseline: HIGH-1/HIGH-3/MED-1(bulk)/LOW-1/LOW-2 all resolved this cycle; the remaining
items are one discipline gap (F1), the named cross-crate seed (F2, routed to `/arch`),
and small residue (F3-F6).
