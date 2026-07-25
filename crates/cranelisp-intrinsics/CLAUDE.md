# cranelisp-intrinsics — local conventions

The voice of the code: API gotchas, heap/RC/reactor invariants with provenance,
and debug hooks for the backend-emitted runtime library. Owned by `/dev` when
narrow-deployed to this crate.

This crate is the **runtime library `cranelisp-backend` emits calls into** (BC
§4b) — paired with `cranelisp-backend`, which depends on it and lowers
`Linkage::Import` string-named calls to these targets. Do NOT restate the ABI /
consumer / catalog contract here — it is the crate-root `lib.rs` `//!` (the
facade doc, `/arch`-approved). Design direction lives in `design/intrinsics/`
(`reactor.md`, `intrinsics-table.md`, `rc-inc-entry-point.md`). This file is
only what the next code-touching agent would otherwise re-derive from source.

## Submodule seam map (where the `#[cfg(test)]` lives)

Most modules externalize their tests to `foo/tests.rs` via a trailing
`#[cfg(test)] mod tests;` (the `#[path]` is implicit — the sibling dir):
`alloc`, `catalog`, `diagnostics`, `drop`, `heap_string`, `io`, `io_observer`,
`ivar`, `layout`, `panic`, `rc`, `reactor`, `trace`, `trace_format`, and
`vec_runtime`. `heap_access`, `io_guard`, and `strand` keep `mod tests { … }`
inline in their `.rs` files; `lib.rs` also keeps the DEF-6 `host_callbacks`
pin inline. `drop/rc_balance.rs` is a second test file under `drop/` holding
the `assert_balanced` alloc==dealloc RC-leak assertions (the crate-internal
stand-in for the retired `assert_rc_balanced`, FIXME 0129).

## Heap layout — base-pointer convention (Decision 10/11)

`alloc::alloc_with_rc(payload)` returns the **BASE** pointer: `+0` alloc_size
(i64), `+8` rc (i64, init 1), payload at `+16` (`HeapHeader::SIZE`). All field
access is positive-offset from base (departs from the sketch's interior
pointer). `heap_access::{read_i64,write_i64}` (`pub(crate)`, MED-1/FIXME 0370)
is the single owner of the raw `*(base+off)` primitive — do not open-code it;
it does NOT own the header layout (that is `cranelisp_types::HeapHeader`) nor
the consuming dec sequences (those stay per-module by design).

- **Blessed layout-ABI consts are locked by `const _: () = assert!(…)`** and
  read by `cranelisp-primitives` with no duplicate copy (FIXME 0245, Principle
  7/14): `HeapString::{LEN_OFFSET=16, DATA_OFFSET=24}`,
  `vec_runtime::{LEN_OFFSET=16, CAP_OFFSET=24, DATA_PTR_OFFSET=32}`. A Vec is
  TWO allocations — RC'd struct `[hdr|len|cap|data_ptr]` (40B) + a plain
  (non-RC) `cap*8` data buffer. Changing any offset is a version bump, not a
  guard.
- **BASE vs PAYLOAD is the recurring footgun.** `heap_alloc` (`runtime/alloc`)
  returns base; `heap_alloc_payload` returns base+16 and is the ONLY correct
  wiring for `HostCallbacks::alloc` (DLLs write from payload 0). DEF-6 (S86)
  corrupted the RC header one node per host↔DLL crossing by wiring the base
  form; `host_callbacks()` in `lib.rs` is the one construction site and its
  fn-ptr identity is pinned by `host_callbacks_alloc_is_payload_returning`.
- `cranelisp_alloc_with_tag` builds `[hdr|tag@16|field_0@24|…]` byte-identical
  to the backend's `HeapAdt` emission so a host-built ADT is indistinguishable
  from a JIT-built one; data-constructor layout only (nullary ctors are bare
  i64 tags, never allocated).

## RC discipline (BC §4b invariant 3)

- **Blessed entry points**: inc → `rc::rc_inc`; shallow dec → `rc::consume_shallow`.
  Open-coded `fetch_add`/`fetch_sub` at extern sites must route through these
  (Principle 7). Inc uses `fetch_add(1, Release)` — the NFR C.4.1 floor
  (`spec/appendix-c-nfr.md` §C.4.1); dec uses `Release` + an `Acquire` fence on
  the free path.
- **`consume_shallow` is NOT safe for Vec (separate data buffer), closures
  (embedded drop glue), or ADTs with heap fields** — those recurse through
  `drop::consume_{slist,sexp,vec_of_heap,io_tree}`, which mirror the backend's
  inline drop glue (`emit_rc_dec_with_inline_drop_glue`). Pick the wrong
  consume fn and you leak or dangle.
- **Nullary-tag guard**: every RC entry no-ops when `ptr < NULLARY_TAG_THRESHOLD`
  (a bare Mixed-category tag, not a heap pointer). Preserve it in any new RC path.
- **IVar spark RC stays SeqCst-atomic** (Decision 13) and is deliberately NOT
  covered by the `NONATOMIC_RC` switch — a small fixed per-spark cost, not the
  per-node data RC the volume claim is about (arch R4 scoped `heap.rs`/`rc.rs`/
  `drop.rs` only).

## Known asymmetries (misread as bugs)

- **`intrinsics_table()` deliberately EXCLUDES real intrinsics**: the catalog is
  *string-named, user-code-dispatched, backend-emitted* targets only.
  `cranelisp_alloc_with_tag` (Rust-path host callback), `cranelisp_check_layout_hash`
  (startup-object only), and the `pub(crate)` stat/check hooks (`rc_dec_check`,
  `rc_stat_{inc,dec}`, `reuse_{hit,miss}_stat`, `extern_adapt_str_len_stat`,
  catalog-referenced by fn-ptr) are all absent by design. Absence ≠ omission.
- **`CRANELISP_NONATOMIC_RC` is UNSOUND above one worker** (lost-update race →
  UAF/leak). Measurement-only, at `RAYON_NUM_THREADS=1`; excluded from the
  canonical `nextest` run. Never ship it.
- **Byte-identical-off is a hard discipline**: every `*_STATS` / dec-check hook
  emits ZERO IR when its env gate is off (the codegen-time gate lives in the
  backend). `reuse_hit`/`reuse_miss` print `0` — placeholder honesty; their
  runtime writer lands at increment-II slot-reuse (`ownership-codegen.md` §6.5).
  `stack_slot`/`rc_nonatomic`/`rc_atomic` in `[RC_STATS]` are **codegen-time**
  counts (backend is the writer) — honestly `0` in a separate `--link` run.
- **Reactor `host` is a raw `*mut Reactor`, NOT derived from `&Reactor`** (B1
  provenance, `build_host_ctx`): poll-fns reborrow `&mut` and mutate through it,
  `turn()` mutates between polls; a shared-ref tag would be UB under Stacked/Tree
  Borrows. Both paths share one raw provenance; sound only because their `&mut`
  lifetimes never overlap (poll-fns inside `Future::poll`; `turn()` only
  between). Do not "clean this up" to a reference.
- **No hand-written `Drop for EffectPoll`** — the `_interest: ReactorInterest`
  field's own drop glue IS the fd/timer active-deregistration path (the
  cancellation leak fix, Principle 18). Adding a manual `Drop` double-frees.
- **Reactor + `mio`/`futures` are UNCONDITIONAL** (the `concurrency-runtime`
  feature was retired S96, `platform-interface.md` §6.8.0a). Lean-default is a
  RUNTIME property — a pure-blocking program constructs no `mio::Poll` (lazy
  init per drive) — never a `#[cfg]` split. `reactor` and `strand` are
  `pub(crate)`: no cross-crate consumer yet (the `/strand` int dump is deferred).

## Debug hooks

| Env var | Effect | Provenance |
|---|---|---|
| `CRANELISP_RC_TRACE=1` | stderr `[RC] op ptr rc tag@16` per alloc/free/inc/dec (debug builds only) | `rc.rs` |
| `CRANELISP_HEAP_SCAN` | full-heap header-integrity scan at every alloc/free; fires on the first clobbered `alloc_size` (debug only) | FIXME 0494 bug #2 |
| `CRANELISP_RC_DEC_CHECK` | backend emits `rc_dec_check` before each inline dec — catches a dec of an already-freed ptr AT the dec (codegen gate) | FIXME 0494 |
| `CRANELISP_RC_STATS` | `[RC_STATS]` atexit line (rc_inc/dec, allocs/deallocs, per-mechanism family, `alloc_bytes`) | S99/S102-I/S105 |
| `CRANELISP_NONATOMIC_RC` | non-atomic RC RMW (unsound >1 worker; isolates atomic-instruction cost) | S99 W0 |
| `CRANELISP_SPARK_STATS` | `[SPARK_STATS]` atexit — spark spawns + `ivar_force` outcomes + executing/peak utilization signals | S104 W0 / FIXME 0534 |
| `CRANELISP_SPARK_BUDGET=N` / `_CORE_MULT=k` / `_SATURATION_GATE=1` | in-flight-spark cap; default `k=2 × threads` (M-dynamic, default-on; `k=4` = pre-S104 static budget, `k=0`/`BUDGET=0` = fully serial); saturation gate = `1×` | S104 W2 §2.8.3 |
| `CRANELISP_NO_LENIENT` / `_SPARK_MAX_DEPTH` / `_HIER_DECLINE` / `_IVAR_SPIN=1` | disable lenient eval / depth cap / hierarchical decline / restore pure busy-spin wait | `ivar.rs` |
| `CRANELISP_DRIVE_MODE=server` / `_REACTOR_BACKSTOP_MS` / `_DEGREE` | reactor drive mode (default OneShot w/ 30s hang guard), scaled backstop, program-degree throttle | FIXME 0479 / `reactor.md` §8.3 |
| `CRANELISP_QUARANTINE_FREED` (+ `_MAX_BYTES=N`) | M1 — withhold freed blocks from the system allocator so `is_live` stays false forever (stale-dec/inc asserts fire deterministically); FIFO-release the coldest past `N` bytes (unset = unbounded) | S113 W5a / `design/intrinsics/diagnostic-modes.md` §3 |
| `CRANELISP_SCRUB_FREED` | M2 — poison header+payload with `0xDEAD2FEE_DEAD2FEE` at the free seam (a stale read is wild-negative / non-canonical ptr / underflow-tripping rc) | S113 W5a / diagnostic-modes.md §3 |
| `CRANELISP_ALLOC_PARITY` (+ `_DUMP`) | M3 — atexit hard-check `ALLOC_COUNT==DEALLOC_COUNT` (+ empty live-set in debug); dump then non-zero abort on imbalance. `_DUMP` = print-and-continue ledger, no abort | S113 W5a / diagnostic-modes.md §3 |
| `CRANELISP_RC_DEC_CHECK` | ALSO release-gates the intrinsic-body RC/alloc seam checks (A1 inc `rc>0` / A2 `consume_shallow` / A3 drop-glue `atomic_dec_rc` underflow / A4 dealloc size-sanity) — a located hard-fail, not just the codegen dec-check hook | S113 W5a / diagnostic-modes.md §5 |

The three memory-safety diagnostic modes (M1/M2/M3) + the seam asserts (A1–A4)
live in `src/diagnostics.rs`. **Byte-identical-off**: all-off = today's code (one
cached bool load per gate, no list constructed, no atexit registered). They hook
the two existing funnels (`alloc::alloc_with_rc`, `alloc::dealloc`) + the two
always-on counters — no ABI/catalog/`cranelisp-types` surface, no emitted-IR
change, identical in `--run`/REPL/`--link`. Fixed order in `dealloc`: capture
`FREED_TRACKED` identity → (M2) scrub → (M1) quarantine-or-release → count. The
A1 debug `is_live` assert is the always-on inc-half of the FIXME-0494 dec-half
check; A2–A4's release variants read only the RC field / size (the `is_live` /
double-free / header-integrity halves stay debug-only — they need `LIVE_ALLOCS`;
M2 poison + M3 parity are their release faces).

The **fork-join error-slot ferry** (`ivar.rs`, `panic.rs`, `test-discovery.md`
§6): a spark thunk's runtime panic lands in the *worker's* `RUNTIME_ERROR`
thread-local; the worker ferries `Some(msg)` into the IVar `error` field (`+40`,
published under the RESOLVED store), and every reader re-raises it join-side via
`panic::set_runtime_error` (first-error-wins) — so lenient eval stays
observationally equivalent to sequential (spec §12.4.3). Platform-dispatch
faults use the same intrinsics-sets-slot / int-reads-and-composes split
(`panic::DispatchFault`, FIXME 0327) — intrinsics is diagnostics-free by charter.
