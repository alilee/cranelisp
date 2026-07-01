---
number: 0494
target: /arch
filed_by: /dev
filed_at: 2026-07-01
sprint_filed: 98
refers_to: design/arch/bounded-contexts.md §4b invariant 15 + §3 backend-obligation note, design/arch/fixmes/0486-arch-int-backend-boundary-for-the-trampoline.md (S98 Level-1 ruling), crates/cranelisp-intrinsics/src/{io.rs (await_poll_node), reactor.rs (EffectPoll/StateClosure), drop.rs}, tests/launch_vec_send_corrupt.rs, tests/launch_grid_corrupt.rs, tests/exemplar_web.rs
status: open
---

# Invariant-15 runtime keep-alive LANDED but does NOT fix bug #2 — the residual UAF is a /backend borrowed-Var two-live-vec RC miscount, not the poll state-closure

> ## ⚠️ ASAN GATE-STOP (2026-07-01, /dev, `cranelisp-intrinsics` deploy) — ASAN CANNOT localize: the faulting store is JIT-emitted; BOTH named Rust candidates RULED OUT
> Built BOTH the host `cranelisp` binary **and** the dlopen'd web cdylib with
> `-Zsanitizer=address` (dlopen instrumentation SUCCEEDED — 217 asan syms in the exe, 35 in
> the DLL) and ran the exact deterministic crashing fixture (8–16 request burst) — **ASAN
> stays completely clean: zero reports, no crash, server survives, all responses correct
> (`body_len=2184` each).** Reason: `vec-get`/`vec-set`/`vec-push` are **inlined as Cranelift
> IR (JIT machine code)** in the common COW path (`cranelisp-backend/src/compiler/vec_codegen.rs`,
> "COW inline + extern fallback"), and **ASAN cannot instrument JIT code** — its allocator's
> redzone+quarantine simply absorbs the overrun the glibc allocator reports as
> `free(): chunks in smallbin corrupted`. This ASAN run is a **localized confirmed-negative**:
> it RULES OUT **both** FIXME-0494 candidates as the faulting site — (1) reactor state-closure /
> **Response-body String lifetime across suspension** (intrinsics `reactor.rs`/`io.rs` — fully
> instrumented; the DLL read the body correctly AFTER the sleep-suspension + launched teardown,
> no UAF, no OOB read → the body String is NOT freed early), and (2) **DEF-6 `CLString`
> marshaling base-pointer** at `send_conn_pollfn` (web DLL + platform marshaling — fully
> instrumented; field reads returned correct `status`/`content-type`/`body`, ASAN saw no
> out-of-bounds read → the base-vs-payload pointer is correct). **Every Rust writer in the
> render is instrumented and clean** (`str-concat`, `int-to-string` are Rust primitives; the
> DLL `format_http_response`/`wire.into_bytes()` is Rust). **The ONLY uninstrumented writer on
> the render path is the inline JIT vec-COW/element codegen** → the residual is a **backend
> JIT-codegen store** (an out-of-bounds / stale-pointer write on the borrowed-Var two-live-vec
> COW path), surfacing ONLY under the {launched strand}×{`sleep` suspend/resume}×{`send-conn`
> DLL crossing} free-timing — NOT a Rust-layer marshaling/lifetime bug, NOT the (separately
> refuted) RC double-dec. **Owner: `/backend` (`vec_codegen.rs`), NOT intrinsics/platform.**
> Right tool for a JIT-emitted write is **valgrind** (a DBT that instruments JIT) or CLIF
> inspection (`CRANELISP_CODEGEN_TRACE=1` / `/clif` on `make-resp`/`churn`) — valgrind/gdb/rr
> are unavailable in this env (no sudo/apt). **No source changed (gate-stop); guards stay RED;
> `exemplar_web` stays `#[ignore]`'d; `0492` stays blocked; `0494` stays OPEN.** Full evidence:
> §"/dev band-A ASAN localization" at the bottom.

> ## ⚠️ CLIF GATE-STOP (2026-07-01, /dev on `cranelisp-backend`, THIRD gate — the vec-COW stale-pointer PRIME HYPOTHESIS is REFUTED by the emitted IR)
> Inspected the emitted CLIF for the two-live-vec render path (`/clif` on
> `make-resp`/`churn`/`render`/`assoc`/`conj`/`get` over a pure, no-platform reduction
> `pure.cl` that exercises the **identical** vec codegen). **The prime hypothesis — "a vec
> data-pointer loaded ONCE and reused for a later element store across a `vec-push`/`assoc`
> that can COW-REALLOC, without reloading after the realloc" — does NOT hold.** In EVERY inline
> vec op the data-pointer is loaded **fresh** (`load v+32`) immediately before the element
> load/store, inside the same basic block, and is **never** held in an SSA value across any call
> that could reallocate:
> - `vec-set` mutate path (`assoc` block2): `v11 = load v3+32` → `store v5, (v11 + idx*8)` — fresh, same block.
> - `vec-get` (`get` block2): `v13 = load v2+32` → `load (v13 + idx*8)` — fresh, same block.
> - `vec-push` fast path (`conj` block5): `v12 = load v2+32` → `store v3, (v12 + len*8)` — fresh; grow (block6) calls the extern which returns the same struct with a **reloaded** data_ptr; copy (block3) returns a new struct. No cached pointer survives a grow.
>
> `vec_push_grow` (`crates/cranelisp-intrinsics/src/vec_runtime.rs:278`) mutates the struct **in
> place** (frees old buffer, installs new, updates `data_ptr` at `+32`, returns the SAME struct)
> — and the CLIF proves the JIT reloads `data_ptr` after it, so the in-place grow is codegen-safe.
> **There is no stale-pointer store and no OOB element store in the vec-op codegen.** GATE
> triggered: no concrete defect confirmed in the IR → **no speculative fix spent** (per the
> reduce-first gate). Two further findings that RE-OPEN the localization (below): (a) the ASAN
> pass's "the only uninstrumented JIT writer on the render path is vec-COW" premise is now
> **falsified** — the vec ops are provably correct, so that elimination-to-vec-codegen collapses;
> (b) **ASAN-clean is NOT proof of a JIT write.** The bug is layout/timing-sensitive (the FIXME's
> own `MALLOC_CHECK_=3` evidence changed the failure to a reactor stall — an allocator-padding
> perturbation that closed the window); ASAN's redzones + quarantine are the SAME class of
> layout/timing perturbation and most plausibly **closed the race window**, not "couldn't see a
> JIT store." That re-opens candidates (1) Response-body/String free-timing and (2) `CLString`
> marshaling that ASAN "ruled out." **No source changed (gate-stop); guards stay RED;
> `exemplar_web` stays `#[ignore]`'d; `0492` stays blocked; `0494` stays OPEN, owner re-point
> below.** Full evidence: §"/dev band-A CLIF refutation" at the bottom.

> ## ⚠️ GATE-STOP UPDATE (2026-07-01, /dev on `cranelisp-backend`, reduce-first timebox) — the /backend-vec-RC hypothesis is REFUTED
> A disciplined reduce-first investigation (per root CLAUDE.md §cross-skill handoff + the S97
> wasted-fix warning) **confirms a NEGATIVE**: bug #2 is **NOT** a `/backend` borrowed-Var
> two-live-vec RC double-dec. No speculative backend fix was spent. Evidence + refined
> hypothesis below (§"/dev band-A investigation"). **The guards stay RED; `0494` stays OPEN;
> the owner needs re-pointing by `/arch` toward the reactor / ADT-marshaling arg-lifetime
> boundary (intrinsics + platform DEF-6 class), NOT `cranelisp-backend` RC codegen.** The
> title above is retained for provenance but its "borrowed-Var vec RC miscount" claim is
> superseded by this box.

## Context — what S98 band-A asked for

FIXME 0486 Level-1 (S98 /arch ruling) locked: bug #2's launched-effect UAF is fixed by
**runtime-owned keep-alive of the poll effect's state-closure** at the intrinsics
`EffectPoll`/`reg` seam (BC §4b invariant 15), **no backend change**. `/dev` (this crate)
was to land the fix, flip `launch_grid_corrupt` + `launch_vec_send_corrupt` green, and
un-ignore `exemplar_web`.

## What landed (correct, kept)

The invariant-15 runtime keep-alive is **implemented and correct** — the **net-zero-inc**
variant: `io::await_poll_node` takes ONE extra RC ref (`rc_inc`) on the state-closure and
hands it to the `EffectPoll`, which releases it (`consume_closure`) exactly once at resolve
(`Poll::Ready` or cancel-drop) via a new `StateClosure` RAII guard; the node's field-0 is
left untouched, so the sub-tree's own tag-4 reclamation still dec's the node's ref and the
closure is freed at the LATER of {node-release, effect-resolve} = true rc→0. This preserves
the pre-fix closure free-timing (listener/conn lifetime correct) AND holds the state-closure
live across a launched teardown. Unit-tested at the seam (2 green: `reactor::tests::
keepalive_state_closure_consumed_exactly_once_on_{ready,cancel_drop}` — exactly-once release
across suspend/resume and cancel). Release gate clean (zero new warnings). This half is DONE
and should stay.

## The finding — invariant 15 is necessary but NOT sufficient for bug #2

With the correct keep-alive landed, **both guards remain RED** (`launch_vec_send_corrupt`,
`launch_grid_corrupt` → genuine SIGABRT `free(): chunks in smallbin corrupted`, server
serves then crashes). The state-closure keep-alive does not touch the failing object.

**Root cause (measured, two independent lines of evidence):**

1. **QA Stage-1 reduction (S98, already in the fixture header):** the load-bearing floor is a
   **borrowed-Var `(Vec …)` with TWO vecs both live** across the launched render — NOT the
   marshaled `Response`/String. String body alone: 0/8. Single live vec: 0/8. **Two live
   vecs: 8/8 SIGABRT.** The vecs (`g` = `build`, `s` = `assoc`-churned) are consumed by
   `render` into the body String INSIDE `make-resp` and dropped at its `let` scope **before**
   `send-conn` even exists — so they are **not captured in the send-conn state-closure**.
   Keeping that closure alive (invariant 15) cannot keep the vecs alive.

2. **/dev A/B of both invariant-15 variants (this sprint):**
   - **net-zero-inc** (shipped): preserves free-timing → server serves correctly
     (`exemplar_web::fans_out` reliably green 3/3, ~2.1s, identical to pre-fix) → the launched
     two-live-vec render runs → **still SIGABRTs**. RC trace shows a UAF *write* to freed
     memory (heap-metadata overrun), not a clean RC underflow.
   - **move-out-with-sentinel** (arch-preferred in the 0486 note): eager-frees EVERY poll
     effect's closure on `Ready`, **including the `accept` effect's closure that captures the
     LISTENER**. Freeing it early wedges the accept loop → the server **hangs** after the
     first connection → the launched vec-render never runs enough to trip the bug → no SIGABRT
     → the guard reads "no signal" and goes **false-green**, while the real serve path
     reliably breaks (`exemplar_web` times out 3/3, 22s). This is a **hang masking the crash**,
     not a fix — precisely the "un-isolated recurring failure" trap.

So the arch-preferred variant is a false-green, and the correct variant leaves the defect. The
residual UAF is a **backend codegen RC miscount on the borrowed-Var vec path
(`ring2-rc.md §5.5`) exercised by the launched strand** — the exact retarget the S98 /qa
Stage-1 note flagged ("the failing hold is the borrowed vec, not the marshaled Response…
retargets /backend's fix toward the borrowed-Var vec RC path"), which the Level-1 ruling
noted but held "invariant 15 unchanged."

## Proposed resolution

1. **Keep** the shipped invariant-15 runtime keep-alive (net-zero-inc) — it is the faithful,
   correct runtime half of the contract and is unit-tested. BC §4b invariant 15 stands as the
   runtime contract; it is just not the whole story for bug #2.
2. **Re-scope the Level-1 "no backend change" premise.** The evidence contradicts it: the
   bug-#2 guard UAF is a `/backend` borrowed-Var two-live-vec RC miscount on the launched
   strand, not a state-closure arg-lifetime gap. `/arch` should either (a) re-point the
   Phase-5 owner of the guard-flip to `/dev`(backend, on `cranelisp-backend` codegen) with a
   fresh minimal repro, or (b) if `/arch` still believes it is runtime-shaped, name the
   specific runtime object whose lifetime is wrong (it is not the poll state-closure — proven
   above).
3. **Guards + `exemplar_web` stay as they were at S98 entry:** `launch_vec_send_corrupt` +
   `launch_grid_corrupt` RED (un-ignored defect repros, correct — the defect persists);
   `exemplar_web::serves_form` re-`#[ignore]`'d with the finding + FIXME 0486 pointer (I
   reverted the un-ignore — un-ignoring would inject a flaky RED, worse than the guarded
   ignore). `0492` (exemplar v9 adoption, blocked on bug #2) stays blocked.
4. **Minimal repro for the /backend handoff** (per root `CLAUDE.md` §"Cross-skill defect
   handoff requires minimal repro"): the two committed guards are the repro; the smaller
   `launch_vec_send_corrupt` (two live `(Vec Int)`, borrowed-Var `get`/`assoc`, launched
   `send-conn`, no ADT wrapper) is the reduction floor. A `/backend` deployment should shrink
   further toward a non-server repro (launched strand + two-live-borrowed-vec render, no
   socket) and inspect the CLIF/`CRANELISP_RC_TRACE` for the borrowed-Var vec double-dec.

## Operational implication

- Band-A does **not** deliver green guards this sprint via the intrinsics seam. The runtime
  keep-alive half is done; the guard-flip is owed to a **/backend codegen** fix (new or
  re-pointed task). `0486` should stay OPEN carrying this residual; `0492` stays blocked.
- I did not edit `design/` (per `/dev` boundary) beyond this FIXME. The `reactor.md`/
  `io-trampoline.md` invariant-15 cite-back that `/design` was to add with the fix should now
  also record that keep-alive is necessary-not-sufficient for bug #2.

## /dev band-A investigation (2026-07-01, `cranelisp-backend`, reduce-first gate — CONFIRMED-NEGATIVE)

Deployed to fix the "borrowed-Var two-live-vec RC double-dec" this FIXME names. Followed the
reduce-first gate: reduce to a CLIF-inspectable non-server repro and confirm a concrete backend
double-dec in the IR **before** editing codegen. The reduction refutes the hypothesis.

### Reproduction + baseline

- Server fixture `web_launch_vec_send_corrupt/main.cl` reproduces reliably: SIGABRT
  `free(): chunks in smallbin corrupted`. Confirmed under **`CRANELISP_NO_LENIENT=1`** too
  (single-threaded — rules out a rayon-spark data race; it is the reactor/launch path).

### Mechanism-isolation table (fixture mutations, each driven with a real HTTP request)

| Shape | Result | What it rules out |
|---|---|---|
| **Synchronous** `make-resp` (identical `get`/`assoc`/`build`/`churn`/`render` codegen) run 100× in a `--run` loop under `stdio` `print`, `CRANELISP_RC_TRACE=1` | **CLEAN** (400 703 alloc / 280 402 free, exit 0, no underflow) | The `make-resp` borrowed-Var vec RC **codegen is balanced**. The exact same compiled functions do not corrupt synchronously. |
| **Sequential** handler (no launch — handler completes before next `accept`) | **CLEAN** | Not a plain per-connection codegen bug. |
| **Launched, NO `sleep` suspension** (handler = `read-conn` → `send-conn (make-resp)`) | **CLEAN** | Launch alone is not sufficient. |
| **Launched + `sleep` suspension** (the shipped fixture) | **CRASH** | The reactor **suspend/resume of a launched strand** is load-bearing. |
| **Launched + `sleep`, two live vecs read via `get` but consumed into an `Int`, CONSTANT Response body** | **CLEAN (3/3)** | The **vec liveness / borrowed-Var reads are NOT the trigger.** |
| **Launched + `sleep`, two vecs feeding `render` → String Response body** (shipped) | **CRASH** | The load-bearing object is the **vec-sourced rendered String body flowing into `send-conn`**, on the suspended launched strand. |

### RC trace analysis (the decisive refutation)

A per-address liveness analyzer over the **crashing** RC trace (both lenient and NO_LENIENT):
**zero** `free`/`dec`/`inc` of an already-freed tracked address (no address-reuse false
positives). **There is no double-dec / free-of-live of any RC-tracked heap object.** The whole-
trace "205 pointers freed 2+ times" figure in the grid header is an **address-reuse artifact**
(alloc→free→alloc→free at the same address), not a double-free.

Corroborating: `MALLOC_CHECK_=3` **changes the failure** from smallbin-corruption to a reactor
stall ("`block_on_reactor: OneShot backstop exceeded 30s — leaf never completed`"). A clean RC
double-free would still double-free under `MALLOC_CHECK_`; a **layout-sensitive heap overrun**
gets absorbed by the check-padding — which is exactly what is observed. LIVE_ALLOCS (invariant 8
double-free debug-assert) did **not** fire, consistent with the corrupted allocation being
**untracked** (Vec **data buffers** are plain `alloc`/`dealloc`, not `alloc_with_rc`; §1.4) or
a marshaling/reactor-state buffer.

### Conclusion — confirmed-negative for `/backend` borrowed-Var vec RC

- **NOT** a backend borrowed-Var vec RC double-dec: identical codegen is clean synchronously;
  the RC accounting of tracked objects is balanced; the isolation shows vec reads are not the
  trigger (constant-body variant clean) — the trigger is the **rendered String body into
  `send-conn` on a launched+suspended strand**.
- The corruption is a **layout-sensitive heap overrun of untracked memory**, in the narrow
  window of {launched strand} × {reactor `sleep` suspend/resume} × {`send-conn` ADT/String
  marshaling to the platform DLL}. This is the **arg-lifetime-across-suspension** boundary
  (`0486` / invariant 15) — the residual is in the SAME reactor/marshaling area the keep-alive
  addresses, on the **Response/body-String** path (which IS in the `send-conn` state-closure),
  **not** the vecs (which are gone before `send-conn` exists — consistent with FIXME 0494's own
  "vecs not in the closure" observation, which is precisely why keeping the closure alive does
  not free-early the vecs: the vecs were never the freed-early object).
- **Caveat (why it is finicky):** QA measured "two heavy live STRINGS render, no vec" as CLEAN
  while "two VEC-sourced render" CRASHES. The discriminator is the exact allocation size/pattern
  (int-to-string transients + growing `acc` interleaved with two 3.2 KB vec data buffers) that
  places a victim chunk adjacent to the overrun. This is the signature of an overrun, not a
  semantic RC error, and is why determinism needs size-400 + a request burst.

### Recommendation to `/arch` (owner re-point)

Re-point the guard-flip owner **away from `cranelisp-backend` RC codegen**. The residual lives at
the reactor/marshaling arg-lifetime boundary:
1. **First suspect:** the `send-conn` state-closure / Response-body-String lifetime across the
   `sleep`→`send-conn` reactor suspension on a **launched** strand (intrinsics `reactor.rs` /
   `io.rs` — the invariant-15 area; keep-alive is necessary-not-sufficient because it covers the
   *poll* state-closure but a second object on the launched-teardown path is freed early or the
   ADT-marshal reads/writes a stale base pointer).
2. **Second suspect (DEF-6 class, `tests/CLAUDE.md` §"Heap-header integrity…"):** the
   `web/Response` ADT + body-`CLString` marshaling base-pointer/length at the host↔DLL
   `send_conn_pollfn` crossing (backend descriptor-baker and/or `exemplar/platforms/web`).
   Recommend re-running these fixtures under ASAN/valgrind (unavailable in this env: no
   gdb/valgrind installed) to pin the overrun's exact write site — that is the fastest next step
   and is what turns this refined hypothesis into a fix.

No source was changed (gate-stop). Guards `launch_grid_corrupt` + `launch_vec_send_corrupt`
stay RED; `exemplar_web` stays `#[ignore]`'d; `0492` stays blocked. `cargo check -p
cranelisp-backend` clean (no edits). `0494` stays OPEN, retargeted per the recommendation above.

## /dev band-A ASAN localization (2026-07-01, `cranelisp-intrinsics` deploy — GATE-STOP, ASAN blind to the JIT write site)

Deployed to **pin bug #2's overrun write site with ASAN** and fix the confirmed cause. ASAN
across the dlopen boundary WORKED (both artefacts instrumented) but **cannot localize this
particular overrun because the faulting store is Cranelift-JIT machine code**, not Rust. This
is a localized confirmed-negative, not a fix.

### Exact commands

```bash
# 1. Baseline (glibc) — confirm the deterministic SIGABRT + ordering
cargo build -p cranelisp -p cranelisp-web -p cranelisp-stdio
# spawn: CRANELISP_PORT=P CRANELISP_PLATFORM_PATH=target/debug CRANELISP_LIB=stdlib \
#          target/debug/cranelisp --run tests/fixtures/web_launch_vec_send_corrupt/main.cl
#   → WEBDBG=1 shows:  [WEB] send ... body_len=2184  →  [WEB] finish/close  →
#     free(): chunks in smallbin corrupted  (SIGABRT, exit 134) on the FIRST request.
#   The render + send read the Response CORRECTLY (body_len=2184); the corruption trips at a
#   free() during the launched-strand TEARDOWN, after the send completes.

# 2. ASAN build — instrument BOTH the host exe AND the dlopen'd web cdylib.
#    NB: RUSTFLAGS env REPLACES ~/.cargo/config.toml's [target.*].rustflags, so the machine-
#    local -rdynamic + mold MUST be re-added or dlsym of the statically-linked primitives
#    (e.g. `neq-string`) fails at JIT link with "can't resolve symbol".
RUSTFLAGS="-Zsanitizer=address -C link-arg=-fuse-ld=mold -C link-arg=-rdynamic" \
  cargo build --target aarch64-unknown-linux-gnu -p cranelisp -p cranelisp-web

# 3. Run the SAME fixture under ASAN (platform path → the ASAN target dir so the instrumented
#    DLL is the one dlopen'd).
export ASAN_OPTIONS="detect_leaks=0:abort_on_error=1:symbolize=1:halt_on_error=1"
ADIR=target/aarch64-unknown-linux-gnu/debug
#  spawn $ADIR/cranelisp --run main.cl with CRANELISP_PLATFORM_PATH=$ADIR, drive 8–16 GETs.
#  Also tried: quarantine_size_mb=0:redzone=16:max_redzone=16:poison_heap=1, 16 requests.
```

### What ASAN showed

- **Instrumentation confirmed real:** `nm -D $ADIR/cranelisp | grep -c asan` → **217**;
  `…/libcranelisp_web.so` → **35**. dlopen of the instrumented DLL into the instrumented exe
  loaded + ran fine (the `-rdynamic` fix cleared the `neq-string` JIT-link failure).
- **The exact deterministic crashing workload runs CLEAN under ASAN:** 9–17 requests, **zero
  ASAN reports, no crash, server survives**, every response correct (`WEBDBG`: `body_len=2184`
  per send). Same under quarantine-off + minimal-redzone + heavier load.
- **No `heap-buffer-overflow`, no `heap-use-after-free`, no bad-free** was ever emitted.

### Why ASAN is blind here (the gate-stop root cause)

`vec-get`/`vec-set`/`vec-push` compile to **inline Cranelift IR** in the common COW path
(`cranelisp-backend/src/compiler/vec_codegen.rs` — "COW inline + extern fallback"; the
`vec-set-copy`/`vec-push-copy` Rust externs in `cranelisp-intrinsics/src/vec_runtime.rs` are a
*fallback*, not the hot path). The corrupting store therefore executes as **JIT-emitted machine
code**, which ASAN's compile-time shadow instrumentation fundamentally does not cover. ASAN's
allocator (redzones + quarantine, its OWN metadata — never glibc smallbins) simply **absorbs**
the overrun that glibc reports as `free(): chunks in smallbin corrupted`, and the uninstrumented
JIT store is never shadow-checked → silence. valgrind (a dynamic binary translator that DOES
instrument JIT) is the tool that would pin it, but valgrind/gdb/rr are unavailable here (no
sudo; `apt-get` needs interactive auth).

### What this confirmed-negative BUYS (the decision ASAN was asked to make)

ASAN was to decide between candidate (1) reactor/Response-body lifetime and candidate (2) DEF-6
`CLString` marshaling base-pointer. **Both are RULED OUT as the faulting site**, because both
are fully-instrumented Rust and ASAN saw no violation in either across the crashing workload:

| Candidate | Instrumented? | ASAN verdict | Why ruled out |
|---|---|---|---|
| (1) Response-body String lifetime across suspension (`reactor.rs`/`io.rs`) | YES | no UAF, no OOB read | the DLL read `body` **correctly** (`body_len=2184`) AFTER the `sleep`-suspend + launched teardown → the body String is **not** freed early |
| (2) DEF-6 `CLString` base-vs-payload at `send_conn_pollfn` (web DLL + platform marshal) | YES | no OOB read | field reads returned correct `status`/`content-type`/`body` → the base pointer is **correct** |
| **(3) inline JIT vec-COW/element write on the borrowed-Var two-live-vec render** | **NO (JIT)** | **invisible to ASAN** | the ONLY uninstrumented writer on the render path; `str-concat`/`int-to-string`/DLL wire-format are all instrumented Rust and clean |

So the residual bug #2 is a **backend JIT-codegen store** — an out-of-bounds or stale-pointer
write on the inline borrowed-Var two-live-vec COW path (`vec_codegen.rs`) — that manifests ONLY
under the {launched strand} × {`sleep` suspend/resume} × {`send-conn` DLL crossing} free-timing
(consistent with the FIXME's "non-server render is clean; the crossing is load-bearing" and
"corrupted memory is untracked Vec data buffers"). It is NOT a Rust-layer marshaling/lifetime
bug (candidates 1 & 2 ruled out) and NOT the separately-refuted RC double-dec.

### Recommendation to `/sprint` + `/arch` (owner re-point, UNCHANGED direction but sharper)

- **Owner = `/backend`, `cranelisp-backend/src/compiler/vec_codegen.rs`** (the inline vec-COW /
  element-store codegen), NOT `cranelisp-intrinsics` (reactor) and NOT `cranelisp-platform` /
  web DLL (marshaling) — the two Rust candidates ASAN eliminated.
- **Localization tool for `/backend`:** since ASAN can't see JIT stores, use **CLIF inspection**
  — `CRANELISP_CODEGEN_TRACE=1` on the fixture (or `/clif make-resp` / `/clif churn` /
  `/clif build` in the REPL) — to read the emitted COW copy-loop bounds + the element store
  offsets against the two-live-vec borrowed-Var path, and/or provision **valgrind** in a env
  that permits it. The small `web_launch_vec_send_corrupt` fixture yields small CLIF.
- **Guards + `exemplar_web` + `0492` unchanged** (RED / `#[ignore]` / blocked). `0494` OPEN.
  No source changed; no `cranelisp-backend`/intrinsics/platform edit. `cargo check` clean.

## /dev band-A CLIF refutation (2026-07-01, `cranelisp-backend`, THIRD gate — vec-COW stale-pointer REFUTED in the IR)

Deployed to **confirm the vec-COW stale-pointer in the emitted CLIF, then fix** (per the reduce-
first gate). The CLIF **refutes** the prime hypothesis; no fix spent. This box supersedes the ASAN
box's "residual = a backend JIT-codegen store on the vec-COW path" conclusion on its central claim.

### Method

Built a pure, no-platform reduction that exercises the **identical** vec codegen as the fixture —
`get`/`assoc`/`conj` borrowed-Var wrappers over `vec-get`/`vec-set`/`vec-push`, `build`
(vec-push loop) + `churn` (vec-set on a shared Var → copy then mutate) + `render`
(two-live-vec → String), and `make-resp` binding `g`+`s` both live. Read the emitted CLIF via
`/clif` on each. (The pure synchronous form is CLEAN per the FIXME's own 100× run — this is the
same compiled code the server runs; the platform/reactor changes only free-timing, not codegen.)

### The emitted IR — every vec op reloads `data_ptr` fresh (the refutation)

| Op (fn) | CLIF (mutate/fast path) | Cached across a realloc? |
|---|---|---|
| `vec-set` mutate (`assoc` block2, rc==1) | `v11 = load v3+32` → `v14 = v11 + idx*8` → `store v5, v14` | **No** — `data_ptr` (v11) loaded fresh, used same block; no call between. Copy path (block3) = `vec-set-copy` → new struct. |
| `vec-get` (`get` block2) | `v13 = load v2+32` → `v17 = load (v13 + idx*8)` | **No** — fresh, same block. |
| `vec-push` fast (`conj` block5, rc==1, len<cap) | `v12 = load v2+32` → `store v3, (v12 + len*8)` → `len++` | **No** — fresh, same block. Grow (block6) = `vec-push-grow` extern → returns same struct with a **reloaded** data_ptr. Copy (block3) = `vec-push-copy` → new struct. |

`vec_push_grow` (`vec_runtime.rs:278`) mutates the struct **in place**: frees the old data buffer,
allocs a new one, writes the new `data_ptr` at `+32`, returns the SAME struct pointer. This is
exactly the operation the prime hypothesis feared — but the CLIF shows **the JIT reloads `data_ptr`
from `+32` after every op**, so a caller holding the struct sees the fresh buffer. There is **no
SSA value that caches a base/data pointer across a reallocating call**, hence **no stale-pointer
store and no OOB element store** in the vec-op codegen. (The `vec-set` mutate path carries no bounds
check, but `churn`'s indices `i-1 ∈ [0, len)` are all in-bounds; `vec-set` never grows.)

`make-resp` CLIF additionally shows its `let [g … s …]` compiles to **lenient-sparked IVars** (two
thunk closures forced via ivar helpers) — context, but NOT the trigger: the FIXME already recorded
`CRANELISP_NO_LENIENT=1` still SIGABRTs, so it is the sequential `make-resp` path (block3: `build`→
`churn`→`render`, with `g`/`s` dropped via `vec_drop` at make-resp return **before** `send-conn`),
not a rayon spark race.

### Two findings that RE-OPEN the localization (the elimination-to-vec-codegen collapses)

1. **The "only uninstrumented JIT writer on the render path = vec-COW" premise is falsified.** The
   ASAN box reached `/backend vec_codegen.rs` by eliminating the Rust writers and asserting vec-COW
   was the sole remaining (JIT-invisible) writer. The vec ops are now **proven correct** in the IR,
   so that elimination no longer lands on vec codegen. Other JIT writers on the path remain
   un-eliminated (scope-cleanup `vec_drop` of `g`/`s` — which frees **untracked** data buffers —
   closure-capture stores, IVar force/store), but none is a stale/OOB element store.
2. **ASAN-clean is NOT evidence of a JIT write.** The bug is **layout/timing-sensitive**: the
   FIXME's own `MALLOC_CHECK_=3` run *changed the failure* (smallbin-corruption → reactor stall) —
   an allocator-padding perturbation that closed the corruption window. ASAN's redzones +
   quarantine are the **same class** of layout/timing perturbation; the most parsimonious reading of
   "ASAN ran clean" is that ASAN **closed the same race window**, not that the faulting store is
   JIT-emitted and shadow-invisible. This directly **re-opens** the two candidates the ASAN box
   marked "ruled out": (1) Response-body/String free-timing across the launched-strand teardown,
   and (2) `CLString` marshaling base-pointer at `send_conn_pollfn`.

### What the evidence now points at (refined hypothesis)

A **free-timing use-after-free / double-free of UNTRACKED memory** (a Vec data buffer or a String
byte buffer — neither is RC-tracked, so "RC balanced" and "invariant-8 LIVE_ALLOCS silent" are both
consistent) on the **reactor launched-strand teardown**, AFTER `send-conn` completes (the DLL reads
`body_len=2184` correctly first). This is a **boundary free-ownership** defect at
`{launched strand} × {sleep suspend/resume} × {send-conn crossing}`, NOT a defect in the vec
element-store codegen. It surfaces only when the launch changes *when* an untracked buffer is freed
relative to a later write/free through a surviving reference.

### Recommendation to `/sprint` + `/arch` (owner re-point — AWAY from vec_codegen)

- **`cranelisp-backend/src/compiler/vec_codegen.rs` is cleared** as the faulting site by direct CLIF
  inspection. Re-point the guard-flip owner to the **launched-strand teardown free-ownership seam**:
  first suspect the reactor/`consume_io_tree` deep-free vs. JIT scope-cleanup double-ownership of an
  untracked buffer (`cranelisp-intrinsics` reactor/drop + the send-conn Response marshaling), with
  candidates (1)+(2) re-opened.
- **Localization that does NOT perturb heap layout** (the key lesson — ASAN/MALLOC_CHECK both hide
  it): add a **DEF-6-class heap-header-integrity `debug_assert!`** (per `tests/CLAUDE.md`
  §"Heap-header integrity…") at `free_data_buffer`/`vec_drop`/`dealloc` that validates the chunk's
  header (and a freed-sentinel to catch the second free) **before** releasing — this converts the
  threshold-delayed glibc abort into a first-crossing failure at the exact seam, **without** adding
  redzones/quarantine/padding that close the window. `rr`/`valgrind` remain unavailable here.
- **Guards + `exemplar_web` + `0492` unchanged** (RED / `#[ignore]` / blocked). `0494` OPEN, owner
  re-pointed off `cranelisp-backend`. No source changed (gate-stop); `cargo check -p
  cranelisp-backend` clean.
