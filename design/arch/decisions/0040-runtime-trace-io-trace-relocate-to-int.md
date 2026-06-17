---
number: 0040
title: `(trace ...)` is a REPL/`--run`-only special form; `trace.rs` and `io_trace.rs` relocate to int; intrinsics keeps an `IoObserver` callback contract
status: operative
---

# 0040 — `(trace ...)` is a REPL/`--run`-only special form; `trace.rs` and `io_trace.rs` relocate to int; intrinsics keeps an `IoObserver` callback contract

> **PARTIAL-RETRACTION BOX (S76, /arch, user-decided 2026-06-04) — the `(trace ...)` half of this Decision is RETRACTED; the `io_trace` / `IoObserver` half STANDS.**
> The user decided the trace architecture afresh on 2026-06-04. The canonical target-state statement
> is now `design/arch/tracing.md` (§§1–6); this Decision is archaeology for the trace half. The
> retraction, clause by clause:
> - **RETRACTED — "`(trace ...)` is REPL/`--run`-only" + "`--link` rejects the form."** `(trace ...)`
>   now works in **all modes including `--link`** (`tracing.md` §2.5). The exe-bundle trace force-link
>   `pub use` line **returns** (it had been deleted as the D40 ladder step); spec §4.12.9's link-time
>   rejection is REPLACED with all-modes availability.
> - **RETRACTED — "the 12 `cranelisp_trace_*` bodies + registration relocate to int."** The 12 bodies
>   relocate **back to `cranelisp-intrinsics`** and publish through `intrinsics_table()` (joining the
>   catalog's as-built 29 entries — authoritative count in BC §4b inv 11 / the catalog test constant;
>   the catalog "trace deliberately ABSENT" scope text flips). `TRACE_STACK` / `TRACE_THREAD_ID` /
>   `consume_trace_call` move with them. `src/trace.rs`, `build_traced_fns`, `repl_trace_format`,
>   `TRACE_DISPLAY`, and the trace half of `int_intrinsics()` **delete** (`tracing.md` §4.3). The S76
>   `Jit::new` registration seam **dissolves for trace** (`tracing.md` §4.2).
> - **NEW (not in D40) — `trace_format` is a pure intrinsic over codegen-baked display descriptors;**
>   discovery moves into backend codegen and swaps ALL symbol tables (primitives included); nested trace
>   is disallowed via a runtime guard. See `tracing.md` §3.4 / §5 / §6.
> - **STANDS — the `io_trace` / `IoObserver` half.** The `IoObserver` callback contract in
>   `cranelisp-intrinsics::io_observer` (the ~50-line registration API) and the relocation of the
>   `io_trace.rs` ring buffer to `src/io_trace.rs` (int) remain valid and unaffected. BC §4b / §6 carry
>   that contract. This Decision's §"Intrinsics surface — the ~50-line IoObserver contract", §"Int
>   hosting — … observer state" (the io_trace ring-buffer parts only), §"Intrinsics-side deletions" (the
>   io_trace.rs ring-buffer deletion only), and the IoObserver Cross-references / Rationale remain
>   accurate as landed.
>
> Full drain of D40 into `tracing.md` + BC is a future fire; this box is the drain-consistency marker.
> The CORRECTION BOX below (the `--link` link-time-vs-compile-time note) is now moot for trace — trace
> is no longer rejected in `--link` at all — but retained for narrative continuity.

> **CORRECTION BOX (S76, /arch) — the `--link` enforcement landed at LINK TIME, not compile time.**
> This Decision's §Shape ("Product-shape constraint (Path B1)") and §Consequences still describe a
> **compile-time** rejection of `(trace ...)` in `--link` mode (frontend/typecheck emitting a
> `CompilationError`; FIXME 0199). That mechanism was **abandoned**. The landed shape (spec
> §4.12.9, finalised S68; source `crates/cranelisp-frontend/src/ast_builder.rs:1019-1028`) is
> **link-time natural missing-symbol failure**: build is mode-agnostic, backend emits the trace
> externs as `Linkage::Import` in every mode, and `--link` simply does not bundle the trace runtime
> into the exe-bundle staticlib — so the system linker errors with an undefined `cranelisp_collect_trace`.
> "**No compile-time pre-pass is required.**" The rest of this Decision (full relocation of bodies +
> registration to int, the IoObserver scope-out, the deletion ladder) is accurate as landed. The
> canonical consolidated statement is now `design/arch/tracing.md` (§2.5 mode availability;
> §4 symbols/registration; §4.4 the OPEN S76 `Jit::new` seam). This box is a drain-consistency
> correction; full drain of D40 into `tracing.md` + BC is a future fire.

`(trace ...)` is scoped as a REPL/`--run`-only special form: in `--link`
standalone-binary mode the form is rejected at compile time. With that
product constraint, `trace.rs` and `io_trace.rs` (~1700 LOC of dev-tooling
currently hosted in `cranelisp-intrinsics` post-D43) relocate in full to
`int` — bodies *and* JIT-emitted-call symbol registrations. The intrinsics
crate keeps a small (~50 LOC) `IoObserver` callback contract as the IO
trampoline's extension point for IO-state observation. `bounded-contexts.md`
§4 / §4b's exclusion of "diagnostics, tracing, observability" from
intrinsics' scope holds; the implementation drift is corrected by full
relocation under the `--link`-rejects-`(trace ...)` premise.

## Shape

### Product-shape constraint (Path B1)

> **STALE — superseded by the CORRECTION BOX at the top of this file.** The
> compile-time rejection described in this subsection was abandoned; the landed
> enforcement is link-time natural missing-symbol failure (spec §4.12.9). Read
> `design/arch/tracing.md` §2.5 for the landed shape. The paragraph below is
> retained for narrative continuity only.

`(trace ...)` is a REPL/`--run`-only special form. `--link` standalone
binary mode rejects the form at compile time — frontend (preferred per
Principle 7, early enforcement) or typecheck emits a `CompilationError`
when `(trace ...)` is encountered under the `--link` build mode flag. The
form is a syntactic distinction recognisable without type information, so
frontend is the canonical enforcement site; `/sprint` routes the
implementation FIXME to the actual owner.

Consequence: `--link` static archives carry zero trace machinery. There is
no degraded-but-defined runtime behaviour in `--link` — there is no runtime
behaviour at all, because the form never reaches codegen.

### Intrinsics surface — the ~50-line IoObserver contract

Intrinsics defines the IO observation taxonomy and registration API as an
extension point (parallel to the existing host-callback patterns):

```rust
// crates/cranelisp-intrinsics/src/io_observer.rs (~50 lines; already exists post-D43)
#[non_exhaustive] #[repr(u8)] pub enum IoEventTag { TrampolineEnter, TrampolineExit, PureStep, BindEnter, BindExit, ContPush, ContPop, PlatformEffect, ParSpark, ParSerialGroupEnter, ParJoin, ParBarrierForce }
#[non_exhaustive] pub enum IoEvent { /* payload variants */ }
pub type IoObserver = fn(IoEventTag, &IoEvent);

pub fn register_io_observer(observer: Option<IoObserver>);
pub fn emit(tag: IoEventTag, event: &IoEvent);     // relaxed-load null check + dispatch
pub fn trace_anchor() -> &'static Instant;         // shared monotonic anchor — kept here
```

The ~17 inline `io_trace::record_event(tag, payload)` calls currently in
`crates/cranelisp-intrinsics/src/io.rs` (call sites at approximately
lines 99, 104, 124, 130, 148, 184, 195, 207, 225, 238, 281, 304, 316,
422, 434, 442 plus a few — line numbers may shift; canonical hit set is
every `io_trace::record_event` call in that file) rewire to
`io_observer::emit(tag, event)`. `emit` is a relaxed-load null check + dispatch to the
registered observer. `--link` binaries pay one relaxed null-check load per
call site (one conditional branch after optimisation); zero ring-buffer or
formatter cost.

### Int hosting — the trace bodies and observer state

`int` (the `src/` binary crate) hosts:

1. **The 12 `cranelisp_trace_*` JIT-emitted-call function bodies.** Listed
   in the pre-relocation residence on `facades/intrinsics.md` §"Trace
   functions" (currently in `crates/cranelisp-intrinsics/src/trace.rs`).
   The 12 fns (`cranelisp_trace_enter`, `_exit`, `_format`, `_swap_got`,
   `_restore_got`, `cranelisp_collect_trace`, `_name`, `_params`,
   `_result`, `_children`, `_nanos`, `_first_child_nanos`) relocate body
   and `#[no_mangle]` declaration into `src/trace/` modules.

2. **Registration via the `int_intrinsics()` map.** `src/session_v4.rs`'s
   `int_intrinsics()` map (the same shape Wave 3a-γ established for
   `discover-tests`, `run-test`, and the previously-orphan
   `cranelisp_trace_format` per `src/CLAUDE.md` §"Int-owned JIT
   intrinsics") registers the 12 trace symbols at every JIT-build site —
   `JITBuilder::symbol(...)` resolves the names to the int-hosted fn ptrs
   at session init. The registration responsibility crosses the
   crate boundary from `cranelisp-backend` (per-`JITBuilder`-instance
   declaration) to `cranelisp` int (per-JIT-build-site registration via
   the int-owned symbol map).

3. **Observer state.** `src/io_trace/` absorbs the ring-buffer machinery
   that is currently in `crates/cranelisp-intrinsics/src/io_trace.rs`:
   per-thread ring buffers, env-var filter parser, panic hook,
   `flush_to_stderr`, formatter, dump, merge-sort, `record_event` body,
   `IoTracePayload` / `IoTraceTag` / `IoTraceEvent` / `FlushGuard` /
   `IO_TRACE_BUFFER_CAPACITY` const. The pre-existing observer-forwarder
   shell at `src/io_trace.rs` (which maps `IoEventTag` → `IoTraceTag`) is
   the destination's seed; the ring-buffer body joins it.

4. **Trace orchestration.** `src/trace/` absorbs the `(trace ...)`
   special-form compilation, ADT marshalling, slash-command handlers, and
   any REPL-only observer wiring. Frame stack and GOT-swap machinery live
   alongside the JIT-emitted-call bodies named in (1).

`int`'s session startup (REPL mode or `--run` with `CRANELISP_IO_TRACE=1`)
calls `intrinsics::register_io_observer(Some(int::io_trace::record))`.
Production batch (`--link`, non-trace `--run`) does not register and does
not host trace machinery.

### Backend surface — the 12 IntrinsicSymbol entries delete

`crates/cranelisp-backend/src/jit.rs:107-118` declares 12 `IntrinsicSymbol
{ ptr: cranelisp_intrinsics::trace::cranelisp_trace_* as *const u8, ... }`
entries that JIT setup hands to `JITBuilder::symbol`. Under B1, those
entries delete entirely. Backend stops contributing trace symbols to the
JIT; the registration responsibility moves to `int`'s `int_intrinsics()`
map per (2) above. Backend's `cranelisp-intrinsics` dependency persists
for the non-trace intrinsics it still names; only the 12 trace lines go.

### exe-bundle surface — the force-link `pub use` deletes

`crates/cranelisp-exe-bundle/src/lib.rs:37` carries
`pub use cranelisp_intrinsics::trace;` as a force-link incantation. Under
B1 — where `--link` rejects `(trace ...)` — the static archive
`libcranelisp_exe_bundle.a` does not need trace symbols and the
force-link line deletes. Consistent with `--link` mode rejecting the form:
exe-bundle does not carry trace symbols.

Per `sprints/SPRINT.md` Notes §"Sibling-wave breakage —
cranelisp-exe-bundle (2026-05-16)", `cranelisp-exe-bundle` is an `/int`
implementation detail; `/int` owns the edit.

### Intrinsics-side deletions

After int has hosted the bodies and registrations:

- `crates/cranelisp-intrinsics/src/trace.rs` deletes entirely (~740 LOC).
- The ring-buffer body of `crates/cranelisp-intrinsics/src/io_trace.rs`
  deletes (~952 LOC); the registration API + `IoEvent` / `IoEventTag`
  callback contract remain on `io_observer.rs` per the §"Intrinsics
  surface" subsection above.
- `consume_trace_call` (per-type drop helper for the `TraceCall` ADT
  layout, currently on the intrinsics facade) relocates with `trace::*`
  to int — the ADT layout is owned by int's `src/trace/`, and the
  consumer fn does not live anywhere else.

## Why relocation, not BC revision

The original `runtime.md` §10 framing (pre-D43) leaned BC-revision —
admit "diagnostics, observability" inside the runtime BC. That direction
reversed on the orchestration-vs-runtime-semantics distinction, and the
present Path-B1 amendment closes the same drift more completely:

- **Orchestration** is one-time setup performed by int (the GOT swap that
  installs trace wrappers). It happens once, before execution; after the
  swap, runtime is just runtime, dispatching through whatever GOT it has.
- **Runtime semantics** under B1 is what the program does once running, in
  modes where `(trace ...)` is legal (REPL, `--run`). The trace
  JIT-emitted-call bodies ARE runtime semantics for those modes — and
  they live where the orchestration lives, in `int`. The intrinsics crate
  reduces to the small `IoObserver` extension-point API.
- `--link` mode rejects the form entirely. No runtime semantics for
  `(trace ...)` exists in `--link` because the form never reaches codegen.

The BC is correct as written; the drift closes by full relocation.

## Consequences

- `(trace ...)` is rejected at compile time in `--link` mode. Spec
  impact: `spec/04-expressions.md` §4.12 gains an explicit
  `--link`-mode-rejection clause (filed as FIXME `target: /spec`).
- `crates/cranelisp-intrinsics/src/trace.rs` deletes entirely (~740 LOC).
- `crates/cranelisp-intrinsics/src/io_trace.rs` ring-buffer + formatter +
  dump + merge-sort + panic hook + env-var filter delete (~952 LOC); only
  `register_io_observer` + `emit` + the `IoEvent` / `IoEventTag` types
  remain (on `io_observer.rs`).
- `crates/cranelisp-intrinsics/src/io.rs` ~17 inline calls swap from
  `io_trace::record_event` to `io_observer::emit(tag, event)`.
- `crates/cranelisp-backend/src/jit.rs:107-118` deletes the 12
  `cranelisp_trace_*` `IntrinsicSymbol` entries.
- `crates/cranelisp-exe-bundle/src/lib.rs:37` deletes the
  `pub use cranelisp_intrinsics::trace;` force-link line.
- `src/session_v4.rs`'s `int_intrinsics()` map gains the 12
  `cranelisp_trace_*` entries (registration responsibility crosses
  from backend to int).
- `src/trace/` (new) absorbs the 12 JIT-emitted-call bodies, GOT-swap
  wrappers, frame stack, slash-command handlers, and `consume_trace_call`
  drop helper. `(trace ...)` special-form compilation + ADT marshalling
  live here.
- `src/io_trace/` (new — the existing observer-forwarder shell at
  `src/io_trace.rs` is the seed) absorbs ring buffers, panic hook,
  formatter, dump, merge-sort, env-var filter, `record_event` body, and
  the `IoTracePayload` / `IoTraceTag` / `IoTraceEvent` / `FlushGuard` /
  `IO_TRACE_BUFFER_CAPACITY` types.
- `intrinsics`'s public surface contracts to the ~50-line
  `IoObserver` extension-point API plus the unchanged trampoline +
  allocator + RC + drop-helper + vec + string + IVar + panic surfaces.
  `facades/intrinsics.md` §"IO observation" already describes the
  post-Wave-4 final shape; the §"Trace functions" and §"`io_trace::*`"
  sections (currently marked "RELOCATING TO `int` IN S67 WAVE 4") are
  what disappear at relocation close.
- `--link` binaries: zero IO-trace overhead, zero trace overhead. The
  force-link line is unnecessary because the form is unreachable.
- REPL/dev `--run`: int's startup registers the observer; trace forms
  evaluate via int-hosted JIT-emitted-call targets resolved through
  `int_intrinsics()`. User-visible behaviour unchanged.
- Net intrinsics LOC reduction: ~1700. Intrinsics focus tightens to
  backend-emitted-call targets plus the host-callback extension point.

## Cross-references

- Aligned with the existing `register_alloc_callback` host-callback
  pattern — intrinsics defines the contract, host (int) implements.
- `facades/intrinsics.md` §"IO observation" — registration API + emit
  contract; final post-Wave-4 shape.
- `facades/intrinsics.md` §"Trace functions" + §"`io_trace::*`" —
  pre-Wave-4 residence with explicit "RELOCATING TO `int`" markers.
- `facades/int.md` §"Tracing helpers — `src/trace/`" + §"Observability —
  `src/io_trace/`" — destination shapes (referenced post-Wave-4).
- `src/CLAUDE.md` §"Int-owned JIT intrinsics" — the
  `int_intrinsics()` registration pattern Wave 3a-γ established.
- Decision 43 — the `cranelisp-runtime` split into `cranelisp-primitives`
  + `cranelisp-intrinsics`; this Decision's registration-API host moved
  with that split.
- Decision 29 — IO trampoline; the trampoline is the consumer of
  `io_observer::emit`.

## Rationale

- Principle 1 (decoupling) — int's diagnostic concerns no longer drag
  intrinsics; intrinsics no longer drags backend into trace symbol
  registration.
- Principle 2 (narrow interfaces) — intrinsics' observation surface is
  ~50 lines; the trace-symbol surface contracts to zero.
- Principle 3 (dependency direction unchanged) — int → intrinsics stays
  the only edge; backend's intrinsics dependency loses the trace lines
  but persists for the rest.
- Principle 7 (single source of truth + early enforcement) —
  diagnostic state has one home, in int; `(trace ...)` rejection lives
  at the earliest point that can detect it (frontend).
- Principle 12 (design for full spec surface) — `--link` mode's
  rejection of `(trace ...)` is an explicit product surface; not an
  accidental limitation.

## Canonical location

`crates/cranelisp-intrinsics/src/io_observer.rs` (the ~50-line
extension-point contract — registration API + `emit` + `IoEvent` /
`IoEventTag`). `src/trace/` and `src/io_trace/` (new in int — the
relocated bodies, ring buffer, JIT-emitted-call targets,
`int_intrinsics()` registrations). Owner of contract: `/arch`. Owner of
relocated code: `/dev (int)` builds + registers; `/dev (intrinsics)`
deletes the local copies once int's hosting lands. `/dev (backend)`
deletes the 12 `IntrinsicSymbol` entries.

## Status pointer — Sprint 67 close

S67 close — Path B1 selected (user-arbitrated 2026-05-16, in response to
the now-deleted FIXME 0195 — `/dev (int)`'s request for /arch
reconciliation, filed against this Decision). The pre-amendment §"Shape"
read B2 (orchestration moves; bodies stay in intrinsics); the prior
§"Status pointer — Sprint 67 close" (added 2026-05-15) read B1 (full
deletion) — internally inconsistent. The above amendment reconciles to
B1 throughout, and the inconsistency-discovery FIXME (0195) is resolved
by this amendment + the cascading FIXMEs 0197–0202 (the durable record
of how 0195 closed).

B1 ladder for Wave 4 sequencing (cascading FIXMEs filed 0197–0202):

1. **/dev (intrinsics) — io.rs rewire** (FIXME 0201). ~17 inline
   `io_trace::record_event` calls in `crates/cranelisp-intrinsics/src/io.rs`
   swap to `io_observer::emit(tag, event)`. Define `emit` in
   `io_observer.rs` as the relaxed-load null check + dispatch.
   Architectural prerequisite for the io_trace ring-buffer relocation.

2. **/dev (frontend) — `--link`-mode rejection** (FIXME 0199). Reject
   `(trace ...)` in `--link` mode. Recommended at the frontend layer per
   Principle 7 (early enforcement) and because the form is a syntactic
   distinction; `/sprint` routes by canonical owner if implementation
   reasons argue typecheck instead. Spec update (FIXME 0200) lands in
   parallel.

3. **/spec — `spec/04-expressions.md` §4.12 amendment** (FIXME 0200).
   "In `--link` standalone-binary mode, `(trace ...)` is a compile-time
   error; the form is REPL/`--run`-only."

4. **/dev (int) — host trace bodies + observer state + register via
   `int_intrinsics()` + exe-bundle force-link deletion** (FIXME 0202,
   Cluster A re-fire). Now-unblocked under B1. Hosts the 12
   `cranelisp_trace_*` bodies in `src/trace/`; hosts io_trace ring buffer
   + formatter + dump + panic hook + filter in `src/io_trace/`;
   registers the 12 trace symbols via `int_intrinsics()` at JIT-build
   sites; deletes the `pub use cranelisp_intrinsics::trace;` line at
   `crates/cranelisp-exe-bundle/src/lib.rs:37`. Depends on FIXMEs 0197
   (backend deletion) and 0201 (io.rs rewire) landing first or in
   concert; depends on FIXME 0199 (frontend rejection) to make the
   exe-bundle deletion correct.

5. **/dev (backend) — delete the 12 `IntrinsicSymbol` entries** (FIXME
   0197). Backend stops contributing trace symbols to JIT; int takes
   over via `int_intrinsics()`. Lands AFTER /dev (int) hosts the trace
   bodies (sequencing dependency on FIXME 0202).

6. **/dev (intrinsics) — delete the local trace.rs + io_trace.rs
   bodies** (FIXME 0198). Depends on FIXME 0202 (int hosting) landing
   first. Removes `crates/cranelisp-intrinsics/src/trace.rs` entirely
   and the ring-buffer body of `crates/cranelisp-intrinsics/src/io_trace.rs`,
   keeping only the registration API + `IoEvent` / `IoEventTag` types on
   `io_observer.rs`.

Wave 4 deletion of `cranelisp-intrinsics::io_trace::*` and
`cranelisp-intrinsics::trace::*` (FIXMEs 0197, 0198, 0202) closes the
substantive Decision. FIXME 0103 closes alongside.
