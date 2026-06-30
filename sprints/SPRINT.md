# Sprint 97: Concurrency-track consolidation — the callback-vtable handle model + drain the S96 carry

**Status**: PHASE 5 LANGUAGE (ACTIVE) — **/arch RATIFIED the callback-vtable handle model (2026-06-30, no flaw); rescope = still S97, SMALLER spine.** Resuming with a /design re-cascade wave → /qa layout-row adjust → re-scoped Wave-2 cutover (DLL-mint blocker gone) → Wave-3 drains → Wave-4 docs/port. Scheduling state lives entirely in a tramp-owned `ctx` vtable (`acquire(token,cap,waker)`/`register_{readable,writable,timer}`/`retire`; release is tramp-owned); handles are opaque ADTs carrying a real opaque `fd` field; **no `ResourceDesc`, no header slot, no `desc_out`, no trait — `PollFn`/`Poll` unchanged**; ABI 8→9 (simpler). FIXME 0482 deleted (resolved-by-supersession). Wave-1 RED baseline `5124e1a` stands (the user-facing sig e2e carry; the layout e2e need /qa rework). Design checkpoint `60bf564`. **NOTE the title/goal below still read "descriptor cut" — superseded; the model is the §"MODEL PIVOT" Notes entry + `effect-concurrency.md §4.1.1`.**

**Goal**: Clear the concurrency track before the parallelism axis (S98) — land the ABI v8→v9 cut that makes the resource `(token, capacity)` descriptor trampoline-owned representation overhead (invisible to user source AND value shape), drain the seven open concurrency-track FIXMEs + three standing known-defect REDs, and split the user-facing concurrency documentation from a new platform-writer's guide along the same seam.

## Why this sprint, why now

The roadmap's next-scheduled increment is the parallelism/memory-contention knot (S94 floor finding — FIXME 0459 + 0408 Sudoku perf). But that is a *clean-substrate* play: it tunes the spark create-gate against a **settled** concurrency model. S96 closed having shipped the control layer + the marquee server, but **filed substantial carry** — a leaky platform ABI (scheduling metadata in user source), seven open concurrency-track FIXMEs, and three failing-not-ignored defect guards. Tuning the contention gate on top of that is tuning against a moving target. **User direction (2026-06-30): "deal with the change to the platform ABI etc. first."** S97 drains the track; parallelism (0459/0408) becomes S98.

## Scope (PHASE 1 SCOPE DRAFT — full concurrency-track drain, user-approved appetite)

### A. The spine — ABI v8→v9: descriptor as trampoline-owned representation overhead (0482)

As shipped (S96, FIXME 0465 resolution), the per-connection scheduling metadata `(token, capacity)` **leaks into user source**: `web/Connection` is `[token capacity fd]`, and `accept-conn` mints `token == fd`, `capacity == 1`, so the user literally writes `(read-conn fd 1 fd)` — one piece of real data plus two pieces of bookkeeping they neither choose nor should see. This contradicts the sprint thesis ("concurrency written by nobody").

**The v9 cut (as ruled by /arch Phase 2):** treat the resource descriptor as trampoline-owned runtime representation overhead — **like the RC/heap header**, type-invisible, not part of any ADT's logical shape — carried across the leaf boundary as a **return-side side-band**. Shape rulings:
- **Produce carrier = a `desc_out: *mut ResourceDesc` out-param on `PollFn`**, NOT a widened `Poll::Ready` struct. `Poll` stays a single-register `#[repr(i32)]` enum; the value stays on the existing `set_result` path. (The cut is about the *descriptor*, not the value — moving the value onto an `sret` struct is gratuitous churn.)
- **`role` (Produce/Consume/None) lives on the manifest `ConcurrencyDescriptor` (per-effect static), NOT on the per-value `ResourceDesc`** — "Produce" is a fact about the *leaf*, not the connection. The value header carries only the dynamic `{token, capacity}` a consume leaf needs.
- A resource-**producing** leaf (`accept-conn`) writes `desc_out`; the trampoline **stamps** `{token, capacity}` into the produced value's header side-band. A resource-**consuming** leaf (`read-conn`/`send-conn`) leaves `desc_out` unset; the trampoline **reads** the descriptor off the consumed handle before it polls (acquire-around-poll). The manifest declares each leaf's role + capacity default; the token value is the platform's internal choice.
- The backend **stops baking `(token, capacity)` from positional args** (the v8 leading-pair bake — "path-of-least-resistance wiring, not a necessity"). **`Connection` slims to fully opaque** (web recovers `fd` from `token==fd` in the header; genuine platform data, if ever needed, stays a distinct opaque ADT field, separate from the scheduling descriptor). Leaves become `read-conn : (Fn [Connection] (IO Request))`.

Completes "concurrency written by nobody" at the **value** level, not just source.

This is a serial cross-surface cascade: **/arch (rules the shape; manifests `platform-interface.md §6.8` ABI v9 + the widened `Poll`/`ResourceDesc`, `effect-concurrency.md §4.1`, BC §3/§5/§6) → /design (`poll-support.md §3.5` — slim `Connection`, leaf sigs take the handle, descriptor from manifest-role + value side-band) → /platform (per-platform leaf reshape: `web` + `stdio`) → /backend (poll-node emit: reserve header descriptor slot, emit produce/consume per manifest, stop baking from positional args) → /int (trampoline split/stamp/read)**.

### B. Folds into the v9 reshape (descriptor-model-entangled — design WITH the cut, not after)

- **0469** (/design) — `poll-support.md §3.5.3`'s "wrappers in `web.cl`" depiction is unrealizable: the platform-load pre-resolve forms a load cycle. The leaf-sig reshape touches the exact wiring; resolve the wrapper-placement question inside the v9 /design pass.
- **0471** (/design) — `read-line`'s token-0 `Commutative` descriptor does not structurally enforce single-in-flight stdin (latent gap, not a live defect). **v9 fixes this STRUCTURALLY** (an upgrade over the FIXME's doc-only resolution): a singleton resource carries a **manifest-static serial token** (`read-line : {token≠0, cardinality 1, role Consume}`) so admission enforces single-in-flight by construction.

**Co-located with /int's v9 work but DECOUPLED from the descriptor cut** (re-classed by /arch from a §B fold — it is a compile-time inference-soundness fix, sound under both v8 and v9; do NOT gate it on the reshape's schedule):

- **0478** (/int) — the single-step launch arm admits a discarded `ResourceSerial` step without the E2 value-locality check the sub-tree arm runs (latent same-token reordering; not triggered by the marquee). Fix lives in `bind_chain_analysis.rs` §4.1 hardening, next to but independent of the descriptor representation.

### C. Independent concurrency-axis defect drains (carried from S96; not ABI-entangled)

- **0474** (/backend) — a continuation-produced (fresh) `IO_TAG_SELECT`/`IO_TAG_PAR` node shallow-decs its header without walking fields → branch `Vec` + branch sub-trees leak. Apply the fix to BOTH tags (shared model). /qa guard owed.
- **race + inline-bind miscompile** (/backend; standing RED `regression::race_with_inline_bind_lambda_branch_compiles_under_lenient`) — `(race (bind (Pure 0) (fn [_] (Pure 111))) (Pure 222))` codegen-errors (lambda-name collision `{2 params} vs {1}` under lenient apply-arg sparking); `select` unaffected. `// spec: §10.12.8`.
- **0476 constructor-as-value** (/backend; standing RED) — `(let [f Some] (f 42))`-shape violates spec §5.2.7 "data constructors are functions". Standing codegen RED.
- **bare-submodule-reexport** (/int; standing RED `spec_08_modules::bare_relative_submodule_reexport_resolves`) — a bare current-module-relative submodule name in `export`/`import` skips spec §8.11.2 step 1 (`handle_export`→`resolve_module_file`). FQ path works. `// spec: §8.11.2`.
- **0475** (/int) — `(select [])` MUST raise a recoverable runtime error (§12.7.2; ruled at S96 close over unsound-null/hang). Impl site `io.rs:496-500`. /qa failing-test owed.
- **0479** (/int) — `block_on_reactor`'s 30s `MAX_TOTAL_BLOCK` watchdog aborts a legitimately-idle server `accept` loop — directly limits the marquee's production-shape goal (a server that cannot idle waiting for connections is not production-shaped). Needs a no-progress watchdog / server-mode opt-out that distinguishes a stuck leaf from a legitimately-parked `accept`.

### D. User-facing — split user-concurrency from a platform-writer's guide (/docs, Phase 6)

**User direction (2026-06-30):** separate user-concurrency from a platform writer's guide. Today `user/guide/concurrency.md` is the only doc and there is **no platform-writer's guide** in `user/` (the leaf/descriptor/manifest material lives only in internal `design/platform/`). The v9 cut is the *architectural* expression of exactly this seam — the descriptor is the platform-writer's concern and must not appear in the user's mental model — so the doc split is its user-facing payoff. Split into: (1) a **user concurrency guide** (inferred half + `race`/`select`/`timeout`/`sleep` + structured cancellation — **no descriptors/tokens/capacity**), and (2) a new **platform-writer's guide** (authoring poll-shape leaves, the produce/consume role + descriptor model, the manifest, the v9 leaf-return ABI). Sequences **after** v9 settles (it documents the v9 leaf-authoring model).

### Out of scope

- **Parallelism / memory-contention knot** → **S98**: 0459 (contention-aware spark gate — static allocation/RC-density axis) + 0408 (Sudoku perf half). Deferred deliberately — it tunes the spark gate against the now-settled substrate this sprint produces.
- **Parked (Phase H / off-track):** 0050/0052/0365 (Phase-H polish), 0407/0416/0419 (arch parked), 0430 (design docstring regen).
- **Opportunistic only (drain if slack):** 0460 (/qa set-doc honest-failure e2e).

## FIXME debt

| FIXME | Target skill | Status | Notes |
|---|---|---|---|
| 0482 | /arch | **DELETED** (superseded) | descriptor cut → superseded by the callback-vtable handle model; substance migrated `effect-concurrency.md §4.1.1` + `platform-interface.md §6.8.0b` |
| 0483 | /arch | open (Phase-7 / when invoked) | NEW — "actors+functions explicit before synthesising" principle (user-directed; filed once redesign settled). /arch authors the principle + deletes. |
| 0469 | /design | **RESOLVED + deleted** (Phase 3) | web wrappers / platform-load cycle → two-module split `web.cl`+`serve.cl`; general load-order rule recorded `poll-support.md §3.6.3` |
| 0471 | /design | **RESOLVED + deleted** (Phase 3) | serial-stdin → manifest-static singleton token `poll-support.md §3.1` (structural, strengthened over doc-only) |
| 0478 | /int | co-located, decoupled | single-step launch arm skips E2 value-locality — /int §4.1 hardening, sound under v8+v9, not gated on the descriptor cut |
| 0474 | /backend | drain (C) | fresh `select`/`par` node branch-Vec leak (both tags) |
| (RED) race+inline-bind | /backend | drain (C) | lambda-name collision under lenient apply-arg sparking |
| (RED) 0476 ctor-as-value | /backend | drain (C) | `(let [f Some] (f 42))` §5.2.7 |
| (RED) bare-submodule-reexport | /int | drain (C) | §8.11.2 step 1 skipped |
| 0475 | /int | drain (C) | `(select [])` recoverable runtime error; /qa guard owed |
| 0479 | /int | drain (C) | reactor 30s watchdog aborts idle-server accept loop |
| 0459 | /backend | **DEFER → S98** | contention-aware spark gate (parallelism axis) |
| 0408 | /port | **DEFER → S98** | Sudoku perf half (parallelism axis) |
| 0460 | /qa | opportunistic | set-doc honest-failure e2e |
| 0430 | /design | parked | docstring-into-source regen (off-track) |
| 0407/0416/0419 | /arch | parked | host-callback / bitwise / shared HostCallbacks builder |
| 0050/0052/0365 | /int·/repl·/spec | parked (Phase H) | display protocol / `/learn` / `Type.member` |

## Architecture review (Phase 2)

**Verdict: SIGN-OFF WITH REVISIONS** (`/arch`, 2026-06-30). The v9 thesis is sound and survives; three shape details adjusted, one fold re-classed. Manifested at `platform-interface.md §6.8.0b`, `effect-concurrency.md §4.1.1`, `bounded-contexts.md §3/§5/§6`, `interfaces.md` (Resource descriptor + heap-layout note). No `cranelisp-types` code edited in Phase 2 — `ResourceDesc`/`ResourceRole`/`PollFn`/`ConcurrencyDescriptor` changes are layout-breaking across every consumer and **land atomically in the v9 cutover change-set** (a standalone Phase-2 edit would red the tree). No new `/spec` FIXME (v9 is representation/ABI, not language semantics; concurrency spec cascade already filed as 0447).

**Shape ruling (confirmed with adjustments):** descriptor as trampoline-owned representation overhead; **value-header slot** storage (rejecting the pointer-keyed side table — fragile under copy/move/RC); backend stops baking from positional args; `Connection` fully opaque; inference E1–E3 unaffected and cleaner. Adjustments folded into §A above: (1) `desc_out` out-param carrier, not a widened `Poll::Ready`; (2) `role` on the manifest, not the per-value descriptor; (3) `Connection` fully opaque.

**Principle-8 interim-risk: PASS.** v9 is not an interim — it *removes* one (the v8 leading-pair positional bake). It is the descriptor model's end-state. The one forward axis (slice-4 degree/backpressure) is already carried by the inert `ConcurrencyDescriptor.global_budget` — no v9 reshape, no v10 bump. Nothing built to be discarded; the "no users" rationale (S96 v8 jump) applies identically.

**`cranelisp-types` impact (defined, lands in cutover change-set):** `ResourceDesc` (`#[repr(C)] {token:u64, capacity:u32, _pad:[u8;4]}`), `ResourceRole` (`#[repr(u8)] {None,Produce,Consume}`), `ConcurrencyDescriptor.role` (replacing one `_reserved` byte — offsets unchanged), `PollFn += desc_out`. `public-api.txt` regen for `cranelisp-types` + `cranelisp-platform` rides the same change-set.

**Fold verdict:** 0469 CONFIRM fold (caveat — the load-order *constraint* is v9-independent, record it in `poll-support.md` as a general platform-authoring rule regardless); 0471 CONFIRM fold, strengthened (structural manifest-static serial token); 0478 RE-CLASS to co-located-but-decoupled /int §4.1 hardening.

**Cascade (one atomic change-set):** arch (done) → /design (`poll-support.md` §3.1 singleton stdin token / §3.5 opaque Connection + leaf sigs + two-module wrapper split + the `desc_out` env contract) → /platform (web `accept`=Produce writes `desc_out`, `read`/`send`=Consume; stdio `read-line`=Consume singleton token) → /backend (poll-node emit: delete positional bake, reserve resource-handle header slot, allocate `desc_out` slot, per-role stamp/read hooks; `CACHE_SCHEMA_VERSION` + baseline regen) → /int (trampoline split/stamp/read; 0478 §4.1 hardening co-located-but-decoupled; `ABI_VERSION=9` loader). /qa pins the user-visible signature change + v9 layout guards up front.

## Skill plans (Phase 3)

### /design (platform) — DONE (2026-06-30)

Core v9 design pass on `design/platform/poll-support.md`: new v9 banner; **§3.1 rewritten** — `read-line` manifest-static singleton serial token `{token≠0, capacity 1, Consume}` enforcing single-in-flight by construction (resolves **0471** structurally); **§3.4/§3.2 superseded** — v8 `inject_poll_leading_pair` positional bake retired; **§3.5 rewritten** — `web/Connection` now `(deftype Connection [])` fully opaque (fd rides the header as `token==fd`), `Listener [fd pool]` stays an ordinary ADT (accept is structurally serial — **not** a resource handle, no listener token), slim sigs `accept-conn:(Fn [Listener] (IO Connection))` Produce / `read-conn:(Fn [Connection] (IO Request))` + `send-conn:(Fn [Connection Response] (IO Int))` Consume, two-module wrapper split `web.cl`(deftypes only) + `serve.cl`(wrappers) resolving the platform-load cycle (**0469**); **§3.6 new** — the `desc_out` leaf-authoring contract (role on manifest `ConcurrencyDescriptor.role`; `PollEnv::set_desc`/`desc_of`) + **§3.6.3 the general v9-independent load-order rule** (a sig-referenced `.cl` type-module cannot import its own not-yet-registered platform). **FIXMEs 0469 + 0471 resolved + `git rm`'d.**

Seams handed downstream: /design (backend) — poll-node emit reserves the fixed-offset `ResourceDesc` header slot, allocates the `desc_out` slot, deletes the positional bake, emits per-role stamp/read hooks; /design (int) — trampoline split (Produce reads `*desc_out`→stamp header; Consume reads consumed handle's header pre-poll) + singleton-token acquire for `read-line` + 0478 §4.1 hardening (co-located, decoupled). Phase-5 watch items: empty-bodied `Connection [] ` marshalling through `CLAdt`/schema; `web.platform-schema` regen.

### /design (backend) — DONE (2026-06-30)

`io-trampoline.md §17` (v9 poll-node emit) + `ring2-rc.md §3.5.10` (0474 ruling). **Emit:** resource-handle ADTs get a 16-byte `ResourceDesc` region at **fixed offset 24** (`RESOURCE_DESC_OFFSET`, uniform → trampoline reads with no per-ADT knowledge; logical fields shift to 40; empty `Connection []`→40-byte object); poll-node grows 48→56, baking `role` (node+32, from manifest `ConcurrencyDescriptor.role`) + the `desc_out` region (node+40); **`inject_poll_leading_pair` + the `arg_vals[0..1]` peel DELETED** (leaf args are `arg_vals[0..]` directly); per-role bake (Produce zero-init / Consume manifest-static `{token,capacity}`, token≠0 ⇒ singleton / None zero). In-process node convention → no `cranelisp-types`/`public-api` touch, only `CACHE_SCHEMA_VERSION`. **Boundary contract (§17.5, frozen offset table):** backend owns slot reservation + `role`/`desc_out` bake + bake-deletion + the manifest-derived resource-handle type set; trampoline owns reading `role` (node+32) + runtime stamp/read/acquire (passes node+40 as `desc_out`; consumed handle = `arg(0)` at `state+8`). **0474 → option (a):** `dec_shallow_io` becomes shape-aware for `IO_TAG_PAR`/`IO_TAG_SELECT`, deep-frees the branch container (reuses `consume_io_tree`'s branch arm — single source), spine tags stay shallow (Principle 7, smaller blast radius than routing-through-consume). 0474 left **open** (Phase-5 /qa guard + /dev fix). **Watch items:** (1) resource-handle type set must be available at ADT-layout time from loaded manifests — if a cross-crate interface is needed, /dev STOPs + files /arch; (2) empty `Connection []` marshalling through `CLAdt`/`web.platform-schema` must not treat the descriptor region as a logical field. Minor: `interfaces.md` heap-layout note doesn't pin the concrete offset (backend pinned 24; optional one-line /arch follow-up — backend owns the layout decision, no FIXME filed).

### /design (int) — DONE (2026-06-30)

`reactor.md` §7 (v9 trampoline split/stamp/read — authoritative int statement), §8 (0479 watchdog), §9 (0475); `bind-chain-analysis.md §3.7` (0478); `io-integration.md §I3` (ABI v9 loader). **Trampoline (§7):** `await_poll_node` reads baked `role` once at node+32 → **Produce**: forward node+40 as `desc_out`, on `Ready` stamp `*(node+40)` into produced value's header at value+24, hand bare value on (value + descriptor = two independent writes; `Poll` single-register); **Consume**: read node's baked desc (node+40), if `token==0` read consumed handle's header (`arg(0)` at `state+8` → `handle+24`), acquire BEFORE first poll, RAII release unchanged; **None**: poll, leaf ignores `desc_out`. The §2.9 acquire-around-poll lifecycle byte-for-byte unchanged — only *where* `(token,capacity)` comes from moves. **Singleton `read-line` (§7.5):** Consume w/ manifest-static `{STDIN_TOKEN≠0,1}`, `token≠0` branch acquires the static token directly, no handle read — single-in-flight by construction. **0479 → armed-ness deadlock detector** (reject the per-leaf descriptor flag): replace wall-clock `MAX_TOTAL_BLOCK` with a structural trip — only when reactor unarmed (`fd_waiters` ∅ ∧ `timer_heap` ∅ ∧ `pending_bridges==0` ∧ supervisor ∅ ∧ no parked permit) — caught immediately, not after 30s; idle-armed `accept` (listener fd in `fd_waiters`) waits forever → production-shaped (generalizes §2.6/§2.12 exemptions, Principle 7). Plus a host-side `drive_mode` knob (`OneShot` default keeps a `--run`/REPL backstop; `Server` disables it) — **no ABI/`cranelisp-types` touch**. **0478 → E1/E2/E3 predicate**: single-step arm now runs the sub-tree arm's checks; **E2 value-locality** `free_vars(io_expr) ∩ free_vars(cont) == ∅` refuses a discarded `ResourceSerial` step sharing a handle with a same-token continuation; E3 tightened `!= Sequential` → **`ResourceSerial` only**; compile-time soundness fix, **sound under v8+v9, NOT gated on v9**. **0475 → degenerate branch-count guard** in `run_select_node` (`io.rs:496-500`) raises "select over empty collection" through the standard runtime-error slot (recoverable at `catch-runtime-error`); /dev fix, /qa owns heap-typed-`a` e2e. **Watch item (§7.3):** consumed handle = `arg(0)`/`state+8` is load-bearing — a future Consume sig moving the handle off arg(0) breaks it; Phase-5 unit guard owed. **bare-submodule-reexport** (/dev note, no deep pass): `handle_export`→`resolve_module_file` must apply §8.11.2 step-1 current-module-relative resolution (symmetric with `handle_import`) before the search-order fallthrough.

### /qa — DONE (2026-06-30)

`tests/plan/sprint-97.md` written (planning doc; tests are Phase-5 Stage-1). **15 new failing-not-ignored e2e** (13 firm + 2 gap-contingent): 4 v9 sig change (old 3-arg `(read-conn fd 1 fd)` rejected / new handle-only typechecks; read/send/accept-conn) · 3 v9 layout (opaque `Connection []` zero-field destructure rejected; descriptor invisible in display; descriptor-region RC no-leak) · 2 × 0474 fresh select/par-in-continuation RC-balance · 4 × 0475 empty-`select` (fatal/catchable/not-Unit-0/no-hang) · 2 × 0479 (idle-armed survives / unarmed trips promptly). **Cross-referenced (no new code):** 2 GREEN regression guards that must stay green through the reshape (`web_server_fans_out…overlap`, `launch_and_continue…does_not_await`); 3 standing REDs that FLIP (race+inline-bind, 0476, bare-reexport). **/dev-owed unit guards recorded** (scheduled with each fix, per two-tier strategy): 0474 intrinsics RC mirror; 0478 two `bind_chain_analysis` E2/E3 seam units (§8.1); §7.3 `arg(0)=state+8` pin; §7.6 stamp/read isolations; §17.8 backend CLIF witnesses; §8.3 0479 immediate-trip. New files `concurrency_v9_abi.rs` / `concurrency_v9_select.rs` + additions to `concurrency_fanout{,_web}.rs`. `ledger.md` untouched (Phase-5/close-time update).

**Phase-3 gaps + dispositions:**
- **G-A (v9 sig has no spec anchor)** — RESOLVED by /sprint: v9 is representation/ABI (arch-ruled, no `/spec` change). Tests anchor to `design/platform/poll-support.md §3.5` + `design/arch/platform-interface.md §6.8.0b` — consistent with existing concurrency tests citing `effect-concurrency.md` in `// spec:`. No `/spec` involvement.
- **G-B** (par combinator spelling/arity) — resolve by inspection at Stage-1.
- **G-C** (bounded produce/consume poll fixture for deterministic RC) — falls back to the /dev intrinsics RC unit if no bounded e2e fixture.
- **G-D (0479 time-boxing)** — Phase-5 /dev must expose the `Server`-mode selector + a scaled-down `OneShot` backstop (no real 30s wait; e2e uses ≈2s backstop + ≈3–4s idle) and decide whether an unarmed-`Pending` program is source-expressible or needs a /dev fixture leaf (else 5.2 falls back to the §8.3 immediate-trip unit). Carried into Phase-5 /dev (int).

**Phase 3 exit gate MET:** /arch public-API + interface set complete (Phase 2); /qa has enough to draft failing tests (this plan; gaps dispositioned); touched design docs current (platform/backend/int all DONE).

## Waves (Phase 4 — RESCOPED 2026-06-30 after the model pivot)

**The pivot makes the spine SMALLER.** The cutover is still ONE atomic change-set (the `cranelisp-types` ABI bump reds the tree until consumers catch up), but it's now mostly *deletion*: backend just removes `inject_poll_leading_pair`; `PollFn`/`Poll` unchanged; int trades the descriptor stamp/read for a permit-map it largely has via §8.1. The Wave-2 DLL-mint blocker is **gone** (opaque `Connection` now carries a real `fd` field → normal `CLAdt::construct`). Independent defect drains are unchanged. Worktree isolation broken → source-touching waves run **serially**.

### Wave 0 — /design re-cascade (NEW; text-only, may fan out read-style)

The three /design DONE entries were written to the dead descriptor model. Re-cascade to the ctx-vtable model per `/arch`'s map:
| Skill | Doc | Task | Status |
|---|---|---|---|
| /design (platform) | `poll-support.md §3.1/3.5/3.6` | poll-fn skeleton (`acquire→syscall→register?`/Ready) via ctx; DELETE the `desc_out` env contract + header-slot depiction; `Connection` opaque **`fd` field** holds `r`. CARRY: web.cl/serve.cl split (0469), load-order rule §3.6.3, singleton stdin token (0471). | pending |
| /design (backend) | `io-trampoline.md §17` | **uniform** poll node; the ONLY delta is DELETING `inject_poll_leading_pair` + the positional peel (no header slot, no role bake, no desc_out). `ring2-rc.md §3.5.10` (0474) stands. | pending |
| /design (int) | `reactor.md §7` | host implements ctx `acquire`/`retire` (the §8.1 permit map) + **tramp-owned release** on Ready/cancel keyed by effect identity; no role-split/stamp/read. §8 (0479) + §9 (0475) stand. Also §8.2: within-token ordering home moves to inference (E2/E3) — the dissolved `SerialGroup`. | pending |

### Wave 1 — QA-first — DONE + needs a layout-row adjust

| Skill | Crate | Task | Status |
|---|---|---|---|
| /qa | tests/ | **Carries:** the user-facing **signature** e2e (opaque `Connection`, `(read-conn conn)` 1-arg typechecks, old 3-arg rejected) — both models slim the sigs identically. **Needs rework:** the 3 **layout** e2e written to the header-slot model — `Connection` now has a *real* opaque `fd` field, so "zero-field destructure rejected" → "opaque field present but not user-destructurable"; "descriptor invisible in display" still holds (cleaner — nothing on the value); "descriptor-region RC no-leak" → ordinary ADT-field RC. | DONE → adjust |

### Wave 2 — the atomic cutover (re-scoped; critical path)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | types+platform+backend+int | `cranelisp-types`: DELETE `ResourceDesc`/`PollFn.desc_out`/the trait; ADD `ResourceRole{None,Produce,Consume,Retire}`, `Acquire{Acquired,Parked}`, `ConcurrencyDescriptor.role` (one reserved byte, offsets unchanged), `HostCtx.{acquire,retire}` fn-ptrs; regen `public-api.txt` ×2. platform: ctx-vtable poll-fn skeleton + opaque-`fd`-field `Connection` + web.cl/serve.cl split + singleton stdin token. backend: **DELETE `inject_poll_leading_pair`** + positional peel; `CACHE_SCHEMA_VERSION` bump. int: host impl of ctx `acquire`/`retire` + tramp-owned release (effect-identity keyed) + `ABI_VERSION=9` loader. Flips the sig+(adjusted)layout e2e GREEN; keeps the 2 regression guards GREEN. + 0478 (decoupled, lands here or W3). | pending |
| /review | (cross-crate) | review vs the ctx-vtable contract + `/arch` rulings; baseline diffs present. | pending |

### Wave 3 — independent defect drains (serial; model-independent — unchanged)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | cranelisp-backend | 0474 deep-free (a) both tags; race+inline-bind; 0476 ctor-as-value. + unit mirrors. /review. | pending |
| /dev | src/ (int) | 0475 empty-`select` runtime-error; 0479 armed-ness detector + `drive_mode` knob (G-D Server-mode selector + scaled backstop); 0478 E1/E2/E3 (if not in W2); bare-submodule-reexport §8.11.2 step-1. /review. | pending |

### Wave 4 — Phase 6 (user-facing; unchanged, docs now CLEANER)

| Skill | Surface | Task | Status |
|---|---|---|---|
| /docs | user/ | Split `concurrency.md` → user concurrency guide (NO scheduling internals) + NEW platform-writer's guide (the ctx-vtable poll-fn skeleton — `acquire`/`register`/`retire`, the four leaf roles — *not* a descriptor ABI). | pending |
| /port | exemplar/ | Adopt the handle model: opaque `Connection`, slim leaf calls, web.cl/serve.cl. Replay marquee fan-out green. | pending |
| /repl·/stdlib·/examples | — | 6a assessment + replay prior demos green. | pending |

---
**Superseded (kept for record):** the original single-wave "v9 atomic cutover" plan below + the three /design-DONE entries' descriptor specifics. The model is `effect-concurrency.md §4.1.1`; the re-cascade is Wave 0 above.

### [SUPERSEDED] Original Phase-4 waves (descriptor cut)

### Wave 1 — QA-first (Phase 5 Stage 1)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /qa | tests/ | Write the 15 failing-not-ignored e2e per `tests/plan/sprint-97.md`. **DONE** — `concurrency_v9_abi.rs` (7) + `concurrency_v9_select.rs` (5) + `concurrency_fanout.rs` (+2, 0474) + `concurrency_fanout_web.rs` (+1, 0479 idle-server). **1781 tests / 18 RED = 15 new + 3 standing; 2 guards GREEN; no regression.** 4 `FIXME(/sprint S97 W3)` for /dev-owed interfaces: `CRANELISP_DRIVE_MODE`+`CRANELISP_REACTOR_BACKSTOP_MS` (0479 5.1), `poll-no-interest` fixture leaf (0479 5.2 unarmed), `poll-produce`/`poll-consume` bounded leaves (2.4 RC-leak, G-C), and the 0475 catch-boundary question (§9 raises at trampoline-run — is it inside `catch-runtime-error`'s bracket?). Process: suite ~47s in RED state (idle witness ~8.6s + empty-select SIGSEGV dumps; collapses when 0475/0479 land). | DONE |

### Wave 2 — the v9 atomic cutover (critical path; lands first)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | types+platform+backend+int | The atomic v9 cutover: `cranelisp-types` (`ResourceDesc`/`ResourceRole`/`ConcurrencyDescriptor.role`/`PollFn += desc_out` + `public-api.txt` regen ×2); platform (web `accept`=Produce writes `desc_out`, `read`/`send`=Consume opaque `Connection []`, two-module `web.cl`/`serve.cl` split, stdio `read-line` singleton token; `web.platform-schema` regen); backend (header slot @24, poll-node `role`@32 + `desc_out`@40, delete `inject_poll_leading_pair`, per-role hooks, `CACHE_SCHEMA_VERSION` bump); int (trampoline split/stamp/read §7, `ABI_VERSION=9` loader). Flips the 7 v9 e2e (sig + layout) green; keeps the 2 regression guards green. Unit guards: §7.6 stamp/read, §17.8 CLIF, §7.3 `arg(0)` pin. | pending |
| /review | (cross-crate) | Change-set review vs the §17.5 boundary contract + arch v9 rulings; baseline diffs present. | pending |

### Wave 3 — independent defect drains (serial; after the cutover)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | cranelisp-backend | 0474 deep-free option (a) (both tags) → flips 0474 RC guards; race+inline-bind lambda-name collision → flips that RED; 0476 ctor-as-value → flips that RED. + unit mirrors. /review. | pending |
| /dev | src/ (int) | 0475 empty-`select` runtime-error guard → flips 0475 e2e; 0479 armed-ness detector + `drive_mode` knob (resolve G-D Server-mode selector + scaled backstop) → flips 0479 e2e; 0478 E1/E2/E3 hardening + §8.1 units; bare-submodule-reexport §8.11.2 step-1 → flips that RED. /review. | pending |

### Wave 4 — Phase 6 (user-facing; after v9 settles)

| Skill | Surface | Task | Status |
|---|---|---|---|
| /docs | user/ | **Split `concurrency.md`** → user concurrency guide (inferred half + `race`/`select`/`timeout`/`sleep` + cancellation, NO descriptors) + NEW platform-writer's guide (poll-shape leaves, produce/consume roles, descriptor model, manifest, v9 leaf-return ABI). | pending |
| /port | exemplar/ | Adopt v9: opaque `Connection`, slim leaf calls, two-module `web.cl`/`serve.cl`. Replay marquee fan-out green. | pending |
| /repl·/stdlib·/examples | — | 6a assessment of v9 + the drains against spec; replay prior demos green. | pending |

## Notes

- 2026-06-30 — **/arch RATIFIED the callback-vtable model (no flaw found) + manifested + rescoped.** Refinements: `acquire(token,cap,waker)` (waker added so `Parked`→re-enqueue), discrete `register_{readable,writable,timer}`, `role` compile-time-only, discrete fns affirmed over a bundled `schedule(intent)`. **Load-bearing consequence ruled:** the v8 `SerialGroup` order-restoring safety net **dissolves** (tramp no longer sees tokens) → within-token source ordering's home **moves to the inference** (E2 value-provenance + E3 cover the promised-order cases); `effect-concurrency.md §8.2`. Rulings (a)–(f) all PASS: establishment-phase token clean (Produce drives acquire/register on the fresh `r`, handle materializes at Ready); release tramp-owned on Ready/cancel keyed by effect identity; retire idempotent; full-duplex = distinct per-direction tokens (no manifest field); cross-resource co-serialization exclusion-form still expressible (ordered-form deferred per 0482, an advanced API); no acquire/reactor-thread deadlock (Parked returns immediately, §8.1 counter). **0482 DELETED** (substance → `effect-concurrency.md §4.1.1` + `platform-interface.md §6.8.0b`). Arch docs changed: `effect-concurrency.md` (§4.1.1 rewrite, §8.1 banner, §8.2 rewrite), `platform-interface.md §6.8.0b` (ctx-vtable ABI), `bounded-contexts.md §3/§5/§6`, `interfaces.md`. **No /spec FIXME** (representation/ABI; concurrency-semantics cascade remains 0447). **Pending /arch principle filing NOW DONE → FIXME 0483 filed** (redesign settled).
- 2026-06-30 — **PENDING /arch principle filing (user-directed, file once the redesign settles).** → **ACTIONED: FIXME 0483 filed** (`design/arch/fixmes/0483-arch-actors-functions-explicit-before-synthesis.md`). Add an `/arch` principle: **make the actors + the functions/contracts between them explicit BEFORE synthesising a mechanism** — the precondition for a solution that is faithful (maps the real interaction structure), simple (minimal mechanism becomes visible), and innovative (better/general designs only become *seeable* once actors+calls are laid bare). Trigger smell: a design arriving **pre-framed across multiple incremental FIXMEs** (0465→0482) — challenge the *premise*, not just the shape; run a first-principles / actor-model / "what would unix do" pass before ratifying. Origin: the S97 descriptor cut was a mechanism synthesised from an inherited frame with no actor model; the 3-column program/tramp/platform table + the calls/returns/callbacks is what surfaced the simple model. Captured in `memory/feedback_actors_functions_before_synthesis.md`. **Do NOT file the FIXME yet — wait for the /arch redesign to land (avoid churn on docs in flight).**
- 2026-06-30 — **MODEL PIVOT (user-ratified) — callback-vtable handle model supersedes the descriptor cut.** Worked through with the user from the Wave-2 STOP. Core: scheduling state (`token`/`capacity`) NEVER rides on user values — it flows through a tramp-owned `ctx` vtable the platform calls. **Vtable:** `acquire(token, cap)→Acquired|Parked`, `register(source, interest, waker)`, `retire(token)`, + the existing `waker` (the model is the waker *generalized*). **Release is tramp-owned** (on poll `Ready` or cancel — cancel never re-enters the poll fn), not a callback. **Handles are opaque ADTs** carrying only genuine data (the platform's `r` lives in the handle's own field + the platform's hands; tramp never introspects). **Poll-fn skeleton (uniform):** `acquire → syscall → (would-block? register + Pending : Ready)`; commutative leaf omits acquire; one-shot `sleep` = degenerate (no handle, just `register(timer)`). **Token = derived scheduling projection of the handle** (default per-resource = `r`; split per-direction for full-duplex; `0` commutative), recomputed not remembered → no separate scoreboard (the reactor interest table IS it). **Layering split:** manifest = compile-time facts (poll-shape? role? capacity? — for inference E1–E3 + codegen); `ctx` = ALL runtime scheduling. **Deletes** `ResourceDesc`/header-slot/`desc_out`/the `AsRawFd`-style trait entirely + dissolves the Wave-2 DLL-mint blocker (no slot to reserve). Unix/rust-stdlib aligned (fd + `accept→(stream,addr)` + Drop/`close`-retires). **User prefers DISCRETE vtable fns over a bundled `schedule(intent)` data object (open to persuasion).** Supersedes FIXME 0482 + the Phase-2 value-header ruling + the §17/§7/§3.5-3.6 descriptor cascade. → /arch to ratify, pressure-test, re-cascade, and rescope S97.
- 2026-06-30 — **Wave 2 STOP (design gap, no edits — tree clean/green).** The v9 produce-stamp needs a produced opaque `Connection []` to be a 40-byte object (header 16 + tag 8 + 16-byte desc slot@24), but `accept-conn` mints it inside the DLL via `CLAdt::construct`→`alloc_with_tag(tag, field_count=0)` → a **24-byte** object; stamping at `value+24` overruns by 16 (DEF-6/Risk-11 heap corruption). The `alloc_with_tag` ABI + platform schema carry **no resource-handle identity** — slot reservation for a zero-logical-field handle at the DLL-mint→host-alloc boundary is **undesigned** (v9 designed the descriptor *shapes*, not this allocation seam; §17.7/§3.5.7's "confirm `CLAdt::construct` emits 40 bytes" is a new interface, not a confirmation). Compile-only v9 tests would pass but the `web_server…overlap` guard runs a real `accept→read→send` and would corrupt → no clean partial for an atomic change-set. **Routed to /arch** to rule the slot-reservation seam (candidates: schema resource-handle bit consulted by `CLAdt::construct` / resource-handle-aware host alloc callback / `accept-conn` mints via backend-emitted constructor). Rest of cutover traced + ready; resumes once /arch rules. Also noted: `_reserved`@17 unit test `scheduling.rs:386` must update; `tests/fixtures/web_fanout/*` still v8-shaped, must move to v9 with the guard.
- 2026-06-30 — S97 opened. S96 SPRINT.md archived to `sprints/archive/sprint-96.md` (was committed/closed at `e981ead` but never moved). Scope = full concurrency-track drain (user-approved appetite) + the /docs user/platform-writer split (user direction). Parallelism axis (0459/0408) deferred to S98.

## Outcome (Phase 7)

{Pending.}
