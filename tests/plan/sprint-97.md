# Sprint 97 — Concurrency-track consolidation (ABI v9 + drains) — Failing-test PLAN

**Owner:** `/qa`. **Status:** PLAN ONLY — no test code yet. The failing tests land in
**Phase 5 Stage 1** (QA-first, sprint-wide, before the per-crate D/D/R cycles). This document
enumerates the row-by-row e2e surface so `/sprint` + the user can review coverage before
Phase-4 waves are allocated, and pins enough design detail (offsets, signatures, expected
RED-until-fix states) to draft each test deterministically.

> **Phase-3 exit gate (per `qa.md` §"Test plan obligation"):** by the close of this pass `/qa`
> confirms it has enough to draft the failing tests Phase 5 Stage 1 starts with — captured as
> concrete rows below — OR flags the gap where the design is still insufficient (§"Phase-3
> gaps", below). Three gaps are flagged; everything else is draftable.

---

## Scope source + contracts of record

**Scope source:** `sprints/SPRINT.md` S97 (Phase-3, entered — `/arch` Phase-2 SIGN-OFF WITH
REVISIONS) §A (the ABI v8→v9 spine, FIXME 0482), §B (folds 0469/0471 RESOLVED; 0478 co-located
decoupled), §C (independent drains: 0474, race+inline-bind, 0476, bare-submodule-reexport, 0475,
0479). The three `/design — DONE` entries under "Skill plans (Phase 3)" carry the offsets and
rulings each row pins.

**Contracts of record:**
- `design/backend/io-trampoline.md §17` (v9 poll-node emit) + **§17.5** (the FROZEN offset
  contract — the codegen↔trampoline boundary: `RESOURCE_DESC_OFFSET = 24`, poll-node `role` @
  node+32, `POLL_DESC_OUT_OFFSET` = node+40, consumed handle = `arg(0)` = `state+8`) + §17.8
  (CLIF-seam testability witnesses).
- `design/backend/ring2-rc.md §3.5.10` (0474 — option (a) deep-free; the `/qa` RC-balance
  obligation + the `/dev` intrinsics-unit mirror).
- `design/int/reactor.md §7` (v9 trampoline split/stamp/read — authoritative int statement),
  **§8** (0479 armed-ness watchdog + `drive_mode` knob), **§9** (0475 empty-`select`).
- `design/int/bind-chain-analysis.md §3.7` (0478 E1/E2/E3) + **§8.1** (the two int-seam unit
  notes).
- `design/platform/poll-support.md §3.1` (singleton stdin token) / **§3.5** (opaque
  `Connection` + slim leaf sigs) / §3.6 (the `desc_out` leaf-authoring contract).

**Spec of record:**
- `spec/10-io.md §10.12.8` (`race`/`select` + "Empty `select`" — the explicit anchor the spec
  itself owes to `/qa`: "[S96 — runtime enforcement owed (FIXME 0475 → /int); /qa to add the
  heap-typed empty-`select` repro]").
- `spec/12-runtime.md §12.7.2` (Runtime Panics — recoverable via `catch-runtime-error`) /
  §12.4.4 (combinators + cancellation; the "select over empty collection" message of record).
- `spec/10-io.md §10.12.7` (Launch-and-Continue — the 0478 E2/E3 surface).
- `spec/05-definitions.md §5.2.7` (Constructor Semantics — the 0476 standing RED).
- `spec/08-modules.md §8.11.2` (Module Resolution Search Order step 1 — the bare-submodule RED).

**ABI / spec-surface ruling (arch Phase 2):** v9 is **representation/ABI, not language
semantics** — NO new `/spec` FIXME, NO new spec section for the leaf-signature reshape. The
user-visible signature change (item 1) is therefore the one row family with **no spec-side
anchor** (Phase-3 gap G-A below). `ABI_VERSION` 8→9 + `CACHE_SCHEMA_VERSION` bump ride the one
atomic cutover change-set.

## Two-tier ownership (which rows `/qa` authors)

Per `tests/CLAUDE.md` §"Two tiers, no middle": **`/qa` authors only the e2e tier** (subprocess
`Cranelisp` builder). The unit-tier guards this plan names (intrinsics RC-balance mirror,
bind_chain_analysis int-seam units, the arg(0)-is-handle pin, the backend CLIF-seam witnesses,
the trampoline stamp/read isolations) are **`/dev`-owed**, authored alongside each crate's fix in
the same wave (`memory/feedback_unit_test_per_fix.md`). They are listed here so the Phase-3
coverage surface is complete and `/sprint` can confirm the unit complement is scheduled — `/qa`
does **not** write them.

Builder API in scope (`tests/helpers/e2e.rs`): `Cranelisp::new()` → `.run("main.cl")` /
`.repl()` / `.link("main.cl")` / `.link_then_run("main.cl")`; `.file(rel, src)`;
`.with_prelude(PreludeVariant::{None,PrimitivesOnly,TestStandard})`; `.env(k,v)`;
`.use_workspace_platforms()`; `.timeout(Duration)`; `.output()` → `.assert_exit` /
`.assert_stdout_contains` / `.assert_stderr_contains` / `.assert_stdout_does_not_contain`. RC
balance via `CRANELISP_RC_TRACE=1` + the `rc_alloc_free_counts` / `rc_leak` precedent in
`tests/concurrency_spark.rs`.

---

## Item 1 — the v9 user-visible signature change (the HEADLINE behavioral change)

The descriptor stops being a cranelisp value: leaves slim from the v8 `(read-conn token capacity
fd)` 3-arg shape to the v9 handle-only `read-conn : (Fn [Connection] (IO Request))`,
`send-conn : (Fn [Connection Response] (IO Int))`, `accept-conn : (Fn [Listener] (IO
Connection))`; `Connection` becomes `(deftype Connection [])` fully opaque
(`poll-support.md §3.5.1/§3.5.2`). All rows **NEW**, all **RED until the v9 cutover lands** (today
the v8 3-arg sig typechecks; the v9 sig does not).

| # | Test (file::fn) | Tier | spec anchor | Assertion | RED-until |
|---|---|---|---|---|---|
| 1.1 | `concurrency_v9_abi::read_conn_three_arg_shape_rejected_neg` | e2e (typecheck via `--run`) | (gap G-A) `poll-support.md §3.5.2` + `spec/10-io.md §10.12` | `(read-conn conn cap fd)` (v8 3-arg) over a `Connection` MUST be a typecheck error (arity/type) — non-zero exit + error text; `.assert_stdout_does_not_contain("internal")` | v9 cutover |
| 1.2 | `concurrency_v9_abi::read_conn_handle_only_shape_typechecks` | e2e | (gap G-A) `poll-support.md §3.5.2` | `(read-conn conn)` (1-arg) over a `Connection` MUST typecheck + compile (compile-only program; the leaf need not run) | v9 cutover |
| 1.3 | `concurrency_v9_abi::send_conn_handle_plus_response_typechecks` | e2e | (gap G-A) `poll-support.md §3.5.2` | `(send-conn conn resp)` (2-arg) typechecks; the v8 4-arg `(send-conn token cap fd resp)` is rejected (`_neg` companion in same fn or sibling) | v9 cutover |
| 1.4 | `concurrency_v9_abi::accept_conn_listener_only_typechecks` | e2e | (gap G-A) `poll-support.md §3.5.2` | `accept-conn : (Fn [Listener] (IO Connection))` — `(accept-conn listener)` typechecks; produces a `Connection` value | v9 cutover |

> **Construction note.** These are compile-only programs that import the web leaves and apply
> them at the wrong/right arity; they assert on the typecheck result, not on running the poll
> leaf, so no live server / network is needed. They DO need the web platform manifest loaded
> (`.use_workspace_platforms()` + `(platform web)` + the v9 `web.cl`/`serve.cl` modules). Phase-5
> watch: the v9 `web.cl` (`Connection []`) + `serve.cl` wrapper split is a co-landing /port +
> /platform deliverable (`poll-support.md §3.5.3`); rows 1.1–1.4 are RED-by-compile-failure
> until those modules exist, which is a valid loud signal.

## Item 2 — v9 layout / representation guards (scheduling state never rides on the value)

**ADJUSTED for the ctx-vtable model (S97 Wave-1 layout rework, 2026-06-30 — the dead
header-slot/`desc_out` model is gone).** Under the callback-vtable handle model
(`effect-concurrency.md §4.1.1`, `poll-support.md §3.5`) `Connection` is `(deftype Connection
[:primitives/Int fd])` — an **opaque ADT carrying a GENUINE `fd` field** (the platform's `r`,
read back by the platform; `r == fd`). It is **present-but-not-user-destructurable**. There is
**NO descriptor, no `RESOURCE_DESC_OFFSET` header slot, no `desc_out`, no node `(token,capacity)`/
`role`** — all scheduling state lives in the trampoline-owned `ctx` vtable, never on the value.
So the guards become: (2.1) opacity rejects a destructure even though a field exists; (2.2/2.5)
no scheduling artifact surfaces at the value/type level; (2.4) the opaque handle RC-balances like
any ordinary 1-field ADT.

| # | Test (file::fn) | Tier | spec anchor | Assertion | RED-until / state |
|---|---|---|---|---|---|
| 2.1 | `concurrency_v9_abi::connection_field_user_readable` | e2e | (gap G-A) `poll-support.md §3.5.1` / `effect-concurrency.md §4.1.1` | **INVERTED S98 band-C (FIXME 0489 / 0484):** `(deftype Connection [:primitives/Int fd])` is **tramp-opaque but USER-READABLE** — a user `(match c [(Connection fd) fd])` MUST typecheck + compile (exit 0) and yield the genuine fd. The prior `_not_user_destructurable_neg` asserted a NON-invariant (there is no ADT-level non-destructurability); it is corrected to a POSITIVE guard. Value-side "no scheduling state" negatives stay on 2.2/2.5. | GREEN (inverted) |
| 2.2 | `concurrency_v9_abi::connection_display_shows_no_descriptor_neg` | e2e | (gap G-A) `poll-support.md §3.5.1` / `effect-concurrency.md §4.1.1` | a probe of `Connection` MUST NOT surface `token`/`capacity` at the value level — cleaner under ctx-vtable (nothing scheduling-related on the value at all). KEPT; assertion now anchored to the fd-field reality. | KEPT (adjusted), RED-until v9 |
| 2.3 | `concurrency_fanout_web::web_server_fans_out_concurrent_requests_overlap` | e2e | `spec/10-io.md §10.12.7` | **EXISTING, currently GREEN** — the marquee overlap regression guard. MUST STAY GREEN through the v9 fixture reshape (opaque `Connection [fd]` + slim sigs in `tests/fixtures/web_fanout/main.cl`, rewritten by /port). Cross-ref, no new test. | existing GREEN — regression guard |
| 2.4 | `concurrency_v9_abi::produce_consume_descriptor_no_rc_leak` | e2e (RC-balance) | (gap G-A) `effect-concurrency.md §4.1.1` | RE-EXPRESSED: there is no descriptor region — over a bounded produce→consume→retire cycle, `[RC] alloc == [RC] free` under `CRANELISP_RC_TRACE=1` because the opaque handle is a normal 1-field ADT (scalar `fd`, no RC) and scheduling is ctx-owned (no value-carried region to leak). Uses the `rc_alloc_free_counts` precedent. `// FIXME(/sprint S97 W3)` G-C bounded `poll-produce`/`poll-consume` fixture (else reduces to the /dev intrinsics RC unit). | RE-EXPRESSED, RED-until v9 — **gap G-C** |
| 2.5 | `concurrency_v9_abi::connection_carries_no_scheduling_state_normal_adt_neg` | e2e | `effect-concurrency.md §4.1.1` | **NEW** (/design(int)-requested absence guard): `Connection` is a normal 1-field opaque ADT — a type probe MUST NOT surface `descriptor`/`desc_out`/`role`/`token`/`capacity` (broadened forbidden set). The value carries no scheduling state of any kind. The CLIF-internal absence (no header slot/role/desc_out/positional bake) is the `/dev`-owed backend unit below, NOT this e2e. | NEW, RED-until v9 |

> Mirror unit (`/dev`-owed, backend, `io-trampoline.md §17` / `platform-interface.md §6.8.0b` —
> ctx-vtable model): the v9 cutover is **pure subtraction** — DELETE `inject_poll_leading_pair`
> (+the `arg_vals[0..1]` peel); the poll node stays v8-uniform (NO header slot @ +24, NO `role` @
> +32, NO `desc_out` @ +40, no growth); `Connection [fd]` is an ordinary 1-field ADT
> (`FIELDS_START = 24`, normal `CLAdt::construct`); `PollFn`/`Poll`/`cranelisp-types`-codegen
> untouched; backend `public-api.txt` UNCHANGED. The **deleted-bake negative** (no positional
> `(token,capacity)` store on the node) + the **no-header-slot** assertion are CLIF-inspectable on
> a shrunk repro — this is the unit complement of e2e row 2.5's value-level face.

## Item 3 — 0474: fresh `select`/`par` continuation-node branch-Vec leak

A fresh `IO_TAG_SELECT`/`IO_TAG_PAR` node built INSIDE a bind continuation is released by the
shallow `dec_shallow_io` path, which never walks field 0 → the branch container + branch
sub-trees leak (`ring2-rc.md §3.5.10`). Option (a) deep-free fix; `/qa` owns the heap-balance
e2e guard.

| # | Test (file::fn) | Tier | spec anchor | Assertion | RED-until |
|---|---|---|---|---|---|
| 3.1 | `concurrency_fanout::fresh_select_in_continuation_rc_balanced` | e2e (RC-balance, serial) | `spec/10-io.md §10.12.8` | `(bind (Pure 0) (fn [_] (select [(Pure 1) (Pure 2)])))` — a continuation-produced fresh select with N≥2 heap branches → `[RC] alloc == [RC] free` under `CRANELISP_RC_TRACE=1` (today leaks the branch container + N branch roots) | NEW, RED-until 0474 deep-free |
| 3.2 | `concurrency_fanout::fresh_par_in_continuation_rc_balanced` | e2e (RC-balance, serial) | `spec/10-io.md §10.12.7` | the `par` analogue — `(bind (Pure 0) (fn [_] (par …)))` over N≥2 heap branches → alloc==free. Same shared-model leak (`IO_TAG_PAR`) | NEW, RED-until 0474 deep-free |

> Mirror unit (`/dev`-owed, intrinsics, `ring2-rc.md §3.5.10` / `io-trampoline.md §16.12`): build
> a tree whose continuation returns a fresh select (then par) node with N branches; after
> `cranelisp_run_io`, `(alloc − baseline) == (dealloc − baseline)` — leaks today, zero post-fix.
> **Phase-3 gap G-B:** confirm the exact `par` combinator spelling/arity at Phase-5 (the doc
> names `IO_TAG_PAR`; the source-level `par`/`par-*` form to instantiate a fresh par in a
> continuation needs the concrete prelude name — pin against `0424` dependent-binding `par-*`).

## Item 4 — 0475: `(select [])` recoverable runtime error

`(select [])` MUST raise a recoverable runtime error (`spec/10-io.md §10.12.8` "Empty `select`" /
`spec/12-runtime.md §12.7.2`) — message "select over empty collection" — catchable via
`catch-runtime-error`, fatal otherwise; NOT a synthesised `0`/Unit (unsound null at heap-typed
`a`), NOT a hang. `/dev` adds the count-zero guard in `run_select_node` (`io.rs:496-500`).

| # | Test (file::fn) | Tier | spec anchor | Assertion | RED-until |
|---|---|---|---|---|---|
| 4.1 | `concurrency_v9_select::empty_select_heap_typed_fatal_runtime_error` | e2e | `spec/10-io.md §10.12.8 (Empty select)` | an empty `(select [])` instantiated at a **heap-typed `a`** (`String`/ADT), UNcaught, under `--run` → non-zero exit + stdout/stderr contains "select over empty collection"; `.timeout(…)` bounds the no-hang requirement | NEW, RED-until 0475 guard |
| 4.2 | ~~`concurrency_v9_select::empty_select_caught_by_catch_runtime_error`~~ | — | `spec/10-io.md §10.12.8` / appendix-a §A.3 | **RETIRED S98 band-C (/spec ruling FIXME 0487 (a)):** wrong premise — an empty `(select [])` raises at effect-run time, OUTSIDE the temporal `catch-runtime-error` construction bracket, so it is **fatal, non-catchable** (not recoverable → exit 42). Deleted. Fatal-path invariants covered GREEN by 4.1/4.3/4.4. | RETIRED |
| 4.3 | `concurrency_v9_select::empty_select_heap_typed_not_unit_zero_neg` | e2e | `spec/10-io.md §10.12.8 (Empty select)` | negative: the empty-select result MUST NOT be `0`/Unit/garbage flowing downstream (asserts the unsound-null path is gone — distinct from 4.1's fatal-exit assertion) | NEW, RED-until 0475 guard |
| 4.4 | `concurrency_v9_select::empty_select_does_not_hang` | e2e | `spec/12-runtime.md §12.4.4` | a `.timeout(short)` witness that empty-select returns promptly (error), not a deadlock-hang (the "never completes is also non-conforming" clause) | NEW, RED-until 0475 guard — may fold into 4.1's timeout |

## Item 5 — 0479: idle-but-armed server `accept` survives past the old 30s cap

The wall-clock `MAX_TOTAL_BLOCK` 30s cap is replaced by a structural **armed-ness** detector
(`reactor.md §8`): an idle-but-armed `accept` (listener fd in `fd_waiters`) waits forever; a
genuinely-unarmed suspended program trips immediately. A host-side `drive_mode` knob keeps a
`OneShot` (`--run`/REPL) wall-clock backstop, disabled in `Server` mode. **Suite-time budget
(`tests/CLAUDE.md` 30s): NO real 30s wall-clock wait** — use the structural-trip witness (no
wait) + a scaled-down backstop.

| # | Test (file::fn) | Tier | spec anchor | Assertion | RED-until / state |
|---|---|---|---|---|---|
| 5.1 | `concurrency_fanout_web::idle_armed_server_survives_then_serves` | e2e | `reactor.md §8` / `spec/10-io.md §10.12.7` | a `Server`-mode fan-out server idles with NO traffic for T > the scaled OneShot backstop (e.g. backstop set ≈2s via knob, idle ≈3–4s), is THEN served one request → MUST succeed (200), proving the armed `accept` was NOT killed. The witness is "survives past where OneShot would have aborted", scaled to fit the suite budget. | NEW, RED-until 0479 + the mode/backstop knob — **Phase-3 gap G-D (time-boxing knob)** |
| 5.2 | `concurrency_v9_select::unarmed_oneshot_suspend_trips_promptly_neg` | e2e | `reactor.md §8` | a one-shot `--run` program that suspends `Pending` with NOTHING armed (no fd, no timer, no bridge, no supervisor, no parked permit) → MUST abort PROMPTLY (well under any old 30s cap, e.g. `.timeout(5s)` and assert it exited, not signaled-on-timeout) with the deadlock diagnostic. | NEW, RED-until 0479 — **Phase-3 gap G-D (source-expressibility of an unarmed-Pending program)** |

> The structural immediate-trip is unit-isolable and `/dev`-owed (`reactor.md §8.3`: "a fixture
> future that returns `Pending` with no armed interest trips the detector immediately; one that
> armed an fd does not"). If 5.2 cannot be expressed deterministically from user source (gap
> G-D), it lands as that `/dev` intrinsics unit and `/qa`'s e2e is the positive 5.1 only.

## Item 6 — 0478: single-step launch-arm E2 value-locality hardening

The single-step launch arm must run the SAME E1/E2/E3 check the sub-tree arm runs
(`bind-chain-analysis.md §3.7`). The two pinning guards are **int-seam UNIT tests, `/dev`-owed**
(`bind-chain-analysis.md §8.1`) — `/qa` does NOT author them; it records them + owns the e2e
green-guard that the hardening does not weaken the legitimate launch. Decoupled from v9 (sound
under v8+v9), NOT gated on the reshape.

| # | Test (file::fn) | Tier | spec anchor | Assertion | Owner / state |
|---|---|---|---|---|---|
| 6.1 | `bind_chain_analysis::test_launch_arm_refuses_same_token_continuation` | unit (binary crate, int seam) | `spec/10-io.md §10.12.7 (E2 value-locality)` | a discarded `ResourceSerial` step `(_ (send-conn conn r1))` whose continuation does `(send-conn conn r2)` (shared free var `conn`) MUST NOT lower to `Expr::LaunchContinue` — stays an ordinary `Bind` (E2 fails) | `/dev` (int) — RECORDED, not /qa-authored |
| 6.2 | `bind_chain_analysis::test_launch_arm_refuses_commutative_single_step` | unit (binary crate, int seam) | `spec/10-io.md §10.12.7` | a discarded `Commutative` (token-0) single step (e.g. shared-`stdout` `print`, result unused) MUST NOT launch (E3 — only `ResourceSerial` single steps are launch-eligible) | `/dev` (int) — RECORDED, not /qa-authored |
| 6.3 | `concurrency_fanout::launch_and_continue_runs_concurrently_launcher_does_not_await` | e2e | `spec/10-io.md §10.12.7` | **EXISTING, GREEN** — the legitimate accept-loop launch (handler `conn` bound inside the launched sub-tree, absent from the continuation; E2 passes) STILL fires concurrently after the hardening. Green-guard cross-ref. | existing GREEN — regression guard |

## Item 7 — the three standing REDs (existing failing-not-ignored guards that FLIP green)

No new test. These already exist as failing-not-ignored guards asserting the CORRECT behaviour;
they flip GREEN when the Phase-5 fix lands. Recorded here for the close-time flip expectation.

| Test (file::fn) | spec anchor | Resolver | Expected flip |
|---|---|---|---|
| `regression::race_with_inline_bind_lambda_branch_compiles_under_lenient` | `spec/10-io.md §10.12.8` | `/backend` (de-collide the inline-`(fn …)` lambda-name allocator: apply-arg-spark vs `race` combinator-arg, `{2 params} vs {1}`) | exit 1 (codegen error) → exit 111 |
| `regression::constructor_as_fn_value_applied_indirectly_does_not_segfault` (0476) | `spec/05-definitions.md §5.2.7` | `/backend` (constructor fn-as-value wrapper codegen, `control_flow/fn_as_value.rs`) | SIGSEGV (exit 139) → exit 7 |
| `spec_08_modules::bare_relative_submodule_reexport_resolves` | `spec/08-modules.md §8.11.2` | `/int` (`handle_export`/`handle_import` honour §8.11.2 step 1 before file fallthrough, `src/process_form/dependency.rs`) | "module 'child' not found" → exit 42 |

## Item 8 — the §7.5 watch-item (consumed handle = `arg(0)` / `state+8`)

**ADJUSTED to the ctx-vtable model.** The arg(0)-marshaling contract SURVIVES (`reactor.md §7.5`
"survivor invariant"): a Consume leaf's resource handle is its FIRST arg, marshaled at env offset
`state + 8` = `PollEnv::arg(0)`. What CHANGES: the trampoline no longer reads a descriptor off
`handle + 24` — the **platform** reads `r`/`fd` back out of the handle's own genuine field
(`CLAdt`/schema) and projects the token itself; the trampoline introspects nothing. A future
Consume sig that moved the handle off `arg(0)` would still silently break the platform's field read.

| # | Test | Tier | spec anchor | Assertion | Owner / state |
|---|---|---|---|---|---|
| 8.1 | intrinsics/platform: `consumed_handle_is_arg0_at_state_plus_8` | unit | `reactor.md §7.5` / `effect-concurrency.md §4.1.1` | a Consume leaf reads the consumed handle pointer at `state + 8` = `arg(0)`, and the **platform** reads `fd`/`r` off the handle's own field (NOT a descriptor at `handle + 24`); pins the arg(0)-is-handle contract so a handle-position reshape is caught | `/dev` — RECORDED, not /qa-authored |

> Companion `/dev`-owed trampoline/platform isolations (`reactor.md §7` ctx-vtable): Produce leaf
> at `Ready` mints the handle carrying the fresh `r` in its field (NO header stamp, NO `desc_out`);
> Consume poll-fn projects the token from the handle's `fd` field + calls `ctx.acquire(token, cap,
> waker)` itself ⇒ permit acquired on the projected token; `read-line` singleton ⇒ acquire on the
> manifest-static stdin token with NO handle read; `None`/commutative leaf ⇒ no acquire; negative:
> absence of any `inject_poll_leading_pair` positional `(token, capacity)` bake on the node.

## §8.2 same-handle ordering watch-item (`/design`(int)-flagged; Phase-5/dev-owed reshape)

`/design`(int) flagged (SPRINT.md Wave-0 /design-DONE, `reactor.md §7.7`): under the ctx-vtable
model the v8 trampoline `SerialGroup` order-restoring net **dissolves** (the trampoline no longer
sees tokens — `effect-concurrency.md §8.2`). **Within-token SOURCE ORDER now lives in the
inference** (E2 value-locality) — but only when same-token effects share the **SAME EXPLICIT
HANDLE** (a shared free var). A same-token *timing/order* pair that threads the token as a literal
arg across data-independent effects is no longer guaranteed ordered post-cutover (the permit gives
exclusion, not order).

**Disposition — one such test EXISTS in the suite, currently GREEN, must be reshaped (NOT a /qa
e2e flip; Phase-5/dev-owed):**

| Test (file::fn) | Current | §8.2 risk | Owed action |
|---|---|---|---|
| `concurrency_poll_capacity::same_token_capacity_1_poll_serial_and_source_ordered` | GREEN (v8 SerialGroup gives a<b<c) | asserts SOURCE ORDER (a<b<c) over three DATA-INDEPENDENT `log` calls sharing only a token LITERAL (`9`) — post-cutover the inference may parallelise them (exclusion via the capacity-1 permit, but NOT order) ⇒ a<b<c could break | Phase-5/dev: reshape to thread the SAME EXPLICIT HANDLE so E2 serialises them in source order (or split the exclusion assertion from the order assertion). A `WATCH(/qa S97 §8.2)` note is in-place at the test. |

> This is a GREEN guard the v9 cutover must **keep green by reshaping**, not a RED that flips. The
> exclusion half (capacity-1 serialisation, wall-clock ≈ 3·D) survives unchanged; only the *order*
> half depends on the handle-threading. /dev owns the reshape (it needs a handle-threaded poll-pool
> fixture leaf, the same G-C-class fixture dependency as 2.4). Other same-token poll-capacity rows
> (`same_token_capacity_n_poll_admits_n…`, `distinct_poll_effects_sharing_one_token…`,
> `n_distinct_token_poll…`) assert only EXCLUSION/overlap (capacity/permit semantics), NOT source
> order, so they are model-independent and carry unchanged.

---

## Phase-3 gaps (where the design is not yet enough for a deterministic `/qa` e2e)

- **G-A — no spec-side anchor for the v9 leaf-signature change (items 1, 2.1, 2.2, 2.4).** Arch
  ruled v9 is representation/ABI, not language semantics → no new `/spec` section. The slim leaf
  signatures + opaque `Connection` live only in `design/platform/poll-support.md §3.5`. The
  traceability convention + `spec_link_check.py` expect a `spec/`-or-`repl/spec.md` `// spec:`
  anchor; a `design/…` citation will read as a free-form note (skipped) or MALFORMED. **Decision
  owed (raise to `/sprint`/`/spec`):** either (i) accept a free-form `// spec: (v9 ABI) design/
  platform/poll-support.md §3.5.2` note on these rows, or (ii) `/spec` adds a thin normative
  anchor for "opaque resource handles / platform-leaf arity" so the headline change is
  spec-traceable. Does NOT block drafting the assertions — only the `// spec:` line.
- **G-B — exact `par` source spelling (item 3.2).** The doc names the runtime tag `IO_TAG_PAR`;
  the source-level form to construct a fresh par inside a continuation needs the concrete prelude
  combinator name/arity (pin against `0424` `par-*`). Resolvable by inspection at Phase-5 Stage-1;
  flagged so the row is not drafted against a guessed name.
- **G-C — deterministic bounded produce/consume RC fixture (item 2.4).** An RC-balance assertion
  over a real network server (`concurrency_fanout_web`) is non-deterministic (the server runs
  indefinitely; trace volume is unbounded). A clean descriptor-no-leak witness needs a **bounded**
  poll fixture that produces then consumes a handful of resource handles and exits — a co-landing
  `/platform` + `/dev` poll fixture (the S96 Gap-G1 "poll-pool" analogue). If that fixture does
  not land, 2.4 reduces to the `/dev` intrinsics RC-balance unit only.
- **G-D — 0479 time-boxing (items 5.1, 5.2).** Two unknowns the design defers to Phase-5 /dev: (1)
  HOW an e2e selects `Server` mode and/or scales the `OneShot` backstop down (`reactor.md §8.2`:
  "How `src/` picks the mode is a small int policy decision deferred to Phase-5 /dev"; the backstop
  value is "configurable, 30s default" with no named env/CLI knob yet) — 5.1 needs at minimum a
  CLI/env signal for `Server` + a way to set the backstop low so the witness fits the 30s suite
  budget; (2) whether an **unarmed-Pending** program (5.2) is expressible from user source
  deterministically, or only via a `/dev` intrinsics fixture leaf (`reactor.md §8.3` describes it
  as a fixture-future unit). **Resolution owed from `/dev` (int) at Phase-5 Stage-1:** name the
  mode/backstop knob; if unarmed-Pending is not source-expressible, 5.2 lands as the `/dev`
  intrinsics immediate-trip unit and `/qa` keeps only the positive 5.1.

## Up-front failing set — what Phase-5 Stage-1 (`/qa`) creates

**`/qa`-authored e2e (NEW, all failing-not-ignored, RED until the named fix):**

| Count | Rows | RED-until |
|---|---|---|
| 4 | 1.1–1.4 (v9 signature change) | v9 cutover |
| 4 | 2.1, 2.2, 2.4, 2.5 (v9 layout/representation — ADJUSTED to ctx-vtable; 2.3 is existing-GREEN regression) | v9 cutover |
| 2 | 3.1, 3.2 (0474 RC-balance) | 0474 deep-free |
| 4 | 4.1–4.4 (0475 empty-select; 4.4 may fold into 4.1) | 0475 guard |
| 2 | 5.1, 5.2 (0479; subject to gap G-D) | 0479 + knob |
| **16** | **(14 firm + 2 gap-contingent)** NEW e2e — +1 (the 2.5 absence guard added in the Wave-1 layout rework) | — |

**Existing tests cross-referenced (no new code):**
- 2 regression GREEN-guards that must STAY green through v9: `concurrency_fanout_web::
  web_server_fans_out_concurrent_requests_overlap` (2.3), `concurrency_fanout::
  launch_and_continue_runs_concurrently_launcher_does_not_await` (6.3).
- 3 standing failing-not-ignored REDs that FLIP green (item 7): `race_with_inline_bind…`,
  `constructor_as_fn_value…` (0476), `bare_relative_submodule_reexport_resolves`.

**`/dev`-owed unit guards RECORDED (not `/qa`-authored; scheduled with each crate's fix):**
0474 intrinsics RC-balance mirror; 6.1 + 6.2 bind_chain_analysis E2/E3 int-seam units; 8.1
arg(0)-is-handle intrinsics pin; the §7.6 trampoline stamp/read isolations; the §17.8 backend
CLIF-seam witnesses; the §8.3 0479 immediate-trip intrinsics unit. `/sprint` should confirm the
unit complement is allocated to the owning `/dev` waves.

## Failing-not-ignored discipline

Every NEW row above is authored **failing, un-ignored** (`memory/feedback_failing_not_ignored.md`)
— it asserts the CORRECT (post-fix) behaviour and so is RED until the owning skill lands the fix,
flipping green in the same change-set as the unit complement (`tests/CLAUDE.md` §"Unit-test-per-
fix"). A row whose API surface does not exist yet (the v9 web modules; the empty-select guard)
fails by **compile/run error** — a valid loud signal, NOT `#[ignore]`. No row is deferred to a
"test owed" follow-up FIXME. The three standing REDs (item 7) need a numbered FIXME — they already
ARE the record+trigger (`memory/feedback_no_fixme_with_failing_test.md`); 0474/0475/0479 likewise
carry their durable record as the RED guards above, not as additional FIXMEs.

## Close-time disposition (Phase 7)

At S97 close `/sprint` re-verifies each row per `tests/plan/ledger.md` §"Close-time Verification
Protocol": a row that now passes on HEAD is **Resolved** (note the flip); a still-RED row carries
forward with its owner + signature; the two GREEN regression guards (2.3, 6.3) must remain GREEN
(a RED there is a v9-reshape regression, not a known guard). The standing REDs (item 7) flip or
carry per their resolver's wave.

## Phase-5 Stage-1 realization (what /qa actually authored — 2026-06-30)

**15 failing-not-ignored e2e written, all RED on HEAD** (full suite: 1781 tests, 18 failed = these
15 + the 3 standing REDs; 2 GREEN regression guards stay green; no other regression). File
placement (matches the plan): `concurrency_v9_abi.rs` = 1.1–1.4 + 2.1, 2.2, 2.4 (7);
`concurrency_v9_select.rs` = 4.1–4.4 + 5.2 (5); `concurrency_fanout.rs` += 3.1, 3.2 (2);
`concurrency_fanout_web.rs` += 5.1 (1).

### Wave-1 layout rework (post model-pivot — ctx-vtable, 2026-06-30)

The S97 model pivoted from the descriptor cut to the **callback-vtable handle model** (FIXME 0482
DELETED; `effect-concurrency.md §4.1.1`). The 4 **signature** e2e (1.1–1.4) carry unchanged (both
models slim the sigs identically). The **3 layout** e2e in `concurrency_v9_abi.rs` were reworked to
the new reality (`Connection` is now an opaque ADT with a GENUINE `fd` field, not a zero-field
header-slot carrier), and **a 4th layout guard (2.5) was added**:

- **2.1 INVERTED (S98 band-C, FIXME 0489 / 0484)** → `connection_field_user_readable`. The S97
  `connection_opaque_field_present_but_not_user_destructurable_neg` asserted a NON-invariant: /arch
  ruled (FIXME 0484) `Connection` is **tramp-opaque but user-readable** — the trampoline never
  introspects the handle, but user code CAN destructure it (`(match c [(Connection fd) fd])`
  typechecks and yields the real fd; there is no ADT-level non-destructurability). Corrected to a
  POSITIVE guard: the user destructure MUST typecheck + compile (exit 0). GREEN.
- **2.2 KEPT** `connection_display_shows_no_descriptor_neg` — still holds, cleaner; assertion
  anchored to the fd-field reality (no `token`/`capacity` on the value).
- **2.4 RE-EXPRESSED** `produce_consume_descriptor_no_rc_leak` — no descriptor region exists; now an
  ordinary 1-field-ADT RC-balance over produce→consume→retire. Keeps `// FIXME(/sprint S97 W3)` for
  the G-C bounded `poll-produce`/`poll-consume` fixture.
- **2.5 NEW** `connection_carries_no_scheduling_state_normal_adt_neg` — the /design(int)-requested
  absence guard, e2e value/type-level face (no `descriptor`/`desc_out`/`role`/`token`/`capacity`).
  The CLIF-internal absence (no header slot/role/desc_out/positional bake) is RECORDED as the
  `/dev`-owed backend unit (Item 2 mirror), NOT forced into a weak e2e.

The shared inline `V9_WEB_CL` constant changed `(deftype Connection [])` →
`(deftype Connection [:primitives/Int fd])` — required so the signature rows also flip green
post-cutover (the rebuilt DLL's `Connection` is `[fd]`, so the module must match `[fd]`, not `[]`).
The `!contains("schema")` RED-until discriminator is unchanged (HEAD's v8 3-field DLL still
mismatches the inline 1-field module → schema gate → RED). **NEW e2e total: 16** (was 15).

**Construction realities Wave-2/3 /dev must know (the RED→GREEN contract each row pins):**

- **Items 1/2 (v9 sig/layout).** Each row drops an inline v9-shaped opaque `web.cl`
  (`Connection [fd]`) + loads the workspace `web` DLL. On HEAD the opaque 1-field module mismatches
  the v8 DLL's **3-field embedded schema** → the run dies at the schema gate (`embedded schema is
  out of date`). Positive rows assert `exit 0`; reject rows assert *non-zero AND output does NOT
  contain `"schema"`* — the `!contains("schema")` clause is the load-bearing RED-until discriminator
  (it fails on the HEAD schema-gate error, flips green when the v9 DLL rebuild makes the rejection a
  clean leaf-arity / opacity type error). So **the v9 e2e flip needs the platform DLL rebuilt opaque
  (Wave 2) AND nothing else** — they do not depend on the /port fixture rewrite. The Wave-2 DLL-mint
  blocker is **GONE** under the pivot (opaque `Connection [fd]` is a normal `CLAdt::construct`).
- **G-B RESOLVED (3.2).** There is **no surface `par`** (`spec/10-io.md §10.12.5`: auto-inserted).
  A fresh `IO_TAG_PAR` in a continuation is built deterministically by **auto-IO-Par over two
  INDEPENDENT poll effects** `(bind (Pure 0) (fn [_] (bind (poll-read 1 1 30) (fn [a] (bind
  (poll-read 2 1 30) (fn [b] (Pure (add-i64 a b))))))))`. Verified the DEPENDENT control (b uses a
  ⇒ no Par) balances 12/12 while the independent shape leaks 12/8 — isolating the imbalance to the
  par branch-Vec. 3.2 is now a **firm** row (not gap-contingent).
- **G-C (2.4) — /dev owes a bounded poll fixture.** 2.4 references absent `poll-pool` leaves
  **`poll-produce` / `poll-consume`** (a bounded produce(stamp)→consume(read) cycle that exits) —
  the S96 Gap-G1 poll-pool analogue. /dev (Wave 3) must ADD them to `platforms/poll-pool/` +
  `tests/scripts/build-link-prereqs.sh`, else 2.4 reduces to the /dev intrinsics RC unit. RED on
  HEAD = absent leaves.
- **G-D (5.1, 5.2) — /dev (int) owes the named knobs/leaf.** 5.1 is written against
  **`CRANELISP_DRIVE_MODE`** (`server`|`oneshot`) + **`CRANELISP_REACTOR_BACKSTOP_MS`** (scaled
  backstop), RED-now via a CONTRAST: a `oneshot`+2s-backstop idle server MUST die at ≈2s (on HEAD
  the knob is ignored ⇒ 30s cap ⇒ still alive at 3s ⇒ RED). 5.2 references an absent §8.3 fixture
  leaf **`poll-no-interest`** (returns `Pending` unarmed). /dev (int) Wave 3 must NAME+wire the
  knobs + provide the fixture leaf; reconcile these names when that wave lands. If unarmed-Pending
  is not surfaced, 5.2 reduces to the §8.3 /dev intrinsics immediate-trip unit (5.1 stays).
- **4.2 catch-boundary FIXME (open question for /dev int).** `catch-runtime-error` brackets only
  the PURE construction of an `IO` value (spec §A.3), but design §9 raises the empty-select error
  in `run_select_node` at TRAMPOLINE-RUN time. On HEAD the empty select under a catch is Ok-at-
  construction (exit 0, select never run). /dev (int) Wave 3 must confirm/wire how the run-time
  empty-select error reaches `catch-runtime-error` — or /dev(int)+/qa re-point 4.2. Marked
  `// FIXME(/sprint S97 W3)` in the test.

**Runtime note (suite stewardship):** the full suite is ~47s on HEAD (up from the ~9s baseline),
dominated by **(a)** 5.1's inherent idle-server witness (≈8.6s — two ~3s idles past the backstop)
and **(b)** the three empty-select SIGSEGV rows' core-dump cost (~1–3s each, RED-STATE ONLY — they
vanish the instant 0475 routes the empty select through the recoverable slot instead of the
unsound-null deref). The blow-up is temporary RED-state cost + the one production-shape server
witness; it is not a hang. Flag for /sprint awareness; revisit at close once 0475/0479 land.
