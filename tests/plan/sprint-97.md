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

## Item 2 — v9 layout / representation guards (descriptor is type-invisible)

The descriptor rides a fixed header slot (`RESOURCE_DESC_OFFSET = 24`), NOT a logical field — it
must not appear in the value's logical shape / field count / display, and must not leak RC.

| # | Test (file::fn) | Tier | spec anchor | Assertion | RED-until / state |
|---|---|---|---|---|---|
| 2.1 | `concurrency_v9_abi::connection_is_opaque_zero_fields_destructure_rejected_neg` | e2e | (gap G-A) `poll-support.md §3.5.1` | `(deftype Connection [])` has ZERO logical fields → a destructure/match `[(Connection a b c)]` MUST be a wrong-field-count error (the descriptor is invisible to the pattern); the v8 `(Connection token capacity fd)` 3-field destructure no longer typechecks | NEW, RED-until v9 |
| 2.2 | `concurrency_v9_abi::connection_display_shows_no_descriptor_neg` | e2e | (gap G-A) `poll-support.md §3.5.1` | a produced `Connection`'s display/value-shape MUST NOT surface `token`/`capacity`/a descriptor field (negative-coverage: descriptor invisible at the value level) | NEW, RED-until v9 |
| 2.3 | `concurrency_fanout_web::web_server_fans_out_concurrent_requests_overlap` | e2e | `spec/10-io.md §10.12.7` | **EXISTING, currently GREEN** — the marquee overlap regression guard. MUST STAY GREEN through the v9 fixture reshape (opaque `Connection` + slim sigs in `tests/fixtures/web_fanout/main.cl`, rewritten by /port). Cross-ref, no new test. | existing GREEN — regression guard |
| 2.4 | `concurrency_v9_abi::produce_consume_descriptor_no_rc_leak` | e2e (RC-balance) | (gap G-A) `io-trampoline.md §17.2` / `reactor.md §7.6` | over a bounded produce(stamp)→consume(read) cycle, `[RC] alloc == [RC] free` under `CRANELISP_RC_TRACE=1` — the 16-byte descriptor region is `NeverHeap` scalars (no RC, no drop glue), so no descriptor-region leak. Uses the `rc_alloc_free_counts` precedent. | NEW, RED-until v9 — **Phase-3 gap G-C (deterministic bounded produce/consume fixture)** |

> Mirror unit (`/dev`-owed, backend, `io-trampoline.md §17.8`): a resource-handle ADT construct
> stores zero into `+24/+32` and (for `Connection []`) no logical fields; a poll effect bakes
> `role` @ `+32` and zero/static into the `+40` region with **no `arg_vals[0]/[1]` positional
> store** (the deleted-bake negative guard); a non-resource ADT keeps `FIELDS_START = 24`. CLIF-
> inspectable on a shrunk repro.

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
| 4.2 | `concurrency_v9_select::empty_select_caught_by_catch_runtime_error` | e2e | `spec/12-runtime.md §12.7.2` | `(catch-runtime-error (fn [] <empty-select-thunk>))` → `(Err "select over empty collection…")`; program recovers and exits with the recovered branch value (recoverable at the catch boundary) | NEW, RED-until 0475 guard |
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

## Item 8 — the §7.3 watch-item (consumed handle = `arg(0)` / `state+8`)

The load-bearing v9 contract: a Consume leaf's resource handle is its FIRST arg, marshaled at env
offset `state + 8` = `PollEnv::arg(0)` (`reactor.md §7.2/§7.3`, `io-trampoline.md §17.5`). A
future Consume sig that moved the handle off `arg(0)` would silently break the header read.

| # | Test | Tier | spec anchor | Assertion | Owner / state |
|---|---|---|---|---|---|
| 8.1 | intrinsics: `consumed_handle_is_arg0_at_state_plus_8` | unit (intrinsics) | `reactor.md §7.3` / `io-trampoline.md §17.5` | a `token == 0` Consume reads the consumed handle pointer at `state + 8` and the descriptor at `handle + 24`; pins the arg(0)-is-handle contract so a handle-position reshape is caught | `/dev` (intrinsics) — RECORDED, not /qa-authored |

> Companion `/dev`-owed trampoline stamp/read isolations (`reactor.md §7.6`): Produce leaf writes
> `{T,N}` to `desc_out` ⇒ produced value header carries `{T,N}` at `+24` on `Ready`; Consume over
> a pre-stamped `{T,N}` handle ⇒ permit acquired on token `T`; `read-line` singleton ⇒ acquire on
> `STDIN_TOKEN` with NO handle read; `None` leaf ⇒ no acquire, no stamp; negative: absence of any
> v8 node `(token, capacity)` read.

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
| 3 | 2.1, 2.2, 2.4 (v9 layout/representation; 2.3 is existing-GREEN regression) | v9 cutover |
| 2 | 3.1, 3.2 (0474 RC-balance) | 0474 deep-free |
| 4 | 4.1–4.4 (0475 empty-select; 4.4 may fold into 4.1) | 0475 guard |
| 2 | 5.1, 5.2 (0479; subject to gap G-D) | 0479 + knob |
| **15** | **(13 firm + 2 gap-contingent)** NEW e2e | — |

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
