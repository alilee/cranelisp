//! Sprint 97 — ABI v8→v9: the **callback-vtable handle model** (model pivot,
//! 2026-06-30; supersedes the descriptor cut + FIXME 0482, both DELETED). QA-first
//! (Phase 5 Wave 1) failing-not-ignored e2e acceptance rows for the user-visible v9
//! signature change (item 1) and the v9 layout / representation guards (item 2 —
//! *adjusted* to the ctx-vtable reality, S97 Wave-1 layout rework).
//!
//! Plan: `tests/plan/sprint-97.md` §"Item 1" + §"Item 2". Contracts of record:
//!   - `design/platform/poll-support.md §3.5` — **opaque `Connection` with a GENUINE
//!     `fd` field** (`(deftype Connection [:primitives/Int fd])`; `r == fd`, the
//!     platform reads it back, user code threads but cannot destructure it open) +
//!     slim leaf sigs (`accept-conn:(Fn [Listener] (IO Connection))` Produce /
//!     `read-conn:(Fn [Connection] (IO Request))` + `send-conn:(Fn [Connection
//!     Response] (IO Int))` Consume).
//!   - `design/arch/effect-concurrency.md §4.1.1` — the model: scheduling state
//!     (`token`/`capacity`/`role`) NEVER rides on a value; it flows through a
//!     trampoline-owned `ctx` vtable (`acquire`/`register_*`/`retire`; release is
//!     tramp-owned) the platform's poll-fn calls. **NO `ResourceDesc`, no header
//!     slot, no `desc_out`, no `PollFn` change, no positional-pair bake.**
//!   - `design/arch/platform-interface.md §6.8.0b` — the ctx-vtable ABI (backend
//!     just DELETES `inject_poll_leading_pair`; `PollFn`/`Poll` unchanged).
//!
//! ## Spec anchor (gap G-A, /sprint-resolved)
//!
//! v9 is **representation/ABI, not language semantics** (arch ruling) — NO new
//! `/spec` section for the leaf-signature reshape. These rows therefore anchor
//! their `// spec:` to the design citations above (consistent with existing
//! concurrency tests citing `effect-concurrency.md`), not a `spec/` section.
//!
//! ## Posture — RED-until the v9 cutover lands (Wave 2)
//!
//! All rows are **failing-not-ignored** (`memory/feedback_failing_not_ignored.md`).
//! They are written against the **intended v9 world**: each test drops a v9-shaped
//! opaque `web.cl` (`Connection [fd]`) into its tmpdir and loads the workspace `web`
//! platform DLL. On HEAD the DLL is still v8 (3-field `Connection [token capacity
//! fd]`), so the platform load fails the **embedded-schema gate** — a clean, loud
//! RED for every row. The v9 cutover (`cranelisp-types` ABI bump + platform DLL
//! reshape to the opaque `Connection [fd]`, SPRINT.md Wave 2) rebuilds the DLL; the
//! schema gate then passes and:
//!   - the POSITIVE rows (1.2/1.3-pos/1.4/handle-only) compile + exit 0;
//!   - the REJECT rows (1.1/1.3-neg/2.1-opacity) surface a clean leaf-arity /
//!     opacity type error (NOT the schema-gate error) — the `!contains("schema")`
//!     discriminator is exactly what keeps them RED on HEAD and flips them GREEN
//!     post-cutover.
//!
//! Free-standing per `tests/CLAUDE.md`: primitives + special forms only; the only
//! external surface is the workspace `web` platform DLL (its leaf signatures ARE
//! what v9 reshapes) + an inline opaque `web.cl`. ZERO `stdlib/` dependency.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, CrOutput};

/// The `poll-pool` fixture platform (`concurrency_fanout.rs`).
const POLL_PLATFORM: &str = "poll-pool";
/// `poll-produce` / `poll-consume` — the Gap-G-C bounded resource-handle fixture
/// leaves (a co-landing `/platform` + `/dev` deliverable, the S96 Gap-G1 poll-pool
/// analogue): `poll-produce` mints an **opaque resource handle** (an ordinary ADT
/// carrying a genuine `fd`-style field — Produce role; the poll-fn drives `acquire`/
/// `register` via the `ctx` vtable, no header stamp), `poll-consume` threads it
/// (Consume role; the poll-fn projects the token from the handle's own field), then
/// both exit. Under the ctx-vtable model NOTHING is stamped onto the value — the
/// handle is a normal ADT, so a produce→consume→retire cycle RC-balances like any
/// ADT-field cycle. Absent on HEAD ⇒ a clean runtime-RED (the leaf does not resolve).
/// See the 2.4 FIXME.
const POLL_PRODUCE: &str = "poll-produce";
const POLL_CONSUME: &str = "poll-consume";

/// Count `[RC] alloc` / `[RC]  free` events in a `CRANELISP_RC_TRACE=1` stderr.
/// Mirrors `concurrency_spark.rs::rc_alloc_free_counts`.
fn rc_alloc_free_counts(stderr: &str) -> (usize, usize) {
    let allocs = stderr.lines().filter(|l| l.contains("[RC]") && l.contains(" alloc ")).count();
    let frees = stderr.lines().filter(|l| l.contains("[RC]") && l.contains(" free ")).count();
    (allocs, frees)
}

/// The v9-shaped web connection-handle ADT module — `Connection` is **opaque but
/// carries a GENUINE `fd` field** (`poll-support.md §3.5.1`: a normal 1-field ADT
/// = HeapHeader(16) + tag(8) + fd(8); the platform reads `r == fd` back out of the
/// field, the trampoline never introspects it; user code threads the handle but the
/// field is **not user-destructurable**). Scheduling state (`token`/`capacity`)
/// never touches the value — it flows through the `ctx` vtable (`effect-concurrency.md
/// §4.1.1`). NO header slot, NO `desc_out`, NO `ResourceDesc`. The other three ADTs
/// mirror `exemplar/web.cl` unchanged. The /port-owned v9 `web.cl` is the production
/// form of this; inlined here so each row is self-contained. On HEAD this opaque
/// 1-field shape mismatches the v8 DLL's 3-field embedded schema (the RED).
const V9_WEB_CL: &str = "\
(deftype Listener [:primitives/Int fd :primitives/Int pool])\n\
(deftype Connection [:primitives/Int fd])\n\
(deftype Request [:primitives/String method :primitives/String path :primitives/String body])\n\
(deftype Response [:primitives/Int status :primitives/String content-type :primitives/String body])\n";

/// Build + `--run` a compile-only v9 program: drop the opaque `web.cl`, load the
/// workspace `web` platform, prepend `(platform web)` + the given imports, append a
/// trivial `(defn main [] (Pure 0))`. The leaves need not RUN (the assertion is on
/// the typecheck result), so no live server / socket is needed.
fn run_v9(imports: &str, defns: &str) -> CrOutput {
    let src = format!(
        "(platform web)\n{imports}\n(import [primitives [Pure]])\n{defns}\n(defn main [] (Pure 0))\n"
    );
    Cranelisp::new()
        .use_workspace_platforms()
        .file("web.cl", V9_WEB_CL)
        .file("user.cl", &src)
        .run("user.cl")
        .output()
}

/// Assert a v9 program is REJECTED by a clean leaf-arity / opacity type error,
/// NOT by the HEAD schema gate. The `!contains("schema")` clause is the load-bearing
/// RED-until-v9 discriminator: on HEAD the program dies at the platform schema gate
/// ("embedded schema is out of date"), so this fails (RED); post-cutover the opaque
/// `Connection [fd]` DLL passes the gate and the leaf-arity / opacity error (no
/// "schema") flips it GREEN.
fn assert_v9_rejected(out: CrOutput, ctx: &str) {
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert_ne!(
        out.status.code(),
        Some(0),
        "{ctx}: the v9-rejected shape MUST NOT typecheck (non-zero exit); got exit 0\n{combined}"
    );
    assert!(
        !combined.contains("schema"),
        "{ctx}: RED-until-v9 — on HEAD this fails at the platform SCHEMA GATE (v8 DLL's \
         3-field Connection vs the opaque v9 Connection [fd]), not the leaf-arity / opacity \
         rejection it must become. Flips GREEN when the v9 cutover (Wave 2) rebuilds the web \
         DLL opaque so the rejection is a clean type error.\ncombined:\n{combined}"
    );
    assert!(
        !combined.to_lowercase().contains("internal"),
        "{ctx}: the rejection must be a clean user-facing type error, never an internal panic\n{combined}"
    );
}

/// Assert a v9 program TYPECHECKS + compiles (a compile-only program exits 0). On
/// HEAD this fails at the schema gate (exit 1) — the RED; post-cutover it exits 0.
fn assert_v9_typechecks(out: CrOutput, ctx: &str) {
    if out.status.code() != Some(0) {
        panic!(
            "{ctx}: RED-until-v9 — the v9 handle-only shape MUST typecheck + compile \
             (exit 0). On HEAD it fails (schema gate / v8 leaf arity); flips GREEN when \
             the v9 cutover (Wave 2) lands.\nexit={:?}\nstdout:\n{}\nstderr:\n{}",
            out.status.code(),
            out.stdout,
            out.stderr
        );
    }
}

// =============================================================================
// Item 1 — the v9 user-visible signature change (the HEADLINE behavioral change).
// =============================================================================

// spec: design/platform/poll-support.md §3.5.2 — v9 `read-conn:(Fn [Connection]
// (IO Request))`. The v8 3-arg shape `(read-conn token capacity fd)` over three
// `Int`s MUST be a typecheck error post-cutover (the descriptor stops being a
// cranelisp value; the leaf takes ONLY the connection handle). RED-until v9 cutover.
#[test]
fn read_conn_three_arg_shape_rejected_neg() {
    let out = run_v9(
        "(import [platform.web [read-conn]])",
        "(defn use3 [:primitives/Int t :primitives/Int c :primitives/Int f] (read-conn t c f))",
    );
    assert_v9_rejected(out, "read_conn_three_arg_shape_rejected_neg");
}

// spec: design/platform/poll-support.md §3.5.2 — v9 `read-conn:(Fn [Connection]
// (IO Request))`: `(read-conn conn)` (1-arg, over a `Connection`) MUST typecheck +
// compile. Compile-only (the leaf need not run). RED-until v9 cutover.
#[test]
fn read_conn_handle_only_shape_typechecks() {
    let out = run_v9(
        "(import [web [Connection]])\n(import [platform.web [read-conn]])",
        "(defn use1 [:web/Connection conn] (read-conn conn))",
    );
    assert_v9_typechecks(out, "read_conn_handle_only_shape_typechecks");
}

// spec: design/platform/poll-support.md §3.5.2 — v9 `send-conn:(Fn [Connection
// Response] (IO Int))`: the 2-arg handle+response shape `(send-conn conn resp)` MUST
// typecheck, AND the v8 4-arg `(send-conn token capacity fd resp)` MUST be rejected
// (the `_neg` companion, same row). RED-until v9 cutover.
#[test]
fn send_conn_handle_plus_response_typechecks() {
    // Positive: the v9 2-arg handle+response shape typechecks.
    let pos = run_v9(
        "(import [web [Connection Response]])\n(import [platform.web [send-conn]])",
        "(defn snd [:web/Connection conn :web/Response r] (send-conn conn r))",
    );
    assert_v9_typechecks(pos, "send_conn_handle_plus_response_typechecks (2-arg positive)");

    // Negative companion: the v8 4-arg `(send-conn token capacity fd resp)` is gone.
    let neg = run_v9(
        "(import [web [Response]])\n(import [platform.web [send-conn]])",
        "(defn snd4 [:primitives/Int t :primitives/Int c :primitives/Int f :web/Response r] \
         (send-conn t c f r))",
    );
    assert_v9_rejected(neg, "send_conn_handle_plus_response_typechecks (4-arg neg companion)");
}

// spec: design/platform/poll-support.md §3.5.2 — v9 `accept-conn:(Fn [Listener]
// (IO Connection))`: `(accept-conn listener)` typechecks and PRODUCES a `Connection`
// value (the lambda binder annotated `:web/Connection` unifies against the leaf's
// `(IO Connection)` result). RED-until v9 cutover.
#[test]
fn accept_conn_listener_only_typechecks() {
    let out = run_v9(
        "(import [web [Listener Connection]])\n(import [platform.web [accept-conn]])\n\
         (import [primitives [bind]])",
        "(defn acc [:web/Listener l] (bind (accept-conn l) (fn [:web/Connection c] (Pure 0))))",
    );
    assert_v9_typechecks(out, "accept_conn_listener_only_typechecks");
}

// =============================================================================
// Item 2 — v9 layout / representation guards (scheduling state never rides on the
// value; the handle is an opaque ADT). ADJUSTED to the ctx-vtable model (S97 Wave-1
// layout rework — the dead header-slot/`desc_out` model is gone).
// =============================================================================

// spec: design/platform/poll-support.md §3.5.1 — `(deftype Connection
// [:primitives/Int fd])` is **tramp-opaque but USER-READABLE** (`/arch`'s ruling,
// FIXME 0484 / `effect-concurrency.md §4.1.1`): the load-bearing invariant is opacity
// toward the *trampoline* — the trampoline threads the handle accept→read/send/close
// without ever introspecting its fields, and only the *platform* (which built it) reads
// `r`/`fd` back out. It is NOT opaque to the user: `Connection` is an ordinary 1-field
// ADT, so user code CAN destructure/`match` it open — `(match c [(Connection fd) fd])`
// typechecks and yields the real fd (the program's own connection datum). There is no
// language mechanism that makes an ADT non-user-destructurable, and none is invented.
//
// POSITIVE guard (inverted S98 band-C, FIXME 0489): a user destructure of `Connection`
// MUST typecheck + compile (exit 0) and read out the genuine `fd` field — if the handle
// were non-user-destructurable this `match` would be a type/opacity error; it is not.
// The value-side "no scheduling state on the handle" negatives (the RIGHT negatives to
// keep — token/capacity/descriptor never ride the value; tramp-opacity is a codegen
// invariant, not e2e-observable here) are covered by the sibling
// `connection_display_shows_no_descriptor_neg` + `connection_carries_no_scheduling_
// state_normal_adt_neg` rows.
#[test]
fn connection_field_user_readable() {
    let out = run_v9(
        "(import [web [Connection]])",
        "(defn d [:web/Connection c] (match c [(Connection fd) fd]))",
    );
    assert_v9_typechecks(out, "connection_field_user_readable");
}

// spec: design/platform/poll-support.md §3.5.1 — negative-coverage: NO scheduling
// state rides on the value. A clean load + probe of the opaque `Connection` MUST NOT
// surface `token` / `capacity` (nor any descriptor/role) anywhere in its display or
// value-shape — under the ctx-vtable model those live entirely in the trampoline's
// `ctx`, never on the handle (`effect-concurrency.md §4.1.1`). Cleaner than the dead
// header-slot model: there is literally nothing scheduling-related on the value.
// RED-until v9: on HEAD the v8 DLL's 3-field embedded schema (a Connection carrying
// `token`/`capacity`) mismatches the opaque 1-field module ⇒ the probe dies at the
// schema gate (the `!contains("schema")` clause is RED); post-cutover the opaque
// `Connection [fd]` probes cleanly with no scheduling field.
//
// NOTE: this probes the TYPE-level invisibility (no socket needed). The value-level
// produced-`Connection` display is exercised by the /port web fan-out fixture.
#[test]
fn connection_display_shows_no_descriptor_neg() {
    let cap = Cranelisp::new()
        .use_workspace_platforms()
        .file("web.cl", V9_WEB_CL)
        .repl()
        .stdin("(platform web)\n(import [web [Connection]])\nConnection\n")
        .output();
    let combined = format!("{}{}", cap.stdout, cap.stderr).to_lowercase();
    // RED-until-v9 signal: a clean opaque load (no schema-gate failure).
    assert!(
        !combined.contains("schema"),
        "connection_display_shows_no_descriptor_neg: RED-until-v9 — on HEAD the opaque \
         Connection mismatches the v8 DLL's embedded schema, so the probe fails at the \
         schema gate. Flips GREEN when the v9 cutover rebuilds the DLL opaque.\n{combined}"
    );
    // No scheduling state at the value level (the negative assertion).
    assert!(
        !combined.contains("token") && !combined.contains("capacity"),
        "connection_display_shows_no_descriptor_neg: the opaque v9 Connection MUST NOT \
         surface `token` / `capacity` (scheduling state is trampoline-`ctx`-owned, never a \
         field on the handle — effect-concurrency.md §4.1.1 / poll-support.md §3.5.1); \
         got:\n{combined}"
    );
}

// spec: design/arch/effect-concurrency.md §4.1.1 — NEW absence guard (/design(int)
// asked for it): the value carries NO scheduling state of any kind. Under the
// ctx-vtable model there is no value-header stamp/read, no node `(token,capacity)`,
// no `role`, no `desc_out` — `Connection` is just a normal 1-field opaque ADT. The
// e2e-observable face is the TYPE introspection: a probe of `Connection` MUST NOT
// surface `descriptor` / `desc` / `role` / `desc_out` / `token` / `capacity`
// anywhere (the broadened forbidden set vs 2.2's display-of-`token`/`capacity`).
// RED-until v9 via the same schema-gate discriminator.
//
// The DEEPER, CLIF-internal absence — no header slot @ +24, no poll-node `role` @
// +32, no `desc_out` @ +40, no `inject_poll_leading_pair` positional bake — is NOT
// e2e-observable; it is a `/dev`-owed backend codegen unit (`io-trampoline.md §17`,
// recorded in `tests/plan/sprint-97.md` §"Item 2" mirror). This e2e covers only the
// value-/type-level "no scheduling state" face.
#[test]
fn connection_carries_no_scheduling_state_normal_adt_neg() {
    let cap = Cranelisp::new()
        .use_workspace_platforms()
        .file("web.cl", V9_WEB_CL)
        .repl()
        .stdin("(platform web)\n(import [web [Connection]])\n/info web/Connection\n")
        .output();
    let combined = format!("{}{}", cap.stdout, cap.stderr).to_lowercase();
    // RED-until-v9 signal: a clean opaque load (no schema-gate failure on HEAD).
    assert!(
        !combined.contains("schema"),
        "connection_carries_no_scheduling_state_normal_adt_neg: RED-until-v9 — on HEAD the \
         opaque 1-field Connection mismatches the v8 DLL's 3-field embedded schema, so the \
         probe dies at the schema gate. Flips GREEN when the v9 cutover rebuilds the DLL \
         opaque.\n{combined}"
    );
    // No scheduling artifact of any kind on the handle/type (the broadened negative).
    for forbidden in ["descriptor", "desc_out", "role", "token", "capacity"] {
        assert!(
            !combined.contains(forbidden),
            "connection_carries_no_scheduling_state_normal_adt_neg: the opaque v9 Connection \
             is a normal 1-field ADT — its introspection MUST NOT surface `{forbidden}` \
             (all scheduling state lives in the trampoline `ctx`, never on the value — \
             effect-concurrency.md §4.1.1); got:\n{combined}"
        );
    }
}

// spec: design/arch/effect-concurrency.md §4.1.1 — under the ctx-vtable model there
// is NO descriptor region on the value: a resource handle is an ordinary opaque ADT
// (`Connection [fd]`) carrying a genuine scalar field. Over a bounded produce→consume
// →retire cycle, `[RC] alloc` MUST equal `[RC] free`: the handle RC-balances like any
// 1-field ADT (the `fd` Int is a scalar — no RC, no drop glue), and scheduling lives
// in the trampoline `ctx`, not on the value, so there is no value-carried region to
// leak. RED on HEAD; GREEN when the bounded fixture (G-C) lands. (Re-expressed from the
// dead "16-byte descriptor region @ +24" model — there is no such region under v9.)
//
// FIXME(/sprint S97 W3) — gap G-C: an RC-balance assertion over a REAL network server
// is non-deterministic (the server runs indefinitely; trace volume is unbounded). A
// clean no-leak witness needs a BOUNDED poll fixture that produces then consumes a
// handful of resource handles and EXITS — the co-landing `/platform` + `/dev`
// `poll-produce` / `poll-consume` leaves (the S96 Gap-G1 poll-pool analogue). /dev
// (Wave 3) must ADD them to `platforms/poll-pool/` + `tests/scripts/
// build-link-prereqs.sh`. If that fixture does not land, 2.4 REDUCES to the `/dev`
// intrinsics RC-balance UNIT (plan §"Item 2" mirror, /dev-owed). On HEAD the leaves are
// absent ⇒ RED (the run errors; no balanced trace).
#[test]
fn produce_consume_descriptor_no_rc_leak() {
    // A bounded produce→consume loop over N opaque handles, then exit. `poll-produce`
    // mints an opaque handle (Produce role; ctx-vtable acquire/register, no stamp);
    // `poll-consume` threads it (Consume role; the poll-fn projects the token from the
    // handle's own field). The handle is a normal ADT ⇒ ordinary alloc/free balance.
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{produce} {consume}]])\n\
         (import [primitives [bind Pure sub-i64 eq-i64]])\n\
         (defn cycle [n]\n\
           (if (eq-i64 n 0)\n\
               (Pure 0)\n\
               (bind ({produce} n) (fn [h]\n\
                 (bind ({consume} h) (fn [_]\n\
                   (cycle (sub-i64 n 1))))))))\n\
         (defn main [] (cycle 8))\n",
        plat = POLL_PLATFORM,
        produce = POLL_PRODUCE,
        consume = POLL_CONSUME,
    );
    let out = Cranelisp::new()
        .use_workspace_platforms()
        .env("CRANELISP_RC_TRACE", "1")
        .file("user.cl", &prog)
        .run("user.cl")
        .output();
    assert_eq!(
        out.status.code(),
        Some(0),
        "the bounded produce/consume cycle must run cleanly to completion (exit 0); RED on \
         HEAD until the G-C `poll-produce`/`poll-consume` fixture leaves land (see FIXME)\n\
         stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    let (allocs, frees) = rc_alloc_free_counts(&out.stderr);
    assert!(allocs > 0, "expected the RC trace to record allocations; got 0");
    assert_eq!(
        allocs, frees,
        "the opaque handle carries NO value-side scheduling region (scheduling is \
         ctx-vtable-owned — effect-concurrency.md §4.1.1), so a bounded produce/consume \
         cycle must be alloc/free balanced; got {allocs} allocs / {frees} frees.\nstderr:\n{}",
        out.stderr
    );
}
