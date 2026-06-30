//! Sprint 97 — ABI v8→v9: the resource descriptor becomes trampoline-owned
//! representation overhead (FIXME 0482). QA-first (Phase 5 Wave 1) failing-not-
//! ignored e2e acceptance rows for the user-visible v9 signature change (item 1)
//! and the v9 layout / representation guards (item 2).
//!
//! Plan: `tests/plan/sprint-97.md` §"Item 1" + §"Item 2". Contracts of record:
//!   - `design/platform/poll-support.md §3.5` — opaque `Connection []` + slim leaf
//!     sigs (`accept-conn:(Fn [Listener] (IO Connection))` Produce /
//!     `read-conn:(Fn [Connection] (IO Request))` + `send-conn:(Fn [Connection
//!     Response] (IO Int))` Consume).
//!   - `design/arch/platform-interface.md §6.8.0b` — the v9 ABI ruling (descriptor
//!     as representation overhead; backend stops baking from positional args).
//!
//! ## Spec anchor (gap G-A, /sprint-resolved)
//!
//! v9 is **representation/ABI, not language semantics** (arch Phase-2 ruling) — NO
//! new `/spec` section for the leaf-signature reshape. These rows therefore anchor
//! their `// spec:` to the design citations above (consistent with existing
//! concurrency tests citing `effect-concurrency.md`), not a `spec/` section.
//!
//! ## Posture — RED-until the v9 cutover lands (Wave 2)
//!
//! All rows are **failing-not-ignored** (`memory/feedback_failing_not_ignored.md`).
//! They are written against the **intended v9 world**: each test drops a v9-shaped
//! opaque `web.cl` (`Connection []`) into its tmpdir and loads the workspace `web`
//! platform DLL. On HEAD the DLL is still v8 (3-field `Connection`), so the platform
//! load fails the **embedded-schema gate** — a clean, loud RED for every row. The
//! v9 cutover (`cranelisp-types` + platform DLL reshape, SPRINT.md Wave 2) rebuilds
//! the DLL against the opaque `Connection`; the schema gate then passes and:
//!   - the POSITIVE rows (1.2/1.3-pos/1.4/handle-only) compile + exit 0;
//!   - the REJECT rows (1.1/1.3-neg/2.1) surface a clean leaf-arity / field-count
//!     type error (NOT the schema-gate error) — the `!contains("schema")`
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
/// analogue): `poll-produce` mints a resource handle (the trampoline STAMPS the
/// `{token,capacity}` descriptor into its header side-band), `poll-consume` consumes
/// it (the trampoline READS the descriptor off the handle pre-poll), then both exit.
/// Absent on HEAD ⇒ a clean runtime-RED (the leaf does not resolve). See the 2.4 FIXME.
const POLL_PRODUCE: &str = "poll-produce";
const POLL_CONSUME: &str = "poll-consume";

/// Count `[RC] alloc` / `[RC]  free` events in a `CRANELISP_RC_TRACE=1` stderr.
/// Mirrors `concurrency_spark.rs::rc_alloc_free_counts`.
fn rc_alloc_free_counts(stderr: &str) -> (usize, usize) {
    let allocs = stderr.lines().filter(|l| l.contains("[RC]") && l.contains(" alloc ")).count();
    let frees = stderr.lines().filter(|l| l.contains("[RC]") && l.contains(" free ")).count();
    (allocs, frees)
}

/// The v9-shaped web connection-handle ADT module — `Connection` is **fully
/// opaque** (`poll-support.md §3.5.1`: zero logical fields; the `{token,capacity}`
/// descriptor rides the value header side-band, invisible to user source). The
/// other three ADTs mirror `exemplar/web.cl` unchanged. The /port-owned v9 `web.cl`
/// is the production form of this; inlined here so each row is self-contained.
/// On HEAD this opaque shape mismatches the v8 DLL's embedded schema (the RED).
const V9_WEB_CL: &str = "\
(deftype Listener [:primitives/Int fd :primitives/Int pool])\n\
(deftype Connection [])\n\
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

/// Assert a v9 program is REJECTED by a clean leaf-arity / field-count type error,
/// NOT by the HEAD schema gate. The `!contains("schema")` clause is the load-bearing
/// RED-until-v9 discriminator: on HEAD the program dies at the platform schema gate
/// ("embedded schema is out of date"), so this fails (RED); post-cutover the opaque
/// DLL passes the gate and the leaf-arity/field-count error (no "schema") flips it
/// GREEN.
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
         3-field Connection vs the opaque v9 Connection), not the leaf-arity / field-count \
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
// Item 2 — v9 layout / representation guards (descriptor is type-invisible).
// =============================================================================

// spec: design/platform/poll-support.md §3.5.1 — `(deftype Connection [])` has ZERO
// logical fields: the `{token,capacity}` descriptor rides the value-header side-band
// (`RESOURCE_DESC_OFFSET = 24`), invisible to the pattern. So a v8-style 3-field
// destructure `[(Connection a b c)]` MUST be a wrong-field-count type error (expected
// 0, got 3) — the descriptor is NOT a destructurable field. RED-until v9 cutover.
#[test]
fn connection_is_opaque_zero_fields_destructure_rejected_neg() {
    let out = run_v9(
        "(import [web [Connection]])",
        "(defn d [:web/Connection c] (match c [(Connection a b c2) a]))",
    );
    assert_v9_rejected(out, "connection_is_opaque_zero_fields_destructure_rejected_neg");
}

// spec: design/platform/poll-support.md §3.5.1 — negative-coverage: the descriptor
// is invisible at the VALUE level. A clean load + probe of the opaque `Connection`
// MUST NOT surface `token` / `capacity` / a descriptor field anywhere in its display
// or value-shape. RED-until v9: on HEAD the v8 DLL's embedded schema (a 3-field
// Connection carrying `token`/`capacity`) mismatches the opaque module ⇒ the probe
// dies at the schema gate (the `!contains("schema")` clause is RED); post-cutover the
// opaque Connection probes cleanly with NO descriptor field.
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
    // The descriptor MUST be invisible at the value level (the negative assertion).
    assert!(
        !combined.contains("token") && !combined.contains("capacity"),
        "connection_display_shows_no_descriptor_neg: the opaque v9 Connection MUST NOT \
         surface `token` / `capacity` (the descriptor is trampoline-owned header overhead, \
         not a logical field — poll-support.md §3.5.1); got:\n{combined}"
    );
}

// spec: design/backend/io-trampoline.md §17.2 — the 16-byte descriptor region
// (`RESOURCE_DESC_OFFSET = 24`) is `NeverHeap` scalars (`{token,capacity}` — no RC, no
// drop glue). Over a bounded produce(stamp)→consume(read) cycle, `[RC] alloc` MUST
// equal `[RC] free`: the descriptor-region carries NO heap reference, so it cannot
// leak. RED on HEAD; GREEN when the v9 stamp/read trampoline (Wave 2) + the bounded
// fixture (G-C) land.
//
// FIXME(/sprint S97 W3) — gap G-C: an RC-balance assertion over a REAL network server
// is non-deterministic (the server runs indefinitely; trace volume is unbounded). A
// clean descriptor-no-leak witness needs a BOUNDED poll fixture that produces then
// consumes a handful of resource handles and EXITS — the co-landing `/platform` +
// `/dev` `poll-produce` / `poll-consume` leaves (the S96 Gap-G1 poll-pool analogue).
// /dev (Wave 3) must ADD them to `platforms/poll-pool/` + `tests/scripts/
// build-link-prereqs.sh`. If that fixture does not land, 2.4 REDUCES to the `/dev`
// intrinsics RC-balance UNIT (plan §"Item 2" mirror, /dev-owed). On HEAD the leaves are
// absent ⇒ RED (the run errors; no balanced trace).
#[test]
fn produce_consume_descriptor_no_rc_leak() {
    // A bounded produce→consume loop over N resource handles, then exit. Each
    // `poll-produce` stamps a descriptor into the produced handle's header; each
    // `poll-consume` reads it. The descriptor region is NeverHeap scalars ⇒ no RC.
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
        "the descriptor region (NeverHeap scalars @ +24) must add NO RC — a bounded \
         produce/consume cycle must be alloc/free balanced; got {allocs} allocs / {frees} \
         frees.\nstderr:\n{}",
        out.stderr
    );
}
