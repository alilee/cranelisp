//! Pool-demo platform for cranelisp — the Sprint-95 slice-3 capacity test leaf.
//!
//! A standalone **blocking** (v6) cdylib that demonstrates the
//! effect-concurrency token-capacity pool on the BLOCKING carrier
//! (`effect-concurrency.md` §8.1 / `io-trampoline.md` §13.2 / `tests/plan/sprint-95.md`
//! §1C/§1D/§1F). Each effect declares its `(token, capacity)` pair dynamically at
//! the effect site via the additive
//! [`CLIO::effect_on_resource_with_capacity`](cranelisp_platform::CLIO::effect_on_resource_with_capacity)
//! constructor (slice-3 capacity carrier, S95), then performs a blocking sleep so
//! the pool's admit/park behaviour is wall-clock observable.
//!
//! Three platform effects, all routing to the BLOCKING pool, all sharing the
//! capacity-on-token model (distinct tokens ⇒ independent pools; shared token ⇒
//! one shared pool — the DB connection-pool case):
//!
//! - `pool-read  : (Int token, Int capacity, Int ms) -> IO Int` — sleep `ms` on
//!   the token's capacity pool, return `ms`.
//! - `pool-write : (Int token, Int capacity, Int ms) -> IO Int` — a DISTINCT
//!   effect kind on the same token (the §1F sharing case), sleep `ms`, return `ms`.
//! - `pool-log   : (Int token, Int capacity, Int ms, String tag) -> IO Int` —
//!   sleep `ms`, then print `tag` to real stdout (the §1D source-order witness),
//!   return `ms`.
//!
//! **Posture (S95 Wave 2).** This leaf supplies a *live* `(token, capacity)` pair
//! on every blocking node, but the host-owned `HashMap<token, Semaphore(capacity)>`
//! pool that ENFORCES it is the Wave-4 intrinsics deliverable. Until that lands the
//! effects route to the existing single-reactor-thread / same-token-serial path, so
//! the §1C/§1D/§1F e2e are **behaviour-RED** (the fixture loads; no parking yet) —
//! they flip GREEN when the pool is wired. The leaf is a v6 blocking platform
//! (no `concurrency` feature), loaded via the namespaced
//! `cranelisp_platform_manifest_pool-demo` export exactly like `test-capture`.

use cranelisp_platform::*;
use std::io::Write;

static HOST: HostContext = HostContext::new();

/// `pool-read`: sleep `ms` ms on the `(token, capacity)` pool, return `ms`.
///
/// The `(token, capacity)` pair is supplied dynamically on the IO node via the
/// slice-3 capacity carrier. capacity 1 ⇒ serial-within-token (`ResourceSerial`);
/// capacity N ⇒ the bounded pool (the (N+1)th parks); effects sharing a token
/// share one pool.
pub extern "C" fn pool_read(token: CLInt, capacity: CLInt, ms: CLInt) -> CLIO<CLInt> {
    let tok = i64::from(token);
    let cap = i64::from(capacity);
    let duration = i64::from(ms);
    CLIO::effect_on_resource_with_capacity(tok, cap, move || {
        std::thread::sleep(std::time::Duration::from_millis(duration as u64));
        CLInt::from(duration)
    })
}

/// `pool-write`: a DISTINCT effect kind from `pool-read` that draws from the SAME
/// token's pool (the §1F sharing case — two distinct effects sharing one token
/// share one `Semaphore`, sum-in-flight ≤ capacity across both kinds). Sleeps
/// `ms`, returns `ms`.
pub extern "C" fn pool_write(token: CLInt, capacity: CLInt, ms: CLInt) -> CLIO<CLInt> {
    let tok = i64::from(token);
    let cap = i64::from(capacity);
    let duration = i64::from(ms);
    CLIO::effect_on_resource_with_capacity(tok, cap, move || {
        std::thread::sleep(std::time::Duration::from_millis(duration as u64));
        CLInt::from(duration)
    })
}

/// `pool-log`: sleep `ms`, then print `tag` to **real stdout** (the §1D
/// within-token source-order witness — at capacity 1 the effects serialise AND
/// land in source order, observable via the emitted tags), return `ms`.
///
/// `tag` is captured into the deferred Effect closure via the consuming capture-RC
/// protocol (Decision 24): `into_owned_consuming` takes ownership of the caller's
/// transferred reference and releases it on drop when the thunk runs.
pub extern "C" fn pool_log(token: CLInt, capacity: CLInt, ms: CLInt, tag: CLString) -> CLIO<CLInt> {
    let tok = i64::from(token);
    let cap = i64::from(capacity);
    let duration = i64::from(ms);
    let owned = tag.into_owned_consuming();
    CLIO::effect_on_resource_with_capacity(tok, cap, move || {
        std::thread::sleep(std::time::Duration::from_millis(duration as u64));
        let mut out = std::io::stdout();
        let _ = out.write_all(owned.as_str().as_bytes());
        let _ = out.flush();
        CLInt::from(duration)
    })
}

declare_platform! {
    name: "pool-demo",
    version: "0.1.0",
    host: HOST,
    functions: [
        pool_read {
            cl_name: "pool-read",
            sig: "(Fn [primitives/Int primitives/Int primitives/Int] (primitives/IO primitives/Int))",
            doc: "Sleep ms on the (token, capacity) pool and return ms (blocking capacity carrier, for testing)",
            params: [token, capacity, ms],
            scheduling: SchedulingClass::ResourceSerial,
        },
        pool_write {
            cl_name: "pool-write",
            sig: "(Fn [primitives/Int primitives/Int primitives/Int] (primitives/IO primitives/Int))",
            doc: "A distinct effect kind sharing the same token's pool: sleep ms and return ms (blocking capacity carrier, for testing token sharing)",
            params: [token, capacity, ms],
            scheduling: SchedulingClass::ResourceSerial,
        },
        pool_log {
            cl_name: "pool-log",
            sig: "(Fn [primitives/Int primitives/Int primitives/Int primitives/String] (primitives/IO primitives/Int))",
            doc: "Sleep ms then print tag to stdout and return ms (blocking capacity carrier, witnesses within-token source order)",
            params: [token, capacity, ms, tag],
            scheduling: SchedulingClass::ResourceSerial,
        },
    ]
}
