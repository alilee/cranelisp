//! N3 (S105, `design/backend/ownership-codegen.md` §13.2.2): the per-SITE
//! residual-atomic-RC dump + Crossing/Confined cell tally (`[RC_SITE_STATS]`).
//!
//! The aggregate `rc_nonatomic`/`rc_atomic` split (B3.3, `[RC_STATS]`) says *how
//! many* RC ops stay atomic, but not *where*; 0526/0528 need the *sites* of the
//! residual atomic ops to target the right cells (I3, `tests/plan/
//! s105-residual-attribution.md` §1.1). This module is the structural **twin** of
//! `compiler::control_flow::utilization`'s `[SPARK_SITE_STATS]` registry: a gated,
//! compile-time `BTreeMap` populated at the confinement-decision seam
//! (`FnCompiler::rc_atomicity_for_node`, the live `node_confined` consumer) and
//! dumped by a backend-side `atexit` hook.
//!
//! **Codegen-time, host-side, byte-identical-off.** The map push happens while the
//! backend *lowers* the program (exactly like the `tally_rc_emit` counter) — NO
//! emitted IR — so with `CRANELISP_RC_STATS` unset the compiled code is
//! byte-identical. Off ⇒ one `LazyLock<bool>` check at each `rc_atomicity_for_node`
//! and no map touch. Honest for `--run`/JIT (compile + run share the process);
//! honestly empty under `--link` (the linked binary did no codegen). Because the
//! map lives backend-side and is dumped by a backend-side `atexit` — NOT via the
//! `cranelisp-intrinsics::rc` print surface — N3 does **not** re-open the h2-RED
//! counter-surface seam (§13.2.2 "backend-side-read caveat").
//!
//! Apportioned by the FINE probes (`CRANELISP_NONATOMIC_RC` +
//! `CRANELISP_CAPTURE_BORROW`), never by `CRANELISP_NO_OWNERSHIP` (§3.1.6-R3): the
//! harness reads this dump under the fine oracles, not the coarse switch.

use std::collections::BTreeMap;
use std::sync::{LazyLock, Mutex, Once};

use cranelisp_types::{ModuleFullPath, Span, Symbol};

/// The confinement classification of a residual RC site: `Confined` ⇒ the op was
/// lowered on the non-atomic arm (`confined = Some(true)`); `Crossing` ⇒ it stayed
/// atomic (`confined = Some(false)` OR the fact was absent / analysis off ⇒
/// conservative atomic). The Crossing sites are exactly the residual-atomic-RC
/// targets 0526/0528 want.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ConfinementClass {
    Confined,
    Crossing,
}

impl ConfinementClass {
    /// Map the `node_confined` fact to a class: `Some(true)` ⇒ Confined (non-atomic);
    /// `Some(false)` (Crossing) / `None` (absent / analysis off) ⇒ Crossing (atomic) —
    /// the exact mapping `rc_atomicity_for_node` uses for the atomicity verdict.
    pub(crate) fn from_confined(confined: Option<bool>) -> Self {
        match confined {
            Some(true) => ConfinementClass::Confined,
            _ => ConfinementClass::Crossing,
        }
    }

    fn label(self) -> &'static str {
        match self {
            ConfinementClass::Confined => "Confined",
            ConfinementClass::Crossing => "Crossing",
        }
    }
}

/// One recorded RC site: its confinement class plus the number of confinement-
/// classified RC ops emitted there (`ops`). A site's class is fixed by its node's
/// `confined` fact, so it is recorded once and reasserted on each op.
struct RcSiteRecord {
    class: ConfinementClass,
    ops: u64,
}

/// site-id (`module/fn@start..end`) → record. `BTreeMap` for a stable sorted dump.
static RC_SITE_STATS: LazyLock<Mutex<BTreeMap<String, RcSiteRecord>>> =
    LazyLock::new(|| Mutex::new(BTreeMap::new()));

static RC_SITE_ATEXIT: Once = Once::new();

/// Gated on `CRANELISP_RC_STATS` (the same env as the `[RC_STATS]` line and the
/// `[SPARK_SITE_STATS]` registry's `CRANELISP_SPARK_STATS` sibling). Read once into
/// a `LazyLock<bool>`; when on, registers the `atexit` dump. Off ⇒ one bool check
/// per call, no map, no dump ⇒ byte-identical-off.
fn rc_site_stats_enabled() -> bool {
    static E: LazyLock<bool> = LazyLock::new(|| {
        let on = std::env::var_os("CRANELISP_RC_STATS").is_some();
        if on {
            RC_SITE_ATEXIT.call_once(|| unsafe {
                libc::atexit(dump_rc_site_stats);
            });
        }
        on
    });
    *E
}

/// Record one confinement-classified RC op at the emitting site, IF the stats gate
/// is on. Called from `FnCompiler::rc_atomicity_for_node` — the live `node_confined`
/// consumer, where the emitting node's span, the enclosing fn FQ, and the
/// confinement class are all in hand. Off ⇒ returns after one bool check (no map).
pub(crate) fn record_rc_site_if_enabled(
    module: &ModuleFullPath,
    fn_name: Option<&Symbol>,
    span: Span,
    confined: Option<bool>,
) {
    if !rc_site_stats_enabled() {
        return;
    }
    let site_id = match fn_name {
        Some(f) => format!("{module}/{f}@{}..{}", span.start, span.end),
        None => format!("{module}/<anon>@{}..{}", span.start, span.end),
    };
    record(site_id, ConfinementClass::from_confined(confined));
}

/// Internal: register/advance one site's op count. Split out (no gate, no I/O) so
/// the tally logic is unit-testable without the process-global env / `atexit`.
fn record(site_id: String, class: ConfinementClass) {
    let mut m = RC_SITE_STATS.lock().unwrap();
    let e = m.entry(site_id).or_insert(RcSiteRecord { class, ops: 0 });
    e.ops += 1;
}

/// Dump the per-site records + the Crossing/Confined cell tally at process exit.
/// One line per site, then one aggregate line. Sites are the residual-atomic-RC
/// attribution substrate; the aggregate cell counts feed the I3 Crossing-vs-Confined
/// read.
extern "C" fn dump_rc_site_stats() {
    let m = RC_SITE_STATS.lock().unwrap();
    let mut confined_cells: u64 = 0;
    let mut crossing_cells: u64 = 0;
    for (id, r) in m.iter() {
        match r.class {
            ConfinementClass::Confined => confined_cells += 1,
            ConfinementClass::Crossing => crossing_cells += 1,
        }
        eprintln!(
            "[RC_SITE_STATS] site={} class={} ops={}",
            id,
            r.class.label(),
            r.ops
        );
    }
    eprintln!("[RC_SITE_STATS] confined_cells={confined_cells} crossing_cells={crossing_cells}");
}

#[cfg(test)]
mod tests {
    use super::*;

    // spec: design/backend/ownership-codegen.md §13.2.2 N3 — the fact→class mapping
    // matches `rc_atomicity_for_node`: Some(true) ⇒ Confined (non-atomic); Some(false)
    // and None (absent / analysis off) ⇒ Crossing (residual atomic).
    #[test]
    fn n3_confinement_class_maps_the_confined_fact() {
        assert_eq!(
            ConfinementClass::from_confined(Some(true)),
            ConfinementClass::Confined
        );
        assert_eq!(
            ConfinementClass::from_confined(Some(false)),
            ConfinementClass::Crossing
        );
        assert_eq!(
            ConfinementClass::from_confined(None),
            ConfinementClass::Crossing
        );
    }

    // spec: design/backend/ownership-codegen.md §13.2.2 N3 — a site accumulates its
    // op count; repeated ops at the same site advance the tally, not the cell count.
    #[test]
    fn n3_record_accumulates_ops_per_site() {
        // Unique site ids so parallel tests never collide on the global map.
        let site = "m/f@1..2 [n3_accumulates]".to_string();
        record(site.clone(), ConfinementClass::Crossing);
        record(site.clone(), ConfinementClass::Crossing);
        record(site.clone(), ConfinementClass::Crossing);
        let m = RC_SITE_STATS.lock().unwrap();
        let r = m.get(&site).expect("site recorded");
        assert_eq!(r.ops, 3, "three ops at one site advance its op tally to 3");
        assert_eq!(
            r.class,
            ConfinementClass::Crossing,
            "the site's class is fixed by its fact"
        );
    }

    // spec: design/backend/ownership-codegen.md §13.2.2 N3 — NEGATIVE: Confined and
    // Crossing are distinct cells; a Confined site does not fold into the Crossing
    // tally (the split is the whole point of the residual-atomic attribution).
    #[test]
    fn n3_confined_and_crossing_are_distinct_cells() {
        let confined_site = "m/g@3..4 [n3_distinct_confined]".to_string();
        let crossing_site = "m/g@5..6 [n3_distinct_crossing]".to_string();
        record(confined_site.clone(), ConfinementClass::Confined);
        record(crossing_site.clone(), ConfinementClass::Crossing);
        let m = RC_SITE_STATS.lock().unwrap();
        assert_eq!(
            m.get(&confined_site).unwrap().class,
            ConfinementClass::Confined
        );
        assert_eq!(
            m.get(&crossing_site).unwrap().class,
            ConfinementClass::Crossing
        );
        assert_ne!(
            m.get(&confined_site).unwrap().class,
            m.get(&crossing_site).unwrap().class,
            "a Confined site must not be classified Crossing"
        );
    }

    // spec: design/backend/ownership-codegen.md §13.2.2 N3 — zero-cost-off: with
    // `CRANELISP_RC_STATS` unset, `record_rc_site_if_enabled` records nothing (the
    // gate short-circuits before any map touch). Uses a unique site id that must be
    // absent afterward. (Canonical `cargo nextest` runs with the env unset.)
    #[test]
    fn n3_record_if_enabled_is_a_noop_when_stats_off() {
        // Guard: this test is only meaningful with the stats env unset (the canonical
        // suite condition); if a run sets it, skip rather than falsely assert.
        if std::env::var_os("CRANELISP_RC_STATS").is_some() {
            return;
        }
        let module = ModuleFullPath::from("m");
        let fname = Symbol::from("noop_probe");
        record_rc_site_if_enabled(&module, Some(&fname), Span::new(7, 8), Some(false));
        let site = "m/noop_probe@7..8".to_string();
        let m = RC_SITE_STATS.lock().unwrap();
        assert!(
            m.get(&site).is_none(),
            "with the stats gate off, no site is recorded (byte-identical-off, zero map touch)"
        );
    }
}
