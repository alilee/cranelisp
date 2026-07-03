//! Ownership-inference carrier types — the typecheck→backend memory-model
//! contract (increment I, S102 CS-A).
//!
//! This module is **carrier definition only**: the [`Mode`] lattice, the
//! per-callable [`ModeSummary`], and the master analysis-off toggle. No
//! analysis logic lives here — the fixpoint that *produces* summaries is
//! `cranelisp-typecheck`'s `pass5_ownership`
//! (`design/typecheck/ownership-inference.md`); the mechanisms that *consume*
//! them are backend emission (`design/backend/ownership-codegen.md`). The
//! architectural spine — the two-class contract (ABI-bearing vs advisory),
//! monotone soundness, and the field-by-field rationale — is
//! `design/arch/ownership-inference.md` §3 (esp. §3.3, the designed carrier).
//!
//! # The two-class contract (spine §3.1/§3.2, R1)
//!
//! - **ABI-bearing half** (`param_modes`, `result`): caller and callee MUST
//!   agree — a mode-vector mismatch is a leak or a double-free. This half
//!   joins the R3 redefinition summary-diff gate ([`ModeSummary::abi_eq`])
//!   and the ABI-epoch slot-versioning discipline (spine §5.6).
//! - **Advisory half** (`param_flow`, `spark_ops`, `result_unique`):
//!   may-optimize permissions. Ignoring any or all of them is correct, only
//!   slower.
//!
//! # Monotone defaults — ⊤-on-absence lives HERE and only here
//!
//! Absence at every level means the Decision-24 conservative point:
//! `mode_summary: None` on an entry, an empty/short vector inside a summary,
//! or an old cache with no field at all — every one of them MUST read as
//! `Owned` / `Retained` / spark-ops-possible through the conservative-read
//! accessors ([`ModeSummary::param_mode`], [`ModeSummary::param_flow`],
//! [`ModeSummary::spark_op`]). **No consumer indexes the vectors directly**
//! (Principles 7 + 18 — one home for the ⊤ rule; both typecheck and backend
//! read through these accessors).
//!
//! # The master toggle
//!
//! [`ownership_analysis_off`] is the read-once `CRANELISP_NO_OWNERSHIP` gate
//! (`design/backend/ownership-codegen.md` §2.1 — one switch, producer-primary
//! enforcement). It lives in this crate because BOTH producers (typecheck's
//! pass entry) and consumers (backend's cache-manifest global key + emission
//! gates) must observe one consistent polarity, and `cranelisp-types` is the
//! only shared root (Principle 7 — two independent readers of one env name is
//! the mirror class; typecheck cannot depend on backend). Relocated from
//! `cranelisp-backend/src/cache/manifest.rs` at S102 CS-A (the needs-list
//! item-12 ruling, `design/typecheck/ownership-inference.md` §13.1).

use std::sync::OnceLock;

use serde::{Deserialize, Serialize};

/// Per-parameter access mode — the lattice `Copy ⊑ Borrowed ⊑ Owned`
/// (`design/arch/ownership-inference.md` §2.1).
///
/// All three points exist from day one even though the increment-I classifier
/// mints `Copy` for scalars only — the contract never migrates, only emitted
/// precision grows (spine §3.5/§7). `Unique` is deliberately NOT a mode:
/// uniqueness is call-site-dynamic, not static ABI (spine R4).
///
/// Widening toward `Owned` is always sound (monotone soundness, spine §6.1);
/// `Owned` is the `Default` — the Decision-24 conservative point.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub enum Mode {
    /// Value-representation eligible — no RC identity at all (scalars in
    /// increment I; Copy-flattened ADTs are increment II, spine §6.3).
    Copy,
    /// Callee only reads; caller retains ownership and emits no transfer inc,
    /// callee emits no param dec.
    Borrowed,
    /// The Decision-24 consuming convention — caller incs (transfers), callee
    /// decs. The conservative ⊤ point.
    #[default]
    Owned,
}

/// What a callable's result is, relative to its parameters
/// (`design/arch/ownership-inference.md` §4.4 — borrow-through-projection).
///
/// ABI-bearing exactly as the param vector is: whether a returned reference is
/// owned by the caller (caller decs) or a borrowed view (caller must not dec)
/// is a caller/callee agreement (spine §3.3, the 0467 folding rationale).
/// `Fresh` is the `Default` — the Decision-24 as-built convention.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub enum ResultMode {
    /// The result is a fresh caller-owned value (Decision-24 as-built).
    #[default]
    Fresh,
    /// The result is a borrowed view rooted in param *i* (e.g. an accessor's
    /// projection) — rc-free against the root's lifetime.
    ProjectionOf(usize),
    /// The result IS param *i*, returned unchanged (the extern audit's
    /// `string-identity` case).
    AliasOf(usize),
}

/// Where an `Owned` parameter's reference goes inside the callee — the
/// advisory fact that makes the escape query interprocedural
/// (`design/typecheck/ownership-inference.md` §2.2: without it,
/// `(defn keep [x] (Some x))` and `(str-len s)` are indistinguishable at the
/// call site).
///
/// `Retained` is the `Default` — the conservative "may be kept anywhere"
/// point; ignoring the field entirely is sound.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub enum ParamFlow {
    /// The callee consumes the reference (dec / drop); it does not outlive
    /// the call.
    Consumed,
    /// The reference flows into the callee's result (constructor-style).
    IntoResult,
    /// The callee may retain the reference beyond the call — the
    /// conservative ⊤ point.
    #[default]
    Retained,
}

/// Per-callable ownership summary — the typecheck→backend contract carrier
/// (`design/arch/ownership-inference.md` §3.3, enriched shape).
///
/// Rides (a) the callable [`DefKind`](crate::DefKind) variants' `mode_summary`
/// slot (persisted into `.meta.json`; read via
/// [`ModuleEntry::mode_summary`](crate::ModuleEntry::mode_summary)), and
/// (b) [`MonoDefnVariant.mode_summary`](crate::MonoDefnVariant) for the
/// compile in hand. The SAME type carries `DefKind::Primitive`'s hand-declared
/// fact-table payload (spine §3.1(a)) — the pass cannot tell a declared leaf
/// from an inferred summary except by `DefKind` (Principle 19).
///
/// Full `Eq` is load-bearing for the fixpoint's change detection: an
/// advisory-half change must re-enter callers too
/// (`design/typecheck/ownership-inference.md` §13.1 item 2).
///
/// Serde: every field is `#[serde(default)]`; a bare `{}` deserialises to
/// [`ModeSummary::default`] — the Decision-24 conservative point — and short
/// vectors read as conservative through the accessors. Old caches and
/// unresolved edges therefore deserialise to today's behaviour (strict
/// additivity, spine §3.3).
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct ModeSummary {
    // --- ABI-bearing half (input to the R3 summary-diff gate + §5.6 slot
    // versioning; compared by `abi_eq`) ---
    /// One [`Mode`] per parameter, positional. Read via [`Self::param_mode`]
    /// (missing/short ⇒ `Owned`).
    #[serde(default)]
    pub param_modes: Vec<Mode>,
    /// The result mode (spine §4.4). Absent ⇒ `Fresh`.
    #[serde(default)]
    pub result: ResultMode,

    // --- Advisory analysis-fact half (sound to ignore) ---
    /// Per param: where an `Owned` param's reference goes. Read via
    /// [`Self::param_flow`] (missing/short ⇒ `Retained`).
    #[serde(default)]
    pub param_flow: Vec<ParamFlow>,
    /// Per param: whether the callee may run RC ops on it off the calling
    /// strand (the confinement axis, spine §2.3). Read via
    /// [`Self::spark_op`] (missing/short ⇒ `true`).
    #[serde(default)]
    pub spark_ops: Vec<bool>,
    /// Increment II (result-uniqueness chaining, spine §10 item 5(b));
    /// emitted `false` throughout increment I.
    #[serde(default)]
    pub result_unique: bool,
}

impl ModeSummary {
    /// The mode of param `i` — **the** ⊤-on-absence read (missing/short ⇒
    /// [`Mode::Owned`]). Consumers MUST NOT index `param_modes` directly.
    pub fn param_mode(&self, i: usize) -> Mode {
        self.param_modes.get(i).copied().unwrap_or(Mode::Owned)
    }

    /// The flow of param `i` — ⊤-on-absence read (missing/short ⇒
    /// [`ParamFlow::Retained`]).
    pub fn param_flow(&self, i: usize) -> ParamFlow {
        self.param_flow.get(i).copied().unwrap_or(ParamFlow::Retained)
    }

    /// Whether the callee may run RC ops on param `i` off the calling strand
    /// — ⊤-on-absence read (missing/short ⇒ `true`, i.e. assume Crossing).
    pub fn spark_op(&self, i: usize) -> bool {
        self.spark_ops.get(i).copied().unwrap_or(true)
    }

    /// ABI-surface equality — compares `(param_modes, result)` ONLY, through
    /// the ⊤-on-absence read (so `[]` and `[Owned, Owned]` are ABI-equal).
    ///
    /// The single definition serving the R3 summary-diff gate (`/int`'s
    /// `AbiSurface` comparison) and every future consumer, so the ABI half is
    /// never hand-picked field-by-field at two sites
    /// (`design/typecheck/ownership-inference.md` §13.1 item 5 — the mirror
    /// hazard). Advisory fields are deliberately NOT compared: an
    /// advisory-only change is never ABI-changing.
    pub fn abi_eq(&self, other: &Self) -> bool {
        let n = self.param_modes.len().max(other.param_modes.len());
        (0..n).all(|i| self.param_mode(i) == other.param_mode(i)) && self.result == other.result
    }

    /// `true` iff this summary's ABI half is the Decision-24 conservative
    /// point (all params `Owned`, result `Fresh`) — i.e. ABI-equivalent to
    /// carrying no summary at all.
    pub fn is_abi_conservative(&self) -> bool {
        self.param_modes.iter().all(|m| *m == Mode::Owned) && self.result == ResultMode::Fresh
    }

    /// ABI-surface equality over optional summaries, treating `None` as the
    /// conservative point — the one home for the `None ≡ all-Owned/Fresh`
    /// equivalence the R3 gate needs (a redefinition that goes from "no
    /// summary" to an all-conservative summary is NOT an ABI change).
    pub fn abi_eq_opt(a: Option<&ModeSummary>, b: Option<&ModeSummary>) -> bool {
        match (a, b) {
            (None, None) => true,
            (Some(s), None) | (None, Some(s)) => s.is_abi_conservative(),
            (Some(a), Some(b)) => a.abi_eq(b),
        }
    }
}

/// Read-once gate for the **`CRANELISP_NO_OWNERSHIP`** master analysis-off
/// toggle (`design/backend/ownership-codegen.md` §2.1 — one switch; the same
/// read-once `OnceLock` pattern as `CRANELISP_NONATOMIC_RC`, so one process
/// observes one consistent polarity).
///
/// Semantics: when set, force the conservative point everywhere. Enforcement
/// is **producer-primary** — with the toggle set, typecheck's
/// `pass5_ownership` returns at entry and emits NOTHING (no summaries ⇒ every
/// consumer is at the Decision-24 conservative point with zero consumer-side
/// branching; `.meta.json` is field-identical to the pre-analysis shape —
/// `design/typecheck/ownership-inference.md` §13.5). Backend consumers: the
/// cache-manifest global key (`CacheManifest::ownership_disabled`,
/// `cranelisp-backend/src/cache/manifest.rs` — polarity flip ⇒ wholesale
/// invalidation) and the increment-I emission gates, both delegating here.
///
/// Hosted in `cranelisp-types` (not backend) per the S102 CS-A item-12
/// ruling: both typecheck and backend read one polarity through one function
/// (Principle 7); this crate is their only shared root.
pub fn ownership_analysis_off() -> bool {
    static E: OnceLock<bool> = OnceLock::new();
    *E.get_or_init(|| std::env::var_os("CRANELISP_NO_OWNERSHIP").is_some())
}

#[cfg(test)]
mod tests;
