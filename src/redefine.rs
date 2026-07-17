//! Dependent-recompilation session transaction — the S101 R3 machinery
//! (`design/int/session-transaction.md`, authoritative; `repl/spec.md` §18 is
//! the normative UX).
//!
//! One turn's flow (design §1): a redefinition commits through the summary-diff
//! gate in `worker::commit_staging_to_live` (§2 — the single slot-policy
//! authority, producing [`RedefinitionOutcome`]s), the eval path runs
//! [`run_transaction`] for each `AbiChanging` outcome after the target's own
//! codegen succeeds (§13), and the transaction derives the reverse dependency
//! index on demand (§3.3), computes the affected-set closure, condenses SCCs,
//! walks them reverse-topologically (callees before callers, §4.1), re-typechecks
//! each visited SCC from its stored sexps (§4.2), and marks members that no
//! longer typecheck BROKEN (§5) — entry retained, code moved to the session
//! retention pool, slot patched in place to a per-symbol trap stub
//! (`cranelisp_backend::compile_trap_stub`).
//!
//! The **stage-M ABI comparand is the type scheme only** (design §2.2): the
//! [`AbiSurface`] is the alpha-canonical fully-qualified rendering the REPL
//! already uses for scheme display (`display::format_scheme_type`), so two
//! checks of the same source compare equal regardless of type-variable ids.
//! Increment I extends `AbiSurface::of` with the ABI-bearing `ModeSummary`
//! half (design §2.4) without restructuring the gate or the transaction.
//!
//! Slot-less pass-through (design §4.1, the FIXME-0473 ruling): a slot-less
//! closure member (constrained/generic template, `Overloaded` base —
//! `callable_got_slot().is_none()`) never gates the walk. It is re-typechecked
//! in its SCC position, but its callers are visited unconditionally, whatever
//! its own outcome; a BROKEN slot-less member takes a registry record only
//! (no code to retain, no slot to trap-patch — §5.1 degenerate arm).

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Mutex;

use cranelisp_types::{
    CranelispError, DefKind, ErrorLocation, FQSymbol, ModuleEntry, ModuleFullPath,
    ModuleStrategy, Sexp, Span, Symbol, UserFnState, GOT_TABLE_SIZE,
};

use crate::code::{Code, SessionSymbolTable};
use crate::session_v4::CompilerSession;
use crate::styled::{render, Role, StyledDoc};

type SymbolTables = dashmap::DashMap<ModuleFullPath, SessionSymbolTable>;

// ---------------------------------------------------------------------------
// AbiSurface — the stage-M summary-diff comparand (design §2.2)
// ---------------------------------------------------------------------------

/// The alpha-canonical rendering of an entry's fully-qualified type scheme —
/// the stage-M ABI comparand. Raw `Scheme` structs must NOT be compared
/// directly (two checks of the same source produce different type-variable
/// ids); `display::format_scheme_type` normalises vars to consecutive letters
/// and fully qualifies type names, so equal-shaped schemes render identically.
///
/// What is deliberately NOT in the comparand: docstrings, param names,
/// visibility, `seq`, the body — a body-only edit is `AbiPreserving`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AbiSurface(String);

impl AbiSurface {
    /// The ABI surface of a `Def` entry, or `None` for non-`Def` entries.
    pub(crate) fn of(entry: &ModuleEntry<Code>) -> Option<AbiSurface> {
        match entry {
            ModuleEntry::Def { scheme, .. } => {
                Some(AbiSurface(crate::display::format_scheme_type(scheme)))
            }
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// RedefKind + classification (design §2.1/§2.2)
// ---------------------------------------------------------------------------

/// The commit gate's three-way classification of a staged callable `Def`
/// against the prior live entry under the same name (design §2.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RedefKind {
    /// No prior live `Def` under this name — today's fresh-allocate path.
    New,
    /// Prior exists; ABI surface unchanged — today's reuse-and-patch path
    /// (late binding preserved; the L-D1 fast path).
    AbiPreserving,
    /// Prior exists; ABI surface changed — fresh slot, old slot frozen with
    /// its code retained (design §7.1).
    AbiChanging,
}

/// One committed symbol's classification, riding `ProcessedCluster` from the
/// commit gate back to the driver (design §13).
#[derive(Debug, Clone)]
pub(crate) struct RedefinitionOutcome {
    pub fq: FQSymbol,
    pub kind: RedefKind,
    /// `true` iff both the prior and staged entries are concrete single-sig
    /// `UserFn` `Def`s — the shape per-symbol precision covers at stage M
    /// (design §2.2/§10 T1). `false` routes the target conservatively
    /// (today's reuse-and-patch; no per-symbol transaction).
    pub per_symbol: bool,
    /// `true` iff the committed name had a prior live `Def` (any slot shape —
    /// S102 §9.1.1 gate widening). The [`RedefKind`] alone cannot carry this:
    /// a slot-less prior classifies `New` (no frozen slot to version), which
    /// conflates "genuinely new" with "template redefinition" — exactly the
    /// T1 shape the §18.1.1 downgrade report must see. A prior non-`Def`
    /// (e.g. an `Import` shadowed by a defn — 0484's territory) is `false`.
    pub prior_was_def: bool,
    /// The prior live slot the commit displaced (`None` when the prior was
    /// slot-less — a template redefined). Read by the F2 slot-refined
    /// [`is_t1_downgrade`] trigger (S103, FIXME 0507 Issue 1).
    pub old_slot: Option<usize>,
    /// The committed live slot (`None` for a slot-less staged entry — the
    /// template/overloaded T1 shapes have no callable slot to commit). Read by
    /// the F2 slot-refined [`is_t1_downgrade`] trigger.
    pub new_slot: Option<usize>,
}

/// The §18.1.1 downgrade-report trigger (design `s102-defect-wave.md` §1 /
/// `session-transaction.md` §9.1.1): the commit took a redefinition-of-a-
/// prior-`Def` route outside per-symbol precision — the T1 reuse-and-patch
/// path. The trigger is the ROUTE, not the surface diff: even a scheme-equal
/// redefinition of a polymorphic template leaves previously-minted mono
/// instances (and their compiled callers) on the old body. Never fires for
/// genuine `New` (no prior `Def`, incl. the prior-`Import` shadow shape),
/// never for per-symbol outcomes (the transaction handles those — mutual
/// exclusion with `recompiled:`/`broken:` by construction), never for
/// gate-exempt internals (`__expr`/`__macro_*`).
///
/// **F2 slot refinement (S103, FIXME 0507 Issue 1).** The bare
/// `prior_was_def && !per_symbol` predicate over-fires for a **slotted prior
/// replaced by a slotted staged entry** outside per-symbol precision — the
/// constructible shape is a `deftype` ctor re-entry (slotted
/// `DefKind::Constructor`): the commit **reuses** the prior slot and patches
/// code in place, so compiled callers dispatch through the same GOT slot and
/// **do** pick up the new definition at their next call. Naming them `stale:`
/// (or reloading their module) would violate §18.1.1's negative MUST. Requiring
/// a slot-shape change (`old_slot.is_none() || new_slot.is_none()`) keeps every
/// designed T1 cell — slot-less **staged** (template/overloaded shapes,
/// `new_slot: None`) and slot-less **prior** (concrete-over-template mint
/// staleness, `old_slot: None`) — and excludes the slotted→slotted
/// late-binding case. This same predicate gates the §10 T1 full-cure driver.
pub(crate) fn is_t1_downgrade(o: &RedefinitionOutcome) -> bool {
    o.prior_was_def
        && !o.per_symbol
        && !is_gate_exempt_internal(o.fq.symbol.as_ref())
        && (o.new_slot.is_none() || o.old_slot.is_none())
}

/// Does this commit outcome clear the symbol's BROKEN record (§18.6 recovery
/// direction 1 — an ordinary redefinition of a broken symbol recovers it)?
///
/// S102 W5 review F1: keying on `kind != New` alone missed the two
/// `New`-classified REDEFINITION shapes that carry `prior_was_def: true`
/// (a slot-less prior `Def` — template redefined, or a concrete fn displaced
/// by a template — classifies `New` because there is no frozen slot to
/// version), so a broken slot-less template redefined green kept printing
/// "is broken by …". A genuinely-new definition (no prior `Def`, incl. the
/// prior-`Import` shadow shape) has no broken record to clear — the remove
/// is a no-op either way, but the predicate states the intent: every
/// redefinition-of-a-prior-Def clears.
pub(crate) fn outcome_clears_broken(o: &RedefinitionOutcome) -> bool {
    o.kind != RedefKind::New || o.prior_was_def
}

/// True iff the entry is a concrete single-sig `UserFn` `Def` — the target
/// kind per-symbol precision covers at stage M (design §2.2).
pub(crate) fn is_concrete_userfn(entry: &ModuleEntry<Code>) -> bool {
    matches!(
        entry,
        ModuleEntry::Def { kind, .. }
            if matches!(kind.as_ref(), DefKind::UserFn { fn_state: UserFnState::Concrete { .. } })
    )
}

/// True for internal compiler artifacts the gate must never classify as
/// ABI-changing: the synthetic `__expr` wrapper (a fresh scheme every
/// expression turn — fresh-slot churn would exhaust the GOT) and macro clause
/// defns (`__macro_{name}_clause_{idx}` — internal dispatch, never a user
/// redefinition target).
pub(crate) fn is_gate_exempt_internal(name: &str) -> bool {
    name == crate::worker::SYNTHETIC_EXPR_WRAPPER || name.starts_with("__macro_")
}

/// The summary-diff gate's pure classification (design §2): prior live entry
/// (if any) vs the staged entry. Returns the [`RedefKind`] plus the
/// `per_symbol` precision flag (see [`RedefinitionOutcome::per_symbol`]).
///
/// Routing outside per-symbol precision (design §10 T1 — the redefined
/// target is not a concrete `UserFn` on both sides) classifies as
/// `AbiPreserving` with `per_symbol: false`: the commit keeps today's
/// reuse-and-patch slot policy and the driver runs no per-symbol transaction.
pub(crate) fn classify_redefinition(
    name: &str,
    prior: Option<&ModuleEntry<Code>>,
    staged: &ModuleEntry<Code>,
) -> (RedefKind, bool) {
    let Some(prior) = prior else {
        return (RedefKind::New, false);
    };
    // A prior non-Def (e.g. an Import binding now shadowed by a local defn)
    // carries no ABI surface of its own — fresh allocation, like New.
    if !matches!(prior, ModuleEntry::Def { .. }) {
        return (RedefKind::New, false);
    }
    if is_gate_exempt_internal(name) {
        return (RedefKind::AbiPreserving, false);
    }
    // A prior slot-less Def (template promoted/replaced) has no frozen slot
    // to version — fresh allocation.
    if prior.callable_got_slot().is_none() {
        return (RedefKind::New, false);
    }
    let per_symbol = is_concrete_userfn(prior) && is_concrete_userfn(staged);
    if !per_symbol {
        // T1: conservative — today's reuse-and-patch (no ABI-epoch versioning
        // for non-concrete-UserFn targets at stage M).
        return (RedefKind::AbiPreserving, false);
    }
    if AbiSurface::of(prior) == AbiSurface::of(staged) {
        (RedefKind::AbiPreserving, true)
    } else {
        (RedefKind::AbiChanging, true)
    }
}

// ---------------------------------------------------------------------------
// GOT exhaustion guard (S101 accumulated obligation 3)
// ---------------------------------------------------------------------------

/// Allocate a live GOT slot, adding the session's user-facing remedy to a
/// module-local exhaustion.
///
/// `SymbolTable::allocate_got_slot` is now the fallible seam (S111 R7): once the
/// fixed `GOT_TABLE_SIZE`-slot slab is full it returns `GotExhausted` rather
/// than overflowing (the former unchecked monotone bump risked a release-mode
/// OOB `store_slot`/`load_slot`). The manual pre-check that used to live here is
/// gone; this wrapper only re-messages the seam error with the session-specific
/// "restart to reclaim frozen slots" remedy (the redefinition chokepoint is the
/// one path where a long dev session with many ABI-changing redefinitions
/// approaches the bound).
#[allow(clippy::result_large_err)] // CranelispError is the crate-wide error carrier
pub(crate) fn allocate_live_got_slot(
    live: &mut SessionSymbolTable,
    module: &ModuleFullPath,
) -> Result<usize, CranelispError> {
    live.allocate_got_slot().map_err(|_e| CranelispError::CodegenError {
        message: format!(
            "GOT slot table exhausted for module '{module}' \
             ({GOT_TABLE_SIZE} slots): too many definitions and \
             ABI-changing redefinitions in one session. Restart the \
             session to reclaim frozen slots.",
        ),
        location: ErrorLocation::from_span(Span::SYNTHETIC),
    })
}

// ---------------------------------------------------------------------------
// Retention pool + broken registry (design §5.1, §6.1)
// ---------------------------------------------------------------------------

/// One retained code handle — frozen-slot supersession (`trap_msg: None`) or
/// a trap stub paired with the provenance buffer its `iconst`'d address
/// points into (`trap_msg: Some`). Appended-only, session-lifetime: entries
/// are never freed on recovery (design §6.2 — a broken symbol recovered with
/// a new ABI keeps its old slot on the trap stub permanently, and even a
/// same-ABI recovery cannot prove no detached strand is mid-call in the
/// stub). Reclaimed wholesale at session end (the `kept_dlls` precedent).
pub(crate) struct RetainedCode {
    /// Whose supersession/trap this is (observability).
    #[allow(dead_code)]
    pub fq: FQSymbol,
    #[allow(dead_code)]
    pub module: ModuleFullPath,
    /// The frozen or trap-patched slot (`None` for code displaced off a
    /// slot-less entry on the module-grain Replace path).
    #[allow(dead_code)]
    pub slot: Option<usize>,
    /// The retention handle (`Arc<Jit>`/`Arc<Linker>` keeps pages mapped).
    #[allow(dead_code)]
    pub code: Code,
    /// `Some` ⇔ `code` is a trap stub whose baked address points into this
    /// buffer. Structural pairing (Principle 18): the message and the stub
    /// ride the same entry, so neither can outlive or underlive the other.
    /// A `Box<str>`'s heap buffer address is stable under `Vec` growth.
    /// (Never read at run time — its JOB is ownership: the stub's baked
    /// pointer reads the bytes.)
    #[allow(dead_code)]
    pub trap_msg: Option<Box<str>>,
}

impl RetainedCode {
    /// A frozen-supersession pool entry (`trap_msg: None`) for a `Code`
    /// displaced from `module`/`name` — the shared shape of the four
    /// displace-to-pool sites (the commit gate's AbiChanging freeze and its
    /// slot-less-staged displacement in `worker::commit_staging_to_live`,
    /// `process_form::clear_module_codegen`, `session_v4::reload_module`,
    /// and [`mark_broken`]'s displaced-code half). The trap-stub shape
    /// (`trap_msg: Some`, pairing the stub with its provenance buffer) is
    /// constructed literally at its single site in [`mark_broken`].
    pub(crate) fn frozen(
        module: &ModuleFullPath,
        name: &Symbol,
        slot: Option<usize>,
        code: Code,
    ) -> Self {
        Self {
            fq: FQSymbol {
                module: module.clone(),
                symbol: name.clone(),
            },
            module: module.clone(),
            slot,
            code,
            trap_msg: None,
        }
    }
}

/// The session retention pool (`SharedState.retained_code`).
pub(crate) type RetentionPool = Mutex<Vec<RetainedCode>>;

/// Symbol-level BROKEN state + provenance (design §5.1; `repl/spec.md` §18.4).
#[derive(Debug, Clone)]
pub(crate) struct BrokenInfo {
    /// The redefined symbol that broke this one — depth-1 provenance, always
    /// the transaction target (design §5.2). Rendered fully qualified.
    pub broken_by: FQSymbol,
    /// The §5.1-format error re-typechecking produced (one line).
    pub original_error: String,
    /// The full trap message: `{broken} is broken by the redefinition of
    /// {cause}: {original error}` — also the buffer text baked into the stub.
    #[allow(dead_code)] // the trap stub's copy is the runtime reader
    pub provenance: String,
}

/// The broken registry type (`SharedState.broken`).
pub(crate) type BrokenRegistry = dashmap::DashMap<FQSymbol, BrokenInfo>;

/// Compose the normative trap-message / provenance string
/// (`repl/spec.md` §18.5): `{broken} is broken by the redefinition of
/// {cause}: {original error}` — fully-qualified names.
pub(crate) fn compose_provenance(
    broken: &FQSymbol,
    cause: &FQSymbol,
    original_error: &str,
) -> String {
    format!("{broken} is broken by the redefinition of {cause}: {original_error}")
}

/// Mark a closure member BROKEN (design §5.1).
///
/// Slotted member: the entry stays (scheme, docstring, `ast`, `callees`
/// intact — staging was discarded on the failed re-typecheck, so live never
/// changed); its `code` moves to the retention pool; its slot is patched in
/// place to a trap stub whose provenance buffer rides the same pool entry;
/// and a registry record is inserted.
///
/// Slot-less member (the §5.1 degenerate arm, per the §4.1 pass-through
/// ruling): registry record ONLY — there is no code to retain and no slot for
/// the stub to land on. Trappability is delivered by propagation: the slotted
/// callers that consequently fail take the full marking.
pub(crate) fn mark_broken(
    tables: &SymbolTables,
    pool: &RetentionPool,
    registry: &BrokenRegistry,
    fq: &FQSymbol,
    cause: &FQSymbol,
    original_error: &str,
) {
    let provenance = compose_provenance(fq, cause, original_error);

    // Read the slot + displace the code under the table guard; release the
    // guard before compiling the stub (no DashMap guard across a JIT build).
    let slotted = tables.get_mut(&fq.module).and_then(|mut st| {
        let got = st.got.clone();
        let entry = st.symbols.get_mut(fq.symbol.as_ref())?;
        let slot = entry.callable_got_slot()?;
        let displaced = match entry {
            ModuleEntry::Def { code, .. } => code.take(),
            _ => None,
        };
        Some((slot, displaced, got))
    });

    if let Some((slot, displaced, got)) = slotted {
        let mut pool_guard = pool.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(code) = displaced {
            // Frozen supersession: the displaced code stays mapped for
            // in-flight frames / heap closures (cures the `*code = None`
            // page-free hazard — design §6.3).
            pool_guard.push(RetainedCode::frozen(&fq.module, &fq.symbol, Some(slot), code));
        }
        // The provenance buffer must live exactly as long as the stub's Code
        // handle: allocate it, bake its address, and push both PAIRED before
        // the slot is patched (nothing can invoke the stub before the
        // `store_slot` below).
        let msg: Box<str> = provenance.clone().into_boxed_str();
        match cranelisp_backend::compile_trap_stub(msg.as_ptr(), msg.len()) {
            Ok((stub_ptr, stub_code)) => {
                pool_guard.push(RetainedCode {
                    fq: fq.clone(),
                    module: fq.module.clone(),
                    slot: Some(slot),
                    code: stub_code.clone(),
                    trap_msg: Some(msg),
                });
                drop(pool_guard);
                // In-place patch — existing unrecompiled callers, wrapper
                // closures, and curried partials all reach the trap through
                // the slot they already embed (L-R1 (a)/(b)/(c)).
                got.store_slot(slot, stub_ptr);
                crate::got_trace::emit_trap_patch(&fq.module, &fq.symbol, slot, stub_ptr);
                // The entry's `code` field holds the stub's handle: the stub
                // IS the code dispatched through this slot now. Load-bearing
                // beyond bookkeeping — a `code: None` + `ast: Some` entry
                // looks "uncompiled" to `derive_codegen_batch`'s synth-def
                // sweep, which would silently RECOMPILE the broken body
                // against the new-world callee on the next eval turn
                // (unsound — the exact hole the trap exists to close) and
                // overwrite the trap patch.
                if let Some(mut st) = tables.get_mut(&fq.module)
                    && let Some(ModuleEntry::Def { code, .. }) =
                        st.symbols.get_mut(fq.symbol.as_ref())
                {
                    *code = Some(stub_code);
                }
            }
            Err(e) => {
                // Stub compilation failure: the slot keeps the old (retained)
                // code pointer — stale but memory-safe. Surface loudly.
                drop(pool_guard);
                eprintln!(
                    "warning: trap-stub compilation failed for {fq}: {e} — \
                     stale code remains callable"
                );
            }
        }
    }

    registry.insert(
        fq.clone(),
        BrokenInfo {
            broken_by: cause.clone(),
            original_error: original_error.to_string(),
            provenance,
        },
    );
}

// ---------------------------------------------------------------------------
// Reverse dependency index (design §3.3)
// ---------------------------------------------------------------------------

/// Callee → callers, derived on demand from `Def.callees` across the live
/// tables at the moment an `AbiChanging` classification fires. Never a
/// second authored store (Principle 7): a scan is correct by construction
/// against whatever the tables hold now, and costs nothing on the body-only
/// fast path (L-D1 — no incremental maintenance tax on registrations).
pub(crate) struct ReverseIndex {
    map: HashMap<FQSymbol, Vec<FQSymbol>>,
}

impl ReverseIndex {
    pub(crate) fn build(tables: &SymbolTables) -> Self {
        let mut map: HashMap<FQSymbol, Vec<FQSymbol>> = HashMap::new();
        for shard in tables.iter() {
            let module = shard.key().clone();
            for (name, entry) in shard.value().all_symbols() {
                // The synthetic `__expr` eval wrapper never joins the index as
                // a CALLER (FIXME 0491): its Def carries real callees, so it
                // would otherwise join closures, get re-typechecked/marked, and
                // leak into every report section (`broken:`/`recompiled:`/
                // `stale:` — both the break and revert directions). Safe by the
                // frozen-world argument: a stale wrapper is never re-invoked —
                // each expression turn redefines it before invoking.
                //
                // The exclusion is `__expr`-ONLY (S103, FIXME 0507 Issue 2 /
                // F3 — supersedes the "0491 rule applies identically" reading).
                // A compiled macro clause (`__macro_{name}_clause_{idx}`)
                // **persists and IS re-invoked** at the next expansion, and per
                // spec §9.3.4/§9.12 a clause body may reference a
                // dependency-module fn — so an AbiChanging redefinition of that
                // dep leaves the clause coherent-stale and, under the old
                // blanket exclusion, invisible. The feed keeps macro-clause
                // reverse edges; the render fold (`render_caller_base`) shows
                // such a caller as its owning user macro `{name}`, never the
                // raw `__macro_*` symbol (§18.1.1 no-internal-artifacts). Note
                // the predicate SPLIT: `is_gate_exempt_internal` stays the
                // TARGET exclusion at the trigger/classify sites; only the
                // CALLER/feed exclusion narrows to `__expr`.
                if name.as_ref() == crate::worker::SYNTHETIC_EXPR_WRAPPER {
                    continue;
                }
                let callees = entry.callees();
                if callees.is_empty() {
                    continue;
                }
                let caller = FQSymbol {
                    module: module.clone(),
                    symbol: name.clone(),
                };
                for callee in callees {
                    map.entry(callee.clone()).or_default().push(caller.clone());
                }
            }
        }
        // Deterministic caller order (HashMap iteration is seed-randomised).
        for callers in map.values_mut() {
            callers.sort_by(|a, b| {
                (a.module.as_ref(), a.symbol.as_ref())
                    .cmp(&(b.module.as_ref(), b.symbol.as_ref()))
            });
            callers.dedup();
        }
        ReverseIndex { map }
    }

    pub(crate) fn callers_of(&self, fq: &FQSymbol) -> &[FQSymbol] {
        self.map.get(fq).map(Vec::as_slice).unwrap_or(&[])
    }

    /// Callers of `target` and of its `$`-mangled variants (a mangled callee
    /// whose base is `target` — mono instances minted from the template),
    /// unioned, sorted, deduped (design §9.1.1: the stale-set feed is
    /// variant-aware — a caller compiled against a minted instance embeds the
    /// old chain exactly as a direct caller does).
    pub(crate) fn callers_of_with_variants(&self, target: &FQSymbol) -> Vec<FQSymbol> {
        let mut out: Vec<FQSymbol> = Vec::new();
        for (callee, callers) in &self.map {
            if callee == target || base_fq(callee) == *target {
                out.extend(callers.iter().cloned());
            }
        }
        out.sort_by(|a, b| {
            (a.module.as_ref(), a.symbol.as_ref()).cmp(&(b.module.as_ref(), b.symbol.as_ref()))
        });
        out.dedup();
        out
    }
}

/// The §18.1.1 stale set for one T1 downgrade target (design
/// `s102-defect-wave.md` §1, `session-transaction.md` §9.1.1): the DIRECT
/// reverse-edge callers of `target` and its `$`-mangled variants, restricted
/// to entries that hold compiled code (`code: Some` — "compiled callers";
/// never-compiled callers — templates, `ast`-only entries — late-bind at
/// their next mint and MUST NOT appear), reported at base-defn grain (a
/// compiled mono caller `g$Int` names `g`), target excluded, sorted/deduped.
///
/// Gate-exempt internals (`__expr`/`__macro_*`) are excluded at the FEED —
/// [`ReverseIndex::build`] never records them as callers (the 0491 rule; the
/// single exclusion authority, Principle 7, pinned by
/// `reverse_index_neg_excludes_gate_exempt_internal_callers`) — so no
/// per-consumer re-filter exists here (S102 W5 review F4: the former
/// belt-and-braces copy was unreachable and is deleted, not kept).
///
/// Pure over the tables; the on-demand [`ReverseIndex`] build runs ONLY on
/// downgrade turns, so the L-D1 pin (body-only concrete redefinitions at
/// today's cost) is untouched.
pub(crate) fn stale_callers(tables: &SymbolTables, target: &FQSymbol) -> Vec<FQSymbol> {
    let reverse = ReverseIndex::build(tables);
    let mut out: Vec<FQSymbol> = Vec::new();
    for caller in reverse.callers_of_with_variants(target) {
        // "Compiled caller" = the caller's own live entry holds compiled code.
        let compiled = tables
            .get(&caller.module)
            .and_then(|t| {
                t.get(caller.symbol.as_ref()).map(|e| {
                    matches!(e, ModuleEntry::Def { code: Some(_), .. })
                })
            })
            .unwrap_or(false);
        if !compiled {
            continue;
        }
        // Report at base grain: a `$`-mangled mono caller names its base defn;
        // a `__macro_*` clause names its owning user macro (§18.1.1). The
        // target itself (e.g. a recursive self-edge through an old mint) is not
        // a member of its own set.
        let base = render_caller_base(&caller);
        if base == *target {
            continue;
        }
        out.push(base);
    }
    out.sort_by(|a, b| {
        (a.module.as_ref(), a.symbol.as_ref()).cmp(&(b.module.as_ref(), b.symbol.as_ref()))
    });
    out.dedup();
    out
}

/// Transitive closure over reverse edges from `target` (design §4.1 step 1).
/// The target itself is NOT a member. BFS order (deterministic given the
/// index's sorted caller lists).
pub(crate) fn affected_closure(reverse: &ReverseIndex, target: &FQSymbol) -> Vec<FQSymbol> {
    let mut seen: HashSet<FQSymbol> = HashSet::new();
    let mut order: Vec<FQSymbol> = Vec::new();
    let mut queue: VecDeque<FQSymbol> = VecDeque::new();
    queue.push_back(target.clone());
    seen.insert(target.clone());
    while let Some(fq) = queue.pop_front() {
        for caller in reverse.callers_of(&fq) {
            if seen.insert(caller.clone()) {
                order.push(caller.clone());
                queue.push_back(caller.clone());
            }
        }
    }
    order
}

// ---------------------------------------------------------------------------
// SCC condensation + reverse-topological order (design §4.1 steps 2–3)
// ---------------------------------------------------------------------------

/// A closure member with the metadata the walk needs.
#[derive(Debug, Clone)]
pub(crate) struct ClosureMember {
    pub fq: FQSymbol,
    /// `callable_got_slot().is_none()` on the live entry — the §4.1
    /// pass-through discriminator (one existing accessor, no new state).
    pub slotless: bool,
    /// Forward callees restricted to the closure ∪ {target}.
    pub callees: Vec<FQSymbol>,
}

/// Tarjan SCC condensation over the closure members' forward edges. Tarjan
/// emits SCCs in reverse topological order of the condensation — each SCC
/// completes after everything it can reach — i.e. **callees before callers**,
/// exactly the walk order §4.1 requires.
pub(crate) fn condense_reverse_topo(members: &[ClosureMember]) -> Vec<Vec<usize>> {
    let index_of: HashMap<&FQSymbol, usize> =
        members.iter().enumerate().map(|(i, m)| (&m.fq, i)).collect();
    let n = members.len();
    let adj: Vec<Vec<usize>> = members
        .iter()
        .map(|m| {
            m.callees
                .iter()
                .filter_map(|c| index_of.get(c).copied())
                .collect()
        })
        .collect();

    struct Tarjan<'a> {
        adj: &'a [Vec<usize>],
        index: Vec<Option<usize>>,
        lowlink: Vec<usize>,
        on_stack: Vec<bool>,
        stack: Vec<usize>,
        next_index: usize,
        sccs: Vec<Vec<usize>>,
    }
    impl Tarjan<'_> {
        fn strongconnect(&mut self, v: usize) {
            self.index[v] = Some(self.next_index);
            self.lowlink[v] = self.next_index;
            self.next_index += 1;
            self.stack.push(v);
            self.on_stack[v] = true;
            for &w in &self.adj[v] {
                if self.index[w].is_none() {
                    self.strongconnect(w);
                    self.lowlink[v] = self.lowlink[v].min(self.lowlink[w]);
                } else if self.on_stack[w] {
                    self.lowlink[v] = self.lowlink[v].min(self.index[w].unwrap());
                }
            }
            if self.lowlink[v] == self.index[v].unwrap() {
                let mut scc = Vec::new();
                while let Some(w) = self.stack.pop() {
                    self.on_stack[w] = false;
                    scc.push(w);
                    if w == v {
                        break;
                    }
                }
                scc.sort_unstable();
                self.sccs.push(scc);
            }
        }
    }
    let mut t = Tarjan {
        adj: &adj,
        index: vec![None; n],
        lowlink: vec![0; n],
        on_stack: vec![false; n],
        stack: Vec::new(),
        next_index: 0,
        sccs: Vec::new(),
    };
    for v in 0..n {
        if t.index[v].is_none() {
            t.strongconnect(v);
        }
    }
    t.sccs
}

/// The §4.1 skip test, pure: an SCC is visited (re-typechecked) iff any of
/// its members' in-scope callees propagates. Intra-SCC callees have no
/// settled status yet (absent from `propagates`) and correctly do not count.
pub(crate) fn scc_should_visit(
    scc: &[usize],
    members: &[ClosureMember],
    propagates: &HashMap<FQSymbol, bool>,
) -> bool {
    scc.iter().any(|&i| {
        members[i]
            .callees
            .iter()
            .any(|c| propagates.get(c).copied().unwrap_or(false))
    })
}

/// The per-member propagation decision after its SCC settles (design §4.1):
///
/// - not visited (SCC skipped) → does not propagate;
/// - **slot-less** member → propagates unconditionally once visited
///   (pass-through — its own outcome, green-changed, green-unchanged, or
///   BROKEN, never gates the walk; the artifact embedding a changed callee's
///   slot is the mono instance in each caller's module);
/// - slotted, re-typechecked green → propagates iff its own gate diff was
///   `AbiChanging`;
/// - slotted, BROKEN → does not propagate (it failed before producing a new
///   ABI surface — spine §5.5 reads at slotted grain).
pub(crate) fn member_propagates(
    slotless: bool,
    visited: bool,
    green_abi_changing: Option<bool>,
) -> bool {
    if !visited {
        return false;
    }
    if slotless {
        return true;
    }
    green_abi_changing.unwrap_or(false)
}

// ---------------------------------------------------------------------------
// TransactionReport (design §9.1; repl/spec.md §18.3)
// ---------------------------------------------------------------------------

/// The transaction's report — the primary observable (L-R3 reads it, positive
/// AND negative). `recompiled` is exact by the §4.1 skip test.
#[derive(Debug)]
pub(crate) struct TransactionReport {
    pub target: FQSymbol,
    /// Exactly the members re-typechecked green (includes re-typechecked
    /// slot-less templates and recovered symbols).
    pub recompiled: Vec<FQSymbol>,
    /// Members that no longer typecheck, with the one-line original error.
    pub broken: Vec<(FQSymbol, String)>,
    /// Previously-BROKEN symbols this transaction fixed (also present in
    /// `recompiled`; kept separately for observability).
    #[allow(dead_code)]
    pub recovered: Vec<FQSymbol>,
    /// Compiled callers left on the previous definition by a §10 T1
    /// downgrade (`repl/spec.md` §18.1.1; data contract §9.1.1). Mutually
    /// exclusive with `recompiled`/`broken` by construction: per-symbol
    /// transactions never produce stale; downgrades never recompile/break.
    /// This is a KEPT section of the one transaction report — the S103 full
    /// cure recompiles exactly these callers and renders it empty
    /// (Principle 8: not throwaway machinery).
    pub stale: Vec<FQSymbol>,
}

impl TransactionReport {
    pub(crate) fn new(target: FQSymbol) -> Self {
        TransactionReport {
            target,
            recompiled: Vec::new(),
            broken: Vec::new(),
            recovered: Vec::new(),
            stale: Vec::new(),
        }
    }

    /// Render the §18.3 cascade sections + the §18.1.1 `stale:` section, or
    /// `None` when all are empty (empty sections are omitted entirely; an
    /// `AbiChanging` redefinition with no compiled dependents — and a
    /// downgrade with no compiled caller left behind — prints nothing extra).
    ///
    /// Symbols in `current_module` appear bare; others module-qualified
    /// (§18.3 / §3.3 layout rule at the grain the report needs). The
    /// `stale:` header line is byte-exact per §18.1.1, `{cause}` fully
    /// qualified.
    pub(crate) fn render(&self, current_module: &ModuleFullPath) -> Option<String> {
        if self.recompiled.is_empty() && self.broken.is_empty() && self.stale.is_empty() {
            return None;
        }
        let name_of = |fq: &FQSymbol| -> String {
            if &fq.module == current_module {
                fq.symbol.to_string()
            } else {
                format!("{}/{}", fq.module, fq.symbol)
            }
        };
        let mut out = String::new();
        if !self.recompiled.is_empty() {
            out.push_str("; recompiled:\n;  ");
            let names: Vec<String> = self.recompiled.iter().map(&name_of).collect();
            out.push_str(&names.join(" "));
            out.push('\n');
        }
        if !self.broken.is_empty() {
            out.push_str("; broken:\n");
            for (fq, err) in &self.broken {
                out.push_str(&format!(";  {} — {}\n", name_of(fq), err));
            }
        }
        if !self.stale.is_empty() {
            // §18.1.1: exact header, then the §1.1-layout name line(s) —
            // same closure as the sections above.
            out.push_str(&format!(
                "; stale: compiled callers keep the previous definition of {}\n;  ",
                self.target
            ));
            let names: Vec<String> = self.stale.iter().map(&name_of).collect();
            out.push_str(&names.join(" "));
            out.push('\n');
        }
        // Drop the trailing newline; the printer adds its own.
        while out.ends_with('\n') {
            out.pop();
        }
        // §10.3 R6: the whole cascade/broken/stale report is REPL structured
        // metadata (dim). `render` splits the R6 span per line (reset before each
        // `\n`, §10.2); colour-off it is byte-identical to `out` (the golden
        // corpus + the redefine unit tests below run colour-off).
        Some(render(&StyledDoc::span(Role::ReplMetadata, out)))
    }
}

/// First line of an error rendering — the §18.3 one-line reason (`the full
/// error remains readable via /info`).
fn first_line(s: &str) -> String {
    s.lines().next().unwrap_or(s).trim().to_string()
}

// ---------------------------------------------------------------------------
// The transaction driver (design §4, §13)
// ---------------------------------------------------------------------------

/// Run the dependent-recompilation transaction for one `AbiChanging`
/// redefinition target. Eval-thread-synchronous, staging-based: no pool
/// transitions, no quiesce (design §4.3 — between the target's commit and a
/// caller's recompile every stale chain resolves through frozen slots, a
/// coherent old-ABI world).
pub(crate) fn run_transaction(
    session: &mut CompilerSession,
    target: &FQSymbol,
) -> TransactionReport {
    let report = TransactionReport::new(target.clone());

    // 1. Reverse index — derived on demand (§3.3); zero cost on the body-only
    //    fast path, correct by construction against the live tables.
    let reverse = ReverseIndex::build(&session.shared.symbol_tables);

    // 2. Potential closure (§4.1 step 1).
    let closure = affected_closure(&reverse, target);
    if closure.is_empty() {
        return report;
    }

    // 3. Member metadata off the live entries.
    let closure_set: HashSet<&FQSymbol> = closure.iter().collect();
    let members: Vec<ClosureMember> = closure
        .iter()
        .filter_map(|fq| {
            let table = session.shared.symbol_tables.get(&fq.module)?;
            let entry = table.get(fq.symbol.as_ref())?;
            let callees: Vec<FQSymbol> = entry
                .callees()
                .iter()
                .filter(|c| *c == target || closure_set.contains(c))
                .cloned()
                .collect();
            Some(ClosureMember {
                fq: fq.clone(),
                slotless: entry.callable_got_slot().is_none(),
                callees,
            })
        })
        .collect();
    if members.is_empty() {
        return report;
    }

    // 4. SCC condensation, reverse-topological (callees before callers).
    let sccs = condense_reverse_topo(&members);

    // 5. The walk — one reverse-topo pass over the SCCs (callees before
    //    callers). Per-SCC recheck + propagation bookkeeping lives in
    //    `process_scc`; the mutable walk state rides on `TransactionWalk`,
    //    seeded with the target marked propagating (§4.1 step 1).
    let mut walk = TransactionWalk::seeded(target, report);
    for scc in &sccs {
        process_scc(session, scc, &members, target, &mut walk);
    }

    // Persist refresh: affected modules re-enter the nice-worker persist
    // queue (a module holding a BROKEN symbol is skipped at write time — the
    // §18.8 cache-write poisoning — and self-heals on its first green turn).
    for m in &walk.touched_modules {
        session.shared.scheduler.mark_object_stale(m);
    }

    walk.report
}

/// Mutable bookkeeping threaded through the SCC walk of a redefinition
/// transaction: the per-member propagation decisions, the set of modules whose
/// object cache must be marked stale, the report-name dedup set, and the report
/// being assembled.
struct TransactionWalk {
    propagates: HashMap<FQSymbol, bool>,
    touched_modules: HashSet<ModuleFullPath>,
    reported: HashSet<FQSymbol>,
    report: TransactionReport,
}

impl TransactionWalk {
    /// Seed the walk with the redefinition target marked as propagating.
    fn seeded(target: &FQSymbol, report: TransactionReport) -> Self {
        let mut propagates: HashMap<FQSymbol, bool> = HashMap::new();
        propagates.insert(target.clone(), true);
        TransactionWalk {
            propagates,
            touched_modules: HashSet::new(),
            reported: HashSet::new(),
            report,
        }
    }
}

/// Process one SCC of the reverse-topo condensation: skip-or-recheck its
/// members' base defns, record the per-member propagation decisions, and fold
/// recompiled / broken / recovered names into the report. Callees are ordered
/// before callers, so a member's `propagates` inputs are already decided.
fn process_scc(
    session: &mut CompilerSession,
    scc: &[usize],
    members: &[ClosureMember],
    target: &FQSymbol,
    walk: &mut TransactionWalk,
) {
    let TransactionWalk { propagates, touched_modules, reported, report } = walk;

    if !scc_should_visit(scc, members, propagates) {
        for &i in scc {
            propagates.insert(members[i].fq.clone(), false);
        }
        return;
    }

    // Cross-module SCCs cannot arise (import acyclicity); all members
    // share one home module.
    let module = members[scc[0]].fq.module.clone();

    // Re-typecheck inputs: the raw stored sexps of the members' BASE
    // defns (a `$`-mangled variant re-mints through its base form).
    let mut units: Vec<FQSymbol> = Vec::new();
    for &i in scc {
        let base = base_fq(&members[i].fq);
        if !units.contains(&base) {
            units.push(base);
        }
    }
    match resolve_recheck_sexps(session, &module, &units) {
        RecheckInputs::Sexps(sexps) => {
            match session.recheck_units_for_transaction(&module, &sexps) {
                Ok(outcomes) => {
                    let by_fq: HashMap<&FQSymbol, RedefKind> =
                        outcomes.iter().map(|o| (&o.fq, o.kind)).collect();
                    for &i in scc {
                        let m = &members[i];
                        let own = by_fq
                            .get(&m.fq)
                            .or_else(|| by_fq.get(&base_fq(&m.fq)))
                            .copied();
                        let green_changing = own.map(|k| k == RedefKind::AbiChanging);
                        propagates.insert(
                            m.fq.clone(),
                            member_propagates(m.slotless, true, green_changing),
                        );
                    }
                    for base in &units {
                        if session.shared.broken.remove(base).is_some() {
                            report.recovered.push(base.clone());
                        }
                        // §18.3 no-internal-artifacts: fold the user-facing
                        // report name (a `__macro_*` clause → its owning
                        // macro, a `$`-mangled mono → its base) at the push
                        // site; `base`/`units` stay RAW for the sexp lookup
                        // and the broken-registry key. Dedup on the folded
                        // name so two clauses of one macro collapse.
                        let display = render_caller_base(base);
                        if reported.insert(display.clone()) {
                            report.recompiled.push(display);
                        }
                    }
                    touched_modules.insert(module.clone());
                }
                Err(e) => {
                    let err = first_line(&e.to_string());
                    for base in &units {
                        mark_broken(
                            &session.shared.symbol_tables,
                            &session.shared.retained_code,
                            &session.shared.broken,
                            base,
                            target,
                            &err,
                        );
                        let display = render_caller_base(base);
                        if reported.insert(display.clone()) {
                            report.broken.push((display, err.clone()));
                        }
                    }
                    for &i in scc {
                        let m = &members[i];
                        // Slotted BROKEN does not propagate; slot-less
                        // BROKEN passes through (§4.1 case B).
                        propagates.insert(m.fq.clone(), m.slotless);
                    }
                    touched_modules.insert(module.clone());
                }
            }
        }
        RecheckInputs::ModuleGrain => {
            // T2 (design §10): a member's raw sexp is unrecoverable even
            // after backing-file rehydration — degrade this module to the
            // module-grain reload and treat its members as
            // recompiled-at-module-grain (conservative propagation).
            let reloaded = module_grain_reload(session, &module);
            for &i in scc {
                let m = &members[i];
                // §18.3 no-internal-artifacts: the report name folds a
                // `__macro_*` clause to its owning macro (the F3 reachable
                // case — a cross-module macro clause with no standalone
                // sexp routes here via T2); the broken-registry key stays
                // RAW (`base_fq`).
                let display = render_caller_base(&m.fq);
                if reloaded {
                    propagates.insert(m.fq.clone(), true);
                    if reported.insert(display.clone()) {
                        report.recompiled.push(display);
                    }
                } else {
                    // No backing file to reload from: trap rather than
                    // leave a stale caller silently unsound.
                    let base = base_fq(&m.fq);
                    let err = "definition source unavailable for dependent \
                               recompilation"
                        .to_string();
                    mark_broken(
                        &session.shared.symbol_tables,
                        &session.shared.retained_code,
                        &session.shared.broken,
                        &base,
                        target,
                        &err,
                    );
                    if reported.insert(display.clone()) {
                        report.broken.push((display, err));
                    }
                    propagates.insert(m.fq.clone(), m.slotless);
                }
            }
            touched_modules.insert(module.clone());
        }
    }
}

/// Strip a `$`-mangled variant name to its base defn FQ.
pub(crate) fn base_fq(fq: &FQSymbol) -> FQSymbol {
    match fq.symbol.as_ref().split_once('$') {
        Some((base, _)) => FQSymbol {
            module: fq.module.clone(),
            symbol: Symbol::from(base),
        },
        None => fq.clone(),
    }
}

/// Fold a synthetic `__macro_{name}_clause_{idx}` clause symbol to its owning
/// user macro base name `{name}` (S103, FIXME 0507 Issue 2 / F3 — §18.1.1
/// "no internal artifacts"). Returns `None` for a non-clause symbol.
pub(crate) fn macro_clause_base_name(name: &str) -> Option<&str> {
    let rest = name.strip_prefix("__macro_")?;
    let idx = rest.rfind("_clause_")?;
    (idx > 0).then(|| &rest[..idx])
}

/// Render a caller FQ at report grain: a `$`-mangled mono variant folds to its
/// base defn, and a `__macro_*` clause folds to its owning user macro
/// (home-module-qualified) — never a raw internal artifact (§18.1.1).
pub(crate) fn render_caller_base(fq: &FQSymbol) -> FQSymbol {
    if let Some(base) = macro_clause_base_name(fq.symbol.as_ref()) {
        return FQSymbol {
            module: fq.module.clone(),
            symbol: Symbol::from(base),
        };
    }
    base_fq(fq)
}

enum RecheckInputs {
    Sexps(Vec<Sexp>),
    ModuleGrain,
}

/// Resolve the raw stored sexps for the recheck units (design §4.2): the
/// introspection store first (populated at every REPL definition), then the
/// FIXME-0220 lazy rehydration from the backing `.cl` for cache-restored
/// modules. Unrecoverable → the T2 module-grain degrade.
fn resolve_recheck_sexps(
    session: &CompilerSession,
    module: &ModuleFullPath,
    units: &[FQSymbol],
) -> RecheckInputs {
    let get_sexp = |fq: &FQSymbol| -> Option<Sexp> {
        session
            .shared
            .introspection
            .as_ref()
            .and_then(|m| m.get(fq))
            .and_then(|i| i.sexp.clone())
    };

    let mut missing: Vec<&FQSymbol> = units.iter().filter(|u| get_sexp(u).is_none()).collect();
    if !missing.is_empty() {
        // Cache-restored modules never populate introspection; rehydrate from
        // the backing `.cl` (the cache key — normally present).
        let rehydrated = session
            .shared
            .typecheck_products
            .get(module)
            .and_then(|tp| tp.file_path.clone())
            .and_then(|p| std::fs::read_to_string(p).ok())
            .map(|source| {
                if let (Some(st), Some(intro)) = (
                    session.shared.symbol_tables.get(module),
                    session.shared.introspection.as_ref(),
                ) {
                    let table = st.clone();
                    drop(st);
                    crate::save::rehydrate_userfn_introspection_from_source(
                        &table, intro, module, &source,
                    );
                    true
                } else {
                    false
                }
            })
            .unwrap_or(false);
        if rehydrated {
            missing.retain(|u| get_sexp(u).is_none());
        }
        if !missing.is_empty() {
            return RecheckInputs::ModuleGrain;
        }
    }

    // Order the cluster by authorship (`seq`) so mutually-recursive units
    // re-check in their original order.
    let mut ordered: Vec<(u64, Sexp)> = units
        .iter()
        .map(|u| {
            let seq = session
                .shared
                .symbol_tables
                .get(&u.module)
                .and_then(|t| match t.get(u.symbol.as_ref()) {
                    Some(ModuleEntry::Def { seq, .. }) => Some(*seq),
                    _ => None,
                })
                .unwrap_or(u64::MAX);
            (seq, get_sexp(u).expect("checked above"))
        })
        .collect();
    ordered.sort_by_key(|(seq, _)| *seq);
    RecheckInputs::Sexps(ordered.into_iter().map(|(_, s)| s).collect())
}

/// T2 module-grain degrade: reload the member's module from its backing file
/// through the existing S35/S37 machinery. Returns `false` when no backing
/// file is known or the reload fails.
fn module_grain_reload(session: &mut CompilerSession, module: &ModuleFullPath) -> bool {
    let Some(path) = session
        .shared
        .typecheck_products
        .get(module)
        .and_then(|tp| tp.file_path.clone())
    else {
        return false;
    };
    session.reload_module(module, &path, &[]).is_ok()
}

// ---------------------------------------------------------------------------
// Session-side driver hooks
// ---------------------------------------------------------------------------

impl CompilerSession {
    /// Post-codegen hook for one successful defining turn (design §13): clears
    /// broken records for every successfully (re)defined symbol (§18.6
    /// recovery direction 1 — an ordinary redefinition of a broken symbol
    /// recovers it, both `AbiPreserving` in-place and `AbiChanging`
    /// fresh-slot), then runs the transaction for each per-symbol
    /// `AbiChanging` outcome and stashes the rendered cascade report for the
    /// REPL printer.
    pub(crate) fn apply_redefinition_outcomes(&mut self, outcomes: &[RedefinitionOutcome]) {
        for o in outcomes {
            if outcome_clears_broken(o) {
                self.shared.broken.remove(&o.fq);
            }
        }
        // Surviving-trigger T1 downgrade targets, driven through the §10 T1
        // full cure AFTER the per-symbol transactions settle (CS-1). Collected
        // rather than driven inline so a multi-def cluster reloads each target
        // module once and the driver's own regen/reload cannot perturb the
        // outcome list mid-iteration.
        let mut t1_targets: Vec<FQSymbol> = Vec::new();
        for o in outcomes {
            if o.kind == RedefKind::AbiChanging && o.per_symbol {
                let report = run_transaction(self, &o.fq);
                if let Some(text) = report.render(&self.current_module_path()) {
                    self.pending_cascade_reports.push(text);
                }
            } else if is_t1_downgrade(o) && !t1_targets.contains(&o.fq) {
                t1_targets.push(o.fq.clone());
            }
        }
        for target in t1_targets {
            self.drive_t1_full_cure(&target);
        }
    }

    /// Q1 (FIXME 0549 / `design/int/session-transaction.md` §10 CS-1): capture
    /// `module`'s live **instantiation-driver** forms — the source expression of
    /// the synthetic `__expr` eval wrapper (a same-module REPL top-level
    /// expression is the minter of same-module polymorphic mono variants like
    /// `g$Int`). Read from the live REPL `Introspection` record, so the mono
    /// re-instantiation obligation travels the compiled/in-memory channel rather
    /// than the persisted `.cl` (which §8 pin (v) makes definitions-only). Empty
    /// when the module has no live `__expr` (no same-module expression drove a
    /// mint this session) — then the reload behaves as a plain from-source reload.
    fn capture_instantiation_drivers(&self, module: &ModuleFullPath) -> Vec<Sexp> {
        let fq = FQSymbol {
            module: module.clone(),
            symbol: Symbol::from(crate::worker::SYNTHETIC_EXPR_WRAPPER),
        };
        self.shared
            .introspection
            .as_ref()
            .and_then(|m| m.get(&fq))
            .and_then(|i| i.sexp.clone())
            .into_iter()
            .collect()
    }

    /// The §10 T1 full cure (S103, FIXME 0507, change-sets CS-1/2/3): a
    /// surviving-trigger T1 downgrade of `target` leaves compiled callers on
    /// the previous definition (the split world the S102 interim `stale:` print
    /// exposed). This driver replaces that print with an end-of-turn-sequenced
    /// module reload that RECOMPILES those callers, so the `stale:` section
    /// renders empty (CS-2, the Principle-8 kept-machinery pin).
    ///
    /// - **CS-1.** `regenerate_backing_file` runs FIRST so the backing source
    ///   carries the just-committed redefinition (never resurrect the
    ///   pre-redefinition source a bare mid-turn reload would read), then
    ///   `reload_module`(target) + the dependent cascade reload through the
    ///   §7.3 Replace commit gate. Eval-synchronous: `reload_module` blocks the
    ///   eval thread on `wait_inmem_complete_blocking` while a pool worker
    ///   re-typechecks (the S93 watcher discipline — no second orchestrator,
    ///   B1 stays closed). Reachable from BOTH the ordinary-def exit and the
    ///   `eval.rs` defmacro early-return (F5a) via `apply_redefinition_outcomes`.
    /// - **CS-2.** A successful reload cures the split world, so NO `stale:`
    ///   report is pushed (the section renders empty). `stale_callers` cannot
    ///   distinguish a recompiled caller from a stale one — the empty render is
    ///   achieved by not pushing after a successful reload, not by a re-scan.
    /// - **CS-3.** A reload FAILURE degrades to the §14.4 error-blocked state
    ///   (the 0489 prompt floor — never a lockout or session exit) and keeps
    ///   the interim `stale:` print; a module whose regen is SUPPRESSED
    ///   (FIXME-0343 `should_regenerate` guard) keeps the print rather than
    ///   reload stale disk source.
    fn drive_t1_full_cure(&mut self, target: &FQSymbol) {
        // The omission rule (§18.1.1): no compiled caller left behind ⇒ no
        // reload, no report. The on-demand `ReverseIndex` scan runs ONLY here
        // (L-D1 untouched — body-only concrete redefinitions never reach it).
        let stale = stale_callers(&self.shared.symbol_tables, target);
        if stale.is_empty() {
            return;
        }
        // CS-3 (regen suppressed): reloading would read stale disk source.
        if !self.module_regeneratable(&target.module) {
            self.push_stale_report(target, stale);
            return;
        }
        // Q1 (FIXME 0549 / §10 CS-1 explicit-capture): capture the target
        // module's live instantiation-driver forms (the synthetic `__expr` eval
        // wrapper's source expression) BEFORE regen makes the backing file
        // definitions-only. The from-source reload re-mints the same-module mono
        // variants they instantiate through this explicit in-memory channel —
        // never the persisted `.cl`. Q1 strictly precedes Q2 (the writer filter);
        // without it, dropping `__expr` from the file would leave a stale mono
        // caller uncured (the reverted Wave-4 regression).
        let drivers = self.capture_instantiation_drivers(&target.module);
        // CS-1: persist the just-committed redefinition, then reload.
        self.regenerate_backing_file();
        let Some(path) = self.module_backing_path(&target.module) else {
            self.push_stale_report(target, stale);
            return;
        };
        match self.reload_module(&target.module, &path, &drivers) {
            Ok(()) => {
                self.reload_t1_dependents(&target.module);
                // CS-2: the reload recompiled exactly the stale callers — the
                // section renders EMPTY (push nothing). Kept machinery, not
                // throwaway (Principle 8).
            }
            Err(e) => {
                // CS-3 (reload failure): the regenerated source is now
                // ill-typed (e.g. an unannotated caller made ambiguous under an
                // overloaded target — a real error `--run` would report for
                // this file too). Degrade to the §14.4 error-blocked floor.
                self.enter_t1_reload_error_block(target, &stale, &first_line(&e.to_string()));
                self.push_stale_report(target, stale);
            }
        }
    }

    /// Enter the §14.4 error-blocked floor after a CS-3 T1 reload failure —
    /// **liftable by repair, never a lockout** (the 0489 floor).
    ///
    /// Resets the scheduler's Failed state so the session exits cleanly (never
    /// a session exit), records each stale caller resident in the target module
    /// as a `FailedForm` (keyed by module) from its introspection source, and
    /// adds the module to `error_modules`. Recording the failed forms is
    /// load-bearing for the "never a lockout" guarantee: `clear_repaired_failed_form`
    /// lifts the block ONLY when `failed_forms` drains, and
    /// `regenerate_backing_file` re-emits them verbatim (`append_failed_forms`)
    /// so the ill-typed caller is never silently dropped. A repair definition
    /// turn (re-defining the ambiguous caller) drains the set and reopens the
    /// prompt. (Unlike a full degraded re-drive this does NOT re-enter the eval
    /// path, so it cannot recurse or perturb the surviving module state.)
    fn enter_t1_reload_error_block(&mut self, target: &FQSymbol, stale: &[FQSymbol], error: &str) {
        use crate::session_v4::FailedForm;
        // Scheduler-only reset here — do NOT purge the failed modules' live
        // tables (contrast the autoload-retry reset). A T1 redefinition rollback
        // relies on the PRIOR (valid) definitions still living in those tables
        // for the caller-repair lift; purging them destroys recoverable state.
        let _ = self.shared.scheduler.reset_all_failed_modules();
        let failed: Vec<FailedForm> = stale
            .iter()
            .filter(|fq| fq.module == target.module)
            .filter_map(|fq| {
                let text = self
                    .shared
                    .introspection
                    .as_ref()
                    .and_then(|m| m.get(fq))
                    .and_then(|i| i.source.clone())?;
                Some(FailedForm {
                    symbol: Some(fq.symbol.clone()),
                    error: error.to_string(),
                    text,
                })
            })
            .collect();
        if !failed.is_empty() {
            self.failed_forms
                .entry(target.module.clone())
                .or_default()
                .extend(failed);
        }
        self.error_modules.insert(target.module.clone());
    }

    /// Push the §18.1.1 `stale:` interim report for `target` (the CS-3
    /// suppressed / reload-failure fallbacks — the full cure otherwise renders
    /// it empty).
    fn push_stale_report(&mut self, target: &FQSymbol, stale: Vec<FQSymbol>) {
        let mut report = TransactionReport::new(target.clone());
        report.stale = stale;
        if let Some(text) = report.render(&self.current_module_path()) {
            self.pending_cascade_reports.push(text);
        }
    }

    /// Whether `module`'s backing file may be regenerated (the FIXME-0343
    /// `should_regenerate` guard — a body-bearing inline-submodule parent is
    /// suppressed). CS-3 keeps the interim print for a suppressed module.
    fn module_regeneratable(&self, module: &ModuleFullPath) -> bool {
        self.shared
            .symbol_tables
            .get(module)
            .map(|st| crate::save::should_regenerate(&st))
            .unwrap_or(false)
    }

    /// The backing `.cl` path for `module` — the typecheck-product `file_path`,
    /// or the `{project_root}/{module}.cl` fallback `regenerate_backing_file`
    /// writes to (only when it exists on disk, so the reload has real source).
    fn module_backing_path(&self, module: &ModuleFullPath) -> Option<std::path::PathBuf> {
        if let Some(tp) = self.shared.typecheck_products.get(module)
            && let Some(p) = tp.file_path.clone()
        {
            return Some(p);
        }
        let fallback = self.shared.project_root.join(format!("{module}.cl"));
        fallback.exists().then_some(fallback)
    }

    /// CS-1 dependent cascade: reload every module importing `changed` from its
    /// own backing file (the §7.3 imports-scan). A cross-module caller — or a
    /// `__macro_*` clause's home module — that uses the redefined dependency
    /// picks up the new definition through its re-typecheck / re-expansion.
    /// Reload failures are non-fatal here (the primary target has already been
    /// cured). The dependent set + path resolution come from the SHARED
    /// `CompilerSession::dependent_modules` scan the watcher's `poll_and_reload`
    /// also uses (Principle 7 — the two cascades cannot drift).
    fn reload_t1_dependents(&mut self, changed: &ModuleFullPath) {
        let mut changed_set: HashSet<ModuleFullPath> = HashSet::new();
        changed_set.insert(changed.clone());
        for (dep, path) in self.dependent_modules(&changed_set) {
            let _ = self.reload_module(&dep, &path, &[]);
        }
    }

    /// Drain the pending cascade-report text for the turn's display, if any.
    pub fn take_cascade_report(&mut self) -> Option<String> {
        if self.pending_cascade_reports.is_empty() {
            return None;
        }
        Some(std::mem::take(&mut self.pending_cascade_reports).join("\n"))
    }

    /// Re-typecheck + recompile one SCC's units as a single Additive cluster
    /// in the members' home module (design §4.2): expand → build →
    /// fresh-staging `check_forms` → commit through the §2 gate → codegen —
    /// exactly the `process_cluster_once` shape minus the scheduler (no pool
    /// transitions; the eval thread waits on dependencies itself).
    ///
    /// Uses a FRESH `CheckState` rooted at the member module (Principle 17)
    /// rather than the REPL carry-forward state — the transaction must not
    /// perturb the interactive session's inference state.
    #[allow(clippy::result_large_err)] // CranelispError is the crate-wide error carrier
    pub(crate) fn recheck_units_for_transaction(
        &mut self,
        module: &ModuleFullPath,
        sexps: &[Sexp],
    ) -> Result<Vec<RedefinitionOutcome>, CranelispError> {
        use crate::worker::{ClusterOnce, ModuleCompiler};
        use cranelisp_typecheck::CheckState;

        const MAX_DEP_RETRIES: usize = 100;

        for _retry in 0..MAX_DEP_RETRIES {
            cranelisp_types::ensure_module_exists(&self.shared.symbol_tables, module);
            let lib_dirs_snap = self.lib_dirs();
            let platform_dirs_snap = self.platform_dirs();
            let mut wctx = ModuleCompiler {
                symbol_tables: &self.shared.symbol_tables,
                next_type_id: &self.shared.next_type_id,
                module_aliases: &self.shared.module_aliases,
                prelude_fallback: &self.shared.prelude_fallback,
                check_state: CheckState::new(module.clone()),
                current_module: module.clone(),
                scheduler: &self.shared.scheduler,
                typecheck_products: &self.shared.typecheck_products,
                introspection: self.shared.introspection.as_ref(),
                lib_dirs: &lib_dirs_snap,
                platform_dirs: &platform_dirs_snap,
                project_root: &self.shared.project_root,
                shared_state: Some(&self.shared),
                // Eval-thread-synchronous: a dependency gap must never move
                // the module to TypecheckBlocked (Invariant SW) — the
                // transaction waits on the dep itself and retries from the top.
                eval_driven: true,
            };

            let result = crate::process_form::process_cluster_once(
                &mut wctx,
                module,
                sexps,
                ModuleStrategy::Additive,
            )?;

            match result {
                ClusterOnce::Done { processed, program } => {
                    crate::worker::inline_jit_codegen_for_module(
                        &self.shared.scheduler,
                        module,
                        &program,
                        &self.shared.symbol_tables,
                        self.shared.introspection.as_ref(),
                        Some(&self.shared),
                    )?;
                    return Ok(processed.redefinitions().to_vec());
                }
                ClusterOnce::Gap { dep } => {
                    self.register_dep_for_eval(&dep)?;
                }
            }
        }
        Err(CranelispError::ModuleError {
            message: format!(
                "dependency chain too deep while re-typechecking '{module}' \
                 during dependent recompilation"
            ),
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
        })
    }

    /// The provenance comment line for a broken symbol resolved in `module`,
    /// or `None` when the symbol is not broken (`repl/spec.md` §18.4):
    /// `; broken by the redefinition of {cause}: {original error}`.
    pub(crate) fn broken_status_line(
        &self,
        name: &str,
        module: &ModuleFullPath,
    ) -> Option<String> {
        // Accept both bare and module-qualified spellings.
        let (module, bare) = match name.rsplit_once('/') {
            Some((m, n)) => (ModuleFullPath::from(m), n),
            None => (module.clone(), name),
        };
        let fq = FQSymbol {
            module,
            symbol: Symbol::from(bare),
        };
        self.shared.broken.get(&fq).map(|info| {
            broken_status_render(&info.broken_by, &info.original_error)
        })
    }
}

/// Render a `; broken by the redefinition of <cause>: <error>` provenance line
/// (`repl/spec.md` §18.4) as one §10.3 **R6** dim `ReplMetadata` span through the
/// styling seam — matching `TransactionReport::render`'s cascade/broken/stale
/// lines. Colour-OFF (`render`) is byte-identical to the plain line, so the
/// `/sig`/`/info` broken-symbol goldens stay green; colour-ON it is dim. A free
/// function so the role is single-sourced (Principle 7) and unit-pinnable without
/// a live `SharedState.broken` map.
fn broken_status_render(broken_by: &FQSymbol, original_error: &str) -> String {
    render(&StyledDoc::span(
        Role::ReplMetadata,
        format!("; broken by the redefinition of {broken_by}: {original_error}"),
    ))
}

// ---------------------------------------------------------------------------
// Unit tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{Scheme, Type, Visibility};
    use std::collections::HashMap as StdHashMap;

    fn scheme(ty: Type) -> Scheme {
        Scheme {
            type_vars: vec![],
            constraints: StdHashMap::new(),
            ty,
        }
    }

    fn concrete_def(ty: Type, slot: usize) -> ModuleEntry<Code> {
        ModuleEntry::Def {
            scheme: scheme(ty),
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(DefKind::UserFn {
                fn_state: UserFnState::Concrete { got_slot: slot, mode_summary: None },
            }),
            callees: Vec::new(),
            trait_origin: None,
            seq: 0,
            ast: None,
            codegen_view: None,
            code: None,
            value_use: false,
        }
    }

    fn def_with_callees(callees: Vec<FQSymbol>, slot: Option<usize>) -> ModuleEntry<Code> {
        let kind = match slot {
            Some(got_slot) => DefKind::UserFn {
                fn_state: UserFnState::Concrete { got_slot, mode_summary: None },
            },
            // A slot-less template kind (Polymorphic carries a scheme id
            // payload in some shapes; Constrained carries the template).
            None => DefKind::Overloaded { variants: vec![] },
        };
        ModuleEntry::Def {
            scheme: scheme(Type::Int),
            visibility: Visibility::Public,
            docstring: None,
            param_names: vec![],
            kind: Box::new(kind),
            callees,
            trait_origin: None,
            seq: 0,
            ast: None,
            codegen_view: None,
            code: None,
            value_use: false,
        }
    }

    fn fq(module: &str, name: &str) -> FQSymbol {
        FQSymbol {
            module: ModuleFullPath::from(module),
            symbol: Symbol::from(name),
        }
    }

    fn fn_ty(params: Vec<Type>, ret: Type) -> Type {
        Type::Fn(params, Box::new(ret))
    }

    // spec: design/int/session-transaction.md §2.2 — the comparand is the
    // alpha-canonical scheme rendering: two checks of the same source with
    // different type-variable ids compare EQUAL.
    #[test]
    fn abi_surface_alpha_canonical_var_ids_compare_equal() {
        let a = concrete_def(fn_ty(vec![Type::Var(3)], Type::Var(3)), 0);
        let b = concrete_def(fn_ty(vec![Type::Var(97)], Type::Var(97)), 1);
        assert_eq!(
            AbiSurface::of(&a),
            AbiSurface::of(&b),
            "alpha-equivalent schemes must have the same ABI surface"
        );
    }

    // spec: design/int/session-transaction.md §2.2 — a type-scheme change is
    // AbiChanging; the slot the entry carries is NOT part of the comparand.
    #[test]
    fn abi_surface_type_change_differs_slot_does_not() {
        let int_fn = concrete_def(fn_ty(vec![Type::Int], Type::Int), 0);
        let int_fn_other_slot = concrete_def(fn_ty(vec![Type::Int], Type::Int), 7);
        let str_fn = concrete_def(fn_ty(vec![Type::String], Type::Int), 0);
        assert_eq!(AbiSurface::of(&int_fn), AbiSurface::of(&int_fn_other_slot));
        assert_ne!(AbiSurface::of(&int_fn), AbiSurface::of(&str_fn));
    }

    // spec: design/int/session-transaction.md §2.1 — RedefKind classification:
    // New (no prior), AbiPreserving (same surface), AbiChanging (changed).
    #[test]
    fn classify_new_preserving_changing() {
        let prior = concrete_def(fn_ty(vec![Type::Int], Type::Int), 0);
        let same = concrete_def(fn_ty(vec![Type::Int], Type::Int), 0);
        let changed = concrete_def(fn_ty(vec![Type::String], Type::Int), 0);

        assert_eq!(classify_redefinition("f", None, &same), (RedefKind::New, false));
        assert_eq!(
            classify_redefinition("f", Some(&prior), &same),
            (RedefKind::AbiPreserving, true)
        );
        assert_eq!(
            classify_redefinition("f", Some(&prior), &changed),
            (RedefKind::AbiChanging, true)
        );
    }

    // spec: design/int/session-transaction.md §2.2 — internal artifacts
    // (`__expr`, macro clauses) never classify AbiChanging (fresh-slot churn
    // would exhaust the GOT on every expression turn), and non-concrete
    // targets are outside per-symbol precision (§10 T1).
    #[test]
    fn classify_neg_internal_names_and_nonconcrete_never_abi_changing() {
        let prior = concrete_def(fn_ty(vec![Type::Int], Type::Int), 0);
        let changed = concrete_def(fn_ty(vec![Type::String], Type::String), 0);
        assert_eq!(
            classify_redefinition("__expr", Some(&prior), &changed),
            (RedefKind::AbiPreserving, false)
        );
        assert_eq!(
            classify_redefinition("__macro_m_clause_0", Some(&prior), &changed),
            (RedefKind::AbiPreserving, false)
        );
        // Prior slot-less (template) → New (no frozen slot to version).
        let slotless_prior = def_with_callees(vec![], None);
        assert_eq!(
            classify_redefinition("f", Some(&slotless_prior), &changed),
            (RedefKind::New, false)
        );
        // Non-concrete staged (Overloaded base) → conservative T1.
        let overloaded = def_with_callees(vec![], None);
        // (a slot-less staged entry never reaches the gate in production —
        // the gate is entered only for staged callable slots — but the pure
        // classifier must still answer conservatively)
        assert_eq!(
            classify_redefinition("f", Some(&prior), &overloaded),
            (RedefKind::AbiPreserving, false)
        );
    }

    // spec: repl/spec.md §18.6 — recovery direction 1 holds across ALL T1
    // shapes (S102 W5 review F1): the two `New`-classified REDEFINITION
    // shapes (slot-less prior Def — template redefined / concrete displaced
    // by template — carry `prior_was_def: true`) clear the broken record
    // like any other redefinition; a genuinely-new definition (no prior Def,
    // incl. the prior-Import shadow shape) does not claim to.
    #[test]
    fn outcome_clears_broken_covers_new_classified_redefinition_shapes() {
        let outcome = |kind, prior_was_def| RedefinitionOutcome {
            fq: fq("user", "k"),
            kind,
            per_symbol: false,
            prior_was_def,
            old_slot: None,
            new_slot: None,
        };
        // The recovery cell the F1 defect missed: broken slot-less template
        // redefined green → classified New + prior_was_def → CLEARS.
        assert!(outcome_clears_broken(&outcome(RedefKind::New, true)));
        // Ordinary redefinitions clear (both classifications).
        assert!(outcome_clears_broken(&outcome(RedefKind::AbiPreserving, true)));
        assert!(outcome_clears_broken(&outcome(RedefKind::AbiChanging, true)));
        // Genuinely new (no prior Def, incl. Import-shadow) — no clear claim.
        assert!(!outcome_clears_broken(&outcome(RedefKind::New, false)));
    }

    // spec: design/int/session-transaction.md §3.3 — the reverse index is
    // derived from `Def.callees` (callee → callers), across modules.
    #[test]
    fn reverse_index_build_and_closure() {
        let tables: SymbolTables = dashmap::DashMap::new();
        let user = ModuleFullPath::from("user");
        let other = ModuleFullPath::from("other");
        let mut ut = SessionSymbolTable::new_with_params(user.clone());
        // g calls f; h calls g; unrelated calls add-i64 only.
        ut.insert(Symbol::from("f"), def_with_callees(vec![], Some(0)));
        ut.insert(Symbol::from("g"), def_with_callees(vec![fq("user", "f")], Some(1)));
        ut.insert(Symbol::from("h"), def_with_callees(vec![fq("user", "g")], Some(2)));
        ut.insert(
            Symbol::from("unrelated"),
            def_with_callees(vec![fq("primitives", "add-i64")], Some(3)),
        );
        tables.insert(user.clone(), ut);
        let mut ot = SessionSymbolTable::new_with_params(other.clone());
        ot.insert(Symbol::from("x"), def_with_callees(vec![fq("user", "f")], Some(0)));
        tables.insert(other, ot);

        let reverse = ReverseIndex::build(&tables);
        let callers: Vec<_> = reverse.callers_of(&fq("user", "f")).to_vec();
        assert_eq!(callers, vec![fq("other", "x"), fq("user", "g")]);

        let closure = affected_closure(&reverse, &fq("user", "f"));
        assert!(closure.contains(&fq("user", "g")), "direct caller in closure");
        assert!(closure.contains(&fq("user", "h")), "transitive caller in closure");
        assert!(closure.contains(&fq("other", "x")), "cross-module caller in closure");
        // Negative (L-R3 exactness feed): unaffected symbols never enter.
        assert!(
            !closure.contains(&fq("user", "unrelated")),
            "unrelated must NOT join the closure"
        );
        assert!(!closure.contains(&fq("user", "f")), "target is not a member");
    }

    // spec: repl/spec.md §18.3 (FIXME 0491) / design/int/session-transaction.md
    // §9.1.1 (S103, FIXME 0507 Issue 2 / F3) — the CALLER/feed exclusion is
    // `__expr`-ONLY (supersedes the former `..._gate_exempt_internal` guard's
    // `__macro_*` half). The synthetic `__expr` eval wrapper never joins the
    // reverse index (a stale wrapper is never re-invoked). A macro clause
    // (`__macro_{name}_clause_{idx}`) IS re-invoked at the next expansion and
    // may reference a redefined dependency fn, so its reverse edge is KEPT — it
    // renders at report grain as its owning user macro `{name}`, never the raw
    // clause symbol.
    #[test]
    fn reverse_index_neg_excludes_only_expr_keeps_macro_clause() {
        let tables: SymbolTables = dashmap::DashMap::new();
        let user = ModuleFullPath::from("user");
        let mut ut = SessionSymbolTable::new_with_params(user.clone());
        ut.insert(Symbol::from("f"), def_with_callees(vec![], Some(0)));
        // The eval wrapper — EXCLUDED (the 0491 rule, `__expr`-only).
        ut.insert(
            Symbol::from("__expr"),
            def_with_callees(vec![fq("user", "f")], Some(1)),
        );
        // A macro clause carrying a REAL callee edge to f — KEPT (F3).
        ut.insert(
            Symbol::from("__macro_m_clause_0"),
            def_with_callees(vec![fq("user", "f")], Some(2)),
        );
        // Control: a real caller with the same edge stays in.
        ut.insert(Symbol::from("g"), def_with_callees(vec![fq("user", "f")], Some(3)));
        tables.insert(user.clone(), ut);

        let reverse = ReverseIndex::build(&tables);
        // `__expr` excluded; `__macro_m_clause_0` and `g` both indexed (sorted
        // by symbol — `_` < `g`).
        assert_eq!(
            reverse.callers_of(&fq("user", "f")),
            &[fq("user", "__macro_m_clause_0"), fq("user", "g")],
            "the eval wrapper is excluded; the macro clause is kept"
        );
        // The macro clause folds to its owning user macro at report grain,
        // never the raw `__macro_*` symbol (§18.1.1).
        assert_eq!(
            render_caller_base(&fq("user", "__macro_m_clause_0")),
            fq("user", "m"),
            "a macro-clause caller renders as its owning macro"
        );
        assert_eq!(macro_clause_base_name("__macro_m_clause_0"), Some("m"));
        assert_eq!(macro_clause_base_name("g"), None, "non-clause names do not fold");
    }

    // spec: design/int/session-transaction.md §4.1 — SCC condensation emits
    // callees before callers (reverse topological); a mutually-recursive
    // group is one SCC.
    #[test]
    fn scc_reverse_topo_order_and_cycles() {
        // g → f(target, not a member); h → g; a ⇄ b (mutual) with a → h.
        let members = vec![
            ClosureMember { fq: fq("user", "g"), slotless: false, callees: vec![fq("user", "f")] },
            ClosureMember { fq: fq("user", "h"), slotless: false, callees: vec![fq("user", "g")] },
            ClosureMember {
                fq: fq("user", "a"),
                slotless: false,
                callees: vec![fq("user", "b"), fq("user", "h")],
            },
            ClosureMember { fq: fq("user", "b"), slotless: false, callees: vec![fq("user", "a")] },
        ];
        let sccs = condense_reverse_topo(&members);
        // Positions: g before h before {a,b}.
        let pos = |name: &str| {
            sccs.iter()
                .position(|scc| scc.iter().any(|&i| members[i].fq.symbol.as_ref() == name))
                .unwrap()
        };
        assert!(pos("g") < pos("h"), "callee g settles before caller h");
        assert!(pos("h") < pos("a"), "callee h settles before caller a");
        let ab = &sccs[pos("a")];
        assert_eq!(ab.len(), 2, "mutual recursion is ONE SCC: {sccs:?}");
    }

    // spec: design/int/session-transaction.md §4.1 — the skip test + the
    // slot-less pass-through: slotted AbiPreserving members stop the walk;
    // slot-less members never gate it (visited ⇒ propagate, whatever the
    // outcome); slotted BROKEN does not propagate; unvisited never propagates.
    #[test]
    fn slotless_pass_through_propagation_decisions() {
        // Slotted green member: propagates iff own gate diff AbiChanging.
        assert!(!member_propagates(false, true, Some(false)), "slotted AbiPreserving stops");
        assert!(member_propagates(false, true, Some(true)), "slotted AbiChanging propagates");
        // Slotted BROKEN (no green outcome): does not propagate.
        assert!(!member_propagates(false, true, None), "slotted BROKEN stops");
        // Slot-less member: pass-through, whatever its own outcome.
        assert!(member_propagates(true, true, Some(false)), "slot-less green-unchanged passes");
        assert!(member_propagates(true, true, Some(true)), "slot-less green-changed passes");
        assert!(member_propagates(true, true, None), "slot-less BROKEN passes");
        // Unvisited members never propagate.
        assert!(!member_propagates(true, false, None));
        assert!(!member_propagates(false, false, None));

        // The worked §4.1 case (A): target f → slot-less template t → caller c.
        // Without pass-through the walk would stop at t (AbiPreserving); with
        // it, c is visited.
        let members = vec![
            ClosureMember { fq: fq("user", "t"), slotless: true, callees: vec![fq("user", "f")] },
            ClosureMember { fq: fq("user", "c"), slotless: false, callees: vec![fq("user", "t")] },
        ];
        let sccs = condense_reverse_topo(&members);
        let mut propagates: HashMap<FQSymbol, bool> = HashMap::new();
        propagates.insert(fq("user", "f"), true);
        // t's SCC: visited (its callee f propagates); t re-checks green with
        // an UNCHANGED scheme (own gate diff AbiPreserving == Some(false)).
        assert!(scc_should_visit(&sccs[0], &members, &propagates));
        propagates.insert(fq("user", "t"), member_propagates(true, true, Some(false)));
        // c's SCC MUST be visited — the pass-through carries past t.
        assert!(
            scc_should_visit(&sccs[1], &members, &propagates),
            "slot-less pass-through must reach the mono-minting caller"
        );
    }

    // spec: design/int/session-transaction.md §6.2 — mark_broken (slotted):
    // the displaced code and the trap stub + provenance buffer land PAIRED in
    // the retention pool; the slot is patched in place; the registry records
    // depth-1 provenance.
    #[test]
    fn mark_broken_slotted_pairs_stub_with_message_and_patches_slot() {
        let tables: SymbolTables = dashmap::DashMap::new();
        let user = ModuleFullPath::from("user");
        let mut ut = SessionSymbolTable::new_with_params(user.clone());
        let slot = ut.allocate_got_slot().expect("fresh table has free slots");
        ut.insert(Symbol::from("g"), concrete_def(fn_ty(vec![Type::Int], Type::Int), slot));
        let old_ptr = 0xDEAD_0000usize as *const u8;
        ut.got.store_slot(slot, old_ptr);
        tables.insert(user.clone(), ut);

        let pool: RetentionPool = Mutex::new(Vec::new());
        let registry: BrokenRegistry = dashmap::DashMap::new();
        mark_broken(
            &tables,
            &pool,
            &registry,
            &fq("user", "g"),
            &fq("user", "f"),
            "type error: expected primitives/String, got primitives/Int",
        );

        // Registry: depth-1 provenance in the normative phrasing.
        let info = registry.get(&fq("user", "g")).expect("registry record");
        assert_eq!(info.broken_by, fq("user", "f"));
        assert!(info.provenance.starts_with("user/g is broken by the redefinition of user/f:"));

        // Pool: the trap stub rides one entry PAIRED with its message buffer.
        let pool_guard = pool.lock().unwrap();
        let stub_entry = pool_guard
            .iter()
            .find(|e| e.trap_msg.is_some())
            .expect("trap stub entry retained");
        assert_eq!(
            stub_entry.trap_msg.as_deref(),
            Some(info.provenance.as_str()),
            "the stub's baked buffer is the SAME pool entry's message"
        );
        assert_eq!(stub_entry.slot, Some(slot));

        // Slot: patched in place (no longer the old pointer, not NULL).
        let table = tables.get(&user).unwrap();
        let now = table.got.load_slot(slot);
        assert!(!now.is_null(), "slot must point at the stub");
        assert_ne!(now, old_ptr, "slot must no longer point at stale code");

        // Entry: the `code` field must hold the trap stub's handle — a
        // `code: None` + `ast: Some` broken entry would look "uncompiled" to
        // `derive_codegen_batch`'s synth-def sweep, which would silently
        // RECOMPILE the broken body against the new-world callee on the next
        // eval turn and overwrite the trap patch (the exact unsoundness the
        // trap closes; see src/CLAUDE.md §redefine.rs key invariants).
        let entry = table.get("g").expect("broken entry stays in the table");
        assert!(
            matches!(entry, ModuleEntry::Def { code: Some(_), .. }),
            "broken entry's code field must hold the trap stub's handle, \
             not None (synth-def sweep resurrection guard)"
        );
    }

    // spec: design/int/session-transaction.md §5.1 — the slot-less degenerate
    // arm: registry record only; NO pool push, NO trap patch.
    #[test]
    fn mark_broken_slotless_neg_registry_only_no_pool_no_patch() {
        let tables: SymbolTables = dashmap::DashMap::new();
        let user = ModuleFullPath::from("user");
        let mut ut = SessionSymbolTable::new_with_params(user.clone());
        ut.insert(Symbol::from("t"), def_with_callees(vec![], None));
        tables.insert(user.clone(), ut);

        let pool: RetentionPool = Mutex::new(Vec::new());
        let registry: BrokenRegistry = dashmap::DashMap::new();
        mark_broken(&tables, &pool, &registry, &fq("user", "t"), &fq("user", "f"), "err");

        assert!(registry.contains_key(&fq("user", "t")), "registry record");
        assert!(pool.lock().unwrap().is_empty(), "no pool push for a slot-less member");
    }

    // spec: design/int/session-transaction.md §"GOT exhaustion" (obligation 3)
    // — the session's allocation chokepoint surfaces exhaustion as an error,
    // never release-mode UB at slot GOT_TABLE_SIZE.
    #[test]
    fn got_exhaustion_surfaces_error_not_ub() {
        let module = ModuleFullPath::from("user");
        let mut st = SessionSymbolTable::new_with_params(module.clone());
        for _ in 0..GOT_TABLE_SIZE {
            allocate_live_got_slot(&mut st, &module).expect("in-bounds allocation");
        }
        let err = allocate_live_got_slot(&mut st, &module)
            .expect_err("slot GOT_TABLE_SIZE must be refused");
        assert!(
            err.to_string().contains("GOT slot table exhausted"),
            "got: {err}"
        );
        assert_eq!(st.next_got_slot, GOT_TABLE_SIZE, "high-water untouched by refusal");
    }

    /// Attach a real (empty-table) JIT `Code` handle so the entry reads as a
    /// "compiled caller" (`code: Some`) to [`stale_callers`]' filter.
    fn compiled(mut entry: ModuleEntry<Code>) -> ModuleEntry<Code> {
        if let ModuleEntry::Def { code, .. } = &mut entry {
            let empty_tables: cranelisp_types::SymbolTables<Code, ()> = dashmap::DashMap::new();
            // Same allow + rationale as the production composition site
            // (`inline_jit_codegen_for_names`): the Arc is the lifecycle root
            // for the mmap'd pages, never sent across threads.
            #[allow(clippy::arc_with_non_send_sync)]
            let jit_arc = std::sync::Arc::new(
                cranelisp_backend::jit::Jit::new(&empty_tables).expect("test jit"),
            );
            *code = Some(Code::jit(jit_arc));
        }
        entry
    }

    fn outcome(
        name: &str,
        kind: RedefKind,
        per_symbol: bool,
        prior_was_def: bool,
    ) -> RedefinitionOutcome {
        RedefinitionOutcome {
            fq: fq("user", name),
            kind,
            per_symbol,
            prior_was_def,
            old_slot: None,
            new_slot: None,
        }
    }

    // spec: design/int/s102-defect-wave.md §1 / session-transaction.md §9.1.1
    // — Matrix C route-trigger cells: the §18.1.1 print triggers on the T1
    // ROUTE (prior `Def`, outside per-symbol precision), whatever the surface
    // diff or the classifier's kind (a slot-less prior classifies `New` —
    // template redefinition rides `prior_was_def`, not the kind).
    #[test]
    fn t1_downgrade_trigger_route_cells() {
        // Template redefinition (poly→poly, scheme-equal or changed; also the
        // concrete-staged-over-template L-U1 shape): kind `New`, prior Def.
        assert!(is_t1_downgrade(&outcome("f", RedefKind::New, false, true)));
        // Concrete→overloaded/template displacement (slot-less staged): the
        // classifier's conservative arm.
        assert!(is_t1_downgrade(&outcome("f", RedefKind::AbiPreserving, false, true)));
        // Mutual exclusion with the per-symbol transaction (negative cell):
        // a concrete AbiChanging target never produces stale, and a body-only
        // AbiPreserving edit never triggers.
        assert!(!is_t1_downgrade(&outcome("f", RedefKind::AbiChanging, true, true)));
        assert!(!is_t1_downgrade(&outcome("f", RedefKind::AbiPreserving, true, true)));
        // Genuine New — no prior Def (incl. the prior-Import shadow shape,
        // 0484's territory): never a downgrade.
        assert!(!is_t1_downgrade(&outcome("f", RedefKind::New, false, false)));
        // Gate-exempt internals: never (an expression turn redefines __expr
        // every time — a per-turn trigger would break the L-D1 lane).
        assert!(!is_t1_downgrade(&outcome("__expr", RedefKind::AbiPreserving, false, true)));
        assert!(!is_t1_downgrade(&outcome(
            "__macro_m_clause_0",
            RedefKind::AbiPreserving,
            false,
            true
        )));
    }

    // spec: design/int/session-transaction.md §9.1.1 (S103, FIXME 0507 Issue 1
    // / F2) — the slot-refined trigger: a slotted prior replaced by a slotted
    // staged entry (deftype ctor re-entry) reuses the slot and late-binds
    // correctly, so it must NOT trigger the downgrade cure. A slot-shape change
    // (either side `None`) is required — the template (staged `None`) and
    // concrete-over-template (prior `None`) T1 cells still fire.
    #[test]
    fn t1_downgrade_trigger_f2_slot_refinement_ctor_reentry() {
        let with_slots = |old_slot, new_slot| RedefinitionOutcome {
            fq: fq("user", "Point"),
            kind: RedefKind::AbiPreserving,
            per_symbol: false,
            prior_was_def: true,
            old_slot,
            new_slot,
        };
        // Ctor re-entry: slotted prior → slotted staged (both present) — the
        // negative cell: reuse-and-patch late-binds, NO trigger.
        assert!(
            !is_t1_downgrade(&with_slots(Some(3), Some(3))),
            "slotted→slotted ctor re-entry must NOT trigger the T1 cure"
        );
        assert!(
            !is_t1_downgrade(&with_slots(Some(3), Some(7))),
            "even a fresh-slotted→slotted shape late-binds via the GOT"
        );
        // Template redefinition (slot-less staged): fires.
        assert!(is_t1_downgrade(&with_slots(Some(3), None)));
        // Concrete-over-template (slot-less prior): fires.
        assert!(is_t1_downgrade(&with_slots(None, Some(3))));
    }

    // spec: design/int/session-transaction.md §9.1.1 (F3) — a compiled
    // macro-clause caller of a redefined dependency fn is stale (its reverse
    // edge is now KEPT, not excluded) and renders as its owning user macro,
    // never the raw `__macro_*` symbol (§18.1.1).
    #[test]
    fn stale_callers_folds_macro_clause_to_owning_macro() {
        let tables: SymbolTables = dashmap::DashMap::new();
        let user = ModuleFullPath::from("user");
        let mut ut = SessionSymbolTable::new_with_params(user.clone());
        ut.insert(Symbol::from("dep"), concrete_def(fn_ty(vec![Type::Int], Type::Int), 0));
        // A compiled macro clause referencing the redefined dep fn.
        ut.insert(
            Symbol::from("__macro_m_clause_0"),
            compiled(def_with_callees(vec![fq("user", "dep")], Some(1))),
        );
        tables.insert(user.clone(), ut);

        let stale = stale_callers(&tables, &fq("user", "dep"));
        assert_eq!(
            stale,
            vec![fq("user", "m")],
            "the macro clause is stale and reports as its owning macro `m`"
        );
    }

    // spec: repl/spec.md §18.1.1 / design §9.1.1 — the stale set is exact
    // both ways: every compiled caller in; never-compiled template callers,
    // gate-exempt internals, and edge-less compiled symbols out; cross-module
    // callers included (module-qualified at render).
    #[test]
    fn stale_callers_set_exactness_cells() {
        let tables: SymbolTables = dashmap::DashMap::new();
        let user = ModuleFullPath::from("user");
        let lib = ModuleFullPath::from("lib");
        let mut ut = SessionSymbolTable::new_with_params(user.clone());
        ut.insert(Symbol::from("id"), concrete_def(fn_ty(vec![Type::Int], Type::Int), 0));
        // Compiled caller: IN.
        ut.insert(
            Symbol::from("gcall"),
            compiled(def_with_callees(vec![fq("user", "id")], Some(1))),
        );
        // Never-compiled template caller (code: None, slot-less): OUT —
        // late-binds at its next mint (§18.1.1 negative half).
        ut.insert(Symbol::from("bystander"), def_with_callees(vec![fq("user", "id")], None));
        // Compiled internal wrapper: OUT (the 0491 rule applies identically).
        ut.insert(
            Symbol::from("__expr"),
            compiled(def_with_callees(vec![fq("user", "id")], Some(2))),
        );
        // Compiled but no edge to the target: OUT.
        ut.insert(
            Symbol::from("unrelated"),
            compiled(def_with_callees(vec![fq("primitives", "add-i64")], Some(3))),
        );
        tables.insert(user.clone(), ut);
        // Cross-module compiled caller: IN.
        let mut lt = SessionSymbolTable::new_with_params(lib.clone());
        lt.insert(
            Symbol::from("x"),
            compiled(def_with_callees(vec![fq("user", "id")], Some(0))),
        );
        tables.insert(lib, lt);

        let stale = stale_callers(&tables, &fq("user", "id"));
        assert_eq!(stale, vec![fq("lib", "x"), fq("user", "gcall")], "exact set, sorted");
    }

    // spec: design/int/s102-defect-wave.md §1 — variant-awareness + base
    // grain: a caller compiled against a `$`-mangled mint of the target is
    // stale (its callee's base is the target) and reports at base-defn grain;
    // an old mint of the TARGET itself is not a member of its own set; a
    // target with no callers yields the empty set (section omitted).
    #[test]
    fn stale_callers_variant_aware_base_grain_and_empty() {
        let tables: SymbolTables = dashmap::DashMap::new();
        let user = ModuleFullPath::from("user");
        let mut ut = SessionSymbolTable::new_with_params(user.clone());
        ut.insert(Symbol::from("id"), concrete_def(fn_ty(vec![Type::Int], Type::Int), 0));
        // Compiled mono caller recorded against the MANGLED mint: IN, as `h`.
        ut.insert(
            Symbol::from("h$primitives/Int"),
            compiled(def_with_callees(vec![fq("user", "id$primitives/Int")], Some(1))),
        );
        // The target's own old mint (recursive self-edge shape): excluded.
        ut.insert(
            Symbol::from("id$primitives/Int"),
            compiled(def_with_callees(vec![fq("user", "id")], Some(2))),
        );
        tables.insert(user.clone(), ut);

        let stale = stale_callers(&tables, &fq("user", "id"));
        assert_eq!(stale, vec![fq("user", "h")], "mangled caller reports at base grain");

        assert!(
            stale_callers(&tables, &fq("user", "nobody")).is_empty(),
            "no callers → empty set (renders nothing)"
        );
    }

    // spec: repl/spec.md §18.1.1 — the section's bytes are exact: the header
    // line names the fully-qualified cause; the name line uses the §1.1
    // layout (bare in the current module, qualified elsewhere); an empty
    // stale set renders nothing (omission rule).
    #[test]
    fn report_render_stale_section_exact_header_and_omission() {
        let cur = ModuleFullPath::from("user");
        let mut r = TransactionReport::new(fq("user", "id"));
        r.stale.push(fq("user", "gcall"));
        r.stale.push(fq("lib", "x"));
        let text = r.render(&cur).unwrap();
        assert_eq!(
            text,
            "; stale: compiled callers keep the previous definition of user/id\n;  gcall lib/x",
            "byte-exact §18.1.1 section"
        );
        // Mutual exclusion in practice: a stale-only report has no
        // recompiled/broken sections.
        assert!(!text.contains("recompiled"), "{text}");
        assert!(!text.contains("broken"), "{text}");
        // Omission: an all-empty report renders nothing.
        assert!(TransactionReport::new(fq("user", "id")).render(&cur).is_none());
    }

    // spec: repl/spec.md §18.3 — the cascade report renders `; recompiled:` /
    // `; broken:` sections, bare names in the current module, module-qualified
    // elsewhere; empty sections are omitted; an empty report renders nothing.
    #[test]
    fn report_render_sections_and_qualification() {
        let cur = ModuleFullPath::from("user");
        let mut r = TransactionReport::new(fq("user", "f"));
        assert!(r.render(&cur).is_none(), "empty report renders nothing (L-D1/L-R3)");

        r.recompiled.push(fq("user", "g"));
        r.recompiled.push(fq("lib", "x"));
        r.broken.push((fq("user", "k"), "type error: expected primitives/String".into()));
        let text = r.render(&cur).unwrap();
        assert!(text.contains("; recompiled:\n;  g lib/x"), "got: {text}");
        assert!(text.contains("; broken:\n;  k — type error: expected primitives/String"), "got: {text}");

        // Broken-only: no recompiled section at all.
        let mut b = TransactionReport::new(fq("user", "f"));
        b.broken.push((fq("user", "k"), "e".into()));
        let text = b.render(&cur).unwrap();
        assert!(!text.contains("recompiled"), "empty recompiled section omitted: {text}");
    }

    // §10.3 R6 (Wave-D2) — the `; broken by the redefinition of …` provenance line
    // (`/sig`/`/info` on a broken symbol, §18.4) is REPL structured metadata: dim
    // colour-ON, byte-identical to the plain line colour-OFF (the broken-symbol
    // goldens stay green). Fail-on-revert pin for `broken_status_render`.
    // spec: repl/spec.md §10.3 R6 / §18.4 — broken-provenance line.
    #[test]
    fn broken_status_render_colour_on_is_r6_dim() {
        let cause = fq("user", "g");
        {
            let _g = crate::style::test_support::ColorGuard::force(true);
            assert_eq!(
                broken_status_render(&cause, "type error: expected primitives/String"),
                "\x1b[2m; broken by the redefinition of user/g: \
                 type error: expected primitives/String\x1b[0m"
            );
        }
        // Colour-OFF byte-identical to the pre-Wave-D2 plain provenance line.
        let _off = crate::style::test_support::ColorGuard::force(false);
        assert_eq!(
            broken_status_render(&cause, "e"),
            "; broken by the redefinition of user/g: e"
        );
    }

    // §10.3 R6 (Wave-D2) — the cascade/broken/stale report is REPL structured
    // metadata: colour-ON, every `;` line is dim (R6), reset before each `\n`
    // (§10.2 — no SGR crosses a line boundary); the newlines stay unstyled.
    // Fail-on-revert pin for the `TransactionReport::render` R6 conversion.
    // spec: repl/spec.md §10.3 R6 — cascade report metadata.
    #[test]
    fn report_render_colour_on_is_r6_dim_per_line() {
        let _g = crate::style::test_support::ColorGuard::force(true);
        let cur = ModuleFullPath::from("user");
        let mut r = TransactionReport::new(fq("user", "f"));
        r.recompiled.push(fq("user", "g"));
        let text = r.render(&cur).unwrap();
        assert_eq!(
            text,
            "\x1b[2m; recompiled:\x1b[0m\n\x1b[2m;  g\x1b[0m",
            "each report line is R6 dim, reset before the newline"
        );
        // Colour-OFF stays byte-identical to the plain report (non-TTY contract).
        drop(_g);
        let _off = crate::style::test_support::ColorGuard::force(false);
        assert_eq!(r.render(&cur).unwrap(), "; recompiled:\n;  g");
    }
}
