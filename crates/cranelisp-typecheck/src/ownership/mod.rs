//! `pass5_ownership` — the interprocedural ownership-inference pass
//! (`design/typecheck/ownership-inference.md`; spine
//! `design/arch/ownership-inference.md`).
//!
//! One post-monomorphisation lifetime/flow analysis over the mono call graph,
//! emitting the increment-I query outputs (Q1 borrow modes, Q2 escape, Q3
//! confinement, plus the projection/result facts and declared-leaf reads). It
//! runs inside `finalize_check_result_inner` after `pass4_monomorphise` and the
//! callee write-back, over the cluster's codegen-bound callables.
//!
//! # Read path and monotone soundness
//!
//! The backend DOES consume these summaries (the increment-I "emitted but
//! UNconsumed, behaviour-neutral for codegen" statement this paragraph used to
//! carry has been false since the read path landed): among others,
//! `backend::compiler::fn_compiler::return_is_fresh_by_summary` elides a
//! callee's return protect exactly when a summary is PRESENT and says
//! `ResultMode::Fresh`. Every fact must therefore be monotone-sound in its own
//! right: widening toward `Owned`/`Escapes`/`Crossing` is always correct, only
//! less precise (spine §6.1).
//!
//! **`Fresh` is the exception to "widening is free", and it is the one that has
//! bitten.** It is the result axis's STRONGEST claim, not its ⊤ — the ⊤ is
//! `ResultMode::MayAliasAny` (S121, §19.2). A summary is publishable only as the
//! output of a converged transfer walk; a cluster that does not converge, and a
//! frame the walk never visits, publish NOTHING (§19.5/§19.6). Absence is the
//! single spelling of the conservative point and is read through the
//! [`ModeSummary`](cranelisp_types::ModeSummary) conservative-read accessors —
//! no code path here indexes the raw vectors.
//!
//! # The toggle
//!
//! When `CRANELISP_NO_OWNERSHIP` is set
//! ([`cranelisp_types::ownership_analysis_off`]), the pass-5 driver
//! [`run_pass5`] returns at entry and emits NOTHING (§13.5) — no summaries, no site facts, no
//! value-use marks. The `.meta.json` payloads are then field-identical to a
//! pre-pass5 compile (serde: absent optional fields serialize away).
//!
//! # Module composition (Principle 23 — strategy seams as named submodules)
//!
//! - [`classify`] (CS-1) — the §2.1 static-call classifier + the `Copy` predicate.
//! - [`transfer`] (CS-2) — the pure per-body transfer function.
//! - [`fixpoint`] (CS-3) — the per-cluster worklist driver + SCC seeding + memo.
//! - [`confinement`] (CS-3) — strand-context classification + the per-cell join.
//! - [`uniqueness`] (CS-3, increment II) — the uniqueness stratum:
//!   `result_unique` chaining + `unique_static` write-path site facts (§14.2).
//! - [`publish`] (CS-4) — summary / site-fact / value-use publication + the H5 trace.

pub(crate) mod classify;
pub(crate) mod confinement;
pub(crate) mod fixpoint;
pub(crate) mod publish;
pub(crate) mod sites;
pub(crate) mod trace;
pub(crate) mod transfer;
pub(crate) mod uniqueness;

pub(crate) use fixpoint::run_pass5;
