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
//! # Read-path increment (monotone soundness)
//!
//! **No backend mechanism consumes summaries in increment I** (that is Wave
//! 11). Summaries are emitted but UNconsumed ⇒ codegen stays strictly
//! Decision-24 and the pass is **behaviour-neutral for codegen**. Every fact is
//! monotone-sound: widening toward `Owned`/`Escapes`/`Crossing` is always
//! correct, only less precise (spine §6.1). Absence is ⊤ everywhere, read
//! through the [`ModeSummary`](cranelisp_types::ModeSummary) conservative-read
//! accessors — no code path here indexes the raw vectors.
//!
//! # The toggle
//!
//! When `CRANELISP_NO_OWNERSHIP` is set, [`crate::checker::TypeCheckEnv::pass5_ownership`]
//! returns at entry and emits NOTHING (§13.5) — no summaries, no site facts, no
//! value-use marks. The `.meta.json` payloads are then field-identical to a
//! pre-pass5 compile (serde: absent optional fields serialize away).
//!
//! # Module composition (Principle 23 — strategy seams as named submodules)
//!
//! - [`classify`] (CS-1) — the §2.1 static-call classifier + the `Copy` predicate.
//! - [`transfer`] (CS-2) — the pure per-body transfer function.
//! - [`fixpoint`] (CS-3) — the per-cluster worklist driver + SCC seeding + memo.
//! - [`confinement`] (CS-3) — strand-context classification + the per-cell join.
//! - [`publish`] (CS-4) — summary / site-fact / value-use publication + the H5 trace.

pub(crate) mod classify;
pub(crate) mod confinement;
pub(crate) mod fixpoint;
pub(crate) mod publish;
pub(crate) mod sites;
pub(crate) mod trace;
pub(crate) mod transfer;

pub(crate) use fixpoint::run_pass5;
