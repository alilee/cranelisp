//! `cranelisp-typecheck` — untyped AST → typed AST + populated symbol
//! tables. Owns Hindley-Milner inference (Algorithm W unification), trait
//! resolution, constrained-polymorphism detection + monomorphisation
//! analysis, and ADT exhaustiveness checking. It produces no code.
//!
//! # Bounded context
//!
//! Typecheck infers types, resolves traits, classifies polymorphism, and
//! analyses match exhaustiveness. Results land in two places: directly on
//! AST nodes (each node carries its inferred type and resolution choices),
//! and in the per-module symbol-table view supplied by the caller. The
//! crate carries no shared session state and no cadence — it is a pure
//! transform invoked synchronously by the integration layer, sitting
//! between frontend (which builds the input) and backend (which consumes
//! the output). It depends on `cranelisp-types` only — never on
//! `cranelisp-frontend` or `cranelisp-backend`.
//!
//! See `design/arch/bounded-contexts.md` §2 (Typecheck) for the canonical
//! cross-surface statement: the bounded-context narrative, the numbered
//! cross-context invariants 1–10, the module-locality rationale (Principle
//! 17 + Decisions 0044/0045/0046), and the placement rationale for "types
//! originated here" / "FQTypeName binding". This preamble carries the
//! **per-item** layer — each public item's own contract — and references
//! BC §2 for the cross-surface context (e.g. "see BC §2 invariant 8").
//!
//! # Public surface — the cluster-atomic boundary
//!
//! The typecheck entry surface is **one** free function per cluster, per
//! Decision 44 (amended FIXME 0167 for Approach B + [`SymbolTableAccess`];
//! 2026-05-13 third amendment collapsing the prior two-pass facade split
//! into a single function):
//!
//! ```ignore
//! pub fn check_forms<C, L>(
//!     parsed: Vec<ParsedEntry>,
//!     ctx: &mut SymbolTableAccess<'_, C, L>,
//!     symbol_tables: &SymbolTables<C, L>,
//!     module_aliases: &ModuleAliases,
//! ) -> Result<(), CheckError>;
//! ```
//!
//! - `parsed` — the full cluster's `ParsedEntry` list, produced by
//!   repeated `cranelisp_frontend::build_form` calls accumulated by the
//!   orchestrator (one `build_form` may yield several entries, e.g. a
//!   multi-clause `defmacro`). [`check_forms`] drives Pass 1 (register
//!   signatures into staging) over every entry, then Pass 2 (check bodies
//!   against the unioned staging+live view) over every entry. Pass-1-to-
//!   Pass-2 working state (`defn_type_vars`, default-method deferrals,
//!   generalisation inputs) is internal to the call frame — never crosses
//!   the facade.
//! - `ctx` — a [`SymbolTableAccess`] window the orchestrator constructs. In
//!   `Cluster` mode the read accessor unions staging over live
//!   (staging-first); the write accessor returns staging. In `Live` mode
//!   both hit the per-module live table directly. The ~91 register-call
//!   sites and ~51 read-access sites call these accessors uniformly — the
//!   staging-vs-live distinction is absorbed inside them (see BC §2
//!   invariant 2).
//! - `symbol_tables` — read-only access to all other modules' tables for
//!   resolving FQ value (`m2/foo`) and FQ type (`m2/SomeType`) references.
//!   Generic over `<C, L>` per Decision 32: typecheck is C/L-blind
//!   (production passes `SymbolTables<Code, ()>`; tests pass
//!   `SymbolTables<(), ()>`).
//! - `module_aliases` — read-only session-level `ModuleAliases`, threaded
//!   alongside `symbol_tables` (Principle 2 — narrow interfaces) because
//!   §8.6.6 qualified-name resolution may substitute an import/export alias
//!   for a `module_path` prefix. Typecheck **follows** aliases; it never
//!   populates them (see BC §2 invariant 8).
//!
//! ## Return contract
//!
//! - `Ok(())` — Pass 1 staged signature shells, Pass 2 staged
//!   body-checked entries that superseded the shells; per-symbol Pass-2
//!   side products landed on staging `ModuleEntry::Def` fields (BC §2
//!   invariant 3a). The orchestrator commits the whole staging table
//!   atomically into live on cluster completion.
//! - `Err(CheckError::Gap(ResolutionGap::SymbolTypechecked(fq)))` — an FQ
//!   value reference can't resolve (its module isn't yet typechecked). The
//!   orchestrator catches, loads + typechecks `fq.module`, then **retries
//!   the whole `check_forms` call** with the same `parsed` list. Staging is
//!   discarded; a fresh frame is constructed for the retry — the cluster is
//!   atomic, there is no sub-cluster retry granularity.
//!   `ResolutionGap::Type(fqt)` is the FQ-type-reference twin.
//!   ([`check_forms`] asks for `SymbolTypechecked` not `SymbolInMemory`:
//!   typecheck needs only the entry's `Scheme`, not its compiled code —
//!   macros are already expanded by the time it runs.)
//! - `Err(CheckError::TypeError { message, location })` — a genuine,
//!   non-recoverable type error. The orchestrator drops staging on the
//!   floor; the live table is byte-identical to its pre-cluster state.
//!
//! **Post-`Err` state contract.** On any `Err`, no live mutation has
//! occurred — the orchestrator commits only on whole-cluster `Ok`, and
//! staging dissolves with the call frame. That staging-drop **is** the
//! whole of typecheck-state rollback: there is no caller-driven snapshot
//! (the `snapshot`/`restore` primitive + `ReplSnapshot` were deleted as
//! dead code in S73). The type-var pool ([`CheckState`]'s `next_id`) is
//! monotonic and intentionally NOT rolled back across the retry boundary —
//! fresh vars from a failed attempt are abandoned, preserving the
//! TypeId-consistency invariant (see BC §2 invariant 7).
//!
//! **Cluster atomicity.** [`check_forms`] is the unit of typecheck
//! atomicity. A cluster is one form (a non-`begin` REPL input), the
//! contents of `(begin form₁ … formN)` (an explicit REPL cluster), or a
//! file's non-structural forms (batch). See `facades/int.md`
//! §"`process_cluster`" for the orchestrator side.
//!
//! # Cluster-check scaffolding — exposed for tests / fine-grained callers
//!
//! [`CheckState`], [`SymbolTableAccess`], [`SymbolTableRead`],
//! [`SymbolTableMut`], and [`TypeCheckEnv`] exist for tests and for crates
//! constructing typecheck driver state directly; `int` uses [`check_forms`]
//! exclusively in production.
//!
//! - [`CheckState`] — per-call transient state (type-var pool / `next_id`,
//!   substitution, lexical scope, deferred resolutions, the current
//!   module). Constructed with `CheckState::new(module)`;
//!   `current_module()` reports the module the state is scoped to.
//! - [`SymbolTableAccess`] — the staging-vs-committed dispatch choke point.
//!   Two modes: `Live { modules, current_module }` (direct per-module live
//!   access — REPL introspection, fine-grained drivers) and
//!   `Cluster { modules, staging, current_module }` (staging-over-live
//!   union during a cluster check). `current_symbol_table()` /
//!   `current_symbol_table_mut()` return the borrow guards below.
//! - [`SymbolTableRead`] / [`SymbolTableMut`] — the **single pair** of
//!   read+write borrow guards crossing or touching the typecheck surface
//!   (S72 W2 /review I-2; user-arbitrated unification under the
//!   `SymbolTable*` names — the type names *what* is accessed, the
//!   `SymbolTable`, not the access mode). Both [`SymbolTableAccess`] and the
//!   interior [`TypeCheckEnv`] accessors return this same pair — no
//!   parallel `pub(crate)` `SymbolTableRead`/`SymbolTableMut` and no
//!   `ClusterRead`/`ClusterWrite` alias exist. A duplicate pair is a
//!   structural defect future audits assert against. `SymbolTableRead`
//!   exposes `.view() -> View<'_, C, L>` (Cluster → `View::union(staging,
//!   live)` staging-first; Live → `View::single(live)`); `SymbolTableMut`
//!   implements `Deref`/`DerefMut` to `SymbolTable<C, L>` so the
//!   register-call sites write through uniformly. They are
//!   internal-but-exposed RAII guards (the cluster-mode return holds two
//!   borrows simultaneously; returning `View` directly would force the
//!   caller's borrow to outlive the staging borrow it depends on) and are
//!   **not** `#[non_exhaustive]` — the `Live`/`Cluster`(`Staging`)
//!   discriminant is a closed binary cluster-vs-live switch, not an open
//!   evolution surface.
//! - [`TypeCheckEnv`] — borrowed references to session-owned shared state
//!   (the `DashMap` of module tables + the `AtomicU32` type-var counter +
//!   the alias table). Its public surface narrows to `new` + `next_type_id`
//!   (the as-designed narrowing target, Sprint 67 PIF row 21); the ~28
//!   per-symbol lookups, module-table accessors, and introspection helpers
//!   are `pub(crate)` callee-side helpers (all callers live inside
//!   [`check_forms`]'s frame). The `current_symbol_table[_mut]()` accessors
//!   return the same single-pair guards as [`SymbolTableAccess`].
//!
//! There is no public pass discriminator and no public accumulator type:
//! `CheckPass`, `FormCheckResult`, and `ModuleCheckAccumulator` were all
//! removed per Decision 44's third amendment — pass ordering and cross-pass
//! state are internal to [`check_forms`]'s frame, with `pub(crate)`
//! scaffolding only.
//!
//! # Result + error types
//!
//! - [`CheckResult`] — pared to the two cross-cluster items the
//!   orchestrator surfaces to the REPL display layer: `display:
//!   Option<DisplayInfo>` (last-form display info) + `warnings:
//!   Vec<Warning>` (cluster-scope warnings). Per-symbol Pass-2 side
//!   products land on staging `ModuleEntry::Def` fields, NOT here
//!   (BC §2 invariant 3a).
//! - [`CheckError`] — `Gap(ResolutionGap)` (recoverable cross-module
//!   dependency) or `TypeError { message, location: ErrorLocation }`
//!   (non-recoverable; `location` carries Decision 39's coordinates-as-data).
//!
//! # Trace hooks — observability layer
//!
//! The crate exposes the cross-crate `SymbolTable`-ensure hook
//! ([`SymbolTableEnsureHook`], [`SymbolTableEnsureOutcome`],
//! [`install_symbol_table_ensure_hook`], [`emit_symbol_table_ensure`]),
//! re-exported at the crate root for convenience. `int`'s observability
//! layer wires this to its scheduler trace sink at startup (per FIXME 0103
//! trace plan, Decision 40); re-installing overwrites without composition.
//! `emit_symbol_table_ensure` is called only from inside typecheck but is
//! `pub` so the observability split is consistent across crates.
//!
//! # Module-lifecycle free function
//!
//! [`advance_next_id_past_table`] is the TypeId-consistency primitive split
//! out of the pre-S67 `restore_cached_module`. The `int`-side cache-hit
//! branch composes it alongside `cranelisp_types::install_module`; together
//! they form the lifecycle pair used by `CompilerSession::introduce_module`.
//!
//! # Types originated here
//!
//! Per Principle 15's placement heuristic, [`CheckResult`], [`CheckError`],
//! [`CheckState`], [`TypeCheckEnv`], [`SymbolTableAccess`],
//! [`SymbolTableRead`], and [`SymbolTableMut`] live in `cranelisp-typecheck`
//! (referenced by `int` only — the borrow guards are typecheck-interior per
//! the single-pair invariant). `ResolutionGap` is the cross-cutting
//! exception — referenced by both the frontend facade (`ExpansionError::Gap`)
//! and typecheck (`CheckError::Gap`), so it lives in `cranelisp-types` per
//! the multi-consumer rule; `View` likewise. Multi-consumer dependency types
//! (`Scheme`, `Subst`, `Type`, `TypeId`, `ResolvedCall`, `MethodResolutions`,
//! `TypeDefInfo`, `DisplayInfo`, `MonoDefn`, `Warning`, `TraitDecl`, …) live
//! in `cranelisp-types` because backend codegen also consumes them. There
//! are **no** crate-root re-exports of `cranelisp-types` items (the legacy
//! `CranelispError` / `TopLevel` convenience re-exports were removed S73 per
//! Principle 15 — callers import them directly from `cranelisp-types`). See
//! BC §2 "Types originated here" for the placement rationale.
//!
//! # Builtin / import-export registration is not a typecheck concern
//!
//! There is no builtin-registration entry point. Synthetic-module assembly
//! (seeding `primitives`/`macros` + the `Option`/`IO`/`Trace`/`TestResult`
//! ADTs) left this crate's bounded context — it is content construction, not
//! type-checking; `int` reconstructs the mount at session init (FIXME 0242),
//! and the `builtins` module is now entirely `#[cfg(test)]` test-support.
//! Likewise `register_imports`/`register_exports` are **struck** (not
//! demoted): import/export registration is frontend's StructuralDecl
//! concern, processed before typecheck runs — `ParsedEntry` has no
//! `Import`/`Export` variant, so typecheck never receives one. The Gap
//! return (BC §2 invariant 8) is the replacement for the struck
//! import-registration machinery.

mod adt;
#[cfg(test)]
mod builtins;
mod checker;
mod cluster;
mod form;
mod infer;
mod ownership;
mod program;
mod resolve;
mod result;
mod scheme;
mod signature_match;
mod scope;
mod trace;
mod traits;
mod unify;

// Public API
//
// There is no builtin-registration entry point. Synthetic-module assembly
// (seeding `primitives`/`macros` + the `Option`/`IO`/`Trace`/`TestResult`
// ADTs) left this crate's bounded context: typecheck checks forms against
// caller-populated symbol tables; it does not construct the language. The
// production mount is reconstructed by `int` at session init (FIXME 0242).
// The `builtins` module is now entirely `#[cfg(test)]` test-support — the
// minimal synthetic seed the unit suite needs (FIXME 0239 test-oracle).
pub use checker::{CheckState, PreludeFallback, TypeCheckEnv, advance_next_id_past_table};
pub use cluster::{SymbolTableAccess, SymbolTableMut, SymbolTableRead};
pub use form::{check_forms, check_type_expr};
pub use result::{CheckError, CheckResult};
pub use signature_match::{signature_matches_exact, signature_matches_partial};
pub use trace::{
    SymbolTableEnsureHook, SymbolTableEnsureOutcome, emit_symbol_table_ensure,
    install_symbol_table_ensure_hook,
};
