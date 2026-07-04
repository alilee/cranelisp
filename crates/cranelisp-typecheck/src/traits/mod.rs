//! Trait registration, impl checking, method resolution, and monomorphisation.
//!
//! Ring 2A: traits provide constrained polymorphism. Operators like `+` are
//! resolved as trait methods (`Num.+$Int`), not builtin primitives.
//!
//! Trait declarations are stored as `ModuleEntry::TraitDecl` entries on per-module
//! SymbolTables. Trait implementations are stored as `ModuleEntry::TraitImpl` entries.
//! Method-to-trait reverse lookup uses the `trait_origin` field on `ModuleEntry::Def`.
//! The old `TraitRegistry` and `ImplRegistry` global caches have been eliminated.
//!
//! ## Submodule layout (S87 Wave 5e decomposition)
//!
//! The former monolithic `traits.rs` is split into six cohesive concern
//! clusters (`design/typecheck/s87-traits-decomposition.md` §1). All items
//! remain crate-private — `lib.rs` declares `mod traits;` (never `pub`), so
//! nothing here crosses the crate boundary (`public-api.txt` byte-identical).
//!
//! - [`registry`] — the write-side: a parsed `TraitDecl` becomes symbol-table
//!   state (`ActiveConstraints` + per-method `Def`s).
//! - [`impl_check`] — impl recording + method-body type-checking.
//! - [`dispatch`] — the read-side: at a call site, decide which impl a
//!   trait-method call resolves to (incl. the D-default + HKT dispatch helpers).
//! - [`monomorphise`] — the monomorphisation engine + the mangling primitives.
//! - [`type_resolve`] — the `TypeExpr -> Type` resolution free functions.

mod registry;
mod impl_check;
mod dispatch;
mod monomorphise;
mod type_resolve;

// Crate-internal re-exports. The other typecheck modules reach these as
// `crate::traits::X` (unchanged from the pre-split `traits.rs` paths); the
// sibling test modules reach the production items through `use super::*`.
// NONE are `pub` — `mod traits` is private, so `public-api.txt` is unaffected.
pub(crate) use registry::*;
pub(crate) use monomorphise::*;
pub(crate) use type_resolve::*;
// `dispatch`'s only `pub(crate)` free fn (`primitive_for_trait_method`) is
// consumed internally by `dispatch.rs` directly; its tests moved to the
// `dispatch::tests` sibling (S102 FIXME 0497 de-pool), reaching it via their
// own `use super::*` — so the traits-root test-only re-export is retired.

/// Mangle a trait-method dispatch/definition symbol with FULL nominal type
/// identity in the `$Type` suffix (home-qualified head). Grammar:
/// `{trait}.{method}${home}/{Type}` (e.g. `Describe.describe$a/Widget`,
/// `Show.show$primitives/Int`).
///
/// **Why FQ (S102 — 4th lossy-head cure).** Spec §3.8.4: two same-bare-named
/// types from different modules (`a/Widget` ≠ `b/Widget`) are DISTINCT. The
/// pre-S102 grammar used the BARE type head (`Describe.describe$Widget`), so
/// both minted the same linker symbol and their two impl bodies collided —
/// silent wrong dispatch. Home-qualifying the `$Type` suffix makes the symbol
/// collision-free by construction (Principle 20), the same cure 0519 applied
/// to the mono-instance mangler.
///
/// **Lock-step invariant (name-path == definition-path).** BOTH the dispatch
/// site (`dispatch::try_resolve_trait_method`) and the definition/writeback
/// site (`impl_check`) MUST mint through THIS one function against the SAME
/// canonical `FQTypeName`, or the call's linker symbol won't match the impl
/// method's definition symbol and dispatch won't resolve. The dispatch side
/// derives the `FQTypeName` from the resolved argument's OWN type (an ADT
/// carries its home directly — re-resolving the bare head in the caller's scope
/// is exactly the lossy-head bug); the definition side derives it from
/// `resolve_type` on the impl target. Both land on the same `module/Type`.
///
/// **Grain: receiver-type HEAD, not arg-recursed.** The suffix carries the
/// receiver type's FQ HEAD only; ADT type-args are NOT recursed (unlike the
/// mono-instance sig). This MATCHES the trait-impl registration grain — the
/// definition side names by `impl_target_name_or_panic` (the head), so the two
/// impls `(impl T (Vec Int))` / `(impl T (Vec String))` already share one head
/// key on BOTH sides. Arg-distinguishing the trait-method grain would require a
/// coordinated change to impl registration too; it is out of scope here.
pub(crate) fn mangle_trait_method(
    trait_disp: &str,
    method: &str,
    fq_type: &cranelisp_types::FQTypeName,
) -> String {
    format!("{trait_disp}.{method}${fq_type}")
}

// The former pooled `traits/tests.rs` (~41 tests) was de-pooled (S102 FIXME
// 0497) across per-submodule sibling test modules — `registry/tests.rs`,
// `impl_check/tests.rs`, `dispatch/tests.rs`, `monomorphise/tests.rs`,
// `type_resolve/tests.rs` — each declared `#[cfg(test)] mod tests;` next to
// the code it exercises. Their shared fixtures + assertion helpers live in
// `test_helpers` so no test is duplicated (Principle 23).
#[cfg(test)]
mod test_helpers;
