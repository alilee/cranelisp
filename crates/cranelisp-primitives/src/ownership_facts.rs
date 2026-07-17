//! Declared ownership fact-table for primitives — the leaf seeding for
//! pass5's ownership fixpoint (S102 CS-B; spine `design/arch/ownership-inference.md`
//! §3.1(a), typecheck-side `design/typecheck/ownership-inference.md` §9/§13.4).
//!
//! Each `DefKind::Primitive` entry carries a hand-declared [`ModeSummary`] as
//! ordinary entry payload — the SAME carrier inferred summaries ride. pass5
//! reads it as a **constant leaf boundary condition** (`§9.2`): never on the
//! worklist, zero fixpoint cost, consulted at `Apply` classification through
//! [`ModuleEntry::mode_summary`](cranelisp_types::ModuleEntry::mode_summary).
//!
//! # The seed and the split ruling
//!
//! The facts are transcribed from the `design/backend/ring2-rc.md` §3.3
//! extern-consumption audit (Principle 7 — the audit is the single source):
//!
//! - **only-read heap params** (the fn returns a scalar and merely inspects its
//!   args — `str-eq`, `str-len`, the `?`-predicates, `vec-len`, `neq-string`)
//!   are declared [`Mode::Borrowed`] (the analysis fact) while the extern body
//!   keeps consuming ([`ParamFlow::Consumed`]) — the §9.1 split ruling: the
//!   ABI convention is unchanged (Decision-24), only the *analysis* stops being
//!   poisoned so the flagship sum-loop inference survives (§9.2).
//! - **transforming heap params** (the fn builds a fresh heap result —
//!   `str-concat`, `substring`, …, `parse-int`, `quote-sexp`) are declared
//!   [`Mode::Owned`] / [`ParamFlow::Consumed`] / [`ResultMode::Fresh`].
//! - **scalar params** (`Int`/`Bool`/`Float`) are [`Mode::Copy`] — no RC
//!   identity at all — with a [`ResultMode::Fresh`] result. Mechanical, zero
//!   audit dependency.
//! - **`string-identity`** is the one alias leaf: the arg flows out unchanged,
//!   so [`ResultMode::AliasOf`]`(0)` (why `AliasOf` is in the vocabulary at all).
//! - **the inline `vec` family** (`vec-get`/`vec-set`/`vec-push`) carries the
//!   projection/COW vocabulary (§9.3): `vec-get` reads/projects →
//!   `ProjectionOf(0)`; `vec-set`/`vec-push` are COW → [`ResultMode::MayAliasOf`]`(0)`
//!   (the result is EITHER a fresh copy OR param 0's own vec, decided at
//!   runtime — NOT `Fresh`; a false `Fresh` was the vec-assoc UAF root, §3.7),
//!   value param `IntoResult`. These two are the ONLY convention-deviating
//!   emission in the table (they borrow-and-may-return their source vec through
//!   `vec_codegen`'s `SourceOwnership::Borrowed` inline path); the only-read
//!   scalar-returning leaves (`str-eq`/`vec-len`/…) borrow their heap arg yet
//!   return a genuinely fresh SCALAR, so `Fresh` there is truthful, not a
//!   deviation — see the declared-facts contract in `CLAUDE.md`.
//!
//! # The Decision-24 conservative default (⊤-on-absence)
//!
//! A primitive with a heap param but **no fact-table classification** returns
//! [`None`] — the Decision-24 conservative point. Absence reads as
//! `Owned`/`Retained`/`Fresh` through the ⊤-on-absence accessors on
//! [`ModeSummary`], so `None` is strictly additive and monotone-sound (spine
//! §6.1). This is *the* default rule: never invent a fact for an unclassified
//! heap leaf.
//!
//! `DefKind::PrimitiveExtern` (`sconcat`, `bind`, …) carries no summary at all —
//! it dispatches by-name (`Linkage::Import`), never constructs an entry in this
//! crate, and stays at the pinned Decision-24 boundary (spine §3.1
//! named-extern pin). The `neq-*` family and `sconcat` likewise have shims but
//! no `ModuleEntry` here (they resolve through the `Eq.!=` trait path / the
//! synthetic `macros` module), so this classifier is never consulted for them;
//! `neq-string` is nonetheless listed in the only-read set so that IF an entry
//! is ever registered it transcribes the audit row (FIXME 0504) by construction.

use cranelisp_types::{Mode, ModeSummary, ParamFlow, ResultMode, Type};

/// A scalar type has no RC identity — always [`Mode::Copy`].
pub(crate) fn is_scalar(ty: &Type) -> bool {
    matches!(ty, Type::Int | Type::Bool | Type::Float)
}

/// Assemble a [`ModeSummary`] from the ABI-bearing modes/result and the
/// advisory per-param flow. `spark_ops` stays empty (⊤ = Crossing, the
/// conservative confinement point) and `result_unique` stays `false`
/// (increment I) via `Default`.
fn summary(param_modes: Vec<Mode>, param_flow: Vec<ParamFlow>, result: ResultMode) -> ModeSummary {
    ModeSummary { param_modes, result, param_flow, ..Default::default() }
}

/// The declared ownership summary for a primitive, keyed by its spec name and
/// concrete type. `None` = the Decision-24 conservative default (an
/// unclassified heap leaf, or a non-`Fn` type).
///
/// This is a name-keyed table **at the primitive's own declaration site** — it
/// is emphatically NOT a typecheck-side privileged-by-name table (Principle 19);
/// facts live where the entity is declared (Principle 7) and reach the pass
/// through the ordinary entry payload.
pub(crate) fn declared_mode_summary(name: &str, ty: &Type) -> Option<ModeSummary> {
    // Explicit-shape leaves: the result mode or per-param flow differs from the
    // mechanical Fresh/uniform-Consumed case.
    match name {
        // The one alias leaf — arg returned unchanged (audit "Returns arg
        // unchanged? Yes"), flows out through the return.
        "string-identity" => {
            return Some(summary(vec![Mode::Owned], vec![ParamFlow::IntoResult], ResultMode::AliasOf(0)));
        }
        // Inline vec family (§9.3) — projection vocabulary.
        "vec-get" => {
            // [(Vec a), Int] — read/project the element rc-free against the root.
            return Some(summary(
                vec![Mode::Borrowed, Mode::Copy],
                vec![ParamFlow::Consumed, ParamFlow::Consumed],
                ResultMode::ProjectionOf(0),
            ));
        }
        "vec-set" => {
            // [(Vec a), Int, a] — COW: the result is EITHER a fresh copy (rc>1
            // arm) OR param 0's own vec returned in place (rc==1 arm), decided
            // at runtime ⇒ `MayAliasOf(0)`, NOT `Fresh` (the §3.7 truthful
            // declaration — a false `Fresh` here let the return-protect elision
            // free a vec the caller still owns, the vec-assoc UAF class). The
            // value param still flows into the (fresh or in-place) result.
            return Some(summary(
                vec![Mode::Owned, Mode::Copy, Mode::Owned],
                vec![ParamFlow::Consumed, ParamFlow::Consumed, ParamFlow::IntoResult],
                ResultMode::MayAliasOf(0),
            ));
        }
        "vec-push" => {
            // [(Vec a), a] — COW: `MayAliasOf(0)` (copy arm vs rc==1 in-place
            // arm), value param flows into the result. See `vec-set` (§3.7).
            return Some(summary(
                vec![Mode::Owned, Mode::Owned],
                vec![ParamFlow::Consumed, ParamFlow::IntoResult],
                ResultMode::MayAliasOf(0),
            ));
        }
        _ => {}
    }

    let params: &[Type] = match ty {
        Type::Fn(params, _) => params,
        _ => return None,
    };

    // Mechanical all-`Copy` / `Fresh` — no heap param, zero audit dependency
    // (ring0 scalar ops + `int`/`float`/`bool-to-string`). Includes the nullary
    // and all-scalar shapes.
    if params.iter().all(is_scalar) {
        return Some(summary(vec![Mode::Copy; params.len()], Vec::new(), ResultMode::Fresh));
    }

    // Heap-param leaves classified by the ring2-rc §3.3 audit + §9.1 split.
    let heap_mode = match name {
        // Only-read: the fn returns a scalar and merely inspects its heap args
        // ⇒ declared `Borrowed` (analysis fact); the extern still consumes.
        "str-eq" | "neq-string" | "str-len" | "starts-with?" | "ends-with?" | "contains?"
        | "vec-len" => Mode::Borrowed,
        // Transforming: the fn builds a fresh heap result ⇒ `Owned`/`Consumed`.
        "str-concat" | "substring" | "char-at" | "split" | "join" | "replace" | "trim"
        | "to-upper" | "to-lower" | "parse-int" | "quote-sexp" => Mode::Owned,
        // Unclassified heap leaf ⇒ Decision-24 conservative default.
        _ => return None,
    };

    let param_modes = params
        .iter()
        .map(|p| if is_scalar(p) { Mode::Copy } else { heap_mode })
        .collect();
    // The extern consumes every heap arg (Decision-24 convention); scalar
    // positions carry a neutral `Consumed` placeholder (advisory, vacuously
    // true for a by-value scalar with no RC).
    let param_flow = vec![ParamFlow::Consumed; params.len()];
    Some(summary(param_modes, param_flow, ResultMode::Fresh))
}

#[cfg(test)]
mod tests;
