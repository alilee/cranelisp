// HeapCategory + classifier relocated to cranelisp-backend per S69 Sub 38
// (bounded-context: backend-internal codegen classification). HeapHeader
// retains as the cross-crate layout contract shared with the backend-emitted
// runtime library (cranelisp-primitives / cranelisp-intrinsics).

use std::collections::HashSet;
use std::mem::{self, offset_of};

use crate::{
    CodeStore, ConcreteType, DefKind, FQTypeName, LinkerStore, ModuleEntry, Symbol, SymbolTable,
    SymbolTables, Type,
};

/// Universal header for all heap-allocated values.
/// All offsets in the compiler derive from this struct's layout.
/// Lives in cranelisp-types so both backend and runtime can reference it.
#[repr(C)]
pub struct HeapHeader {
    /// Total allocation size in bytes (header + payload). Used by dealloc.
    pub alloc_size: i64,
    /// Reference count. Accessed via atomic_rmw (Release ordering) per NFR C.4.1.
    /// Initial value: 1 (the allocating binding owns the value).
    pub rc: i64,
}

impl HeapHeader {
    pub const SIZE: usize = mem::size_of::<Self>(); // 16
    pub const ALLOC_SIZE_OFFSET: i32 = offset_of!(Self, alloc_size) as i32; // 0
    /// RC field offset — single source of truth for RC location.
    /// emit_rc_inc and emit_rc_dec use this exclusively.
    pub const RC_OFFSET: i32 = offset_of!(Self, rc) as i32; // 8
}

// Compile-time assertions — fail at build time if layout changes.
const _: () = assert!(HeapHeader::SIZE == 16);
const _: () = assert!(HeapHeader::ALLOC_SIZE_OFFSET == 0);
const _: () = assert!(HeapHeader::RC_OFFSET == 8);

// ---------------------------------------------------------------------------
// R5 value-representation flattening — the single-sourced Copy/value-layout
// predicate (increment II; `design/arch/ownership-inference.md` §6.3,
// `design/backend/ownership-codegen.md` §7.1).
// ---------------------------------------------------------------------------

/// Maximum machine-word size of a value-flattened concrete type in the first R5
/// landing — **one word (8 bytes)**.
///
/// Every ABI surface in the system is uniformly `i64` today (params, returns,
/// `Vec` slots, ADT fields, closure captures, GOT-dispatched signatures), so a
/// one-word value **is** its word and crosses every existing boundary with
/// **zero ABI change** — no boxing-at-edges, no multi-slot parameter lowering
/// (`design/backend/ownership-codegen.md` §7.2). Multi-word flattening is the
/// designed extension, deferred with a named trigger; bumping this constant is a
/// representation change and therefore a `CACHE_SCHEMA_VERSION`-bump event.
pub const VALUE_LAYOUT_MAX_WORDS: usize = 1;

/// The value-representation verdict for a concrete type.
///
/// A [`Some`] result from [`value_layout`] means the type is **Copy-eligible and
/// value-flattenable within the size bound**: it is laid out inline (in
/// registers, `Vec` slots, or parent-ADT fields) with **no header, no refcount,
/// no drop glue** — the backend's `HeapCategory::Value` arm
/// (`design/backend/ownership-codegen.md` §7.1). A [`None`] means the type keeps
/// its current heap/scalar representation verbatim.
///
/// This is a **classification result** (the `HeapCategory` analogue), not a
/// persisted DTO — it is recomputed from the type defs on every compile and
/// never serialised. `#[non_exhaustive]` because the multi-word extension
/// (§7.2) will add layout detail (alignment / tag-word placement); consumers
/// read it as `ValueLayout { words, .. }`.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ValueLayout {
    /// Number of machine words the flattened representation occupies
    /// (`≤ VALUE_LAYOUT_MAX_WORDS`). A single scalar-payload wrapper such as
    /// `(Cell Int)` is `1`; a zero-field single-ctor product is `0`.
    pub words: usize,
}

/// The **single-sourced** Copy/value-layout predicate — is this concrete type
/// representable as an inline value of `≤ VALUE_LAYOUT_MAX_WORDS` words?
///
/// `Some(ValueLayout { words })` ⟺ the type is **Copy-eligible** (a scalar, or
/// a single-constructor ADT whose fields are all transitively value-eligible)
/// **∧** its fully-flattened representation is `≤ VALUE_LAYOUT_MAX_WORDS` words.
/// `None` ⟺ the type keeps today's heap/scalar representation.
///
/// # Why this lives in `cranelisp-types` (soundness single-sourcing)
///
/// Two crates must agree on this verdict or the system is **unsound**, not
/// merely inconsistent: typecheck's `Copy` mode classifier (a param moded
/// `Copy` whose representation the backend did *not* flatten is a pointer
/// bit-copied with no `rc_inc` — a missing-inc use-after-free) and the
/// backend's layout decision (`HeapCategory::classify`'s `Value` arm). Two
/// independently-maintained copies of a soundness-**coupled** pure predicate is
/// the Principle-7 mirror-defect class, so **one** predicate lives here beside
/// [`HeapHeader`] and both consumers delegate to it (spine §6.3 ruling,
/// resolving FIXME 0468). The backend derives **no** flattening predicate of
/// its own — its `HeapCategory::classify` `ADT` arm reads this carrier's
/// verdict exactly as typecheck's mode classifier does.
///
/// # Monotone-sound conservatism (first landing)
///
/// Returning `None` is *always* sound (it keeps today's lowering — spine §6.1
/// monotone soundness); only precision is lost. The first landing is
/// deliberately conservative in three ways, each a `None`:
/// - **multi-constructor** ADTs (a tag word alongside the payload — §7.1);
/// - **`Vec`** and other built-in heap collections (heap identity);
/// - **generic** ADT fields whose stored constructor-scheme type is not already
///   fully concrete (no per-instantiation substitution in the first landing —
///   `(Cell Int)`-style monomorphic products only, §7.2). A field whose type
///   fails [`ConcreteType::from_type`] makes the whole type ineligible.
///
/// `type_defs` is the per-module symbol-table view both crates already hold (the
/// same `Option<&SymbolTables>` `HeapCategory::classify` takes); `None`
/// classifies every ADT as ineligible (conservative — the pre-typecheck stages).
pub fn value_layout<C, L>(
    ty: &ConcreteType,
    type_defs: Option<&SymbolTables<C, L>>,
) -> Option<ValueLayout>
where
    C: CodeStore,
    L: LinkerStore,
{
    // `visited` is the set of ADT names on the *current* resolution path — the
    // cycle guard that keeps a self- or mutually-recursive concrete type
    // (`(deftype Stream (Stream [:Int head :Stream tail]))`, or an A-holds-B /
    // B-holds-A pair) from recursing forever. It is path-scoped (each ADT is
    // removed once its subtree is resolved), so a value type reused across
    // sibling fields (`Two [:Cell a :Cell b]`) still counts each occurrence.
    let mut visited = HashSet::new();
    let words = layout_words(ty, type_defs, &mut visited)?;
    (words <= VALUE_LAYOUT_MAX_WORDS).then_some(ValueLayout { words })
}

/// Total machine-word count of `ty`'s fully-flattened value representation, or
/// `None` if `ty` has any heap identity / multi-constructor tag / non-concrete
/// field (i.e. is not Copy-eligible). Structural eligibility only — the
/// `≤ VALUE_LAYOUT_MAX_WORDS` size bound is applied once, at the top, by
/// [`value_layout`].
fn layout_words<C, L>(
    ty: &ConcreteType,
    type_defs: Option<&SymbolTables<C, L>>,
    visited: &mut HashSet<FQTypeName>,
) -> Option<usize>
where
    C: CodeStore,
    L: LinkerStore,
{
    match ty {
        // Scalars are the base case: value-represented, one word.
        ConcreteType::Int | ConcreteType::Bool | ConcreteType::Float => Some(1),
        // Heap identities — never value-flattened.
        ConcreteType::String | ConcreteType::Fn(_, _) => None,
        ConcreteType::ADT(fqtn, _args) => adt_layout_words(fqtn, type_defs, visited),
    }
}

/// Word count of a single-constructor value-eligible ADT, or `None`.
fn adt_layout_words<C, L>(
    fqtn: &FQTypeName,
    type_defs: Option<&SymbolTables<C, L>>,
    visited: &mut HashSet<FQTypeName>,
) -> Option<usize>
where
    C: CodeStore,
    L: LinkerStore,
{
    // `Vec` is a built-in heap collection (not registered via deftype) — never a
    // flattened value. A `Vec` OF value elements is handled by the backend's
    // null-elem-fn path, not by the `Vec` itself flattening (§7.3).
    if fqtn.name.as_ref() == "Vec" {
        return None;
    }

    // Cycle guard (compiler-DoS bound): a type already on the current resolution
    // path is (mutually-)recursive and therefore unbounded-size — it can never be
    // a `≤ VALUE_LAYOUT_MAX_WORDS` inline value, so `None` is exactly the correct
    // (monotone-sound) verdict: keep today's heap lowering. Without this, a
    // self-referential concrete product (`Stream [:Int head :Stream tail]`) or an
    // A-holds-B / B-holds-A pair recurses forever → stack overflow.
    if !visited.insert(fqtn.clone()) {
        return None;
    }

    // Compute the word count, then pop `fqtn` off the path regardless of outcome
    // (so a value type reused across sibling fields is not falsely flagged as a
    // cycle). The inner closure carries the `?`-early-returns; the pop always runs.
    let result = (|| {
        let tables = type_defs?;

        // Recover the constructor's field types WHILE holding the module's Ref,
        // then drop the guard BEFORE recursing — recursion may `get` a field
        // type's own module, and holding two DashMap Refs into one shard can
        // deadlock.
        let field_types: Vec<ConcreteType> = {
            let table = tables.get(&fqtn.module)?;
            let ctor_names = type_ctor_names(table.value(), fqtn)?;
            // Single-constructor only — a multi-ctor ADT needs a tag word
            // alongside the payload, excluded from the first landing (§7.1).
            let [ctor_name] = ctor_names.as_slice() else {
                return None;
            };
            ctor_field_concrete_types(table.value(), ctor_name)?
        };

        let mut total = 0usize;
        for ft in &field_types {
            total = total.checked_add(layout_words(ft, type_defs, visited)?)?;
        }
        Some(total)
    })();

    visited.remove(fqtn);
    result
}

/// The constructor name-list for the type keyed at `fqtn.name` — from a
/// `TypeDef` entry (sum/enum, or a product whose type-name differs from its
/// ctor-name) or from a single-ctor product ctor `Def`'s `type_def` facet
/// (type-name == ctor-name, S79 Option 3a). `None` for any non-type entry.
fn type_ctor_names<C, L>(table: &SymbolTable<C, L>, fqtn: &FQTypeName) -> Option<Vec<Symbol>>
where
    C: CodeStore,
    L: LinkerStore,
{
    match table.get(fqtn.name.as_ref())? {
        ModuleEntry::TypeDef { info, .. } => Some(info.constructors.clone()),
        ModuleEntry::Def { kind, .. } => match &**kind {
            DefKind::Constructor { type_def: Some(td), .. } => Some(td.constructors.clone()),
            _ => None,
        },
        _ => None,
    }
}

/// The field types of the constructor `ctor_name` as fully-concrete types, or
/// `None` if the entry is not a constructor or any field type is not already
/// concrete. The ctor's `scheme.ty` is `field_types… -> ADT` (a nullary ctor's
/// scheme is the ADT type directly, so it has zero fields — a `0`-word value).
fn ctor_field_concrete_types<C, L>(
    table: &SymbolTable<C, L>,
    ctor_name: &Symbol,
) -> Option<Vec<ConcreteType>>
where
    C: CodeStore,
    L: LinkerStore,
{
    let ModuleEntry::Def { scheme, kind, .. } = table.get(ctor_name.as_ref())? else {
        return None;
    };
    if !matches!(&**kind, DefKind::Constructor { .. }) {
        return None;
    }
    let field_tys: &[Type] = match &scheme.ty {
        Type::Fn(params, _ret) => params.as_slice(),
        _ => &[],
    };
    // Every field must already be fully concrete; a residual type variable (an
    // uninstantiated generic ctor field) is conservatively ineligible (§7.2).
    field_tys
        .iter()
        .map(|t| ConcreteType::from_type(t).ok())
        .collect()
}

#[cfg(test)]
mod value_layout_tests;
