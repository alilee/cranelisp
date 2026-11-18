// HeapCategory + classifier relocated to cranelisp-backend per S69 Sub 38
// (bounded-context: backend-internal codegen classification). HeapHeader
// retains as the cross-crate layout contract shared with the backend-emitted
// runtime library (cranelisp-primitives / cranelisp-intrinsics).

use std::collections::HashSet;
use std::mem::{self, offset_of};

use crate::{
    Binding, CallableOrigin, CodeStore, ConcreteType, Decl, FQTypeName, LinkerStore,
    ModuleFullPath, NotConcrete, Symbol, SymbolTable, SymbolTables, Type, TypeRecord,
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
// The Copy/value-layout predicate: a release-tier fact
// (`design/arch/ownership-inference.md` §6.3, `design/arch/interfaces.md`
// §"R5 value-representation flattening"). Its one consumer is typecheck's
// `Copy` classification. No lowering reads it: the dev tier lays every such
// value out as a heap value (Principle 27).
// ---------------------------------------------------------------------------

/// Maximum machine-word size of a value-eligible concrete type: **one word
/// (8 bytes)**.
///
/// Every ABI surface is uniformly `i64` (parameters, returns, `Vec` slots, ADT
/// fields, closure captures, GOT-dispatched signatures), so a one-word value
/// could cross every existing boundary as its word, with no ABI change. A
/// larger bound changes which types typecheck classifies `Copy`, and those
/// modes are persisted, so changing this constant is a
/// `CACHE_SCHEMA_VERSION`-bump event.
pub const VALUE_LAYOUT_MAX_WORDS: usize = 1;

/// The value-representation verdict for a concrete type.
///
/// A [`Some`] result from [`value_layout`] means the type is **Copy-eligible
/// within the size bound**: it could be laid out inline with no header, no
/// refcount and no drop glue. A [`None`] means it could not. The verdict is a
/// fact about the type, not a description of the emitted layout: the dev
/// lowering gives a `Some` ADT the ordinary heap layout.
///
/// This is a **classification result**, not a persisted DTO: it is recomputed
/// from the type definitions on every compile and never serialised.
/// `#[non_exhaustive]` because a multi-word bound would add layout detail;
/// consumers read it as `ValueLayout { words, .. }`.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ValueLayout {
    /// Number of machine words the inline representation would occupy
    /// (`≤ VALUE_LAYOUT_MAX_WORDS`). Under the one-word bound this is always `1`: a
    /// value is a scalar, or a single-constructor **single-value-field** wrapper
    /// such as `(Cell Int)` whose one field flattens to one word. A 0-field or
    /// ≥2-field product is **not** value-eligible (`None`) — see [`value_layout`].
    pub words: usize,
}

/// The **single-sourced** Copy/value-layout predicate — is this concrete type
/// representable as an inline value of `≤ VALUE_LAYOUT_MAX_WORDS` words?
///
/// `Some(ValueLayout { words })` ⟺ the type is **Copy-eligible** — a scalar, or
/// a single-constructor ADT with **exactly one field** that is itself
/// value-eligible (transitively) **∧** the whole fits in
/// `≤ VALUE_LAYOUT_MAX_WORDS` words (always exactly `1` under the one-word
/// bound). `None` ⟺ the type is not Copy-eligible.
///
/// **Single-field is a soundness rule, not just a size bound.** A 0-field
/// (0-word) or ≥2-field product is `None` even when its word count would fit.
/// The only inline representation the verdict licenses is *the identity move
/// of a single value word*, and a lowering that reads the verdict must
/// implement exactly that shape (see `adt_layout_words`).
///
/// # Consumers, and why this lives in `cranelisp-types`
///
/// The one consumer is typecheck's `Copy` mode classification. The dev lowering
/// reads the verdict nowhere and counts every ADT it admits as a heap value
/// (`design/arch/interfaces.md` §"R5 value-representation flattening"). The
/// predicate is retained as a release-tier fact with its producer tests.
///
/// A lowering that lays a type out inline must agree with typecheck on this
/// verdict or the system is unsound: a parameter moded `Copy` whose value is in
/// fact a heap object is bit-copied with no `rc_inc`, a use-after-free. Any
/// such reader therefore delegates to this predicate and derives none of its
/// own (Principle 7).
///
/// # Monotone-sound conservatism
///
/// Returning `None` is always sound (monotone soundness,
/// `design/arch/ownership-inference.md` §6.1); only precision is lost. Each of
/// these is a `None`:
/// - **multi-constructor** ADTs (a tag word alongside the payload);
/// - **0-field or ≥2-field** single-constructor products (the soundness rule
///   above);
/// - **`Vec`** and other built-in heap collections (heap identity);
/// - **generic** ADT fields whose stored constructor-scheme type is not already
///   fully concrete: the walk performs no per-instantiation substitution, so
///   only `(Cell Int)`-style monomorphic products are eligible. A field whose
///   type fails [`ConcreteType::from_type`] makes the whole type ineligible.
///
/// `type_defs` is the per-module symbol-table view; `None` classifies every
/// ADT as ineligible (the conservative answer, used before typecheck).
/// This table adapter delegates to [`value_layout_with_lookup`]; callers with
/// staged declarations supply their coherent lookup through that entry point.
pub fn value_layout<C, L>(
    ty: &ConcreteType,
    type_defs: Option<&SymbolTables<C, L>>,
) -> Option<ValueLayout>
where
    C: CodeStore,
    L: LinkerStore,
{
    value_layout_with_lookup(ty, &|module, key| {
        type_defs?.get(module)?.get(key.as_ref()).cloned()
    })
}

/// Calculate the shared Copy/value layout using the caller's declaration view.
///
/// Typecheck supplies staged declarations here; [`value_layout`] is the adapter
/// over published tables. Both entry points use the same eligibility,
/// constructor-key projection and recursive walk documented by [`value_layout`].
///
/// `lookup` probes an exact module and storage key, returning an owned binding
/// or `None` on absence. It performs no name resolution, alias following or
/// prelude fallback. A staging view returns a present staged binding even if
/// ineligible, falling through to published state only for an absent key.
/// The caller keeps the declaration view coherent for the calculation and
/// releases all table guards or staging borrows before returning each binding.
/// The walk drops those owned bindings before recursing into field types.
///
/// Missing or unsuitable metadata gives `None`. Scalars need no lookup. The
/// callback is borrowed only for this call; the result retains no bindings,
/// guards or callback references. No lifecycle or slot is created or published.
pub fn value_layout_with_lookup<C, F>(ty: &ConcreteType, lookup: &F) -> Option<ValueLayout>
where
    C: CodeStore,
    F: Fn(&ModuleFullPath, &Symbol) -> Option<Binding<C>>,
{
    // `visited` is the set of ADT names on the *current* resolution path — the
    // cycle guard that keeps a self- or mutually-recursive concrete type
    // (`(deftype Stream (Stream [:Int head :Stream tail]))`, or an A-holds-B /
    // B-holds-A pair) from recursing forever. It is path-scoped (each ADT is
    // removed once its subtree is resolved), so a value type reused across
    // sibling fields (`Two [:Cell a :Cell b]`) still counts each occurrence.
    let mut visited = HashSet::new();
    let words = layout_words(ty, lookup, &mut visited)?;
    (words <= VALUE_LAYOUT_MAX_WORDS).then_some(ValueLayout { words })
}

/// Total machine-word count of `ty`'s fully-flattened value representation, or
/// `None` if `ty` has any heap identity / multi-constructor tag / non-concrete
/// field (i.e. is not Copy-eligible). Structural eligibility only — the
/// `≤ VALUE_LAYOUT_MAX_WORDS` size bound is applied once, at the top, by
/// [`value_layout`].
fn layout_words<C, F>(
    ty: &ConcreteType,
    lookup: &F,
    visited: &mut HashSet<FQTypeName>,
) -> Option<usize>
where
    C: CodeStore,
    F: Fn(&ModuleFullPath, &Symbol) -> Option<Binding<C>>,
{
    match ty {
        // Scalars are the base case: value-represented, one word.
        ConcreteType::Int | ConcreteType::Bool | ConcreteType::Float => Some(1),
        // Heap identities — never value-flattened.
        ConcreteType::String | ConcreteType::Fn(_, _) => None,
        ConcreteType::ADT(fqtn, _args) => adt_layout_words(fqtn, lookup, visited),
    }
}

/// Word count of a single-constructor value-eligible ADT, or `None`.
fn adt_layout_words<C, F>(
    fqtn: &FQTypeName,
    lookup: &F,
    visited: &mut HashSet<FQTypeName>,
) -> Option<usize>
where
    C: CodeStore,
    F: Fn(&ModuleFullPath, &Symbol) -> Option<Binding<C>>,
{
    // `Vec` is a built-in heap collection (not registered via deftype) and has
    // heap identity whatever its element type.
    if fqtn.name.as_ref() == "Vec" {
        return None;
    }

    // Cycle guard (compiler-DoS bound): a type already on the current resolution
    // path is (mutually-)recursive and therefore unbounded-size — it can never be
    // a `≤ VALUE_LAYOUT_MAX_WORDS` inline value, so `None` is exactly the correct
    // (monotone-sound) verdict. Without this, a
    // self-referential concrete product (`Stream [:Int head :Stream tail]`) or an
    // A-holds-B / B-holds-A pair recurses forever → stack overflow.
    if !visited.insert(fqtn.clone()) {
        return None;
    }

    // Compute the word count, then pop `fqtn` off the path regardless of outcome
    // (so a value type reused across sibling fields is not falsely flagged as a
    // cycle). The inner closure carries the `?`-early-returns; the pop always runs.
    let result = (|| {
        // Own only the concrete fields across recursion: another lookup can
        // enter the same DashMap shard or staging RefCell.
        let field_types: Vec<ConcreteType> = {
            let binding = lookup(&fqtn.module, &Symbol::from(fqtn.name.as_ref()))?;
            let ctor_names = type_ctor_names_from_binding(&binding, fqtn, &|key| {
                lookup(&fqtn.module, key).is_some()
            })?;
            // Single-constructor only: a multi-constructor ADT needs a tag
            // word alongside the payload.
            let [ctor_name] = ctor_names.as_slice() else {
                return None;
            };
            ctor_field_concrete_types(&lookup(&fqtn.module, ctor_name)?)?
        };

        // Exactly one field, itself value-eligible. The inline representation
        // is that field's one word, and it is RC-free by induction: a
        // value-eligible field carries no heap reference, so a bit-copy
        // duplicates no owned pointer. Counting words instead is unsound in two
        // ways a single-word reader cannot represent:
        //   * a 0-word product (`(deftype U (U))`, or `(deftype P (P [:U u]))`)
        //     would be `Copy` with no word to move;
        //   * a ≥2-field product of one word in total
        //     (`(deftype M (M [:Int x :U u]))`) would bind every field to the
        //     one word.
        // Pinned by `heap/value_layout_tests.rs`.
        let [ft] = field_types.as_slice() else {
            return None;
        };
        layout_words(ft, lookup, visited)
    })();

    visited.remove(fqtn);
    result
}

/// The constructor name-list for the type keyed at `fqtn.name` — from a
/// `TypeDef` entry (sum/enum, or a product whose type-name differs from its
/// ctor-name) or from a single-ctor product ctor `Def`'s `type_def` facet
/// (type-name == ctor-name, S79 Option 3a). `None` for any non-type entry.
///
/// # The single ctor-name resolver (FIXME 0528 — Principle-7 mirror cure)
///
/// This table adapter shares one `Binding`→ctor-name-list projection with
/// [`value_layout_with_lookup`]. The backend's heap classification delegates
/// here, keeping the defined-type/product-facet switch and canonical-key
/// preference identical across all layout consumers.
pub fn type_ctor_names<C, L>(table: &SymbolTable<C, L>, fqtn: &FQTypeName) -> Option<Vec<Symbol>>
where
    C: CodeStore,
    L: LinkerStore,
{
    type_ctor_names_from_binding(table.get(fqtn.name.as_ref())?, fqtn, &|key| {
        table.get(key.as_ref()).is_some()
    })
}

fn type_ctor_names_from_binding<C: CodeStore>(
    binding: &Binding<C>,
    fqtn: &FQTypeName,
    contains: &impl Fn(&Symbol) -> bool,
) -> Option<Vec<Symbol>> {
    match &binding.declaration {
        // **Obligation A (S109 W1, `dotted-ctor-canonical-keys.md` §2).** Return
        // the *storage keys* of the ctor `Def`s, not display names.
        // `TypeDefInfo.constructors` carries bare display names; a sum ctor's real
        // `Def` now lives under the canonical `member_key(Type, Ctor)` key
        // (`Maybe.Some`) with the bare name a poison-able `Import` alias — so
        // consumers probing `table.get(returned)` MUST get the canonical key. The
        // mapping happens HERE, in the ONE reader. The probe-canonical-else-bare
        // shape stays robust to the product facet (type-name key).
        Decl::Type(TypeRecord::Defined { info, .. }) => Some(
            info.constructors
                .iter()
                .map(|c| {
                    let canonical = crate::member_key(&fqtn.name, c.as_ref());
                    if contains(&canonical) {
                        canonical
                    } else {
                        c.clone()
                    }
                })
                .collect(),
        ),
        Decl::Callable(callable) => match &callable.origin {
            CallableOrigin::Ctor {
                type_def: Some(td), ..
            } => Some(td.constructors.clone()),
            _ => None,
        },
        _ => None,
    }
}

/// The field types of a constructor binding as fully-concrete types, or
/// `None` if the entry is not a constructor or any field type is not already
/// concrete. The ctor's `scheme.ty` is `field_types… -> ADT` (a nullary ctor's
/// scheme is the ADT type directly, so it has zero fields — a `0`-word value).
fn ctor_field_concrete_types<C: CodeStore>(binding: &Binding<C>) -> Option<Vec<ConcreteType>> {
    let callable = binding.callable()?;
    if !matches!(callable.origin, CallableOrigin::Ctor { .. }) {
        return None;
    }
    let field_tys: &[Type] = match &callable.arm.scheme.ty {
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

// ---------------------------------------------------------------------------
// The substituting ctor-field projection (S119 types-first slice; register
// rows R-6/R-16; `design/arch/total-concreteness.md` §2.1).
// ---------------------------------------------------------------------------

/// Why [`ctor_field_types_at`] could not produce the instantiated field types.
///
/// A dedicated error sum rather than `NotConcrete` alone, so a caller bug
/// (wrong key, wrong arity, wrong instantiation) is not conflated with the
/// honest refusal (a residual field type) — never fabricate, never launder
/// (register rows R-13/R-16).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CtorFieldsAtError {
    /// The entry at `ctor_key` is absent or not a `CallableOrigin::Ctor` —
    /// a caller-side keying bug, not a property of the type.
    NotACtor,
    /// `args.len()` does not match the ctor's result-ADT parameter count.
    ParamArity { expected: usize, got: usize },
    /// A result-ADT parameter of the ctor's scheme is already concrete and
    /// differs from the supplied instantiation argument at that position.
    InstantiationMismatch { position: usize },
    /// A field type remains non-concrete after substitution — the whole ctor
    /// is refused (the [`value_layout`] model-site spelling: ONE residual
    /// field refuses everything; nothing is fabricated).
    NotConcrete(NotConcrete),
}

impl std::fmt::Display for CtorFieldsAtError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CtorFieldsAtError::NotACtor => write!(f, "entry is not a constructor"),
            CtorFieldsAtError::ParamArity { expected, got } => write!(
                f,
                "constructor instantiation arity mismatch: expected {expected} type argument(s), got {got}"
            ),
            CtorFieldsAtError::InstantiationMismatch { position } => write!(
                f,
                "constructor instantiation mismatch at type-argument position {position}"
            ),
            CtorFieldsAtError::NotConcrete(nc) => write!(
                f,
                "constructor field type remains non-concrete after instantiation ({nc:?})"
            ),
        }
    }
}

impl std::error::Error for CtorFieldsAtError {}

/// Field types of the constructor stored at `ctor_key`, **at the concrete
/// instantiation `args`**, or a refusal — the instantiation-substituting
/// sibling of the declaration-side [`value_layout`] projection (which reads
/// only already-concrete declarations and stays preserved verbatim, R-16).
///
/// Unifies the ctor scheme's result-ADT parameters against `args`
/// positionally, applies the substitution to the declared field types, and
/// converts each via [`ConcreteType::from_type`] — ONE residual field refuses
/// the whole ctor ([`CtorFieldsAtError::NotConcrete`]). **Never fabricates**:
/// there is no default arm, no `unwrap_or(Int)` — this is the only legal
/// derivation of instantiated ctor-field types for category/glue purposes
/// (`design/arch/total-concreteness.md` §2.1).
///
/// `args` are the type's arguments in **declared parameter order**: `args[i]`
/// instantiates the type's `i`-th parameter. A field takes the argument of
/// the parameter it mentions, whatever order the fields mention the
/// parameters in and whether or not every parameter is mentioned. Pairing
/// arguments with variables by first appearance in the fields is a different,
/// wrong projection.
///
/// `ctor_key` is the **storage key** of the ctor `Def` (canonical
/// `member_key(Type, Ctor)` for sum ctors, the bare type name for a product) —
/// callers resolve the key first; a miss or a non-ctor entry is
/// [`CtorFieldsAtError::NotACtor`], a caller bug distinct from a refusal.
///
/// A nullary ctor (scheme type is the bare ADT) has zero fields — `Ok(vec![])`
/// at any well-formed instantiation.
pub fn ctor_field_types_at<C, L>(
    table: &SymbolTable<C, L>,
    ctor_key: &Symbol,
    args: &[ConcreteType],
) -> Result<Vec<ConcreteType>, CtorFieldsAtError>
where
    C: CodeStore,
    L: LinkerStore,
{
    let Some(callable) = table
        .get(ctor_key.as_ref())
        .and_then(|binding| binding.callable())
    else {
        return Err(CtorFieldsAtError::NotACtor);
    };
    if !matches!(callable.origin, CallableOrigin::Ctor { .. }) {
        return Err(CtorFieldsAtError::NotACtor);
    }

    // Ctor scheme shape (adt_build::build_adt_entries, the ONE derivation):
    // data ctor → `Fn(field-tys, ADT(fqtn, params))`; nullary → bare ADT.
    let (field_tys, result_ty): (&[Type], &Type) = match &callable.arm.scheme.ty {
        Type::Fn(params, ret) => (params.as_slice(), ret.as_ref()),
        other => (&[], other),
    };
    let Type::ADT(_, result_params) = result_ty else {
        // A ctor whose scheme result is not an ADT is malformed — treat as a
        // keying/shape bug, never a refusal.
        return Err(CtorFieldsAtError::NotACtor);
    };

    if result_params.len() != args.len() {
        return Err(CtorFieldsAtError::ParamArity {
            expected: result_params.len(),
            got: args.len(),
        });
    }

    // Positional unification of result-ADT params against the instantiation:
    // a `Var` param binds; an already-concrete param must agree.
    let mut subst = crate::Subst::new();
    for (position, (param, arg)) in result_params.iter().zip(args.iter()).enumerate() {
        match param {
            Type::Var(id) => {
                subst.insert(*id, arg.to_type());
            }
            concrete => match ConcreteType::from_type(concrete) {
                Ok(ct) if ct == *arg => {}
                _ => return Err(CtorFieldsAtError::InstantiationMismatch { position }),
            },
        }
    }

    field_tys
        .iter()
        .map(|t| {
            ConcreteType::from_type(&crate::apply(&subst, t))
                .map_err(CtorFieldsAtError::NotConcrete)
        })
        .collect()
}

#[cfg(test)]
mod value_layout_tests;
