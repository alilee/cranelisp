//! Platform-interface schema generator (`design/arch/platform-interface.md`
//! §5.5/§6.0, user-ratified 2026-06-07; BC §3 "the platform-interface codegen
//! role").
//!
//! Backend owns the **schema generator** — a routine that, given a root type
//! set + a `SymbolTable` map, derives the referenced-ADT set, takes the
//! **transitive closure** over field types (nested ADTs in; scalar leaves out),
//! substitutes concrete type args for instantiations, and emits the schema
//! artifact text:
//!
//! ```text
//! ;; layout-hash: <hash>
//! (schema
//!   (shapes/Rectangle
//!     (Rectangle 0 ((w primitives/Int) (h primitives/Int)))))
//! ```
//!
//! The shape is `Map<FQTypeName, Vec<(CtorName, tag, Vec<(Symbol, FieldType)>)>>`
//! with concrete instantiations keyed by the structured type expression
//! (`(Option shapes/Rectangle)`), never a mangle (§5.5.3). The text is an
//! S-expression so the existing frontend reader can parse it DLL-side
//! (§2.2 q-schema-grammar recommendation — one parser, no second grammar).
//!
//! # The shared closure-walk (BC §3, platform-interface.md §6.0)
//!
//! The generator MUST share the **closure-walk + concrete-instantiation
//! substitution** with the trace `DisplayDescriptor` baker
//! (`compiler::trace_codegen`). The shared asset is the **walk** — the
//! algorithm that, given a root type and the type-def lookups, produces the
//! closed-over set of concrete constructor layouts — NOT the serialized output
//! form: the trace baker emits a self-relative binary `DisplayDescriptor` blob
//! (program-lifetime), the schema generator emits S-expr text (build-artifact
//! lifetime). Forcing one serialization on two consumers that legitimately
//! differ would over-couple them (Principle 6).
//!
//! This module is the home of the shared rule that types a constructor's
//! fields at an instantiation ([`ctor_field_types_at`]); `trace_codegen`
//! consumes it so the rule lives once.
//!
//! # One generator, multiple callers
//!
//! - int's `/platform-schema <name>` REPL command (prints the artifact);
//! - int's session-load layout-hash check (regenerate + compare);
//! - the `--link` startup-object hash bake (regenerate from compiled modules,
//!   hash, bake into the startup stub — `exe`-bundle territory).
//!
//! All three reach `generate_schema` / `compute_layout_hash` (the `pub`
//! surface) with a `SymbolTable` map + the root type set; the second
//! convergence's canonical-form/DAG problem dissolves because there is ONE
//! generator on both the produce side (`/platform-schema`) and the check side
//! (load / `--link`) — they hash bytes produced by the same code
//! (platform-interface.md §5.5.4).

use std::collections::BTreeMap;

use dashmap::DashMap;

use cranelisp_types::{
    CallableOrigin, FQTypeName, ModuleFullPath, Subst, Symbol, SymbolTable, Type, apply,
};

// ════════════════════════════════════════════════════════════════════════════
// Constructor field types at an instantiation — shared with the trace
// DisplayDescriptor baker.
// ════════════════════════════════════════════════════════════════════════════

/// Why a constructor's declared parameters cannot be paired with an
/// instantiation's type arguments. Either is a keying error: typecheck never
/// produces such an instantiation of a well-formed constructor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ParamPairingError {
    Arity { declared: usize, supplied: usize },
    Mismatch { position: usize },
}

impl std::fmt::Display for ParamPairingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParamPairingError::Arity { declared, supplied } => write!(
                f,
                "the type declares {declared} parameter(s) but is instantiated at {supplied}"
            ),
            ParamPairingError::Mismatch { position } => write!(
                f,
                "the declared parameter at position {position} is not a variable and differs from its argument"
            ),
        }
    }
}

/// The declared parameters of the type a constructor builds: the arguments of
/// its scheme's result ADT (`Fn(fields, ADT(name, params))`, or a bare
/// `ADT(name, params)` when nullary). Empty for a scheme of any other shape.
pub(crate) fn declared_params(scheme: &Type) -> &[Type] {
    let result = match scheme {
        Type::Fn(_, ret) => ret.as_ref(),
        other => other,
    };
    match result {
        Type::ADT(_, params) => params,
        _ => &[],
    }
}

/// One constructor's field types at an instantiation: each type argument is
/// paired with the declared parameter in its position (ACT-1062), the rule
/// `cranelisp_types::ctor_field_types_at` applies over concrete types. Shared
/// by the trace descriptor baker and the schema walk.
pub(crate) fn ctor_field_types_at(
    fields: &[Type],
    params: &[Type],
    args: &[Type],
) -> Result<Vec<Type>, ParamPairingError> {
    if params.len() != args.len() {
        return Err(ParamPairingError::Arity {
            declared: params.len(),
            supplied: args.len(),
        });
    }
    let mut subst = Subst::new();
    for (position, (param, arg)) in params.iter().zip(args).enumerate() {
        match param {
            // `apply` treats `{id -> Var(id)}` as an occurs-check violation and
            // panics on it (FIXME 0284): a type instantiated at its own residual
            // variable maps nothing, and the field stays residual.
            Type::Var(id) if *arg == Type::Var(*id) => {}
            Type::Var(id) => {
                subst.insert(*id, arg.clone());
            }
            declared if declared == arg => {}
            _ => return Err(ParamPairingError::Mismatch { position }),
        }
    }
    Ok(fields.iter().map(|ty| apply(&subst, ty)).collect())
}

// ════════════════════════════════════════════════════════════════════════════
// Names-aware constructor layout reader — walks symbol_tables directly.
// ════════════════════════════════════════════════════════════════════════════

/// One constructor of a walked type: name, heap tag, and ordered NAMED + TYPED
/// fields. The schema needs field NAMES (for `read_field("w")` DLL-side), which
/// the trace baker's `CtorMeta`/`CtorField` discard — so this reader reads
/// `param_names` off the constructor `Def` directly.
struct WalkedCtor {
    name: Symbol,
    tag: usize,
    /// `(field_name, field_type)` — field_type already concrete-substituted.
    fields: Vec<(Symbol, Type)>,
}

/// Read a type's constructors (named + typed fields) from the symbol tables,
/// each field typed at `type_args` by [`ctor_field_types_at`]. Returns `None`
/// if the type def is not found or a constructor's parameters do not pair
/// with `type_args` (the caller treats it as a leaf; a keying miss yields a
/// wrong layout hash, which the DLL load refuses).
///
/// Constructors are uniformly `ModuleEntry::Def { kind: DefKind::Constructor {
/// tag, field_count, .. }, param_names, scheme }` — field names from
/// `param_names`, field types from the scheme's `Fn` params (S79 Option 3a;
/// product ctors are got-slotted `Def`s exactly like sum ctors, no longer
/// absorbed into a `ModuleEntry::TypeDef`).
///
/// The TypeDefInfo (which names the type's constructors) is read from either:
/// - a separate `ModuleEntry::TypeDef` entry — the **sum/enum** case
///   (`Option` keyed distinctly from `Some`/`None`); or
/// - the **product** ctor `Def`'s `DefKind::Constructor { type_def: Some(..) }`
///   type facet — the single-ctor product case (type-name == ctor-name), where
///   the surviving `"Rectangle"` entry IS the got-slotted ctor `Def`.
fn ctors_of<C, L>(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    fqtn: &FQTypeName,
    type_args: &[Type],
) -> Option<Vec<WalkedCtor>>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let table = symbol_tables.get(&fqtn.module)?;
    let type_entry = table.get(fqtn.name.as_ref())?;
    // The TypeDefInfo lives on a `TypeDef` entry (sum/enum) or on the product
    // ctor `Def`'s `type_def` facet (single-ctor product, type-name==ctor-name).
    let info = type_entry.type_def_info()?.clone();
    drop(table);

    let mut ctors: Vec<WalkedCtor> = Vec::with_capacity(info.constructors.len());

    let table = symbol_tables.get(&fqtn.module)?;
    for ctor_name in &info.constructors {
        // Probe the canonical `member_key(Type, Ctor)` key first (S109 W1 — a sum
        // ctor's real `Def` lives under `Shape.Circle`, the bare name being an
        // `Import` alias carrying no `scheme`), bare fallback for the product
        // dual-facet. The schema/layout-hash stays keyed by the BARE display name
        // (`raws.push { name: ctor_name }`), so the hash is stable across the
        // keying change — only the PROBE is canonical-aware.
        let ctor_probe = table
            .get(cranelisp_types::member_key(&fqtn.name, ctor_name.as_ref()).as_ref())
            .or_else(|| table.get(ctor_name.as_ref()));
        // §10.5: a ctor whose canonical AND bare probes both miss is silently
        // dropped from the schema — the next keying drift would surface as a wrong
        // layout-hash / schema, not an error. Fail loud in CI (release skips).
        debug_assert!(
            ctor_probe.is_some_and(|entry| entry.callable().is_some_and(|callable| {
                matches!(callable.origin, CallableOrigin::Ctor { .. })
            })),
            "ctor '{ctor_name}' of '{fqtn}' has no resolvable Def — keying drift"
        );
        if let Some(callable) = ctor_probe.and_then(cranelisp_types::Binding::callable)
            && let CallableOrigin::Ctor {
                tag, field_count, ..
            } = &callable.origin
        {
            // Names from param_names, types from the scheme's Fn params
            // (nullary → no Fn → empty).
            let scheme = &callable.arm.scheme.ty;
            let declared_fields: &[Type] = match scheme {
                Type::Fn(params, _) => params,
                _ => &[],
            };
            let field_types =
                ctor_field_types_at(declared_fields, declared_params(scheme), type_args).ok()?;
            let names: Vec<Symbol> = (0..*field_count)
                .map(|i| {
                    callable
                        .arm
                        .param_names
                        .get(i)
                        .cloned()
                        .unwrap_or_else(|| Symbol::from(format!("_{i}")))
                })
                .collect();
            ctors.push(WalkedCtor {
                name: ctor_name.clone(),
                tag: *tag,
                fields: names.into_iter().zip(field_types).collect(),
            });
        }
    }
    Some(ctors)
}

// ════════════════════════════════════════════════════════════════════════════
// The closure walk + the FieldType encoding.
// ════════════════════════════════════════════════════════════════════════════

const VEC_TYPE_NAME: &str = "Vec";

/// Render a `Type` as a `FieldType` S-expression leaf/applied form
/// (platform-interface.md §5.5.2):
///
/// ```text
/// FieldType ::= primitives/Int                       ; Scalar — bare FQ name
///             | (geometry/Point …args)               ; Adt — applied form
///             | (Vec <FieldType>)                    ; Vec of element
/// ```
///
/// Scalars and zero-arg ADTs render as the bare FQ name; parameterised ADTs and
/// `Vec` render as the applied parenthesised form. The recursion mirrors the
/// type-expression shapes a `deftype` field can carry.
fn field_type_sexpr(ty: &Type) -> String {
    match ty {
        Type::Int => "primitives/Int".to_string(),
        Type::Bool => "primitives/Bool".to_string(),
        Type::Float => "primitives/Float".to_string(),
        Type::String => "primitives/String".to_string(),
        Type::ADT(fqtn, args) => {
            if fqtn.name.as_ref() == VEC_TYPE_NAME {
                let elem = args
                    .first()
                    .map(field_type_sexpr)
                    .unwrap_or_else(|| "_".to_string());
                format!("({VEC_TYPE_NAME} {elem})")
            } else if args.is_empty() {
                format!("{fqtn}")
            } else {
                let arg_strs: Vec<String> = args.iter().map(field_type_sexpr).collect();
                format!("({fqtn} {})", arg_strs.join(" "))
            }
        }
        // Residual type variables / higher-kinded apps with no concrete
        // instantiation: the platform sigs are monomorphic so this should not
        // occur for a reachable field, but render a stable placeholder rather
        // than panic — the layout-hash gate catches any real divergence.
        Type::Var(_) | Type::TyConApp(_, _) | Type::Fn(_, _) => "_".to_string(),
    }
}

/// Render the **map key** for a walked type — the structured type expression
/// (platform-interface.md §5.5.3). A zero-arg ADT keys by its bare FQ name; a
/// concrete instantiation keys by the applied form `(Option shapes/Rectangle)`
/// — machine-read, never a mangle.
fn type_key_sexpr(fqtn: &FQTypeName, args: &[Type]) -> String {
    if args.is_empty() {
        format!("{fqtn}")
    } else {
        let arg_strs: Vec<String> = args.iter().map(field_type_sexpr).collect();
        format!("({fqtn} {})", arg_strs.join(" "))
    }
}

/// One entry of the closed-over schema: the structured-type-expression key and
/// its constructor list. Held in a `BTreeMap` keyed by the rendered key string
/// so emission is deterministic (q-tag-stability: the walk is source-positional
/// and the ordering is canonical — two runs over identical resolved source
/// produce byte-identical text and therefore an identical hash).
struct SchemaEntry {
    ctors: Vec<WalkedCtor>,
}

/// Walk the transitive closure of ADT layouts reachable from `roots`.
///
/// For each root `Type::ADT(fqtn, args)`: read its constructors (named + typed
/// fields, concrete-substituted), add the entry keyed by the structured type
/// expression, and recurse into every field type that is itself an ADT (scalar
/// leaves and `Vec` element scalars terminate). `Vec(elem)` is NOT a schema
/// entry of its own (its layout is the ABI), but its element type IS walked so a
/// `(Vec shapes/Point)` field pulls `Point` into the closure.
///
/// Deterministic + cycle-safe: a key already in the map is not re-walked.
fn closure_walk<C, L>(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    roots: &[Type],
) -> BTreeMap<String, SchemaEntry>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let mut out: BTreeMap<String, SchemaEntry> = BTreeMap::new();
    let mut stack: Vec<Type> = roots.to_vec();

    while let Some(ty) = stack.pop() {
        // Only ADTs (excluding Vec, whose layout is the ABI) are schema entries.
        let Type::ADT(fqtn, args) = &ty else {
            // Walk into Vec elements / Fn results via the generic field walk
            // below; scalars terminate.
            push_nested(&ty, &mut stack);
            continue;
        };
        if fqtn.name.as_ref() == VEC_TYPE_NAME {
            // Vec is not an entry; walk its element.
            if let Some(elem) = args.first() {
                stack.push(elem.clone());
            }
            continue;
        }
        let key = type_key_sexpr(fqtn, args);
        if out.contains_key(&key) {
            continue;
        }
        let Some(ctors) = ctors_of(symbol_tables, fqtn, args) else {
            // Unknown type def (not yet resolved): skip — the layout-hash gate
            // surfaces any real divergence at load/link.
            continue;
        };
        // Recurse into every field type that reaches further ADTs.
        for ctor in &ctors {
            for (_, fty) in &ctor.fields {
                push_nested(fty, &mut stack);
            }
        }
        out.insert(key, SchemaEntry { ctors });
    }

    out
}

/// Push the ADT-reaching sub-types of a field type onto the walk stack.
fn push_nested(ty: &Type, stack: &mut Vec<Type>) {
    match ty {
        Type::ADT(fqtn, args) => {
            if fqtn.name.as_ref() == VEC_TYPE_NAME {
                if let Some(elem) = args.first() {
                    push_nested(elem, stack);
                }
            } else {
                stack.push(ty.clone());
            }
        }
        Type::Fn(params, ret) => {
            for p in params {
                push_nested(p, stack);
            }
            push_nested(ret, stack);
        }
        Type::TyConApp(_, args) => {
            for a in args {
                push_nested(a, stack);
            }
        }
        Type::Int | Type::Bool | Type::String | Type::Float | Type::Var(_) => {}
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Emission + hashing — the pub surface.
// ════════════════════════════════════════════════════════════════════════════

/// Emit the canonical schema body text (WITHOUT the `;; layout-hash:` header) —
/// the bytes the hash is computed over.
fn emit_schema_body(entries: &BTreeMap<String, SchemaEntry>) -> String {
    let mut s = String::from("(schema");
    for (key, entry) in entries {
        s.push_str("\n  (");
        s.push_str(key);
        for ctor in &entry.ctors {
            s.push_str(&format!("\n    ({} {} (", ctor.name, ctor.tag));
            let field_strs: Vec<String> = ctor
                .fields
                .iter()
                .map(|(name, ty)| format!("({name} {})", field_type_sexpr(ty)))
                .collect();
            s.push_str(&field_strs.join(" "));
            s.push_str("))");
        }
        s.push(')');
    }
    s.push(')');
    s
}

/// Compute the canonical layout hash of the schema closed over `roots`.
///
/// The hash is over the canonical schema body text — already the closed-over,
/// normalized representation of every layout the platform's sigs reach, so
/// hashing it (rather than the source `.cl`) hashes exactly the bytes that
/// matter and is whitespace/comment-insensitive by construction
/// (platform-interface.md §5.5.4). The host regenerates from the live tables and
/// compares to the DLL's exported `__cranelisp_layout_hash_<name>`; because the
/// SAME generator runs on both sides, agreement is by construction.
///
/// Returns a lowercase hex digest string.
pub fn compute_layout_hash<C, L>(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    roots: &[Type],
) -> String
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let entries = closure_walk(symbol_tables, roots);
    let body = emit_schema_body(&entries);
    hash_hex(body.as_bytes())
}

/// Generate the full schema artifact text — a `;; layout-hash: <hash>` header
/// line followed by the canonical schema body (platform-interface.md §5.5).
///
/// This is the text `/platform-schema <name>` prints (int redirects it to the
/// embed file) and the bytes the `--link` startup-object hash bake hashes. The
/// header hash equals `compute_layout_hash` over the same `roots`.
pub fn generate_schema<C, L>(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    roots: &[Type],
) -> String
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let entries = closure_walk(symbol_tables, roots);
    let body = emit_schema_body(&entries);
    let hash = hash_hex(body.as_bytes());
    format!(";; layout-hash: {hash}\n{body}")
}

/// Derive the root ADT type set from a platform module's symbol table — every
/// ADT named in a `DefKind::PlatformEffect` entry's sig scheme (parameter or
/// return), scalars excluded.
///
/// This is the producer side of the `/platform-schema` command: int looks up the
/// loaded platform's `SymbolTable`, calls this to get the roots, and passes them
/// (with the full `symbol_tables` map for the closure walk) to `generate_schema`
/// (platform-interface.md §5.5.1 step 1).
pub fn platform_effect_roots<C, L>(platform_table: &SymbolTable<C, L>) -> Vec<Type>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let mut roots: Vec<Type> = Vec::new();
    for (_, entry) in platform_table.all_symbols() {
        let Some(callable) = entry.callable() else {
            continue;
        };
        if !matches!(callable.origin, CallableOrigin::PlatformEffect { .. }) {
            continue;
        }
        match &callable.arm.scheme.ty {
            Type::Fn(params, ret) => {
                for p in params {
                    collect_adt_roots(p, &mut roots);
                }
                collect_adt_roots(ret, &mut roots);
            }
            other => collect_adt_roots(other, &mut roots),
        }
    }
    roots
}

/// Collect ADT-typed roots from a type (scalars and `Vec` itself excluded; a
/// `Vec`'s element ADT IS a root). Deduplicates structurally.
fn collect_adt_roots(ty: &Type, roots: &mut Vec<Type>) {
    match ty {
        Type::ADT(fqtn, args) => {
            if fqtn.name.as_ref() == VEC_TYPE_NAME {
                if let Some(elem) = args.first() {
                    collect_adt_roots(elem, roots);
                }
            } else {
                if !roots.contains(ty) {
                    roots.push(ty.clone());
                }
                for a in args {
                    collect_adt_roots(a, roots);
                }
            }
        }
        Type::Fn(params, ret) => {
            for p in params {
                collect_adt_roots(p, roots);
            }
            collect_adt_roots(ret, roots);
        }
        Type::TyConApp(_, args) => {
            for a in args {
                collect_adt_roots(a, roots);
            }
        }
        Type::Int | Type::Bool | Type::String | Type::Float | Type::Var(_) => {}
    }
}

/// FNV-1a 64-bit digest as lowercase hex. A small, dependency-free, stable hash
/// — the layout hash needs determinism + whitespace-insensitivity (achieved by
/// the canonical-text input), not cryptographic strength. The same routine runs
/// on the produce side (`/platform-schema`) and the check side (load / `--link`)
/// so the digests agree by construction.
fn hash_hex(bytes: &[u8]) -> String {
    const OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
    const PRIME: u64 = 0x0000_0100_0000_01b3;
    let mut h = OFFSET;
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(PRIME);
    }
    format!("{h:016x}")
}

#[cfg(test)]
mod tests;
