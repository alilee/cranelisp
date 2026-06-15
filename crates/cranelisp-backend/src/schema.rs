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
//! This module is the canonical home of the substitution primitives
//! (`collect_var_ids`, `subst_for_ctor_fields`); `trace_codegen` consumes them
//! through these `pub(crate)` re-exports so the walk lives once.
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
    apply, DefKind, FQTypeName, ModuleEntry, ModuleFullPath, Subst, Symbol,
    SymbolTable, Type, TypeId,
};

// ════════════════════════════════════════════════════════════════════════════
// Substitution primitives — shared with the trace DisplayDescriptor baker.
// ════════════════════════════════════════════════════════════════════════════

/// Collect unique `Type::Var` ids from a type in order of first occurrence.
///
/// Canonical home of the substitution helper the trace baker also needs
/// (`trace_codegen` re-uses it via the `pub(crate)` export); kept here so the
/// closure-walk substitution lives once (BC §3, platform-interface.md §6.0).
pub(crate) fn collect_var_ids(ty: &Type, ids: &mut Vec<TypeId>) {
    match ty {
        Type::Var(id) => {
            if !ids.contains(id) {
                ids.push(*id);
            }
        }
        Type::Fn(params, ret) => {
            for p in params {
                collect_var_ids(p, ids);
            }
            collect_var_ids(ret, ids);
        }
        Type::ADT(_, args) | Type::TyConApp(_, args) => {
            for a in args {
                collect_var_ids(a, ids);
            }
        }
        Type::Int | Type::Bool | Type::String | Type::Float => {}
    }
}

/// Build the positional substitution from a polymorphic type's
/// constructor-field type vars to a call/instantiation site's concrete
/// `type_args`.
///
/// Collects the var ids used across the type's constructor fields (in
/// first-occurrence order) and maps them positionally to `type_args` — the same
/// rule `trace_codegen::build_adt_subst` and `src/display.rs::build_adt_subst`
/// use. `field_type_lists` is the per-constructor field-type lists of the type
/// being instantiated.
pub(crate) fn subst_for_ctor_fields(
    field_type_lists: &[Vec<Type>],
    type_args: &[Type],
) -> Subst {
    let mut var_ids = Vec::new();
    for fields in field_type_lists {
        for ty in fields {
            collect_var_ids(ty, &mut var_ids);
        }
    }
    let mut subst = Subst::new();
    for (i, &id) in var_ids.iter().enumerate() {
        if let Some(arg) = type_args.get(i) {
            // Skip an identity self-mapping `{id -> Var(id)}`. It carries no
            // information (substituting a var for itself is a no-op), but
            // `cranelisp_types::apply` treats `{id -> Var(id)}` as an
            // occurs-check violation and `debug_assert!`-panics on it (a panic
            // that, when this baker runs on a `nice-worker` thread, aborts the
            // process — observed as the trace ADT-render crash, FIXME 0284).
            //
            // This arises whenever a polymorphic type is instantiated at its
            // own residual type vars — e.g. tracing `mk : (Fn [] (Option a))`
            // where `a` is unconstrained: the call-site `type_args` for the
            // result `(Option a)` is `[Var(a)]`, and the positional mapping is
            // `{ctor_field_var -> Var(a)}` with the same id on both sides.
            // Omitting the no-op keeps `apply` bounded and the field type
            // resolves to the residual `TypeVar` descriptor (rendered bare),
            // which is the correct fallback for an un-instantiated field.
            if let Type::Var(arg_id) = arg
                && *arg_id == id
            {
                continue;
            }
            subst.insert(id, arg.clone());
        }
    }
    subst
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
/// applying `subst` to each field type. Returns `None` if the type def is not
/// found (the caller treats it as a leaf — its layout is the ABI or it is
/// unresolved).
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
    let info = match type_entry {
        ModuleEntry::TypeDef { info, .. } => info.clone(),
        ModuleEntry::Def { kind, .. } => match &**kind {
            DefKind::Constructor { type_def: Some(td), .. } => (**td).clone(),
            _ => return None,
        },
        _ => return None,
    };
    drop(table);

    // Gather per-constructor (name, tag, field (name, ty)) lists.
    // First pass collects raw (pre-subst) field-type lists so we can build the
    // positional substitution across ALL constructors (matching the baker).
    struct Raw {
        name: Symbol,
        tag: usize,
        field_names: Vec<Symbol>,
        field_types: Vec<Type>,
    }
    let mut raws: Vec<Raw> = Vec::with_capacity(info.constructors.len());

    let table = symbol_tables.get(&fqtn.module)?;
    for ctor_name in &info.constructors {
        if let Some(ModuleEntry::Def { kind, scheme, param_names, .. }) =
            table.get(ctor_name.as_ref())
            && let DefKind::Constructor { tag, field_count, .. } = &**kind
        {
            // Sum/enum constructor Def: names from param_names, types from
            // the scheme's Fn params (nullary → no Fn → empty).
            let field_types: Vec<Type> = match &scheme.ty {
                Type::Fn(params, _) => params.clone(),
                _ => Vec::new(),
            };
            let names: Vec<Symbol> = (0..*field_count)
                .map(|i| {
                    param_names
                        .get(i)
                        .cloned()
                        .unwrap_or_else(|| Symbol::from(format!("_{i}")))
                })
                .collect();
            raws.push(Raw {
                name: ctor_name.clone(),
                tag: *tag,
                field_names: names,
                field_types,
            });
        }
    }
    drop(table);

    // Build the positional subst from ALL constructors' field-var ids → args.
    let field_type_lists: Vec<Vec<Type>> =
        raws.iter().map(|r| r.field_types.clone()).collect();
    let subst = subst_for_ctor_fields(&field_type_lists, type_args);

    let ctors = raws
        .into_iter()
        .map(|r| WalkedCtor {
            name: r.name,
            tag: r.tag,
            fields: r
                .field_names
                .into_iter()
                .zip(r.field_types.iter())
                .map(|(n, ty)| (n, apply(&subst, ty)))
                .collect(),
        })
        .collect();
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
pub fn platform_effect_roots<C, L>(
    platform_table: &SymbolTable<C, L>,
) -> Vec<Type>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let mut roots: Vec<Type> = Vec::new();
    for (_, entry) in platform_table.all_symbols() {
        let ModuleEntry::Def { kind, scheme, .. } = entry else {
            continue;
        };
        if !matches!(kind.as_ref(), DefKind::PlatformEffect { .. }) {
            continue;
        }
        match &scheme.ty {
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
mod tests {
    use super::*;
    use cranelisp_types::{Scheme, Visibility};
    use std::collections::HashMap;

    fn fqtn(module: &str, name: &str) -> FQTypeName {
        FQTypeName::new(ModuleFullPath::from(module), name.into())
    }

    /// Register a product `deftype` (single same-named ctor) into `tables`,
    /// supplying positional `_{i}` field names. Use `register_product_named`
    /// to supply real declared names.
    fn register_product(
        tables: &DashMap<ModuleFullPath, SymbolTable>,
        module: &str,
        name: &str,
        field_types: Vec<Type>,
    ) {
        let param_names: Vec<Symbol> = (0..field_types.len())
            .map(|i| Symbol::from(format!("_{i}")))
            .collect();
        register_product_named(tables, module, name, param_names, field_types);
    }

    /// Register a product `deftype` with explicit declared field names —
    /// the S79 Option 3a dual-facet shape: a got-slotted ctor `Def` with
    /// `DefKind::Constructor { type_def: Some(..), .. }` carrying its real
    /// `param_names` (field names) and `scheme` (field types).
    fn register_product_named(
        tables: &DashMap<ModuleFullPath, SymbolTable>,
        module: &str,
        name: &str,
        param_names: Vec<Symbol>,
        field_types: Vec<Type>,
    ) {
        let m = ModuleFullPath::from(module);
        let mut st = tables
            .remove(&m)
            .map(|(_, t)| t)
            .unwrap_or_else(|| SymbolTable::new(m.clone()));
        let adt = Type::ADT(fqtn(module, name), vec![]);
        let scheme = Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Fn(field_types.clone(), Box::new(adt)),
        };
        let type_def = cranelisp_types::TypeDefInfo {
            name: fqtn(module, name),
            type_params: vec![],
            constructors: vec![Symbol::from(name)],
        };
        st.insert(
            Symbol::from(name),
            ModuleEntry::Def {
                scheme,
                visibility: Visibility::Public,
                docstring: None,
                param_names,
                kind: Box::new(DefKind::Constructor {
                    got_slot: 0,
                    type_name: fqtn(module, name),
                    tag: 0,
                    field_count: field_types.len(),
                    internal: false,
                    type_def: Some(Box::new(type_def)),
                }),
                callees: vec![],
                trait_origin: None,
                seq: 0,
                ast: None,
                code: None,
            },
        );
        tables.insert(m, st);
    }

    // spec: design/arch/platform-interface.md §5.5.2 — a product type's schema
    //       entry lists its single same-named constructor (tag 0) with ordered
    //       typed fields; scalar field types render as bare FQ names.
    #[test]
    fn product_type_schema_lists_typed_fields() {
        let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        register_product_named(
            &tables,
            "shapes",
            "Rectangle",
            vec![Symbol::from("w"), Symbol::from("h")],
            vec![Type::Int, Type::Int],
        );

        let root = Type::ADT(fqtn("shapes", "Rectangle"), vec![]);
        let text = generate_schema(&tables, &[root]);

        assert!(text.starts_with(";; layout-hash: "), "header line present");
        assert!(text.contains("(shapes/Rectangle"), "type keyed by FQ name");
        // S79 Option 3a: the product ctor `Def`'s real `param_names` (w/h) are
        // emitted, NOT positional `_0`/`_1` — the FIXME 0319 field-name fix.
        assert!(
            text.contains("(Rectangle 0 ((w primitives/Int) (h primitives/Int)))"),
            "ctor tag 0 with two real-named typed fields; got:\n{text}",
        );
    }

    // spec: design/arch/platform-interface.md §5.5.1 — the transitive closure
    //       pulls a nested ADT into the schema (a field whose type is another
    //       ADT joins the set). Scalar leaves terminate.
    #[test]
    fn closure_pulls_nested_adt() {
        let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        register_product(&tables, "geometry", "Point", vec![Type::Int, Type::Int]);
        register_product(
            &tables,
            "shapes",
            "Box",
            vec![Type::ADT(fqtn("geometry", "Point"), vec![])],
        );

        let root = Type::ADT(fqtn("shapes", "Box"), vec![]);
        let text = generate_schema(&tables, &[root]);
        assert!(text.contains("(shapes/Box"), "root in schema");
        assert!(
            text.contains("(geometry/Point"),
            "nested ADT pulled into the closure; got:\n{text}",
        );
        assert!(
            text.contains("geometry/Point"),
            "Box's field renders the nested ADT type by FQ name",
        );
    }

    // spec: design/arch/platform-interface.md §5.5.4 — regenerating the schema
    //       over identical resolved source yields an identical hash (the walk is
    //       source-positional + canonical-text; q-tag-stability). A layout change
    //       changes the hash.
    #[test]
    fn layout_hash_is_stable_and_change_sensitive() {
        let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        register_product(&tables, "shapes", "Rectangle", vec![Type::Int, Type::Int]);
        let root = Type::ADT(fqtn("shapes", "Rectangle"), vec![]);

        let h1 = compute_layout_hash(&tables, std::slice::from_ref(&root));
        let h2 = compute_layout_hash(&tables, std::slice::from_ref(&root));
        assert_eq!(h1, h2, "two runs over identical source agree");

        // The header hash equals compute_layout_hash.
        let text = generate_schema(&tables, std::slice::from_ref(&root));
        assert!(
            text.contains(&format!(";; layout-hash: {h1}")),
            "header hash matches compute_layout_hash",
        );

        // A changed layout (one fewer field) changes the hash.
        let tables2: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        register_product(&tables2, "shapes", "Rectangle", vec![Type::Int]);
        let h3 = compute_layout_hash(&tables2, &[root]);
        assert_ne!(h1, h3, "a layout change must change the hash");
    }

    // spec: design/arch/platform-interface.md §5.5.1 — `platform_effect_roots`
    //       derives the root ADT set from the PlatformEffect sig schemes,
    //       excluding scalars; the schema closes over exactly those.
    #[test]
    fn platform_effect_roots_excludes_scalars() {
        let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        register_product(&tables, "shapes", "Rectangle", vec![Type::Int, Type::Int]);

        // A platform module with one effect: (Fn [shapes/Rectangle] primitives/Int).
        let plat = ModuleFullPath::from("platform.shapes");
        let mut pt = SymbolTable::new(plat.clone());
        let rect = Type::ADT(fqtn("shapes", "Rectangle"), vec![]);
        pt.insert(
            Symbol::from("rectangle-area"),
            ModuleEntry::Def {
                scheme: Scheme {
                    type_vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Fn(vec![rect.clone()], Box::new(Type::Int)),
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![Symbol::from("r")],
                kind: Box::new(DefKind::PlatformEffect {
                    scheduling_class: cranelisp_types::SchedulingClass::Sequential,
                    got_slot: 0,
                }),
                callees: vec![],
                trait_origin: None,
                seq: 0,
                ast: None,
                code: None,
            },
        );
        tables.insert(plat.clone(), pt);

        let roots = platform_effect_roots(tables.get(&plat).unwrap().value());
        assert_eq!(roots, vec![rect], "Rectangle is the only ADT root; Int excluded");
    }

    // ── subst_for_ctor_fields: identity self-map elision (FIXME 0284) ──────────

    // A polymorphic type instantiated at its OWN residual type var produces a
    // positional mapping `{field_var -> Var(field_var)}` — the same id on both
    // sides. `cranelisp_types::apply` treats `{id -> Var(id)}` as an
    // occurs-check violation and `debug_assert!`-panics on it. The baker must
    // NOT emit that no-op mapping. This is the bake-side root of the trace
    // ADT-render crash (e.g. tracing `mk : (Fn [] (Option a))`).
    #[test]
    fn subst_skips_identity_self_map() {
        // Option-shaped: None has no fields, Some has one field of type `a`
        // (Var(0)). Instantiated at `[Var(0)]` — its own var.
        let field_type_lists = vec![vec![], vec![Type::Var(0)]];
        let subst = subst_for_ctor_fields(&field_type_lists, &[Type::Var(0)]);
        assert!(
            !subst.contains_key(&0),
            "identity self-map {{0 -> Var(0)}} must be elided, not inserted: {subst:?}"
        );
        // And applying the (empty) subst to the field type must not panic and
        // must leave the residual var intact (rendered bare downstream).
        let resolved = cranelisp_types::apply(&subst, &Type::Var(0));
        assert_eq!(resolved, Type::Var(0));
    }

    // A non-identity instantiation is still recorded (the elision is narrow:
    // only `{id -> Var(id)}` is skipped, concrete and cross-var maps stand).
    #[test]
    fn subst_keeps_concrete_and_cross_var_maps() {
        let field_type_lists = vec![vec![Type::Var(0)], vec![Type::Var(1)]];
        // Var(0) -> Int (concrete), Var(1) -> Var(2) (cross-var, not identity).
        let subst = subst_for_ctor_fields(
            &field_type_lists,
            &[Type::Int, Type::Var(2)],
        );
        assert_eq!(subst.get(&0), Some(&Type::Int), "concrete map kept");
        assert_eq!(subst.get(&1), Some(&Type::Var(2)), "cross-var map kept");
    }
}
