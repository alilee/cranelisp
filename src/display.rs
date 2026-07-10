// Canonical value display format (spec §12.9).
//
// Migrated from cranelisp-backend in Sprint 66 Wave 3b-2a. Owned by the int
// crate as a REPL/trace concern (presentation, not codegen). Imports the heap
// layout constants from cranelisp-backend::heap; depends on cranelisp-types
// for type definitions and cranelisp-intrinsics for string access.

use std::collections::HashMap;

use dashmap::DashMap;

use cranelisp_types::{
    DefKind, FQTypeName, ModuleEntry, ModuleFullPath, PrimitiveNaming, Scheme, Symbol, SymbolTable,
    Type, TypeDefInfo, TypeId, VarNaming, NULLARY_TAG_THRESHOLD, render_type,
};

use cranelisp_backend::heap::{HeapAdt, HeapVec};

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Format a runtime value as its canonical display string (spec §12.9).
///
/// Returns the value-only display — NO `:Type` prefix. The caller is
/// responsible for prepending the type prefix when needed (e.g., REPL
/// output uses `:Type value`; trace stores just the value string).
///
/// Dispatches by type:
///   Int    → decimal representation: "42", "-7"
///   Bool   → "true" / "false"
///   Float  → decimal with mandatory ".0" suffix: "3.14", "1.0"
///   String → quoted contents: "\"hello\""
///   Fn     → "<closure>"
///   ADT    → constructor dot notation (see below)
///   Vec    → "[elem1 elem2 ...]"
///
/// Thin wrapper over `format_field_value`; exercised by this module's unit
/// tests. `format_result_value` is the production entry point (REPL result
/// display). Allowed dead in non-test builds.
#[allow(dead_code)]
pub fn format_value<C, L>(
    value: i64,
    ty: &Type,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
) -> String
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    format_field_value(value, ty, symbol_tables)
}

/// Format a runtime value with `:Type value` prefix for REPL display.
///
/// Combines qualified type formatting with value formatting.
/// This is the top-level entry point for REPL result display.
pub fn format_result_value<C, L>(
    value: i64,
    ty: &Type,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
) -> String
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    match ty {
        Type::Bool => {
            let display_val = if value != 0 { "true" } else { "false" };
            format!(":primitives/Bool {display_val}")
        }
        Type::Float => {
            let f = f64::from_bits(value as u64);
            let s = format!("{f}");
            if s.contains('.') {
                format!(":primitives/Float {s}")
            } else {
                format!(":primitives/Float {s}.0")
            }
        }
        Type::Int => format!(":primitives/Int {value}"),
        Type::String => format_string_value(value),
        Type::Fn(_, _) => {
            let type_str = format_type_qualified(ty);
            format!(":{type_str} <closure>")
        }
        Type::ADT(fqtn, type_args) => {
            format_adt_value(value, fqtn, type_args, symbol_tables)
        }
        other => {
            let type_str = format_type_qualified(other);
            format!(":{type_str} {value}")
        }
    }
}

/// Convenience wrapper: format_result_value with empty symbol_tables.
///
/// Sprint 67 hack-back: callers migrated to `format_result_value` with an
/// explicit symbol-tables ref. Retained for tests + symmetry with the wider
/// formatter API; `#[allow(dead_code)]` while unused.
#[allow(dead_code)]
pub(crate) fn format_result(value: i64, ty: &Type) -> String {
    let empty: DashMap<ModuleFullPath, SymbolTable<(), ()>> = DashMap::new();
    format_result_value(value, ty, &empty)
}

/// Format a type with fully-qualified names for REPL display (spec §1.4).
///
/// Primitive types get `primitives/` prefix, ADT types get their module prefix,
/// `Fn` keyword and type variables stay unqualified.
pub fn format_type_qualified(
    ty: &Type,
) -> String {
    // Compute var names from the full type, then render through the shared walk
    // (S87 consolidation, FIXME 0420): FQ primitives + lettered vars reproduce
    // the former `format_type_qualified_inner` byte-for-byte.
    let var_names = cranelisp_types::type_var_names(ty);
    render_type(ty, PrimitiveNaming::Qualified, VarNaming::Lettered(&var_names))
}

/// Format a constrained function's scheme for REPL display (spec §1.3).
///
/// Produces inline-constraint notation:
///   `:(Fn [:Num a :Num a] a) user/double`
///
/// Every occurrence of a constrained type variable in parameter position
/// is shown as `:TraitName var` (spec §3.5.1).
/// Unconstrained variables appear bare.
pub fn format_scheme_display(
    name: &str,
    scheme: &Scheme,
    module: &ModuleFullPath,
) -> String {
    let type_str = format_scheme_type(scheme);
    format!(":{type_str} {module}/{name}")
}

/// Render a `Scheme`'s type as a normalized, fully-qualified REPL type string
/// (spec §1.4) — WITHOUT the `:` prefix or `module/name` suffix.
///
/// This is the single source of truth (Principle 7) for "scheme → type
/// string" used by both the definition-display path (`format_scheme_display`
/// / `format_def_entry`) and the `/list` per-symbol line
/// (`repl.rs::handle_list`). It normalizes type variables to consecutive
/// lowercase letters (`t1` → `a`) via `type_var_names` and qualifies
/// primitive/ADT names (`Int` → `primitives/Int`). When the scheme carries
/// constraints, every constrained var occurrence in parameter position is
/// shown as `:TraitName var` (spec §3.5.1); an unconstrained scheme renders
/// as the plain qualified type.
pub fn format_scheme_type(scheme: &Scheme) -> String {
    let var_names = cranelisp_types::type_var_names(&scheme.ty);

    if scheme.constraints.is_empty() {
        // No constraints: the plain qualified+normalized type via the shared walk
        // (S87 consolidation, FIXME 0420). Reuse the var_names so normalization
        // is identical to the constrained path.
        return render_type(
            &scheme.ty,
            PrimitiveNaming::Qualified,
            VarNaming::Lettered(&var_names),
        );
    }

    // Build a map from TypeId to the constraint traits for quick lookup.
    // Use sorted trait names for deterministic output.
    // Constraints are now Vec<FQTraitName>; use local trait name for display.
    let mut constraint_map: HashMap<TypeId, Vec<&str>> = HashMap::new();
    for (type_id, traits) in &scheme.constraints {
        let mut trait_strs: Vec<&str> = traits.iter().map(|t| t.name.as_ref()).collect();
        trait_strs.sort();
        constraint_map.insert(*type_id, trait_strs);
    }

    format_type_with_inline_constraints(
        &scheme.ty,
        &var_names,
        &constraint_map,
        false,
    )
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Format a type with inline constraint annotations (spec §1.3, §1.4).
///
/// Type names are fully qualified. Inside function param lists (`in_params = true`):
///   every occurrence of constrained var: `:TraitName var` (spec §3.5.1)
/// Outside param lists (return type, ADT args): vars are always bare.
///
/// S87 (FIXME 0420, §4.4 approach (a)): this renderer is REPL-display-specific —
/// the `:TraitName var` decoration in param position is a `cranelisp-types`
/// boundary crate must NOT own (Principle 1). It therefore keeps its own
/// recursion to thread `in_params`, but routes every variant that carries NO
/// constraint decoration — the primitive leaves, `ADT`, and `TyConApp` (vars
/// inside ADT/TyConApp args are always rendered bare) — through the shared
/// `cranelisp_types::render_type` walk with FQ primitives + lettered vars.
/// Only the `Fn` structure (which must thread `in_params`) and the constrained
/// `Var`-in-params decoration stay local.
fn format_type_with_inline_constraints(
    ty: &Type,
    var_names: &HashMap<TypeId, String>,
    constraints: &HashMap<TypeId, Vec<&str>>,
    in_params: bool,
) -> String {
    match ty {
        Type::Fn(params, ret) => {
            let parts: Vec<String> = params
                .iter()
                .map(|p| {
                    format_type_with_inline_constraints(
                        p, var_names, constraints, true,
                    )
                })
                .collect();
            let ret_s = format_type_with_inline_constraints(
                ret, var_names, constraints, false,
            );
            format!("(Fn [{}] {ret_s})", parts.join(" "))
        }
        Type::Var(id) => {
            let var_name = var_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("t{id}"));
            if in_params {
                if let Some(traits) = constraints.get(id) {
                    // Every occurrence in params: show `:TraitName var`
                    let trait_prefix: Vec<String> =
                        traits.iter().map(|t| format!(":{t}")).collect();
                    format!("{} {var_name}", trait_prefix.join(" "))
                } else {
                    // Unconstrained var in params: bare name
                    var_name
                }
            } else {
                // Outside params (return type, etc.): always bare
                var_name
            }
        }
        // Primitives, ADT, and TyConApp carry no `:TraitName` decoration (vars in
        // their args are always rendered bare), so they delegate fully to the
        // shared walk — FQ primitives + lettered vars, byte-identical to the
        // former local arms.
        Type::Int | Type::Bool | Type::String | Type::Float | Type::ADT(_, _)
        | Type::TyConApp(_, _) => {
            render_type(ty, PrimitiveNaming::Qualified, VarNaming::Lettered(var_names))
        }
    }
}

/// Format a String heap value as `:primitives/String "contents"`.
fn format_string_value(value: i64) -> String {
    if value == 0 || (value as usize) < NULLARY_TAG_THRESHOLD {
        // Null or small value -- not a valid heap pointer.
        return format!(":primitives/String <invalid:{value}>");
    }
    // SAFETY: value is a heap pointer to a valid HeapString (produced by JIT code).
    let s = unsafe { cranelisp_intrinsics::heap_string::read_string_as_str(value) };
    format!(":primitives/String \"{s}\"")
}

/// Check whether a type has exactly one constructor whose name matches the type name.
///
/// Single-constructor product types like `(deftype Point [:Int x :Int y])` have
/// a redundant `Type.Constructor` display (`Point.Point`). For these types we
/// suppress the `Type.` prefix and show just the constructor name.
fn is_single_matching_constructor(type_name: &str, type_info: &TypeDefInfo) -> bool {
    type_info.constructors.len() == 1 && type_info.constructors[0].as_ref() == type_name
}

/// Format the constructor display name for an ADT value.
///
/// For single-constructor types where the constructor name matches the type name,
/// returns just the constructor name (e.g., `Point`). For multi-constructor types,
/// returns `Type.Constructor` (e.g., `Color.Red`, `Option.Some`).
pub fn format_ctor_display(
    type_name: &str,
    ctor_name: &str,
    type_info: &TypeDefInfo,
) -> String {
    if is_single_matching_constructor(type_name, type_info) {
        ctor_name.to_string()
    } else {
        format!("{type_name}.{ctor_name}")
    }
}

/// Look up a TypeDefInfo from symbol tables by FQTypeName.
///
/// Reads an entry **as a type** — the int-side mirror of typecheck's
/// `type_def_view_of` (S79 Option 3a, FIXME 0319/0321). A sum/enum type's
/// `name` key is a `ModuleEntry::TypeDef`; a single-ctor **product** type's
/// `name` key collides with its sole constructor, so the surviving entry is the
/// got-slotted ctor `Def { kind: Constructor { type_def: Some(td), .. } }` that
/// carries the type facet `td`. Both must answer here, else a product value
/// renders as a raw pointer (Root C).
fn lookup_type_def_from_tables<C, L>(
    fqtn: &FQTypeName,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
) -> Option<TypeDefInfo>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let table = symbol_tables.get(&fqtn.module)?;
    let type_key = Symbol::from(fqtn.name.as_ref());
    match table.get(type_key.as_ref()) {
        Some(ModuleEntry::TypeDef { info, .. }) => Some(info.clone()),
        // A single-ctor product type: the entry is the ctor `Def` carrying the
        // type facet on its `DefKind::Constructor.type_def`.
        Some(ModuleEntry::Def { kind, .. }) => match kind.as_ref() {
            DefKind::Constructor { type_def: Some(td), .. } => Some((**td).clone()),
            _ => None,
        },
        _ => None,
    }
}

/// Format an ADT value with constructor name lookup and dot notation (spec §1.5).
///
/// Nullary constructors display as `Type.Ctor` (e.g., `Color.Red`).
/// Data constructors display as `(Type.Ctor field1 field2)` (e.g., `(Option.Some 42)`).
/// Single-constructor product types where the constructor name matches the type name
/// suppress the `Type.` prefix (e.g., `(Point 3 4)` not `(Point.Point 3 4)`).
/// Type names in the `:Type` prefix are fully qualified.
fn format_adt_value<C, L>(
    value: i64,
    fqtn: &FQTypeName,
    type_args: &[Type],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
) -> String
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let type_display = format_adt_type_qualified(fqtn, type_args);
    let type_name_str = fqtn.name.as_ref();

    // Vec is a built-in type, not in type_defs -- handle it specially.
    if type_name_str == "Vec" {
        let elem_type = type_args.first();
        let elems = format_vec_elements(value, elem_type, symbol_tables);
        return format!(":{type_display} {elems}");
    }

    let Some(type_info) = lookup_type_def_from_tables(fqtn, symbol_tables) else {
        // No type def available -- fallback to bare value display.
        return format!(":{type_display} {value}");
    };

    // R5 value-layout (Wave-3a): a flattened single-ctor single-value-field ADT
    // stores the field value INLINE — the runtime word is neither a nullary tag
    // nor a heap pointer. Recognise it before the tag/heap branching below, else
    // the flat word is misread as a tag (`<tag:N>`) or, for a `Float` field,
    // dereferenced as a pointer (SIGSEGV). Spec §12.9 / repl §1.5.
    if let Some(form) =
        format_value_layout_adt(value, fqtn, type_args, &type_info, symbol_tables)
    {
        return format!(":{type_display} {form}");
    }

    // Determine if this is a nullary tag or a heap pointer.
    if (value as usize) < NULLARY_TAG_THRESHOLD {
        // Nullary constructor: value is the tag directly.
        let tag = value as usize;
        let ctor_name = find_constructor_by_tag(&type_info, tag);
        let ctor_display = format_ctor_display(type_name_str, &ctor_name, &type_info);
        format!(":{type_display} {ctor_display}")
    } else {
        // Data constructor: read tag and fields from heap.
        format_adt_heap_value(value, &type_display, type_name_str, &type_info, type_args, symbol_tables)
    }
}

/// R5 value-layout display (spec §12.9 / repl §1.5).
///
/// A single-constructor, single-value-field ADT (`(deftype Box (Box [:Int v]))`)
/// is flattened by the Wave-3a `value_layout` optimisation: its runtime word is
/// the field's value carried INLINE — NOT a nullary tag and NOT a heap pointer.
/// The formatter recognises the shape via the SAME `cranelisp_types::value_layout`
/// predicate the backend's `HeapCategory::Value` arm uses (single-sourced — the
/// verdict is never re-derived here) and reconstructs `(Ctor field-value)` by
/// reading the flattened word AS the field's value. A value-layout ADT field is
/// itself value-eligible, so a nested value field recurses through
/// `format_field_value`. Returns the value-only form (no `:Type` prefix), or
/// `None` when the type is not value-layout (keeps the existing tag/heap path).
fn format_value_layout_adt<C, L>(
    value: i64,
    fqtn: &FQTypeName,
    type_args: &[Type],
    type_info: &TypeDefInfo,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
) -> Option<String>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    // Ask the single-sourced predicate — do NOT re-derive value-eligibility.
    let ty = Type::ADT(fqtn.clone(), type_args.to_vec());
    let concrete = cranelisp_types::ConcreteType::from_type(&ty).ok()?;
    cranelisp_types::value_layout(&concrete, Some(symbol_tables))?;

    // `value_layout` guarantees exactly one constructor with exactly one
    // value-eligible field; the flattened `value` IS that field's value.
    let ctor_name = type_info.constructors.first()?.to_string();
    let field_types = ctor_field_types(fqtn, &ctor_name, symbol_tables);
    let field_ty = field_types.first()?;
    let subst = build_adt_subst(type_info, type_args, symbol_tables);
    let field_ty = substitute_field_type(field_ty, &subst);
    let field_str = format_field_value(value, &field_ty, symbol_tables);
    let ctor_display = format_ctor_display(fqtn.name.as_ref(), &ctor_name, type_info);
    Some(format!("({ctor_display} {field_str})"))
}

/// Format the type portion of an ADT display with qualification (spec §1.4).
/// Simple types: `user/Color`. Parameterized: `(user/Option primitives/Int)`.
pub fn format_adt_type_qualified(
    fqtn: &FQTypeName,
    type_args: &[Type],
) -> String {
    let qname = format!("{}/{}", fqtn.module, fqtn.name);
    if type_args.is_empty() {
        qname
    } else {
        let arg_strs: Vec<String> = type_args
            .iter()
            .map(format_type_qualified)
            .collect();
        format!("({qname} {})", arg_strs.join(" "))
    }
}

/// Find a constructor name by tag, or return a fallback string.
///
/// S70: `TypeDefInfo.constructors` is now `Vec<Symbol>` in tag order — the tag
/// IS the index. (The `ConstructorInfo` struct with explicit `tag`/`fields`
/// retired; ctor metadata lives on each ctor's `DefKind::Constructor` Def.)
fn find_constructor_by_tag(type_info: &TypeDefInfo, tag: usize) -> String {
    type_info
        .constructors
        .get(tag)
        .map(|c| c.to_string())
        .unwrap_or_else(|| format!("<tag:{tag}>"))
}

/// Look up a constructor's field types by reading its scheme.
///
/// A data constructor's scheme is `forall [vars]. (Fn [field-tys] ADT)`; the
/// `Fn` param types ARE the field types in declaration order. A nullary
/// constructor has a non-`Fn` scheme (bare ADT) → no fields.
///
/// Single storage shape (S79 Option 3a, FIXME 0319): every constructor — sum,
/// enum, AND single-ctor product — is a got-slotted `ModuleEntry::Def { kind:
/// Constructor }` keyed by the ctor name, carrying the field types on its own
/// `scheme`. A single-ctor product where ctor name == type name (e.g.
/// `(deftype Point [:Int x :Int y])`) is the SAME `Def` (it additionally carries
/// a `type_def: Some(..)` type facet), so the `Def` arm matches it too. The old
/// `ModuleEntry::TypeDef.constructor_scheme` product-fallback leg (FIXME 0302) is
/// retired — there is no separate `TypeDef` entry under a product's name.
///
/// S70: replaces the retired `ConstructorInfo.fields` lookup.
fn ctor_field_types<C, L>(
    fqtn: &FQTypeName,
    ctor_name: &str,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
) -> Vec<Type>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let Some(table) = symbol_tables.get(&fqtn.module) else {
        return Vec::new();
    };
    let scheme_ty = match table.get(ctor_name) {
        // Every constructor — sum, enum, and single-ctor product — is now a
        // got-slotted `Def`; field types come off its `scheme`.
        Some(ModuleEntry::Def { scheme, .. }) => Some(&scheme.ty),
        _ => None,
    };
    match scheme_ty {
        Some(Type::Fn(params, _)) => params.clone(),
        _ => Vec::new(),
    }
}

/// Format a heap-allocated ADT value (data constructor with fields).
///
/// Reads tag from HeapAdt::TAG_OFFSET (16), fields from HeapAdt::field_offset(i).
/// Recursively formats field values using their declared types.
/// Uses `Type.Constructor` dot notation per spec §1.5, suppressing the `Type.`
/// prefix for single-constructor product types where the constructor name matches
/// the type name.
///
/// For polymorphic ADTs (e.g., `(Option Int)`), substitutes the concrete type_args
/// into field types before formatting. Without this, fields with type variables
/// would display as raw values instead of properly formatted values.
fn format_adt_heap_value<C, L>(
    value: i64,
    type_display: &str,
    type_name: &str,
    type_info: &TypeDefInfo,
    type_args: &[Type],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
) -> String
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    // SAFETY: value is a heap pointer to a valid HeapAdt (produced by JIT code).
    let base = value as *const u8;
    let tag = unsafe { *(base.add(HeapAdt::TAG_OFFSET as usize) as *const i64) } as usize;

    // S70: tag is the index into `constructors: Vec<Symbol>`; field types come
    // from the ctor Def's scheme.
    let Some(ctor_name) = type_info.constructors.get(tag).map(|s| s.to_string()) else {
        return format!(":{type_display} <unknown-tag:{tag}>");
    };
    let fqtn = &type_info.name;
    let field_types = ctor_field_types(fqtn, &ctor_name, symbol_tables);

    if field_types.is_empty() {
        // Nullary constructor stored on heap (shouldn't happen, but handle gracefully).
        let ctor_display = format_ctor_display(type_name, &ctor_name, type_info);
        return format!(":{type_display} {ctor_display}");
    }

    // Build substitution from type_params to type_args for polymorphic ADTs.
    let subst = build_adt_subst(type_info, type_args, symbol_tables);

    // Read and format each field.
    let mut field_strs = Vec::new();
    for (i, field_ty) in field_types.iter().enumerate() {
        let field_offset = HeapAdt::field_offset(i) as usize;
        let field_val = unsafe { *(base.add(field_offset) as *const i64) };
        // Substitute type args into field type before formatting.
        let field_ty = substitute_field_type(field_ty, &subst);
        let field_str = format_field_value(field_val, &field_ty, symbol_tables);
        field_strs.push(field_str);
    }

    let fields_display = field_strs.join(" ");
    let ctor_display = format_ctor_display(type_name, &ctor_name, type_info);
    format!(":{type_display} ({ctor_display} {fields_display})")
}

/// Build a type substitution from a TypeDefInfo's type_params and concrete type_args.
///
/// The type_params are Symbol names (e.g., "a", "b") but the field types use
/// Type::Var(TypeId). We need to map from the Var ids used in field types
/// to the concrete types in type_args.
fn build_adt_subst<C, L>(
    type_info: &TypeDefInfo,
    type_args: &[Type],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
) -> HashMap<TypeId, Type>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let mut subst = HashMap::new();
    // Collect all Var ids used in constructor fields, in order. S70: field
    // types are read from each ctor Def's scheme rather than a pre-built
    // `ConstructorInfo.fields` vector.
    let mut var_ids = Vec::new();
    for ctor in &type_info.constructors {
        for field_ty in ctor_field_types(&type_info.name, ctor.as_ref(), symbol_tables) {
            collect_var_ids(&field_ty, &mut var_ids);
        }
    }
    // Map each unique Var id to the corresponding type arg.
    for (i, &id) in var_ids.iter().enumerate() {
        if i < type_args.len() {
            subst.insert(id, type_args[i].clone());
        }
    }
    subst
}

/// Collect unique Var ids from a type in order of first occurrence.
fn collect_var_ids(ty: &Type, ids: &mut Vec<TypeId>) {
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

/// Strip the `:{type_display} ` value-line prefix from a recursively-rendered
/// ADT display, leaving just the constructor value form (e.g.
/// `(Wrap.MkWrap 7)`).
///
/// `type_display` may itself contain spaces when the nested value is a
/// PARAMETERIZED ADT — `(user/Wrap primitives/Int)`. A naive
/// `split_once(' ')` split at the first space lands INSIDE the type
/// (`:(user/Wrap` | `primitives/Int) …`), which is exactly the FIXME 0493
/// garbling (a type token where the nested constructor should open, plus an
/// unbalanced closing paren). Stripping the exact known prefix is space-safe.
fn strip_type_prefix(rendered: String, type_display: &str) -> String {
    let prefix = format!(":{type_display} ");
    match rendered.strip_prefix(&prefix) {
        Some(rest) => rest.to_string(),
        None => rendered,
    }
}

/// Substitute type variables in a field type using the given substitution.
fn substitute_field_type(
    ty: &Type,
    subst: &HashMap<TypeId, Type>,
) -> Type {
    cranelisp_types::apply(subst, ty)
}

/// Format Vec elements by reading the heap layout.
///
/// HeapVec layout: `[alloc_size(+0) | rc(+8) | len(+16) | cap(+24) | data_ptr(+32)]`
/// Elements are stored in the data buffer at `data_ptr`, each 8 bytes (i64).
fn format_vec_elements<C, L>(
    value: i64,
    elem_type: Option<&Type>,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
) -> String
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    if value == 0 || (value as usize) < NULLARY_TAG_THRESHOLD {
        return "[]".to_string();
    }

    let base = value as *const u8;
    // SAFETY: value is a heap pointer to a valid HeapVec (produced by JIT code).
    let len = unsafe { *(base.add(HeapVec::LEN_OFFSET as usize) as *const i64) } as usize;
    if len == 0 {
        return "[]".to_string();
    }

    let data_ptr = unsafe { *(base.add(HeapVec::DATA_PTR_OFFSET as usize) as *const *const i64) };
    if data_ptr.is_null() {
        return "[]".to_string();
    }

    let mut elems = Vec::with_capacity(len);
    for i in 0..len {
        let elem_val = unsafe { *data_ptr.add(i) };
        let formatted = match elem_type {
            Some(ty) => format_field_value(elem_val, ty, symbol_tables),
            None => format!("{elem_val}"),
        };
        elems.push(formatted);
    }

    format!("[{}]", elems.join(" "))
}

/// Format a single field value based on its type.
///
/// Field values use `Type.Constructor` dot notation for ADT constructors (spec §1.5).
fn format_field_value<C, L>(
    value: i64,
    ty: &Type,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
) -> String
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    match ty {
        Type::Int => format!("{value}"),
        Type::Bool => {
            if value != 0 { "true".to_string() } else { "false".to_string() }
        }
        Type::Float => {
            let f = f64::from_bits(value as u64);
            let s = format!("{f}");
            if s.contains('.') { s } else { format!("{s}.0") }
        }
        Type::String => {
            if value == 0 || (value as usize) < NULLARY_TAG_THRESHOLD {
                format!("<invalid-string:{value}>")
            } else {
                // SAFETY: value is a heap pointer to a valid HeapString (produced by JIT code);
                // the guard above rejects null and small (nullary tag) values.
                let s = unsafe { cranelisp_intrinsics::heap_string::read_string_as_str(value) };
                format!("\"{s}\"")
            }
        }
        Type::Fn(_, _) => "<closure>".to_string(),
        Type::ADT(fqtn, args) => {
            let type_name_str = fqtn.name.as_ref();
            // Vec is built-in, not in type_defs.
            if type_name_str == "Vec" {
                return format_vec_elements(value, args.first(), symbol_tables);
            }
            // Recursive ADT formatting with dot notation.
            let type_display = format_adt_type_qualified(fqtn, args);
            if let Some(info) = lookup_type_def_from_tables(fqtn, symbol_tables) {
                // R5 value-layout: a nested flattened single-value-field ADT
                // stores its field value inline — recognise it before the
                // tag/heap branch (else `<tag:N>` / pointer-deref crash).
                if let Some(form) =
                    format_value_layout_adt(value, fqtn, args, &info, symbol_tables)
                {
                    form
                } else if (value as usize) < NULLARY_TAG_THRESHOLD {
                    let tag = value as usize;
                    let ctor_name = find_constructor_by_tag(&info, tag);
                    format_ctor_display(type_name_str, &ctor_name, &info)
                } else {
                    // Recursive heap ADT -- format with parens and dot notation.
                    let inner = format_adt_heap_value(
                        value, &type_display, type_name_str, &info, args, symbol_tables,
                    );
                    // Strip the leading `:{type_display} ` prefix, leaving just
                    // the nested constructor value. `type_display` may itself
                    // contain spaces for a PARAMETERIZED nested ADT (e.g.
                    // `(user/Wrap primitives/Int)`), so the old `split_once(' ')`
                    // split INSIDE the type — leaking a type token and dropping a
                    // closing paren (FIXME 0493). Strip the exact known prefix.
                    strip_type_prefix(inner, &type_display)
                }
            } else {
                format!("{value}")
            }
        }
        _ => format!("{value}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::FQTraitName;

    // --- strip_type_prefix (FIXME 0493 — nested parameterized-ADT display) ---

    // The garbling cell: a nested PARAMETERIZED ADT's type_display contains a
    // space, so the pre-fix split_once(' ') split inside the type, leaking a
    // type token + dropping a paren. The exact-prefix strip is space-safe.
    #[test]
    fn strip_type_prefix_parameterized_nested_type_is_space_safe() {
        let rendered = ":(user/Wrap primitives/Int) (Wrap.MkWrap 7)".to_string();
        assert_eq!(
            strip_type_prefix(rendered, "(user/Wrap primitives/Int)"),
            "(Wrap.MkWrap 7)"
        );
    }

    #[test]
    fn strip_type_prefix_simple_type() {
        let rendered = ":user/Color Color.Red".to_string();
        assert_eq!(strip_type_prefix(rendered, "user/Color"), "Color.Red");
    }

    // A doubly-nested value: the whole recursive form after the outer type is
    // preserved (no premature split at the first inner space).
    #[test]
    fn strip_type_prefix_preserves_doubly_nested_value() {
        let rendered =
            ":(user/List primitives/Int) (List.Cons 1 (List.Cons 2 List.Nil))".to_string();
        assert_eq!(
            strip_type_prefix(rendered, "(user/List primitives/Int)"),
            "(List.Cons 1 (List.Cons 2 List.Nil))"
        );
    }

    // --- constructor-name decision seams (FIXME 0496 — the ADT-render core) ---
    //
    // `format_adt_value`/`format_adt_heap_value` are generic over the heap and
    // hard to drive without a live JIT value, but the *decision* of which
    // constructor name to render (and whether to suppress the redundant
    // `Type.` prefix on a single-ctor product) is pure and is the seam the
    // 0493 garbled-render defect lived at. These pin that decision directly.

    fn type_info(type_name: &str, ctors: &[&str]) -> TypeDefInfo {
        TypeDefInfo {
            name: FQTypeName::new(
                ModuleFullPath::from("user"),
                cranelisp_types::TypeName::from(type_name),
            ),
            type_params: Vec::new(),
            constructors: ctors.iter().map(|c| Symbol::from(*c)).collect(),
        }
    }

    // spec: repl/spec.md §1.5 — data ctor at a valid tag renders its name
    #[test]
    fn find_constructor_by_tag_valid() {
        let ti = type_info("Color", &["Red", "Green", "Blue"]);
        assert_eq!(find_constructor_by_tag(&ti, 0), "Red");
        assert_eq!(find_constructor_by_tag(&ti, 2), "Blue");
    }

    // spec: repl/spec.md §1.5 — an out-of-range tag falls back to `<tag:N>`
    // rather than panicking or silently mis-indexing (negative/edge cell).
    #[test]
    fn find_constructor_by_tag_out_of_range_falls_back() {
        let ti = type_info("Color", &["Red", "Green", "Blue"]);
        assert_eq!(find_constructor_by_tag(&ti, 3), "<tag:3>");
        assert_eq!(find_constructor_by_tag(&type_info("Empty", &[]), 0), "<tag:0>");
    }

    // spec: repl/spec.md §1.5 — single-ctor product (ctor name == type name)
    // is the prefix-suppression trigger.
    #[test]
    fn is_single_matching_constructor_product_true() {
        assert!(is_single_matching_constructor("Point", &type_info("Point", &["Point"])));
    }

    // spec: repl/spec.md §1.5 — a multi-ctor type is NOT prefix-suppressed
    // (negative), nor is a lone ctor whose name differs from the type.
    #[test]
    fn is_single_matching_constructor_negatives() {
        // two ctors → not a product
        assert!(!is_single_matching_constructor("Color", &type_info("Color", &["Red", "Green"])));
        // single ctor but name differs from the type
        assert!(!is_single_matching_constructor("Wrap", &type_info("Wrap", &["MkWrap"])));
    }

    // spec: repl/spec.md §1.5 — product suppresses `Type.`; sum/enum keeps it.
    #[test]
    fn format_ctor_display_product_suppresses_prefix() {
        let ti = type_info("Point", &["Point"]);
        assert_eq!(format_ctor_display("Point", "Point", &ti), "Point");
    }

    #[test]
    fn format_ctor_display_multi_ctor_keeps_prefix() {
        let ti = type_info("Option", &["Some", "None"]);
        assert_eq!(format_ctor_display("Option", "Some", &ti), "Option.Some");
        assert_eq!(format_ctor_display("Option", "None", &ti), "Option.None");
    }

    // --- format_value: scalar types ---

    #[test]
    fn format_value_int_positive() {
        let empty: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let v = format_value(42, &Type::Int, &empty);
        assert_eq!(v, "42");
    }

    #[test]
    fn format_value_int_negative() {
        let empty: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let v = format_value(-7, &Type::Int, &empty);
        assert_eq!(v, "-7");
    }

    #[test]
    fn format_value_int_zero() {
        let empty: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let v = format_value(0, &Type::Int, &empty);
        assert_eq!(v, "0");
    }

    #[test]
    fn format_value_bool_true() {
        let empty: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let v = format_value(1, &Type::Bool, &empty);
        assert_eq!(v, "true");
    }

    #[test]
    fn format_value_bool_false() {
        let empty: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let v = format_value(0, &Type::Bool, &empty);
        assert_eq!(v, "false");
    }

    #[test]
    fn format_value_float_with_decimal() {
        let empty: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        // 3.25, not 3.14: clippy::approx_constant (deny) rejects near-PI literals.
        let bits = 3.25_f64.to_bits() as i64;
        let v = format_value(bits, &Type::Float, &empty);
        assert!(v.contains('.'), "float display should contain a decimal point: {v}");
    }

    #[test]
    fn format_value_float_whole_number_gets_dot_zero() {
        let empty: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let bits = 1.0_f64.to_bits() as i64;
        let v = format_value(bits, &Type::Float, &empty);
        assert!(v.ends_with(".0"), "whole float should end with .0: {v}");
    }

    #[test]
    fn format_value_fn_displays_closure() {
        let empty: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let ty = Type::Fn(vec![Type::Int], Box::new(Type::Int));
        let v = format_value(0, &ty, &empty);
        assert_eq!(v, "<closure>");
    }

    // --- format_type_qualified: primitive types ---

    #[test]
    fn format_type_qualified_int() {
        let s = format_type_qualified(&Type::Int);
        assert_eq!(s, "primitives/Int");
    }

    #[test]
    fn format_type_qualified_bool() {
        let s = format_type_qualified(&Type::Bool);
        assert_eq!(s, "primitives/Bool");
    }

    #[test]
    fn format_type_qualified_string() {
        let s = format_type_qualified(&Type::String);
        assert_eq!(s, "primitives/String");
    }

    #[test]
    fn format_type_qualified_float() {
        let s = format_type_qualified(&Type::Float);
        assert_eq!(s, "primitives/Float");
    }

    #[test]
    fn format_type_qualified_fn() {
        let ty = Type::Fn(vec![Type::Int, Type::Bool], Box::new(Type::String));
        let s = format_type_qualified(&ty);
        assert_eq!(s, "(Fn [primitives/Int primitives/Bool] primitives/String)");
    }

    // --- format_result_value: `:Type value` prefix ---

    #[test]
    fn format_result_value_int() {
        let empty: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let s = format_result_value(42, &Type::Int, &empty);
        assert_eq!(s, ":primitives/Int 42");
    }

    #[test]
    fn format_result_value_bool_true() {
        let empty: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let s = format_result_value(1, &Type::Bool, &empty);
        assert_eq!(s, ":primitives/Bool true");
    }

    #[test]
    fn format_result_value_bool_false() {
        let empty: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let s = format_result_value(0, &Type::Bool, &empty);
        assert_eq!(s, ":primitives/Bool false");
    }

    #[test]
    fn format_result_value_float() {
        let empty: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let bits = 2.5_f64.to_bits() as i64;
        let s = format_result_value(bits, &Type::Float, &empty);
        assert_eq!(s, ":primitives/Float 2.5");
    }

    #[test]
    fn format_result_value_fn() {
        let empty: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let ty = Type::Fn(vec![Type::Int], Box::new(Type::Int));
        let s = format_result_value(0, &ty, &empty);
        assert_eq!(s, ":(Fn [primitives/Int] primitives/Int) <closure>");
    }

    // --- format_scheme_display: constrained types ---

    // spec: spec/03-types.md §3.5.1 — constraint prefix repeated on every occurrence
    #[test]
    fn format_scheme_display_repeats_constraints_on_every_var_occurrence() {
        // (Fn [:Num a :Num a] a) — two params with same constrained var
        let var_id = 100;
        let scheme = Scheme {
            type_vars: vec![var_id],
            constraints: HashMap::from([(var_id, vec![FQTraitName::new(
                ModuleFullPath::from("core.num"),
                "Num".into(),
            )])]),
            ty: Type::Fn(
                vec![Type::Var(var_id), Type::Var(var_id)],
                Box::new(Type::Var(var_id)),
            ),
        };
        let module = ModuleFullPath::from("user");
        let s = format_scheme_display("add", &scheme, &module);
        assert_eq!(s, ":(Fn [:Num a :Num a] a) user/add");
    }

    // spec: spec/03-types.md §3.5.1 — multiple constraints repeated on every occurrence
    #[test]
    fn format_scheme_display_repeats_multiple_constraints() {
        // (Fn [:Eq :Num a :Eq :Num a] a)
        let var_id = 100;
        let scheme = Scheme {
            type_vars: vec![var_id],
            constraints: HashMap::from([(
                var_id,
                vec![
                    FQTraitName::new(ModuleFullPath::from("core.num"), "Num".into()),
                    FQTraitName::new(ModuleFullPath::from("core.eq"), "Eq".into()),
                ],
            )]),
            ty: Type::Fn(
                vec![Type::Var(var_id), Type::Var(var_id)],
                Box::new(Type::Var(var_id)),
            ),
        };
        let module = ModuleFullPath::from("user");
        let s = format_scheme_display("bar", &scheme, &module);
        // Traits are sorted alphabetically: Eq before Num
        assert_eq!(s, ":(Fn [:Eq :Num a :Eq :Num a] a) user/bar");
    }

    // --- format_result: convenience wrapper ---

    #[test]
    fn format_result_delegates_correctly() {
        let s = format_result(99, &Type::Int);
        assert_eq!(s, ":primitives/Int 99");
    }

    // --- ctor_field_types: single-ctor product (S79 Option 3a, FIXME 0319) ---

    use cranelisp_types::{DefKind, ModuleEntry, Symbol, TypeDefInfo};

    fn point_fqtn() -> FQTypeName {
        FQTypeName {
            module: ModuleFullPath::from("user"),
            name: cranelisp_types::TypeName::from("Point"),
        }
    }

    /// Build a `user` module table holding only a single-constructor product
    /// `Point` whose ctor name == type name. The `Point` key holds a got-slotted
    /// ctor `Def` carrying the field types on its own `scheme` AND a type facet
    /// (`type_def: Some(..)`), exactly as the typechecker registers it (S79
    /// Option 3a). There is no separate `TypeDef` entry.
    fn point_product_tables() -> DashMap<ModuleFullPath, SymbolTable> {
        let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let mut table = SymbolTable::new(ModuleFullPath::from("user"));
        let info = TypeDefInfo {
            name: point_fqtn(),
            type_params: Vec::new(),
            constructors: vec![Symbol::from("Point")],
        };
        // ctor scheme: (Fn [Int Int] Point)
        let ctor_scheme = Scheme {
            type_vars: Vec::new(),
            constraints: HashMap::new(),
            ty: Type::Fn(
                vec![Type::Int, Type::Int],
                Box::new(Type::ADT(point_fqtn(), Vec::new())),
            ),
        };
        table.insert(
            Symbol::from("Point"),
            ModuleEntry::def(ctor_scheme, DefKind::Constructor {
                got_slot: 0,
                type_name: point_fqtn(),
                tag: 0,
                field_count: 2,
                internal: false,
                type_def: Some(Box::new(info)),
                mode_summary: None,
            })
            .param_names(vec![Symbol::from("x"), Symbol::from("y")])
            .build(),
        );
        tables.insert(ModuleFullPath::from("user"), table);
        tables
    }

    // spec: repl/spec.md §1.5 (line 309) — single-ctor product whose ctor name
    // matches the type name. The `Point` key holds the got-slotted ctor `Def`
    // (with a `type_def: Some(..)` facet); `ctor_field_types` reads its `scheme`
    // exactly like any other ctor — the prior `constructor_scheme` product
    // fallback (FIXME 0302) is retired (S79 Option 3a, FIXME 0319).
    #[test]
    fn ctor_field_types_reads_single_ctor_product_def_scheme() {
        let tables = point_product_tables();
        let fields = ctor_field_types(&point_fqtn(), "Point", &tables);
        assert_eq!(
            fields,
            vec![Type::Int, Type::Int],
            "single-ctor product field types come off the product ctor Def's scheme"
        );
    }

    // Negative: a multi-ctor type registers each ctor as a distinct `Def`, so
    // the `Def` arm resolves field types for sum ctors too — same arm as the
    // product case (no product special-case remains).
    #[test]
    fn ctor_field_types_reads_distinct_def_for_named_ctor() {
        let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let mut table = SymbolTable::new(ModuleFullPath::from("user"));
        let fqtn = FQTypeName {
            module: ModuleFullPath::from("user"),
            name: cranelisp_types::TypeName::from("Shape"),
        };
        // ctor `Circle` keyed separately from its type `Shape`.
        let ctor_scheme = Scheme {
            type_vars: Vec::new(),
            constraints: HashMap::new(),
            ty: Type::Fn(vec![Type::Float], Box::new(Type::ADT(fqtn.clone(), Vec::new()))),
        };
        table.insert(
            Symbol::from("Circle"),
            ModuleEntry::def(ctor_scheme, DefKind::Constructor {
                got_slot: 0,
                type_name: fqtn.clone(),
                tag: 0,
                field_count: 1,
                internal: false,
                type_def: None,
                mode_summary: None,
            })
            .build(),
        );
        tables.insert(ModuleFullPath::from("user"), table);
        let fields = ctor_field_types(&fqtn, "Circle", &tables);
        assert_eq!(fields, vec![Type::Float]);
    }

    // --- Root C (FIXME 0321): product-ctor value display ---

    // spec: repl/spec.md §1.5 — a single-ctor product type's `name` key is its
    // ctor `Def` carrying the `type_def` facet, NOT a `ModuleEntry::TypeDef`.
    // `lookup_type_def_from_tables` (the "entry as a type" reader) MUST extract
    // the facet for products too — else a product VALUE falls through to the raw
    // pointer fallback in `format_adt_value` (`:user/Point <rawptr>`) instead of
    // `(Point 3 4)`. Guards the Root-C value-display regression.
    #[test]
    fn lookup_type_def_resolves_product_ctor_facet() {
        let tables = point_product_tables();
        let info = lookup_type_def_from_tables(&point_fqtn(), &tables)
            .expect("a product type resolves via its ctor Def's type_def facet");
        assert_eq!(info.name, point_fqtn());
        assert_eq!(info.constructors, vec![Symbol::from("Point")]);
        // The product ctor's name matches the type name → `format_ctor_display`
        // suppresses the redundant dot, yielding bare `Point` not `Point.Point`.
        assert_eq!(format_ctor_display("Point", "Point", &info), "Point");
    }

    // --- R5 value-layout display (S103 Defect 1, FIXME(/backend)) ---

    /// Build a `user` module table holding a single-constructor, single-field
    /// value-layout ADT `(deftype {name} ({name} [:{field} v]))`. Both the type
    /// facet and the ctor `Def` (with a `(Fn [field] ADT)` scheme) live under the
    /// `{name}` key — exactly the shape `value_layout` reads.
    fn value_layout_tables(name: &str, field_ty: Type) -> DashMap<ModuleFullPath, SymbolTable> {
        let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let mut table = SymbolTable::new(ModuleFullPath::from("user"));
        let fqtn = FQTypeName {
            module: ModuleFullPath::from("user"),
            name: cranelisp_types::TypeName::from(name),
        };
        let info = TypeDefInfo {
            name: fqtn.clone(),
            type_params: Vec::new(),
            constructors: vec![Symbol::from(name)],
        };
        let ctor_scheme = Scheme {
            type_vars: Vec::new(),
            constraints: HashMap::new(),
            ty: Type::Fn(vec![field_ty], Box::new(Type::ADT(fqtn.clone(), Vec::new()))),
        };
        table.insert(
            Symbol::from(name),
            ModuleEntry::def(ctor_scheme, DefKind::Constructor {
                got_slot: 0,
                type_name: fqtn.clone(),
                tag: 0,
                field_count: 1,
                internal: false,
                type_def: Some(Box::new(info)),
                mode_summary: None,
            })
            .param_names(vec![Symbol::from("v")])
            .build(),
        );
        tables.insert(ModuleFullPath::from("user"), table);
        tables
    }

    fn adt_ty(name: &str) -> Type {
        Type::ADT(
            FQTypeName {
                module: ModuleFullPath::from("user"),
                name: cranelisp_types::TypeName::from(name),
            },
            Vec::new(),
        )
    }

    // spec: repl/spec.md §1.5 — a value_layout-flattened single-Int-field ADT
    // renders as the constructor form `(Box 99)`, reading the flattened word AS
    // the Int field value — NOT as a `<tag:99>` sentinel.
    #[test]
    fn format_result_value_r5_value_layout_int() {
        let tables = value_layout_tables("Box", Type::Int);
        let s = format_result_value(99, &adt_ty("Box"), &tables);
        assert_eq!(s, ":user/Box (Box 99)");
    }

    // spec: spec/12-runtime.md §12.9 — the value_layout class over a `:Float`
    // field: the flattened f64 bit-pattern MUST be read as the field value, never
    // dereferenced as a heap pointer (the SIGSEGV the e2e repro pins). No crash.
    #[test]
    fn format_result_value_r5_value_layout_float_reads_field_not_pointer() {
        let tables = value_layout_tables("F", Type::Float);
        let bits = 2.5_f64.to_bits() as i64; // a huge word — a raw ptr-deref would crash
        let s = format_result_value(bits, &adt_ty("F"), &tables);
        assert_eq!(s, ":user/F (F 2.5)");
    }

    // spec: repl/spec.md §1.5 — the value_layout class over a `:Bool` field
    // renders the discriminant word as the bool value: `(B true)`, not `<tag:1>`.
    #[test]
    fn format_result_value_r5_value_layout_bool() {
        let tables = value_layout_tables("B", Type::Bool);
        let s = format_result_value(1, &adt_ty("B"), &tables);
        assert_eq!(s, ":user/B (B true)");
    }

    // spec: repl/spec.md §1.5 — a value_layout ADT nested as a FIELD of an outer
    // (non-value_layout, 2-field) ADT recurses to its constructor form: the flat
    // inner word renders `(Box 5)` inside the outer `format_field_value` path.
    #[test]
    fn format_field_value_r5_value_layout_nested() {
        let tables = value_layout_tables("Box", Type::Int);
        // Format the flattened Box word (5) as a nested Box field.
        let s = format_field_value(5, &adt_ty("Box"), &tables);
        assert_eq!(s, "(Box 5)");
    }
}
