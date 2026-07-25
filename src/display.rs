// Canonical value display format (spec §12.9).
//
// Migrated from cranelisp-backend in Sprint 66 Wave 3b-2a. Owned by the int
// crate as a REPL/trace concern (presentation, not codegen). Imports the heap
// layout constants from cranelisp-backend::heap; depends on cranelisp-types
// for type definitions and cranelisp-intrinsics for string access.

use std::collections::HashMap;

use dashmap::DashMap;

use cranelisp_types::{
    DefKind, FQTypeName, ModuleEntry, ModuleFullPath, NULLARY_TAG_THRESHOLD, PrimitiveNaming,
    Scheme, Symbol, SymbolTable, Type, TypeDefInfo, TypeId, VarNaming, render_type,
};

use cranelisp_backend::heap::{HeapAdt, HeapVec};

use crate::styled::{Role, StyledDoc, render};

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
/// The plain-text value-only display (no `:Type` prefix) — the `.text()` of the
/// `push_field_value` span build. Exercised by this module's unit tests;
/// `format_result_value` is the production entry point (REPL result display).
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
    let mut doc = StyledDoc::new();
    push_field_value(value, ty, symbol_tables, &mut doc);
    doc.text()
}

/// Format a runtime value with `:Type value` prefix for REPL display.
///
/// Combines qualified type formatting with value formatting. This is the
/// top-level entry point for REPL result display — it builds a role-tagged
/// `StyledDoc` (the §10.3 R4 type annotation + R2/R3/R15 value spans) and
/// `render`s it. Colour-off the output is byte-identical to the role-free text.
pub fn format_result_value<C, L>(
    value: i64,
    ty: &Type,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
) -> String
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    render(&result_value_doc(value, ty, symbol_tables))
}

/// Build the `:Type value` result-value `StyledDoc` — R4 type annotation, then
/// the value literal as R2 (num/bool) / R3 (string) / R15 (closure, ctor, vec).
pub(crate) fn result_value_doc<C, L>(
    value: i64,
    ty: &Type,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
) -> StyledDoc
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let mut doc = StyledDoc::new();
    match ty {
        Type::Bool => {
            let display_val = if value != 0 { "true" } else { "false" };
            envelope(&mut doc, ":primitives/Bool", |d| {
                d.push(Role::LitNumBool, display_val)
            });
        }
        Type::Float => {
            let f = f64::from_bits(value as u64);
            let s = format!("{f}");
            let s = if s.contains('.') { s } else { format!("{s}.0") };
            envelope(&mut doc, ":primitives/Float", |d| {
                d.push(Role::LitNumBool, s)
            });
        }
        Type::Int => {
            envelope(&mut doc, ":primitives/Int", |d| {
                d.push(Role::LitNumBool, value.to_string())
            });
        }
        Type::String => {
            if value == 0 || (value as usize) < NULLARY_TAG_THRESHOLD {
                envelope(&mut doc, ":primitives/String", |d| {
                    d.plain(format!("<invalid:{value}>"))
                });
            } else {
                // SAFETY: value is a heap pointer to a valid HeapString.
                let s = unsafe { cranelisp_intrinsics::heap_string::read_string_as_str(value) };
                envelope(&mut doc, ":primitives/String", |d| {
                    d.push(Role::LitStr, format!("\"{s}\""))
                });
            }
        }
        Type::Fn(_, _) => {
            let type_str = format_type_qualified(ty);
            envelope(&mut doc, &format!(":{type_str}"), |d| d.plain("<closure>"));
        }
        Type::ADT(fqtn, type_args) => {
            let type_display = format_adt_type_qualified(fqtn, type_args);
            doc.push(Role::TypeAnnotation, format!(":{type_display}"));
            doc.plain(" ");
            push_adt_value_form(value, fqtn, type_args, symbol_tables, &mut doc);
        }
        other => {
            let type_str = format_type_qualified(other);
            envelope(&mut doc, &format!(":{type_str}"), |d| {
                d.plain(value.to_string())
            });
        }
    }
    doc
}

/// Push a `:Type value` envelope: the R4 type annotation, a `Plain` space, then
/// the caller's value spans.
fn envelope(doc: &mut StyledDoc, type_ann: &str, value: impl FnOnce(&mut StyledDoc)) {
    doc.push(Role::TypeAnnotation, type_ann);
    doc.plain(" ");
    value(doc);
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
pub fn format_type_qualified(ty: &Type) -> String {
    // Compute var names from the full type, then render through the shared walk
    // (S87 consolidation, FIXME 0420): FQ primitives + lettered vars reproduce
    // the former `format_type_qualified_inner` byte-for-byte.
    let var_names = cranelisp_types::type_var_names(ty);
    render_type(
        ty,
        PrimitiveNaming::Qualified,
        VarNaming::Lettered(&var_names),
    )
}

/// Format a constrained function's scheme for REPL display (spec §1.3).
///
/// Produces inline-constraint notation:
///   `:(Fn [:Num a :Num a] a) user/double`
///
/// Every occurrence of a constrained type variable in parameter position
/// is shown as `:TraitName var` (spec §3.5.1).
/// Unconstrained variables appear bare.
#[cfg(test)]
pub fn format_scheme_display(name: &str, scheme: &Scheme, module: &ModuleFullPath) -> String {
    format_scheme_display_doc(name, scheme, module).text()
}

/// The `:Type module/name` primary-line `StyledDoc` — R4 type annotation, R7 dim
/// `module/` prefix, R15 name. The single-source builder for the introspection
/// primary line (`format_def_entry`, `format_overloaded_variants`).
pub(crate) fn format_scheme_display_doc(
    name: &str,
    scheme: &Scheme,
    module: &ModuleFullPath,
) -> StyledDoc {
    let type_str = format_scheme_type(scheme);
    let mut d = StyledDoc::new();
    d.push(Role::TypeAnnotation, format!(":{type_str}"));
    d.plain(" ");
    d.push(Role::ModulePrefix, format!("{module}/"));
    d.plain(name);
    d
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

    // Build a map from TypeId to the canonical constraint-trait identities for
    // quick lookup.  The typechecker has already resolved these names; display
    // must consume that settled identity rather than narrowing it back to a
    // bare name and trying to qualify it again later.
    let mut constraint_map: HashMap<TypeId, Vec<String>> = HashMap::new();
    for (type_id, traits) in &scheme.constraints {
        let mut trait_strs: Vec<String> = traits.iter().map(ToString::to_string).collect();
        trait_strs.sort();
        constraint_map.insert(*type_id, trait_strs);
    }

    format_type_with_inline_constraints(&scheme.ty, &var_names, &constraint_map, false)
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
    constraints: &HashMap<TypeId, Vec<String>>,
    in_params: bool,
) -> String {
    match ty {
        Type::Fn(params, ret) => {
            let parts: Vec<String> = params
                .iter()
                .map(|p| format_type_with_inline_constraints(p, var_names, constraints, true))
                .collect();
            let ret_s = format_type_with_inline_constraints(ret, var_names, constraints, false);
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
        Type::Int
        | Type::Bool
        | Type::String
        | Type::Float
        | Type::ADT(_, _)
        | Type::TyConApp(_, _) => render_type(
            ty,
            PrimitiveNaming::Qualified,
            VarNaming::Lettered(var_names),
        ),
    }
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
pub fn format_ctor_display(type_name: &str, ctor_name: &str, type_info: &TypeDefInfo) -> String {
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
            DefKind::Constructor {
                type_def: Some(td), ..
            } => Some((**td).clone()),
            _ => None,
        },
        _ => None,
    }
}

/// Push an ADT value's VALUE form (no `:Type` prefix) as role spans (spec §1.5).
///
/// Nullary constructors display as `Type.Ctor` (`Color.Red`); data constructors
/// as `(Type.Ctor field1 field2)` (`(Option.Some 42)`); single-constructor
/// product types where the ctor name matches the type name suppress the `Type.`
/// prefix (`(Point 3 4)`). The ctor dot-name and structural punctuation are R15
/// `Plain`; scalar field literals recurse to R2/R3 via `push_field_value`. This
/// is the ONE value-only ADT renderer — used by both the top-level result value
/// and by nested ADT fields.
fn push_adt_value_form<C, L>(
    value: i64,
    fqtn: &FQTypeName,
    type_args: &[Type],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    doc: &mut StyledDoc,
) where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let type_name_str = fqtn.name.as_ref();

    // Vec is a built-in type, not in type_defs -- handle it specially.
    if type_name_str == "Vec" {
        push_vec_elements(value, type_args.first(), symbol_tables, doc);
        return;
    }

    let Some(type_info) = lookup_type_def_from_tables(fqtn, symbol_tables) else {
        // No type def available -- fallback to bare value display.
        doc.plain(value.to_string());
        return;
    };

    // R5 value-layout (Wave-3a): a flattened single-ctor single-value-field ADT
    // stores the field value INLINE — the runtime word is neither a nullary tag
    // nor a heap pointer. Recognise it before the tag/heap branching below, else
    // the flat word is misread as a tag (`<tag:N>`) or, for a `Float` field,
    // dereferenced as a pointer (SIGSEGV). Spec §12.9 / repl §1.5.
    if push_value_layout_adt(value, fqtn, type_args, &type_info, symbol_tables, doc) {
        return;
    }

    // Determine if this is a nullary tag or a heap pointer.
    if (value as usize) < NULLARY_TAG_THRESHOLD {
        // Nullary constructor: value is the tag directly.
        let tag = value as usize;
        let ctor_name = find_constructor_by_tag(&type_info, tag);
        doc.plain(format_ctor_display(type_name_str, &ctor_name, &type_info));
    } else {
        // Data constructor: read tag and fields from heap.
        push_adt_heap_value(
            value,
            type_name_str,
            &type_info,
            type_args,
            symbol_tables,
            doc,
        );
    }
}

/// R5 value-layout display (spec §12.9 / repl §1.5) — value-only, span form.
///
/// A single-constructor, single-value-field ADT (`(deftype Box (Box [:Int v]))`)
/// is flattened by the Wave-3a `value_layout` optimisation: its runtime word is
/// the field's value carried INLINE — NOT a nullary tag and NOT a heap pointer.
/// Recognises the shape via the SAME `cranelisp_types::value_layout` predicate
/// the backend's `HeapCategory::Value` arm uses (single-sourced) and pushes the
/// `(Ctor field-value)` form. Returns `true` when it handled the value; `false`
/// when the type is not value-layout (the caller keeps the tag/heap path).
fn push_value_layout_adt<C, L>(
    value: i64,
    fqtn: &FQTypeName,
    type_args: &[Type],
    type_info: &TypeDefInfo,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    doc: &mut StyledDoc,
) -> bool
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    // Ask the single-sourced predicate — do NOT re-derive value-eligibility.
    let ty = Type::ADT(fqtn.clone(), type_args.to_vec());
    let Ok(concrete) = cranelisp_types::ConcreteType::from_type(&ty) else {
        return false;
    };
    if cranelisp_types::value_layout(&concrete, Some(symbol_tables)).is_none() {
        return false;
    }

    // `value_layout` guarantees exactly one constructor with exactly one
    // value-eligible field; the flattened `value` IS that field's value.
    let Some(ctor_name) = type_info.constructors.first().map(|c| c.to_string()) else {
        return false;
    };
    let field_types = ctor_field_types(fqtn, &ctor_name, symbol_tables);
    let Some(field_ty) = field_types.first() else {
        return false;
    };
    let subst = build_adt_subst(type_info, type_args, symbol_tables);
    let field_ty = substitute_field_type(field_ty, &subst);
    let ctor_display = format_ctor_display(fqtn.name.as_ref(), &ctor_name, type_info);
    doc.plain(format!("({ctor_display} "));
    push_field_value(value, &field_ty, symbol_tables, doc);
    doc.plain(")");
    true
}

/// Format the type portion of an ADT display with qualification (spec §1.4).
/// Simple types: `user/Color`. Parameterized: `(user/Option primitives/Int)`.
pub fn format_adt_type_qualified(fqtn: &FQTypeName, type_args: &[Type]) -> String {
    let qname = format!("{}/{}", fqtn.module, fqtn.name);
    if type_args.is_empty() {
        qname
    } else {
        let arg_strs: Vec<String> = type_args.iter().map(format_type_qualified).collect();
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
    // Probe the canonical `member_key(Type, Ctor)` key FIRST (S109 W1 — a sum
    // ctor's real `Def` lives under `Maybe.Some`, the bare name being a poison-able
    // `Import` alias that carries no `scheme`), falling back to the bare key for
    // the product dual-facet (kept at the type-name key) and for pre-flip bare
    // keying (commit 1 — behaviour-invariant, the canonical key does not yet
    // exist so the bare fallback serves). Without the canonical probe a data ctor
    // renders with its fields dropped (`(Cons 2 …)` → `Lst.Cons`).
    let canonical = cranelisp_types::member_key(&fqtn.name, ctor_name);
    let scheme_ty = match table
        .get(canonical.as_ref())
        .or_else(|| table.get(ctor_name))
    {
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
fn push_adt_heap_value<C, L>(
    value: i64,
    type_name: &str,
    type_info: &TypeDefInfo,
    type_args: &[Type],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    doc: &mut StyledDoc,
) where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    // SAFETY: value is a heap pointer to a valid HeapAdt (produced by JIT code).
    let base = value as *const u8;
    let tag = unsafe { *(base.add(HeapAdt::TAG_OFFSET as usize) as *const i64) } as usize;

    // S70: tag is the index into `constructors: Vec<Symbol>`; field types come
    // from the ctor Def's scheme.
    let Some(ctor_name) = type_info.constructors.get(tag).map(|s| s.to_string()) else {
        doc.plain(format!("<unknown-tag:{tag}>"));
        return;
    };
    let fqtn = &type_info.name;
    let field_types = ctor_field_types(fqtn, &ctor_name, symbol_tables);

    if field_types.is_empty() {
        // Nullary constructor stored on heap (shouldn't happen, but handle gracefully).
        doc.plain(format_ctor_display(type_name, &ctor_name, type_info));
        return;
    }

    // Build substitution from type_params to type_args for polymorphic ADTs.
    let subst = build_adt_subst(type_info, type_args, symbol_tables);

    // `(Ctor field1 field2)` — the ctor dot-name and punctuation are R15 Plain;
    // scalar field literals recurse to R2/R3.
    doc.plain("(");
    doc.plain(format_ctor_display(type_name, &ctor_name, type_info));
    for (i, field_ty) in field_types.iter().enumerate() {
        let field_offset = HeapAdt::field_offset(i) as usize;
        let field_val = unsafe { *(base.add(field_offset) as *const i64) };
        // Substitute type args into field type before formatting.
        let field_ty = substitute_field_type(field_ty, &subst);
        doc.plain(" ");
        push_field_value(field_val, &field_ty, symbol_tables, doc);
    }
    doc.plain(")");
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

/// Substitute type variables in a field type using the given substitution.
fn substitute_field_type(ty: &Type, subst: &HashMap<TypeId, Type>) -> Type {
    cranelisp_types::apply(subst, ty)
}

/// Format Vec elements by reading the heap layout.
///
/// HeapVec layout: `[alloc_size(+0) | rc(+8) | len(+16) | cap(+24) | data_ptr(+32)]`
/// Elements are stored in the data buffer at `data_ptr`, each 8 bytes (i64).
fn push_vec_elements<C, L>(
    value: i64,
    elem_type: Option<&Type>,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    doc: &mut StyledDoc,
) where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    if value == 0 || (value as usize) < NULLARY_TAG_THRESHOLD {
        doc.plain("[]");
        return;
    }

    let base = value as *const u8;
    // SAFETY: value is a heap pointer to a valid HeapVec (produced by JIT code).
    let len = unsafe { *(base.add(HeapVec::LEN_OFFSET as usize) as *const i64) } as usize;
    if len == 0 {
        doc.plain("[]");
        return;
    }

    let data_ptr = unsafe { *(base.add(HeapVec::DATA_PTR_OFFSET as usize) as *const *const i64) };
    if data_ptr.is_null() {
        doc.plain("[]");
        return;
    }

    doc.plain("[");
    for i in 0..len {
        if i > 0 {
            doc.plain(" ");
        }
        let elem_val = unsafe { *data_ptr.add(i) };
        match elem_type {
            Some(ty) => push_field_value(elem_val, ty, symbol_tables, doc),
            None => doc.plain(format!("{elem_val}")),
        }
    }
    doc.plain("]");
}

/// `#[cfg(test)]`/legacy plain-text field renderer — the `.text()` of
/// `push_field_value`. `format_field_value` is exercised by this module's unit
/// tests; the production path builds spans via `push_field_value`.
#[cfg(test)]
fn format_field_value<C, L>(
    value: i64,
    ty: &Type,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
) -> String
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let mut doc = StyledDoc::new();
    push_field_value(value, ty, symbol_tables, &mut doc);
    doc.text()
}

/// Push a single field value's VALUE spans based on its type (spec §1.5).
///
/// Scalars carry their literal role (R2 num/bool, R3 string); ADT ctor
/// dot-names, `<closure>`, and structural punctuation are R15 `Plain`. Field
/// values use `Type.Constructor` dot notation for ADT constructors.
fn push_field_value<C, L>(
    value: i64,
    ty: &Type,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    doc: &mut StyledDoc,
) where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    match ty {
        Type::Int => doc.push(Role::LitNumBool, format!("{value}")),
        Type::Bool => {
            doc.push(Role::LitNumBool, if value != 0 { "true" } else { "false" });
        }
        Type::Float => {
            let f = f64::from_bits(value as u64);
            let s = format!("{f}");
            let s = if s.contains('.') { s } else { format!("{s}.0") };
            doc.push(Role::LitNumBool, s);
        }
        Type::String => {
            if value == 0 || (value as usize) < NULLARY_TAG_THRESHOLD {
                doc.plain(format!("<invalid-string:{value}>"));
            } else {
                // SAFETY: value is a heap pointer to a valid HeapString (produced by JIT code);
                // the guard above rejects null and small (nullary tag) values.
                let s = unsafe { cranelisp_intrinsics::heap_string::read_string_as_str(value) };
                doc.push(Role::LitStr, format!("\"{s}\""));
            }
        }
        Type::Fn(_, _) => doc.plain("<closure>"),
        Type::ADT(fqtn, args) => {
            // The value-only ADT renderer handles Vec / value-layout / nullary /
            // heap uniformly (single-sourced with the top-level result value).
            push_adt_value_form(value, fqtn, args, symbol_tables, doc);
        }
        _ => doc.plain(format!("{value}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::FQTraitName;

    // === §10.3 colour-ON byte-exact fixtures (Wave-D /dev obligation) =========
    // The `ColorGuard` forces the process-global colour gate ON (nextest gives
    // each test its own process, so the force is race-free); the fixtures pin the
    // exact SGR spans at the exact offsets (§10.3 requirement 3 determinism).

    use crate::style::test_support::ColorGuard;

    // K1 — result value (num): `(+ 1 2)` → `:primitives/Int 3`. R4 cyan type
    // annotation as a single construct + R2 yellow literal; the space is R15.
    // spec: repl/spec.md §10.3 R4/R2 (result-value colouring, NEW in Wave D).
    #[test]
    fn colour_on_k1_result_value_int() {
        let _g = ColorGuard::force(true);
        let empty: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let out = format_result_value(3, &Type::Int, &empty);
        assert_eq!(out, "\x1b[36m:primitives/Int\x1b[0m \x1b[33m3\x1b[0m");
    }

    // K2 — a STRING result value: the `:primitives/String` annotation is R4 cyan,
    // the quoted literal `"hi"` is R3 green (§10.3 R3-in-value composition). The
    // heap string is a real allocation so the producer's `read_string_as_str` path
    // is exercised. Fail-on-revert pin for the string-value role composition.
    // spec: repl/spec.md §10.3 R4/R3 — string result value.
    #[test]
    fn colour_on_k2_result_value_string_green() {
        let _g = ColorGuard::force(true);
        let empty: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        // A real heap string (base pointer > NULLARY_TAG_THRESHOLD).
        let ptr = cranelisp_intrinsics::heap_string::alloc_string(b"hi") as i64;
        let out = format_result_value(ptr, &Type::String, &empty);
        assert_eq!(
            out,
            "\x1b[36m:primitives/String\x1b[0m \x1b[32m\"hi\"\x1b[0m"
        );
    }

    // K1 sibling — Bool literal is R2 yellow too.
    // spec: repl/spec.md §10.3 R2 — bool literal in value display.
    #[test]
    fn colour_on_k1_result_value_bool() {
        let _g = ColorGuard::force(true);
        let empty: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let out = format_result_value(1, &Type::Bool, &empty);
        assert_eq!(out, "\x1b[36m:primitives/Bool\x1b[0m \x1b[33mtrue\x1b[0m");
    }

    // Colour-OFF invariant: the SAME producer emits exactly the plain text (the
    // non-TTY golden contract, §10.3 requirement 2).
    // spec: repl/spec.md §10.3 requirement 2.
    #[test]
    fn colour_off_k1_result_value_is_plain() {
        let _g = ColorGuard::force(false);
        let empty: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        assert_eq!(
            format_result_value(3, &Type::Int, &empty),
            ":primitives/Int 3"
        );
    }

    // K3 primary-line building block — `:(Fn …) module/name` is R4 (whole type)
    // + Plain space + R7 (dim `module/`) + R15 (name). The introspection primary
    // line (`format_def_entry`, `/sig`, bare lookup) is built on this doc.
    // spec: repl/spec.md §10.3 R4/R7/R15 (introspection primary line).
    #[test]
    fn colour_on_k3_scheme_display_module_prefix_dim() {
        let _g = ColorGuard::force(true);
        let scheme = Scheme {
            type_vars: Vec::new(),
            constraints: HashMap::new(),
            ty: Type::Fn(vec![Type::Int], Box::new(Type::Int)),
        };
        let module = ModuleFullPath::from("user");
        let out = render(&format_scheme_display_doc("double", &scheme, &module));
        assert_eq!(
            out,
            "\x1b[36m:(Fn [primitives/Int] primitives/Int)\x1b[0m \x1b[2muser/\x1b[0mdouble"
        );
    }

    // --- nested-ADT value rendering (FIXME 0493 — nested parameterized ADT) ---
    //
    // The FIXME-0493 garbling class (a nested PARAMETERIZED ADT's `:type value`
    // string split at the first space, landing INSIDE the type) is now
    // structurally impossible: `push_field_value`/`push_adt_value_form` build the
    // VALUE form directly (no `:Type` prefix on nested fields, so nothing to
    // strip). The end-to-end guard is
    // `display_exact::display_exact_nested_parameterized_adt_wrap_in_wrap`.

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
        assert_eq!(
            find_constructor_by_tag(&type_info("Empty", &[]), 0),
            "<tag:0>"
        );
    }

    // spec: repl/spec.md §1.5 — single-ctor product (ctor name == type name)
    // is the prefix-suppression trigger.
    #[test]
    fn is_single_matching_constructor_product_true() {
        assert!(is_single_matching_constructor(
            "Point",
            &type_info("Point", &["Point"])
        ));
    }

    // spec: repl/spec.md §1.5 — a multi-ctor type is NOT prefix-suppressed
    // (negative), nor is a lone ctor whose name differs from the type.
    #[test]
    fn is_single_matching_constructor_negatives() {
        // two ctors → not a product
        assert!(!is_single_matching_constructor(
            "Color",
            &type_info("Color", &["Red", "Green"])
        ));
        // single ctor but name differs from the type
        assert!(!is_single_matching_constructor(
            "Wrap",
            &type_info("Wrap", &["MkWrap"])
        ));
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
        assert!(
            v.contains('.'),
            "float display should contain a decimal point: {v}"
        );
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
        // The stored `core.num/Num` identity is rendered unchanged on both
        // occurrences; display performs no bare-name re-resolution.
        let var_id = 100;
        let scheme = Scheme {
            type_vars: vec![var_id],
            constraints: HashMap::from([(
                var_id,
                vec![FQTraitName::new(
                    ModuleFullPath::from("core.num"),
                    "Num".into(),
                )],
            )]),
            ty: Type::Fn(
                vec![Type::Var(var_id), Type::Var(var_id)],
                Box::new(Type::Var(var_id)),
            ),
        };
        let module = ModuleFullPath::from("user");
        let s = format_scheme_display("add", &scheme, &module);
        assert_eq!(s, ":(Fn [:core.num/Num a :core.num/Num a] a) user/add");
    }

    // spec: spec/03-types.md §3.5.1 — multiple constraints repeated on every occurrence
    #[test]
    fn format_scheme_display_repeats_multiple_constraints() {
        // Multiple canonical identities sort by their fully-qualified text.
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
        assert_eq!(
            s,
            ":(Fn [:core.eq/Eq :core.num/Num a :core.eq/Eq :core.num/Num a] a) user/bar"
        );
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
            ModuleEntry::def(
                ctor_scheme,
                DefKind::Constructor {
                    got_slot: 0,
                    type_name: point_fqtn(),
                    tag: 0,
                    field_count: 2,
                    internal: false,
                    type_def: Some(Box::new(info)),
                    mode_summary: None,
                },
            )
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
            ty: Type::Fn(
                vec![Type::Float],
                Box::new(Type::ADT(fqtn.clone(), Vec::new())),
            ),
        };
        table.insert(
            Symbol::from("Circle"),
            ModuleEntry::def(
                ctor_scheme,
                DefKind::Constructor {
                    got_slot: 0,
                    type_name: fqtn.clone(),
                    tag: 0,
                    field_count: 1,
                    internal: false,
                    type_def: None,
                    mode_summary: None,
                },
            )
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
            ty: Type::Fn(
                vec![field_ty],
                Box::new(Type::ADT(fqtn.clone(), Vec::new())),
            ),
        };
        table.insert(
            Symbol::from(name),
            ModuleEntry::def(
                ctor_scheme,
                DefKind::Constructor {
                    got_slot: 0,
                    type_name: fqtn.clone(),
                    tag: 0,
                    field_count: 1,
                    internal: false,
                    type_def: Some(Box::new(info)),
                    mode_summary: None,
                },
            )
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
