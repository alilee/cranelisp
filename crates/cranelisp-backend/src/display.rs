// Canonical value display format (spec §12.9).
//
// Extracted from the binary crate so that both the REPL and the trace runtime
// can share the same formatting logic. Depends on cranelisp-types for type
// definitions and cranelisp-runtime for heap layout constants and string access.

use std::collections::HashMap;

use cranelisp_types::{
    ModuleFullPath, Scheme, Type, TypeDefInfo, TypeId, TypeName, NULLARY_TAG_THRESHOLD,
};

use crate::heap::{HeapAdt, HeapVec};

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
pub fn format_value(
    value: i64,
    ty: &Type,
    type_defs: &HashMap<TypeName, TypeDefInfo>,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
) -> String {
    format_field_value(value, ty, type_defs, type_modules)
}

/// Format a runtime value with `:Type value` prefix for REPL display.
///
/// Combines qualified type formatting with value formatting.
/// This is the top-level entry point for REPL result display.
pub fn format_result_value(
    value: i64,
    ty: &Type,
    type_defs: &HashMap<TypeName, TypeDefInfo>,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
) -> String {
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
            let type_str = format_type_qualified(ty, type_modules);
            format!(":{type_str} <closure>")
        }
        Type::ADT(type_name, type_args) => {
            format_adt_value(value, type_name, type_args, type_defs, type_modules)
        }
        other => {
            let type_str = format_type_qualified(other, type_modules);
            format!(":{type_str} {value}")
        }
    }
}

/// Convenience wrapper: format_result_value with empty type_defs/type_modules.
pub fn format_result(value: i64, ty: &Type) -> String {
    format_result_value(value, ty, &HashMap::new(), &HashMap::new())
}

/// Format a type with fully-qualified names for REPL display (spec §1.4).
///
/// Primitive types get `primitives/` prefix, ADT types get their module prefix,
/// `Fn` keyword and type variables stay unqualified.
pub fn format_type_qualified(
    ty: &Type,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
) -> String {
    // Compute var names from the full type, then use them in the recursive helper.
    let var_names = cranelisp_types::type_var_names(ty);
    format_type_qualified_inner(ty, type_modules, &var_names)
}

/// Format a constrained function's scheme for REPL display (spec §1.3).
///
/// Produces inline-constraint notation:
///   `:(Fn [:Num a :a] a) user/double`
///
/// On first occurrence of a constrained type variable, the constraint trait
/// is shown as `:TraitName var`. Subsequent occurrences use `:var`.
/// Unconstrained variables appear bare.
pub fn format_scheme_display(
    name: &str,
    scheme: &Scheme,
    module: &ModuleFullPath,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
) -> String {
    let var_names = cranelisp_types::type_var_names(&scheme.ty);

    // Build a map from TypeId to the constraint traits for quick lookup.
    // Use sorted trait names for deterministic output.
    let mut constraint_map: HashMap<TypeId, Vec<&str>> = HashMap::new();
    for (type_id, traits) in &scheme.constraints {
        let mut trait_strs: Vec<&str> = traits.iter().map(|t| t.as_ref()).collect();
        trait_strs.sort();
        constraint_map.insert(*type_id, trait_strs);
    }

    // Track which constrained vars have been "introduced" (first occurrence shown).
    let mut introduced: std::collections::HashSet<TypeId> = std::collections::HashSet::new();

    let type_str = format_type_with_inline_constraints(
        &scheme.ty,
        &var_names,
        &constraint_map,
        &mut introduced,
        false,
        type_modules,
    );

    format!(":{type_str} {module}/{name}")
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Qualify a type name using the type_modules map.
fn qualify_type_name(
    name: &str,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
) -> String {
    if let Some(module) = type_modules.get(name) {
        format!("{module}/{name}")
    } else {
        // Not in type_modules — unqualified (e.g., type vars, unknown types).
        name.to_string()
    }
}

/// Recursive helper for `format_type_qualified` with pre-computed var names.
fn format_type_qualified_inner(
    ty: &Type,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
    var_names: &HashMap<TypeId, String>,
) -> String {
    match ty {
        Type::Int => "primitives/Int".to_string(),
        Type::Bool => "primitives/Bool".to_string(),
        Type::String => "primitives/String".to_string(),
        Type::Float => "primitives/Float".to_string(),
        Type::Fn(params, ret) => {
            let parts: Vec<String> = params
                .iter()
                .map(|p| format_type_qualified_inner(p, type_modules, var_names))
                .collect();
            let ret_s = format_type_qualified_inner(ret, type_modules, var_names);
            format!("(Fn [{}] {ret_s})", parts.join(" "))
        }
        Type::ADT(name, args) => {
            let qname = qualify_type_name(name, type_modules);
            if args.is_empty() {
                qname
            } else {
                let arg_strs: Vec<String> = args
                    .iter()
                    .map(|a| format_type_qualified_inner(a, type_modules, var_names))
                    .collect();
                format!("({qname} {})", arg_strs.join(" "))
            }
        }
        Type::Var(id) => {
            var_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("t{id}"))
        }
        Type::TyConApp(id, args) => {
            let name = var_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("t{id}"));
            if args.is_empty() {
                name
            } else {
                let arg_strs: Vec<String> = args
                    .iter()
                    .map(|a| format_type_qualified_inner(a, type_modules, var_names))
                    .collect();
                format!("({name} {})", arg_strs.join(" "))
            }
        }
    }
}

/// Format a type with inline constraint annotations (spec §1.3, §1.4).
///
/// Type names are fully qualified. Inside function param lists (`in_params = true`):
///   first occurrence of constrained var: `:TraitName var`
///   subsequent occurrences: `:var`
/// Outside param lists (return type, ADT args): vars are always bare.
fn format_type_with_inline_constraints(
    ty: &Type,
    var_names: &HashMap<TypeId, String>,
    constraints: &HashMap<TypeId, Vec<&str>>,
    introduced: &mut std::collections::HashSet<TypeId>,
    in_params: bool,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
) -> String {
    match ty {
        Type::Int => "primitives/Int".to_string(),
        Type::Bool => "primitives/Bool".to_string(),
        Type::String => "primitives/String".to_string(),
        Type::Float => "primitives/Float".to_string(),
        Type::Fn(params, ret) => {
            let parts: Vec<String> = params
                .iter()
                .map(|p| {
                    format_type_with_inline_constraints(
                        p, var_names, constraints, introduced, true, type_modules,
                    )
                })
                .collect();
            let ret_s = format_type_with_inline_constraints(
                ret, var_names, constraints, introduced, false, type_modules,
            );
            format!("(Fn [{}] {ret_s})", parts.join(" "))
        }
        Type::ADT(name, args) => {
            let qname = qualify_type_name(name, type_modules);
            if args.is_empty() {
                qname
            } else {
                let arg_strs: Vec<String> = args
                    .iter()
                    .map(|a| {
                        format_type_with_inline_constraints(
                            a, var_names, constraints, introduced, false, type_modules,
                        )
                    })
                    .collect();
                format!("({qname} {})", arg_strs.join(" "))
            }
        }
        Type::Var(id) => {
            let var_name = var_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("t{id}"));
            if in_params {
                if let Some(traits) = constraints.get(id) {
                    if !introduced.contains(id) {
                        // First occurrence in params: show `:TraitName var`
                        introduced.insert(*id);
                        let trait_prefix = traits.join(" ");
                        format!(":{trait_prefix} {var_name}")
                    } else {
                        // Subsequent occurrence in params: show `:var`
                        format!(":{var_name}")
                    }
                } else {
                    // Unconstrained var in params: bare name
                    var_name
                }
            } else {
                // Outside params (return type, etc.): always bare
                var_name
            }
        }
        Type::TyConApp(id, args) => {
            let name = var_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("t{id}"));
            if args.is_empty() {
                name
            } else {
                let arg_strs: Vec<String> = args
                    .iter()
                    .map(|a| {
                        format_type_with_inline_constraints(
                            a, var_names, constraints, introduced, false, type_modules,
                        )
                    })
                    .collect();
                format!("({name} {})", arg_strs.join(" "))
            }
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
    let s = unsafe { cranelisp_runtime::read_string_as_str(value) };
    format!(":primitives/String \"{s}\"")
}

/// Check whether a type has exactly one constructor whose name matches the type name.
///
/// Single-constructor product types like `(deftype Point [:Int x :Int y])` have
/// a redundant `Type.Constructor` display (`Point.Point`). For these types we
/// suppress the `Type.` prefix and show just the constructor name.
fn is_single_matching_constructor(type_name: &TypeName, type_info: &TypeDefInfo) -> bool {
    type_info.constructors.len() == 1 && type_info.constructors[0].name.0 == type_name.0
}

/// Format the constructor display name for an ADT value.
///
/// For single-constructor types where the constructor name matches the type name,
/// returns just the constructor name (e.g., `Point`). For multi-constructor types,
/// returns `Type.Constructor` (e.g., `Color.Red`, `Option.Some`).
pub fn format_ctor_display(
    type_name: &TypeName,
    ctor_name: &str,
    type_info: &TypeDefInfo,
) -> String {
    if is_single_matching_constructor(type_name, type_info) {
        ctor_name.to_string()
    } else {
        format!("{type_name}.{ctor_name}")
    }
}

/// Format an ADT value with constructor name lookup and dot notation (spec §1.5).
///
/// Nullary constructors display as `Type.Ctor` (e.g., `Color.Red`).
/// Data constructors display as `(Type.Ctor field1 field2)` (e.g., `(Option.Some 42)`).
/// Single-constructor product types where the constructor name matches the type name
/// suppress the `Type.` prefix (e.g., `(Point 3 4)` not `(Point.Point 3 4)`).
/// Type names in the `:Type` prefix are fully qualified.
fn format_adt_value(
    value: i64,
    type_name: &TypeName,
    type_args: &[Type],
    type_defs: &HashMap<TypeName, TypeDefInfo>,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
) -> String {
    let type_display = format_adt_type_qualified(type_name, type_args, type_modules);

    // Vec is a built-in type, not in type_defs -- handle it specially.
    if type_name == "Vec" {
        let elem_type = type_args.first();
        let elems = format_vec_elements(value, elem_type, type_defs, type_modules);
        return format!(":{type_display} {elems}");
    }

    let Some(type_info) = type_defs.get(type_name) else {
        // No type def available -- fallback to bare value display.
        return format!(":{type_display} {value}");
    };

    // Determine if this is a nullary tag or a heap pointer.
    if (value as usize) < NULLARY_TAG_THRESHOLD {
        // Nullary constructor: value is the tag directly.
        let tag = value as usize;
        let ctor_name = find_constructor_by_tag(type_info, tag);
        let ctor_display = format_ctor_display(type_name, &ctor_name, type_info);
        format!(":{type_display} {ctor_display}")
    } else {
        // Data constructor: read tag and fields from heap.
        format_adt_heap_value(value, &type_display, type_name, type_info, type_args, type_defs, type_modules)
    }
}

/// Format the type portion of an ADT display with qualification (spec §1.4).
/// Simple types: `user/Color`. Parameterized: `(user/Option primitives/Int)`.
pub fn format_adt_type_qualified(
    type_name: &TypeName,
    type_args: &[Type],
    type_modules: &HashMap<TypeName, ModuleFullPath>,
) -> String {
    let qname = qualify_type_name(type_name, type_modules);
    if type_args.is_empty() {
        qname
    } else {
        let arg_strs: Vec<String> = type_args
            .iter()
            .map(|a| format_type_qualified(a, type_modules))
            .collect();
        format!("({qname} {})", arg_strs.join(" "))
    }
}

/// Find a constructor name by tag, or return a fallback string.
fn find_constructor_by_tag(type_info: &TypeDefInfo, tag: usize) -> String {
    type_info
        .constructors
        .iter()
        .find(|c| c.tag == tag)
        .map(|c| format!("{}", c.name))
        .unwrap_or_else(|| format!("<tag:{tag}>"))
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
fn format_adt_heap_value(
    value: i64,
    type_display: &str,
    type_name: &TypeName,
    type_info: &TypeDefInfo,
    type_args: &[Type],
    type_defs: &HashMap<TypeName, TypeDefInfo>,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
) -> String {
    // SAFETY: value is a heap pointer to a valid HeapAdt (produced by JIT code).
    let base = value as *const u8;
    let tag = unsafe { *(base.add(HeapAdt::TAG_OFFSET as usize) as *const i64) } as usize;
    let ctor = type_info.constructors.iter().find(|c| c.tag == tag);

    let Some(ctor) = ctor else {
        return format!(":{type_display} <unknown-tag:{tag}>");
    };

    if ctor.fields.is_empty() {
        // Nullary constructor stored on heap (shouldn't happen, but handle gracefully).
        let ctor_display = format_ctor_display(type_name, &ctor.name, type_info);
        return format!(":{type_display} {ctor_display}");
    }

    // Build substitution from type_params to type_args for polymorphic ADTs.
    let subst = build_adt_subst(type_info, type_args);

    // Read and format each field.
    let mut field_strs = Vec::new();
    for (i, field_info) in ctor.fields.iter().enumerate() {
        let field_offset = HeapAdt::field_offset(i) as usize;
        let field_val = unsafe { *(base.add(field_offset) as *const i64) };
        // Substitute type args into field type before formatting.
        let field_ty = substitute_field_type(&field_info.ty, &subst);
        let field_str = format_field_value(field_val, &field_ty, type_defs, type_modules);
        field_strs.push(field_str);
    }

    let fields_display = field_strs.join(" ");
    let ctor_display = format_ctor_display(type_name, &ctor.name, type_info);
    format!(":{type_display} ({ctor_display} {fields_display})")
}

/// Build a type substitution from a TypeDefInfo's type_params and concrete type_args.
///
/// The type_params are Symbol names (e.g., "a", "b") but the field types use
/// Type::Var(TypeId). We need to map from the Var ids used in field types
/// to the concrete types in type_args.
fn build_adt_subst(
    type_info: &TypeDefInfo,
    type_args: &[Type],
) -> HashMap<TypeId, Type> {
    let mut subst = HashMap::new();
    // Collect all Var ids used in constructor fields, in order.
    let mut var_ids = Vec::new();
    for ctor in &type_info.constructors {
        for field in &ctor.fields {
            collect_var_ids(&field.ty, &mut var_ids);
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
fn format_vec_elements(
    value: i64,
    elem_type: Option<&Type>,
    type_defs: &HashMap<TypeName, TypeDefInfo>,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
) -> String {
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
            Some(ty) => format_field_value(elem_val, ty, type_defs, type_modules),
            None => format!("{elem_val}"),
        };
        elems.push(formatted);
    }

    format!("[{}]", elems.join(" "))
}

/// Format a single field value based on its type.
///
/// Field values use `Type.Constructor` dot notation for ADT constructors (spec §1.5).
fn format_field_value(
    value: i64,
    ty: &Type,
    type_defs: &HashMap<TypeName, TypeDefInfo>,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
) -> String {
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
                let s = unsafe { cranelisp_runtime::read_string_as_str(value) };
                format!("\"{s}\"")
            }
        }
        Type::Fn(_, _) => "<closure>".to_string(),
        Type::ADT(name, args) => {
            // Vec is built-in, not in type_defs.
            if name == "Vec" {
                return format_vec_elements(value, args.first(), type_defs, type_modules);
            }
            // Recursive ADT formatting with dot notation.
            let type_display = format_adt_type_qualified(name, args, type_modules);
            if let Some(info) = type_defs.get(name) {
                if (value as usize) < NULLARY_TAG_THRESHOLD {
                    let tag = value as usize;
                    let ctor_name = find_constructor_by_tag(info, tag);
                    format_ctor_display(name, &ctor_name, info)
                } else {
                    // Recursive heap ADT -- format with parens and dot notation.
                    let inner = format_adt_heap_value(
                        value, &type_display, name, info, args, type_defs, type_modules,
                    );
                    // Strip the leading `:Type ` prefix from the recursive call.
                    inner.split_once(' ').map_or_else(
                        || inner.clone(),
                        |(_, rest)| rest.to_string(),
                    )
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

    // --- format_value: scalar types ---

    #[test]
    fn format_value_int_positive() {
        let v = format_value(42, &Type::Int, &HashMap::new(), &HashMap::new());
        assert_eq!(v, "42");
    }

    #[test]
    fn format_value_int_negative() {
        let v = format_value(-7, &Type::Int, &HashMap::new(), &HashMap::new());
        assert_eq!(v, "-7");
    }

    #[test]
    fn format_value_int_zero() {
        let v = format_value(0, &Type::Int, &HashMap::new(), &HashMap::new());
        assert_eq!(v, "0");
    }

    #[test]
    fn format_value_bool_true() {
        let v = format_value(1, &Type::Bool, &HashMap::new(), &HashMap::new());
        assert_eq!(v, "true");
    }

    #[test]
    fn format_value_bool_false() {
        let v = format_value(0, &Type::Bool, &HashMap::new(), &HashMap::new());
        assert_eq!(v, "false");
    }

    #[test]
    fn format_value_float_with_decimal() {
        let bits = 3.14_f64.to_bits() as i64;
        let v = format_value(bits, &Type::Float, &HashMap::new(), &HashMap::new());
        assert!(v.contains('.'), "float display should contain a decimal point: {v}");
    }

    #[test]
    fn format_value_float_whole_number_gets_dot_zero() {
        let bits = 1.0_f64.to_bits() as i64;
        let v = format_value(bits, &Type::Float, &HashMap::new(), &HashMap::new());
        assert!(v.ends_with(".0"), "whole float should end with .0: {v}");
    }

    #[test]
    fn format_value_fn_displays_closure() {
        let ty = Type::Fn(vec![Type::Int], Box::new(Type::Int));
        let v = format_value(0, &ty, &HashMap::new(), &HashMap::new());
        assert_eq!(v, "<closure>");
    }

    // --- format_type_qualified: primitive types ---

    #[test]
    fn format_type_qualified_int() {
        let s = format_type_qualified(&Type::Int, &HashMap::new());
        assert_eq!(s, "primitives/Int");
    }

    #[test]
    fn format_type_qualified_bool() {
        let s = format_type_qualified(&Type::Bool, &HashMap::new());
        assert_eq!(s, "primitives/Bool");
    }

    #[test]
    fn format_type_qualified_string() {
        let s = format_type_qualified(&Type::String, &HashMap::new());
        assert_eq!(s, "primitives/String");
    }

    #[test]
    fn format_type_qualified_float() {
        let s = format_type_qualified(&Type::Float, &HashMap::new());
        assert_eq!(s, "primitives/Float");
    }

    #[test]
    fn format_type_qualified_fn() {
        let ty = Type::Fn(vec![Type::Int, Type::Bool], Box::new(Type::String));
        let s = format_type_qualified(&ty, &HashMap::new());
        assert_eq!(s, "(Fn [primitives/Int primitives/Bool] primitives/String)");
    }

    // --- format_result_value: `:Type value` prefix ---

    #[test]
    fn format_result_value_int() {
        let s = format_result_value(42, &Type::Int, &HashMap::new(), &HashMap::new());
        assert_eq!(s, ":primitives/Int 42");
    }

    #[test]
    fn format_result_value_bool_true() {
        let s = format_result_value(1, &Type::Bool, &HashMap::new(), &HashMap::new());
        assert_eq!(s, ":primitives/Bool true");
    }

    #[test]
    fn format_result_value_bool_false() {
        let s = format_result_value(0, &Type::Bool, &HashMap::new(), &HashMap::new());
        assert_eq!(s, ":primitives/Bool false");
    }

    #[test]
    fn format_result_value_float() {
        let bits = 2.5_f64.to_bits() as i64;
        let s = format_result_value(bits, &Type::Float, &HashMap::new(), &HashMap::new());
        assert_eq!(s, ":primitives/Float 2.5");
    }

    #[test]
    fn format_result_value_fn() {
        let ty = Type::Fn(vec![Type::Int], Box::new(Type::Int));
        let s = format_result_value(0, &ty, &HashMap::new(), &HashMap::new());
        assert_eq!(s, ":(Fn [primitives/Int] primitives/Int) <closure>");
    }

    // --- format_result: convenience wrapper ---

    #[test]
    fn format_result_delegates_correctly() {
        let s = format_result(99, &Type::Int);
        assert_eq!(s, ":primitives/Int 99");
    }
}
