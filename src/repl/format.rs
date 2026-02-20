use std::collections::{HashMap, HashSet};

use crate::display::{format_trait_decl, format_trait_method_type_with_params, format_type_def};
use crate::macro_expand::MacroEntry;
use crate::typechecker::{SymbolInfo, TypeChecker};
use crate::types::{Type, TypeId};

/// Collect type variable IDs in first-appearance order (left-to-right DFS).
fn collect_type_vars(ty: &Type, seen: &mut Vec<TypeId>) {
    match ty {
        Type::Var(id) => {
            if !seen.contains(id) {
                seen.push(*id);
            }
        }
        Type::Fn(params, ret) => {
            for p in params {
                collect_type_vars(p, seen);
            }
            collect_type_vars(ret, seen);
        }
        Type::ADT(_, args) => {
            for a in args {
                collect_type_vars(a, seen);
            }
        }
        Type::TyConApp(id, args) => {
            if !seen.contains(id) {
                seen.push(*id);
            }
            for a in args {
                collect_type_vars(a, seen);
            }
        }
        _ => {}
    }
}

/// Build a map from TypeId to human-readable name (a, b, c, ...).
pub fn type_var_names(ty: &Type) -> HashMap<TypeId, String> {
    let mut ids = Vec::new();
    collect_type_vars(ty, &mut ids);
    ids.into_iter()
        .enumerate()
        .map(|(i, id)| (id, String::from((b'a' + i as u8) as char)))
        .collect()
}

/// Format a type for REPL display using S-expression function syntax: `(Fn [Int Int] Int)`.
pub fn format_type(ty: &Type, var_names: &HashMap<TypeId, String>) -> String {
    match ty {
        Type::Fn(params, ret) => {
            let parts: Vec<String> = params.iter().map(|p| format_type(p, var_names)).collect();
            format!("(Fn [{}] {})", parts.join(" "), format_type(ret, var_names))
        }
        Type::Var(id) => var_names
            .get(id)
            .cloned()
            .unwrap_or_else(|| format!("t{}", id)),
        Type::ADT(name, args) => {
            if args.is_empty() {
                name.clone()
            } else {
                let parts: Vec<String> = args.iter().map(|a| format_type(a, var_names)).collect();
                format!("({} {})", name, parts.join(" "))
            }
        }
        Type::TyConApp(id, args) => {
            let name = var_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("t{}", id));
            if args.is_empty() {
                name
            } else {
                let parts: Vec<String> = args.iter().map(|a| format_type(a, var_names)).collect();
                format!("({} {})", name, parts.join(" "))
            }
        }
        other => format!("{}", other),
    }
}

/// Format a type for display, renaming type variables to a, b, c, ...
pub fn format_type_for_display(ty: &Type) -> String {
    let names = type_var_names(ty);
    format_type(ty, &names)
}

/// Qualify bare ADT names in a type tree with their module prefix for display.
pub fn qualify_type_for_display(ty: &Type, tc: &TypeChecker) -> Type {
    match ty {
        Type::ADT(name, args) => {
            let qualified = tc.qualify_adt_name(name);
            let qualified_args = args
                .iter()
                .map(|a| qualify_type_for_display(a, tc))
                .collect();
            Type::ADT(qualified, qualified_args)
        }
        Type::Fn(params, ret) => Type::Fn(
            params
                .iter()
                .map(|p| qualify_type_for_display(p, tc))
                .collect(),
            Box::new(qualify_type_for_display(ret, tc)),
        ),
        other => other.clone(),
    }
}

/// Format a type with trait constraints, using `:Trait a` notation on first appearance.
fn format_type_with_constraints(
    ty: &Type,
    var_names: &HashMap<TypeId, String>,
    constraints: &HashMap<TypeId, Vec<String>>,
    emitted: &mut HashSet<TypeId>,
) -> String {
    match ty {
        Type::Var(id) => {
            let name = var_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("t{}", id));
            if let Some(traits) = constraints.get(id) {
                if emitted.insert(*id) {
                    let prefix: Vec<String> = traits.iter().map(|t| format!(":{}", t)).collect();
                    return format!("{} {}", prefix.join(" "), name);
                }
            }
            name
        }
        Type::Fn(params, ret) => {
            let parts: Vec<String> = params
                .iter()
                .map(|p| format_type_with_constraints(p, var_names, constraints, emitted))
                .collect();
            format!(
                "(Fn [{}] {})",
                parts.join(" "),
                format_type_with_constraints(ret, var_names, constraints, emitted)
            )
        }
        Type::ADT(name, args) => {
            if args.is_empty() {
                name.clone()
            } else {
                let parts: Vec<String> = args
                    .iter()
                    .map(|a| format_type_with_constraints(a, var_names, constraints, emitted))
                    .collect();
                format!("({} {})", name, parts.join(" "))
            }
        }
        Type::TyConApp(id, args) => {
            let name = var_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("t{}", id));
            if let Some(traits) = constraints.get(id) {
                if emitted.insert(*id) {
                    let prefix: Vec<String> = traits.iter().map(|t| format!(":{}", t)).collect();
                    if args.is_empty() {
                        return format!("{} {}", prefix.join(" "), name);
                    } else {
                        let parts: Vec<String> = args
                            .iter()
                            .map(|a| {
                                format_type_with_constraints(a, var_names, constraints, emitted)
                            })
                            .collect();
                        return format!("({} {} {})", prefix.join(" "), name, parts.join(" "));
                    }
                }
            }
            if args.is_empty() {
                name
            } else {
                let parts: Vec<String> = args
                    .iter()
                    .map(|a| format_type_with_constraints(a, var_names, constraints, emitted))
                    .collect();
                format!("({} {})", name, parts.join(" "))
            }
        }
        other => format!("{}", other),
    }
}

/// Format a scheme for display with constraints.
pub fn format_scheme_for_display(scheme: &crate::types::Scheme) -> String {
    let names = type_var_names(&scheme.ty);
    if scheme.constraints.is_empty() {
        format_type(&scheme.ty, &names)
    } else {
        let mut emitted = HashSet::new();
        format_type_with_constraints(&scheme.ty, &names, &scheme.constraints, &mut emitted)
    }
}

/// Check if a name is a special form by querying the TypeChecker's symbol_meta.
pub fn is_special_form(tc: &TypeChecker, name: &str) -> bool {
    tc.get_symbol_meta(name)
        .map(|m| m.is_special_form())
        .unwrap_or(false)
}

/// Get the description string for a special form.
pub fn special_form_description(tc: &TypeChecker, name: &str) -> Option<String> {
    tc.get_symbol_meta(name)
        .and_then(|m| m.special_form_description())
        .map(|s| s.to_string())
}

/// Get the docstring for a special form.
pub fn special_form_docstring(tc: &TypeChecker, name: &str) -> Option<String> {
    tc.get_symbol_meta(name)
        .filter(|m| m.is_special_form())
        .and_then(|m| m.docstring())
        .map(|s| s.to_string())
}

/// Collect all special form names from the root module's symbol table.
pub fn special_form_names(tc: &TypeChecker) -> Vec<&str> {
    let mut names: Vec<&str> = Vec::new();
    if let Some(cm) = tc.modules.get(crate::names::ModuleFullPath::root().as_ref()) {
        for (name, entry) in &cm.symbols {
            if let crate::module::ModuleEntry::Def {
                kind: crate::module::DefKind::SpecialForm { .. },
                ..
            } = entry
            {
                names.push(&**name);
            }
        }
    }
    names.sort();
    names
}

/// Return a classification label for a SymbolInfo, used by `/info` display.
pub fn classification_label(
    info: &SymbolInfo,
    meta: Option<&crate::typechecker::SymbolMeta>,
) -> &'static str {
    // Check meta for special forms first
    if let Some(m) = meta {
        if m.is_special_form() {
            return "special form";
        }
        if m.is_inline_primitive() {
            return "inline primitive";
        }
        if let crate::typechecker::SymbolMeta::Primitive { kind, .. } = m {
            return match kind {
                crate::typechecker::PrimitiveKind::Platform => "platform primitive",
                crate::typechecker::PrimitiveKind::Extern => "extern primitive",
                _ => "primitive",
            };
        }
    }
    match info {
        SymbolInfo::Macro { .. } => "macro",
        SymbolInfo::UserFn { .. } => "function",
        SymbolInfo::ConstrainedFn { .. } => "constrained function",
        SymbolInfo::OverloadedFn { .. } => "overloaded function",
        SymbolInfo::InlinePrimitive { .. } => "inline primitive",
        SymbolInfo::ExternPrimitive { .. } => "extern primitive",
        SymbolInfo::TraitDecl(decl, _) => {
            if !decl.type_params.is_empty() {
                "trait (higher-kinded)"
            } else {
                "trait"
            }
        }
        SymbolInfo::TraitMethod { .. } => "trait function",
        SymbolInfo::UserType { .. } => "type",
        SymbolInfo::TypeName { .. } => "builtin type",
        SymbolInfo::Constructor { .. } => "constructor",
        SymbolInfo::Ambiguous { .. } => "ambiguous",
    }
}

/// Format a category for `/list` display.
/// Small categories (<7 items) appear on a single line.
/// Large categories (>=7 items) show one line per first-letter group.
pub fn format_category(label: &str, names: &[&str]) -> String {
    use std::collections::BTreeMap;

    if names.is_empty() {
        return String::new();
    }

    // Group by first character (case-insensitive)
    let mut groups: BTreeMap<char, Vec<&str>> = BTreeMap::new();
    let mut non_alpha: Vec<&str> = Vec::new();

    for name in names {
        let first = name.chars().next().unwrap_or('_');
        if first.is_alphabetic() {
            groups
                .entry(first.to_ascii_uppercase())
                .or_default()
                .push(name);
        } else {
            non_alpha.push(name);
        }
    }

    // Accumulate letter groups onto lines, breaking when adding the next
    // group would push past 6 symbols on the current line.
    let mut lines = vec![label.to_string()];
    let mut current_line: Vec<&str> = Vec::new();

    let flush = |line: &mut Vec<&str>, lines: &mut Vec<String>| {
        if !line.is_empty() {
            lines.push(format!("  {}", line.join(" ")));
            line.clear();
        }
    };

    for name in &non_alpha {
        current_line.push(name);
        if current_line.len() >= 6 {
            flush(&mut current_line, &mut lines);
        }
    }
    if !non_alpha.is_empty() {
        flush(&mut current_line, &mut lines);
    }
    for group in groups.values() {
        if !current_line.is_empty() && current_line.len() + group.len() > 6 {
            flush(&mut current_line, &mut lines);
        }
        for name in group {
            current_line.push(name);
            if current_line.len() >= 6 {
                flush(&mut current_line, &mut lines);
            }
        }
    }
    flush(&mut current_line, &mut lines);

    lines.join("\n")
}

/// Format a SymbolInfo for display: `name :: description`.
/// Used by both `:info` and bare-name expression display to avoid duplication.
pub fn format_symbol_info(name: &str, info: &SymbolInfo) -> String {
    match info {
        SymbolInfo::TraitDecl(decl, impl_types) => {
            if impl_types.is_empty() {
                format!("{} :: {}", name, format_trait_decl(decl))
            } else {
                format!(
                    "{} :: {} | impl {}",
                    name,
                    format_trait_decl(decl),
                    impl_types.join(", ")
                )
            }
        }
        SymbolInfo::TypeName { impls } => {
            if impls.is_empty() {
                format!("{} :: type", name)
            } else {
                format!("{} :: type | impl {}", name, impls.join(", "))
            }
        }
        SymbolInfo::TraitMethod {
            trait_name,
            sig,
            type_params,
        } => {
            format!(
                "{}.{} :: {}",
                trait_name,
                name,
                format_trait_method_type_with_params(sig, trait_name, type_params)
            )
        }
        SymbolInfo::InlinePrimitive { scheme } => {
            format!(
                "{} :: inline primitive: {}",
                name,
                format_scheme_for_display(scheme)
            )
        }
        SymbolInfo::ExternPrimitive { scheme } => {
            format!(
                "{} :: extern primitive: {}",
                name,
                format_scheme_for_display(scheme)
            )
        }
        SymbolInfo::ConstrainedFn { scheme } => {
            format!("{} :: {}", name, format_scheme_for_display(scheme))
        }
        SymbolInfo::OverloadedFn { schemes } => {
            let sigs: Vec<String> = schemes
                .iter()
                .map(|s| format_scheme_for_display(s))
                .collect();
            let pad = " ".repeat(name.len() + 4); // align under first sig
            format!("{} :: {}", name, sigs.join(&format!("\n{}", pad)))
        }
        SymbolInfo::Constructor { type_name, scheme } => {
            format!(
                "{}.{} :: {}",
                type_name,
                name,
                format_scheme_for_display(scheme)
            )
        }
        SymbolInfo::UserType { type_def } => {
            format!("{} :: {}", name, format_type_def(type_def))
        }
        SymbolInfo::UserFn { scheme } => {
            format!("{} :: {}", name, format_scheme_for_display(scheme))
        }
        SymbolInfo::Macro {
            name: _,
            fixed_params,
            rest_param,
            ..
        } => {
            let mut parts = Vec::new();
            for p in *fixed_params {
                parts.push(format!(":Sexp {}", p));
            }
            if let Some(rest) = rest_param {
                parts.push(format!("& :(SList Sexp) {}", rest));
            }
            format!("{} :: macro: [{}] -> Sexp", name, parts.join(" "))
        }
        SymbolInfo::Ambiguous { alternatives } => {
            if alternatives.is_empty() {
                format!("{} :: ambiguous", name)
            } else {
                format!(
                    "{} :: ambiguous — use {}",
                    name,
                    alternatives.join(" or ")
                )
            }
        }
    }
}

/// Type display for macros: "my-when :: macro: (Fn [(SList Sexp)] Sexp)"
pub fn format_macro_type(entry: &MacroEntry) -> String {
    format!("{} :: macro: (Fn [(SList Sexp)] Sexp)", entry.name)
}

/// Sig display for macros: (defmacro my-when "doc" [:Sexp cond :Sexp body] Sexp)
pub fn format_macro_defn_sig(entry: &MacroEntry) -> String {
    let doc_part = entry
        .docstring
        .as_ref()
        .map(|d| format!(" \"{}\"", d))
        .unwrap_or_default();
    let mut parts = Vec::new();
    for p in &entry.fixed_params {
        parts.push(format!(":Sexp {}", p));
    }
    if let Some(ref rest) = entry.rest_param {
        parts.push(format!("& :(SList Sexp) {}", rest));
    }
    format!(
        "(defmacro {}{} [{}] Sexp)",
        entry.name,
        doc_part,
        parts.join(" ")
    )
}

/// Format a type as a parameter annotation: `:Int`, `:a`, `:(List Int)`, `:Num` (for constrained).
pub fn format_type_as_annotation(
    ty: &Type,
    var_names: &HashMap<TypeId, String>,
    constraints: &HashMap<TypeId, Vec<String>>,
) -> String {
    match ty {
        Type::Int => ":Int".to_string(),
        Type::Bool => ":Bool".to_string(),
        Type::String => ":String".to_string(),
        Type::Float => ":Float".to_string(),
        Type::Var(id) => {
            if let Some(traits) = constraints.get(id) {
                if let Some(first) = traits.first() {
                    return format!(":{}", first);
                }
            }
            let name = var_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("t{}", id));
            format!(":{}", name)
        }
        Type::ADT(name, args) if args.is_empty() => format!(":{}", name),
        Type::ADT(name, args) => {
            let parts: Vec<String> = args.iter().map(|a| format_type(a, var_names)).collect();
            format!(":({} {})", name, parts.join(" "))
        }

        Type::Fn(params, ret) => {
            let parts: Vec<String> = params.iter().map(|p| format_type(p, var_names)).collect();
            format!(
                ":(Fn [{}] {})",
                parts.join(" "),
                format_type(ret, var_names)
            )
        }
        Type::TyConApp(id, args) => {
            let name = var_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("t{}", id));
            if args.is_empty() {
                format!(":{}", name)
            } else {
                let parts: Vec<String> = args.iter().map(|a| format_type(a, var_names)).collect();
                format!(":({} {})", name, parts.join(" "))
            }
        }
    }
}

/// Format a function signature: `(defn name "doc" [:Type param ...] RetType)`.
pub fn format_fn_sig(
    name: &str,
    scheme: &crate::types::Scheme,
    meta: Option<&crate::typechecker::SymbolMeta>,
) -> String {
    let var_names = type_var_names(&scheme.ty);
    let doc_part = meta
        .and_then(|m| m.docstring())
        .map(|d| format!(" \"{}\"", d))
        .unwrap_or_default();

    if let Type::Fn(params, ret) = &scheme.ty {
        let param_names = meta.map(|m| m.param_names()).unwrap_or(&[]);
        let parts: Vec<String> = params
            .iter()
            .enumerate()
            .map(|(i, ty)| {
                let ann = format_type_as_annotation(ty, &var_names, &scheme.constraints);
                if let Some(pname) = param_names.get(i) {
                    format!("{} {}", ann, pname)
                } else {
                    ann
                }
            })
            .collect();
        let ret_str = format_type(ret, &var_names);
        format!(
            "(defn {}{} [{}] {})",
            name,
            doc_part,
            parts.join(" "),
            ret_str
        )
    } else {
        format!(
            "(defn {}{} {})",
            name,
            doc_part,
            format_type(&scheme.ty, &var_names)
        )
    }
}

/// Format a trait declaration with docstring for `/sig`.
pub fn format_trait_sig(decl: &crate::ast::TraitDecl, impl_types: &[String]) -> String {
    let doc_part = decl
        .docstring
        .as_ref()
        .map(|d| format!(" \"{}\"", d))
        .unwrap_or_default();

    let trait_header = if decl.type_params.is_empty() {
        decl.name.clone()
    } else {
        format!("({} {})", decl.name, decl.type_params.join(" "))
    };

    let methods: Vec<String> = decl
        .methods
        .iter()
        .map(|m| {
            let method_doc = m
                .docstring
                .as_ref()
                .map(|d| format!(" \"{}\"", d))
                .unwrap_or_default();
            let params: Vec<String> = m
                .params
                .iter()
                .map(crate::display::format_type_expr_source)
                .collect();
            format!(
                "({}{} [{}] {})",
                m.name,
                method_doc,
                params.join(" "),
                crate::display::format_type_expr_source(&m.ret_type)
            )
        })
        .collect();

    let impl_part = if impl_types.is_empty() {
        String::new()
    } else {
        format!(" | impl {}", impl_types.join(", "))
    };

    if methods.len() <= 1 {
        format!(
            "(deftrait {}{} {}){}",
            trait_header,
            doc_part,
            methods.join(" "),
            impl_part
        )
    } else {
        let indent = "  ";
        let body = methods
            .iter()
            .map(|s| format!("{}{}", indent, s))
            .collect::<Vec<_>>()
            .join("\n");
        format!(
            "(deftrait {}{}\n{}){}",
            trait_header, doc_part, body, impl_part
        )
    }
}

/// Format a type definition with docstrings for `/sig`.
pub fn format_type_def_sig(td: &crate::typechecker::TypeDefInfo) -> String {
    let doc_part = td
        .docstring
        .as_ref()
        .map(|d| format!(" \"{}\"", d))
        .unwrap_or_default();

    // Build type_param → letter mapping
    let var_names: HashMap<TypeId, String> = td
        .type_params
        .iter()
        .enumerate()
        .map(|(i, &id)| (id, String::from((b'a' + i as u8) as char)))
        .collect();

    let header = if td.type_params.is_empty() {
        td.name.clone()
    } else {
        let param_names: Vec<String> = td
            .type_params
            .iter()
            .map(|id| var_names[id].clone())
            .collect();
        format!("({} {})", td.name, param_names.join(" "))
    };

    let ctor_strs: Vec<String> = td
        .constructors
        .iter()
        .map(|ctor| {
            let ctor_doc = ctor
                .docstring
                .as_ref()
                .map(|d| format!(" \"{}\"", d))
                .unwrap_or_default();

            if ctor.fields.is_empty() {
                if ctor_doc.is_empty() {
                    ctor.name.clone()
                } else {
                    format!("({}{})", ctor.name, ctor_doc)
                }
            } else if td.constructors.len() == 1 && ctor.name == td.name {
                // Product type
                let fields: Vec<String> = ctor
                    .fields
                    .iter()
                    .map(|(fname, fty)| {
                        let ann = format_field_type_sig(fty, &var_names);
                        format!("{} {}", ann, fname)
                    })
                    .collect();
                format!("[{}]", fields.join(" "))
            } else {
                let fields: Vec<String> = ctor
                    .fields
                    .iter()
                    .map(|(fname, fty)| {
                        let ann = format_field_type_sig(fty, &var_names);
                        format!("{} {}", ann, fname)
                    })
                    .collect();
                format!("({}{} [{}])", ctor.name, ctor_doc, fields.join(" "))
            }
        })
        .collect();

    if td.constructors.len() == 1 && td.constructors[0].name == td.name {
        format!("(deftype {}{} {})", header, doc_part, ctor_strs[0])
    } else {
        let indent = "  ";
        let body = ctor_strs
            .iter()
            .map(|s| format!("{}{}", indent, s))
            .collect::<Vec<_>>()
            .join("\n");
        format!("(deftype {}{}\n{})", header, doc_part, body)
    }
}

/// Format a field type as annotation syntax for deftype sig display.
fn format_field_type_sig(ty: &Type, var_names: &HashMap<TypeId, String>) -> String {
    match ty {
        Type::Var(id) => {
            let name = var_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("t{}", id));
            format!(":{}", name)
        }
        Type::Int => ":Int".to_string(),
        Type::Bool => ":Bool".to_string(),
        Type::String => ":String".to_string(),
        Type::Float => ":Float".to_string(),
        Type::ADT(name, args) if args.is_empty() => format!(":{}", name),
        Type::ADT(name, args) => {
            let parts: Vec<String> = args.iter().map(|a| format_type(a, var_names)).collect();
            format!(":({} {})", name, parts.join(" "))
        }

        Type::Fn(params, ret) => {
            let parts: Vec<String> = params.iter().map(|p| format_type(p, var_names)).collect();
            format!(
                ":(Fn [{}] {})",
                parts.join(" "),
                format_type(ret, var_names)
            )
        }
        Type::TyConApp(id, args) => {
            let name = var_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("t{}", id));
            if args.is_empty() {
                format!(":{}", name)
            } else {
                let parts: Vec<String> = args.iter().map(|a| format_type(a, var_names)).collect();
                format!(":({} {})", name, parts.join(" "))
            }
        }
    }
}

pub fn format_result_value(result: i64, ty: &Type, tc: &TypeChecker) -> String {
    if *ty == Type::Bool {
        if result != 0 {
            "true".to_string()
        } else {
            "false".to_string()
        }
    } else if *ty == Type::Float {
        let f = f64::from_bits(result as u64);
        format!("{}", f)
    } else if matches!(ty, Type::Fn(_, _)) {
        format!("<closure@0x{:x}>", result)
    } else if *ty == Type::String {
        let s = unsafe { super::util::read_cranelisp_string(result) };
        format!("\"{}\"", s)
    } else if let Type::ADT(type_name, type_args) = ty {
        if type_name == "Vec" && type_args.len() == 1 {
            format_vec_value(result, &type_args[0], tc)
        } else if type_name == "List" && type_args.len() == 1 {
            format_list_value(result, &type_args[0], tc)
        } else if type_name == "SList" && type_args.len() == 1 {
            format_slist_value(result, &type_args[0], tc)
        } else if type_name == "Seq" && type_args.len() == 1 {
            format_seq_value(result, &type_args[0], tc)
        } else {
            format_adt_value(result, type_name, tc)
        }
    } else {
        format!("{}", result)
    }
}

/// Format an ADT value for REPL display. Reads tag/fields from heap.
fn format_adt_value(result: i64, type_name: &str, tc: &TypeChecker) -> String {
    let qualified = tc.qualify_adt_name(type_name);
    let td = match tc.resolve_type_def_via_modules(&qualified) {
        Some(td) => td,
        None => return format!("<ADT@0x{:x}>", result),
    };

    // Extract module prefix for constructor qualification
    let module_prefix = qualified.rfind('/').map(|pos| &qualified[..pos]);
    let qualify_ctor = |name: &str| -> String {
        match module_prefix {
            Some(m) => format!("{}/{}", m, name),
            None => name.to_string(),
        }
    };

    // Determine which constructor this value belongs to
    // Nullary constructors: value IS the tag (small integer)
    // Data constructors: value is a heap pointer, tag at [0]
    let nullary_ctors: Vec<_> = td
        .constructors
        .iter()
        .filter(|c| c.fields.is_empty())
        .collect();

    // Check if it's a nullary constructor
    for ctor in &nullary_ctors {
        if result == ctor.tag as i64 {
            return qualify_ctor(&ctor.name);
        }
    }

    // It's a data constructor — read tag from heap
    let tag = unsafe { *(result as *const i64) } as usize;
    let ctor = match td.constructors.iter().find(|c| c.tag == tag) {
        Some(c) => c,
        None => return format!("<ADT@0x{:x}>", result),
    };

    if ctor.fields.is_empty() {
        return qualify_ctor(&ctor.name);
    }

    // Read and format fields
    let mut parts = vec![qualify_ctor(&ctor.name)];
    for (i, (_fname, fty)) in ctor.fields.iter().enumerate() {
        let offset = ((i + 1) * 8) as isize;
        let field_val = unsafe { *((result as *const u8).offset(offset) as *const i64) };
        // Resolve field type (apply current subst)
        let resolved_fty = tc.resolve(fty);
        parts.push(format_result_value(field_val, &resolved_fty, tc));
    }

    if parts.len() == 1 {
        parts[0].clone()
    } else {
        format!("({})", parts.join(" "))
    }
}

/// Format a Vec value for REPL display: `[elem1, elem2, ...]` or `[]`.
fn format_vec_value(result: i64, elem_type: &Type, tc: &TypeChecker) -> String {
    let ptr = result as *const i64;
    let len = unsafe { *ptr } as usize;
    if len == 0 {
        return "[]".to_string();
    }
    let data_ptr = unsafe { *ptr.add(2) } as *const i64;
    let resolved_elem = tc.resolve(elem_type);
    let mut parts = Vec::new();
    for i in 0..len {
        let elem_val = unsafe { *data_ptr.add(i) };
        parts.push(format_result_value(elem_val, &resolved_elem, tc));
    }
    format!("[{}]", parts.join(" "))
}

/// Format a List value for REPL display.
/// Empty list → "Nil", non-empty → "(list elem1 elem2 ...)"
fn format_list_value(result: i64, elem_type: &Type, tc: &TypeChecker) -> String {
    let mut elements = Vec::new();
    let mut current = result;
    let max_elements = 100;

    loop {
        if elements.len() >= max_elements {
            elements.push("...".to_string());
            break;
        }

        // Nil is tag 0 (bare i64, not a pointer)
        if current == 0 {
            break;
        }

        // Cons is tag 1, heap layout: [tag, head, tail]
        let tag = unsafe { *(current as *const i64) } as usize;
        if tag != 1 {
            // Unexpected tag — fallback
            elements.push(format!("<List@0x{:x}>", current));
            break;
        }

        let head = unsafe { *((current as *const u8).offset(8) as *const i64) };
        let tail = unsafe { *((current as *const u8).offset(16) as *const i64) };

        let resolved_elem = tc.resolve(elem_type);
        elements.push(format_result_value(head, &resolved_elem, tc));
        current = tail;
    }

    if elements.is_empty() {
        "Nil".to_string()
    } else {
        format!("(list {})", elements.join(" "))
    }
}

/// Format an SList value for REPL display (macro-system list type).
/// SNil → "SNil", non-empty → "(SCons elem1 (SCons elem2 SNil))"
fn format_slist_value(result: i64, elem_type: &Type, tc: &TypeChecker) -> String {
    let mut elements = Vec::new();
    let mut current = result;
    let max_elements = 100;

    loop {
        if elements.len() >= max_elements {
            elements.push("...".to_string());
            break;
        }

        // SNil is tag 0 (bare i64, not a pointer)
        if current == 0 {
            break;
        }

        // SCons is tag 1, heap layout: [tag, head, tail]
        let tag = unsafe { *(current as *const i64) } as usize;
        if tag != 1 {
            elements.push(format!("<SList@0x{:x}>", current));
            break;
        }

        let head = unsafe { *((current as *const u8).offset(8) as *const i64) };
        let tail = unsafe { *((current as *const u8).offset(16) as *const i64) };

        let resolved_elem = tc.resolve(elem_type);
        elements.push(format_result_value(head, &resolved_elem, tc));
        current = tail;
    }

    if elements.is_empty() {
        "SNil".to_string()
    } else {
        // Display as a flat list for readability
        format!("(slist {})", elements.join(" "))
    }
}

/// Format a Seq value for REPL display.
/// Forces up to 20 tail thunks. SeqNil → "(seq)", finite → "(seq 0 1 2)",
/// capped → "(seq 0 1 2 ... +more)".
fn format_seq_value(result: i64, elem_type: &Type, tc: &TypeChecker) -> String {
    let mut elements = Vec::new();
    let mut current = result;
    let max_elements = 20;

    loop {
        if elements.len() >= max_elements {
            elements.push("... +more".to_string());
            break;
        }

        // SeqNil is tag 0 (bare i64, not a pointer)
        if current == 0 {
            break;
        }

        // SeqCons is tag 1, heap layout: [tag, head, rest_thunk]
        let tag = unsafe { *(current as *const i64) } as usize;
        if tag != 1 {
            elements.push(format!("<Seq@0x{:x}>", current));
            break;
        }

        let head = unsafe { *((current as *const u8).offset(8) as *const i64) };
        let thunk_ptr = unsafe { *((current as *const u8).offset(16) as *const i64) };

        let resolved_elem = tc.resolve(elem_type);
        elements.push(format_result_value(head, &resolved_elem, tc));

        // Force the thunk: closure layout is [code_ptr, captures...]
        // Signature: extern "C" fn(env_ptr: i64) -> i64
        let code_ptr = unsafe { *(thunk_ptr as *const i64) };
        let func: extern "C" fn(i64) -> i64 = unsafe { std::mem::transmute(code_ptr) };
        current = func(thunk_ptr);
    }

    if elements.is_empty() {
        "(seq)".to_string()
    } else {
        format!("(seq {})", elements.join(" "))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{TraitDecl, TraitMethodSig, TypeExpr};
    use crate::typechecker::{ConstructorInfo, SymbolInfo, TypeDefInfo};
    use crate::types::{Scheme, Type};
    use std::collections::HashMap;

    #[test]
    fn format_type_name_with_impls() {
        let info = SymbolInfo::TypeName {
            impls: vec!["Num", "Eq"],
        };
        assert_eq!(
            format_symbol_info("Int", &info),
            "Int :: type | impl Num, Eq"
        );
    }

    #[test]
    fn format_type_name_no_impls() {
        let info = SymbolInfo::TypeName { impls: vec![] };
        assert_eq!(format_symbol_info("Vec", &info), "Vec :: type");
    }

    #[test]
    fn format_inline_primitive() {
        let scheme = Scheme::mono(Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)));
        let info = SymbolInfo::InlinePrimitive { scheme: &scheme };
        assert_eq!(
            format_symbol_info("add-i64", &info),
            "add-i64 :: inline primitive: (Fn [Int Int] Int)"
        );
    }

    #[test]
    fn format_extern_primitive() {
        let scheme = Scheme::mono(Type::Fn(vec![Type::Int], Box::new(Type::String)));
        let info = SymbolInfo::ExternPrimitive { scheme: &scheme };
        assert_eq!(
            format_symbol_info("int-to-string", &info),
            "int-to-string :: extern primitive: (Fn [Int] String)"
        );
    }

    #[test]
    fn format_user_fn() {
        let scheme = Scheme {
            vars: vec![0],
            constraints: HashMap::new(),
            ty: Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0))),
        };
        let info = SymbolInfo::UserFn { scheme: &scheme };
        assert_eq!(format_symbol_info("foo", &info), "foo :: (Fn [a] a)");
    }

    #[test]
    fn format_constrained_fn() {
        let mut constraints = HashMap::new();
        constraints.insert(0, vec!["Num".to_string()]);
        let scheme = Scheme {
            vars: vec![0],
            constraints,
            ty: Type::Fn(vec![Type::Var(0), Type::Var(0)], Box::new(Type::Var(0))),
        };
        let info = SymbolInfo::ConstrainedFn { scheme: &scheme };
        assert_eq!(format_symbol_info("add", &info), "add :: (Fn [:Num a a] a)");
    }

    #[test]
    fn format_overloaded_fn() {
        let s1 = Scheme::mono(Type::Fn(vec![Type::Int], Box::new(Type::Int)));
        let s2 = Scheme::mono(Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)));
        let info = SymbolInfo::OverloadedFn {
            schemes: vec![&s1, &s2],
        };
        let result = format_symbol_info("bar", &info);
        assert!(result.starts_with("bar :: (Fn [Int] Int)"));
        assert!(result.contains("(Fn [Int Int] Int)"));
    }

    #[test]
    fn format_constructor_nullary() {
        let scheme = Scheme {
            vars: vec![0],
            constraints: HashMap::new(),
            ty: Type::ADT("Option".to_string(), vec![Type::Var(0)]),
        };
        let info = SymbolInfo::Constructor {
            type_name: "Option",
            scheme: &scheme,
        };
        assert_eq!(
            format_symbol_info("None", &info),
            "Option.None :: (Option a)"
        );
    }

    #[test]
    fn format_constructor_data() {
        let scheme = Scheme {
            vars: vec![0],
            constraints: HashMap::new(),
            ty: Type::Fn(
                vec![Type::Var(0)],
                Box::new(Type::ADT("Option".to_string(), vec![Type::Var(0)])),
            ),
        };
        let info = SymbolInfo::Constructor {
            type_name: "Option",
            scheme: &scheme,
        };
        assert_eq!(
            format_symbol_info("Some", &info),
            "Option.Some :: (Fn [a] (Option a))"
        );
    }

    #[test]
    fn format_operator_method() {
        let sig = TraitMethodSig {
            docstring: None,
            hkt_param_index: None,
            name: "+".to_string(),
            params: vec![TypeExpr::SelfType, TypeExpr::SelfType],
            ret_type: TypeExpr::SelfType,
            span: (0, 0),
        };
        let info = SymbolInfo::TraitMethod {
            trait_name: "Num",
            sig: &sig,
            type_params: &[],
        };
        assert_eq!(format_symbol_info("+", &info), "Num.+ :: (Fn [:Num a a] a)");
    }

    #[test]
    fn format_trait_method() {
        let sig = TraitMethodSig {
            docstring: None,
            hkt_param_index: None,
            name: "show".to_string(),
            params: vec![TypeExpr::SelfType],
            ret_type: TypeExpr::Named("String".to_string()),
            span: (0, 0),
        };
        let info = SymbolInfo::TraitMethod {
            trait_name: "Display",
            sig: &sig,
            type_params: &[],
        };
        assert_eq!(
            format_symbol_info("show", &info),
            "Display.show :: (Fn [:Display a] String)"
        );
    }

    #[test]
    fn format_user_type() {
        let type_def = TypeDefInfo {
            name: "Color".to_string(),
            type_params: vec![],
            constructors: vec![
                ConstructorInfo {
                    name: "Red".to_string(),
                    tag: 0,
                    fields: vec![],
                    docstring: None,
                },
                ConstructorInfo {
                    name: "Green".to_string(),
                    tag: 1,
                    fields: vec![],
                    docstring: None,
                },
                ConstructorInfo {
                    name: "Blue".to_string(),
                    tag: 2,
                    fields: vec![],
                    docstring: None,
                },
            ],
            docstring: None,
        };
        let info = SymbolInfo::UserType {
            type_def: &type_def,
        };
        let result = format_symbol_info("Color", &info);
        assert!(result.starts_with("Color :: (deftype Color"));
        assert!(result.contains("Red"));
        assert!(result.contains("Green"));
        assert!(result.contains("Blue"));
    }

    #[test]
    fn format_trait_decl_with_impls() {
        let decl = TraitDecl {
            visibility: crate::ast::Visibility::Public,
            docstring: None,
            name: "Display".to_string(),
            type_params: vec![],
            methods: vec![TraitMethodSig {
                docstring: None,
                hkt_param_index: None,
                name: "show".to_string(),
                params: vec![TypeExpr::SelfType],
                ret_type: TypeExpr::Named("String".to_string()),
                span: (0, 0),
            }],
            span: (0, 0),
        };
        let impl_types = vec!["Int".to_string(), "Bool".to_string()];
        let info = SymbolInfo::TraitDecl(&decl, impl_types);
        let result = format_symbol_info("Display", &info);
        assert!(result.starts_with("Display :: (deftrait Display"));
        assert!(result.contains("| impl Int, Bool"));
    }
}
