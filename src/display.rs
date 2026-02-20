use std::collections::HashMap;

use crate::ast::{TraitDecl, TraitMethodSig, TypeExpr};
use crate::typechecker::TypeDefInfo;
use crate::types::{Type, TypeId};

/// Format a TypeExpr node, mapping SelfType using constraint-once rule:
/// first SelfType → `:Trait a`, subsequent → bare `a`.
/// For HKT traits, constructor params in Applied position get `:Trait f` on first use.
fn format_type_expr(
    texpr: &TypeExpr,
    trait_name: &str,
    self_var: &str,
    first_self: &mut bool,
    con_params: &[String],
    first_con: &mut Vec<bool>,
) -> String {
    match texpr {
        TypeExpr::SelfType => {
            if *first_self {
                *first_self = false;
                format!(":{} {}", trait_name, self_var)
            } else {
                self_var.to_string()
            }
        }
        TypeExpr::Named(name) => name.clone(),
        TypeExpr::FnType(params, ret) => {
            let parts: Vec<String> = params
                .iter()
                .map(|p| {
                    format_type_expr(p, trait_name, self_var, first_self, con_params, first_con)
                })
                .collect();
            format!(
                "(Fn [{}] {})",
                parts.join(" "),
                format_type_expr(ret, trait_name, self_var, first_self, con_params, first_con)
            )
        }
        TypeExpr::TypeVar(name) => name.clone(),
        TypeExpr::Applied(name, args) => {
            let parts: Vec<String> = args
                .iter()
                .map(|a| {
                    format_type_expr(a, trait_name, self_var, first_self, con_params, first_con)
                })
                .collect();
            // Check if this is an HKT constructor param on first use
            if let Some(idx) = con_params.iter().position(|p| p == name) {
                if first_con[idx] {
                    first_con[idx] = false;
                    return format!("(:{} {} {})", trait_name, name, parts.join(" "));
                }
            }
            format!("({} {})", name, parts.join(" "))
        }
    }
}

/// Format a full trait method signature as `(Fn [...] ret)`.
/// Uses constraint-once rule: `:Trait a` on first SelfType, bare `a` thereafter.
/// For HKT traits, constructor params get `:Trait f` on first Applied use.
pub fn format_trait_method_type(method_sig: &TraitMethodSig, trait_name: &str) -> String {
    format_trait_method_type_with_params(method_sig, trait_name, &[])
}

/// Format a trait method type with HKT constructor parameter names.
pub fn format_trait_method_type_with_params(
    method_sig: &TraitMethodSig,
    trait_name: &str,
    con_params: &[String],
) -> String {
    let self_var = "a";
    let mut first_self = true;
    let mut first_con = vec![true; con_params.len()];
    let parts: Vec<String> = method_sig
        .params
        .iter()
        .map(|p| {
            format_type_expr(
                p,
                trait_name,
                self_var,
                &mut first_self,
                con_params,
                &mut first_con,
            )
        })
        .collect();
    format!(
        "(Fn [{}] {})",
        parts.join(" "),
        format_type_expr(
            &method_sig.ret_type,
            trait_name,
            self_var,
            &mut first_self,
            con_params,
            &mut first_con
        )
    )
}

/// Render a TypeExpr back to source syntax (SelfType → `self`, not `:Trait a`).
pub fn format_type_expr_source(texpr: &TypeExpr) -> String {
    match texpr {
        TypeExpr::SelfType => "self".to_string(),
        TypeExpr::Named(name) => name.clone(),
        TypeExpr::FnType(params, ret) => {
            let parts: Vec<String> = params.iter().map(format_type_expr_source).collect();
            format!(
                "(Fn [{}] {})",
                parts.join(" "),
                format_type_expr_source(ret)
            )
        }
        TypeExpr::TypeVar(name) => name.clone(),
        TypeExpr::Applied(name, args) => {
            let parts: Vec<String> = args.iter().map(format_type_expr_source).collect();
            format!("({} {})", name, parts.join(" "))
        }
    }
}

/// Format a TraitDecl as source syntax.
/// Single method: `(deftrait Display (show [self] String))`
/// Multi method:
/// ```text
/// (deftrait Num
///   (+ [self self] self)
///   (- [self self] self))
/// ```
pub fn format_trait_decl(decl: &TraitDecl) -> String {
    let methods: Vec<String> = decl
        .methods
        .iter()
        .map(|m| {
            let params: Vec<String> = m.params.iter().map(format_type_expr_source).collect();
            format!(
                "({} [{}] {})",
                m.name,
                params.join(" "),
                format_type_expr_source(&m.ret_type)
            )
        })
        .collect();
    // Show type params for HKT traits: (deftrait (Functor f) ...)
    let trait_header = if decl.type_params.is_empty() {
        decl.name.clone()
    } else {
        format!("({} {})", decl.name, decl.type_params.join(" "))
    };
    if methods.len() <= 1 {
        format!("(deftrait {} {})", trait_header, methods.join(" "))
    } else {
        let indent = "  ";
        let body = methods
            .iter()
            .map(|s| format!("{}{}", indent, s))
            .collect::<Vec<_>>()
            .join("\n");
        format!("(deftrait {}\n{})", trait_header, body)
    }
}

/// Format a field type using the type_params → letter mapping, with `:` prefix for deftype syntax.
fn format_field_type(ty: &Type, var_names: &HashMap<TypeId, String>) -> String {
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
            let parts: Vec<String> = args
                .iter()
                .map(|a| format_field_type_inner(a, var_names))
                .collect();
            format!(":({} {})", name, parts.join(" "))
        }
        Type::Fn(params, ret) => {
            let parts: Vec<String> = params
                .iter()
                .map(|p| format_field_type_inner(p, var_names))
                .collect();
            format!(
                ":(Fn [{}] {})",
                parts.join(" "),
                format_field_type_inner(ret, var_names)
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
                let parts: Vec<String> = args
                    .iter()
                    .map(|a| format_field_type_inner(a, var_names))
                    .collect();
                format!(":({} {})", name, parts.join(" "))
            }
        }
    }
}

/// Format a type without the leading `:` (for nested positions).
fn format_field_type_inner(ty: &Type, var_names: &HashMap<TypeId, String>) -> String {
    match ty {
        Type::Var(id) => var_names
            .get(id)
            .cloned()
            .unwrap_or_else(|| format!("t{}", id)),
        Type::Int => "Int".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::String => "String".to_string(),
        Type::Float => "Float".to_string(),
        Type::ADT(name, args) if args.is_empty() => name.clone(),
        Type::ADT(name, args) => {
            let parts: Vec<String> = args
                .iter()
                .map(|a| format_field_type_inner(a, var_names))
                .collect();
            format!("({} {})", name, parts.join(" "))
        }
        Type::Fn(params, ret) => {
            let parts: Vec<String> = params
                .iter()
                .map(|p| format_field_type_inner(p, var_names))
                .collect();
            format!(
                "(Fn [{}] {})",
                parts.join(" "),
                format_field_type_inner(ret, var_names)
            )
        }
        Type::TyConApp(id, args) => {
            let name = var_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("t{}", id));
            if args.is_empty() {
                name
            } else {
                let parts: Vec<String> = args
                    .iter()
                    .map(|a| format_field_type_inner(a, var_names))
                    .collect();
                format!("({} {})", name, parts.join(" "))
            }
        }
    }
}

/// Format a TypeDefInfo as deftype source syntax.
///
/// Product type: `(deftype Point [:Int x :Int y])`
/// Sum type:     `(deftype (Option a)\n  None\n  (Some [:a unwrap]))`
/// Enum:         `(deftype Color Red Green Blue)`
pub fn format_type_def(td: &TypeDefInfo) -> String {
    // Build type_param → letter mapping
    let var_names: HashMap<TypeId, String> = td
        .type_params
        .iter()
        .enumerate()
        .map(|(i, &id)| (id, String::from((b'a' + i as u8) as char)))
        .collect();

    // Type header: "Name" or "(Name a b)"
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

    // Format each constructor
    let ctor_strs: Vec<String> = td
        .constructors
        .iter()
        .map(|ctor| {
            if ctor.fields.is_empty() {
                // Nullary
                ctor.name.clone()
            } else if td.constructors.len() == 1 && ctor.name == td.name {
                // Product type: just field list (ctor name == type name)
                let fields: Vec<String> = ctor
                    .fields
                    .iter()
                    .map(|(fname, fty)| format!("{} {}", format_field_type(fty, &var_names), fname))
                    .collect();
                format!("[{}]", fields.join(" "))
            } else {
                // Data constructor
                let fields: Vec<String> = ctor
                    .fields
                    .iter()
                    .map(|(fname, fty)| format!("{} {}", format_field_type(fty, &var_names), fname))
                    .collect();
                format!("({} [{}])", ctor.name, fields.join(" "))
            }
        })
        .collect();

    // Single constructor product type → single line
    if td.constructors.len() == 1 && td.constructors[0].name == td.name {
        format!("(deftype {} {})", header, ctor_strs[0])
    } else {
        // Multiline for sum types and enums
        let indent = "  ";
        let body = ctor_strs
            .iter()
            .map(|s| format!("{}{}", indent, s))
            .collect::<Vec<_>>()
            .join("\n");
        format!("(deftype {}\n{})", header, body)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::TypeExpr;

    #[test]
    fn format_show_display() {
        let sig = TraitMethodSig {
            docstring: None,
            hkt_param_index: None,
            name: "show".to_string(),
            params: vec![TypeExpr::SelfType],
            ret_type: TypeExpr::Named("String".to_string()),
            span: (0, 0),
        };
        assert_eq!(
            format_trait_method_type(&sig, "Display"),
            "(Fn [:Display a] String)"
        );
    }

    #[test]
    fn format_multi_self_param() {
        let sig = TraitMethodSig {
            docstring: None,
            hkt_param_index: None,
            name: "combine".to_string(),
            params: vec![TypeExpr::SelfType, TypeExpr::SelfType],
            ret_type: TypeExpr::SelfType,
            span: (0, 0),
        };
        assert_eq!(
            format_trait_method_type(&sig, "Semigroup"),
            "(Fn [:Semigroup a a] a)"
        );
    }

    #[test]
    fn format_io_returning_method() {
        let sig = TraitMethodSig {
            docstring: None,
            hkt_param_index: None,
            name: "emit".to_string(),
            params: vec![TypeExpr::SelfType],
            ret_type: TypeExpr::Applied(
                "IO".to_string(),
                vec![TypeExpr::Named("Int".to_string())],
            ),
            span: (0, 0),
        };
        assert_eq!(
            format_trait_method_type(&sig, "Emittable"),
            "(Fn [:Emittable a] (IO Int))"
        );
    }

    #[test]
    fn format_trait_decl_display() {
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
        assert_eq!(
            format_trait_decl(&decl),
            "(deftrait Display (show [self] String))"
        );
    }

    #[test]
    fn format_trait_decl_multi_method() {
        let decl = TraitDecl {
            visibility: crate::ast::Visibility::Public,
            docstring: None,
            name: "Numeric".to_string(),
            type_params: vec![],
            methods: vec![
                TraitMethodSig {
                    docstring: None,
                    hkt_param_index: None,
                    name: "zero".to_string(),
                    params: vec![],
                    ret_type: TypeExpr::SelfType,
                    span: (0, 0),
                },
                TraitMethodSig {
                    docstring: None,
                    hkt_param_index: None,
                    name: "add".to_string(),
                    params: vec![TypeExpr::SelfType, TypeExpr::SelfType],
                    ret_type: TypeExpr::SelfType,
                    span: (0, 0),
                },
            ],
            span: (0, 0),
        };
        assert_eq!(
            format_trait_decl(&decl),
            "(deftrait Numeric\n  (zero [] self)\n  (add [self self] self))"
        );
    }
}
