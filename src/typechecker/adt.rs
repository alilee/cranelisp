use std::collections::HashMap;

use crate::ast::*;
use crate::types::*;

use super::{ConstructorInfo, TypeChecker, TypeDefInfo};

impl TypeChecker {
    /// Register a type definition (deftype). Creates type registry entries and
    /// registers constructor functions and field accessors in the type environment.
    pub fn register_type_def(&mut self, td: &TopLevel) {
        let (visibility, name, docstring, type_params, constructors, _span) = match td {
            TopLevel::TypeDef {
                visibility,
                name,
                docstring,
                type_params,
                constructors,
                span,
            } => (*visibility, name, docstring, type_params, constructors, span),
            _ => return,
        };

        // Allocate fresh type vars for each type parameter
        let mut var_map: HashMap<String, TypeId> = HashMap::new();
        let mut param_ids: Vec<TypeId> = Vec::new();
        for param_name in type_params {
            let id = self.next_id;
            self.next_id += 1;
            var_map.insert(param_name.clone(), id);
            param_ids.push(id);
        }

        // Build the ADT type: ADT("Option", [Var(a_id), ...])
        let type_args: Vec<Type> = param_ids.iter().map(|&id| Type::Var(id)).collect();
        let adt_type = Type::ADT(name.clone(), type_args.clone());

        // Build ConstructorInfo entries and register in env
        let mut ctor_infos = Vec::new();
        for (tag, ctor) in constructors.iter().enumerate() {
            let fields: Vec<(String, Type)> = ctor
                .fields
                .iter()
                .map(|f| {
                    let ty = self.resolve_type_expr_with_vars(&f.type_expr, &adt_type, &var_map);
                    (f.name.clone(), ty)
                })
                .collect();

            // Register constructor in env
            if fields.is_empty() {
                // Nullary constructor: type is just ADT
                let scheme = Scheme {
                    vars: param_ids.clone(),
                    ty: adt_type.clone(),
                    constraints: HashMap::new(),
                };
                self.insert_def_vis(ctor.name.clone(), scheme, visibility);
            } else {
                // Data constructor: type is Fn([field_types], ADT)
                let field_tys: Vec<Type> = fields.iter().map(|(_, t)| t.clone()).collect();
                let fn_ty = Type::Fn(field_tys, Box::new(adt_type.clone()));
                let scheme = Scheme {
                    vars: param_ids.clone(),
                    ty: fn_ty,
                    constraints: HashMap::new(),
                };
                self.insert_def_vis(ctor.name.clone(), scheme, visibility);
            }

            // Register accessor functions for each field
            for (field_idx, (field_name, field_ty)) in fields.iter().enumerate() {
                // Accessor: ADT -> field_type
                let accessor_ty = Type::Fn(vec![adt_type.clone()], Box::new(field_ty.clone()));
                let scheme = Scheme {
                    vars: param_ids.clone(),
                    ty: accessor_ty,
                    constraints: HashMap::new(),
                };
                // Only register if not already taken (first constructor wins for shared names)
                if self.lookup(field_name).is_none() {
                    self.insert_def_vis(field_name.clone(), scheme, visibility);
                }
                // Store accessor info for codegen: field_name → (type_name, ctor_name, field_idx, tag)
                // This is already available via TypeDefInfo in CompiledModule, so no separate map needed.
                let _ = field_idx; // used for documentation, codegen reads from TypeDefInfo
            }

            ctor_infos.push(ConstructorInfo {
                name: ctor.name.clone(),
                tag,
                fields,
                docstring: ctor.docstring.clone(),
            });
        }

        let tdi = TypeDefInfo {
            name: name.clone(),
            type_params: param_ids,
            constructors: ctor_infos,
            docstring: docstring.clone(),
        };

        // Detect product type: single constructor with same name as type.
        let is_product = tdi.constructors.len() == 1 && tdi.constructors[0].name == *name;

        if is_product {
            // Product type: TypeDef entry serves double duty (type + constructor).
            // Capture the constructor scheme before overwriting with TypeDef.
            let constructor_scheme = self.lookup(name).cloned();

            let current = self.current_module_path.clone();
            let cm = self
                .modules
                .entry(current.clone())
                .or_insert_with(|| crate::module::CompiledModule::new(current));
            cm.symbols.insert(
                crate::names::Symbol::from(name.as_str()),
                crate::module::ModuleEntry::TypeDef {
                    info: tdi,
                    visibility,
                    constructor_scheme,
                    sexp: None,
                },
            );
        } else {
            // Sum type / enum: write Constructor entries for each constructor,
            // then write a separate TypeDef entry for the type name.
            let ctor_entries: Vec<_> = tdi
                .constructors
                .iter()
                .filter_map(|ci| self.lookup(&ci.name).cloned().map(|s| (ci.clone(), s)))
                .collect();

            for (ci, ctor_scheme) in ctor_entries {
                self.insert_constructor(
                    ci.name.clone(),
                    name.clone(),
                    ci,
                    ctor_scheme,
                    visibility,
                );
            }

            let current = self.current_module_path.clone();
            let cm = self
                .modules
                .entry(current.clone())
                .or_insert_with(|| crate::module::CompiledModule::new(current));
            cm.symbols.insert(
                crate::names::Symbol::from(name.as_str()),
                crate::module::ModuleEntry::TypeDef {
                    info: tdi,
                    visibility,
                    constructor_scheme: None,
                    sexp: None,
                },
            );
        }
    }
}
