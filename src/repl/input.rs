use crate::ast::{ConstructorDef, Defn, DefnVariant, Expr, ReplInput, TopLevel, Visibility};
use crate::display::{format_trait_decl, format_type_def};
use crate::error::{format_error, Span};
use crate::module::CompiledModule;
use crate::names::{ModuleFullPath, Symbol};
use crate::sexp::Sexp;
use crate::typechecker::SymbolInfo;



use super::format::{
    format_macro_type, format_result_value, format_scheme_for_display, format_symbol_info,
    format_type_for_display, qualify_type_for_display, special_form_description,
};
use super::ReplSession;

impl ReplSession {
    /// Handle a parsed ReplInput.
    pub fn handle_input(&mut self, repl_input: ReplInput, input: &str, sexp: &Sexp) {
        // Block definitions for locked modules
        if self.locked_modules.contains(&self.current_module) {
            match &repl_input {
                ReplInput::Expr(_) => {} // expressions still work
                _ => {
                    eprintln!(
                        "; Module '{}' is locked — file has errors. Fix the file or /reload",
                        self.current_module.short_name()
                    );
                    return;
                }
            }
        }
        match repl_input {
            ReplInput::TypeDef {
                name,
                docstring,
                type_params,
                constructors,
                span,
                ..
            } => self.handle_type_def(name, docstring, type_params, constructors, span, sexp),
            ReplInput::DefnMulti {
                name,
                docstring,
                variants,
                ..
            } => self.handle_defn_multi(name, docstring, variants, input, sexp),
            ReplInput::Defn(defn) => self.handle_defn(defn, input, sexp),
            ReplInput::TraitDecl(td) => self.handle_trait_decl(td, sexp),
            ReplInput::TraitImpl(ti) => self.handle_trait_impl(ti, input, sexp),
            ReplInput::Expr(expr) => self.handle_expr(expr, input),
        }
    }

    fn handle_type_def(
        &mut self,
        name: String,
        docstring: Option<String>,
        type_params: Vec<String>,
        constructors: Vec<ConstructorDef>,
        span: Span,
        sexp: &Sexp,
    ) {
        let td = TopLevel::TypeDef {
            visibility: Visibility::Public,
            name: name.clone(),
            docstring,
            type_params,
            constructors,
            span,
        };
        self.tc.register_type_def(&td);
        self.jit.register_type_defs(&self.tc);

        // Store sexp on the TypeDef entry
        {
            let mod_name = self.current_module.short_name().to_string();
            let mod_path = ModuleFullPath::from(mod_name.as_str());
            if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                if let Some(crate::module::ModuleEntry::TypeDef {
                    sexp: entry_sexp, ..
                }) = cm.symbols.get_mut(name.as_str())
                {
                    *entry_sexp = Some(sexp.clone());
                }
            }
        }

        if let Some(tdi) = self.tc.resolve_type_def_via_modules(&name) {
            println!("{} :: {}", name, format_type_def(tdi));
        }

        self.save_current_module();
    }

    fn handle_defn_multi(
        &mut self,
        name: String,
        docstring: Option<String>,
        variants: Vec<DefnVariant>,
        input: &str,
        sexp: &Sexp,
    ) {
        // Store base-name metadata for /sig
        let base_meta = crate::typechecker::SymbolMeta::UserFn {
            docstring,
            param_names: vec![],
        };
        self.tc.update_current_module_meta(&name, base_meta);

        let checked = match self.tc.check_defn_multi(&name, &variants) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("{}", format_error(input, &e));
                return;
            }
        };

        let mut method_resolutions = match self.tc.resolve_methods() {
            Ok(mr) => mr,
            Err(e) => {
                eprintln!("{}", format_error(input, &e));
                return;
            }
        };
        if let Err(e) = self.tc.resolve_overloads(&mut method_resolutions) {
            eprintln!("{}", format_error(input, &e));
            return;
        }

        let et = self.tc.resolve_expr_types();
        for (mangled_name, mangled_defn, _scheme) in &checked {
            let scheme = self.tc.finalize_defn_type(mangled_name);
            // Ensure Def entry exists for fn_slots
            {
                let mod_name = self.current_module.short_name().to_string();
                let mod_path = ModuleFullPath::from(mod_name.as_str());
                if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                    cm.insert_def(
                        Symbol::from(mangled_name.as_str()),
                        scheme.clone(),
                        Visibility::Public,
                        None,
                    );
                }
            }
            // Allocate or reuse slot
            let slot = {
                let mod_path = ModuleFullPath::from(self.current_module.short_name());
                let cm = self.tc.modules.get_mut(&mod_path).unwrap();
                cm.get_got_slot(mangled_name)
                    .map(Ok)
                    .unwrap_or_else(|| cm.allocate_got_slot(mangled_defn.span))
            };
            let slot = match slot {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("{}", format_error(input, &e));
                    return;
                }
            };
            // Pre-register for fn_slots
            {
                let mod_path = ModuleFullPath::from(self.current_module.short_name());
                if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                    cm.pre_register_for_codegen(mangled_name, slot, mangled_defn.params.len());
                }
            }
            let fn_slots = self.jit.build_fn_slots_from_modules(&self.tc.modules);
            let compile_meta = match self.jit.compile_defn(
                mangled_defn,
                &scheme,
                &method_resolutions,
                &et,
                slot,
                &fn_slots,
                &self.tc.modules,
            ) {
                Ok(m) => m,
                Err(e) => {
                    eprintln!("{}", format_error(input, &e));
                    return;
                }
            };
            // Update CompiledModule with codegen metadata
            {
                let mod_name = self.current_module.short_name().to_string();
                let mod_path = ModuleFullPath::from(mod_name.as_str());
                if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                    cm.write_got_slot(slot, compile_meta.code_ptr);
                    cm.update_codegen(
                        mangled_name,
                        &compile_meta,
                        Some(input),
                        Some(sexp),
                        Some(mangled_defn),
                    );
                    cm.accumulate_method_resolutions(method_resolutions.clone());
                    cm.accumulate_expr_types(et.clone());
                }
            }
            let resolved = self.tc.resolve(&scheme.ty);
            println!("{} :: {}", mangled_name, format_type_for_display(&resolved));
        }
        self.track_repl_defn(&name, Some(sexp));
        self.save_current_module();
    }

    fn handle_defn(&mut self, defn: Defn, input: &str, sexp: &Sexp) {
        match self.tc.check_defn(&defn) {
            Ok(_) => {}
            Err(e) => {
                eprintln!("{}", format_error(input, &e));
                return;
            }
        };

        let mut method_resolutions = match self.tc.resolve_methods() {
            Ok(mr) => mr,
            Err(e) => {
                eprintln!("{}", format_error(input, &e));
                return;
            }
        };
        if let Err(e) = self.tc.resolve_overloads(&mut method_resolutions) {
            eprintln!("{}", format_error(input, &e));
            return;
        }

        let et = self.tc.resolve_expr_types();
        let scheme = self.tc.finalize_defn_type(&defn.name);

        self.track_repl_defn(&defn.name, Some(sexp));

        if scheme.is_constrained() {
            self.tc.register_constrained_fn(&defn, &scheme);
        } else {
            // Get or allocate slot
            let slot = {
                let mod_path = ModuleFullPath::from(self.current_module.short_name());
                let cm = self.tc.modules.get_mut(&mod_path).unwrap();
                cm.get_got_slot(&defn.name)
                    .map(Ok)
                    .unwrap_or_else(|| cm.allocate_got_slot(defn.span))
            };
            let slot = match slot {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("{}", format_error(input, &e));
                    return;
                }
            };
            // Pre-register for fn_slots
            {
                let mod_path = ModuleFullPath::from(self.current_module.short_name());
                if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                    cm.pre_register_for_codegen(&defn.name, slot, defn.params.len());
                }
            }
            let fn_slots = self.jit.build_fn_slots_from_modules(&self.tc.modules);
            match self.jit.compile_defn(
                &defn,
                &scheme,
                &method_resolutions,
                &et,
                slot,
                &fn_slots,
                &self.tc.modules,
            ) {
                Ok(compile_meta) => {
                    let mod_name = self.current_module.short_name().to_string();
                    let mod_path = ModuleFullPath::from(mod_name.as_str());
                    if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                        cm.write_got_slot(slot, compile_meta.code_ptr);
                        cm.update_codegen(
                            &defn.name,
                            &compile_meta,
                            Some(input),
                            Some(sexp),
                            Some(&defn),
                        );
                        cm.accumulate_method_resolutions(method_resolutions);
                        cm.accumulate_expr_types(et);
                    }
                }
                Err(e) => {
                    eprintln!("{}", format_error(input, &e));
                    return;
                }
            }
        }

        println!("{} :: {}", defn.name, format_scheme_for_display(&scheme));
        self.save_current_module();
    }

    fn handle_trait_decl(&mut self, td: crate::ast::TraitDecl, sexp: &Sexp) {
        for method in &td.methods {
            self.jit.register_trait_method(&method.name);
        }
        self.tc.register_trait_public(&td);

        // Store sexp on the TraitDecl entry
        {
            let mod_name = self.current_module.short_name().to_string();
            let mod_path = ModuleFullPath::from(mod_name.as_str());
            if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                if let Some(crate::module::ModuleEntry::TraitDecl {
                    sexp: entry_sexp, ..
                }) = cm.symbols.get_mut(td.name.as_str())
                {
                    *entry_sexp = Some(sexp.clone());
                }
            }
        }

        println!("{} :: {}", td.name, format_trait_decl(&td));
        self.save_current_module();
    }

    fn handle_trait_impl(&mut self, ti: crate::ast::TraitImpl, input: &str, sexp: &Sexp) {
        if let Err(e) = self.tc.validate_impl_public(&ti) {
            eprintln!("{}", format_error(input, &e));
            return;
        }
        self.tc.register_impl(&ti);

        let self_type = match self.tc.resolve_impl_self_type(&ti) {
            Ok(t) => t,
            Err(e) => {
                eprintln!("{}", format_error(input, &e));
                return;
            }
        };
        let target = ti.impl_target_mangled();

        for method in &ti.methods {
            let mangled = Defn {
                visibility: Visibility::Public,
                name: format!("{}${}", method.name, target),
                docstring: None,
                params: method.params.clone(),
                param_annotations: method.param_annotations.clone(),
                body: method.body.clone(),
                span: method.span,
            };
            match self.tc.check_impl_method(&mangled, &self_type) {
                Ok(_) => {}
                Err(e) => {
                    eprintln!("{}", format_error(input, &e));
                    return;
                }
            };
            let mut method_resolutions = match self.tc.resolve_methods() {
                Ok(mr) => mr,
                Err(e) => {
                    eprintln!("{}", format_error(input, &e));
                    return;
                }
            };
            if let Err(e) = self.tc.resolve_overloads(&mut method_resolutions) {
                eprintln!("{}", format_error(input, &e));
                return;
            }
            let et = self.tc.resolve_expr_types();
            let scheme = self.tc.finalize_defn_type(&mangled.name);

            if scheme.is_constrained() {
                self.tc.register_constrained_fn(&mangled, &scheme);
            } else {
                // Ensure Def entry exists
                {
                    let mod_name = self.current_module.short_name().to_string();
                    let mod_path = ModuleFullPath::from(mod_name.as_str());
                    if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                        cm.insert_def(
                            Symbol::from(mangled.name.as_str()),
                            scheme.clone(),
                            Visibility::Public,
                            None,
                        );
                    }
                }
                let slot = {
                    let mod_path = ModuleFullPath::from(self.current_module.short_name());
                    let cm = self.tc.modules.get_mut(&mod_path).unwrap();
                    cm.get_got_slot(&mangled.name)
                        .map(Ok)
                        .unwrap_or_else(|| cm.allocate_got_slot(mangled.span))
                };
                let slot = match slot {
                    Ok(s) => s,
                    Err(e) => {
                        eprintln!("{}", format_error(input, &e));
                        return;
                    }
                };
                {
                    let mod_path = ModuleFullPath::from(self.current_module.short_name());
                    if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                        cm.pre_register_for_codegen(
                            &mangled.name,
                            slot,
                            mangled.params.len(),
                        );
                    }
                }
                let fn_slots = self.jit.build_fn_slots_from_modules(&self.tc.modules);
                match self.jit.compile_defn(
                    &mangled,
                    &scheme,
                    &method_resolutions,
                    &et,
                    slot,
                    &fn_slots,
                    &self.tc.modules,
                ) {
                    Ok(compile_meta) => {
                        let mod_name = self.current_module.short_name().to_string();
                        let mod_path = ModuleFullPath::from(mod_name.as_str());
                        if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                            cm.write_got_slot(slot, compile_meta.code_ptr);
                            cm.update_codegen(
                                &mangled.name,
                                &compile_meta,
                                Some(input),
                                Some(sexp),
                                Some(&mangled),
                            );
                            cm.accumulate_method_resolutions(method_resolutions);
                            cm.accumulate_expr_types(et);
                        }
                    }
                    Err(e) => {
                        eprintln!("{}", format_error(input, &e));
                        return;
                    }
                }
            }
        }

        // Store impl sexp for file generation
        {
            let mod_name = self.current_module.short_name().to_string();
            let mod_path = ModuleFullPath::from(mod_name.as_str());
            if let Some(cm) = self.tc.modules.get_mut(&mod_path) {
                cm.impl_sexps.push(crate::module::ImplSexp {
                    trait_name: crate::names::TraitName::from(ti.trait_name.as_str()),
                    target: crate::names::TypeName::from(ti.target_type.as_str()),
                    sexp: sexp.clone(),
                });
            }
        }

        if ti.type_args.is_empty() {
            println!("impl {} for {}", ti.trait_name, ti.target_type);
        } else {
            println!(
                "impl {} for ({} {})",
                ti.trait_name,
                ti.target_type,
                ti.type_args.join(" ")
            );
        }

        self.save_current_module();
    }

    fn handle_expr(&mut self, expr: Expr, input: &str) {
        // Bare special form or operator — display usage
        if let Expr::Var { name, .. } = &expr {
            if let Some(desc) = special_form_description(&self.tc, name) {
                println!("{}", desc);
                return;
            }
        }

        // Bare module name — display module info
        if let Expr::Var { name, .. } = &expr {
            let module_id = crate::module::ModuleFullPath(name.clone());
            if self.loaded_modules.contains_key(&module_id) {
                let public_names = self.tc.get_module_public_names(name);
                if public_names.is_empty() {
                    println!("Module '{}' (no public symbols)", name);
                } else {
                    println!("Module '{}':", name);
                    for pname in &public_names {
                        let qualified = format!("{}/{}", name, pname);
                        if let Some(info) = self.tc.describe_symbol(&qualified) {
                            println!("  {}", format_symbol_info(pname, &info));
                        } else {
                            println!("  {}", pname);
                        }
                    }
                }
                return;
            }
        }

        // Bare macro name — display macro type
        if let Expr::Var { name, .. } = &expr {
            if let Some(entry) = self.macro_env.get(name) {
                println!("{}", format_macro_type(entry));
                return;
            }
        }

        // Known symbol — display description without compiling
        if let Expr::Var { name, .. } = &expr {
            if let Some(info) = self.tc.describe_symbol(name) {
                let qualified = self.tc.qualified_name(name).to_string();
                let display_name: &str = match &info {
                    SymbolInfo::UserFn { .. }
                    | SymbolInfo::ConstrainedFn { .. }
                    | SymbolInfo::OverloadedFn { .. }
                    | SymbolInfo::InlinePrimitive { .. }
                    | SymbolInfo::ExternPrimitive { .. } => &qualified,
                    _ => name.as_str(),
                };
                println!("{}", format_symbol_info(display_name, &info));
                return;
            }
        }

        // Typecheck
        let ty = match self.tc.check_expr(&expr) {
            Ok(t) => t,
            Err(e) => {
                eprintln!("{}", format_error(input, &e));
                return;
            }
        };

        // Resolve trait methods + overloads
        let mut method_resolutions = match self.tc.resolve_methods() {
            Ok(mr) => mr,
            Err(e) => {
                eprintln!("{}", format_error(input, &e));
                return;
            }
        };
        if let Err(e) = self.tc.resolve_overloads(&mut method_resolutions) {
            eprintln!("{}", format_error(input, &e));
            return;
        }

        // On-demand monomorphisation
        let et = self.tc.resolve_expr_types();
        match self.tc.monomorphise_all() {
            Ok((mono_defns, mono_dispatches)) => {
                method_resolutions.extend(mono_dispatches);
                if let Err(e) = self.compile_mono_specializations(&mono_defns, &method_resolutions, &et) {
                    eprintln!("{}", format_error(input, &e));
                    return;
                }
            }
            Err(e) => {
                eprintln!("{}", format_error(input, &e));
                return;
            }
        }

        // Compile and execute
        let fn_slots = self.jit.build_fn_slots_from_modules(&self.tc.modules);
        match self.jit.eval_expr(&expr, &method_resolutions, &et, &fn_slots, &self.tc.modules) {
            Ok(result) => {
                let resolved = self.tc.resolve(&ty);
                let display_type = qualify_type_for_display(&resolved, &self.tc);
                let formatted_type = format_type_for_display(&display_type);
                let value_str = format_result_value(result, &resolved, &self.tc);
                println!("{} :: {}", value_str, formatted_type);
            }
            Err(e) => {
                eprintln!("{}", format_error(input, &e));
            }
        }
    }

    /// Register a user-defined name in the current module scope.
    /// Writes into CompiledModule and registers the module prefix.
    /// If `sexp_val` is Some, stores it on the Def entry for file generation.
    fn track_repl_defn(&mut self, name: &str, sexp_val: Option<&Sexp>) {
        let mod_name = self.current_module.short_name().to_string();
        self.tc.register_module_prefix(&mod_name);

        // Write into CompiledModule
        let scheme_opt = self.tc.lookup(name).cloned();
        let meta_opt = self.tc.get_symbol_meta(name).cloned();
        if let Some(scheme) = scheme_opt {
            let mod_path = ModuleFullPath::from(mod_name.as_str());
            let cm = self
                .tc
                .modules
                .entry(mod_path.clone())
                .or_insert_with(|| CompiledModule::new(mod_path));
            cm.insert_def(Symbol::from(name), scheme, Visibility::Public, meta_opt);
            // Store sexp for file generation
            if let Some(s) = sexp_val {
                if let Some(crate::module::ModuleEntry::Def {
                    kind:
                        crate::module::DefKind::UserFn {
                            codegen: cg,
                            ..
                        },
                    ..
                }) = cm.symbols.get_mut(name)
                {
                    cg.sexp = Some(s.clone());
                }
            }
        }
    }
}
