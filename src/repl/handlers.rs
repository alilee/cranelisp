use std::time::Instant;

use crate::ast::{Expr, ReplInput};
use crate::ast_builder::parse_repl_input;
use crate::error::format_error;
use crate::intrinsics;
use crate::names::resolve_bare_name;
use crate::typechecker::SymbolInfo;
use crate::types::Type;

use super::commands::ReplCommand;
use super::format::{
    format_fn_sig, format_result_value, format_scheme_for_display, format_symbol_info,
    format_trait_sig, format_type, format_type_as_annotation, format_type_def_sig,
    format_type_for_display, special_form_description, special_form_docstring, special_form_names,
    type_var_names,
};
use super::ReplSession;

impl ReplSession {
    /// Returns true if the REPL should quit.
    pub fn handle_command(&mut self, cmd: ReplCommand<'_>, _full_input: &str) -> bool {
        match cmd {
            ReplCommand::Quit => return true,
            ReplCommand::Help => {
                println!("Commands:");
                println!("  /sig <name>    (/s)  Show signature with docstring and typed params");
                println!("  /doc <name>    (/d)  Show docstring");
                println!("  /type <expr>   (/t)  Show type without evaluating");
                println!(
                    "  /info <name>   (/i)  Type, source, code size, compile time, specializations"
                );
                println!("  /source <name>       Show original source text");
                println!("  /sexp <name>         Show S-expression (parser phase 1)");
                println!("  /ast <name>          Show AST (parser phase 2)");
                println!("  /clif <name>         Show Cranelift IR");
                println!("  /disasm <name>       Show disassembled native code");
                println!("  /time <expr>         Evaluate with timing breakdown");
                println!("  /expand <form> (/e)  Macro-expand a form and show result");
                println!("  /list [name]   (/l)  List symbols defined in current module");
                println!("  /imports [name]      List imported symbols and special forms");
                println!("  /mod [name]          Switch namespace (no arg = user)");
                println!("  /reload [name] (/r)  Reload module from file (no arg = locked modules)");
                println!("  /mem [<expr>]  (/m)  Allocation stats, deltas for expr, /mem reset");
                println!("  /exe [path]          Export standalone executable");
                println!("  /quit          (/q)  Exit the REPL");
                println!("  /help          (/h)  This help");
            }
            ReplCommand::Type(arg) => self.cmd_type(arg),
            ReplCommand::Info(name) => self.cmd_info(name),
            ReplCommand::Sig(name) => self.cmd_sig(name),
            ReplCommand::Doc(name) => self.cmd_doc(name),
            ReplCommand::Source(name) => self.cmd_source(name),
            ReplCommand::Sexp(name) => self.cmd_sexp(name),
            ReplCommand::Ast(name) => self.cmd_ast(name),
            ReplCommand::Clif(name) => self.cmd_clif(name),
            ReplCommand::Disasm(name) => self.cmd_disasm(name),
            ReplCommand::Time(arg) => self.cmd_time(arg),
            ReplCommand::Mem(arg) => self.cmd_mem(arg),
            ReplCommand::List(filter) => self.cmd_list(filter),
            ReplCommand::Imports(filter) => self.cmd_imports(filter),
            ReplCommand::Expand(arg) => self.cmd_expand(arg),
            ReplCommand::Mod(arg) => self.cmd_mod(arg),
            ReplCommand::Reload(arg) => self.cmd_reload(arg),
            ReplCommand::Exe(arg) => self.cmd_exe(arg),
        }
        false
    }

    fn cmd_type(&mut self, arg: &str) {
        if arg.is_empty() {
            eprintln!("/type requires an expression");
            return;
        }
        let parsed = match parse_repl_input(arg) {
            Ok(ri) => ri,
            Err(e) => {
                eprintln!("{}", format_error(arg, &e));
                return;
            }
        };
        match parsed {
            ReplInput::Expr(expr) => {
                // Macro name
                if let Expr::Var { name, .. } = &expr {
                    if let Some(info @ SymbolInfo::Macro { .. }) = self.tc.describe_symbol(name) {
                        println!("{}", format_symbol_info(name, &info));
                        return;
                    }
                }
                // Constrained/overloaded functions: show scheme directly
                if let Expr::Var { name, .. } = &expr {
                    if let Some(info) = self.tc.describe_symbol(name) {
                        match info {
                            SymbolInfo::ConstrainedFn { scheme }
                            | SymbolInfo::UserFn { scheme } => {
                                println!("{}", format_scheme_for_display(scheme));
                                return;
                            }
                            SymbolInfo::OverloadedFn { schemes } => {
                                let sigs: Vec<String> = schemes
                                    .iter()
                                    .map(|s| format_scheme_for_display(s))
                                    .collect();
                                println!("{}", sigs.join("\n"));
                                return;
                            }
                            _ => {}
                        }
                    }
                }
                match self.tc.check_expr(&expr) {
                    Ok(ty) => {
                        // Resolve but discard pending resolutions
                        let _ = self.tc.resolve_methods();
                        let resolved = self.tc.resolve(&ty);
                        println!("{}", format_type_for_display(&resolved));
                    }
                    Err(e) => eprintln!("{}", format_error(arg, &e)),
                }
            }
            _ => eprintln!("/type expects an expression, not a definition"),
        }
    }

    fn cmd_info(&mut self, name: &str) {
        use super::format::classification_label;

        if name.is_empty() {
            eprintln!("/info requires a name");
            return;
        }
        let bare = resolve_bare_name(name);
        let display_name = if name.contains('/') {
            name.to_string()
        } else {
            self.tc.qualified_name(bare).to_string()
        };

        // Check special forms first
        if let Some(desc) = special_form_description(&self.tc, bare) {
            println!("{} :: special form", display_name);
            println!("  {}", desc);
            return;
        }

        // Check typechecker symbol info (handles dotted names)
        let info = match self.tc.describe_symbol(name) {
            Some(i) => i,
            None => {
                eprintln!("Unknown symbol: {}", name);
                return;
            }
        };

        let meta = self.tc.get_symbol_meta(bare);
        let label = classification_label(&info, meta);

        // Header line: qualified_name :: classification
        let header_name = match &info {
            SymbolInfo::TraitMethod { trait_name, .. } => format!("{}.{}", trait_name, bare),
            SymbolInfo::Constructor { type_name, .. } => format!("{}.{}", type_name, bare),
            _ => display_name.clone(),
        };
        println!("{} :: {}", header_name, label);

        // Definition form (indented sig output)
        match &info {
            SymbolInfo::UserFn { scheme } | SymbolInfo::ConstrainedFn { scheme } => {
                println!("  {}", format_fn_sig(&display_name, scheme, meta));
            }
            SymbolInfo::OverloadedFn { schemes } => {
                let base_meta = self.tc.get_symbol_meta(bare);
                let doc_part = base_meta
                    .and_then(|m| m.docstring())
                    .map(|d| format!(" \"{}\"", d))
                    .unwrap_or_default();
                let mangled_names: Vec<String> = self
                    .tc
                    .get_resolved_overloads(bare)
                    .map(|resolved| resolved.iter().map(|(_, _, m)| m.clone()).collect())
                    .unwrap_or_default();
                if schemes.len() == 1 {
                    let mangled = mangled_names.first().map(|m| m.as_str());
                    let variant_meta = mangled
                        .and_then(|m| self.tc.get_symbol_meta(m))
                        .or(base_meta);
                    println!("  {}", format_fn_sig(&display_name, schemes[0], variant_meta));
                } else {
                    let variants: Vec<String> = schemes
                        .iter()
                        .enumerate()
                        .map(|(i, s)| {
                            let var_names = type_var_names(&s.ty);
                            let param_names = mangled_names
                                .get(i)
                                .and_then(|m| self.tc.get_symbol_meta(m));
                            if let Type::Fn(params, ret) = &s.ty {
                                let parts: Vec<String> = params
                                    .iter()
                                    .enumerate()
                                    .map(|(j, p)| {
                                        let ann = format_type_as_annotation(
                                            p,
                                            &var_names,
                                            &s.constraints,
                                        );
                                        if let Some(pname) =
                                            param_names.and_then(|m| m.param_names().get(j))
                                        {
                                            format!("{} {}", ann, pname)
                                        } else {
                                            ann
                                        }
                                    })
                                    .collect();
                                let ret_str = format_type(ret, &var_names);
                                format!("    ([{}] {})", parts.join(" "), ret_str)
                            } else {
                                format!("    {}", format_scheme_for_display(s))
                            }
                        })
                        .collect();
                    println!(
                        "  (defn {}{}\n{})",
                        display_name,
                        doc_part,
                        variants.join("\n")
                    );
                }
            }
            SymbolInfo::InlinePrimitive { scheme } | SymbolInfo::ExternPrimitive { scheme } => {
                println!("  {}", format_fn_sig(&display_name, scheme, meta));
            }
            SymbolInfo::TraitDecl(decl, impl_types) => {
                println!("  {}", format_trait_sig(decl, impl_types));
            }
            SymbolInfo::TraitMethod {
                trait_name,
                sig,
                type_params,
            } => {
                let doc_part = sig
                    .docstring
                    .as_ref()
                    .map(|d| format!(" \"{}\"", d))
                    .unwrap_or_default();
                println!(
                    "  ({}{} :: {})",
                    bare,
                    doc_part,
                    crate::display::format_trait_method_type_with_params(sig, trait_name, type_params)
                );
            }
            SymbolInfo::UserType { type_def } => {
                println!("  {}", format_type_def_sig(type_def));
                if let Some(impls) = self.tc.impls_for_type(bare) {
                    if !impls.is_empty() {
                        println!("  impl {}", impls.join(", "));
                    }
                }
            }
            SymbolInfo::TypeName { impls } => {
                if !impls.is_empty() {
                    println!("  impl {}", impls.join(", "));
                }
            }
            SymbolInfo::Constructor { type_name, scheme } => {
                let doc = self.tc.resolve_type_def_via_modules(type_name).and_then(|td| {
                    td.constructors
                        .iter()
                        .find(|c| c.name == bare)
                        .and_then(|c| c.docstring.as_ref())
                });
                let doc_part = doc.map(|d| format!(" \"{}\"", d)).unwrap_or_default();
                println!(
                    "  {}.{}{} :: {}",
                    type_name,
                    bare,
                    doc_part,
                    format_scheme_for_display(scheme)
                );
            }
            SymbolInfo::Macro {
                fixed_params,
                rest_param,
                docstring,
                ..
            } => {
                let doc_part = docstring
                    .map(|d| format!(" \"{}\"", d))
                    .unwrap_or_default();
                let mut parts = Vec::new();
                for p in *fixed_params {
                    parts.push(format!(":Sexp {}", p));
                }
                if let Some(rest) = rest_param {
                    parts.push(format!("& :(List Sexp) {}", rest));
                }
                println!(
                    "  (defmacro {}{} [{}] Sexp)",
                    bare,
                    doc_part,
                    parts.join(" ")
                );
            }
            SymbolInfo::Ambiguous { alternatives } => {
                if !alternatives.is_empty() {
                    println!("  use {}", alternatives.join(" or "));
                }
            }
        }

        // JIT info
        if let Some(view) = self.tc.get_def_codegen(bare) {
            Self::print_jit_info_view(&view);
        }

        // Specializations
        let specs = self.tc.find_specializations(bare);
        if !specs.is_empty() {
            println!("  specializations:");
            for (mangled, view) in &specs {
                let size_str = view
                    .code_size
                    .map(|s| format!("{} bytes", s))
                    .unwrap_or_else(|| "?".to_string());
                let time_str = view
                    .compile_duration
                    .map(|d| format!("{:.2}ms", d.as_secs_f64() * 1000.0))
                    .unwrap_or_else(|| "?".to_string());
                println!("    {} — {}, compiled in {}", mangled, size_str, time_str);
            }
        }
    }

    fn cmd_sig(&self, name: &str) {
        if name.is_empty() {
            eprintln!("/sig requires a name");
            return;
        }
        let bare = resolve_bare_name(name);
        let display_name = if name.contains('/') {
            name.to_string()
        } else {
            self.tc.qualified_name(bare).to_string()
        };
        if let Some(info) = self.tc.describe_symbol(name) {
            match &info {
                SymbolInfo::Macro {
                    fixed_params,
                    rest_param,
                    docstring,
                    ..
                } => {
                    let doc_part = docstring
                        .map(|d| format!(" \"{}\"", d))
                        .unwrap_or_default();
                    let mut parts = Vec::new();
                    for p in *fixed_params {
                        parts.push(format!(":Sexp {}", p));
                    }
                    if let Some(rest) = rest_param {
                        parts.push(format!("& :(List Sexp) {}", rest));
                    }
                    println!(
                        "(defmacro {}{} [{}] Sexp)",
                        bare,
                        doc_part,
                        parts.join(" ")
                    );
                    return;
                }
                SymbolInfo::UserFn { scheme } | SymbolInfo::ConstrainedFn { scheme } => {
                    let meta = self.tc.get_symbol_meta(bare);
                    println!("{}", format_fn_sig(&display_name, scheme, meta));
                }
                SymbolInfo::OverloadedFn { schemes } => {
                    let base_meta = self.tc.get_symbol_meta(bare);
                    let doc_part = base_meta
                        .and_then(|m| m.docstring())
                        .map(|d| format!(" \"{}\"", d))
                        .unwrap_or_default();
                    // Get mangled names to look up per-variant param names
                    let mangled_names: Vec<String> = self
                        .tc
                        .get_resolved_overloads(bare)
                        .map(|resolved| resolved.iter().map(|(_, _, m)| m.clone()).collect())
                        .unwrap_or_default();
                    if schemes.len() == 1 {
                        let mangled = mangled_names.first().map(|m| m.as_str());
                        let meta = mangled
                            .and_then(|m| self.tc.get_symbol_meta(m))
                            .or_else(|| self.tc.get_symbol_meta(bare));
                        println!("{}", format_fn_sig(&display_name, schemes[0], meta));
                    } else {
                        let variants: Vec<String> = schemes
                            .iter()
                            .enumerate()
                            .map(|(i, s)| {
                                let var_names = type_var_names(&s.ty);
                                let param_names = mangled_names
                                    .get(i)
                                    .and_then(|m| self.tc.get_symbol_meta(m));
                                if let Type::Fn(params, ret) = &s.ty {
                                    let parts: Vec<String> = params
                                        .iter()
                                        .enumerate()
                                        .map(|(j, p)| {
                                            let ann = format_type_as_annotation(
                                                p,
                                                &var_names,
                                                &s.constraints,
                                            );
                                            if let Some(pname) =
                                                param_names.and_then(|m| m.param_names().get(j))
                                            {
                                                format!("{} {}", ann, pname)
                                            } else {
                                                ann
                                            }
                                        })
                                        .collect();
                                    let ret_str = format_type(ret, &var_names);
                                    format!("  ([{}] {})", parts.join(" "), ret_str)
                                } else {
                                    format!("  {}", format_scheme_for_display(s))
                                }
                            })
                            .collect();
                        println!(
                            "(defn {}{}\n{})",
                            display_name,
                            doc_part,
                            variants.join("\n")
                        );
                    }
                }
                SymbolInfo::TraitDecl(decl, impl_types) => {
                    println!("{}", format_trait_sig(decl, impl_types));
                }
                SymbolInfo::TraitMethod {
                    trait_name, sig, ..
                } => {
                    let doc_part = sig
                        .docstring
                        .as_ref()
                        .map(|d| format!(" \"{}\"", d))
                        .unwrap_or_default();
                    println!(
                        "{}.{}{} :: {}",
                        trait_name,
                        bare,
                        doc_part,
                        crate::display::format_trait_method_type_with_params(sig, trait_name, &[])
                    );
                }
                SymbolInfo::UserType { type_def } => {
                    println!("{}", format_type_def_sig(type_def));
                }
                SymbolInfo::Constructor { type_name, scheme } => {
                    // Show constructor with docstring from parent type
                    let doc = self.tc.resolve_type_def_via_modules(type_name).and_then(|td| {
                        td.constructors
                            .iter()
                            .find(|c| c.name == bare)
                            .and_then(|c| c.docstring.as_ref())
                    });
                    let doc_part = doc.map(|d| format!(" \"{}\"", d)).unwrap_or_default();
                    println!(
                        "{}.{}{} :: {}",
                        type_name,
                        bare,
                        doc_part,
                        format_scheme_for_display(scheme)
                    );
                }
                SymbolInfo::InlinePrimitive { scheme } | SymbolInfo::ExternPrimitive { scheme } => {
                    let meta = self.tc.get_symbol_meta(bare);
                    println!("{}", format_fn_sig(&display_name, scheme, meta));
                }
                _ => {
                    println!("{}", format_symbol_info(bare, &info));
                }
            }
            return;
        }
        if let Some(desc) = special_form_description(&self.tc, bare) {
            println!("{}", desc);
            return;
        }
        eprintln!("Unknown symbol: {}", name);
    }

    fn cmd_doc(&self, name: &str) {
        if name.is_empty() {
            eprintln!("/doc requires a name");
            return;
        }
        let bare = resolve_bare_name(name);
        // Check symbol_meta first (defn, defn multi, primitives, special forms)
        if let Some(meta) = self.tc.get_symbol_meta(bare) {
            if let Some(doc) = meta.docstring() {
                println!("{}", doc);
                return;
            }
        }
        // Check trait declarations
        if let Some(decl) = self.tc.get_trait(bare) {
            if let Some(doc) = &decl.docstring {
                println!("{}", doc);
                return;
            }
        }
        // Check trait method docstrings
        if let Some(trait_name) = self.tc.get_method_trait(bare) {
            if let Some(decl) = self.tc.get_trait(trait_name) {
                if let Some(sig) = decl.methods.iter().find(|m| m.name == bare) {
                    if let Some(doc) = &sig.docstring {
                        println!("{}", doc);
                        return;
                    }
                }
            }
        }
        // Check type definitions
        if let Some(td) = self.tc.resolve_type_def_via_modules(bare) {
            if let Some(doc) = &td.docstring {
                println!("{}", doc);
                return;
            }
        }
        // Check constructor docstrings
        if let Some(type_name) = self.tc.resolve_constructor_type_via_modules(bare) {
            if let Some(td) = self.tc.resolve_type_def_via_modules(type_name) {
                if let Some(ctor) = td.constructors.iter().find(|c| c.name == bare) {
                    if let Some(doc) = &ctor.docstring {
                        println!("{}", doc);
                        return;
                    }
                }
            }
        }
        // Check macros
        if let Some(SymbolInfo::Macro { docstring, .. }) = self.tc.describe_symbol(bare) {
            if let Some(doc) = docstring {
                println!("{}", doc);
            } else {
                eprintln!("No docstring for '{}' (macro)", name);
            }
            return;
        }
        // Check special forms
        if let Some(doc) = special_form_docstring(&self.tc, bare) {
            println!("{}", doc);
            return;
        }
        eprintln!("No docstring for '{}'", name);
    }

    fn cmd_source(&self, name: &str) {
        if name.is_empty() {
            eprintln!("/source requires a name");
            return;
        }
        if let Some(view) = self.tc.get_def_codegen(name) {
            if let Some(src) = view.source {
                println!("{}", src);
                return;
            }
        }
        // Check macros — prefer source text, fall back to sexp Display
        if let Some(src) = self.tc.get_macro_source(name) {
            println!("{}", src);
            return;
        }
        if let Some(sexp) = self.tc.get_macro_sexp(name) {
            println!("{}", sexp);
            return;
        }
        // Check specializations
        let specs = self.tc.find_specializations(name);
        if !specs.is_empty() {
            for (mangled, view) in &specs {
                if let Some(src) = view.source {
                    println!("; {}", mangled);
                    println!("{}", src);
                }
            }
            return;
        }
        eprintln!("No source available for '{}'", name);
    }

    fn cmd_sexp(&self, name: &str) {
        if name.is_empty() {
            eprintln!("/sexp requires a name");
            return;
        }
        if let Some(view) = self.tc.get_def_codegen(name) {
            if let Some(sexp) = view.sexp {
                println!("{}", sexp);
                return;
            }
        }
        // Check macros
        if let Some(sexp) = self.tc.get_macro_sexp(name) {
            println!("{}", sexp);
            return;
        }
        // Check specializations
        let specs = self.tc.find_specializations(name);
        if !specs.is_empty() {
            for (mangled, view) in &specs {
                if let Some(sexp) = view.sexp {
                    println!("; {}", mangled);
                    println!("{}", sexp);
                }
            }
            return;
        }
        eprintln!("No S-expression available for '{}'", name);
    }

    fn cmd_ast(&self, name: &str) {
        if name.is_empty() {
            eprintln!("/ast requires a name");
            return;
        }
        if let Some(view) = self.tc.get_def_codegen(name) {
            if let Some(defn) = view.defn {
                println!("{}", defn);
                return;
            }
        }
        // Check specializations
        let specs = self.tc.find_specializations(name);
        if !specs.is_empty() {
            for (mangled, view) in &specs {
                if let Some(defn) = view.defn {
                    println!("; {}", mangled);
                    println!("{}", defn);
                }
            }
            return;
        }
        eprintln!("No AST available for '{}'", name);
    }

    fn cmd_clif(&self, name: &str) {
        if name.is_empty() {
            eprintln!("/clif requires a name");
            return;
        }
        // Check if it's an inline primitive
        if let Some(SymbolInfo::InlinePrimitive { .. }) = self.tc.describe_symbol(name) {
            println!("{} is an inline primitive — no generated CLIF IR", name);
            return;
        }
        if let Some(view) = self.tc.get_def_codegen(name) {
            if let Some(ir) = view.clif_ir {
                println!("{}", ir);
                return;
            }
        }
        // Check specializations
        let specs = self.tc.find_specializations(name);
        if !specs.is_empty() {
            for (mangled, view) in &specs {
                if let Some(ir) = view.clif_ir {
                    println!("; CLIF IR for {}", mangled);
                    println!("{}", ir);
                }
            }
            return;
        }
        eprintln!("No CLIF IR available for '{}'", name);
    }

    fn cmd_disasm(&self, name: &str) {
        if name.is_empty() {
            eprintln!("/disasm requires a name");
            return;
        }
        if let Some(SymbolInfo::InlinePrimitive { .. }) = self.tc.describe_symbol(name) {
            println!("{} is an inline primitive — no generated code", name);
            return;
        }
        if let Some(view) = self.tc.get_def_codegen(name) {
            if let Some(asm) = view.disasm {
                println!("{}", asm);
                return;
            }
        }
        // Check specializations
        let specs = self.tc.find_specializations(name);
        if !specs.is_empty() {
            for (mangled, view) in &specs {
                if let Some(asm) = view.disasm {
                    println!("; Disassembly for {}", mangled);
                    println!("{}", asm);
                }
            }
            return;
        }
        eprintln!("No disassembly available for '{}'", name);
    }

    fn cmd_time(&mut self, arg: &str) {
        if arg.is_empty() {
            eprintln!("/time requires an expression");
            return;
        }

        let parse_start = Instant::now();
        let parsed = match parse_repl_input(arg) {
            Ok(ri) => ri,
            Err(e) => {
                eprintln!("{}", format_error(arg, &e));
                return;
            }
        };
        let parse_time = parse_start.elapsed();

        match parsed {
            ReplInput::Expr(expr) => {
                let tc_start = Instant::now();
                let ty = match self.tc.check_expr(&expr) {
                    Ok(t) => t,
                    Err(e) => {
                        eprintln!("{}", format_error(arg, &e));
                        return;
                    }
                };
                let mut method_resolutions = match self.tc.resolve_methods() {
                    Ok(mr) => mr,
                    Err(e) => {
                        eprintln!("{}", format_error(arg, &e));
                        return;
                    }
                };
                if let Err(e) = self.tc.resolve_overloads(&mut method_resolutions) {
                    eprintln!("{}", format_error(arg, &e));
                    return;
                }
                // On-demand monomorphisation
                let et = self.tc.resolve_expr_types();
                match self.tc.monomorphise_all() {
                    Ok((mono_defns, mono_dispatches)) => {
                        method_resolutions.extend(mono_dispatches);
                        if let Err(e) = self.compile_mono_specializations(&mono_defns, &method_resolutions, &et) {
                            eprintln!("{}", format_error(arg, &e));
                            return;
                        }
                    }
                    Err(e) => {
                        eprintln!("{}", format_error(arg, &e));
                        return;
                    }
                }
                let tc_time = tc_start.elapsed();

                let exec_start = Instant::now();
                let fn_slots = self.jit.build_fn_slots_from_modules(&self.tc.modules);
                match self.jit.eval_expr(&expr, &method_resolutions, &et, &fn_slots, &self.tc.modules) {
                    Ok(result) => {
                        let exec_time = exec_start.elapsed();
                        let resolved = self.tc.resolve(&ty);
                        let formatted_type = format_type_for_display(&resolved);
                        let value_str = format_result_value(result, &resolved, &self.tc);
                        println!("{} :: {}", value_str, formatted_type);
                        println!(
                            "  parse: {:.2}ms  typecheck: {:.2}ms  compile+exec: {:.2}ms",
                            parse_time.as_secs_f64() * 1000.0,
                            tc_time.as_secs_f64() * 1000.0,
                            exec_time.as_secs_f64() * 1000.0,
                        );
                    }
                    Err(e) => eprintln!("{}", format_error(arg, &e)),
                }
            }
            _ => eprintln!("/time expects an expression, not a definition"),
        }
    }

    fn print_mem_line(
        prefix: &str,
        allocs: usize,
        deallocs: usize,
        live: usize,
        bytes_current: usize,
        bytes_peak: usize,
        bytes_total: usize,
    ) {
        println!(
            "{}allocs: {}  deallocs: {}  live: {}  bytes: {} current / {} peak / {} total",
            prefix, allocs, deallocs, live, bytes_current, bytes_peak, bytes_total,
        );
    }

    fn cmd_mem(&mut self, arg: &str) {
        if arg.is_empty() {
            Self::print_mem_line(
                "",
                intrinsics::alloc_count(),
                intrinsics::dealloc_count(),
                intrinsics::alloc_count() - intrinsics::dealloc_count(),
                intrinsics::bytes_current(),
                intrinsics::bytes_peak(),
                intrinsics::bytes_allocated(),
            );
            return;
        }

        if arg.trim() == "reset" {
            intrinsics::reset_counts();
            println!("counters reset");
            return;
        }

        // With-expression mode: show base, run expr, show deltas
        let parsed = match parse_repl_input(arg) {
            Ok(ri) => ri,
            Err(e) => {
                eprintln!("{}", format_error(arg, &e));
                return;
            }
        };

        match parsed {
            ReplInput::Expr(expr) => {
                let ty = match self.tc.check_expr(&expr) {
                    Ok(t) => t,
                    Err(e) => {
                        eprintln!("{}", format_error(arg, &e));
                        return;
                    }
                };
                let mut method_resolutions = match self.tc.resolve_methods() {
                    Ok(mr) => mr,
                    Err(e) => {
                        eprintln!("{}", format_error(arg, &e));
                        return;
                    }
                };
                if let Err(e) = self.tc.resolve_overloads(&mut method_resolutions) {
                    eprintln!("{}", format_error(arg, &e));
                    return;
                }
                let et = self.tc.resolve_expr_types();
                match self.tc.monomorphise_all() {
                    Ok((mono_defns, mono_dispatches)) => {
                        method_resolutions.extend(mono_dispatches);
                        if let Err(e) = self.compile_mono_specializations(&mono_defns, &method_resolutions, &et) {
                            eprintln!("{}", format_error(arg, &e));
                            return;
                        }
                    }
                    Err(e) => {
                        eprintln!("{}", format_error(arg, &e));
                        return;
                    }
                }

                let before_alloc = intrinsics::alloc_count();
                let before_dealloc = intrinsics::dealloc_count();
                let before_current = intrinsics::bytes_current();
                let before_peak = intrinsics::bytes_peak();
                let before_total = intrinsics::bytes_allocated();

                Self::print_mem_line(
                    "  before: ",
                    before_alloc,
                    before_dealloc,
                    before_alloc - before_dealloc,
                    before_current,
                    before_peak,
                    before_total,
                );

                let fn_slots = self.jit.build_fn_slots_from_modules(&self.tc.modules);
                match self.jit.eval_expr(&expr, &method_resolutions, &et, &fn_slots, &self.tc.modules) {
                    Ok(result) => {
                        let after_alloc = intrinsics::alloc_count();
                        let after_dealloc = intrinsics::dealloc_count();
                        let after_current = intrinsics::bytes_current();
                        let after_peak = intrinsics::bytes_peak();
                        let after_total = intrinsics::bytes_allocated();

                        let resolved = self.tc.resolve(&ty);
                        let formatted_type = format_type_for_display(&resolved);
                        let value_str = format_result_value(result, &resolved, &self.tc);
                        println!("{} :: {}", value_str, formatted_type);

                        let d_allocs = after_alloc - before_alloc;
                        let d_deallocs = after_dealloc - before_dealloc;
                        let d_live = d_allocs - d_deallocs;
                        let d_current = after_current as isize - before_current as isize;
                        let d_peak = after_peak as isize - before_peak as isize;
                        let d_total = after_total - before_total;
                        println!(
                            "   delta: allocs: {}  deallocs: {}  live: {}  bytes: {:+} current / {:+} peak / +{} total",
                            d_allocs, d_deallocs, d_live, d_current, d_peak, d_total,
                        );
                    }
                    Err(e) => eprintln!("{}", format_error(arg, &e)),
                }
            }
            _ => eprintln!("/mem expects an expression, 'reset', or no argument"),
        }
    }

    fn cmd_list(&mut self, filter: &str) {
        use super::format::format_category;

        // Parse args: "/list", "/list partial", "/list module", "/list module partial"
        let parts: Vec<&str> = filter.split_whitespace().collect();
        let (target_module, partial) = match parts.len() {
            0 => (None, None),
            1 => {
                // Check if it's a loaded module name
                let module_id = crate::module::ModuleFullPath(parts[0].to_string());
                if self.loaded_modules.contains_key(&module_id) {
                    (Some(parts[0]), None)
                } else {
                    (None, Some(parts[0]))
                }
            }
            _ => (Some(parts[0]), Some(parts[1])),
        };

        if let Some(partial) = partial {
            // Filtered: show matching symbols with full type info
            self.cmd_list_filtered(target_module, partial);
            return;
        }

        // Show module contents if a specific module is targeted
        if let Some(mod_name) = target_module {
            self.cmd_list_module(mod_name);
            return;
        }

        // Show only symbols defined in current module
        let symbols = self.tc.list_symbols();

        let mut types = Vec::new();
        let mut traits = Vec::new();
        let mut macros = Vec::new();
        let mut fns = Vec::new();

        for (name, info) in &symbols {
            let is_import = self.tc.is_import_in_current_module(name);
            if is_import {
                continue;
            }
            match info {
                SymbolInfo::TypeName { .. } | SymbolInfo::UserType { .. } => {
                    types.push(name.as_str())
                }
                SymbolInfo::TraitDecl(_, _) => traits.push(name.as_str()),
                SymbolInfo::Macro { name: n, .. } => macros.push(*n),
                SymbolInfo::Ambiguous { .. } => {}
                _ => fns.push(name.as_str()),
            }
        }

        // Collect loaded module names
        let mut module_names: Vec<&str> = self
            .loaded_modules
            .keys()
            .filter(|id| !self.prelude_module_ids.contains(id.as_ref()))
            .map(|id| id.0.as_str())
            .collect();
        module_names.sort();

        // Collect platform declarations from current module
        let mut platform_names: Vec<String> = Vec::new();
        if let Some(cm) = self.tc.modules.get(&self.current_module) {
            for entry in cm.symbols.values() {
                if let crate::module::ModuleEntry::PlatformDecl {
                    platform_module, ..
                } = entry
                {
                    let name = platform_module
                        .0
                        .strip_prefix("platform.")
                        .unwrap_or(&platform_module.0);
                    platform_names.push(name.to_string());
                }
            }
        }
        platform_names.sort();
        let platform_refs: Vec<&str> = platform_names.iter().map(|s| s.as_str()).collect();

        let categories: &[(&str, &[&str])] = &[
            ("Modules", &module_names),
            ("Platforms", &platform_refs),
            ("Macros", &macros),
            ("Traits", &traits),
            ("Types", &types),
            ("Fns", &fns),
        ];

        for (label, names) in categories {
            if !names.is_empty() {
                println!("{}", format_category(label, names));
            }
        }
    }

    fn cmd_imports(&mut self, filter: &str) {
        use super::format::format_category;

        if !filter.is_empty() {
            // Filtered: show matching imported symbols with full type info
            self.cmd_list_filtered(None, filter);
            return;
        }

        let symbols = self.tc.list_symbols();

        let mut types = Vec::new();
        let mut traits = Vec::new();
        let mut macros = Vec::new();
        let mut imports = Vec::new();

        for (name, info) in &symbols {
            let is_import = self.tc.is_import_in_current_module(name);
            if !is_import {
                continue;
            }
            match info {
                SymbolInfo::TypeName { .. } | SymbolInfo::UserType { .. } => {
                    types.push(name.as_str())
                }
                SymbolInfo::TraitDecl(_, _) => traits.push(name.as_str()),
                SymbolInfo::Macro { name: n, .. } => macros.push(*n),
                SymbolInfo::Ambiguous { .. } => {}
                _ => imports.push(name.as_str()),
            }
        }

        let specials: Vec<&str> = special_form_names(&self.tc);

        let categories: &[(&str, &[&str])] = &[
            ("Special forms", &specials),
            ("Macros", &macros),
            ("Traits", &traits),
            ("Types", &types),
            ("Fns", &imports),
        ];

        for (label, names) in categories {
            if !names.is_empty() {
                println!("{}", format_category(label, names));
            }
        }
    }

    fn cmd_list_module(&self, module_name: &str) {
        let public_names = self.tc.get_module_public_names(module_name);
        if public_names.is_empty() {
            println!("Module '{}' has no public symbols", module_name);
            return;
        }
        println!("Module '{}':", module_name);
        for name in &public_names {
            let qualified = format!("{}/{}", module_name, name);
            if let Some(info) = self.tc.describe_symbol(&qualified) {
                println!("  {}", format_symbol_info(name, &info));
            } else {
                println!("  {}", name);
            }
        }
    }

    fn cmd_list_filtered(&self, target_module: Option<&str>, partial: &str) {
        let filter_lower = partial.to_lowercase();
        let mut found = false;

        if target_module.is_none() {
            // Check special forms
            let all_specials = special_form_names(&self.tc);
            let mut matching_specials: Vec<&str> = all_specials
                .iter()
                .filter(|n| n.to_lowercase().contains(&filter_lower))
                .copied()
                .collect();
            matching_specials.sort();
            for name in &matching_specials {
                if let Some(desc) = special_form_description(&self.tc, name) {
                    println!("  {}", desc);
                    found = true;
                }
            }
        }

        // Check symbols (from target module or current module)
        if let Some(mod_name) = target_module {
            let public_names = self.tc.get_module_public_names(mod_name);
            for name in &public_names {
                if name.to_lowercase().contains(&filter_lower) {
                    let qualified = format!("{}/{}", mod_name, name);
                    if let Some(info) = self.tc.describe_symbol(&qualified) {
                        println!("  {}", format_symbol_info(name, &info));
                        found = true;
                    }
                }
            }
        } else {
            let symbols = self.tc.list_symbols();
            for (name, info) in &symbols {
                if name.to_lowercase().contains(&filter_lower) {
                    let qualified = self.tc.qualified_name(name).to_string();
                    let display: &str = match info {
                        SymbolInfo::UserFn { .. }
                        | SymbolInfo::ConstrainedFn { .. }
                        | SymbolInfo::OverloadedFn { .. }
                        | SymbolInfo::InlinePrimitive { .. }
                        | SymbolInfo::ExternPrimitive { .. } => &qualified,
                        _ => name.as_str(),
                    };
                    println!("  {}", format_symbol_info(display, info));
                    found = true;
                }
            }
        }

        if !found {
            println!("No symbols matching '{}'", partial);
        }
    }

    fn cmd_mod(&mut self, arg: &str) {
        use crate::module::ModuleFullPath;

        let target = if arg.is_empty() {
            ModuleFullPath("user".to_string())
        } else {
            let target = ModuleFullPath(arg.to_string());
            // Load if not already loaded
            if !self.loaded_modules.contains_key(&target) {
                match self.load_module_by_name(arg) {
                    Ok(()) => {}
                    Err(e) => {
                        eprintln!("{}", e);
                        return;
                    }
                }
            }
            target
        };

        if target == self.current_module {
            return;
        }

        // Leave current module scope: clear import tracking
        self.tc.end_module_scope();

        self.current_module = target.clone();
        self.tc.set_current_module_path(target);
    }

    fn cmd_expand(&self, arg: &str) {
        if arg.is_empty() {
            eprintln!("/expand requires a form");
            return;
        }
        let sexps = match crate::sexp::parse_sexps(arg) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("{}", format_error(arg, &e));
                return;
            }
        };
        for sexp in sexps {
            match crate::macro_expand::expand_sexp(sexp, &self.macro_env, 0) {
                Ok(expanded) => println!("{}", expanded),
                Err(e) => eprintln!("{}", format_error(arg, &e)),
            }
        }
    }

    fn cmd_exe(&mut self, arg: &str) {
        // Determine output path: use arg if given, else place next to current module file
        let output_path = if arg.is_empty() {
            // Derive from current module's file path: same dir, same stem, no extension
            match self
                .tc
                .modules
                .get(&self.current_module)
                .and_then(|cm| cm.file_path.as_ref())
            {
                Some(file_path) => file_path.with_extension(""),
                None => {
                    eprintln!("Current module has no backing file — specify an output path: /exe <path>");
                    return;
                }
            }
        } else {
            std::path::PathBuf::from(arg)
        };

        // Save all loaded modules to ensure cache is up-to-date
        self.save_current_module();

        // Collect all module .o file paths from cache
        let lib_dir = crate::module::find_lib_dir(&self.project_root);
        let project_cache_dir = crate::cache::cache_dir(&self.project_root);
        let lib_cache_dir = lib_dir.as_ref().map(|ld| crate::cache::cache_dir(ld));

        let mut module_o_paths: Vec<std::path::PathBuf> = Vec::new();
        for module_id in self.loaded_modules.keys() {
            let mod_path = crate::module::ModuleFullPath::from(module_id.short_name());

            // Determine if this is a lib module
            let is_lib = lib_dir.as_ref().is_some_and(|ld| {
                self.tc
                    .modules
                    .get(&mod_path)
                    .and_then(|cm| cm.file_path.as_ref())
                    .is_some_and(|fp| fp.starts_with(ld))
            });

            let target_cache = if is_lib {
                lib_cache_dir.as_ref().unwrap_or(&project_cache_dir).clone()
            } else {
                project_cache_dir.clone()
            };

            let o_path = target_cache.join(format!(
                "{}.o",
                crate::cache::module_file_name(&mod_path)
            ));
            if o_path.exists() {
                module_o_paths.push(o_path);
            }
        }

        if module_o_paths.is_empty() {
            eprintln!("No compiled modules found — nothing to link");
            return;
        }

        // Generate startup stub into project cache dir
        let platform_manifests =
            crate::exe::collect_platform_manifest_names(&self.tc.modules);
        let startup_bytes = match crate::exe::generate_startup_object(&platform_manifests) {
            Ok(b) => b,
            Err(e) => {
                eprintln!("Error generating startup: {}", e);
                return;
            }
        };
        let entry_name = crate::cache::module_file_name(&self.current_module);
        let startup_o = project_cache_dir.join(format!("{}-startup.o", entry_name));
        if let Err(e) = std::fs::write(&startup_o, &startup_bytes) {
            eprintln!("Error writing startup.o: {}", e);
            return;
        }

        // Find the runtime bundle .a
        let bundle_path = match crate::exe::find_bundle_lib() {
            Ok(p) => p,
            Err(e) => {
                eprintln!("Error finding runtime bundle: {}", e);
                return;
            }
        };

        // Find platform rlibs from loaded modules
        let platform_rlibs = crate::exe::find_platform_rlibs(&self.tc.modules);

        // Link
        match crate::exe::link_executable(
            &output_path,
            &module_o_paths,
            &startup_o,
            &bundle_path,
            &platform_rlibs,
        ) {
            Ok(()) => {
                eprintln!("; Wrote executable: {}", output_path.display());
            }
            Err(e) => {
                eprintln!("Error linking executable: {}", e);
            }
        }
    }

    fn print_jit_info_view(view: &crate::typechecker::DefCodegenView<'_>) {
        if let Some(src) = view.source {
            println!("  source: {}", src);
        }
        let size_str = view
            .code_size
            .map(|s| format!("{} bytes", s))
            .unwrap_or_else(|| "?".to_string());
        let time_str = view
            .compile_duration
            .map(|d| format!("{:.2}ms", d.as_secs_f64() * 1000.0))
            .unwrap_or_else(|| "?".to_string());
        println!("  code: {}, compiled in {}", size_str, time_str);
    }
}
