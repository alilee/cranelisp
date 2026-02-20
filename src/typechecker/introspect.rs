use std::collections::HashSet;
use std::time::Duration;

use super::{PrimitiveKind, SymbolInfo, TypeChecker};
use crate::ast::Defn;
use crate::module::{DefCodegen, DefKind, ModuleEntry};
use crate::names::split_dotted;
use crate::sexp::Sexp;
use crate::types::{Scheme, Type};

/// Convert a DefCodegen reference to a lightweight DefCodegenView borrow.
fn codegen_view(cg: &DefCodegen) -> DefCodegenView<'_> {
    DefCodegenView {
        source: cg.source.as_deref(),
        sexp: cg.sexp.as_ref(),
        defn: cg.defn.as_ref(),
        clif_ir: cg.clif_ir.as_deref(),
        disasm: cg.disasm.as_deref(),
        code_size: cg.code_size,
        compile_duration: cg.compile_duration,
        got_slot: cg.got_slot,
        code_ptr: cg.code_ptr,
        param_count: cg.param_count,
    }
}

/// Lightweight borrow of codegen fields from a CompiledModule Def entry.
pub struct DefCodegenView<'a> {
    pub source: Option<&'a str>,
    pub sexp: Option<&'a Sexp>,
    pub defn: Option<&'a Defn>,
    pub clif_ir: Option<&'a str>,
    pub disasm: Option<&'a str>,
    pub code_size: Option<usize>,
    pub compile_duration: Option<Duration>,
    pub got_slot: Option<usize>,
    pub code_ptr: Option<*const u8>,
    pub param_count: Option<usize>,
}

/// Returns true if the name is an internal/mangled name that should be hidden from listings.
fn is_internal_name(name: &str) -> bool {
    name.contains('$') || (name.starts_with("__") && name.ends_with("__"))
}

impl TypeChecker {
    /// Describe a symbol for REPL display. Returns None if not a known symbol.
    pub fn describe_symbol(&self, name: &str) -> Option<SymbolInfo<'_>> {
        // 1. Dotted name? Resolve Type.Constructor or Trait.method
        if let Some((parent, member)) = split_dotted(name) {
            if let Some(td) = self.resolve_type_def_via_modules(parent) {
                if td.constructors.iter().any(|c| c.name == member) {
                    return self.describe_symbol(member);
                }
                return None;
            }
            if self.find_trait_decl(parent).is_some() {
                if self.find_trait_for_method(member) == Some(parent) {
                    return self.describe_symbol(member);
                }
                return None;
            }
            return None;
        }

        // 2. User-defined type? (TypeDef entries are in symbols; check before
        //    entry-based classification so product types show as UserType)
        if let Some(type_def) = self.resolve_type_def_via_modules(name) {
            return Some(SymbolInfo::UserType { type_def });
        }

        // 3. Builtin type? (Int, Bool, String, Float — have trait impls)
        if let Some(impls) = self.impls_for_type(name) {
            return Some(SymbolInfo::TypeName { impls });
        }

        // 3b. Ambiguous bare name?
        if let Some(entry) =
            self.resolve_entry_in_module(&self.current_module_path, name, 0, false)
        {
            if matches!(entry, ModuleEntry::Ambiguous) {
                let alts = self.find_ambiguous_alternatives(name);
                return Some(SymbolInfo::Ambiguous { alternatives: alts });
            }
        }

        // 4. Entry-based classification via module-walk
        let entry = match self.lookup_entry_via_modules(name) {
            Some(e) => e,
            None => {
                // Fallback: overloaded functions may exist in overloads but not in modules
                // (e.g., during REPL DefnMulti before track_repl_defn)
                if self.overloads.contains_key(name) {
                    let schemes: Vec<&Scheme> =
                        if let Some(resolved) = self.resolved_overloads.get(name) {
                            resolved
                                .iter()
                                .filter_map(|(_, _, mangled)| self.lookup(mangled.as_str()))
                                .collect()
                        } else {
                            Vec::new()
                        };
                    return Some(SymbolInfo::OverloadedFn { schemes });
                }
                return None;
            }
        };
        match entry {
            ModuleEntry::TraitDecl { decl, .. } => {
                let impl_types = self.impls_for_trait(name);
                Some(SymbolInfo::TraitDecl(decl, impl_types))
            }
            ModuleEntry::Constructor {
                type_name, scheme, ..
            } => Some(SymbolInfo::Constructor {
                type_name,
                scheme,
            }),
            ModuleEntry::Def {
                kind: DefKind::Primitive { primitive_kind: PrimitiveKind::Inline, .. },
                scheme,
                ..
            } => Some(SymbolInfo::InlinePrimitive { scheme }),
            ModuleEntry::Def {
                kind: DefKind::Primitive { primitive_kind: PrimitiveKind::Extern | PrimitiveKind::Platform, .. },
                scheme,
                ..
            } => {
                Some(SymbolInfo::ExternPrimitive { scheme })
            }
            ModuleEntry::Def {
                kind: DefKind::UserFn { constrained_fn: Some(_), .. },
                scheme,
                ..
            } => Some(SymbolInfo::ConstrainedFn { scheme }),
            ModuleEntry::Def { scheme, .. } => {
                // Trait method (including operators)?
                if let Some(trait_name) = self.find_trait_for_method(name) {
                    if let Some(decl) = self.find_trait_decl(trait_name) {
                        if let Some(sig) = decl.methods.iter().find(|m| m.name == name) {
                            return Some(SymbolInfo::TraitMethod {
                                trait_name,
                                sig,
                                type_params: &decl.type_params,
                            });
                        }
                    }
                }
                // Overloaded (multi-sig) function?
                if self.overloads.contains_key(name) {
                    let schemes: Vec<&Scheme> =
                        if let Some(resolved) = self.resolved_overloads.get(name) {
                            resolved
                                .iter()
                                .filter_map(|(_, _, mangled)| self.lookup(mangled.as_str()))
                                .collect()
                        } else {
                            Vec::new()
                        };
                    return Some(SymbolInfo::OverloadedFn { schemes });
                }
                // Plain user function?
                if matches!(scheme.ty, Type::Fn(_, _)) {
                    Some(SymbolInfo::UserFn { scheme })
                } else {
                    // Builtin type placeholder (Vec) or other non-function Def
                    None
                }
            }
            ModuleEntry::Macro {
                name,
                fixed_params,
                rest_param,
                docstring,
                ..
            } => Some(SymbolInfo::Macro {
                name,
                fixed_params,
                rest_param: rest_param.as_deref(),
                docstring: docstring.as_deref(),
            }),
            // Import/Reexport: resolve_entry_in_module should have followed the chain
            // TypeDef in symbols: handled by resolve_type_def_via_modules above
            _ => None,
        }
    }

    /// Enumerate all in-scope symbols for REPL listing.
    /// Walks the current module's `symbols` (defs, imports, constructors, traits, type defs).
    /// Returns (name, SymbolInfo) pairs sorted alphabetically.
    pub fn list_symbols(&self) -> Vec<(String, SymbolInfo<'_>)> {
        let mut seen = HashSet::new();
        let mut results = Vec::new();

        if let Some(cm) = self.modules.get(self.current_module_path.as_ref()) {
            for name in cm.symbols.keys() {
                let name_str = name.to_string();
                if !is_internal_name(&name_str)
                    && !name_str.contains('/')
                    && seen.insert(name_str.clone())
                {
                    if let Some(info) = self.describe_symbol(&name_str) {
                        results.push((name_str, info));
                    }
                }
            }
        }

        results.sort_by_key(|(a, _)| a.to_lowercase());
        results
    }

    /// Check if a name is an import/reexport in the current module (before chain-following).
    pub fn is_import_in_current_module(&self, name: &str) -> bool {
        if let Some(cm) = self.modules.get(self.current_module_path.as_ref()) {
            if let Some(entry) = cm.get(name) {
                return matches!(
                    entry,
                    ModuleEntry::Import { .. } | ModuleEntry::Reexport { .. }
                );
            }
        }
        false
    }

    /// Collect implementing type names for a given trait.
    fn impls_for_trait(&self, trait_name: &str) -> Vec<String> {
        let mut seen = Vec::new();
        for ui in self.all_impls() {
            if ui.trait_name == trait_name {
                let formatted = if ui.type_args.is_empty() {
                    ui.target_type.clone()
                } else {
                    let args: Vec<String> = ui
                        .type_args
                        .iter()
                        .map(|a| {
                            // Check if this arg has a constraint
                            if let Some((_, trait_c)) =
                                ui.type_constraints.iter().find(|(v, _)| v == a)
                            {
                                format!(":{} {}", trait_c, a)
                            } else {
                                a.clone()
                            }
                        })
                        .collect();
                    format!("({} {})", ui.target_type, args.join(" "))
                };
                if !seen.contains(&formatted) {
                    seen.push(formatted);
                }
            }
        }
        seen
    }

    /// Look up a Def entry's codegen fields by name (module-walk resolution).
    pub fn get_def_codegen(&self, name: &str) -> Option<DefCodegenView<'_>> {
        // Try current module first, then walk all modules
        for cm in self.modules.values() {
            if let Some(ModuleEntry::Def {
                kind: DefKind::UserFn { codegen, .. },
                ..
            }) = cm.get(name)
            {
                return Some(codegen_view(codegen));
            }
        }
        None
    }

    /// Find specializations (mangled names matching `prefix$*`) across all modules.
    pub fn find_specializations(&self, prefix: &str) -> Vec<(String, DefCodegenView<'_>)> {
        let needle = format!("{}$", prefix);
        let mut results = Vec::new();
        for cm in self.modules.values() {
            for (sym, entry) in &cm.symbols {
                if sym.starts_with(&needle) {
                    if let ModuleEntry::Def {
                        kind: DefKind::UserFn { codegen, .. },
                        ..
                    } = entry
                    {
                        results.push((sym.to_string(), codegen_view(codegen)));
                    }
                }
            }
        }
        results
    }

    /// Get macro sexp by name (searching across all modules).
    pub fn get_macro_sexp(&self, name: &str) -> Option<&Sexp> {
        for cm in self.modules.values() {
            if let Some(ModuleEntry::Macro { sexp, .. }) = cm.get(name) {
                return sexp.as_ref();
            }
        }
        None
    }

    /// Get macro source text by name (searching across all modules).
    pub fn get_macro_source(&self, name: &str) -> Option<&str> {
        for cm in self.modules.values() {
            if let Some(ModuleEntry::Macro { source, .. }) = cm.get(name) {
                return source.as_deref();
            }
        }
        None
    }

    /// Collect trait names implemented for a given type name.
    /// Works for both builtin types (Int, Bool, String, Float) and user ADTs.
    pub(crate) fn impls_for_type(&self, type_name: &str) -> Option<Vec<&str>> {
        // Check if type exists: builtin types or ADTs
        match type_name {
            "Int" | "Bool" | "String" | "Float" => {}
            _ => {
                // Only return impls if this is a known type
                self.resolve_type_def_via_modules(type_name)?;
            }
        }
        let mut traits: Vec<&str> = Vec::new();
        for ui in self.all_impls() {
            if ui.target_type == type_name && !traits.contains(&ui.trait_name.as_str()) {
                traits.push(&ui.trait_name);
            }
        }
        Some(traits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;
    use crate::ast_builder::parse_program;

    const PRELUDE: &str = include_str!("../unittest_prelude.cl");

    fn tc_with_prelude() -> TypeChecker {
        let mut tc = TypeChecker::new();
        tc.init_builtins();
        tc.install_synthetic_bare_names();
        let prelude_program = parse_program(PRELUDE).unwrap();
        // Register type definitions first
        for item in &prelude_program {
            if matches!(item, TopLevel::TypeDef { .. }) {
                tc.register_type_def(item);
            }
        }
        for item in &prelude_program {
            match item {
                TopLevel::TraitDecl(td) => {
                    tc.register_trait_public(td);
                }
                TopLevel::TraitImpl(ti) => {
                    tc.validate_impl_public(ti).unwrap();
                    tc.register_impl(ti);
                    for method in &ti.methods {
                        let mangled = Defn {
                            visibility: crate::ast::Visibility::Public,
                            name: format!("{}${}", method.name, ti.target_type),
                            docstring: None,
                            params: method.params.clone(),
                            param_annotations: method.param_annotations.clone(),
                            body: method.body.clone(),
                            span: method.span,
                        };
                        tc.check_defn(&mangled).unwrap();
                    }
                }
                _ => {}
            }
        }
        tc
    }

    #[test]
    fn describe_symbol_trait_decl() {
        let tc = tc_with_prelude();
        match tc.describe_symbol("Display") {
            Some(SymbolInfo::TraitDecl(decl, impl_types)) => {
                assert_eq!(decl.name, "Display");
                assert!(impl_types.contains(&"Int".to_string()));
                assert!(impl_types.contains(&"Bool".to_string()));
                assert!(impl_types.contains(&"String".to_string()));
                assert!(impl_types.contains(&"Float".to_string()));
            }
            other => panic!("expected TraitDecl, got {:?}", other.is_some()),
        }
        match tc.describe_symbol("Num") {
            Some(SymbolInfo::TraitDecl(decl, impl_types)) => {
                assert_eq!(decl.name, "Num");
                assert!(impl_types.contains(&"Int".to_string()));
                assert!(impl_types.contains(&"Float".to_string()));
            }
            other => panic!("expected TraitDecl, got {:?}", other.is_some()),
        }
    }

    #[test]
    fn describe_symbol_type_name() {
        let tc = tc_with_prelude();
        match tc.describe_symbol("Int") {
            Some(SymbolInfo::TypeName { impls }) => {
                assert!(impls.contains(&"Display"));
                assert!(impls.contains(&"Num"));
                assert!(impls.contains(&"Eq"));
                assert!(impls.contains(&"Ord"));
            }
            other => panic!("expected TypeName, got {:?}", other.is_some()),
        }
        match tc.describe_symbol("Bool") {
            Some(SymbolInfo::TypeName { impls }) => {
                assert!(impls.contains(&"Display"));
            }
            other => panic!("expected TypeName, got {:?}", other.is_some()),
        }
    }

    #[test]
    fn describe_symbol_inline_primitive() {
        let tc = tc_with_prelude();
        match tc.describe_symbol("add-i64") {
            Some(SymbolInfo::InlinePrimitive { scheme }) => {
                assert!(format!("{}", scheme.ty).contains("Int"));
            }
            other => panic!("expected InlinePrimitive, got {:?}", other.is_some()),
        }
        match tc.describe_symbol("eq-i64") {
            Some(SymbolInfo::InlinePrimitive { scheme }) => {
                assert!(format!("{}", scheme.ty).contains("Int"));
            }
            other => panic!("expected InlinePrimitive, got {:?}", other.is_some()),
        }
    }

    #[test]
    fn describe_symbol_trait_method() {
        let tc = tc_with_prelude();
        match tc.describe_symbol("show") {
            Some(SymbolInfo::TraitMethod {
                trait_name, sig, ..
            }) => {
                assert_eq!(trait_name, "Display");
                assert_eq!(sig.name, "show");
            }
            other => panic!("expected TraitMethod, got {:?}", other.is_some()),
        }
    }

    #[test]
    fn describe_symbol_unknown() {
        let tc = tc_with_prelude();
        assert!(tc.describe_symbol("nonexistent").is_none());
    }

    #[test]
    fn describe_symbol_operator_plus() {
        let tc = tc_with_prelude();
        match tc.describe_symbol("+") {
            Some(SymbolInfo::TraitMethod {
                trait_name, sig, ..
            }) => {
                assert_eq!(trait_name, "Num");
                assert_eq!(sig.name, "+");
            }
            other => panic!("expected TraitMethod, got {:?}", other.is_some()),
        }
    }

    #[test]
    fn describe_symbol_operator_eq() {
        let tc = tc_with_prelude();
        match tc.describe_symbol("=") {
            Some(SymbolInfo::TraitMethod {
                trait_name, sig, ..
            }) => {
                assert_eq!(trait_name, "Eq");
                assert_eq!(sig.name, "=");
            }
            other => panic!("expected TraitMethod, got {:?}", other.is_some()),
        }
    }

    #[test]
    fn describe_symbol_operator_lt() {
        let tc = tc_with_prelude();
        match tc.describe_symbol("<") {
            Some(SymbolInfo::TraitMethod {
                trait_name, sig, ..
            }) => {
                assert_eq!(trait_name, "Ord");
                assert_eq!(sig.name, "<");
            }
            other => panic!("expected TraitMethod, got {:?}", other.is_some()),
        }
    }

    #[test]
    fn describe_symbol_user_fn() {
        let mut tc = tc_with_prelude();
        let defn = crate::ast_builder::parse_repl_input("(defn foo [x] x)").unwrap();
        if let crate::ast::ReplInput::Defn(d) = defn {
            tc.check_defn(&d).unwrap();
        }
        match tc.describe_symbol("foo") {
            Some(SymbolInfo::UserFn { scheme }) => {
                assert!(matches!(scheme.ty, Type::Fn(_, _)));
            }
            other => panic!("expected UserFn, got {:?}", other.is_some()),
        }
    }

    #[test]
    fn describe_symbol_extern_primitive() {
        let tc = tc_with_prelude();
        match tc.describe_symbol("int-to-string") {
            Some(SymbolInfo::ExternPrimitive { scheme }) => {
                assert!(format!("{}", scheme.ty).contains("String"));
            }
            other => panic!("expected ExternPrimitive, got {:?}", other.is_some()),
        }
    }

    #[test]
    fn describe_symbol_constructor() {
        let tc = tc_with_prelude();
        match tc.describe_symbol("Some") {
            Some(SymbolInfo::Constructor { type_name, .. }) => {
                assert_eq!(type_name, "Option");
            }
            other => panic!("expected Constructor, got {:?}", other.is_some()),
        }
        match tc.describe_symbol("None") {
            Some(SymbolInfo::Constructor { type_name, .. }) => {
                assert_eq!(type_name, "Option");
            }
            other => panic!("expected Constructor, got {:?}", other.is_some()),
        }
    }

    #[test]
    fn describe_symbol_user_type() {
        let tc = tc_with_prelude();
        match tc.describe_symbol("Option") {
            Some(SymbolInfo::UserType { type_def }) => {
                assert_eq!(type_def.name, "Option");
                assert_eq!(type_def.constructors.len(), 2);
            }
            other => panic!("expected UserType, got {:?}", other.is_some()),
        }
    }

    #[test]
    fn describe_symbol_ambiguous_trait_method() {
        let mut tc = tc_with_prelude();
        // Define a second trait with the same method name as Display's "show"
        let src = r#"(deftrait Debug (show [self] String))"#;
        let items = parse_program(src).unwrap();
        for item in &items {
            if let TopLevel::TraitDecl(td) = item {
                tc.register_trait_public(td);
            }
        }
        // Bare "show" should now be ambiguous
        match tc.describe_symbol("show") {
            Some(SymbolInfo::Ambiguous { alternatives }) => {
                assert!(
                    alternatives.contains(&"Debug.show".to_string()),
                    "should list Debug.show, got: {:?}",
                    alternatives
                );
                assert!(
                    alternatives.contains(&"Display.show".to_string()),
                    "should list Display.show, got: {:?}",
                    alternatives
                );
            }
            other => panic!("expected Ambiguous, got {}", if other.is_some() { "Some(other)" } else { "None" }),
        }
    }
}
