mod adt;
mod inference;
mod introspect;
mod mono;
mod overloads;
mod primitives;
mod program;
mod traits;
mod unification;

pub(crate) use unification::{has_type_var, substitute_vars};
pub use introspect::DefCodegenView;

use std::collections::{HashMap, HashSet};

use serde::{Deserialize, Serialize};

use crate::ast::*;
use crate::error::{CranelispError, Span};
use crate::module::{CompiledModule, ModuleEntry};
use crate::names::{FQSymbol, ModuleFullPath, Symbol};
use crate::types::*;

/// Check if a name consists entirely of operator characters (matches the grammar's `operator_char` rule).
pub fn is_operator_name(name: &str) -> bool {
    !name.is_empty() && name.chars().all(|c| matches!(c, '+' | '-' | '*' | '/' | '=' | '<' | '>'))
}

/// Result of resolving a call to a concrete implementation.
#[derive(Debug, Clone)]
pub enum ResolvedCall {
    TraitMethod {
        mangled_name: String,
    },
    SigDispatch {
        mangled_name: String,
    },
    AutoCurry {
        target_name: String,
        applied_count: usize,
        total_count: usize,
    },
    /// A call to a builtin function (extern primitive or platform function).
    /// Resolved by looking up the FQSymbol's module entry for its FuncId.
    BuiltinFn(crate::names::FQSymbol),
}

/// Method resolution table: maps expression spans to resolved calls.
pub type MethodResolutions = HashMap<Span, ResolvedCall>;

/// Describes what a symbol refers to in the REPL.
pub enum SymbolInfo<'a> {
    /// A trait declaration (e.g., `Display`, `Num`) with implementing types.
    TraitDecl(&'a TraitDecl, Vec<String>),
    /// A type name (e.g., `Int`, `Bool`, `String`) with its trait impls.
    TypeName { impls: Vec<&'a str> },
    /// A trait method (regular or operator) callable by name (e.g., `show`, `fmap`, `+`, `=`).
    TraitMethod {
        trait_name: &'a str,
        sig: &'a TraitMethodSig,
        type_params: &'a [String],
    },
    /// An inline primitive function (e.g., `add-i64`, `eq-i64`).
    InlinePrimitive { scheme: &'a Scheme },
    /// An extern primitive function (e.g., `int-to-string`, `vec-get`).
    ExternPrimitive { scheme: &'a Scheme },
    /// A constrained polymorphic function (e.g., `(defn foo [x y] (+ x y))`).
    ConstrainedFn { scheme: &'a Scheme },
    /// An overloaded (multi-sig) function (e.g., `(defn bar ([x] ...) ([x y] ...))`).
    OverloadedFn { schemes: Vec<&'a Scheme> },
    /// A data/nullary constructor (e.g., `Some`, `None`, `Point`).
    Constructor {
        type_name: &'a str,
        scheme: &'a Scheme,
    },
    /// A user-defined type (e.g., `Point`, `Option`).
    UserType { type_def: &'a TypeDefInfo },
    /// A plain user-defined function (e.g., `(defn foo [x] x)`).
    UserFn { scheme: &'a Scheme },
    /// A macro definition (e.g., `(defmacro list [& args] ...)`).
    Macro {
        name: &'a str,
        fixed_params: &'a [String],
        rest_param: Option<&'a str>,
        docstring: Option<&'a str>,
    },
    /// A bare name that became ambiguous (two different sources registered it).
    Ambiguous { alternatives: Vec<String> },
}

/// Information about a single constructor in a type definition.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstructorInfo {
    pub name: String,
    pub tag: usize,
    pub fields: Vec<(String, Type)>, // (field_name, field_type) — type may contain Var
    pub docstring: Option<String>,
}

/// Information about a type definition (deftype).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeDefInfo {
    pub name: String,
    pub type_params: Vec<TypeId>, // fresh type variable IDs for a, b, etc.
    pub constructors: Vec<ConstructorInfo>,
    pub docstring: Option<String>,
}

/// Classification of built-in primitive functions.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub enum PrimitiveKind {
    /// Inline Cranelift IR (add-i64, eq-i64, etc.)
    Inline,
    /// Rust FFI calls (int-to-string, vec-get, etc.)
    Extern,
    /// Platform effects (print, read-line)
    Platform,
}

/// Unified metadata for all named symbols.
/// SpecialForm and Primitive variants require docstrings (String, not Option);
/// UserFn allows optional docstrings. The Rust compiler enforces that every
/// built-in symbol is registered with documentation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SymbolMeta {
    /// Special forms (if, let, defn, mod, import, export...).
    SpecialForm {
        description: String,
        docstring: String,
    },
    /// Built-in primitives (inline, extern, platform).
    Primitive {
        kind: PrimitiveKind,
        docstring: String,
        param_names: Vec<String>,
    },
    /// User-defined functions.
    UserFn {
        docstring: Option<String>,
        param_names: Vec<String>,
    },
}

impl SymbolMeta {
    pub fn docstring(&self) -> Option<&str> {
        match self {
            SymbolMeta::SpecialForm { docstring, .. } => Some(docstring),
            SymbolMeta::Primitive { docstring, .. } => Some(docstring),
            SymbolMeta::UserFn { docstring, .. } => docstring.as_deref(),
        }
    }

    pub fn param_names(&self) -> &[String] {
        match self {
            SymbolMeta::SpecialForm { .. } => &[],
            SymbolMeta::Primitive { param_names, .. } => param_names,
            SymbolMeta::UserFn { param_names, .. } => param_names,
        }
    }

    pub fn is_inline_primitive(&self) -> bool {
        matches!(
            self,
            SymbolMeta::Primitive {
                kind: PrimitiveKind::Inline,
                ..
            }
        )
    }

    pub fn is_extern_primitive(&self) -> bool {
        matches!(
            self,
            SymbolMeta::Primitive {
                kind: PrimitiveKind::Extern,
                ..
            }
        )
    }

    pub fn is_special_form(&self) -> bool {
        matches!(self, SymbolMeta::SpecialForm { .. })
    }

    pub fn special_form_description(&self) -> Option<&str> {
        match self {
            SymbolMeta::SpecialForm { description, .. } => Some(description),
            _ => None,
        }
    }
}

pub struct TypeChecker {
    next_id: TypeId,
    subst: Subst,
    /// Local environment: function params, let bindings, match vars.
    local_env: HashMap<Symbol, Scheme>,
    /// Pending method resolution records: (span, method_name, arg_type).
    pending_resolutions: Vec<(Span, String, Type)>,
    /// Overloaded function registry: base name → [(internal_name, param_count)].
    overloads: HashMap<String, Vec<(String, usize)>>,
    /// Concrete signatures discovered after checking variant bodies.
    /// base name → [(param_types, return_type, mangled_name)]
    resolved_overloads: HashMap<String, Vec<(Vec<Type>, Type, String)>>,
    /// Pending overload resolutions: (span, base_name, arg_types, return_type_var).
    pending_overload_resolutions: Vec<(Span, String, Vec<Type>, Type)>,
    /// Pending auto-curry resolutions: (span, callee_name, applied_count, total_count).
    pending_auto_curry: Vec<(Span, String, usize, usize)>,
    /// Constraints on type variables: var_id → {trait_names}.
    var_constraints: HashMap<TypeId, HashSet<String>>,
    /// Deferred pending resolutions that couldn't be resolved (var had multiple impls).
    deferred_resolutions: Vec<(Span, String, Type)>,
    /// Calls to constrained functions: (call_span, fn_name, arg_types).
    pending_mono_calls: Vec<(Span, String, Vec<Type>)>,
    /// Already-generated specialization mangled names.
    generated_specializations: HashSet<String>,
    /// Expression type map: records the inferred type of each expression by span.
    /// Types may contain unresolved type variables; resolve through subst before use.
    pub expr_types: HashMap<Span, Type>,
    /// Builtin function resolutions: maps call-site spans to BuiltinFn resolutions.
    /// Populated during inference for extern/platform primitive calls.
    builtin_resolutions: HashMap<Span, ResolvedCall>,
    /// Track which module names have been compiled (for error messages).
    pub module_names: HashSet<ModuleFullPath>,

    // ── Module scoping fields ──────────────────────────────────────────────
    /// Per-module symbol tables: the sole source of truth for name→scheme resolution.
    pub modules: HashMap<ModuleFullPath, crate::module::CompiledModule>,
    /// The module currently being compiled or evaluated.
    /// Used by `lookup_via_modules()` to resolve bare names through the module system.
    current_module_path: ModuleFullPath,
}

/// A function whose type has trait constraints on its type variables.
/// Stored for later monomorphisation at call sites.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstrainedFn {
    pub defn: Defn,
    pub scheme: Scheme,
    pub deferred_resolutions: Vec<(Span, String, Type)>,
    /// The module where this constrained function was defined.
    /// Monomorphised specializations are compiled into this module.
    pub defining_module: ModuleFullPath,
}

/// A monomorphised specialization of a constrained function.
#[derive(Debug, Clone)]
pub struct MonoDefn {
    pub defn: Defn,
    pub resolutions: MethodResolutions,
}

/// Result of type-checking a program, including monomorphisation data.
pub struct CheckResult {
    pub method_resolutions: MethodResolutions,
    pub constrained_fn_names: HashSet<String>,
    pub mono_defns: Vec<(MonoDefn, ModuleFullPath)>,
    /// Resolved expression types: maps expression spans to their fully-resolved types.
    pub expr_types: HashMap<Span, Type>,
}

#[allow(clippy::new_without_default)]
impl TypeChecker {
    pub fn new() -> Self {
        TypeChecker {
            next_id: 0,
            subst: HashMap::new(),
            local_env: HashMap::new(),

            pending_resolutions: Vec::new(),
            overloads: HashMap::new(),
            resolved_overloads: HashMap::new(),
            pending_overload_resolutions: Vec::new(),
            pending_auto_curry: Vec::new(),
            var_constraints: HashMap::new(),
            deferred_resolutions: Vec::new(),
            pending_mono_calls: Vec::new(),
            generated_specializations: HashSet::new(),
            expr_types: HashMap::new(),
            builtin_resolutions: HashMap::new(),
            module_names: HashSet::new(),
            modules: HashMap::new(),
            current_module_path: ModuleFullPath::from("user"),
        }
    }

    /// Iterate all trait impls across all modules.
    fn all_impls(&self) -> impl Iterator<Item = &TraitImpl> {
        self.modules.values().flat_map(|cm| cm.impls.iter())
    }

    /// If `name` resolves to an extern/platform primitive (one with a JIT symbol name),
    /// return its fully-qualified symbol. Used to emit `BuiltinFn` resolutions.
    fn resolve_builtin_fq(&self, name: &str) -> Option<FQSymbol> {
        let entry = self.lookup_entry_via_modules(name)?;
        if let crate::module::ModuleEntry::Def {
            kind:
                crate::module::DefKind::Primitive {
                    jit_name: Some(_), ..
                },
            ..
        } = entry
        {
            // Use qualified_name to get the canonical FQSymbol
            Some(self.qualified_name(name))
        } else {
            None
        }
    }

    /// Look up a name's type scheme.
    /// Resolution order: local_env → module-walk.
    pub fn lookup(&self, name: &str) -> Option<&Scheme> {
        // 1. Local bindings (params, let, match vars)
        if let Some(s) = self.local_env.get(name) {
            return Some(s);
        }
        // 2. Module-walk resolution (per-module symbol tables)
        self.lookup_via_modules(name)
    }

    /// Look up a name's type scheme in the environment.
    pub fn lookup_env(&self, name: &str) -> Option<&Scheme> {
        self.lookup(name)
    }

    /// Return the qualified name for a bare name using module-walk resolution.
    /// Follows Import/Reexport chains to find the defining module.
    /// Returns an `FQSymbol` with root module if the name is not found in any module.
    pub fn qualified_name(&self, bare: &str) -> FQSymbol {
        // Look up in current module
        if let Some(cm) = self.modules.get(self.current_module_path.as_ref()) {
            if let Some(entry) = cm.get(bare) {
                return self.resolve_qualified_chain(entry, bare, &self.current_module_path, 0);
            }
        }
        // Root module fallback
        if let Some(cm) = self.modules.get("") {
            if let Some(entry) = cm.get(bare) {
                return self.resolve_qualified_chain(entry, bare, &ModuleFullPath::root(), 0);
            }
        }
        FQSymbol::new(ModuleFullPath::root(), Symbol::from(bare))
    }

    /// Follow Import/Reexport chains to find the defining module and return an `FQSymbol`.
    fn resolve_qualified_chain(
        &self,
        entry: &ModuleEntry,
        name: &str,
        module: &ModuleFullPath,
        depth: usize,
    ) -> FQSymbol {
        if depth > 16 {
            return FQSymbol::new(module.clone(), Symbol::from(name));
        }
        match entry {
            ModuleEntry::Import { source } | ModuleEntry::Reexport { source } => {
                if let Some(cm) = self.modules.get(source.module.as_ref()) {
                    if let Some(next_entry) = cm.get(&source.symbol) {
                        return self.resolve_qualified_chain(
                            next_entry,
                            &source.symbol,
                            &source.module,
                            depth + 1,
                        );
                    }
                }
                // Can't follow further — use source
                source.clone()
            }
            ModuleEntry::Def { .. } | ModuleEntry::Constructor { .. } => {
                FQSymbol::new(module.clone(), Symbol::from(name))
            }
            _ => FQSymbol::new(module.clone(), Symbol::from(name)),
        }
    }


    /// Insert a definition into the current module's CompiledModule with conflict detection.
    /// If the name is already taken by a different source, the bare name becomes Ambiguous
    /// and a warning is emitted. Qualified names (Trait.method, Type.Ctor) still resolve.
    fn insert_def_checked(&mut self, name: String, scheme: Scheme) {
        let current = self.current_module_path.clone();
        let cm = self
            .modules
            .entry(current.clone())
            .or_insert_with(|| CompiledModule::new(current));
        let poisoned = cm.insert_def_checked(
            Symbol::from(name.as_str()),
            scheme,
            Visibility::Public,
            None,
        );
        if poisoned {
            let alts = self.find_ambiguous_alternatives(&name);
            eprintln!(
                "warning: bare name '{}' is now ambiguous — use {}",
                name,
                alts.join(" or ")
            );
        }
    }

    /// Register a macro in the current module's CompiledModule for introspection and import/export.
    pub fn register_macro_in_module(
        &mut self,
        name: &str,
        fixed_params: Vec<String>,
        rest_param: Option<String>,
        docstring: Option<String>,
        visibility: Visibility,
        sexp: Option<crate::sexp::Sexp>,
        source: Option<String>,
    ) {
        let current = self.current_module_path.clone();
        let cm = self
            .modules
            .entry(current.clone())
            .or_insert_with(|| CompiledModule::new(current));
        cm.insert_macro(
            Symbol::from(name),
            fixed_params,
            rest_param,
            docstring,
            visibility,
            sexp,
            source,
        );
    }

    /// Enumerate qualified alternatives for an ambiguous bare name.
    /// Scans TraitDecl entries for matching methods, TypeDef entries for matching
    /// constructors and field names.
    fn find_ambiguous_alternatives(&self, name: &str) -> Vec<String> {
        let mut alts = Vec::new();
        for cm in self.modules.values() {
            for (sym, entry) in &cm.symbols {
                match entry {
                    ModuleEntry::TraitDecl { decl, .. } => {
                        if decl.methods.iter().any(|m| m.name == name) {
                            alts.push(format!("{}.{}", decl.name, name));
                        }
                    }
                    ModuleEntry::TypeDef { info, .. } => {
                        // Check constructors
                        if info.constructors.iter().any(|c| c.name == name) {
                            alts.push(format!("{}.{}", sym, name));
                        }
                        // Check field names
                        for ctor in &info.constructors {
                            if ctor.fields.iter().any(|(fname, _)| fname == name) {
                                alts.push(format!("{}.{}", sym, name));
                                break;
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        alts.sort();
        alts.dedup();
        alts
    }

    /// Check if a bare name is ambiguous in the current module.
    /// Returns an error with qualified alternatives if so.
    fn check_ambiguity(
        &self,
        name: &str,
        span: crate::error::Span,
    ) -> Result<(), CranelispError> {
        if let Some(entry) =
            self.resolve_entry_in_module(&self.current_module_path, name, 0, false)
        {
            if matches!(entry, ModuleEntry::Ambiguous) {
                let alts = self.find_ambiguous_alternatives(name);
                let suggestion = if alts.is_empty() {
                    String::new()
                } else {
                    format!(" — use {}", alts.join(" or "))
                };
                return Err(CranelispError::TypeError {
                    message: format!("ambiguous bare name '{name}'{suggestion}"),
                    span,
                });
            }
        }
        Ok(())
    }

    /// Look up a constructor's scheme from the module that defines the parent type,
    /// bypassing the current module's potentially-ambiguous bare name.
    fn lookup_constructor_scheme(&self, type_name: &str, ctor_name: &str) -> Option<&Scheme> {
        for cm in self.modules.values() {
            if let Some(ModuleEntry::TypeDef { info, .. }) = cm.symbols.get(type_name) {
                if info.constructors.iter().any(|c| c.name == ctor_name) {
                    // Found the module that defines this type — look up the constructor directly
                    return cm.get_scheme(ctor_name);
                }
            }
        }
        None
    }

    /// Construct a field accessor's scheme from TypeDefInfo for the given type.
    /// Bypasses the module's Def entry (which may be from a different type when
    /// multiple types share the same field name in the flat compilation path).
    fn lookup_field_accessor_scheme(&self, type_name: &str, field_name: &str) -> Option<Scheme> {
        for cm in self.modules.values() {
            if let Some(ModuleEntry::TypeDef { info: td, .. }) = cm.symbols.get(type_name) {
                for ctor in &td.constructors {
                    for (fname, fty) in &ctor.fields {
                        if fname == field_name {
                            let type_args: Vec<Type> =
                                td.type_params.iter().map(|&id| Type::Var(id)).collect();
                            let adt_type = Type::ADT(td.name.clone(), type_args);
                            let accessor_ty =
                                Type::Fn(vec![adt_type], Box::new(fty.clone()));
                            return Some(Scheme {
                                vars: td.type_params.clone(),
                                ty: accessor_ty,
                                constraints: std::collections::HashMap::new(),
                            });
                        }
                    }
                }
            }
        }
        None
    }

    /// Construct a trait method's scheme from the TraitDecl in the defining module,
    /// bypassing the current module's potentially-ambiguous bare name.
    fn lookup_trait_method_scheme(
        &mut self,
        trait_name: &str,
        method_name: &str,
    ) -> Option<Scheme> {
        // First, find the TraitMethodSig from the TraitDecl
        let method_sig = {
            let mut found = None;
            for cm in self.modules.values() {
                for entry in cm.symbols.values() {
                    if let ModuleEntry::TraitDecl { decl, .. } = entry {
                        if decl.name == trait_name {
                            if let Some(sig) =
                                decl.methods.iter().find(|m| m.name == method_name)
                            {
                                found = Some(sig.clone());
                                break;
                            }
                        }
                    }
                }
                if found.is_some() {
                    break;
                }
            }
            found
        };
        let sig = method_sig?;
        // Build scheme: forall a. <sig with self=a>
        let a = self.fresh_var();
        let a_id = match &a {
            Type::Var(id) => *id,
            _ => unreachable!(),
        };
        let param_tys: Vec<Type> = sig
            .params
            .iter()
            .map(|p| self.resolve_type_expr(p, &a))
            .collect();
        let ret_ty = self.resolve_type_expr(&sig.ret_type, &a);
        Some(Scheme {
            vars: vec![a_id],
            constraints: std::collections::HashMap::new(),
            ty: Type::Fn(param_tys, Box::new(ret_ty)),
        })
    }

    /// Insert a definition into the current module's CompiledModule.
    /// Used for module-level definitions (defn, type constructors, trait methods, primitives).
    fn insert_def(&mut self, name: String, scheme: Scheme) {
        self.insert_def_vis(name, scheme, Visibility::Public);
    }

    fn insert_def_vis(&mut self, name: String, scheme: Scheme, visibility: Visibility) {
        let current = self.current_module_path.clone();
        let cm = self
            .modules
            .entry(current.clone())
            .or_insert_with(|| CompiledModule::new(current));
        cm.insert_def(
            Symbol::from(name.as_str()),
            scheme,
            visibility,
            None,
        );
    }

    /// Insert a constructor entry into the current module's CompiledModule.
    /// Used by `register_type_def` for ADT constructors and field accessors.
    fn insert_constructor(
        &mut self,
        ctor_name: String,
        type_name: String,
        info: ConstructorInfo,
        scheme: Scheme,
        visibility: Visibility,
    ) {
        let current = self.current_module_path.clone();
        let cm = self
            .modules
            .entry(current.clone())
            .or_insert_with(|| CompiledModule::new(current));
        cm.symbols.insert(
            Symbol::from(ctor_name.as_str()),
            ModuleEntry::Constructor {
                type_name: Symbol::from(type_name.as_str()),
                info,
                scheme,
                visibility,
            },
        );
    }

    /// Remove a definition from the current module's CompiledModule.
    fn remove_def(&mut self, name: &str) -> Option<Scheme> {
        if let Some(cm) = self.modules.get_mut(self.current_module_path.as_ref()) {
            // Extract the scheme before removing
            let scheme = cm.get_scheme(name).cloned();
            cm.symbols.remove(name);
            return scheme;
        }
        None
    }

    /// Resolve a type fully through the substitution map.
    pub fn resolve(&self, ty: &Type) -> Type {
        apply(&self.subst, ty)
    }

    /// Resolve all recorded expression types through the current substitution.
    /// Returns the resolved map, clearing the internal accumulator.
    pub fn resolve_expr_types(&mut self) -> HashMap<Span, Type> {
        let resolved = self
            .expr_types
            .iter()
            .map(|(span, ty)| (*span, apply(&self.subst, ty)))
            .collect();
        self.expr_types.clear();
        resolved
    }

    /// Look up symbol metadata (docstring + param names) via module-walk.
    pub fn get_symbol_meta(&self, name: &str) -> Option<&SymbolMeta> {
        self.resolve_symbol_meta_via_modules(name)
    }

    /// Look up a trait declaration by walking all module TraitDecl entries.
    pub fn get_trait(&self, name: &str) -> Option<&TraitDecl> {
        self.find_trait_decl(name)
    }

    /// Find a trait declaration by walking all module TraitDecl entries.
    fn find_trait_decl(&self, trait_name: &str) -> Option<&TraitDecl> {
        for cm in self.modules.values() {
            if let Some(crate::module::ModuleEntry::TraitDecl { decl, .. }) = cm.get(trait_name) {
                return Some(decl);
            }
        }
        None
    }

    /// Find which trait a method belongs to by walking all module TraitDecl entries.
    fn find_trait_for_method(&self, method_name: &str) -> Option<&str> {
        for cm in self.modules.values() {
            for entry in cm.symbols.values() {
                if let crate::module::ModuleEntry::TraitDecl { decl, .. } = entry {
                    if decl.methods.iter().any(|m| m.name == method_name) {
                        return Some(&decl.name);
                    }
                }
            }
        }
        None
    }

    /// Look up which trait a method belongs to.
    pub fn get_method_trait(&self, method: &str) -> Option<&str> {
        self.find_trait_for_method(method)
    }

    /// Qualify a bare name for file generation.
    /// Returns `Some("Type.Name")` for constructors and `Some("Trait.method")` for
    /// trait methods. Returns `None` for everything else (local vars, special forms,
    /// regular functions).
    pub fn qualify_name(&self, name: &str) -> Option<String> {
        // Don't qualify names that already contain a dot or slash
        if name.contains('.') || name.contains('/') {
            return None;
        }
        // Don't qualify colon-prefixed type annotations
        if name.starts_with(':') {
            return None;
        }
        // Check if name resolves to a Constructor
        let current = &self.current_module_path;
        if let Some(ModuleEntry::Constructor { type_name, .. }) =
            self.resolve_entry_in_module(current, name, 0, false)
        {
            return Some(format!("{}.{}", type_name, name));
        }
        // Check if it's a trait method
        if let Some(trait_name) = self.find_trait_for_method(name) {
            return Some(format!("{}.{}", trait_name, name));
        }
        None
    }

    /// Look up resolved overload variants for a multi-sig function.
    /// Returns [(param_types, return_type, mangled_name)] if found.
    pub fn get_resolved_overloads(&self, name: &str) -> Option<&Vec<(Vec<Type>, Type, String)>> {
        self.resolved_overloads.get(name)
    }

    /// Register a single env alias (e.g., for module alias qualified names).
    /// Parses the qualified name and writes to the corresponding CompiledModule.
    pub fn register_alias(&mut self, name: &str, scheme: &Scheme) {
        if let Some(slash_pos) = name.find('/') {
            if slash_pos > 0 {
                let module_part = &name[..slash_pos];
                let bare_part = &name[slash_pos + 1..];
                let mod_path = ModuleFullPath::from(module_part);
                let cm = self
                    .modules
                    .entry(mod_path.clone())
                    .or_insert_with(|| CompiledModule::new(mod_path));
                cm.insert_def(
                    Symbol::from(bare_part),
                    scheme.clone(),
                    Visibility::Public,
                    None,
                );
                return;
            }
        }
        // Non-qualified: write to current module
        let current = self.current_module_path.clone();
        let cm = self
            .modules
            .entry(current.clone())
            .or_insert_with(|| CompiledModule::new(current));
        cm.insert_def(Symbol::from(name), scheme.clone(), Visibility::Public, None);
    }

    /// Register a module name as a known prefix for qualified name parsing.
    /// Called after compiling a module so that `module/name` references resolve correctly.
    pub fn register_module_prefix(&mut self, module_name: &str) {
        self.module_names.insert(ModuleFullPath::from(module_name));
    }

    /// Look up the visibility of a name defined in a module.
    pub fn get_name_visibility(&self, module_name: &str, bare_name: &str) -> Option<Visibility> {
        self.modules.get(module_name)?.get_visibility(bare_name)
    }

    // ── Module scope management ────────────────────────────────────────────

    /// Get all public names defined by a module.
    pub fn get_module_public_names(&self, module_name: &str) -> Vec<String> {
        self.modules
            .get(module_name)
            .map(|cm| cm.public_names())
            .unwrap_or_default()
    }

    /// Get all names (public and private) defined by a module.
    pub fn get_module_all_names(&self, module_name: &str) -> Vec<(String, Visibility)> {
        self.modules
            .get(module_name)
            .map(|cm| cm.all_names_with_visibility())
            .unwrap_or_default()
    }

    /// Install imported bare names into the current module scope.
    /// `resolved_imports` is a list of (bare_name, source_module) pairs.
    /// Writes Import entries into the current module's CompiledModule.
    /// Cross-source import collisions poison the bare name to Ambiguous with a warning.
    pub fn begin_module_scope(
        &mut self,
        resolved_imports: &[(String, String)],
    ) -> Result<(), crate::error::CranelispError> {
        for (bare_name, source_module) in resolved_imports {
            let current = self.current_module_path.clone();
            let cm = self
                .modules
                .entry(current.clone())
                .or_insert_with(|| crate::module::CompiledModule::new(current));
            let poisoned = cm.insert_import_checked(
                Symbol::from(bare_name.as_str()),
                FQSymbol::new(
                    ModuleFullPath::from(source_module.as_str()),
                    Symbol::from(bare_name.as_str()),
                ),
            );
            if poisoned {
                let alts = self.find_ambiguous_alternatives(bare_name);
                if !alts.is_empty() {
                    eprintln!(
                        "warning: bare name '{}' is now ambiguous — use {}",
                        bare_name,
                        alts.join(" or ")
                    );
                }
            }
        }
        Ok(())
    }

    /// Install additional imported names without clearing existing imports.
    /// Used by the REPL's `(import ...)` command and `install_synthetic_bare_names`
    /// to add names incrementally.
    pub fn install_imported_names(&mut self, resolved_imports: &[(String, String)]) {
        for (bare_name, source_module) in resolved_imports {
            let current = self.current_module_path.clone();
            let cm = self
                .modules
                .entry(current.clone())
                .or_insert_with(|| crate::module::CompiledModule::new(current));
            let poisoned = cm.insert_import_checked(
                Symbol::from(bare_name.as_str()),
                FQSymbol::new(
                    ModuleFullPath::from(source_module.as_str()),
                    Symbol::from(bare_name.as_str()),
                ),
            );
            if poisoned {
                let alts = self.find_ambiguous_alternatives(bare_name);
                if !alts.is_empty() {
                    eprintln!(
                        "warning: bare name '{}' is now ambiguous — use {}",
                        bare_name,
                        alts.join(" or ")
                    );
                }
            }
        }
    }

    /// No-op after removing current_module_imports.
    /// Retained because callers exist; the module's Import entries persist in CompiledModule
    /// (they belong to that module and don't need cleanup).
    pub fn end_module_scope(&mut self) {}

    /// Check if a bare name is currently imported (for definition conflict detection).
    pub fn is_imported(&self, name: &str) -> Option<&str> {
        let cm = self.modules.get(self.current_module_path.as_ref())?;
        let source = cm.import_source(name)?;
        Some(&**source)
    }

    /// Check if defining a name conflicts with an explicit import.
    /// Returns an error if the name is already imported from another module.
    pub fn check_definition_conflict(
        &self,
        name: &str,
        span: crate::error::Span,
    ) -> Result<(), crate::error::CranelispError> {
        if let Some(source) = self.is_imported(name) {
            return Err(crate::error::CranelispError::TypeError {
                message: format!(
                    "definition '{}' conflicts with import from module '{}'",
                    name, source
                ),
                span,
            });
        }
        Ok(())
    }

    /// Collect all type schemes reachable from the current module's scope.
    /// Used by `generalize()` to determine which type variables are free in the environment.
    fn reachable_schemes(&self) -> Vec<&Scheme> {
        let mut schemes = Vec::new();
        // Current module's symbols
        if let Some(cm) = self.modules.get(self.current_module_path.as_ref()) {
            for entry in cm.symbols.values() {
                match entry {
                    ModuleEntry::Def { scheme, .. }
                    | ModuleEntry::Constructor { scheme, .. }
                    | ModuleEntry::TypeDef { constructor_scheme: Some(scheme), .. } => {
                        schemes.push(scheme);
                    }
                    ModuleEntry::Import { source } | ModuleEntry::Reexport { source } => {
                        if let Some(s) =
                            self.resolve_in_module(&source.module, &source.symbol, 0, false)
                        {
                            schemes.push(s);
                        }
                    }
                    _ => {}
                }
            }
        }
        // Root module (special forms, registered there by register_special_forms)
        if !self.current_module_path.is_root() {
            if let Some(cm) = self.modules.get("") {
                for entry in cm.symbols.values() {
                    if let ModuleEntry::Def { scheme, .. } = entry {
                        schemes.push(scheme);
                    }
                }
            }
        }
        schemes
    }

    // ── Module-walk resolution (Step 5) ─────────────────────────────────

    /// Set the current module path for module-walk resolution.
    pub fn set_current_module_path(&mut self, path: ModuleFullPath) {
        self.current_module_path = path;
    }

    /// Set the current module by short name (convenience wrapper).
    pub fn set_current_module(&mut self, name: &str) {
        self.current_module_path = ModuleFullPath::from(name);
    }

    /// Get the short name of the current module.
    pub fn current_module_name(&self) -> &str {
        self.current_module_path.short_name()
    }

    /// Update the meta field on a Def entry in the current module's CompiledModule.
    /// Best-effort: no-op if the module or entry doesn't exist or isn't a Def.
    pub fn update_current_module_meta(&mut self, name: &str, meta: SymbolMeta) {
        if let Some(cm) = self.modules.get_mut(&self.current_module_path) {
            cm.update_meta(name, meta);
        }
    }

    /// Resolve a bare name in a specific module's CompiledModule to its terminal ModuleEntry.
    /// Follows Import/Reexport chains with a depth limit.
    /// When `require_public` is true, only Public entries are returned (used for
    /// cross-module qualified access like `util/name`).
    fn resolve_entry_in_module(
        &self,
        module: &ModuleFullPath,
        name: &str,
        depth: usize,
        require_public: bool,
    ) -> Option<&crate::module::ModuleEntry> {
        if depth > 16 {
            return None;
        }
        let cm = self.modules.get(module.as_ref())?;
        let entry = cm.get(name)?;
        match entry {
            crate::module::ModuleEntry::Def { visibility, .. }
            | crate::module::ModuleEntry::Constructor { visibility, .. }
            | crate::module::ModuleEntry::TypeDef { visibility, .. }
            | crate::module::ModuleEntry::TraitDecl { visibility, .. }
            | crate::module::ModuleEntry::Macro { visibility, .. } => {
                if require_public && *visibility != Visibility::Public {
                    return None;
                }
                Some(entry)
            }
            crate::module::ModuleEntry::Import { source }
            | crate::module::ModuleEntry::Reexport { source } => {
                self.resolve_entry_in_module(&source.module, &source.symbol, depth + 1, false)
            }
            crate::module::ModuleEntry::PlatformDecl { .. }
            | crate::module::ModuleEntry::Ambiguous => Some(entry),
        }
    }

    /// Resolve a bare name to its Scheme via module-walk (thin wrapper over resolve_entry_in_module).
    fn resolve_in_module(
        &self,
        module: &ModuleFullPath,
        name: &str,
        depth: usize,
        require_public: bool,
    ) -> Option<&Scheme> {
        match self.resolve_entry_in_module(module, name, depth, require_public)? {
            crate::module::ModuleEntry::Def { scheme, .. }
            | crate::module::ModuleEntry::Constructor { scheme, .. } => Some(scheme),
            crate::module::ModuleEntry::TypeDef { constructor_scheme: Some(scheme), .. } => Some(scheme),
            _ => None,
        }
    }

    /// Look up a name using the per-module symbol tables.
    fn lookup_via_modules(&self, name: &str) -> Option<&Scheme> {
        // 1. Qualified name (contains '/' with non-empty module prefix)?
        // A bare '/' or names starting with '/' are operators, not qualified names.
        if let Some(slash_pos) = name.find('/') {
            if slash_pos > 0 {
                let module_part = &name[..slash_pos];
                let name_part = &name[slash_pos + 1..];
                // Cross-module qualified access: enforce visibility
                return self.resolve_in_module(
                    &ModuleFullPath::from(module_part),
                    name_part,
                    0,
                    true,
                );
            }
            // slash_pos == 0: bare '/' or '/=' — operator, fall through
        }

        // 2. Current module's symbols (own module: no visibility check)
        if let Some(scheme) =
            self.resolve_in_module(&self.current_module_path, name, 0, false)
        {
            return Some(scheme);
        }

        // 3. Root module (special forms are registered in modules[ModuleFullPath::root()])
        if let Some(scheme) = self.resolve_in_module(&ModuleFullPath::root(), name, 0, false) {
            return Some(scheme);
        }

        None
    }

    /// Look up a name using module-walk and return the terminal ModuleEntry.
    /// Same resolution order as lookup_via_modules: qualified → current module → root.
    fn lookup_entry_via_modules(&self, name: &str) -> Option<&crate::module::ModuleEntry> {
        // 1. Qualified name
        if let Some(slash_pos) = name.find('/') {
            if slash_pos > 0 {
                let module_part = &name[..slash_pos];
                let name_part = &name[slash_pos + 1..];
                return self.resolve_entry_in_module(
                    &ModuleFullPath::from(module_part),
                    name_part,
                    0,
                    true,
                );
            }
        }
        // 2. Current module
        if let Some(entry) =
            self.resolve_entry_in_module(&self.current_module_path, name, 0, false)
        {
            return Some(entry);
        }
        // 3. Root module
        self.resolve_entry_in_module(&ModuleFullPath::root(), name, 0, false)
    }

    /// Resolve a name to its TypeDefInfo via module-walk.
    /// TypeDef entries are stored in `symbols`, and Import/Reexport chains are
    /// followed automatically by `resolve_entry_in_module`.
    pub fn resolve_type_def_via_modules(&self, name: &str) -> Option<&TypeDefInfo> {
        // 1. Qualified name — go directly to the target module
        if let Some(slash_pos) = name.find('/') {
            if slash_pos > 0 {
                let module_part = &name[..slash_pos];
                let name_part = &name[slash_pos + 1..];
                return self.resolve_type_def_in_module(module_part, name_part);
            }
        }
        // 2. Current module
        if let Some(info) = self.resolve_type_def_in_module(
            self.current_module_path.as_ref(),
            name,
        ) {
            return Some(info);
        }
        // 3. Root module
        if let Some(info) = self.resolve_type_def_in_module("", name) {
            return Some(info);
        }
        None
    }

    /// For display: qualify a bare ADT name with its module if not in current/root scope.
    /// Returns "foo/Point2" if Point2 is only found in module "foo".
    pub fn qualify_adt_name(&self, name: &str) -> String {
        if name.contains('/') {
            return name.to_string();
        }
        // Current module or root → no qualification needed
        if self
            .resolve_type_def_in_module(self.current_module_path.as_ref(), name)
            .is_some()
            || self.resolve_type_def_in_module("", name).is_some()
        {
            return name.to_string();
        }
        // Scan all modules
        for (path, cm) in &self.modules {
            if let Some(crate::module::ModuleEntry::TypeDef { .. }) = cm.get(name) {
                if !path.is_empty() {
                    return format!("{}/{}", path.as_ref(), name);
                }
            }
        }
        name.to_string()
    }

    /// Follow import/reexport chain from a starting module to find TypeDefInfo.
    fn resolve_type_def_in_module(&self, start_module: &str, name: &str) -> Option<&TypeDefInfo> {
        let entry = self.resolve_entry_in_module(
            &ModuleFullPath::from(start_module),
            name,
            0,
            false,
        )?;
        match entry {
            crate::module::ModuleEntry::TypeDef { info, .. } => Some(info),
            _ => None,
        }
    }

    /// Resolve a constructor name to its type name via module-walk.
    pub fn resolve_constructor_type_via_modules(&self, name: &str) -> Option<&str> {
        match self.lookup_entry_via_modules(name)? {
            crate::module::ModuleEntry::Constructor { type_name, .. } => Some(type_name),
            // Product types: TypeDef with constructor_scheme doubles as the constructor
            crate::module::ModuleEntry::TypeDef { info, constructor_scheme: Some(_), .. } => {
                Some(&info.name)
            }
            _ => None,
        }
    }

    /// Resolve a name to its SymbolMeta via module-walk.
    pub fn resolve_symbol_meta_via_modules(&self, name: &str) -> Option<&SymbolMeta> {
        match self.lookup_entry_via_modules(name)? {
            crate::module::ModuleEntry::Def {
                meta: Some(m), ..
            } => Some(m),
            _ => None,
        }
    }

    /// Resolve a name to its ConstrainedFn via module-walk.
    pub fn resolve_constrained_fn_via_modules(&self, name: &str) -> Option<&ConstrainedFn> {
        match self.lookup_entry_via_modules(name)? {
            crate::module::ModuleEntry::Def {
                kind: crate::module::DefKind::UserFn { constrained_fn: Some(cf), .. },
                ..
            } => Some(cf),
            _ => None,
        }
    }

    /// Collect all TypeDefInfo entries across all modules.
    /// Used by JIT to build codegen type definitions.
    pub fn collect_all_type_defs(&self) -> HashMap<String, TypeDefInfo> {
        let mut result = HashMap::new();
        for cm in self.modules.values() {
            for (sym, entry) in &cm.symbols {
                if let ModuleEntry::TypeDef { info, .. } = entry {
                    let name = sym.to_string();
                    result.entry(name).or_insert_with(|| info.clone());
                }
            }
        }
        result
    }

    /// Collect all constructor-to-type mappings across all modules.
    /// Used by JIT to build codegen constructor lookup.
    pub fn collect_all_constructor_to_type(&self) -> HashMap<String, String> {
        let mut result = HashMap::new();
        for cm in self.modules.values() {
            for (sym, entry) in &cm.symbols {
                match entry {
                    crate::module::ModuleEntry::Constructor { type_name, .. } => {
                        let name = sym.to_string();
                        result
                            .entry(name)
                            .or_insert_with(|| type_name.to_string());
                    }
                    // Product types: TypeDef with constructor_scheme is also a constructor
                    crate::module::ModuleEntry::TypeDef {
                        info,
                        constructor_scheme: Some(_),
                        ..
                    } => {
                        let name = sym.to_string();
                        result
                            .entry(name)
                            .or_insert_with(|| info.name.clone());
                    }
                    _ => {}
                }
            }
        }
        result
    }
}

#[cfg(test)]
mod tests;
