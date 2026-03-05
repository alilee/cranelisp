use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::PathBuf;

use crate::{
    ConstructorInfo, Defn, FQSymbol, ModuleFullPath, ModuleName, Scheme, Sexp, Span, Symbol,
    TraitDecl, TraitImpl, TraitName, Type, TypeDefInfo, TypeName, Visibility,
};

// --- Symbol Table ---

/// Per-module symbol table. Pure data -- no runtime state.
/// Owned by TypeChecker, read by Backend for type information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SymbolTable {
    pub path: ModuleFullPath,
    pub symbols: HashMap<Symbol, ModuleEntry>,
}

impl SymbolTable {
    pub fn new(path: ModuleFullPath) -> Self {
        SymbolTable {
            path,
            symbols: HashMap::new(),
        }
    }

    pub fn get(&self, name: &str) -> Option<&ModuleEntry> {
        self.symbols.get(name)
    }

    pub fn insert(&mut self, name: Symbol, entry: ModuleEntry) {
        self.symbols.insert(name, entry);
    }

    pub fn public_symbols(&self) -> impl Iterator<Item = (&Symbol, &ModuleEntry)> {
        self.symbols.iter().filter(|(_, e)| e.is_public())
    }
}

// --- Module Entries ---

/// An entry in a module's symbol table.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ModuleEntry {
    /// A definition: function, primitive, special form.
    Def {
        scheme: Scheme,
        visibility: Visibility,
        docstring: Option<String>,
        param_names: Vec<Symbol>,
        kind: Box<DefKind>,
    },
    /// An imported name from another module (Ring 2).
    Import { source: FQSymbol },
    /// A re-exported name from another module (Ring 2).
    Reexport { source: FQSymbol },
    /// A type definition (deftype).
    TypeDef {
        info: TypeDefInfo,
        visibility: Visibility,
        constructor_scheme: Option<Scheme>,
        sexp: Option<Sexp>,
    },
    /// A trait declaration (deftrait, Ring 2).
    TraitDecl {
        decl: TraitDecl,
        visibility: Visibility,
        sexp: Option<Sexp>,
    },
    /// A constructor (from a deftype).
    Constructor {
        type_name: Symbol,
        info: ConstructorInfo,
        scheme: Scheme,
        visibility: Visibility,
    },
    /// A macro definition (defmacro, Ring 3).
    Macro {
        name: Symbol,
        clauses: Vec<MacroClauseInfo>,
        docstring: Option<String>,
        visibility: Visibility,
        sexp: Option<Sexp>,
        source: Option<String>,
    },
    /// A platform DLL declaration (Ring 4).
    PlatformDecl {
        dll_path: PathBuf,
        platform_module: ModuleFullPath,
    },
    /// A bare name that became ambiguous (two different sources registered it, Ring 2).
    Ambiguous,
}

impl ModuleEntry {
    /// Returns true if this entry is publicly visible.
    pub fn is_public(&self) -> bool {
        match self {
            ModuleEntry::Def { visibility, .. }
            | ModuleEntry::TypeDef { visibility, .. }
            | ModuleEntry::TraitDecl { visibility, .. }
            | ModuleEntry::Constructor { visibility, .. }
            | ModuleEntry::Macro { visibility, .. } => *visibility == Visibility::Public,
            ModuleEntry::Import { .. } | ModuleEntry::Reexport { .. } => true,
            ModuleEntry::PlatformDecl { .. } => true,
            ModuleEntry::Ambiguous => false,
        }
    }
}

// --- Definition Classification ---

/// What kind of definition a symbol is.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DefKind {
    /// A special form (if, let, defn, ...).
    SpecialForm { description: String },
    /// A built-in primitive (inline IR, extern FFI, or platform effect).
    Primitive {
        primitive_kind: PrimitiveKind,
        jit_name: Option<JitSymbol>,
    },
    /// A user-defined function.
    UserFn {
        constrained_fn: Option<Box<ConstrainedFn>>,
    },
    /// Multi-sig overloaded function base name (Ring 2).
    Overloaded {
        variants: Vec<OverloadVariant>,
    },
}

/// Classification of primitive functions.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PrimitiveKind {
    /// Inlined as Cranelift IR at the call site
    Inline,
    /// Calls an extern Rust function via JIT symbol (Ring 1+)
    Extern,
    /// Platform effect (dispatched through IO trampoline, Ring 4)
    PlatformEffect,
}

/// One variant of an overloaded (multi-sig) function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OverloadVariant {
    pub param_types: Vec<Type>,
    pub ret_type: Type,
    pub mangled_name: Symbol,
}

/// A constrained polymorphic function awaiting monomorphisation (Ring 2).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConstrainedFn {
    pub defn: Defn,
    pub scheme: Scheme,
}

// --- Macro Support Types ---

/// Information about a single macro clause (for multi-clause defmacro, Ring 3).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MacroClauseInfo {
    pub params: Vec<MacroParam>,
    pub source: Option<String>,
}

/// A macro parameter: either a simple name or a bracket destructuring.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MacroParam {
    /// Simple name binding
    Name(Symbol),
    /// Bracket destructuring: `[fixed... & rest]`
    Bracket {
        fixed: Vec<Symbol>,
        rest: Option<Symbol>,
    },
}

// --- Import/Export (Ring 2) ---

/// What names to import from a module.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ImportNames {
    Specific(Vec<Symbol>),
    Glob,
    MemberGlob(Symbol),
    None,
}

/// An import declaration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImportSpec {
    pub module_path: ModuleFullPath,
    pub alias: Option<ModuleName>,
    pub names: ImportNames,
    pub span: Span,
}

/// An export declaration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExportSpec {
    pub module_path: ModuleFullPath,
    pub names: ImportNames,
    pub span: Span,
}

/// Stored impl S-expression for deferred processing.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImplSexp {
    pub trait_name: TraitName,
    pub target: TypeName,
    pub sexp: Sexp,
}

// --- Module Structure ---

/// Module structural metadata: file paths, declarations, imports, exports.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModuleStructure {
    pub path: ModuleFullPath,
    pub file_path: Option<PathBuf>,
    pub mod_decls: Vec<ModuleName>,
    pub import_specs: Vec<ImportSpec>,
    pub export_specs: Vec<ExportSpec>,
    pub impl_sexps: Vec<ImplSexp>,
    pub impls: Vec<TraitImpl>,
    pub dll_path: Option<PathBuf>,
}

use crate::JitSymbol;
