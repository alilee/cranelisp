//! cranelisp-types: shared boundary types for the Cranelisp compiler pipeline.
//! See design/arch/interfaces.md for the complete type catalog.

pub mod span;
pub mod newtype;
pub mod error;
pub mod sexp;
pub mod ast;
pub mod types;
pub mod check;
pub mod module;
pub mod heap;
pub mod pipeline;
pub mod operator;
pub mod marshal;

// Re-export key types at crate root for convenience.
pub use span::Span;
pub use error::{CranelispError, Warning, WarningKind};
pub use sexp::Sexp;
pub use ast::{
    ConstructorDef, Defn, DefnVariant, Expr, FieldDef, MatchArm, Pattern, Program,
    TopLevel, TraitDecl, TraitImpl, TraitMethodSig, TypeExpr, Visibility, free_vars_expr,
};
pub use types::{Scheme, Subst, Type, TypeId, apply, free_vars, max_type_var_id, format_type_display, format_type_with_vars, type_var_names};
pub use check::{
    CheckResult, ConstructorInfo, DisplayInfo, FieldInfo, MethodResolutions, MonoDefn,
    ReplSnapshot, ResolvedCall, TypeDefInfo,
};
pub use module::{
    ConstrainedFn, DefKind, ExportSpec, ImplSexp, ImportNames, ImportSpec, MacroClauseInfo,
    MacroParam, ModDecl, ModuleEntry, ModuleStructure, OverloadVariant, PlatformSpec, PrimitiveKind,
    SymbolTable,
};
pub use heap::{HeapCategory, HeapHeader};
pub use pipeline::{
    CallEdge, CallGraph, CallInfo, CodegenBehaviour, CompileContext, CompileResult,
    GOT_TABLE_SIZE, MacroExpander, ModuleStrategy, NoOpExpander, NULLARY_TAG_THRESHOLD,
};
pub use operator::{ring0_primitives, ring1_primitives, ring3_primitives, PrimitiveDef};
pub use marshal::{
    TAG_SNIL, TAG_SCONS,
    TAG_SEXP_INT, TAG_SEXP_FLOAT, TAG_SEXP_BOOL, TAG_SEXP_STR,
    TAG_SEXP_SYM, TAG_SEXP_LIST, TAG_SEXP_BRACKET,
};

// String newtypes
pub use newtype::{
    FQSymbol, JitSymbol, ModuleFullPath, ModuleName, Symbol, TraitName, TypeName,
};
