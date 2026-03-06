//! TypeChecker struct: the central state for type inference.
//!
//! Scope operations, fresh variable generation, and expr_type recording.
//! Other modules extend TypeChecker via `impl TypeChecker` blocks.

use std::collections::HashMap;

use cranelisp_types::{
    CranelispError, MethodResolutions, ModuleFullPath, ReplSnapshot,
    Scheme, Span, Subst, Symbol, SymbolTable, Type, TypeId, Warning,
    apply,
};

use crate::adt::TypeDefRegistry;
use crate::scope::ScopeStack;
use crate::scheme;
use crate::traits::{ActiveConstraints, ImplRegistry, TraitRegistry};

/// Central state for Hindley-Milner type inference.
///
/// Fields are pub(crate) so that `impl TypeChecker` blocks in other modules
/// can access them directly (borrow-splitting pattern).
pub struct TypeChecker {
    /// Monotonic counter for fresh type variable IDs.
    pub(crate) next_id: TypeId,
    /// Global substitution (unification bindings).
    pub(crate) subst: Subst,
    /// Lexical scope stack.
    pub(crate) env: ScopeStack,
    /// Type of every expression, keyed by span.
    pub(crate) expr_types: HashMap<Span, Type>,
    /// How each call site was resolved (builtin operators in Ring 0).
    pub(crate) method_resolutions: MethodResolutions,
    /// Non-fatal warnings accumulated during checking.
    pub(crate) warnings: Vec<Warning>,
    /// Module-level symbol table (single "user" module in Ring 0).
    pub(crate) symbol_table: SymbolTable,
    /// Registered type definitions (ADTs).
    pub(crate) type_defs: TypeDefRegistry,
    /// Registered trait declarations (Ring 2).
    pub(crate) trait_registry: TraitRegistry,
    /// Registered trait implementations (Ring 2).
    pub(crate) impl_registry: ImplRegistry,
    /// Active type variable constraints during body checking (Ring 2).
    pub(crate) active_constraints: ActiveConstraints,
}

impl TypeChecker {
    /// Create a new TypeChecker with Ring 0 builtins registered.
    pub fn new() -> Self {
        let mut tc = TypeChecker {
            next_id: 0,
            subst: Subst::new(),
            env: ScopeStack::new(),
            expr_types: HashMap::new(),
            method_resolutions: HashMap::new(),
            warnings: Vec::new(),
            symbol_table: SymbolTable::new(ModuleFullPath::from("user")),
            type_defs: TypeDefRegistry::new(),
            trait_registry: TraitRegistry::default(),
            impl_registry: ImplRegistry::default(),
            active_constraints: ActiveConstraints::default(),
        };
        tc.register_builtins();
        tc
    }

    // --- Scope operations (delegate to ScopeStack) ---

    /// Push a new scope frame.
    pub(crate) fn push_scope(&mut self) {
        self.env.push_scope();
    }

    /// Pop the topmost scope frame.
    pub(crate) fn pop_scope(&mut self) {
        self.env.pop_scope();
    }

    /// Bind a name in the current scope with a type scheme.
    pub(crate) fn bind_local(&mut self, name: Symbol, scheme: Scheme) {
        self.env.bind(name, scheme);
    }

    /// Look up a name in scope stack, falling back to symbol table.
    pub(crate) fn lookup(&self, name: &str) -> Option<Scheme> {
        // Check local scope stack first
        if let Some(scheme) = self.env.lookup(name) {
            return Some(scheme.clone());
        }

        // Fall back to symbol table (module-level definitions)
        self.lookup_in_symbol_table(name)
    }

    /// Look up a name in the symbol table and extract its scheme.
    fn lookup_in_symbol_table(&self, name: &str) -> Option<Scheme> {
        use cranelisp_types::ModuleEntry;

        match self.symbol_table.get(name)? {
            ModuleEntry::Def { scheme, .. } => Some(scheme.clone()),
            ModuleEntry::Constructor { scheme, .. } => Some(scheme.clone()),
            // Product types: TypeDef with constructor_scheme (same name)
            ModuleEntry::TypeDef {
                constructor_scheme: Some(scheme),
                ..
            } => Some(scheme.clone()),
            _ => None,
        }
    }

    // --- Fresh variable generation ---

    /// Generate a fresh type variable.
    pub(crate) fn fresh_var(&mut self) -> Type {
        crate::unify::fresh_var(&mut self.next_id)
    }

    /// Generate a fresh type variable and return both the type and ID.
    /// Used by ADT registration to allocate type parameter variables.
    pub(crate) fn fresh_var_id(&mut self) -> (Type, TypeId) {
        crate::unify::fresh_var_id(&mut self.next_id)
    }

    // --- Unification (delegate to unify module, borrow-splitting) ---

    /// Unify two types. Wraps the free function with self's subst.
    /// `span` is used for error context.
    pub(crate) fn unify(
        &mut self,
        t1: &Type,
        t2: &Type,
        span: Span,
    ) -> Result<(), CranelispError> {
        crate::unify::unify(&mut self.subst, t1, t2).map_err(|e| {
            // Re-wrap with the caller's span if the error has SYNTHETIC span
            if e.span() == Span::SYNTHETIC {
                CranelispError::TypeError {
                    message: e.message().to_string(),
                    span,
                }
            } else {
                e
            }
        })
    }

    // --- Scheme operations ---

    /// Instantiate a scheme with fresh variables.
    ///
    /// If the scheme has constraints, they are tracked on the fresh variables
    /// in `self.active_constraints` for later propagation during generalize.
    pub(crate) fn instantiate(&mut self, s: &Scheme) -> Type {
        if s.constraints.is_empty() {
            scheme::instantiate(s, &mut self.next_id)
        } else {
            self.instantiate_constrained(s)
        }
    }

    /// Generalize a type relative to the current environment,
    /// propagating any active constraints on the quantified variables.
    pub(crate) fn generalize(&self, ty: &Type) -> Scheme {
        let env_fv = self.env.free_vars_in_env();
        let mut scheme = scheme::generalize(&self.subst, ty, &env_fv);

        // Propagate constraints from active_constraints to the scheme
        let constraints =
            self.active_constraints.collect_for_vars(&scheme.vars);
        if !constraints.is_empty() {
            scheme.constraints = constraints;
        }

        scheme
    }

    // --- Expression type recording ---

    /// Record the inferred type for an expression (keyed by span).
    pub(crate) fn record_expr_type(&mut self, span: Span, ty: Type) {
        self.expr_types.insert(span, ty);
    }

    /// Apply the current substitution to a type.
    pub(crate) fn apply_subst(&self, ty: &Type) -> Type {
        apply(&self.subst, ty)
    }

    // --- REPL snapshot/restore ---

    /// Take a snapshot of the current state for REPL error recovery.
    pub fn snapshot(&self) -> ReplSnapshot {
        ReplSnapshot {
            next_type_id: self.next_id,
            symbol_count: self.symbol_table.symbols.len(),
            subst_len: self.subst.len(),
        }
    }

    /// Restore state from a snapshot (on REPL error).
    pub fn restore(&mut self, snapshot: ReplSnapshot) {
        self.next_id = snapshot.next_type_id;
        self.subst.retain(|id, _| *id < snapshot.next_type_id);
        self.expr_types.clear();
        self.method_resolutions.clear();
        self.warnings.clear();
        // Symbol table entries added after snapshot are removed
        // We track by count, but HashMap doesn't preserve order.
        // For Ring 0, we accept this limitation -- full REPL restore
        // is implemented in Wave 3 with proper tracking.
    }

    // --- Known types lookup (for resolve_type_expr) ---

    /// Build a map of known type names for type expression resolution.
    pub(crate) fn known_type_names(&self) -> crate::resolve::KnownTypes {
        self.type_defs.known_types()
    }
}

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
}
