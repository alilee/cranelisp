//! Feature-gated helpers for other crates' tests: a symbol-table builder and
//! the lenient typed-view builder.

use std::collections::HashMap;

use crate::{
    ApplyRef, Binding, CallableOrigin, CodeStore, Expr, FQSymbol, LinkerStore, ModuleFullPath,
    MonoExpr, Scheme, Span, Symbol, SymbolTable, VarRef, Visibility,
};

/// Build a typed view of a test fixture body whose node types need not be
/// concrete.
///
/// Forwards to the lenient builder: a node with a non-concrete or absent type
/// takes a placeholder `ConcreteType::Int`, which is a fabricated type and not
/// a fact about the node. A real-span `Var` or `Apply` with no verdict in
/// `var_refs` or `apply_refs` panics.
pub fn lenient_from_expr(
    expr: &Expr,
    pattern_ctors: &HashMap<Span, FQSymbol>,
    var_refs: &HashMap<Span, VarRef>,
    apply_refs: &HashMap<Span, ApplyRef>,
) -> MonoExpr {
    MonoExpr::lenient_from_expr(expr, pattern_ctors, var_refs, apply_refs)
}

#[allow(clippy::large_enum_variant)]
enum Entry<C: CodeStore> {
    Binding(Symbol, Binding<C>),
    Declared {
        name: Symbol,
        scheme: Scheme,
        origin: CallableOrigin,
        visibility: Visibility,
    },
}

/// Generic, content-agnostic builder for a single symbol table.
pub struct SymbolTableBuilder<C: CodeStore = (), L: LinkerStore = ()> {
    path: ModuleFullPath,
    entries: Vec<Entry<C>>,
    _linker: std::marker::PhantomData<L>,
}

impl<C: CodeStore, L: LinkerStore> SymbolTableBuilder<C, L> {
    pub fn new(path: ModuleFullPath) -> Self {
        Self {
            path,
            entries: Vec::new(),
            _linker: std::marker::PhantomData,
        }
    }

    /// Add a non-callable binding.
    pub fn entry(mut self, name: impl Into<Symbol>, binding: Binding<C>) -> Self {
        self.entries.push(Entry::Binding(name.into(), binding));
        self
    }

    /// Add a callable in the Declared interstage.
    pub fn declared(
        mut self,
        name: impl Into<Symbol>,
        scheme: Scheme,
        origin: CallableOrigin,
        visibility: Visibility,
    ) -> Self {
        self.entries.push(Entry::Declared {
            name: name.into(),
            scheme,
            origin,
            visibility,
        });
        self
    }

    pub fn build(self) -> SymbolTable<C, L> {
        let mut table = SymbolTable::<C, L>::new_with_params(self.path);
        for entry in self.entries {
            match entry {
                Entry::Binding(name, binding) => {
                    table
                        .install_binding(name, binding)
                        .expect("test builder accepts only non-callable bindings");
                }
                Entry::Declared {
                    name,
                    scheme,
                    origin,
                    visibility,
                } => table
                    .declare(name, scheme, Vec::new(), None, 0, origin, visibility)
                    .expect("test declarations must not conflict"),
            }
        }
        table
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Decl, Type, TypeRecord};
    use std::collections::HashMap;

    #[test]
    fn lenient_view_keeps_verdicts_and_fills_a_non_concrete_type() {
        let span = Span::new(3, 12);
        let global = FQSymbol {
            module: ModuleFullPath::from("m"),
            symbol: Symbol::from("generic"),
        };
        let var = Expr::Var {
            name: Symbol::from("generic"),
            span,
            resolved_call: None,
            inferred_type: Some(Box::new(Type::Var(0))),
        };
        let var_refs = HashMap::from([(span, VarRef::Global(global.clone()))]);

        let view = lenient_from_expr(&var, &HashMap::new(), &var_refs, &HashMap::new());

        // The strict builder refuses this node; the lenient one fills its type.
        assert!(MonoExpr::from_expr(&var, &HashMap::new(), &var_refs, &HashMap::new()).is_err());
        match view {
            MonoExpr::Var { resolution, ty, .. } => {
                assert_eq!(resolution, VarRef::Global(global));
                assert_eq!(ty, crate::ConcreteType::Int);
            }
            other => panic!("expected a variable node, found {other:?}"),
        }
    }

    #[test]
    fn builder_populates_bindings_and_declarations() {
        let scheme = Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Int,
        };
        let table: SymbolTable = SymbolTableBuilder::new(ModuleFullPath::from("test"))
            .declared("id", scheme, CallableOrigin::Plain, Visibility::Public)
            .entry(
                "missing",
                Binding::new(
                    Decl::Type(TypeRecord::Intrinsic {
                        ty: Type::Int,
                        docstring: None,
                    }),
                    Visibility::Private,
                ),
            )
            .build();

        assert!(table.get("id").and_then(Binding::callable).is_some());
        assert!(matches!(
            table.get("missing").map(|binding| &binding.declaration),
            Some(Decl::Type(TypeRecord::Intrinsic { ty: Type::Int, .. }))
        ));
    }
}
