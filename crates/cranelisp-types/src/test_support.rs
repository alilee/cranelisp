//! Feature-gated helpers for constructing one symbol table in tests.

use crate::{
    Binding, CallableOrigin, CodeStore, LinkerStore, ModuleFullPath, Scheme, Symbol, SymbolTable,
    Visibility,
};

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
