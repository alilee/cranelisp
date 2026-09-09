use cranelisp_types::{
    Binding, Decl, FQSymbol, Symbol, SymbolTable, SymbolTables, Type, TypeRecord, Visibility,
};

fn declaration() -> Decl<()> {
    Decl::Type(TypeRecord::Intrinsic {
        ty: Type::Int,
        docstring: None,
    })
}

// spec: spec/08-modules.md §8.6.4–§8.6.5 — distinct canonical declarations
// may share a spelling; registration retains every candidate and ambiguity is
// decided only at the use site.
#[test]
fn one_entry_retains_canonical_binding_and_all_terminal_name_candidates() {
    let mut table = SymbolTable::new("m".into());
    for canonical in ["Box.v", "HasV.v"] {
        table
            .install_binding(
                Symbol::from(canonical),
                Binding::new(declaration(), Visibility::Public),
            )
            .unwrap();
        table
            .expose_candidate(
                Symbol::from("v"),
                FQSymbol {
                    module: "m".into(),
                    symbol: Symbol::from(canonical),
                },
                Visibility::Public,
            )
            .unwrap();
    }

    assert!(table.get("v").is_none(), "a reference is not a declaration");
    assert_eq!(table.name_candidates(&Symbol::from("v")).len(), 2);
    assert_eq!(
        table.name_candidates(&Symbol::from("Box.v"))[0]
            .source
            .symbol,
        Symbol::from("Box.v"),
        "the canonical binding is its own implicit candidate"
    );

    let tables: SymbolTables<(), ()> = SymbolTables::new();
    table.validate_name_candidates(&tables).unwrap();
}
