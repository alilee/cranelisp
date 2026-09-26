use super::*;
use crate::{
    Binding, CallableArm, CallableOrigin, Decl, Life, ModuleAliasEntry, ModuleFullPath, Scheme,
    SymbolTable, Visibility,
};
use std::collections::HashMap;

fn scheme() -> Scheme {
    Scheme {
        type_vars: Vec::new(),
        constraints: HashMap::new(),
        ty: crate::Type::Int,
    }
}

fn declared(visibility: Visibility) -> Binding {
    Binding::new(
        Decl::Callable(crate::Callable {
            docstring: None,
            seq: 0,
            origin: CallableOrigin::Plain,
            arm: CallableArm::new(scheme(), Vec::new(), Life::Declared { prior: None }),
        }),
        visibility,
    )
}

fn table(path: &str, entries: Vec<(&str, Binding)>) -> SymbolTable {
    let mut table = SymbolTable::new(ModuleFullPath::from(path));
    for (name, binding) in entries {
        if binding.callable().is_some() {
            let callable = binding.callable().unwrap();
            table
                .declare(
                    Symbol::from(name),
                    callable.arm.scheme.clone(),
                    callable.arm.param_names.clone(),
                    callable.docstring.clone(),
                    callable.seq,
                    callable.origin.clone(),
                    binding.visibility,
                )
                .unwrap();
        } else {
            table.install_binding(Symbol::from(name), binding).unwrap();
        }
    }
    table
}

fn alias_entry(target: &str, visibility: Visibility) -> ModuleAliasEntry {
    ModuleAliasEntry::new(ModuleFullPath::from(target), visibility, Span::SYNTHETIC)
}

fn expose(
    table: &mut SymbolTable,
    local_name: &str,
    module: &str,
    symbol: &str,
    visibility: Visibility,
) {
    table
        .expose_candidate(
            Symbol::from(local_name),
            FQSymbol {
                module: ModuleFullPath::from(module),
                symbol: Symbol::from(symbol),
            },
            visibility,
        )
        .unwrap();
}

#[test]
fn module_alias_key_is_owner_scoped() {
    assert_eq!(
        module_alias_key(&ModuleFullPath::from("m.n"), "u"),
        ModuleFullPath::from("m.n.u")
    );
    assert_eq!(
        module_alias_key(&ModuleFullPath::from(""), "u"),
        ModuleFullPath::from("u")
    );
}

#[test]
fn scoped_alias_exact_and_undeclared_passthrough() {
    let aliases = ModuleAliases::new();
    aliases.insert(
        module_alias_key(&ModuleFullPath::from("client"), "u"),
        alias_entry("core.util", Visibility::Private),
    );
    assert_eq!(
        substitute_module_alias(
            &aliases,
            &ModuleFullPath::from("client"),
            &ModuleFullPath::from("u")
        ),
        ModuleFullPath::from("core.util")
    );
    assert_eq!(
        substitute_module_alias(
            &aliases,
            &ModuleFullPath::from("other"),
            &ModuleFullPath::from("u")
        ),
        ModuleFullPath::from("u")
    );
}

#[test]
fn two_referrers_cannot_borrow_each_others_local_alias() {
    let aliases = ModuleAliases::new();
    aliases.insert(
        module_alias_key(&ModuleFullPath::from("a"), "u"),
        alias_entry("left", Visibility::Private),
    );
    aliases.insert(
        module_alias_key(&ModuleFullPath::from("b"), "u"),
        alias_entry("right", Visibility::Private),
    );
    assert_eq!(
        substitute_module_alias(
            &aliases,
            &ModuleFullPath::from("a"),
            &ModuleFullPath::from("u.deep")
        ),
        ModuleFullPath::from("left.deep")
    );
    assert_eq!(
        substitute_module_alias(
            &aliases,
            &ModuleFullPath::from("b"),
            &ModuleFullPath::from("u.deep")
        ),
        ModuleFullPath::from("right.deep")
    );
}

#[test]
fn public_submodule_mount_walks_by_resolved_prefix() {
    let aliases = ModuleAliases::new();
    aliases.insert(
        module_alias_key(&ModuleFullPath::from("client"), "u"),
        alias_entry("lib", Visibility::Private),
    );
    aliases.insert(
        module_alias_key(&ModuleFullPath::from("lib"), "sub"),
        alias_entry("mounted.target", Visibility::Public),
    );
    assert_eq!(
        substitute_module_alias(
            &aliases,
            &ModuleFullPath::from("client"),
            &ModuleFullPath::from("u.sub.deep")
        ),
        ModuleFullPath::from("mounted.target.deep")
    );
}

#[test]
fn private_submodule_mount_is_not_traversed_downstream() {
    let aliases = ModuleAliases::new();
    aliases.insert(
        module_alias_key(&ModuleFullPath::from("lib"), "hidden"),
        alias_entry("secret", Visibility::Private),
    );
    assert_eq!(
        substitute_module_alias(
            &aliases,
            &ModuleFullPath::from("client"),
            &ModuleFullPath::from("lib.hidden.deep")
        ),
        ModuleFullPath::from("lib.hidden.deep")
    );
}

#[test]
fn referring_module_may_traverse_its_private_full_path_mount() {
    let aliases = ModuleAliases::new();
    aliases.insert(
        module_alias_key(&ModuleFullPath::from("client"), "hidden"),
        alias_entry("secret", Visibility::Private),
    );
    assert_eq!(
        substitute_module_alias(
            &aliases,
            &ModuleFullPath::from("client"),
            &ModuleFullPath::from("client.hidden.deep")
        ),
        ModuleFullPath::from("secret.deep")
    );
}

#[test]
fn alias_walk_refuses_more_than_the_shared_depth_limit() {
    let aliases = ModuleAliases::new();
    aliases.insert(
        module_alias_key(&ModuleFullPath::from("client"), "u"),
        alias_entry("n0", Visibility::Private),
    );
    let mut segments = vec!["u".to_string()];
    for index in 0..CHAIN_FOLLOW_DEPTH_LIMIT {
        let segment = format!("s{index}");
        aliases.insert(
            module_alias_key(&ModuleFullPath::from(format!("n{index}")), &segment),
            alias_entry(&format!("n{}", index + 1), Visibility::Public),
        );
        segments.push(segment);
    }
    let path = ModuleFullPath::from(segments.join("."));
    assert_eq!(
        substitute_module_alias(&aliases, &ModuleFullPath::from("client"), &path),
        path
    );
}

#[test]
fn unqualified_import_chain_returns_terminal_storage_key() {
    let mut current = table("client", vec![]);
    expose(
        &mut current,
        "renamed",
        "dep",
        "actual",
        Visibility::Private,
    );
    let dep = table("dep", vec![("actual", declared(Visibility::Public))]);
    let tables = SymbolTables::new();
    tables.insert(ModuleFullPath::from("client"), current.clone());
    tables.insert(ModuleFullPath::from("dep"), dep);
    let view = View::single(&current);
    let aliases = ModuleAliases::new();
    let current_path = ModuleFullPath::from("client");
    let scope = ResolutionScope::new(&tables, &aliases, &view, &current_path, None);
    let resolved = scope.resolve("renamed", Span::SYNTHETIC).unwrap();
    assert_eq!(resolved.canonical.module, ModuleFullPath::from("dep"));
    assert_eq!(resolved.canonical.symbol, Symbol::from("actual"));
}

#[test]
fn qualified_resolution_uses_referring_module_alias() {
    let current = table("client", vec![]);
    let dep = table("dep", vec![("f", declared(Visibility::Public))]);
    let tables = SymbolTables::new();
    tables.insert(ModuleFullPath::from("client"), current.clone());
    tables.insert(ModuleFullPath::from("dep"), dep);
    let aliases = ModuleAliases::new();
    aliases.insert(
        module_alias_key(&ModuleFullPath::from("client"), "u"),
        alias_entry("dep", Visibility::Private),
    );
    let view = View::single(&current);
    let current_path = ModuleFullPath::from("client");
    let scope = ResolutionScope::new(&tables, &aliases, &view, &current_path, None);
    assert_eq!(
        scope
            .resolve("u/f", Span::SYNTHETIC)
            .unwrap()
            .canonical
            .module,
        ModuleFullPath::from("dep")
    );
}

#[test]
fn referring_alias_precedes_same_spelled_real_module() {
    let current = table("client", vec![]);
    let alias_target = table("dep", vec![("f", declared(Visibility::Public))]);
    let same_spelled_module = table("u", vec![("f", declared(Visibility::Public))]);
    let tables = SymbolTables::new();
    tables.insert(ModuleFullPath::from("client"), current.clone());
    tables.insert(ModuleFullPath::from("dep"), alias_target);
    tables.insert(ModuleFullPath::from("u"), same_spelled_module);
    let aliases = ModuleAliases::new();
    aliases.insert(
        module_alias_key(&ModuleFullPath::from("client"), "u"),
        alias_entry("dep", Visibility::Private),
    );
    let view = View::single(&current);
    let current_path = ModuleFullPath::from("client");
    let scope = ResolutionScope::new(&tables, &aliases, &view, &current_path, None);

    assert_eq!(
        scope
            .resolve("u/f", Span::SYNTHETIC)
            .unwrap()
            .canonical
            .module,
        ModuleFullPath::from("dep")
    );
}

#[test]
fn qualified_private_terminal_is_reported_private() {
    let current = table("client", vec![]);
    let dep = table("dep", vec![("f", declared(Visibility::Private))]);
    let tables = SymbolTables::new();
    tables.insert(ModuleFullPath::from("client"), current.clone());
    tables.insert(ModuleFullPath::from("dep"), dep);
    let aliases = ModuleAliases::new();
    let view = View::single(&current);
    let current_path = ModuleFullPath::from("client");
    let scope = ResolutionScope::new(&tables, &aliases, &view, &current_path, None);
    assert!(matches!(
        scope.resolve("dep/f", Span::SYNTHETIC),
        Err(ResolveError::PrivateInaccessible { .. })
    ));
}

// spec: spec/08-modules.md §8.9.2 and spec/09-macros.md §§9.1.3/9.4.4.
//   tests/plan/s121-test-plan.md §3.9 QR-1.
#[test]
fn qualified_short_exposure_resolves_exact_terminal_without_leaking_or_exposing_private() {
    let current = table("client", vec![]);
    let mut dep = table("dep", vec![("SList.SNil", declared(Visibility::Public))]);
    expose(&mut dep, "SNil", "dep", "SList.SNil", Visibility::Public);
    expose(
        &mut dep,
        "HiddenNil",
        "dep",
        "SList.SNil",
        Visibility::Private,
    );
    let tables = SymbolTables::new();
    tables.insert(ModuleFullPath::from("client"), current.clone());
    tables.insert(ModuleFullPath::from("dep"), dep);
    let aliases = ModuleAliases::new();
    let view = View::single(&current);
    let current_path = ModuleFullPath::from("client");
    let scope = ResolutionScope::new(&tables, &aliases, &view, &current_path, None);
    let canonical = FQSymbol {
        module: ModuleFullPath::from("dep"),
        symbol: Symbol::from("SList.SNil"),
    };

    assert_eq!(
        scope
            .resolve("dep/SList.SNil", Span::SYNTHETIC)
            .unwrap()
            .canonical,
        canonical
    );
    assert_eq!(
        scope
            .resolve("dep/SNil", Span::SYNTHETIC)
            .unwrap()
            .canonical,
        canonical
    );
    assert!(matches!(
        scope.resolve("SNil", Span::SYNTHETIC),
        Err(ResolveError::TypeNotFound { .. })
    ));
    assert!(matches!(
        scope.resolve("dep/HiddenNil", Span::SYNTHETIC),
        Err(ResolveError::TypeNotFound { .. })
    ));
}

// spec: spec/08-modules.md §8.6.5.
//   tests/plan/s121-test-plan.md §3.9 QR-1.
#[test]
fn qualified_short_exposure_preserves_distinct_terminal_ambiguity() {
    let current = table("client", vec![]);
    let mut dep = table(
        "dep",
        vec![
            ("Left.value", declared(Visibility::Public)),
            ("Right.value", declared(Visibility::Public)),
        ],
    );
    let left = FQSymbol {
        module: ModuleFullPath::from("dep"),
        symbol: Symbol::from("Left.value"),
    };
    let right = FQSymbol {
        module: ModuleFullPath::from("dep"),
        symbol: Symbol::from("Right.value"),
    };
    dep.expose_candidate(Symbol::from("name"), left.clone(), Visibility::Public)
        .unwrap();
    dep.expose_candidate(Symbol::from("name"), right.clone(), Visibility::Public)
        .unwrap();
    let tables = SymbolTables::new();
    tables.insert(ModuleFullPath::from("client"), current.clone());
    tables.insert(ModuleFullPath::from("dep"), dep);
    let aliases = ModuleAliases::new();
    let view = View::single(&current);
    let current_path = ModuleFullPath::from("client");
    let scope = ResolutionScope::new(&tables, &aliases, &view, &current_path, None);

    let Err(ResolveError::Ambiguous { candidates, .. }) =
        scope.resolve("dep/name", Span::SYNTHETIC)
    else {
        panic!("two distinct qualified candidates must remain ambiguous");
    };
    assert_eq!(candidates.len(), 2);
    assert!(candidates.contains(&left));
    assert!(candidates.contains(&right));
}

#[test]
fn macro_projection_reads_macro_declaration() {
    let mut current = table("m", Vec::new());
    current
        .install_macro(
            Symbol::from("mac"),
            None,
            0,
            crate::Sexp::List(Vec::new(), Span::SYNTHETIC),
            Vec::new(),
            Visibility::Public,
        )
        .unwrap();
    let tables = SymbolTables::new();
    tables.insert(ModuleFullPath::from("m"), current.clone());
    let aliases = ModuleAliases::new();
    let view = View::single(&current);
    let current_path = ModuleFullPath::from("m");
    let scope = ResolutionScope::new(&tables, &aliases, &view, &current_path, None);
    assert_eq!(
        scope
            .resolve_macro_head("mac", Span::SYNTHETIC)
            .unwrap()
            .unwrap()
            .symbol,
        Symbol::from("mac")
    );
}

#[test]
fn macro_projection_filters_nonmacro_candidates_before_deciding_ambiguity() {
    let mut current = table("m", vec![("ordinary", declared(Visibility::Public))]);
    current
        .install_macro(
            Symbol::from("macro"),
            None,
            0,
            crate::Sexp::List(Vec::new(), Span::SYNTHETIC),
            Vec::new(),
            Visibility::Public,
        )
        .unwrap();
    expose(&mut current, "head", "m", "ordinary", Visibility::Private);
    expose(&mut current, "head", "m", "macro", Visibility::Private);
    let tables = SymbolTables::new();
    tables.insert(ModuleFullPath::from("m"), current.clone());
    let aliases = ModuleAliases::new();
    let view = View::single(&current);
    let current_path = ModuleFullPath::from("m");
    let scope = ResolutionScope::new(&tables, &aliases, &view, &current_path, None);

    assert!(matches!(
        scope.resolve("head", Span::SYNTHETIC),
        Err(ResolveError::Ambiguous { .. })
    ));
    assert_eq!(
        scope.resolve_macro_head("head", Span::SYNTHETIC).unwrap(),
        Some(FQSymbol {
            module: ModuleFullPath::from("m"),
            symbol: Symbol::from("macro"),
        })
    );
}

#[test]
fn prelude_fallback_remains_public_head_only() {
    let current = table("client", vec![]);
    let prelude = table("prelude", vec![("x", declared(Visibility::Public))]);
    let tables = SymbolTables::new();
    tables.insert(ModuleFullPath::from("client"), current.clone());
    tables.insert(ModuleFullPath::from("prelude"), prelude);
    let aliases = ModuleAliases::new();
    let view = View::single(&current);
    let current_path = ModuleFullPath::from("client");
    let prelude_path = ModuleFullPath::from("prelude");
    let scope = ResolutionScope::new(&tables, &aliases, &view, &current_path, Some(&prelude_path));
    assert_eq!(
        scope
            .resolve("x", Span::SYNTHETIC)
            .unwrap()
            .canonical
            .module,
        prelude_path
    );
}

#[test]
fn unqualified_candidates_union_inner_and_implicit_prelude_sets() {
    let current = table("client", vec![("x", declared(Visibility::Private))]);
    let prelude = table("prelude", vec![("x", declared(Visibility::Public))]);
    let tables = SymbolTables::new();
    tables.insert(ModuleFullPath::from("client"), current.clone());
    tables.insert(ModuleFullPath::from("prelude"), prelude);
    let aliases = ModuleAliases::new();
    let view = View::single(&current);
    let current_path = ModuleFullPath::from("client");
    let prelude_path = ModuleFullPath::from("prelude");
    let scope = ResolutionScope::new(&tables, &aliases, &view, &current_path, Some(&prelude_path));

    let candidates = scope.resolve_candidates("x", Span::SYNTHETIC).unwrap();
    assert_eq!(candidates.len(), 2);
    assert_eq!(candidates[0].canonical.module, current_path);
    assert_eq!(candidates[1].canonical.module, prelude_path);
    assert!(matches!(
        scope.resolve("x", Span::SYNTHETIC),
        Err(ResolveError::Ambiguous { candidates, .. }) if candidates.len() == 2
    ));
}

#[test]
fn implicit_prelude_candidate_for_same_terminal_is_deduplicated() {
    let mut current = table("client", vec![]);
    expose(
        &mut current,
        "x",
        "dependency",
        "terminal",
        Visibility::Private,
    );
    let mut prelude = table("prelude", vec![]);
    expose(
        &mut prelude,
        "x",
        "dependency",
        "terminal",
        Visibility::Public,
    );
    let dependency = table(
        "dependency",
        vec![("terminal", declared(Visibility::Public))],
    );
    let tables = SymbolTables::new();
    tables.insert(ModuleFullPath::from("client"), current.clone());
    tables.insert(ModuleFullPath::from("prelude"), prelude);
    tables.insert(ModuleFullPath::from("dependency"), dependency);
    let aliases = ModuleAliases::new();
    let view = View::single(&current);
    let current_path = ModuleFullPath::from("client");
    let prelude_path = ModuleFullPath::from("prelude");
    let scope = ResolutionScope::new(&tables, &aliases, &view, &current_path, Some(&prelude_path));

    let candidates = scope.resolve_candidates("x", Span::SYNTHETIC).unwrap();
    assert_eq!(candidates.len(), 1);
    assert_eq!(
        candidates[0].canonical,
        FQSymbol {
            module: ModuleFullPath::from("dependency"),
            symbol: Symbol::from("terminal"),
        }
    );
    assert_eq!(
        scope.resolve("x", Span::SYNTHETIC).unwrap().canonical,
        candidates[0].canonical
    );
}

#[test]
fn prelude_alias_head_visibility_controls_public_terminal_fallback() {
    let client_path = ModuleFullPath::from("client");
    let prelude_path = ModuleFullPath::from("prelude");
    let library_path = ModuleFullPath::from("library");
    let current = table("client", vec![]);
    let library = table("library", vec![("terminal", declared(Visibility::Public))]);
    let aliases = ModuleAliases::new();
    let view = View::single(&current);

    let mut private_prelude = table("prelude", vec![]);
    expose(
        &mut private_prelude,
        "visible_name",
        "library",
        "terminal",
        Visibility::Private,
    );
    let private_tables = SymbolTables::new();
    private_tables.insert(client_path.clone(), current.clone());
    private_tables.insert(prelude_path.clone(), private_prelude);
    private_tables.insert(library_path.clone(), library.clone());
    let private_scope = ResolutionScope::new(
        &private_tables,
        &aliases,
        &view,
        &client_path,
        Some(&prelude_path),
    );
    assert!(matches!(
        private_scope.resolve("visible_name", Span::SYNTHETIC),
        Err(ResolveError::TypeNotFound {
            name,
            from_module,
            ..
        }) if name == "visible_name" && from_module == client_path
    ));

    let mut public_prelude = table("prelude", vec![]);
    expose(
        &mut public_prelude,
        "visible_name",
        "library",
        "terminal",
        Visibility::Public,
    );
    let public_tables = SymbolTables::new();
    public_tables.insert(client_path.clone(), current.clone());
    public_tables.insert(prelude_path.clone(), public_prelude);
    public_tables.insert(library_path.clone(), library);
    let public_scope = ResolutionScope::new(
        &public_tables,
        &aliases,
        &view,
        &client_path,
        Some(&prelude_path),
    );
    let resolved = public_scope
        .resolve("visible_name", Span::SYNTHETIC)
        .unwrap();
    assert_eq!(resolved.canonical.module, library_path);
    assert_eq!(resolved.canonical.symbol, Symbol::from("terminal"));
}

#[test]
fn union_view_same_module_candidate_resolves_terminal() {
    let current_path = ModuleFullPath::from("client");
    let staging = table("client", vec![("terminal", declared(Visibility::Private))]);
    let mut staging = staging;
    expose(
        &mut staging,
        "head",
        "client",
        "terminal",
        Visibility::Private,
    );
    let live = table("client", vec![]);
    let tables = SymbolTables::new();
    tables.insert(current_path.clone(), live.clone());
    let aliases = ModuleAliases::new();
    let view = View::union(&staging, &live);
    let scope = ResolutionScope::new(&tables, &aliases, &view, &current_path, None);

    let resolved = scope.resolve("head", Span::SYNTHETIC).unwrap();
    assert_eq!(resolved.canonical.module, current_path);
    assert_eq!(resolved.canonical.symbol, Symbol::from("terminal"));
}

// spec: design/arch/interfaces.md §Qualified lookup dependencies — T5
//   (tests/plan/s122-evidence-delta.md LD-T).
#[test]
fn lookup_module_names_the_table_that_answered_a_foreign_qualified_spelling() {
    let current_path = ModuleFullPath::from("client");
    let prelude_path = ModuleFullPath::from("prelude");
    let mut current = table("client", vec![("k", declared(Visibility::Private))]);
    expose(
        &mut current,
        "renamed",
        "dep",
        "actual",
        Visibility::Private,
    );
    let mut reexporter = table("r", vec![]);
    expose(&mut reexporter, "f", "c", "f", Visibility::Public);
    let tables = SymbolTables::new();
    tables.insert(current_path.clone(), current.clone());
    for (path, names) in [
        ("dep", vec!["f", "actual"]),
        ("c", vec!["f"]),
        ("client.util", vec!["two"]),
        ("util", vec!["three"]),
        ("prelude", vec!["px"]),
    ] {
        let entries = names
            .into_iter()
            .map(|name| (name, declared(Visibility::Public)))
            .collect();
        tables.insert(ModuleFullPath::from(path), table(path, entries));
    }
    tables.insert(ModuleFullPath::from("r"), reexporter);
    let aliases = ModuleAliases::new();
    aliases.insert(
        module_alias_key(&current_path, "u"),
        alias_entry("dep", Visibility::Private),
    );
    let view = View::single(&current);
    let scope = ResolutionScope::new(&tables, &aliases, &view, &current_path, Some(&prelude_path));
    let answered = |name: &str| {
        let resolved = scope.resolve(name, Span::SYNTHETIC).unwrap();
        (
            resolved.canonical.module.to_string(),
            resolved.lookup_module.map(|module| module.to_string()),
        )
    };
    let named = |canonical: &str, lookup: &str| (canonical.to_string(), Some(lookup.to_string()));
    let unrecorded = |canonical: &str| (canonical.to_string(), None);

    assert_eq!(
        answered("u/f"),
        named("dep", "dep"),
        "alias target, not alias"
    );
    assert_eq!(
        answered("r/f"),
        named("c", "r"),
        "spelled hop, not terminal home"
    );
    assert_eq!(
        answered("client.util/two"),
        named("client.util", "client.util")
    );
    assert!(scope.resolve("client.util/three", Span::SYNTHETIC).is_err());
    assert_eq!(
        answered("util/three"),
        named("util", "util"),
        "absolute after child miss"
    );

    assert_eq!(answered("k"), unrecorded("client"));
    assert_eq!(answered("client/k"), unrecorded("client"));
    assert_eq!(answered("renamed"), unrecorded("dep"));
    assert_eq!(answered("px"), unrecorded("prelude"));

    let descendant_path = ModuleFullPath::from("client.util");
    let descendant = table("client.util", vec![]);
    let descendant_view = View::single(&descendant);
    let descendant_scope =
        ResolutionScope::new(&tables, &aliases, &descendant_view, &descendant_path, None);
    let private_ancestor = descendant_scope
        .resolve("client/k", Span::SYNTHETIC)
        .unwrap();
    assert_eq!(
        (
            private_ancestor.canonical.module,
            private_ancestor.lookup_module
        ),
        (current_path.clone(), Some(current_path)),
        "descendant's qualified spelling of an ancestor-private binding"
    );
}
