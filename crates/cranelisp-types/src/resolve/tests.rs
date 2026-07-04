use super::*;
use crate::module::{DefKind, MacroClauseInfo, SymbolTable, UserFnState};
use crate::types::{Scheme, Type};
use std::collections::HashMap;

fn empty_scheme() -> Scheme {
    Scheme { type_vars: vec![], constraints: HashMap::new(), ty: Type::Int }
}

fn def_entry(kind: DefKind, visibility: Visibility) -> ModuleEntry<()> {
    ModuleEntry::def(empty_scheme(), kind).visibility(visibility).build()
}

fn macro_kind() -> DefKind {
    DefKind::Macro {
        clauses_meta: Vec::<MacroClauseInfo>::new(),
        // D1 (S80): compile-path recompile source on the entry. A
        // placeholder empty list suffices for the resolution-only tests
        // here (none drive the recompile path).
        macro_sexp: crate::Sexp::List(vec![], crate::Span::SYNTHETIC),
    }
}

fn tables_with(entries: &[(&str, &str, ModuleEntry<()>)]) -> SymbolTables<(), ()> {
    let tables: SymbolTables<(), ()> = dashmap::DashMap::new();
    for (module, name, entry) in entries {
        let path = ModuleFullPath::from(*module);
        tables
            .entry(path.clone())
            .or_insert_with(|| SymbolTable::<(), ()>::new_with_params(path.clone()))
            .insert(Symbol::from(*name), entry.clone());
    }
    tables
}

fn import(target_module: &str, target_symbol: &str, visibility: Visibility) -> ModuleEntry<()> {
    ModuleEntry::Import {
        source: FQSymbol {
            module: ModuleFullPath::from(target_module),
            symbol: Symbol::from(target_symbol),
        },
        visibility,
    }
}

#[test]
fn resolves_local_short_name() {
    // spec §8.6.6 — unqualified short name in the current module.
    let tables = tables_with(&[("user", "foo", def_entry(DefKind::UserFn { fn_state: UserFnState::NotDetermined }, Visibility::Public))]);
    let user = tables.get(&ModuleFullPath::from("user")).unwrap();
    let view = View::single(&user);
    let current = ModuleFullPath::from("user");
    let r = resolve(&tables, &dashmap::DashMap::new(), &view, &current, "foo", Span::SYNTHETIC)
        .expect("foo resolves");
    assert_eq!(r.home, ModuleFullPath::from("user"));
    assert_eq!(r.fq.symbol, Symbol::from("foo"));
}

#[test]
fn chain_follows_import_to_home() {
    // Principle 17 shape 1 — chain-follow an Import edge to the canonical home.
    let tables = tables_with(&[
        ("dep", "bar", def_entry(DefKind::UserFn { fn_state: UserFnState::NotDetermined }, Visibility::Public)),
        ("user", "bar", import("dep", "bar", Visibility::Private)),
    ]);
    let user = tables.get(&ModuleFullPath::from("user")).unwrap();
    let view = View::single(&user);
    let current = ModuleFullPath::from("user");
    let r = resolve(&tables, &dashmap::DashMap::new(), &view, &current, "bar", Span::SYNTHETIC)
        .expect("bar resolves via import");
    assert_eq!(r.home, ModuleFullPath::from("dep"));
}

#[test]
fn recognises_macro_head() {
    let tables = tables_with(&[("user", "when", def_entry(macro_kind(), Visibility::Public))]);
    let user = tables.get(&ModuleFullPath::from("user")).unwrap();
    let view = View::single(&user);
    let current = ModuleFullPath::from("user");
    let fq = resolve_macro_head(&tables, &dashmap::DashMap::new(), &view, &current, "when", Span::SYNTHETIC)
        .expect("no hard error")
        .expect("when is a macro head");
    assert_eq!(fq.symbol, Symbol::from("when"));
    assert_eq!(fq.module, ModuleFullPath::from("user"));
}

#[test]
fn non_macro_head_is_none_not_error() {
    let tables = tables_with(&[("user", "plain", def_entry(DefKind::UserFn { fn_state: UserFnState::NotDetermined }, Visibility::Public))]);
    let user = tables.get(&ModuleFullPath::from("user")).unwrap();
    let view = View::single(&user);
    let current = ModuleFullPath::from("user");
    let r = resolve_macro_head(&tables, &dashmap::DashMap::new(), &view, &current, "plain", Span::SYNTHETIC)
        .expect("no hard error");
    assert!(r.is_none(), "a non-macro head is Ok(None), not an Err");
}

#[test]
fn forward_reference_absent_from_view_is_none() {
    // Locked defmacro-before-use rule: a name not yet in the view is not
    // a macro head — Ok(None), flows on as an ordinary reference.
    let tables = tables_with(&[("user", "x", def_entry(DefKind::UserFn { fn_state: UserFnState::NotDetermined }, Visibility::Public))]);
    let user = tables.get(&ModuleFullPath::from("user")).unwrap();
    let view = View::single(&user);
    let current = ModuleFullPath::from("user");
    let r = resolve_macro_head(&tables, &dashmap::DashMap::new(), &view, &current, "not-defined-yet", Span::SYNTHETIC)
        .expect("no hard error");
    assert!(r.is_none());
}

#[test]
fn private_inaccessible_outside_subtree() {
    // spec §8.7.3 — qualified access to a private name from outside the
    // defining subtree fails with PrivateInaccessible.
    let tables = tables_with(&[("dep", "secret", def_entry(DefKind::UserFn { fn_state: UserFnState::NotDetermined }, Visibility::Private))]);
    let user = tables.get(&ModuleFullPath::from("dep")).unwrap();
    let view = View::single(&user);
    let current = ModuleFullPath::from("user");
    let err = resolve(&tables, &dashmap::DashMap::new(), &view, &current, "dep/secret", Span::SYNTHETIC)
        .expect_err("private name is inaccessible from user");
    assert!(matches!(err, ResolveError::PrivateInaccessible { .. }));
}

#[test]
fn qualified_unknown_module_distinguished() {
    let tables: SymbolTables<(), ()> = dashmap::DashMap::new();
    let live = SymbolTable::<(), ()>::new_with_params(ModuleFullPath::from("user"));
    let view = View::single(&live);
    let current = ModuleFullPath::from("user");
    let err = resolve(&tables, &dashmap::DashMap::new(), &view, &current, "ghost/sym", Span::SYNTHETIC)
        .expect_err("ghost module is unknown");
    assert!(matches!(err, ResolveError::QualifiedModuleUnknown { .. }));
}

#[test]
fn split_qualified_bare_operator_is_not_qualified() {
    // FIXME 0328 regression: the bare `/` division operator must NOT be
    // mis-parsed as `module/symbol` (Principle 16 — punctuation symbols
    // are not special). The non-empty-part guard on both helpers pins it.
    //
    // Pre-fix logic (`split_once('/')` unguarded) split `/` into
    // ("", "") and treated it as qualified — this assert would fail then.
    assert_eq!(split_qualified("/"), None, "bare `/` is not qualified");
    assert_eq!(split_qualified("//"), None, "bare `//` is not qualified");
    // Leading/trailing slash: one part empty → not qualified.
    assert_eq!(split_qualified("foo/"), None, "trailing slash is not qualified");
    assert_eq!(split_qualified("/bar"), None, "leading slash is not qualified");
    // A plain short name has no `/` at all.
    assert_eq!(split_qualified("foo"), None, "short name is not qualified");
    // The genuine qualified case still works.
    assert_eq!(
        split_qualified("mod/sym"),
        Some((ModuleFullPath::from("mod"), "sym".to_string())),
        "a genuine module/symbol still splits",
    );

    // canonical_symbol must preserve the bare operator, NOT corrupt it to "".
    // Pre-fix (`rsplit_once('/')` unguarded) yielded Symbol::from("") here.
    assert_eq!(canonical_symbol("/"), Symbol::from("/"), "bare `/` preserved");
    assert_eq!(canonical_symbol("mod/sym"), Symbol::from("sym"), "qualified → local symbol");
}

fn alias(target: &str) -> crate::ModuleAliasEntry {
    crate::ModuleAliasEntry::new(
        ModuleFullPath::from(target),
        Visibility::Private,
        Span::SYNTHETIC,
    )
}

#[test]
fn substitute_module_alias_longest_prefix_dot_segment() {
    // spec §8.6.6 step 5 — longest-prefix dot-segment module-alias
    // substitution. Pins the now-public primitive at the seam the S81
    // Principle-7 dedup consolidated onto (the int FQ-autoload boundary
    // and typecheck's resolve_qualified now share this one walk).
    let aliases: ModuleAliases = dashmap::DashMap::new();
    // `(mod util)` short-name alias → full submodule path.
    aliases.insert(ModuleFullPath::from("util"), alias("parent.util"));

    // Exact key match → target.
    assert_eq!(
        substitute_module_alias(&aliases, &ModuleFullPath::from("util")),
        ModuleFullPath::from("parent.util"),
    );
    // Dot-segment prefix → target + carried remainder.
    assert_eq!(
        substitute_module_alias(&aliases, &ModuleFullPath::from("util.inner")),
        ModuleFullPath::from("parent.util.inner"),
    );
    // No alias key is a prefix → unchanged.
    assert_eq!(
        substitute_module_alias(&aliases, &ModuleFullPath::from("other")),
        ModuleFullPath::from("other"),
    );
    // A non-dot-boundary near-match must NOT match (`utility` is not
    // `util` + a dot-segment) → unchanged.
    assert_eq!(
        substitute_module_alias(&aliases, &ModuleFullPath::from("utility")),
        ModuleFullPath::from("utility"),
    );
}

#[test]
fn substitute_module_alias_prefers_longest_prefix() {
    // Two overlapping prefixes both match `a.b.c`; the LONGER key wins.
    let aliases: ModuleAliases = dashmap::DashMap::new();
    aliases.insert(ModuleFullPath::from("a"), alias("X"));
    aliases.insert(ModuleFullPath::from("a.b"), alias("Y"));
    assert_eq!(
        substitute_module_alias(&aliases, &ModuleFullPath::from("a.b.c")),
        ModuleFullPath::from("Y.c"),
        "longest-prefix `a.b` wins over `a`",
    );
}

// ---------------------------------------------------------------------------
// check_binding_addition — the shared §8.6.4 collision predicate (FIXME 0516).
// The rule is a pure function of the (incoming, existing) provenance pair;
// these cells assert IDENTICAL rejection at both binding events (def-event and
// import-event × both orders) plus the allowed/free pairings.
// ---------------------------------------------------------------------------

fn remedy() -> FQSymbol {
    FQSymbol { module: ModuleFullPath::from("util"), symbol: Symbol::from("measure") }
}

use crate::resolve::{BindingProvenance as BP, check_binding_addition};

#[test]
fn binding_addition_def_over_import_rejects() {
    // spec: 08-modules §8.6.4 — the def-event: incoming Definition over an
    // existing explicit import is a collision.
    let name = Symbol::from("measure");
    let e = check_binding_addition(&name, BP::Definition, BP::Import, &remedy(), Span::SYNTHETIC);
    let msg = e.unwrap_err().to_string().to_lowercase();
    assert!(msg.contains("conflict"), "{msg}");
    assert!(msg.contains("util/measure"), "remedy FQ present: {msg}");
}

#[test]
fn binding_addition_def_over_export_and_prelude_reject() {
    let name = Symbol::from("measure");
    for existing in [BP::Export, BP::Prelude] {
        assert!(
            check_binding_addition(&name, BP::Definition, existing, &remedy(), Span::SYNTHETIC)
                .is_err(),
            "def over {existing:?} MUST reject"
        );
    }
}

#[test]
fn binding_addition_import_over_def_rejects() {
    // spec: 08-modules §8.6.4 — the SYMMETRIC companion (the arm the import
    // event was missing; the #8 hole). Incoming Import/Export over an existing
    // local Definition MUST reject IDENTICALLY to the def-event direction.
    let name = Symbol::from("measure");
    for incoming in [BP::Import, BP::Export] {
        let e = check_binding_addition(
            &name,
            incoming,
            BP::Definition,
            &remedy(),
            Span::SYNTHETIC,
        );
        let msg = e.unwrap_err().to_string().to_lowercase();
        assert!(msg.contains("conflict"), "{incoming:?} over def rejects: {msg}");
        assert!(msg.contains("§8.6.4"), "{msg}");
    }
}

#[test]
fn binding_addition_def_over_def_allowed_redefinition() {
    // Own prior definition of the same name — ordinary REPL redefinition.
    let name = Symbol::from("measure");
    assert!(
        check_binding_addition(&name, BP::Definition, BP::Definition, &remedy(), Span::SYNTHETIC)
            .is_ok(),
        "def-over-def is redefinition, allowed"
    );
}

#[test]
fn binding_addition_import_over_import_not_this_predicate() {
    // Import-over-import is the §8.6.5 distinct-terminal rule, NOT this
    // predicate — every import/export vs import/export pairing passes here.
    let name = Symbol::from("measure");
    for incoming in [BP::Import, BP::Export, BP::Prelude] {
        for existing in [BP::Import, BP::Export, BP::Prelude] {
            assert!(
                check_binding_addition(&name, incoming, existing, &remedy(), Span::SYNTHETIC)
                    .is_ok(),
                "{incoming:?} over {existing:?} is not a §8.6.4 collision"
            );
        }
    }
}
