use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use cranelisp_types::{
    ExportSpec, ImportNames, ImportSpec, ModDecl, ModuleFullPath, ModuleName, Span, Symbol,
    Visibility,
};

use super::*;

/// Published state for a project rooted at `/proj` with entry `user` and a
/// lib directory at `/lib`.
struct World {
    tables: dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    products: dashmap::DashMap<ModuleFullPath, TypecheckProduct>,
    prelude_fallback: cranelisp_typecheck::PreludeFallback,
    entry: ModuleFullPath,
    root: PathBuf,
}

enum File {
    Project,
    Library,
    At(&'static str),
    None,
}

impl World {
    fn new() -> Self {
        let world = World {
            tables: dashmap::DashMap::new(),
            products: dashmap::DashMap::new(),
            prelude_fallback: Default::default(),
            entry: ModuleFullPath::from("user"),
            root: PathBuf::from("/proj"),
        };
        world.module("user", File::Project)
    }

    fn module(self, name: &str, file: File) -> Self {
        let path = ModuleFullPath::from(name);
        let relative = format!("{}.cl", name.replace('.', "/"));
        let file_path = match file {
            File::Project => Some(self.root.join(relative)),
            File::Library => Some(Path::new("/lib").join(relative)),
            File::At(at) => Some(PathBuf::from(at)),
            File::None => None,
        };
        self.products.insert(
            path.clone(),
            TypecheckProduct {
                file_path,
                source_text: None,
                unresolved_dispatch: Vec::new(),
            },
        );
        self.tables
            .insert(path.clone(), SessionSymbolTable::new_with_params(path));
        self
    }

    fn table(
        &self,
        module: &str,
    ) -> dashmap::mapref::one::RefMut<'_, ModuleFullPath, SessionSymbolTable> {
        self.tables
            .get_mut(&ModuleFullPath::from(module))
            .unwrap_or_else(|| panic!("fixture module {module} exists"))
    }

    fn import(self, from: &str, to: &str, names: ImportNames) -> Self {
        self.table(from).imports.push(ImportSpec {
            module_path: ModuleFullPath::from(to),
            alias: None,
            names,
            span: Span::SYNTHETIC,
        });
        self
    }

    fn import_alias(self, from: &str, to: &str, alias: &str) -> Self {
        self.table(from).imports.push(ImportSpec {
            module_path: ModuleFullPath::from(to),
            alias: Some(ModuleName::from(alias)),
            names: ImportNames::None,
            span: Span::SYNTHETIC,
        });
        self
    }

    fn export(self, from: &str, to: &str, names: ImportNames) -> Self {
        self.table(from).exports.push(ExportSpec {
            module_path: ModuleFullPath::from(to),
            names,
            span: Span::SYNTHETIC,
        });
        self
    }

    fn declare(self, parent: &str, child: &str, visibility: Visibility) -> Self {
        self.table(parent).submodules.push(ModDecl {
            name: ModuleName::from(child),
            visibility,
            inline_body: None,
            span: Span::SYNTHETIC,
        });
        self
    }

    fn prelude_on(self, module: &str) -> Self {
        self.prelude_fallback
            .insert(ModuleFullPath::from(module), true);
        self
    }

    fn inputs(&self) -> SelectionInputs<'_> {
        SelectionInputs {
            tables: &self.tables,
            products: &self.products,
            prelude_fallback: &self.prelude_fallback,
            entry: &self.entry,
            project_root: &self.root,
        }
    }

    fn chain(&self) -> BTreeSet<String> {
        self.inputs()
            .chain_modules()
            .expect("selection succeeds")
            .iter()
            .map(ToString::to_string)
            .collect()
    }
}

fn names(list: &[&str]) -> ImportNames {
    ImportNames::Specific(list.iter().copied().map(Symbol::from).collect())
}

fn set(items: &[&str]) -> BTreeSet<String> {
    items.iter().map(|s| s.to_string()).collect()
}

// spec: repl/spec/00-cli-invocation.md §0.2.2 Test Mode (`--test`) — the chain
// runs through non-empty imports and exports and through declared `(mod …)`
// and `(mod- …)` children (design/int/test-runner.md §10 selection row 1).
#[test]
fn chain_follows_imports_exports_and_declared_children() {
    let world = World::new()
        .module("a", File::Project)
        .module("b", File::Project)
        .module("b.c", File::Project)
        .module("b.d", File::Project)
        .import("user", "a", names(&["fa"]))
        .export("a", "b", ImportNames::Glob)
        .declare("b", "c", Visibility::Public)
        .declare("b", "d", Visibility::Private);
    assert_eq!(world.chain(), set(&["user", "a", "b", "b.c", "b.d"]));
}

// spec: repl/spec/00-cli-invocation.md §0.2.2 Test Mode (`--test`) — the chain
// stops at a library module: neither it, its declared child nor a project
// module reachable only through it is selected (§10 selection row 2).
#[test]
fn chain_stops_at_a_library_module() {
    let world = World::new()
        .module("lm", File::Library)
        .module("lm.kid", File::Library)
        .module("p", File::Project)
        .import("user", "lm", names(&["fl"]))
        .declare("lm", "kid", Visibility::Public)
        .import("lm", "p", names(&["fp"]));
    assert_eq!(world.chain(), set(&["user"]));
}

// spec: repl/spec/00-cli-invocation.md §0.2.2 Test Mode (`--test`) — a
// submodule of a library module is a library module even when its recorded
// file is its project-root candidate (§10 selection row 3).
#[test]
fn child_of_a_library_parent_is_library_whatever_its_file() {
    let world = World::new()
        .module("lm", File::Library)
        .module("lm.kid", File::Project)
        .declare("lm", "kid", Visibility::Public)
        .import("user", "lm.kid", ImportNames::Glob);
    assert_eq!(
        world.inputs().classify(&ModuleFullPath::from("lm.kid")),
        ModuleClass::Library
    );
    assert_eq!(world.chain(), set(&["user"]));
}

// spec: repl/spec/00-cli-invocation.md §0.2.2 Test Mode (`--test`) — a bare
// import names the importer's declared child when it declares one, and the
// root module otherwise (§10 selection row 4).
#[test]
fn bare_import_resolves_through_declared_children() {
    let declared = World::new()
        .module("q", File::Project)
        .module("user.q", File::Project)
        .declare("user", "q", Visibility::Private)
        .import("user", "q", names(&["f"]));
    assert_eq!(declared.chain(), set(&["user", "user.q"]));

    let undeclared = World::new()
        .module("q", File::Project)
        .module("user.q", File::Project)
        .import("user", "q", names(&["f"]));
    assert_eq!(undeclared.chain(), set(&["user", "q"]));
}

// spec: repl/spec/00-cli-invocation.md §0.2.2 Test Mode (`--test`) — an import
// cycle terminates and each module is selected once (§10 selection row 5).
#[test]
fn import_cycle_terminates_and_selects_each_module_once() {
    let world = World::new()
        .module("a", File::Project)
        .module("b", File::Project)
        .import("user", "a", ImportNames::Glob)
        .import("a", "b", ImportNames::Glob)
        .import("b", "a", ImportNames::Glob)
        .import("b", "user", ImportNames::Glob);
    let chain = world.inputs().chain_modules().expect("selection succeeds");
    assert_eq!(chain.len(), 3, "{chain:?}");
    assert_eq!(world.chain(), set(&["user", "a", "b"]));
}

// spec: design/int/test-runner.md §4.2 — an admitted edge to a module with no
// published table is an invariant error naming the module (§10 selection
// row 6).
#[test]
fn admitted_edge_to_a_missing_table_is_an_error_naming_it() {
    let world = World::new().import("user", "ghost", ImportNames::Glob);
    let error = world
        .inputs()
        .chain_modules()
        .expect_err("a missing table is refused");
    assert!(error.to_string().contains("`ghost`"), "{error}");
}

// spec: repl/spec/00-cli-invocation.md §0.2.2 Test Mode (`--test`) — project
// and library are classified by resolution tier, not by path prefix; a module
// with no recorded file is unfiled; the entry is a project module (§10
// selection row 7).
#[test]
fn classifier_uses_the_resolution_tier_not_a_path_prefix() {
    let world = World::new()
        .module("stdlib.foo", File::At("/proj/stdlib/foo.cl"))
        .module("foo", File::At("/proj/stdlib/foo.cl"))
        .module("synthetic", File::None);
    let inputs = world.inputs();
    let class = |m: &str| inputs.classify(&ModuleFullPath::from(m));
    assert_eq!(class("stdlib.foo"), ModuleClass::Project);
    assert_eq!(class("foo"), ModuleClass::Library);
    assert_eq!(class("synthetic"), ModuleClass::Unfiled);
    assert_eq!(class("user"), ModuleClass::Project);

    let library_entry = World::new().module("user", File::Library);
    assert_eq!(
        library_entry
            .inputs()
            .classify(&ModuleFullPath::from("user")),
        ModuleClass::Project
    );
}

// spec: repl/spec/00-cli-invocation.md §0.2.2 Test Mode (`--test`) — null,
// empty and alias-only imports and exports are not chain edges (§10 selection
// row 9).
#[test]
fn null_empty_and_alias_only_entries_are_not_edges() {
    let world = World::new()
        .module("nul", File::Project)
        .module("empty", File::Project)
        .module("al", File::Project)
        .module("ex", File::Project)
        .import("user", "nul", ImportNames::None)
        .import("user", "empty", ImportNames::Specific(Vec::new()))
        .import_alias("user", "al", "alx")
        .export("user", "ex", ImportNames::None);
    assert_eq!(world.chain(), set(&["user"]));
}

// spec: repl/spec/00-cli-invocation.md §0.2.2 Test Mode (`--test`) — the
// implicit prelude is an edge; a project prelude is selected and followed, a
// library prelude is neither, whether reached implicitly or by an explicit
// import (§10 selection row 10).
#[test]
fn prelude_edge_follows_the_library_stop() {
    let project_prelude = World::new()
        .module("prelude", File::Project)
        .module("pp", File::Project)
        .import("prelude", "pp", ImportNames::Glob)
        .prelude_on("user");
    assert_eq!(project_prelude.chain(), set(&["user", "prelude", "pp"]));

    let library_prelude = World::new()
        .module("prelude", File::Library)
        .module("pp", File::Project)
        .import("prelude", "pp", ImportNames::Glob)
        .prelude_on("user");
    assert_eq!(library_prelude.chain(), set(&["user"]));

    let explicit_library_prelude = World::new()
        .module("prelude", File::Library)
        .module("pp", File::Project)
        .import("prelude", "pp", ImportNames::Glob)
        .import("user", "prelude", ImportNames::Glob);
    assert_eq!(explicit_library_prelude.chain(), set(&["user"]));

    let bit_without_prelude = World::new().prelude_on("user");
    assert_eq!(bit_without_prelude.chain(), set(&["user"]));
}

// spec: repl/spec/16-test-discovery.md §16.2.2 `/run-all-tests` — every loaded
// module except library modules: project and unfiled modules are kept (§10
// selection row 11).
#[test]
fn run_all_membership_excludes_only_library_modules() {
    let world = World::new()
        .module("p", File::Project)
        .module("lm", File::Library)
        .module("lm.kid", File::Project)
        .declare("lm", "kid", Visibility::Public)
        .module("scratch", File::None);
    let members: BTreeSet<String> = world
        .inputs()
        .non_library_modules()
        .iter()
        .map(ToString::to_string)
        .collect();
    assert_eq!(members, set(&["user", "p", "scratch"]));
}
