//! Which modules a test run covers (`design/int/test-runner.md` §4): the
//! project/library classifier, the `--test` chain walk and `/run-all-tests`
//! membership. Every read is a keyed read of published session state; the walk
//! selects modules and resolves no name (Principle 17).

use std::collections::{HashSet, VecDeque};
use std::path::Path;

use cranelisp_types::{CranelispError, ErrorLocation, ImportNames, ModuleFullPath, Span};

use crate::code::SessionSymbolTable;
use crate::imports::{DeclaredChildren, declared_child_path};
use crate::session_v4::TypecheckProduct;

/// A module's class for test selection (§0.2.2).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ModuleClass {
    /// The entry module, a module resolved from the project root, or a
    /// declared child of a project module.
    Project,
    /// A module resolved from a lib directory, or a declared child of one.
    Library,
    /// A module with no recorded source file: synthetic, platform or
    /// REPL-created.
    Unfiled,
}

/// The published state selection reads.
pub(crate) struct SelectionInputs<'s> {
    pub(crate) tables: &'s dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    pub(crate) products: &'s dashmap::DashMap<ModuleFullPath, TypecheckProduct>,
    pub(crate) prelude_fallback: &'s cranelisp_typecheck::PreludeFallback,
    pub(crate) entry: &'s ModuleFullPath,
    pub(crate) project_root: &'s Path,
}

impl SelectionInputs<'_> {
    pub(crate) fn classify(&self, module: &ModuleFullPath) -> ModuleClass {
        if module == self.entry {
            return ModuleClass::Project;
        }
        if let Some(parent) = self.declaring_parent(module) {
            return self.classify(&parent);
        }
        let recorded = self
            .products
            .get(module)
            .and_then(|product| product.file_path.clone());
        match recorded {
            Some(file)
                if file == crate::pipeline::project_root_candidate(module, self.project_root) =>
            {
                ModuleClass::Project
            }
            Some(_) => ModuleClass::Library,
            None => ModuleClass::Unfiled,
        }
    }

    /// The parent whose table declares `module` as a `(mod …)`/`(mod- …)`
    /// child, derived exactly as enrolment derives the child's path.
    fn declaring_parent(&self, module: &ModuleFullPath) -> Option<ModuleFullPath> {
        let (parent, _) = module.as_ref().rsplit_once('.')?;
        let parent = ModuleFullPath::from(parent);
        let table = self.tables.get(&parent)?;
        table
            .submodules
            .iter()
            .any(|decl| declared_child_path(&parent, decl.name.as_ref()) == *module)
            .then_some(parent)
    }

    /// The `--test` selection: the entry module and every project module
    /// reachable from it through admitted edges, never through a module that
    /// is not a project module. Returned in visit order.
    pub(crate) fn chain_modules(&self) -> Result<Vec<ModuleFullPath>, CranelispError> {
        let mut selected = Vec::new();
        let mut visited = HashSet::from([self.entry.clone()]);
        let mut queue = VecDeque::from([self.entry.clone()]);
        while let Some(module) = queue.pop_front() {
            if self.classify(&module) != ModuleClass::Project {
                continue;
            }
            for target in self.edges(&module)? {
                if visited.insert(target.clone()) {
                    queue.push_back(target);
                }
            }
            selected.push(module);
        }
        Ok(selected)
    }

    /// The chain edges out of `module` (§4.2). Every target has a table.
    fn edges(&self, module: &ModuleFullPath) -> Result<Vec<ModuleFullPath>, CranelispError> {
        let mut edges = {
            let table = self
                .tables
                .get(module)
                .ok_or_else(|| missing_table(module))?;
            let children = DeclaredChildren::of(module, &table.submodules);
            let imports = table
                .imports
                .iter()
                .filter(|spec| names_list_is_admitted(&spec.names))
                .map(|spec| children.resolve(&spec.module_path));
            let exports = table
                .exports
                .iter()
                .filter(|spec| names_list_is_admitted(&spec.names))
                .map(|spec| children.resolve(&spec.module_path));
            let declared = table
                .submodules
                .iter()
                .map(|decl| declared_child_path(module, decl.name.as_ref()));
            imports.chain(exports).chain(declared).collect::<Vec<_>>()
        };
        if let Some(target) = edges
            .iter()
            .find(|target| !self.tables.contains_key(*target))
        {
            return Err(missing_table(target));
        }
        let prelude = ModuleFullPath::from(crate::expander::PRELUDE_MODULE);
        let implicit_prelude = self.prelude_fallback.get(module).is_some_and(|on| *on);
        if implicit_prelude && self.tables.contains_key(&prelude) {
            edges.push(prelude);
        }
        Ok(edges)
    }

    /// `/run-all-tests` membership: every loaded module except library
    /// modules.
    pub(crate) fn non_library_modules(&self) -> Vec<ModuleFullPath> {
        let loaded: Vec<ModuleFullPath> = self.tables.iter().map(|t| t.key().clone()).collect();
        loaded
            .into_iter()
            .filter(|module| self.classify(module) != ModuleClass::Library)
            .collect()
    }
}

/// An `import` or `export` entry is an edge only when its names list is not
/// empty (§0.2.2): alias-only and null entries name no names.
fn names_list_is_admitted(names: &ImportNames) -> bool {
    match names {
        ImportNames::Specific(names) => !names.is_empty(),
        ImportNames::Glob | ImportNames::MemberGlob(_) => true,
        ImportNames::None => false,
    }
}

/// Compilation loads every admitted edge's target, so a missing table is an
/// integration defect.
fn missing_table(module: &ModuleFullPath) -> CranelispError {
    CranelispError::ModuleError {
        message: format!(
            "test selection reached module `{module}`, which has no loaded symbol table; \
             every module the test chain reaches must already be compiled"
        ),
        location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
    }
}

#[cfg(test)]
mod tests;
