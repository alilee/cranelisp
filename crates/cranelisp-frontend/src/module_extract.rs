//! Sexp-level module declaration extraction.
//!
//! Walks top-level S-expressions and extracts `mod`, `mod-`, `import`, and `export`
//! forms into `ModuleStructure`, returning remaining sexps for further processing.
//! This runs before macro expansion per spec §8.12.1.

use std::path::PathBuf;

use cranelisp_types::{
    CranelispError, ExportSpec, ImportNames, ImportSpec, ModDecl, ModuleFullPath, ModuleName,
    ModuleStructure, Sexp, Span,
};

/// Extract module declarations from top-level S-expressions.
///
/// Recognizes `(mod name)`, `(mod- name)`, `(import [...])`, and `(export [...])`.
/// All other sexps pass through unchanged.
///
/// Returns `(ModuleStructure, remaining_sexps)`.
pub fn extract_module_declarations(
    path: ModuleFullPath,
    file_path: Option<PathBuf>,
    sexps: Vec<Sexp>,
) -> Result<(ModuleStructure, Vec<Sexp>), CranelispError> {
    let mut mod_decls = Vec::new();
    let mut import_specs = Vec::new();
    let mut export_specs = Vec::new();
    let mut remaining = Vec::new();

    for sexp in sexps {
        match &sexp {
            Sexp::List(elems, span) if !elems.is_empty() => {
                if let Sexp::Symbol(head, _) = &elems[0] {
                    match head.as_str() {
                        "mod" | "mod-" => {
                            let decl = parse_mod_decl(elems, *span, head == "mod-")?;
                            mod_decls.push(decl);
                            continue;
                        }
                        "import" => {
                            let specs = parse_import(elems, *span)?;
                            import_specs.extend(specs);
                            continue;
                        }
                        "export" => {
                            let specs = parse_export(elems, *span)?;
                            export_specs.extend(specs);
                            continue;
                        }
                        _ => {}
                    }
                }
                remaining.push(sexp);
            }
            _ => remaining.push(sexp),
        }
    }

    let structure = ModuleStructure {
        path,
        file_path,
        mod_decls,
        import_specs,
        export_specs,
        impl_sexps: Vec::new(),
        impls: Vec::new(),
        dll_path: None,
    };

    Ok((structure, remaining))
}

// ---------------------------------------------------------------------------
// mod parsing
// ---------------------------------------------------------------------------

/// Parse `(mod name)`, `(mod name form...)`, `(mod- name)`, or `(mod- name form...)`.
fn parse_mod_decl(elems: &[Sexp], span: Span, is_private: bool) -> Result<ModDecl, CranelispError> {
    if elems.len() < 2 {
        return Err(CranelispError::ModuleError {
            message: "mod declaration requires a name".to_string(),
            file: None,
            span,
        });
    }

    let name = expect_symbol(&elems[1], "mod declaration name")?;

    let inline_body = if elems.len() > 2 {
        Some(elems[2..].to_vec())
    } else {
        None
    };

    Ok(ModDecl {
        name: ModuleName::from(name),
        is_private,
        inline_body,
        span,
    })
}

// ---------------------------------------------------------------------------
// import parsing
// ---------------------------------------------------------------------------

/// Parse `(import [module-spec names-list ...])`.
///
/// The bracket contents are pairs: `module-spec names-list module-spec names-list ...`
/// where module-spec is a symbol, `super`, or `(module alias)`, and names-list is `[names]`.
fn parse_import(elems: &[Sexp], span: Span) -> Result<Vec<ImportSpec>, CranelispError> {
    if elems.len() != 2 {
        return Err(CranelispError::ModuleError {
            message: "import requires exactly one bracket argument".to_string(),
            file: None,
            span,
        });
    }

    let entries = match &elems[1] {
        Sexp::Bracket(items, _) => items,
        _ => {
            return Err(CranelispError::ModuleError {
                message: "import argument must be a bracket list".to_string(),
                file: None,
                span: elems[1].span(),
            });
        }
    };

    parse_import_entries(entries, span)
}

/// Parse pairs of `module-spec names-list` from bracket contents.
fn parse_import_entries(items: &[Sexp], form_span: Span) -> Result<Vec<ImportSpec>, CranelispError> {
    let mut specs = Vec::new();
    let mut i = 0;

    while i < items.len() {
        let (module_path, alias, mod_span) = parse_module_spec(&items[i])?;

        i += 1;
        if i >= items.len() {
            return Err(CranelispError::ModuleError {
                message: format!("import: missing names list after module '{}'", module_path),
                file: None,
                span: form_span,
            });
        }

        let (names, _names_span) = parse_names_list(&items[i])?;
        let spec_span = mod_span.merge(items[i].span());
        i += 1;

        specs.push(ImportSpec {
            module_path: ModuleFullPath::from(module_path),
            alias: alias.map(ModuleName::from),
            names,
            span: spec_span,
        });
    }

    Ok(specs)
}

/// Parse a module specifier: bare symbol, `super`, or `(module alias)`.
///
/// Returns `(module_path, optional_alias, span)`.
fn parse_module_spec(sexp: &Sexp) -> Result<(String, Option<String>, Span), CranelispError> {
    match sexp {
        Sexp::Symbol(name, span) => Ok((name.clone(), None, *span)),
        Sexp::List(elems, span) => {
            // (module alias) form
            if elems.len() != 2 {
                return Err(CranelispError::ModuleError {
                    message: "aliased module spec must be (module alias)".to_string(),
                    file: None,
                    span: *span,
                });
            }
            let module = expect_symbol(&elems[0], "module path in alias")?;
            let alias = expect_symbol(&elems[1], "alias name")?;
            Ok((module, Some(alias), *span))
        }
        other => Err(CranelispError::ModuleError {
            message: "expected module specifier (symbol or (module alias))".to_string(),
            file: None,
            span: other.span(),
        }),
    }
}

/// Parse a names list: `[name1 name2]`, `[*]`, `[Display.*]`, or `[]`.
///
/// Returns `(ImportNames, span)`.
fn parse_names_list(sexp: &Sexp) -> Result<(ImportNames, Span), CranelispError> {
    match sexp {
        Sexp::Bracket(items, span) => {
            if items.is_empty() {
                return Ok((ImportNames::None, *span));
            }

            // Check for glob: single `*`
            if items.len() == 1
                && let Sexp::Symbol(name, _) = &items[0]
            {
                if name == "*" {
                    return Ok((ImportNames::Glob, *span));
                }
                // Check for member glob: `Display.*`
                if let Some(base) = name.strip_suffix(".*") {
                    return Ok((
                        ImportNames::MemberGlob(base.to_string().into()),
                        *span,
                    ));
                }
            }

            // Specific names
            let mut names = Vec::new();
            for item in items {
                let name = expect_symbol(item, "import name")?;
                // Check for member glob in multi-item list
                if let Some(base) = name.strip_suffix(".*") {
                    return Ok((
                        ImportNames::MemberGlob(base.to_string().into()),
                        *span,
                    ));
                }
                names.push(name.into());
            }
            Ok((ImportNames::Specific(names), *span))
        }
        other => Err(CranelispError::ModuleError {
            message: "expected bracket names list".to_string(),
            file: None,
            span: other.span(),
        }),
    }
}

// ---------------------------------------------------------------------------
// export parsing
// ---------------------------------------------------------------------------

/// Parse `(export [module names-list ...])`.
fn parse_export(elems: &[Sexp], span: Span) -> Result<Vec<ExportSpec>, CranelispError> {
    if elems.len() != 2 {
        return Err(CranelispError::ModuleError {
            message: "export requires exactly one bracket argument".to_string(),
            file: None,
            span,
        });
    }

    let entries = match &elems[1] {
        Sexp::Bracket(items, _) => items,
        _ => {
            return Err(CranelispError::ModuleError {
                message: "export argument must be a bracket list".to_string(),
                file: None,
                span: elems[1].span(),
            });
        }
    };

    parse_export_entries(entries, span)
}

/// Parse pairs of `module names-list` from bracket contents.
fn parse_export_entries(items: &[Sexp], form_span: Span) -> Result<Vec<ExportSpec>, CranelispError> {
    let mut specs = Vec::new();
    let mut i = 0;

    while i < items.len() {
        let module_path = expect_symbol(&items[i], "export module path")?;
        let mod_span = items[i].span();

        i += 1;
        if i >= items.len() {
            return Err(CranelispError::ModuleError {
                message: format!("export: missing names list after module '{}'", module_path),
                file: None,
                span: form_span,
            });
        }

        let (names, _names_span) = parse_names_list(&items[i])?;
        let spec_span = mod_span.merge(items[i].span());
        i += 1;

        specs.push(ExportSpec {
            module_path: ModuleFullPath::from(module_path),
            names,
            span: spec_span,
        });
    }

    Ok(specs)
}

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

/// Extract a string from a Symbol sexp, or return an error.
fn expect_symbol(sexp: &Sexp, context: &str) -> Result<String, CranelispError> {
    match sexp {
        Sexp::Symbol(name, _) => Ok(name.clone()),
        other => Err(CranelispError::ModuleError {
            message: format!("expected symbol for {}, got {:?}", context, other),
            file: None,
            span: other.span(),
        }),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::Sexp;

    /// Helper: parse source text into sexps via the reader.
    fn parse(src: &str) -> Vec<Sexp> {
        crate::reader::parse(src).expect("parse failed")
    }

    fn extract(src: &str) -> (ModuleStructure, Vec<Sexp>) {
        let sexps = parse(src);
        extract_module_declarations(
            ModuleFullPath::from("test"),
            None,
            sexps,
        )
        .expect("extraction failed")
    }

    // -- mod declarations --

    // spec: 08-modules §8.2.1 — public submodule declaration
    #[test]
    fn test_mod_public() {
        let (ms, remaining) = extract("(mod util)");
        assert_eq!(ms.mod_decls.len(), 1);
        assert_eq!(&*ms.mod_decls[0].name, "util");
        assert!(!ms.mod_decls[0].is_private);
        assert!(ms.mod_decls[0].inline_body.is_none());
        assert!(remaining.is_empty());
    }

    // spec: 08-modules §8.2.3 — private submodule declaration
    #[test]
    fn test_mod_private() {
        let (ms, remaining) = extract("(mod- internal)");
        assert_eq!(ms.mod_decls.len(), 1);
        assert_eq!(&*ms.mod_decls[0].name, "internal");
        assert!(ms.mod_decls[0].is_private);
        assert!(ms.mod_decls[0].inline_body.is_none());
        assert!(remaining.is_empty());
    }

    // spec: 08-modules §8.2.2 — inline submodule declaration
    #[test]
    fn test_mod_inline() {
        let (ms, remaining) = extract(
            "(mod test (import [super [*]]) (defn test-add [] (+ 3 4)))",
        );
        assert_eq!(ms.mod_decls.len(), 1);
        assert_eq!(&*ms.mod_decls[0].name, "test");
        assert!(!ms.mod_decls[0].is_private);
        let body = ms.mod_decls[0].inline_body.as_ref().unwrap();
        assert_eq!(body.len(), 2); // import + defn
        assert!(remaining.is_empty());
    }

    // -- import declarations --

    // spec: 08-modules §8.3.1 — specific name import
    #[test]
    fn test_import_specific_names() {
        let (ms, remaining) = extract("(import [core.option [Some None]])");
        assert_eq!(ms.import_specs.len(), 1);
        assert_eq!(&*ms.import_specs[0].module_path, "core.option");
        assert!(ms.import_specs[0].alias.is_none());
        match &ms.import_specs[0].names {
            ImportNames::Specific(names) => {
                assert_eq!(names.len(), 2);
                assert_eq!(&*names[0], "Some");
                assert_eq!(&*names[1], "None");
            }
            other => panic!("expected Specific, got {:?}", other),
        }
        assert!(remaining.is_empty());
    }

    // spec: 08-modules §8.3.2 — glob import
    #[test]
    fn test_import_glob() {
        let (ms, _) = extract("(import [core.math [*]])");
        assert_eq!(ms.import_specs.len(), 1);
        assert_eq!(&*ms.import_specs[0].module_path, "core.math");
        assert_eq!(ms.import_specs[0].names, ImportNames::Glob);
    }

    // spec: 08-modules §8.3.3 — member glob import
    #[test]
    fn test_import_member_glob() {
        let (ms, _) = extract("(import [core.fmt [Display.*]])");
        assert_eq!(ms.import_specs.len(), 1);
        assert_eq!(&*ms.import_specs[0].module_path, "core.fmt");
        match &ms.import_specs[0].names {
            ImportNames::MemberGlob(base) => assert_eq!(&**base, "Display"),
            other => panic!("expected MemberGlob, got {:?}", other),
        }
    }

    // spec: 08-modules §8.3.4 — aliased import
    #[test]
    fn test_import_alias() {
        let (ms, _) = extract("(import [(core.string str) [concat join]])");
        assert_eq!(ms.import_specs.len(), 1);
        assert_eq!(&*ms.import_specs[0].module_path, "core.string");
        assert_eq!(ms.import_specs[0].alias.as_ref().unwrap().as_ref(), "str");
        match &ms.import_specs[0].names {
            ImportNames::Specific(names) => {
                assert_eq!(names.len(), 2);
                assert_eq!(&*names[0], "concat");
                assert_eq!(&*names[1], "join");
            }
            other => panic!("expected Specific, got {:?}", other),
        }
    }

    // spec: 08-modules §8.3.5 — alias-only import (empty names list)
    #[test]
    fn test_import_alias_only() {
        let (ms, _) = extract("(import [(core.option opt) []])");
        assert_eq!(ms.import_specs.len(), 1);
        assert_eq!(&*ms.import_specs[0].module_path, "core.option");
        assert_eq!(ms.import_specs[0].alias.as_ref().unwrap().as_ref(), "opt");
        assert_eq!(ms.import_specs[0].names, ImportNames::None);
    }

    // spec: 08-modules §8.3.6 — super import
    #[test]
    fn test_import_super() {
        let (ms, _) = extract("(import [super [*]])");
        assert_eq!(ms.import_specs.len(), 1);
        assert_eq!(&*ms.import_specs[0].module_path, "super");
        assert_eq!(ms.import_specs[0].names, ImportNames::Glob);
    }

    // spec: 08-modules §8.3.7 — multiple modules in one import form
    #[test]
    fn test_import_multiple_modules() {
        let (ms, _) = extract("(import [core.option [Some None] core.math [*]])");
        assert_eq!(ms.import_specs.len(), 2);
        assert_eq!(&*ms.import_specs[0].module_path, "core.option");
        match &ms.import_specs[0].names {
            ImportNames::Specific(names) => assert_eq!(names.len(), 2),
            other => panic!("expected Specific, got {:?}", other),
        }
        assert_eq!(&*ms.import_specs[1].module_path, "core.math");
        assert_eq!(ms.import_specs[1].names, ImportNames::Glob);
    }

    // -- export declarations --

    // spec: 08-modules §8.4.2 — glob re-export
    #[test]
    fn test_export_glob() {
        let (ms, _) = extract("(export [core [*]])");
        assert_eq!(ms.export_specs.len(), 1);
        assert_eq!(&*ms.export_specs[0].module_path, "core");
        assert_eq!(ms.export_specs[0].names, ImportNames::Glob);
    }

    // spec: 08-modules §8.4.3 — multiple module re-export
    #[test]
    fn test_export_multiple() {
        let (ms, _) = extract("(export [core [*] primitives [vec-len]])");
        assert_eq!(ms.export_specs.len(), 2);
        assert_eq!(&*ms.export_specs[0].module_path, "core");
        assert_eq!(ms.export_specs[0].names, ImportNames::Glob);
        assert_eq!(&*ms.export_specs[1].module_path, "primitives");
        match &ms.export_specs[1].names {
            ImportNames::Specific(names) => {
                assert_eq!(names.len(), 1);
                assert_eq!(&*names[0], "vec-len");
            }
            other => panic!("expected Specific, got {:?}", other),
        }
    }

    // -- passthrough behavior --

    // spec: 08-modules §8.12.1 — non-mod/import/export sexps pass through
    #[test]
    fn test_passthrough() {
        let (ms, remaining) = extract("(defn add [x y] (+ x y))");
        assert!(ms.mod_decls.is_empty());
        assert!(ms.import_specs.is_empty());
        assert!(ms.export_specs.is_empty());
        assert_eq!(remaining.len(), 1);
    }

    // spec: 08-modules §8.2.6, §8.3.8, §8.4.5 — mixed forms partitioned correctly
    #[test]
    fn test_mixed_forms() {
        let src = r#"
            (mod util)
            (import [core.math [*]])
            (export [core [*]])
            (defn main [] 42)
            (mod- internal)
            (defn helper [x] x)
        "#;
        let (ms, remaining) = extract(src);
        assert_eq!(ms.mod_decls.len(), 2);
        assert_eq!(&*ms.mod_decls[0].name, "util");
        assert!(!ms.mod_decls[0].is_private);
        assert_eq!(&*ms.mod_decls[1].name, "internal");
        assert!(ms.mod_decls[1].is_private);
        assert_eq!(ms.import_specs.len(), 1);
        assert_eq!(ms.export_specs.len(), 1);
        assert_eq!(remaining.len(), 2); // two defn forms
    }

    // spec: 08-modules §8.4.1 — specific re-export
    #[test]
    fn test_export_specific() {
        let (ms, _) = extract("(export [core.option [Option Some None]])");
        assert_eq!(ms.export_specs.len(), 1);
        assert_eq!(&*ms.export_specs[0].module_path, "core.option");
        match &ms.export_specs[0].names {
            ImportNames::Specific(names) => {
                assert_eq!(names.len(), 3);
                assert_eq!(&*names[0], "Option");
                assert_eq!(&*names[1], "Some");
                assert_eq!(&*names[2], "None");
            }
            other => panic!("expected Specific, got {:?}", other),
        }
    }

    // spec: 08-modules §8.2 — mod with no name is an error
    #[test]
    fn test_mod_missing_name() {
        let sexps = parse("(mod)");
        let result = extract_module_declarations(
            ModuleFullPath::from("test"),
            None,
            sexps,
        );
        assert!(result.is_err());
    }

    // spec: 08-modules §8.3 — import with missing names list is an error
    #[test]
    fn test_import_missing_names() {
        let sexps = parse("(import [core.option])");
        let result = extract_module_declarations(
            ModuleFullPath::from("test"),
            None,
            sexps,
        );
        assert!(result.is_err());
    }

    // spec: 08-modules §8.1 — file_path and module path are preserved
    #[test]
    fn test_module_path_preserved() {
        let (ms, _) = extract_module_declarations(
            ModuleFullPath::from("app.handler"),
            Some(PathBuf::from("/project/app/handler.cl")),
            vec![],
        )
        .unwrap();
        assert_eq!(&*ms.path, "app.handler");
        assert_eq!(
            ms.file_path.as_ref().unwrap().to_str().unwrap(),
            "/project/app/handler.cl"
        );
    }

    // spec: 08-modules §8.3.8 — multiple import forms accumulate
    #[test]
    fn test_multiple_import_forms() {
        let src = r#"
            (import [core.option [Some None]])
            (import [core.math [*]])
        "#;
        let (ms, _) = extract(src);
        assert_eq!(ms.import_specs.len(), 2);
        assert_eq!(&*ms.import_specs[0].module_path, "core.option");
        assert_eq!(&*ms.import_specs[1].module_path, "core.math");
    }
}
