//! Sexp-level module declaration extraction.
//!
//! Walks top-level S-expressions and extracts `mod`, `mod-`, `import`, and `export`
//! forms into `ExtractedDeclarations`, returning remaining sexps for further processing.
//! This runs before macro expansion per spec §8.12.1.

use cranelisp_types::{ErrorLocation, 
    CranelispError, ExportSpec, ImportNames, ImportSpec, ModDecl, ModuleFullPath, ModuleName,
    PlatformSpec, Sexp, Span,
};

/// Extracted module-level declarations from top-level S-expressions.
#[derive(Debug, Clone)]
pub struct ExtractedDeclarations {
    pub path: ModuleFullPath,
    pub mod_decls: Vec<ModDecl>,
    pub import_specs: Vec<ImportSpec>,
    pub export_specs: Vec<ExportSpec>,
    pub platform_specs: Vec<PlatformSpec>,
}

/// Extract module declarations from top-level S-expressions.
///
/// Recognizes `(mod name)`, `(mod- name)`, `(import [...])`, and `(export [...])`.
/// All other sexps pass through unchanged.
///
/// Returns `(ExtractedDeclarations, remaining_sexps)`.
pub fn extract_module_declarations(
    path: ModuleFullPath,
    sexps: Vec<Sexp>,
) -> Result<(ExtractedDeclarations, Vec<Sexp>), CranelispError> {
    let mut mod_decls = Vec::new();
    let mut import_specs = Vec::new();
    let mut export_specs = Vec::new();
    let mut platform_specs = Vec::new();
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
                            let specs = parse_import(elems, *span, &path)?;
                            import_specs.extend(specs);
                            continue;
                        }
                        "export" => {
                            let specs = parse_export(elems, *span)?;
                            export_specs.extend(specs);
                            continue;
                        }
                        "platform" => {
                            let spec = parse_platform(elems, *span)?;
                            platform_specs.push(spec);
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

    let declarations = ExtractedDeclarations {
        path,
        mod_decls,
        import_specs,
        export_specs,
        platform_specs,
    };

    Ok((declarations, remaining))
}

// ---------------------------------------------------------------------------
// mod parsing
// ---------------------------------------------------------------------------

/// Parse `(mod name)`, `(mod name form...)`, `(mod- name)`, or `(mod- name form...)`.
fn parse_mod_decl(elems: &[Sexp], span: Span, is_private: bool) -> Result<ModDecl, CranelispError> {
    if elems.len() < 2 {
        return Err(CranelispError::ModuleError {
            message: "mod declaration requires a name".to_string(),
            location: ErrorLocation::from_span_file(span, None),
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
///
/// `containing_module` is the path of the module whose source contains this
/// import form; it is required to rewrite `super` to the parent module path
/// per spec §8.3.7.
fn parse_import(
    elems: &[Sexp],
    span: Span,
    containing_module: &ModuleFullPath,
) -> Result<Vec<ImportSpec>, CranelispError> {
    if elems.len() != 2 {
        return Err(CranelispError::ModuleError {
            message: "import requires exactly one bracket argument".to_string(),
            location: ErrorLocation::from_span_file(span, None),
        });
    }

    let entries = match &elems[1] {
        Sexp::Bracket(items, _) => items,
        _ => {
            return Err(CranelispError::ModuleError {
                message: "import argument must be a bracket list".to_string(),
                location: ErrorLocation::from_span_file(elems[1].span(), None),
            });
        }
    };

    parse_import_entries(entries, span, containing_module)
}

/// Parse pairs of `module-spec names-list` from bracket contents.
///
/// Rewrites `super` module specifiers to the parent of `containing_module`
/// per spec §8.3.7: inside `a.b.c`, `super` resolves to `a.b`. Using `super`
/// in a root module produces a compile-time error. After this function
/// returns, no `ImportSpec.module_path` contains the literal string `"super"`.
fn parse_import_entries(
    items: &[Sexp],
    form_span: Span,
    containing_module: &ModuleFullPath,
) -> Result<Vec<ImportSpec>, CranelispError> {
    let mut specs = Vec::new();
    let mut i = 0;

    while i < items.len() {
        let (raw_module_path, alias, mod_span) = parse_module_spec(&items[i])?;

        // Rewrite `super` to the parent module path (spec §8.3.7).
        let module_path = if raw_module_path == "super" {
            match containing_module.as_ref().rsplit_once('.') {
                Some((parent, _)) => parent.to_string(),
                None => {
                    return Err(CranelispError::ModuleError {
                        message: format!(
                            "'super' import used in top-level module '{}' (no parent)",
                            containing_module.as_ref()
                        ),
                        location: ErrorLocation::from_span_file(mod_span, None),
                    });
                }
            }
        } else {
            raw_module_path
        };

        i += 1;
        if i >= items.len() {
            return Err(CranelispError::ModuleError {
                message: format!("import: missing names list after module '{}'", module_path),
                location: ErrorLocation::from_span_file(form_span, None),
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
                    location: ErrorLocation::from_span_file(*span, None),
                });
            }
            let module = expect_symbol(&elems[0], "module path in alias")?;
            let alias = expect_symbol(&elems[1], "alias name")?;
            Ok((module, Some(alias), *span))
        }
        other => Err(CranelispError::ModuleError {
            message: "expected module specifier (symbol or (module alias))".to_string(),
            location: ErrorLocation::from_span_file(other.span(), None),
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
            location: ErrorLocation::from_span_file(other.span(), None),
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
            location: ErrorLocation::from_span_file(span, None),
        });
    }

    let entries = match &elems[1] {
        Sexp::Bracket(items, _) => items,
        _ => {
            return Err(CranelispError::ModuleError {
                message: "export argument must be a bracket list".to_string(),
                location: ErrorLocation::from_span_file(elems[1].span(), None),
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
                location: ErrorLocation::from_span_file(form_span, None),
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
// platform parsing
// ---------------------------------------------------------------------------

/// Parse `(platform name)` into a `PlatformSpec`.
fn parse_platform(elems: &[Sexp], span: Span) -> Result<PlatformSpec, CranelispError> {
    if elems.len() != 2 {
        return Err(CranelispError::ModuleError {
            message: "platform declaration requires exactly one name argument".to_string(),
            location: ErrorLocation::from_span_file(span, None),
        });
    }

    let name = expect_symbol(&elems[1], "platform declaration name")?;

    Ok(PlatformSpec { name, span })
}

// ---------------------------------------------------------------------------
// Public sexp-level parsing wrappers (for v4 worker per-form classification)
// ---------------------------------------------------------------------------

/// Parse a single `(import ...)` sexp into import specs.
///
/// The sexp must be a `(import [...])` list form. Used by the v4 worker's
/// `classify_form` to parse imports during per-form processing.
///
/// `containing_module` is the path of the module whose source contains this
/// import form; it is required to rewrite `super` to the parent module path
/// per spec §8.3.7. After this function returns, no
/// `ImportSpec.module_path` contains the literal string `"super"` — the
/// frontend-boundary invariant for `ImportSpec`.
// Facade entry retained per `design/arch/facades/frontend.md` §"Sub-parsers
// for structural forms — internal only" — single-form parser exposed as a
// `pub(crate)` helper for future REPL slash-command routing through
// `extract_module_declarations`. Currently has no in-crate callers; the
// `#[allow(dead_code)]` documents the intentional retention until the
// REPL-side wiring (per facade) is in place.
#[allow(dead_code)]
pub(crate) fn parse_import_sexp(
    sexp: &Sexp,
    containing_module: &ModuleFullPath,
) -> Result<Vec<ImportSpec>, CranelispError> {
    match sexp {
        Sexp::List(elems, span) if !elems.is_empty() => {
            parse_import(elems, *span, containing_module)
        }
        _ => Err(CranelispError::ModuleError {
            message: "expected (import [...]) form".to_string(),
            location: ErrorLocation::from_span_file(sexp.span(), None),
        }),
    }
}

/// Parse a single `(export ...)` sexp into export specs.
#[allow(dead_code)] // Facade entry — see `parse_import_sexp` doc comment.
pub(crate) fn parse_export_sexp(sexp: &Sexp) -> Result<Vec<ExportSpec>, CranelispError> {
    match sexp {
        Sexp::List(elems, span) if !elems.is_empty() => {
            parse_export(elems, *span)
        }
        _ => Err(CranelispError::ModuleError {
            message: "expected (export [...]) form".to_string(),
            location: ErrorLocation::from_span_file(sexp.span(), None),
        }),
    }
}

/// Parse a single `(mod ...)` or `(mod- ...)` sexp into a `ModDecl`.
#[allow(dead_code)] // Facade entry — see `parse_import_sexp` doc comment.
pub(crate) fn parse_mod_sexp(sexp: &Sexp) -> Result<ModDecl, CranelispError> {
    match sexp {
        Sexp::List(elems, span) if !elems.is_empty() => {
            if let Sexp::Symbol(head, _) = &elems[0] {
                let is_private = head == "mod-";
                parse_mod_decl(elems, *span, is_private)
            } else {
                Err(CranelispError::ModuleError {
                    message: "expected (mod ...) or (mod- ...) form".to_string(),
                    location: ErrorLocation::from_span_file(*span, None),
                })
            }
        }
        _ => Err(CranelispError::ModuleError {
            message: "expected (mod ...) or (mod- ...) form".to_string(),
            location: ErrorLocation::from_span_file(sexp.span(), None),
        }),
    }
}

/// Parse a single `(platform ...)` sexp into a `PlatformSpec`.
#[allow(dead_code)] // Facade entry — see `parse_import_sexp` doc comment.
pub(crate) fn parse_platform_sexp(sexp: &Sexp) -> Result<PlatformSpec, CranelispError> {
    match sexp {
        Sexp::List(elems, span) if !elems.is_empty() => {
            parse_platform(elems, *span)
        }
        _ => Err(CranelispError::ModuleError {
            message: "expected (platform ...) form".to_string(),
            location: ErrorLocation::from_span_file(sexp.span(), None),
        }),
    }
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
            location: ErrorLocation::from_span_file(other.span(), None),
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

    fn extract(src: &str) -> (ExtractedDeclarations, Vec<Sexp>) {
        let sexps = parse(src);
        extract_module_declarations(
            ModuleFullPath::from("test"),
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

    // spec: 08-modules §8.3.7 — super import rewritten to parent module path
    //
    // Per the super-import arbitration (design/arch/super-import-arbitration.md),
    // `super` is rewritten at frontend capture time. After extraction,
    // `ImportSpec.module_path` never contains the literal string `"super"`.
    #[test]
    fn test_import_super_rewrites_to_parent() {
        let sexps = parse("(import [super [*]])");
        let (ms, _) = extract_module_declarations(
            ModuleFullPath::from("math.test"),
            sexps,
        )
        .expect("extraction failed");
        assert_eq!(ms.import_specs.len(), 1);
        // `super` inside `math.test` resolves to `math`.
        assert_eq!(&*ms.import_specs[0].module_path, "math");
        assert_eq!(ms.import_specs[0].names, ImportNames::Glob);
    }

    // spec: 08-modules §8.3.7 — nested super rewrite (a.b.c → a.b)
    #[test]
    fn test_import_super_rewrites_nested_parent() {
        let sexps = parse("(import [super [helper]])");
        let (ms, _) = extract_module_declarations(
            ModuleFullPath::from("app.handler.test"),
            sexps,
        )
        .expect("extraction failed");
        assert_eq!(ms.import_specs.len(), 1);
        assert_eq!(&*ms.import_specs[0].module_path, "app.handler");
    }

    // spec: 08-modules §8.3.7 — super at a top-level module is a compile-time error
    #[test]
    fn test_import_super_at_root_errors() {
        let sexps = parse("(import [super [*]])");
        let result = extract_module_declarations(
            ModuleFullPath::from("root"),
            sexps,
        );
        let err = result.expect_err("expected error for super at root module");
        match err {
            CranelispError::ModuleError { message, .. } => {
                assert!(
                    message.contains("super"),
                    "error message should mention super, got: {}",
                    message,
                );
                assert!(
                    message.contains("root"),
                    "error message should name the offending module, got: {}",
                    message,
                );
                assert!(
                    message.contains("no parent") || message.contains("top-level"),
                    "error message should explain the no-parent condition, got: {}",
                    message,
                );
            }
            other => panic!("expected ModuleError, got {:?}", other),
        }
    }

    // spec: 08-modules §8.3.8 — multiple modules in one import form
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
            sexps,
        );
        assert!(result.is_err());
    }

    // spec: 08-modules §8.1 — module path is preserved
    #[test]
    fn test_module_path_preserved() {
        let (ms, _) = extract_module_declarations(
            ModuleFullPath::from("app.handler"),
            vec![],
        )
        .unwrap();
        assert_eq!(&*ms.path, "app.handler");
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

    // -- platform declarations --

    // spec: 10-io §10.9.1 — platform declaration extracted from top-level forms
    #[test]
    fn test_platform_extracted() {
        let (ms, remaining) = extract("(platform stdio)");
        assert_eq!(ms.platform_specs.len(), 1);
        assert_eq!(ms.platform_specs[0].name, "stdio");
        assert!(remaining.is_empty());
    }

    // spec: 10-io §10.9.1 — multiple platform declarations accumulate
    #[test]
    fn test_multiple_platforms() {
        let src = r#"
            (platform stdio)
            (platform network)
            (defn main [] 42)
        "#;
        let (ms, remaining) = extract(src);
        assert_eq!(ms.platform_specs.len(), 2);
        assert_eq!(ms.platform_specs[0].name, "stdio");
        assert_eq!(ms.platform_specs[1].name, "network");
        assert_eq!(remaining.len(), 1); // defn passes through
    }

    // spec: 10-io §10.9.1 — platform with wrong arity is an error
    #[test]
    fn test_platform_wrong_arity() {
        let sexps = parse("(platform)");
        let result = extract_module_declarations(
            ModuleFullPath::from("test"),
            sexps,
        );
        assert!(result.is_err());
    }

    // spec: 10-io §10.9.1 — platform forms don't appear in remaining sexps
    #[test]
    fn test_platform_not_in_remaining() {
        let src = "(platform stdio) (defn main [] 42)";
        let (ms, remaining) = extract(src);
        assert_eq!(ms.platform_specs.len(), 1);
        assert_eq!(remaining.len(), 1);
        // Verify the remaining form is the defn, not the platform
        if let Sexp::List(elems, _) = &remaining[0] {
            if let Sexp::Symbol(head, _) = &elems[0] {
                assert_eq!(head.as_str(), "defn");
            } else {
                panic!("expected defn symbol");
            }
        } else {
            panic!("expected list form");
        }
    }
}
