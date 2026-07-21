//! Sexp-level module declaration extraction.
//!
//! Walks top-level S-expressions and extracts `mod`, `mod-`, `import`,
//! `export`, and `platform` forms into [`ExtractedDeclarations`],
//! returning remaining sexps for further processing. This runs before
//! macro expansion per spec §8.12.1.
//!
//! [`extract_module_declarations`] is one of the four free-function
//! entries of the frontend boundary (see crate-root preamble §"Public
//! surface — the form-by-form boundary"). It is the post-parse pass:
//! `parse` produces a flat `Vec<Sexp>`; this function peels off the
//! structural declarations, leaving the residual non-structural forms
//! for the per-form `build_form` / `build_expr` calls. The two-call
//! shape lets `parse` stay reusable for non-orchestration consumers
//! (REPL slash commands, comment-preserving variants) without forcing
//! them to construct a structural-decl store they'll never use.
//!
//! Per BC invariant #3 (`super` resolved at frontend), the
//! `containing_module` parameter is mandatory:
//! `ImportSpec.module_path` NEVER contains the literal `"super"` past
//! this boundary. All `super`-resolution happens against the parsing
//! module's own path per spec §8.3.7.

use crate::ast_builder::{HeadKind, StructuralKind, classify_head};
use cranelisp_types::{ErrorLocation,
    CranelispError, ExportSpec, ImportNames, ImportSpec, ModDecl, ModuleFullPath, ModuleName,
    PlatformSpec, Sexp, Span, Visibility,
};

/// Extracted module-level declarations from top-level S-expressions.
///
/// Returned by [`extract_module_declarations`]. Structural sugar over
/// `cranelisp-types` items — every field is a `cranelisp-types` newtype
/// or spec record. Identity is "the bundle returned by
/// `extract_module_declarations`" rather than a domain concept.
///
/// Per the crate-root preamble §"Re-export policy", this struct is the
/// frontend's one public DTO (post-S76 W-Macro: `ExpansionError` retired
/// with the `expand` skeleton). It lives at
/// `cranelisp_frontend::module_extract::ExtractedDeclarations` (this
/// module-qualified path is the home-module canonical) and is also
/// re-exported at the crate root as `cranelisp_frontend::ExtractedDeclarations`
/// for caller ergonomics — the integration-layer cluster orchestrator
/// imports it from the root. Single-import readability is the
/// Principle 15 narrowness argument.
///
/// Fed directly into `SymbolTable::write_structural_decls` per Decision 33
/// — single source of truth for structural decls on `SymbolTable`, no
/// parallel `ModuleStructure` store.
///
/// `#[non_exhaustive]` so adding new declaration categories is
/// non-breaking.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct ExtractedDeclarations {
    /// The containing module's full path. Preserved on return so the
    /// orchestrator can address per-form work to the right module
    /// without re-deriving it from the source's filesystem location.
    pub path: ModuleFullPath,
    /// `(mod name)` / `(mod- name)` declarations in source order.
    /// Visibility is recorded per-entry (the `mod-` head produces
    /// `Visibility::Private`).
    pub mod_decls: Vec<ModDecl>,
    /// `(import [...])` declarations in source order. Per BC invariant
    /// #3 (`super` resolved at frontend), no `ImportSpec.module_path`
    /// contains the literal `"super"` past this boundary.
    pub import_specs: Vec<ImportSpec>,
    /// `(export [...])` declarations in source order.
    pub export_specs: Vec<ExportSpec>,
    /// `(platform name)` declarations in source order.
    pub platform_specs: Vec<PlatformSpec>,
}

/// Extract module declarations from top-level S-expressions.
///
/// Recognizes `(mod name)`, `(mod- name)`, `(import [...])`,
/// `(export [...])`, and `(platform name)`. All other sexps pass through
/// unchanged into `remaining_sexps`.
///
/// One of the four free-function entries of the frontend boundary (see
/// crate-root preamble). Invoked once per source-file's worth of
/// parsed forms; the residual non-structural forms feed per-form
/// `build_form` / `build_expr` calls downstream.
///
/// # Parameters
///
/// - `containing_module` — the path of the module whose source provides
///   `sexps`. **Required** because BC invariant #3 mandates `super`
///   resolution at parse time: `ImportSpec.module_path` MUST never carry
///   the literal `"super"` past the frontend boundary. Per spec §8.3.7,
///   inside `a.b.c` the form `(import [super [...]])` resolves to `a.b`.
///   The path is needed to do that rewrite. It is also preserved on the
///   returned `ExtractedDeclarations.path`.
/// - `sexps` — the parsed source forms in source order.
///
/// # Returns
///
/// `(ExtractedDeclarations, remaining_sexps)`. The remaining sexps
/// preserve source order; structural-decl forms have been peeled off.
pub fn extract_module_declarations(
    containing_module: &ModuleFullPath,
    sexps: &[Sexp],
) -> Result<(ExtractedDeclarations, Vec<Sexp>), CranelispError> {
    let mut mod_decls = Vec::new();
    let mut import_specs = Vec::new();
    let mut export_specs = Vec::new();
    let mut platform_specs = Vec::new();
    let mut remaining = Vec::new();

    for sexp in sexps {
        match sexp {
            Sexp::List(elems, span) if !elems.is_empty() => {
                // Peel dispatch consumes the ONE head classifier's structural
                // payload (FIXME 0678/0703 (3)) rather than re-listing
                // `"mod" | "mod-" | "import" | "export" | "platform"` — a head
                // added to `classify_head` alone would otherwise be rejected by
                // `build_form` as "must be peeled" while never being peeled here.
                if let Sexp::Symbol(head, _) = &elems[0]
                    && let HeadKind::StructuralDecl(kind) = classify_head(head)
                {
                    match kind {
                        StructuralKind::Mod(visibility) => {
                            let decl = parse_mod_decl(elems, *span, visibility)?;
                            mod_decls.push(decl);
                        }
                        StructuralKind::Import => {
                            let specs = parse_import(elems, *span, containing_module)?;
                            import_specs.extend(specs);
                        }
                        StructuralKind::Export => {
                            let specs = parse_export(elems, *span)?;
                            export_specs.extend(specs);
                        }
                        StructuralKind::Platform => {
                            let spec = parse_platform(elems, *span)?;
                            platform_specs.push(spec);
                        }
                    }
                    continue;
                }
                remaining.push(sexp.clone());
            }
            _ => remaining.push(sexp.clone()),
        }
    }

    let declarations = ExtractedDeclarations {
        path: containing_module.clone(),
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
fn parse_mod_decl(elems: &[Sexp], span: Span, visibility: Visibility) -> Result<ModDecl, CranelispError> {
    if elems.len() < 2 {
        return Err(CranelispError::ModuleError {
            message: "mod declaration requires a name".to_string(),
            location: ErrorLocation::from_span_file(span, None),
        });
    }

    let name = expect_symbol(&elems[1], "mod declaration name")?;

    // spec §5.8: the module name MUST be a simple symbol — "not qualified, not
    // dotted". A `/` (module qualifier) or `.` (dotted path) in a `mod`/`mod-`
    // head is a compile-time error. Same binder-head diagnostic family as
    // `reject_qualified_binder_head`, but `mod` is a MODULE-PHASE decl (not a §5
    // declaration head), so it enforces its own simple-symbol rule at this seam
    // and rejects `.` as well as `/` (design/frontend/binder-head-reject.md §8).
    // Covers both `mod` and `mod-` (single shared parser).
    if name.contains('/') || name.contains('.') {
        return Err(CranelispError::ModuleError {
            message: format!(
                "'{name}' is not a valid module name — a `mod`/`mod-` head must be a \
                 simple symbol, not qualified (`/`) or dotted (`.`) (spec §5.8)"
            ),
            location: ErrorLocation::from_span_file(elems[1].span(), None),
        });
    }

    let inline_body = if elems.len() > 2 {
        Some(elems[2..].to_vec())
    } else {
        None
    };

    Ok(ModDecl {
        name: ModuleName::from(name),
        visibility,
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
            // The module path (elems[0]) is a REFERENCE — a qualified/dotted path
            // is permitted. The alias (elems[1]) is a LOCAL binder (spec §5
            // binder-positions table, §8.3.4) — a qualified spelling rejects,
            // same diagnostic family as the other local binders.
            crate::ast_builder::reject_qualified_binder_head(&alias, elems[1].span())?;
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

    // The platform name composes the `platform.<name>` module path, so a
    // qualified (`/`) or dotted (`.`) name would corrupt that composition — it
    // MUST be a simple symbol. Same simple-symbol guard as the `mod`/`mod-` head
    // (spec §5.8 model; §5.10 needs the "not qualified, not dotted" wording,
    // tracked in FIXME 0660 / /spec rider). Same diagnostic family.
    if name.contains('/') || name.contains('.') {
        return Err(CranelispError::ModuleError {
            message: format!(
                "'{name}' is not a valid platform name — a `platform` head must be a \
                 simple symbol, not qualified (`/`) or dotted (`.`) (spec §5.10)"
            ),
            location: ErrorLocation::from_span_file(elems[1].span(), None),
        });
    }

    Ok(PlatformSpec { name, span })
}

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

/// Extract a string from a Symbol sexp, or return an error.
fn expect_symbol(sexp: &Sexp, context: &str) -> Result<String, CranelispError> {
    match sexp {
        Sexp::Symbol(name, _) => Ok(name.clone()),
        other => Err(CranelispError::ModuleError {
            // Render the offending form via its canonical single-line source
            // form (`Sexp::format_flat`) — NOT `{:?}`, which would leak a Debug
            // `Sexp`/`Span { .. }` struct dump into user-facing text (the P6
            // diagnostic-quality class the 0500 rendered-diagnostic tier guards).
            message: format!("expected symbol for {}, got {}", context, other.format_flat()),
            location: ErrorLocation::from_span_file(other.span(), None),
        }),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
