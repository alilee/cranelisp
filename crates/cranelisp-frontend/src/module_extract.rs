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
//! `containing_module` parameter is mandatory: neither an
//! `ImportSpec.module_path` nor an `ExportSpec.module_path` contains the
//! literal `"super"` past this boundary. All `super`-resolution happens
//! against the parsing module's own path per spec §8.3.8.

use crate::ast_builder::{HeadKind, StructuralKind, classify_head};
use cranelisp_types::{
    CranelispError, ErrorLocation, ExportSpec, ImportEntry, ImportNames, ImportSpec, ModDecl,
    ModuleFullPath, ModuleName, PlatformSpec, Sexp, Span, Visibility,
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
/// Written onto the per-module `SymbolTable` by appending directly to its
/// public structural vectors in source order. There is no bulk-load method;
/// the `SymbolTable` remains the single structural-declaration store, with no
/// parallel `ModuleStructure`.
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
    /// `(export [...])` declarations in source order, parsed by the same
    /// pair parser as imports: `super` is resolved, and a `(path alias)`
    /// specifier's mount alias is in `ExportSpec::alias`.
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
///   resolution at parse time: no `ImportSpec` or `ExportSpec` module path
///   carries the literal `"super"` past the frontend boundary. Per spec
///   §8.3.8, inside `a.b.c` the form `(import [super [...]])` resolves to `a.b`.
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
                            let pairs =
                                parse_pair_form(elems, *span, containing_module, PairForm::Import)?;
                            import_specs.extend(pairs.into_iter().map(|pair| ImportSpec {
                                module_path: pair.module_path,
                                alias: pair.alias,
                                names: pair.names,
                                span: pair.span,
                            }));
                        }
                        StructuralKind::Export => {
                            let pairs =
                                parse_pair_form(elems, *span, containing_module, PairForm::Export)?;
                            export_specs.extend(pairs.into_iter().map(|pair| ExportSpec {
                                module_path: pair.module_path,
                                alias: pair.alias,
                                names: pair.names,
                                span: pair.span,
                            }));
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
fn parse_mod_decl(
    elems: &[Sexp],
    span: Span,
    visibility: Visibility,
) -> Result<ModDecl, CranelispError> {
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
// import and export parsing — one pair parser (design/frontend/modules.md §2.1)
// ---------------------------------------------------------------------------

/// Which declaration a `module-spec names-list` pair belongs to. Import and
/// export are one operation differing only in visibility (spec §8.4.0), so this
/// is the only thing the shared parser is told: it names the form in
/// diagnostics and nothing else.
#[derive(Debug, Clone, Copy)]
enum PairForm {
    Import,
    Export,
}

impl PairForm {
    fn noun(self) -> &'static str {
        match self {
            PairForm::Import => "import",
            PairForm::Export => "export",
        }
    }
}

/// One parsed `module-spec names-list` pair, before it is wrapped in the
/// form's record (`ImportSpec` or `ExportSpec`).
struct DeclPair {
    module_path: ModuleFullPath,
    alias: Option<ModuleName>,
    names: ImportNames,
    span: Span,
}

/// The entry shapes a names list accepts (spec §8.3 `name` and `member_glob`),
/// named by every entry diagnostic.
const ENTRY_SHAPES: &str =
    "a name, a dotted member `Type.member`, a member glob `Type.*`, or a rename `(source local)`";

fn module_err(message: String, span: Span) -> CranelispError {
    CranelispError::ModuleError {
        message,
        location: ErrorLocation::from_span_file(span, None),
    }
}

/// Parse `(import [module-spec names-list ...])` or
/// `(export [module-spec names-list ...])` into its pairs, in source order.
///
/// `containing_module` is the path of the module whose source contains the
/// form; it is required to rewrite `super` to the parent module path (spec
/// §8.3.8), for both forms.
fn parse_pair_form(
    elems: &[Sexp],
    span: Span,
    containing_module: &ModuleFullPath,
    form: PairForm,
) -> Result<Vec<DeclPair>, CranelispError> {
    let noun = form.noun();
    if elems.len() != 2 {
        return Err(module_err(
            format!("{noun} requires exactly one bracket argument"),
            span,
        ));
    }
    let Sexp::Bracket(items, _) = &elems[1] else {
        return Err(module_err(
            format!("{noun} argument must be a bracket list"),
            elems[1].span(),
        ));
    };

    let mut pairs = Vec::new();
    let mut i = 0;
    while i < items.len() {
        let (module_path, alias, mod_span) = parse_module_spec(&items[i], containing_module, form)?;
        i += 1;
        let Some(names_sexp) = items.get(i) else {
            return Err(module_err(
                format!("{noun}: missing names list after module '{module_path}'"),
                span,
            ));
        };
        let names = parse_names_list(names_sexp, form)?;
        i += 1;
        pairs.push(DeclPair {
            module_path,
            alias,
            names,
            span: mod_span.merge(names_sexp.span()),
        });
    }
    Ok(pairs)
}

/// Parse a module specifier: a module path, `super`, or `(path alias)`.
///
/// The path is a reference and may be dotted. `super` is rewritten here to the
/// parent of `containing_module` (spec §8.3.8): inside `a.b.c` it is `a.b`, and
/// in a root module it is a located error. No returned path is the literal
/// `"super"` (BC invariant 3). The alias is a binder (spec §8.3.4, which covers
/// export mount aliases too) and rejects a qualified or dotted spelling.
fn parse_module_spec(
    sexp: &Sexp,
    containing_module: &ModuleFullPath,
    form: PairForm,
) -> Result<(ModuleFullPath, Option<ModuleName>, Span), CranelispError> {
    let noun = form.noun();
    let (written_path, alias, span) = match sexp {
        Sexp::Symbol(name, span) => (name.clone(), None, *span),
        Sexp::List(elems, span) => {
            if elems.len() != 2 {
                return Err(module_err(
                    format!(
                        "{noun}: an aliased module specifier is `(module alias)` — exactly \
                         two symbols, got {}",
                        sexp.format_flat()
                    ),
                    *span,
                ));
            }
            let module = expect_symbol(&elems[0], "module path in alias")?;
            let alias = expect_symbol(&elems[1], "alias name")?;
            crate::ast_builder::reject_qualified_binder_head(&alias, elems[1].span())?;
            (module, Some(ModuleName::from(alias)), *span)
        }
        other => {
            return Err(module_err(
                format!(
                    "{noun}: expected a module specifier (a module path, `super`, or \
                     `(module alias)`), got {}",
                    other.format_flat()
                ),
                other.span(),
            ));
        }
    };

    let module_path = if written_path == "super" {
        match containing_module.as_ref().rsplit_once('.') {
            Some((parent, _)) => parent.to_string(),
            None => {
                return Err(module_err(
                    format!(
                        "'super' {noun} used in top-level module '{}' (no parent)",
                        containing_module.as_ref()
                    ),
                    span,
                ));
            }
        }
    } else {
        written_path
    };
    Ok((ModuleFullPath::from(module_path), alias, span))
}

/// Parse a names list (spec §8.3, §8.3.11; design/frontend/modules.md §2.1).
///
/// The list shape is decided first: `[]` is [`ImportNames::None`], a sole `*`
/// is [`ImportNames::Glob`], and anything else is [`ImportNames::Specific`],
/// with every element classified on its own, in source order. Among other
/// elements `*` is the multiplication operator, an ordinary entry. No returned
/// `Specific` is empty.
fn parse_names_list(sexp: &Sexp, form: PairForm) -> Result<ImportNames, CranelispError> {
    let Sexp::Bracket(items, _) = sexp else {
        return Err(module_err(
            format!(
                "{}: expected bracket names list, got {}",
                form.noun(),
                sexp.format_flat()
            ),
            sexp.span(),
        ));
    };
    match items.as_slice() {
        [] => Ok(ImportNames::None),
        [Sexp::Symbol(only, _)] if only == "*" => Ok(ImportNames::Glob),
        _ => items
            .iter()
            .map(|item| parse_entry(item, form))
            .collect::<Result<_, _>>()
            .map(ImportNames::Specific),
    }
}

/// Classify one element of a specific names list.
///
/// | Element | Entry |
/// |---|---|
/// | `name` | `Name { source: name, local: name }` |
/// | `Type.member` | `Name { source: Type.member, local: member }` |
/// | `(source local)` | `Name { source, local }` |
/// | `Parent.*` | `MemberGlob(Parent)` |
///
/// `local` is derived here and nowhere else (Principle 24): the member of a
/// dotted entry is what follows its last `.`, through the crate's one dotted
/// splitter. Anything else is a located module error at the element.
fn parse_entry(item: &Sexp, form: PairForm) -> Result<ImportEntry, CranelispError> {
    match item {
        Sexp::Symbol(written, span) => {
            if let Some(parent) = written.strip_suffix(".*") {
                return parse_member_glob(parent, written, *span, form);
            }
            reject_qualified_entry_source(written, *span, form)?;
            let local = crate::ast_builder::split_dotted_name(written)
                .map_or(written.as_str(), |(_, member)| member);
            Ok(ImportEntry::Name {
                source: written.as_str().into(),
                local: local.into(),
            })
        }
        Sexp::List(parts, span) => parse_rename(parts, *span, form),
        other => Err(module_err(
            format!(
                "{}: expected a names-list entry ({ENTRY_SHAPES}), got {}",
                form.noun(),
                other.format_flat()
            ),
            other.span(),
        )),
    }
}

/// A member glob's parent is one bare type or trait name of the source module
/// (spec §8.3 `member_glob = symbol '.*'`).
fn parse_member_glob(
    parent: &str,
    written: &str,
    span: Span,
    form: PairForm,
) -> Result<ImportEntry, CranelispError> {
    use crate::ast_builder::{split_dotted_name, split_qualified_name};
    if parent.is_empty()
        || split_qualified_name(parent).is_some()
        || split_dotted_name(parent).is_some()
    {
        return Err(module_err(
            format!(
                "{}: '{written}' is not a member glob — its parent must be one bare type or \
                 trait name of the source module (`Type.*`)",
                form.noun()
            ),
            span,
        ));
    }
    Ok(ImportEntry::MemberGlob(parent.into()))
}

/// The source of an entry names something in the module the pair already
/// names, so it carries no `/` qualifier (spec §8.3 `name` production).
fn reject_qualified_entry_source(
    written: &str,
    span: Span,
    form: PairForm,
) -> Result<(), CranelispError> {
    match crate::ast_builder::split_qualified_name(written) {
        None => Ok(()),
        Some((_, bare)) => Err(module_err(
            format!(
                "{}: '{written}' is a qualified name, but a names-list entry names something in \
                 the module it is paired with — write '{bare}' ({ENTRY_SHAPES})",
                form.noun()
            ),
            span,
        )),
    }
}

/// Parse a renamed entry `(source local)` (spec §8.3.5, §8.4.5).
///
/// The source is a reference, bare or dotted; the local is a binder and goes
/// through the shared binder reject (spec §8.3.4). A self-rename `(Some Some)`
/// is valid and yields `source == local`.
fn parse_rename(parts: &[Sexp], span: Span, form: PairForm) -> Result<ImportEntry, CranelispError> {
    let noun = form.noun();
    let [source_sexp, local_sexp] = parts else {
        return Err(module_err(
            format!(
                "{noun}: a renamed entry is `(source local)` — exactly two symbols, got {} \
                 element(s)",
                parts.len()
            ),
            span,
        ));
    };
    let rename_symbol = |sexp: &Sexp, role: &str| match sexp {
        Sexp::Symbol(name, span) => Ok((name.clone(), *span)),
        other => Err(module_err(
            format!(
                "{noun}: the {role} of a renamed entry `(source local)` must be a symbol, got {}",
                other.format_flat()
            ),
            other.span(),
        )),
    };
    let (source, source_span) = rename_symbol(source_sexp, "source")?;
    let (local, local_span) = rename_symbol(local_sexp, "local name")?;
    if source.ends_with(".*") {
        return Err(module_err(
            format!(
                "{noun}: '{source}' is a member glob and cannot be renamed — a renamed entry's \
                 source is a name or a dotted member"
            ),
            source_span,
        ));
    }
    reject_qualified_entry_source(&source, source_span, form)?;
    crate::ast_builder::reject_qualified_binder_head(&local, local_span)?;
    Ok(ImportEntry::Name {
        source: source.into(),
        local: local.into(),
    })
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
            message: format!(
                "expected symbol for {}, got {}",
                context,
                other.format_flat()
            ),
            location: ErrorLocation::from_span_file(other.span(), None),
        }),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
