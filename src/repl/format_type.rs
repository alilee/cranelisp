//! Per-kind introspection-display producers — the `*_display`/`*_display_doc`
//! family that renders a *named definition* (type, trait, builtin type, special
//! form, macro, overloaded fn) for `/info`/`/sig`/`/doc`/`/type`, plus the
//! `; defn:`/`; impl:`/`; match:` related-section builders they share. The
//! type-level sibling of the value-echo renderers in `repl/format.rs`; consumes
//! the shared resolution toolbox in `repl/mod.rs`. A-split of `repl/format.rs`
//! per `design/int/repl-decomposition.md` §1.6.1 (FIXME 0627); pure relocation,
//! behaviour-invariant.

use super::*;

/// Format an overloaded (multi-sig) function as one line per variant, with
/// fully-qualified `module/name` per spec §4.1.1. Used by bare-symbol display
/// (`format_def_entry`).
///
/// First line carries the `; defn` classification + optional docstring; subsequent
/// variant lines carry only the type and qualified name. See repl/spec.md §1.3
/// + §4.1.1 and design/int/multi-sig-introspection.md.
#[cfg(test)]
pub(crate) fn format_overloaded_variants(
    name: &str,
    module: &ModuleFullPath,
    variants: &[OverloadVariant],
    docstring: Option<&str>,
    module_table: Option<&crate::code::SessionSymbolTable>,
) -> String {
    render(&format_overloaded_variants_doc(
        name,
        module,
        variants,
        docstring,
        module_table,
    ))
}

pub(crate) fn format_overloaded_variants_doc(
    name: &str,
    module: &ModuleFullPath,
    variants: &[OverloadVariant],
    docstring: Option<&str>,
    module_table: Option<&crate::code::SessionSymbolTable>,
) -> StyledDoc {
    let mut doc = StyledDoc::new();
    for (i, v) in variants.iter().enumerate() {
        if i > 0 {
            doc.plain("\n");
        }
        let type_str = variant_type_str(v, module_table);
        push_type_annotation(&mut doc, &type_str);
        doc.plain(" ");
        push_fq_name(&mut doc, module, name);
        if i == 0 {
            doc.plain(" ");
            push_metadata(&mut doc, classification_metadata("defn", docstring));
        }
    }
    doc
}

/// Render ONE multi-sig variant's type string (D1, `traits.md` §7.0.2).
///
/// The bare `OverloadVariant { param_types, ret_type }` cannot encode a trait
/// bound — constraints live only on a `Scheme`. So a genuinely-constrained clause
/// (`([a b] (+ a b))` infers `Num a`) rendered from the bare `Type::Fn` DROPS its
/// constraint (`(Fn [a a] a)` instead of `(Fn [:Num a :Num a] a)`) — a §1.4
/// non-conformance. The fix READS the recorded settled state: follow
/// `v.mangled_name` to the clause's template entry in the module's OWN table and
/// render its `Scheme` (constraints intact) via `format_scheme_type`. This is NOT
/// the forbidden echo-re-derive shape — it re-derives nothing, it reads the
/// constraint typecheck already recorded (arch revision 9 principle preserved,
/// placement corrected to int).
///
/// **Binding arch pin:** a fetch miss with a table present is an invariant breach
/// (the base `Overloaded` entry always co-registers its per-clause template) —
/// `debug_assert!` + the bare-`Type::Fn` render as the RELEASE fallback ONLY.
/// Never silent-strip-as-normal, never re-derive from surface syntax. The
/// no-table path (unit tests without a session) is a distinct benign case that
/// does not assert.
fn variant_type_str(
    v: &OverloadVariant,
    module_table: Option<&crate::code::SessionSymbolTable>,
) -> String {
    if let Some(table) = module_table {
        if let Some(ModuleEntry::Def { scheme, .. }) = table.get(v.mangled_name.as_ref()) {
            return crate::display::format_scheme_type(scheme);
        }
        debug_assert!(
            false,
            "D1 invariant breach: multi-sig variant template `{}` absent from the \
             module table — its constraint-carrying scheme is unreachable \
             (traits.md §7.0.2). Rendering the bare `Type::Fn` as the release \
             fallback (constraint would be silently dropped).",
            v.mangled_name
        );
    }
    // Release fallback (fetch miss) / no session table (unit tests): bare render.
    let fn_ty = Type::Fn(v.param_types.clone(), Box::new(v.ret_type.clone()));
    format_type_qualified(&fn_ty)
}

// =============================================================================
// Display formatting helpers (ported from repl/commands.rs)
// =============================================================================

/// Format a special form for display (spec §4.1.5).
///
/// The `:Type` prefix is rendered from the SpecialForm entry's own `scheme`
/// (the SINGLE SOURCE — registered in `bootstrap::register_special_forms`),
/// retiring the former hardcoded `match name { … }` sig table (FIXME 0338,
/// Principle 7). A scheme whose top type is a `Fn` produces the prefix; any
/// other shape (defensive — should not occur for a registered form) omits it.
pub(crate) fn format_special_form_display(
    name: &str,
    scheme: &Scheme,
    description: &str,
) -> String {
    render(&format_special_form_display_doc(name, scheme, description))
}

pub(crate) fn format_special_form_display_doc(
    name: &str,
    scheme: &Scheme,
    description: &str,
) -> StyledDoc {
    let mut doc = StyledDoc::new();
    if matches!(scheme.ty, Type::Fn(..)) {
        let type_str = format_type_qualified(&scheme.ty);
        push_type_annotation(&mut doc, &type_str);
        doc.plain(" ");
    }
    // A special form's subject is a bare `name` (no module qualifier), R15.
    doc.plain(name);
    doc.plain(" ");
    push_metadata(&mut doc, format!("; special form - {description}"));
    doc
}

/// Format a macro for display (spec §4.1.6).
#[cfg(test)]
pub(crate) fn format_macro_display(
    name: &str,
    clauses: &[MacroClauseInfo],
    docstring: Option<&str>,
    module: &ModuleFullPath,
) -> String {
    render(&format_macro_display_doc(name, clauses, docstring, module))
}

pub(crate) fn format_macro_display_doc(
    name: &str,
    clauses: &[MacroClauseInfo],
    docstring: Option<&str>,
    module: &ModuleFullPath,
) -> StyledDoc {
    let mut doc = StyledDoc::new();
    push_type_annotation(&mut doc, &format!("{module}/{name}"));
    doc.plain(" ");
    push_metadata(
        &mut doc,
        append_docstring_comment("; defmacro".to_string(), docstring),
    );
    for clause in clauses {
        let params = format_macro_clause_params(clause);
        doc.plain("\n");
        push_metadata(&mut doc, format!("; {params} -> Sexp"));
    }
    // repl/spec.md §11.2.2: a multi-clause macro card ends with a clause-count
    // summary line (two leading spaces, no `;`). The single-clause worked
    // example (`/info when`) shows NO count line, so gate on `> 1`. The count
    // is always >= 2 under this gate, so a fixed "clauses" is correct.
    if clauses.len() > 1 {
        doc.plain(format!("\n  {} clauses", clauses.len()));
    }
    doc
}

/// Format macro clause parameters as `[param1 param2 ...]`.
pub(crate) fn format_macro_clause_params(clause: &MacroClauseInfo) -> String {
    let mut parts = Vec::new();
    for param in &clause.params {
        match param {
            MacroParam::Name(name) => parts.push(name.to_string()),
            MacroParam::Bracket { fixed, rest } => {
                let mut inner: Vec<String> = fixed.iter().map(|f| f.to_string()).collect();
                if let Some(r) = rest {
                    inner.push(format!("& {r}"));
                }
                parts.push(format!("[{}]", inner.join(" ")));
            }
        }
    }
    if let Some(rest) = &clause.rest_param {
        parts.push(format!("& {rest}"));
    }
    format!("[{}]", parts.join(" "))
}

/// Format a related symbols section (spec §1.1). The symbol block uses the
/// shared §3.3 layout formatter (repl/spec.md:198 — related lists use the same
/// normative L0–L4 layout as `/list`), rendered as comment rows.
/// The `StyledDoc` for a related-symbol section — the drawer header AND its name
/// bodies are all R6 metadata (§10.3 R6); the `\n` line breaks stay Plain.
pub(crate) fn format_related_section_doc(label: &str, names: &[&str]) -> StyledDoc {
    let owned: Vec<String> = names.iter().map(|n| n.to_string()).collect();
    format_related_section_groups_doc(label, &[owned])
}

/// Related-symbol drawer with caller-defined ordering partitions. Each
/// partition uses the normative symbol layout independently, so a semantic
/// group boundary (the type impl drawer's local-before-imported rule) is not
/// erased by the layout formatter's defensive lexical sort.
fn format_related_section_groups_doc(label: &str, groups: &[Vec<String>]) -> StyledDoc {
    let mut doc = StyledDoc::new();
    doc.plain("\n");
    push_metadata(&mut doc, format!("; {label}:"));
    for group in groups {
        for row in format_symbol_layout(group) {
            doc.plain("\n");
            push_metadata(&mut doc, format!(";  {row}"));
        }
    }
    doc
}

#[cfg(test)]
pub(crate) fn format_trait_related_sections(
    method_names: &[&str],
    impl_type_names: &[&str],
) -> String {
    render(&format_trait_related_sections_doc(
        method_names,
        impl_type_names,
    ))
}

pub(crate) fn format_trait_related_sections_doc(
    method_names: &[&str],
    impl_type_names: &[&str],
) -> StyledDoc {
    let mut doc = StyledDoc::new();
    if !method_names.is_empty() {
        doc.extend(format_related_section_doc("defn", method_names));
    }
    // FIXME 0647: OMIT the `; impl:` drawer when the trait has no implementations,
    // matching the `deftype` `; match:`/`; impl:` omit-when-empty precedent
    // (§4.1.3). This makes the definition ECHO and the bare LOOKUP agree — the
    // former `full_impl_section` gate (0542) that forced an EMPTY drawer on bare
    // lookup is retired. (/repl re-syncs §4.1.3/§4.1.4 as the normative statement.)
    if !impl_type_names.is_empty() {
        doc.extend(format_related_section_doc("impl", impl_type_names));
    }
    doc
}

impl CompilerSession {
    /// Format a user-defined type for display (spec §4.1.3).
    ///
    /// Shows `:module/TypeName ; deftype` with `; match:` and `; impl:` sections.
    #[cfg(test)]
    pub(crate) fn format_type_display(&self, type_name: &str, module: &ModuleFullPath) -> String {
        render(&self.format_type_display_doc(type_name, module))
    }

    /// The `:module/TypeName ; deftype` type-display `StyledDoc` (spec §4.1.3) —
    /// the whole `:module/Type` is one R4 span (no `module/` decomposition inside
    /// a type annotation, §10.3 R4); `; deftype` and the `; match:`/`; impl:`
    /// drawers are R6 metadata.
    pub(crate) fn format_type_display_doc(
        &self,
        type_name: &str,
        module: &ModuleFullPath,
    ) -> StyledDoc {
        let mut result = StyledDoc::new();
        push_type_annotation(&mut result, &format!("{module}/{type_name}"));
        result.plain(" ");
        push_metadata(&mut result, "; deftype");
        let tn = TypeName::from(type_name);
        // FIXME 0192 method 2: `get_type_constructors` deleted; inline the
        // 1-line wrapper over the relocated `lookup_type_def_chain`.
        //
        // D1 (S108): root the constructor chain-lookup at the type's already-
        // RESOLVED HOME `module` (the fn already holds it), NOT
        // `current_module_path()`. At the home the TypeDef is local, so the
        // chain terminates at depth 0 and the implicit-prelude outer-scope hop
        // never arises — a seeded ADT (Option/Result/IO) reached via the
        // prelude glob keeps its `; match:` section (spec §4.1.3), same as a
        // user deftype (which worked only incidentally when scope == home).
        if let Some(info) =
            cranelisp_types::lookup_type_def_chain(&self.shared.symbol_tables, module, &tn)
            && !info.constructors.is_empty()
        {
            // `TypeDefInfo.constructors` is now `Vec<Symbol>` (S70 — the
            // `ConstructorInfo` struct retired; ctor metadata lives on each
            // ctor's `DefKind::Constructor` entry).
            let names: Vec<&str> = info.constructors.iter().map(|c| c.as_ref()).collect();
            result.extend(format_related_section_doc("match", &names));
        }
        // The `; impl:` view is a Decision-45 Pattern-B VIEW question ("which
        // traits does this type implement, as visible from HERE") — scope-rooted
        // by semantics. E8 (S108, resolve-home-enumeration.md §5a): the asking
        // module's view INCLUDES the prelude outer scope when its
        // `prelude_fallback` bit is ON, so the candidate SET is the UNION of the
        // inner-scope run and a prelude-hop run (the ONE `impls_for_type_in_view`
        // wrapper — never two hand-rolled hops, Principle 7).
        let trait_names = self.impls_for_type_in_view(&FQTypeName::new(module.clone(), tn));
        if !trait_names.is_empty() {
            result.extend(format_related_section_groups_doc(
                "impl",
                &[trait_names.local, trait_names.imported],
            ));
        }
        result
    }

    /// Format a trait for display (spec §4.1.4).
    ///
    /// Shows `:home/TraitName ; deftrait` with `; defn:` and `; impl:` sections,
    /// ALL rooted at `home` — the trait's RESOLVED home module produced by the
    /// canonical gate (`lookup_with_prelude_fallback` → `resolve_entry_for_display`,
    /// held by the sole caller `format_def_entry`).
    ///
    /// 0558 (S108, resolve-home-enumeration.md §5, class `wrong-scope-lookup`):
    /// the prior body re-resolved the home from the asking scope
    /// (`resolve_terminal_entry_and_home`, no prelude hop) and rooted both section
    /// lookups at `scope`, so a prelude-globbed trait (reachable at `user` ONLY
    /// via the implicit outer-scope bit, no `Import` edge) dropped its `; defn:`
    /// and left `; impl:` empty. Taking the home from the gate and rooting at it —
    /// where the `TraitDecl` is LOCAL (depth 0) — makes the §4.1.4 unconditional
    /// sections survive the prelude glob. Rooting the impl enumeration at the
    /// trait's home is COMPLETE by construction: Decision 0045 writes every
    /// `impl$Type$Trait` into the trait's defining module, so "implementing types
    /// of trait T" is a home question, not a view question (Principle 17 shape 3).
    #[cfg(test)]
    pub(crate) fn format_trait_display(
        &self,
        trait_name: &str,
        docstring: Option<&str>,
        home: &ModuleFullPath,
    ) -> String {
        render(&self.format_trait_display_doc(trait_name, docstring, home))
    }

    /// The `:home/TraitName ; deftrait` trait-display `StyledDoc` (spec §4.1.4) —
    /// the whole `:home/Trait` is one R4 span; the classification, docstring, and
    /// `; defn:`/`; impl:` drawers are R6 metadata.
    pub(crate) fn format_trait_display_doc(
        &self,
        trait_name: &str,
        docstring: Option<&str>,
        home: &ModuleFullPath,
    ) -> StyledDoc {
        let tn = TraitName::from(trait_name);
        let mut result = StyledDoc::new();
        push_type_annotation(&mut result, &format!("{home}/{trait_name}"));
        result.plain(" ");
        push_metadata(
            &mut result,
            append_docstring_comment("; deftrait".to_string(), docstring),
        );
        // §4.1.4: the `; defn:` (method names) section always surfaces (a trait
        // always has methods). The `; impl:` (implementing types) section is
        // OMITTED when the trait has no implementations (FIXME 0647 — matching the
        // `deftype` `; match:` omit-when-empty precedent; the echo and the lookup
        // now agree). FIXME 0192 method 4: `get_trait_methods` deleted; inline the
        // 1-line wrapper over `lookup_trait_decl_chain` — rooted at the trait's HOME.
        let method_names: Vec<String> =
            cranelisp_types::lookup_trait_decl_chain(&self.shared.symbol_tables, home, &tn)
                .map(|decl| decl.methods.iter().map(|m| m.name.to_string()).collect())
                .unwrap_or_default();
        let fq_trait = FQTraitName::new(home.clone(), tn);
        let impl_type_names: Vec<String> = self
            .impl_pairs_in_trait_home(home)
            .into_iter()
            .filter(|pair| pair.trait_name == fq_trait)
            .map(|pair| pair.impl_type.name.to_string())
            .collect();
        let method_refs: Vec<&str> = method_names.iter().map(String::as_str).collect();
        let impl_refs: Vec<&str> = impl_type_names.iter().map(String::as_str).collect();
        result.extend(format_trait_related_sections_doc(&method_refs, &impl_refs));
        result
    }

    /// Format a builtin type (Int, Bool, Float, String) for display (spec §4.1.3).
    pub(crate) fn format_builtin_type_display(&self, type_name: &str) -> String {
        render(&self.format_builtin_type_display_doc(type_name))
    }

    /// The `:primitives/TypeName ; type` builtin-type `StyledDoc` (spec §4.1.3).
    pub(crate) fn format_builtin_type_display_doc(&self, type_name: &str) -> StyledDoc {
        let tn = TypeName::from(type_name);
        let mut result = StyledDoc::new();
        push_type_annotation(&mut result, &format!("primitives/{type_name}"));
        result.plain(" ");
        push_metadata(&mut result, "; type");
        // E8 (S108, resolve-home-enumeration.md §5a): the same ONE view wrapper
        // that feeds `format_type_display` — the candidate SET is the inner-scope
        // run ∪ the prelude hop (bit-gated), so a bare `Int` under the prelude
        // surfaces its prelude-globbed trait impls (`; impl: Display Eq Num Ord`,
        // §4.1.3). Sharing the wrapper closes the two-formatter sibling gap that
        // recurs when one is fixed and the other is not (the Inc1 D1/D2 lesson).
        let trait_names =
            self.impls_for_type_in_view(&FQTypeName::new(ModuleFullPath::from("primitives"), tn));
        if !trait_names.is_empty() {
            result.extend(format_related_section_groups_doc(
                "impl",
                &[trait_names.local, trait_names.imported],
            ));
        }
        result
    }

    /// The type-side `; impl:` VIEW's candidate-trait enumeration (E8, S108,
    /// resolve-home-enumeration.md §5a). "Which traits does this type implement,
    /// as visible from the current scope" is a Decision-45 Pattern-B VIEW
    /// question — scope-rooted by semantics. But "scope-rooted" governs the
    /// per-candidate ROOTING and the answer's frame, NOT the candidate SET: the
    /// asking module's view INCLUDES the prelude outer scope whenever its
    /// `prelude_fallback` bit is ON (S78 §2 — that is what the bit means), so the
    /// candidate enumeration is the UNION of:
    ///
    /// - the inner-scope run — `get_impls_for_type_chain(tables, scope, tn)`; and
    /// - the prelude-hop run — the SAME reader rooted at `prelude`, when the bit
    ///   is ON and scope ≠ `prelude`, restricted to prelude heads that pass the
    ///   I-1 public-only filter (a PRIVATE prelude trait must NOT leak into a user
    ///   view — the `recognize_macro_head` / `prelude_terminal_visible`
    ///   discipline). Since `cranelisp-types` takes no visibility parameter and
    ///   does not change, the filter is an int-side POST-filter on the head entry.
    ///
    /// Merged by bare `TraitName`, sorted + deduped (name-dedup is safe: a
    /// scope-local trait and a distinct prelude trait sharing a bare name is a
    /// poisoned name upstream per §8.6.5, so the union cannot conflate two live
    /// traits). Per-candidate home-probing is unchanged (Decision 0045 makes the
    /// per-trait answer complete by construction). This is the ONE session wrapper
    /// feeding BOTH `format_type_display` and `format_builtin_type_display`
    /// (Principle 7 — never two hand-rolled hops).
    fn impls_for_type_in_view(&self, target: &FQTypeName) -> VisibleImplTraits {
        let scope = self.current_module_path();
        let mut pairs = self.impl_pairs_for_type_from_root(&scope, target, false);
        let prelude_path = ModuleFullPath::from("prelude");
        if scope != prelude_path {
            let bit_on = self
                .shared
                .prelude_fallback
                .get(&scope)
                .map(|b| *b)
                .unwrap_or(false);
            if bit_on {
                pairs.extend(self.impl_pairs_for_type_from_root(&prelude_path, target, true));
            }
        }
        pairs.sort_by(|left, right| {
            let left_imported = left.trait_name.module != scope;
            let right_imported = right.trait_name.module != scope;
            left_imported
                .cmp(&right_imported)
                .then_with(|| left.trait_name.name.cmp(&right.trait_name.name))
                .then_with(|| left.trait_name.module.cmp(&right.trait_name.module))
        });
        pairs.dedup();
        let mut visible = VisibleImplTraits::default();
        for pair in pairs {
            if pair.trait_name.module == scope {
                visible.local.push(pair.trait_name.name.to_string());
            } else {
                visible.imported.push(pair.trait_name.name.to_string());
            }
        }
        visible
    }

    /// Canonical impl pairs visible through one resolution root.
    ///
    /// `get_impls_for_type_chain` remains the candidate-set authority. This
    /// wrapper retains each candidate's resolved `FQTraitName`, then filters the
    /// canonical pair rows by the queried `FQTypeName`. No rendered/bare name is
    /// used as semantic identity.
    fn impl_pairs_for_type_from_root(
        &self,
        root: &ModuleFullPath,
        target: &FQTypeName,
        public_heads_only: bool,
    ) -> Vec<ImplPair> {
        let candidates = cranelisp_types::get_impls_for_type_chain(
            &self.shared.symbol_tables,
            root,
            &target.name,
        );
        let mut pairs = Vec::new();
        for candidate in candidates {
            let Some((head, home)) = cranelisp_types::resolve_terminal_entry_and_home(
                &self.shared.symbol_tables,
                root,
                candidate.as_ref(),
            ) else {
                continue;
            };
            if !matches!(head, ModuleEntry::TraitDecl { .. })
                || public_heads_only && !head.is_public()
            {
                continue;
            }
            let fq_trait = FQTraitName::new(home.clone(), candidate);
            pairs.extend(
                self.impl_pairs_in_trait_home(&home)
                    .into_iter()
                    .filter(|pair| pair.trait_name == fq_trait && pair.impl_type == *target),
            );
        }
        pairs.sort_by(|left, right| {
            left.trait_name
                .to_string()
                .cmp(&right.trait_name.to_string())
                .then_with(|| left.impl_type.to_string().cmp(&right.impl_type.to_string()))
        });
        pairs.dedup();
        pairs
    }

    /// Enumerate the canonical `(trait, type)` relation stored at one trait
    /// home. Both `/info <Trait>` and `/info <Type>` project this same reader.
    fn impl_pairs_in_trait_home(&self, home: &ModuleFullPath) -> Vec<ImplPair> {
        let mut pairs = Vec::new();
        cranelisp_types::for_each_in_module(&self.shared.symbol_tables, home, |_name, entry| {
            if let ModuleEntry::TraitImpl {
                trait_name,
                impl_type,
                ..
            } = entry
            {
                pairs.push(ImplPair {
                    trait_name: trait_name.clone(),
                    impl_type: impl_type.clone(),
                });
            }
        });
        pairs.sort_by(|left, right| {
            left.trait_name
                .to_string()
                .cmp(&right.trait_name.to_string())
                .then_with(|| left.impl_type.to_string().cmp(&right.impl_type.to_string()))
        });
        pairs.dedup();
        pairs
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ImplPair {
    trait_name: FQTraitName,
    impl_type: FQTypeName,
}

#[derive(Debug, Default)]
struct VisibleImplTraits {
    local: Vec<String>,
    imported: Vec<String>,
}

impl VisibleImplTraits {
    fn is_empty(&self) -> bool {
        self.local.is_empty() && self.imported.is_empty()
    }

    #[cfg(test)]
    fn iter(&self) -> impl Iterator<Item = &str> {
        self.local.iter().chain(&self.imported).map(String::as_str)
    }
}

// ---------------------------------------------------------------------------
// Sprint 58 Wave 4 Step 5d (ii): multi-sig REPL bare-symbol display.
// spec: repl/spec.md §1.3 + §4.1.1 — overloaded fn shows all variant
// signatures, one per line.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod overloaded_display_tests {
    use super::*;

    fn variant(params: Vec<Type>, ret: Type, mangled: &str) -> OverloadVariant {
        OverloadVariant {
            param_types: params,
            ret_type: ret,
            mangled_name: Symbol::from(mangled),
        }
    }

    // spec: repl/spec.md §1.3 + §4.1.1 — multi-sig display emits ≥2 lines.
    #[test]
    fn overloaded_display_emits_one_line_per_variant() {
        let module = ModuleFullPath::from("user");
        let variants = vec![
            variant(vec![Type::Int], Type::Int, "pick$Int"),
            variant(vec![Type::Int, Type::Int], Type::Int, "pick$Int+Int"),
        ];
        let out = format_overloaded_variants("pick", &module, &variants, None, None);
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(
            lines.len(),
            2,
            "two variants must produce two lines, got: {out}"
        );
        // Both lines mention the qualified name.
        for line in &lines {
            assert!(
                line.contains("user/pick"),
                "each variant line must include qualified name, got: {line}"
            );
        }
        // First variant's parameter shape: `[primitives/Int]`.
        assert!(
            lines[0].contains("[primitives/Int]"),
            "first line must show 1-arg signature, got: {}",
            lines[0]
        );
        // Second variant's parameter shape: `[primitives/Int primitives/Int]`.
        assert!(
            lines[1].contains("[primitives/Int primitives/Int]"),
            "second line must show 2-arg signature, got: {}",
            lines[1]
        );
        // Only the first line carries the `; defn` classification.
        assert!(
            lines[0].contains("; defn"),
            "first line must carry `; defn` classification, got: {}",
            lines[0]
        );
        assert!(
            !lines[1].contains("; defn"),
            "second line MUST NOT repeat `; defn` classification, got: {}",
            lines[1]
        );
    }

    // spec: repl/spec.md §4.1.1 — first variant carries the docstring; later
    // variants do not.
    #[test]
    fn overloaded_display_attaches_docstring_to_first_variant_only() {
        let module = ModuleFullPath::from("user");
        let variants = vec![
            variant(vec![Type::Int], Type::Int, "pick$Int"),
            variant(vec![Type::Int, Type::Int], Type::Int, "pick$Int+Int"),
        ];
        let out = format_overloaded_variants(
            "pick",
            &module,
            &variants,
            Some("Pick one or sum two"),
            None,
        );
        let lines: Vec<&str> = out.lines().collect();
        assert!(
            lines[0].contains("Pick one or sum two"),
            "first line must include the docstring, got: {}",
            lines[0]
        );
        assert!(
            !lines[1].contains("Pick one or sum two"),
            "second line MUST NOT repeat the docstring, got: {}",
            lines[1]
        );
    }

    // spec: repl/spec.md §4.1.1 — single-variant degenerate case is correct
    // (one line, no duplication).
    #[test]
    fn overloaded_display_single_variant_emits_one_line() {
        let module = ModuleFullPath::from("user");
        let variants = vec![variant(vec![Type::Int], Type::Int, "id$Int")];
        let out = format_overloaded_variants("id", &module, &variants, None, None);
        assert_eq!(
            out.lines().count(),
            1,
            "single-variant Overloaded must emit one line, got: {out}"
        );
    }

    // D1 (traits.md §7.0.2): a constrained multi-sig clause renders its INFERRED
    // trait bound inline — the renderer follows `mangled_name` to the clause's
    // template entry and reads its `Scheme` (constraints intact), NOT the bare
    // `OverloadVariant` `Type::Fn` (which cannot encode a bound). The load-bearing
    // seam behind the `multi_sig_variant_display_carries_inferred_num_constraint`
    // e2e pin.
    // spec: repl/spec.md §4.1.1 — a multi-sig variant that infers a bound displays it.
    #[test]
    fn overloaded_variant_reads_constrained_template_scheme() {
        use cranelisp_types::{DefKind, FQTraitName, Scheme, TypeId, UserFnState};
        use std::collections::HashMap;
        let module = ModuleFullPath::from("user");
        let mut st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        // The 2-arg clause's template: `Num a => (Fn [a a] a)`, keyed `h$Var`.
        let vid: TypeId = 7;
        let mut constraints: HashMap<TypeId, Vec<FQTraitName>> = HashMap::new();
        constraints.insert(vid, vec![FQTraitName::new(module.clone(), "Num".into())]);
        let scheme = Scheme {
            type_vars: vec![vid],
            constraints,
            ty: Type::Fn(
                vec![Type::Var(vid), Type::Var(vid)],
                Box::new(Type::Var(vid)),
            ),
        };
        st.insert(
            "h$Var".into(),
            ModuleEntry::def(
                scheme,
                DefKind::UserFn {
                    fn_state: UserFnState::Concrete {
                        got_slot: 0,
                        mode_summary: None,
                    },
                },
            )
            .build(),
        );
        let variants = vec![variant(
            vec![Type::Var(vid), Type::Var(vid)],
            Type::Var(vid),
            "h$Var",
        )];
        let out = format_overloaded_variants("h", &module, &variants, None, Some(&st));
        assert!(
            out.contains("(Fn [:user/Num a :user/Num a] a) user/h"),
            "the constrained variant MUST render its inferred `Num` bound inline \
             (read from the template scheme), not the constraint-stripped \
             `(Fn [a a] a)`; got:\n{out}"
        );
    }

    // D1 miss-fallback (binding arch pin): a fetch miss WITH a table present is an
    // invariant breach — `debug_assert!` fires (this test, debug build) and the
    // release fallback is the bare `Type::Fn` render, never a silent strip.
    // spec: traits.md §7.0.2 — the fetch-miss invariant.
    #[test]
    #[should_panic(expected = "D1 invariant breach")]
    fn overloaded_variant_fetch_miss_with_table_trips_debug_assert() {
        let module = ModuleFullPath::from("user");
        // Empty table: the variant's template mangle is absent → breach.
        let st = crate::code::SessionSymbolTable::new_with_params(module.clone());
        let variants = vec![variant(vec![Type::Int], Type::Int, "gone$Int")];
        let _ = format_overloaded_variants("g", &module, &variants, None, Some(&st));
    }
}

// ---------------------------------------------------------------------------
// FIXME 0542 — bare trait lookup always surfaces `; defn:` and `; impl:`
// sections. Unit-tests the extracted always-emit section builder
// (`format_trait_related_sections`) at the exact seam of the fix.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod trait_related_section_tests {
    use super::*;

    // spec: repl/spec.md §4.1.4 — FIXME 0647: an impl-less trait OMITS the empty
    // `; impl:` section on BOTH the bare lookup and the definition echo (the
    // former 0542 always-emit-on-lookup rule is retired), matching the `deftype`
    // `; match:` omit-when-empty precedent. Only the `; defn:` section survives.
    #[test]
    fn trait_sections_omit_empty_impl_header() {
        let out = format_trait_related_sections(&["show"], &[]);
        assert!(
            out.contains("; defn:") && out.contains("show"),
            "the `; defn:` method section MUST list `show`; got:\n{out}",
        );
        assert!(
            !out.contains("; impl:"),
            "an impl-less trait MUST omit the empty `; impl:` section (§4.1.4, \
             FIXME 0647 — deftype omit-when-empty precedent); got:\n{out}",
        );
    }

    // spec: repl/spec.md §4.1.4 — when impls exist the `; impl:` section lists
    // the implementing types and NOTHING else (positive + negative in one).
    #[test]
    fn trait_sections_impl_lists_only_implementing_types() {
        let out = format_trait_related_sections(&["show"], &["Int"]);
        // Isolate the `; impl:` body rows (comment lines after the header).
        let impl_body: Vec<&str> = out
            .lines()
            .skip_while(|l| l.trim() != "; impl:")
            .skip(1)
            .take_while(|l| l.trim_start().starts_with(';'))
            .collect();
        let joined = impl_body.join(" ");
        assert!(
            joined.contains("Int"),
            "the `; impl:` section MUST list `Int`; body={impl_body:?}",
        );
        assert!(
            !joined.contains("Bool"),
            "the `; impl:` section MUST NOT leak an unrelated type `Bool`; \
             body={impl_body:?}",
        );
    }
}

#[cfg(test)]
mod fq_arg_format_type_tests {
    use super::*;

    use crate::repl::test_support::*;

    use cranelisp_types::{ModuleEntry, ModuleFullPath, Span, Symbol, Visibility};

    // spec: repl/spec.md §4.1.2/§1.5 (0570-sibling display-envelope-mirror) — the
    // constructor display authority renders the ONE canonical `user/Color.Red`
    // for BOTH the bare-input `name = "Red"` and the dotted-input `name =
    // "Color.Red"` (the S109 canonical key), never doubling the type segment to
    // `user/Color.Color.Red`. Byte-equality of the two input shapes at the single
    // `format_def_entry` seam guards the convergence (one formatter, no per-input
    // special-case).
    #[test]
    fn constructor_display_bare_and_dotted_input_render_one_canonical_home() {
        let s = session();
        let ctor = install_color_red(&s);
        let user = s.current_module_path();
        let bare = s.format_def_entry(&ctor, "Red", &user);
        let dotted = s.format_def_entry(&ctor, "Color.Red", &user);
        assert_eq!(
            bare, dotted,
            "bare `Red` and dotted `Color.Red` MUST render the identical §4.1.2 \
             constructor line; got bare={bare:?} dotted={dotted:?}"
        );
        assert!(
            dotted.contains("user/Color.Red") && !dotted.contains("Color.Color.Red"),
            "the dotted input MUST render the single canonical `user/Color.Red`, \
             never the doubled `user/Color.Color.Red`; got: {dotted}"
        );
    }
    // D1 (S108): `format_type_display` for a type whose resolved home is NOT
    // the current REPL module surfaces its constructors under `; match:`. The
    // bootstrapped `Option` lives in `primitives`; the current module is
    // `user`. Rooting the constructor chain-lookup at the RESOLVED HOME
    // `module` (the param) — not `current_module_path()` (`user`) — makes the
    // TypeDef local so the chain terminates at depth 0 and the seeded ADT keeps
    // its `; match:` section. spec: repl/spec.md §4.1.3
    #[test]
    fn format_type_display_roots_match_section_at_resolved_home() {
        let s = session();
        let prim = ModuleFullPath::from("primitives");
        // Sanity: the current module is NOT the type's home, so the pre-fix
        // scope-rooted lookup (from `user`) would have missed the ctors.
        assert_ne!(s.current_module_path(), prim);
        let out = s.format_type_display("Option", &prim);
        assert!(
            out.contains(":primitives/Option ; deftype"),
            "primary line must qualify the home; got: {out}"
        );
        assert!(
            out.contains("; match:"),
            "seeded ADT resolved from a non-current home MUST surface `; match:`; got: {out}"
        );
        assert!(
            out.contains("None") && out.contains("Some"),
            "`; match:` MUST list ctors None and Some; got: {out}"
        );
    }
    // 0558 (resolve-home-enumeration.md §5): `format_trait_display` roots its
    // `; defn:`/`; impl:` sections at the RESOLVED HOME passed by the gate — where
    // the `TraitDecl` is local (depth 0) — not the asking scope. A trait `T`
    // defined in `home` (not the current `user` scope) surfaces `:home/T` plus its
    // method and impl sections; the pre-fix scope-rooted lookup mis-homed to
    // `:user/T` and dropped both sections. spec: repl/spec.md §4.1.4
    #[test]
    fn format_trait_display_roots_sections_at_resolved_home() {
        use cranelisp_types::{
            TraitDeclInfo, TraitMethodKind, TraitMethodSig, TraitName, TypeExpr,
        };
        let s = session();
        let home = ModuleFullPath::from("home");
        let mut table = SessionSymbolTable::new_with_params(home.clone());
        table.insert(
            Symbol::from("T"),
            ModuleEntry::TraitDecl {
                info: TraitDeclInfo {
                    name: TraitName::from("T"),
                    type_params: vec![],
                    methods: vec![TraitMethodSig {
                        name: Symbol::from("mm"),
                        docstring: None,
                        params: vec![],
                        kind: TraitMethodKind::Required {
                            ret_type: TypeExpr::SelfType,
                        },
                        span: Span::SYNTHETIC,
                        hkt_param_index: None,
                    }],
                },
                visibility: Visibility::Public,
                docstring: None,
            },
        );
        table.insert(Symbol::from("T.Widget"), impl_entry(&home, "T", "Widget"));
        s.shared.symbol_tables.insert(home.clone(), table);

        // The current scope is `user`, where `T` is NOT reachable — a scope-rooted
        // lookup (the pre-fix bug) would mis-home to `:user/T` + empty sections.
        assert_ne!(s.current_module_path(), home);
        let out = s.format_trait_display("T", None, &home);
        assert!(
            out.contains(":home/T ; deftrait"),
            "primary line MUST qualify the RESOLVED home, not the asking scope; got: {out}"
        );
        assert!(
            !out.contains(":user/T"),
            "must NOT mis-home to the asking scope; got: {out}"
        );
        assert!(
            out.contains("; defn:") && out.contains("mm"),
            "the `; defn:` section MUST list method `mm` (home-rooted); got: {out}"
        );
        assert!(
            out.contains("; impl:") && out.contains("Widget"),
            "the `; impl:` section MUST list `Widget` (home-rooted); got: {out}"
        );
    }
    // E8 (resolve-home-enumeration.md §5a): the type-side `; impl:` VIEW's
    // candidate SET unions the inner-scope run with a PRELUDE-HOP run when the
    // asking scope's `prelude_fallback` bit is ON — so a PUBLIC prelude-globbed
    // trait's impl on the type surfaces. spec: repl/spec.md §4.1.3
    #[test]
    fn impls_for_type_in_view_unions_public_prelude_trait() {
        use cranelisp_types::TypeName;
        let s = session();
        let prelude = ModuleFullPath::from("prelude");
        let scope = s.current_module_path();
        let mut ptbl = SessionSymbolTable::new_with_params(prelude.clone());
        ptbl.insert(
            Symbol::from("Disp"),
            trait_decl_entry("Disp", Visibility::Public),
        );
        ptbl.insert(
            Symbol::from("Disp.Int"),
            impl_entry(&prelude, "Disp", "Int"),
        );
        s.shared.symbol_tables.insert(prelude.clone(), ptbl);
        s.shared.prelude_fallback.insert(scope, true);

        let traits = s.impls_for_type_in_view(&FQTypeName::new(prelude, TypeName::from("Int")));
        assert!(
            traits.iter().any(|t| t == "Disp"),
            "the type-side `; impl:` view MUST include the prelude-globbed trait via \
             the prelude hop; got: {traits:?}"
        );
    }
    // E8 negative: a SUPPRESSED prelude (the `prelude_fallback` bit OFF, e.g.
    // `(import [prelude []])`) yields NO prelude-trait rows in the view.
    // spec: repl/spec.md §4.1.3
    #[test]
    fn impls_for_type_in_view_suppressed_prelude_shows_no_prelude_rows() {
        use cranelisp_types::TypeName;
        let s = session();
        let prelude = ModuleFullPath::from("prelude");
        let mut ptbl = SessionSymbolTable::new_with_params(prelude.clone());
        ptbl.insert(
            Symbol::from("Disp"),
            trait_decl_entry("Disp", Visibility::Public),
        );
        ptbl.insert(
            Symbol::from("Disp.Int"),
            impl_entry(&prelude, "Disp", "Int"),
        );
        s.shared.symbol_tables.insert(prelude.clone(), ptbl);
        // Bit deliberately NOT set (absence-is-OFF) — the suppressed-prelude case.

        let traits = s.impls_for_type_in_view(&FQTypeName::new(prelude, TypeName::from("Int")));
        assert!(
            !traits.iter().any(|t| t == "Disp"),
            "with the prelude bit OFF, NO prelude-trait rows appear; got: {traits:?}"
        );
    }
    // E8 negative: a PRIVATE prelude trait (`deftrait-`) MUST NOT leak into a
    // user's type-side view — the I-1 public-head post-filter drops it.
    // spec: repl/spec.md §4.1.3
    #[test]
    fn impls_for_type_in_view_drops_private_prelude_trait() {
        use cranelisp_types::TypeName;
        let s = session();
        let prelude = ModuleFullPath::from("prelude");
        let scope = s.current_module_path();
        let mut ptbl = SessionSymbolTable::new_with_params(prelude.clone());
        ptbl.insert(
            Symbol::from("Secret"),
            trait_decl_entry("Secret", Visibility::Private),
        );
        ptbl.insert(
            Symbol::from("Secret.Int"),
            impl_entry(&prelude, "Secret", "Int"),
        );
        s.shared.symbol_tables.insert(prelude.clone(), ptbl);
        s.shared.prelude_fallback.insert(scope, true);

        let traits = s.impls_for_type_in_view(&FQTypeName::new(prelude, TypeName::from("Int")));
        assert!(
            !traits.iter().any(|t| t == "Secret"),
            "a PRIVATE prelude trait MUST NOT leak into a user's `; impl:` view; got: {traits:?}"
        );
    }
    // E8 positive (scope-local): a trait + impl in the CURRENT scope surfaces via
    // the inner-scope run alone (no prelude hop needed) — the union preserves the
    // Pattern-B inner-scope answer. spec: repl/spec.md §4.1.3
    #[test]
    fn impls_for_type_in_view_includes_scope_local_trait() {
        use cranelisp_types::TypeName;
        let s = session();
        let scope = s.current_module_path();
        if let Some(mut tbl) = s.shared.symbol_tables.get_mut(&scope) {
            tbl.insert(
                Symbol::from("Loc"),
                trait_decl_entry("Loc", Visibility::Public),
            );
            tbl.insert(
                Symbol::from("Loc.Gadget"),
                impl_entry(&scope, "Loc", "Gadget"),
            );
        } else {
            let mut tbl = SessionSymbolTable::new_with_params(scope.clone());
            tbl.insert(
                Symbol::from("Loc"),
                trait_decl_entry("Loc", Visibility::Public),
            );
            tbl.insert(
                Symbol::from("Loc.Gadget"),
                impl_entry(&scope, "Loc", "Gadget"),
            );
            s.shared.symbol_tables.insert(scope.clone(), tbl);
        }

        let traits = s.impls_for_type_in_view(&FQTypeName::new(scope, TypeName::from("Gadget")));
        assert!(
            traits.iter().any(|t| t == "Loc"),
            "a scope-local trait's impl MUST surface via the inner-scope run; got: {traits:?}"
        );
    }

    // The inverse reader compares the complete FQ type identity, not only its
    // bare `TypeName`. A foreign `Gadget` impl must not appear in the drawer for
    // the distinct `user/Gadget`.
    #[test]
    fn impls_for_type_in_view_rejects_same_bare_type_from_other_module() {
        let s = session();
        let scope = s.current_module_path();
        let foreign = ModuleFullPath::from("foreign");
        let mut foreign_table = SessionSymbolTable::new_with_params(foreign.clone());
        foreign_table.insert(
            Symbol::from("ForeignTrait"),
            trait_decl_entry("ForeignTrait", Visibility::Public),
        );
        foreign_table.insert(
            Symbol::from("ForeignTrait.Gadget"),
            impl_entry(&foreign, "ForeignTrait", "Gadget"),
        );
        s.shared
            .symbol_tables
            .insert(foreign.clone(), foreign_table);
        s.shared
            .symbol_tables
            .get_mut(&scope)
            .expect("session scope exists")
            .insert(
                Symbol::from("ForeignTrait"),
                ModuleEntry::Import {
                    source: FQSymbol {
                        module: foreign,
                        symbol: Symbol::from("ForeignTrait"),
                    },
                    visibility: Visibility::Private,
                },
            );

        let traits = s.impls_for_type_in_view(&FQTypeName::new(scope, TypeName::from("Gadget")));
        assert!(
            traits.is_empty(),
            "an impl for foreign/Gadget must not match user/Gadget; got: {traits:?}"
        );
    }

    #[test]
    fn related_impl_groups_keep_local_names_before_imported_names() {
        let doc = format_related_section_groups_doc(
            "impl",
            &[
                vec!["ZuluLocal".to_string()],
                vec!["AlphaImported".to_string()],
            ],
        );
        let rendered = render(&doc);
        let local = rendered.find("ZuluLocal").expect("local row is present");
        let imported = rendered
            .find("AlphaImported")
            .expect("imported row is present");
        assert!(
            local < imported,
            "semantic local/imported partitions must survive lexical layout; got: {rendered}"
        );
    }

    // E8 negative (§4.1.3 empty-omitted unchanged): with no impls reachable, the
    // type display omits the `; impl:` section entirely (the type rule, unlike a
    // trait's unconditional sections). spec: repl/spec.md §4.1.3
    #[test]
    fn builtin_type_display_omits_empty_impl_section() {
        let s = session();
        // No prelude bit, no trait impls → the view is empty → no `; impl:`.
        let out = s.format_builtin_type_display("Int");
        assert!(
            out.contains(":primitives/Int ; type"),
            "the primary type line is present; got: {out}"
        );
        assert!(
            !out.contains("; impl:"),
            "an empty `; impl:` section MUST be omitted for a type (§4.1.3); got: {out}"
        );
    }
}
