//! Cross-module macro hygiene: the qualify walk over one macro's expansion
//! (`design/int/expansion-qualification-scope.md`). It shares the expander's
//! binder model (`super::is_binding_form`/`params_scope`/`pattern_binders`/
//! `is_annotation_symbol`) and quote classifier, so the two walks agree.

use std::collections::HashSet;

use cranelisp_types::{ModuleFullPath, Sexp, Span, Symbol};

/// Qualify bare symbols in macro-expanded sexp with their defining module paths.
///
/// After macro expansion, bare symbol references like `make-seven` may refer to
/// symbols in the macro's defining module. These must be qualified (e.g.,
/// `helper/make-seven`) so the consuming module's typechecker can resolve them.
///
/// **Scope-aware (FIXME 0670).** Qualification is a **resolution-product**
/// operation — only a **free reference** carries resolved identity. A **binder**
/// (defn/fn param, `let` name, `match` var-pattern) INTRODUCES a name and is
/// never qualified; a **local read** of a bound name refers to that binder, not
/// a defining-module symbol, and is also held verbatim (`/arch` path-1 ruling,
/// Principle 24 corollary; `expansion-qualification-scope.md`). This walk is the
/// P7 mirror of the expander's own `expand_scoped` binder handling — the two
/// share ONE binder-slot enumeration (`expander::is_binding_form`/`params_scope`/
/// `pattern_binders`/`is_annotation_symbol`), never a second copy.
///
/// A symbol is qualified iff it is a FREE reference — not lexically bound — AND:
/// - bare (no `/` already) and not a type annotation (`:` prefix) / `_`,
/// - found in the defining module's symbol table,
/// - NOT already available in the current module.
///
/// One expansion is qualified against the one module that defines its macro,
/// as it returns (`design/int/s125-binary-clean.md` §5.2). `shadows` is the
/// lexical scope at the call site, so a name the caller binds there and passes
/// as an argument stays bare.
pub(crate) fn qualify_expansion(
    scope: QualifyScope<'_>,
    sexp: Sexp,
    shadows: &HashSet<String>,
) -> Sexp {
    qualify_scoped(&scope, sexp, shadows)
}

/// What one expansion is qualified against, threaded through the walk.
pub(crate) struct QualifyScope<'a> {
    pub(crate) symbol_tables: &'a dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
    pub(crate) current_module: &'a ModuleFullPath,
    pub(crate) defining_module: &'a ModuleFullPath,
    /// The spans of the output symbols that are the caller's own text, held
    /// verbatim (`design/int/expansion-qualification-scope.md` §2.7).
    pub(crate) caller_text: &'a HashSet<Span>,
}

/// Scope-aware qualify core. `shadows` is the set of names lexically bound by an
/// enclosing binding form (`expand_scoped`'s `shadows`, one-to-one).
fn qualify_scoped(ctx: &QualifyScope, sexp: Sexp, shadows: &HashSet<String>) -> Sexp {
    match sexp {
        Sexp::Symbol(ref name, span) => {
            // The caller's own text resolves in the caller's scope (§2.7), and
            // a lexically-bound name — a binder or a local read of one — is
            // never a free reference (FIXME 0670); both are held verbatim.
            if ctx.caller_text.contains(&span) || shadows.contains(name.as_str()) {
                return sexp;
            }
            qualify_free_symbol(ctx, sexp)
        }
        Sexp::List(children, span) => {
            // 0. SHIELD (reader-quote family) — S115, FIXME 0718 /
            //    `expansion-qualification-scope.md` §2.4. A symbol inside quoted
            //    DATA is not a reference at all, so the §2.1 rule ("qualify iff a
            //    free reference") excludes it: qualifying `'(name)` to `'(dm/name)`
            //    would change a runtime VALUE. Structurally identical to
            //    `expand_scoped`'s Rule Q / Rule QQ and recognized by the SAME
            //    shared `cranelisp_types::quote_head` classifier — never a private copy
            //    (Principle 7). Placed FIRST, as in the expander.
            match cranelisp_types::quote_head(&children) {
                // Rule Q — held fully verbatim, no descent.
                Some(cranelisp_types::QuoteHead::Quote) => {
                    return Sexp::List(children, span);
                }
                // Rule QQ — the body is walked verbatim at qq_depth 0; only the
                // body of a LIVE unquote/unquote-splicing is re-entered.
                Some(cranelisp_types::QuoteHead::Quasiquote) => {
                    let mut children = children;
                    let body = children.pop().expect("len == 2: quasiquote body");
                    let head_sym = children.pop().expect("len == 2: quasiquote head");
                    let inner = qualify_shield_qq(ctx, body, shadows, 0);
                    return Sexp::List(vec![head_sym, inner], span);
                }
                Some(
                    cranelisp_types::QuoteHead::Unquote
                    | cranelisp_types::QuoteHead::UnquoteSplicing,
                )
                | None => {}
            }
            // 1. `defmacro`/`defmacro-` (§2.6): a macro-emitted macro definition
            //    carries the SAME binder slots as `defn` — head, name, optional
            //    docstring, param bracket(s) — and qualifying the NAME would emit
            //    `(defmacro dm/name …)`, which the frontend rejects as a qualified
            //    binder head (a wrong-reject). Route to `qualify_defn`, which
            //    already holds exactly those slots verbatim and qualifies only the
            //    clause bodies under the param scope (P7 — no second shape).
            //    `defmacro` deliberately stays OUT of `expander::is_binding_form`
            //    (that predicate gates `expand_binding_form`, whose arms do not
            //    cover it); the shield is expressed here, structurally, via the
            //    shared `expander::is_defmacro_head` test.
            if let Some(Sexp::Symbol(head, _)) = children.first()
                && super::is_defmacro_head(head)
            {
                return qualify_defn(ctx, children, span, shadows);
            }
            // 2. A binding special form establishes a lexical scope: its binder
            // slots are held verbatim and its value/body children are qualified
            // under the EXTENDED scope. Dispatch through the SHARED enumeration
            // (`expander::is_binding_form`) so both walks stay in lockstep.
            if let Some(Sexp::Symbol(head, _)) = children.first()
                && super::is_binding_form(head)
            {
                let head = head.clone();
                return qualify_binding_form(ctx, &head, children, span, shadows);
            }
            // Non-binding head — recurse into every child under the current
            // (unchanged) scope, qualifying call targets and arguments.
            let qualified_children: Vec<Sexp> = children
                .into_iter()
                .map(|c| qualify_scoped(ctx, c, shadows))
                .collect();
            Sexp::List(qualified_children, span)
        }
        Sexp::Bracket(children, span) => {
            let qualified_children: Vec<Sexp> = children
                .into_iter()
                .map(|c| qualify_scoped(ctx, c, shadows))
                .collect();
            Sexp::Bracket(qualified_children, span)
        }
        // Other sexp types (Int, Float, String, Bool) pass through unchanged.
        other => other,
    }
}

/// The qualify walk's quasiquote shield — the P7 twin of `expander::shield_qq`
/// (S115, FIXME 0718 / `expansion-qualification-scope.md` §2.4).
///
/// Everything under a `quasiquote` is held VERBATIM except the body of a **live**
/// `unquote`/`unquote-splicing`, which is ordinary expression position (§9.4.2)
/// and is re-entered through [`qualify_scoped`] under the enclosing scope. The
/// nesting math mirrors the expander exactly: live at `qq_depth == 0`; a nested
/// `quasiquote` increments; an unquote under a nested quasiquote decrements. A
/// nested `(quote …)` is NOT short-circuited (the expander's §5.1 rule) — the
/// walk descends structurally at the same depth so inner live unquotes are found.
fn qualify_shield_qq(
    ctx: &QualifyScope,
    node: Sexp,
    shadows: &HashSet<String>,
    qq_depth: usize,
) -> Sexp {
    match node {
        Sexp::List(children, span) if !children.is_empty() => {
            match cranelisp_types::quote_head(&children) {
                Some(
                    cranelisp_types::QuoteHead::Unquote
                    | cranelisp_types::QuoteHead::UnquoteSplicing,
                ) => {
                    let mut children = children;
                    let body = children.pop().expect("len == 2: unquote body");
                    let head_sym = children.pop().expect("len == 2: unquote head");
                    let inner = if qq_depth == 0 {
                        // LIVE unquote — ordinary expression position: qualify.
                        qualify_scoped(ctx, body, shadows)
                    } else {
                        qualify_shield_qq(ctx, body, shadows, qq_depth - 1)
                    };
                    return Sexp::List(vec![head_sym, inner], span);
                }
                Some(cranelisp_types::QuoteHead::Quasiquote) => {
                    let mut children = children;
                    let body = children.pop().expect("len == 2: quasiquote body");
                    let head_sym = children.pop().expect("len == 2: quasiquote head");
                    let inner = qualify_shield_qq(ctx, body, shadows, qq_depth + 1);
                    return Sexp::List(vec![head_sym, inner], span);
                }
                Some(cranelisp_types::QuoteHead::Quote) | None => {}
            }
            let mapped: Vec<Sexp> = children
                .into_iter()
                .map(|c| qualify_shield_qq(ctx, c, shadows, qq_depth))
                .collect();
            Sexp::List(mapped, span)
        }
        Sexp::Bracket(children, span) => {
            // Brackets can't head an unquote but CAN contain live unquotes (`[~x]`).
            let mapped: Vec<Sexp> = children
                .into_iter()
                .map(|c| qualify_shield_qq(ctx, c, shadows, qq_depth))
                .collect();
            Sexp::Bracket(mapped, span)
        }
        // Atoms (INCLUDING bare symbols — quoted data, never references) and the
        // empty list are held verbatim.
        other => other,
    }
}

/// Qualify a FREE bare symbol (already known not to be lexically bound). The
/// original scope-blind body — the already-qualified/annotation/`_`/
/// current-module-availability skips, then the defining-module lookup.
fn qualify_free_symbol(ctx: &QualifyScope, sexp: Sexp) -> Sexp {
    let Sexp::Symbol(ref name, span) = sexp else {
        return sexp;
    };
    // Skip already-qualified names, type annotations, special names.
    if name.contains('/') || name.starts_with(':') || name.starts_with('_') {
        return sexp;
    }
    // Skip if the symbol is already available in the current module.
    if let Some(table) = ctx.symbol_tables.get(ctx.current_module)
        && table.get(name).is_some()
    {
        return sexp;
    }
    // Check the defining module for this symbol.
    let Some(table) = ctx.symbol_tables.get(ctx.defining_module) else {
        return sexp;
    };
    let candidates = table.name_candidates(&Symbol::from(name.as_str()));
    let qual_module = if candidates.len() == 1 {
        &candidates[0].source.module
    } else if table.get(name).is_some() {
        ctx.defining_module
    } else {
        return sexp;
    };
    let qualified = format!("{}/{}", qual_module.as_ref(), name);
    Sexp::Symbol(qualified, span)
}

/// Dispatch a binding special form to its scope-aware qualifier — the one-to-one
/// mirror of `expander::expand_binding_form` (FIXME 0670). Each arm holds its
/// binder slots verbatim, accumulates the introduced names into the scope, and
/// qualifies the value/body children under the extended scope.
fn qualify_binding_form(
    ctx: &QualifyScope,
    head: &str,
    children: Vec<Sexp>,
    span: Span,
    shadows: &HashSet<String>,
) -> Sexp {
    match head {
        "let" => qualify_let(ctx, children, span, shadows),
        "fn" | "lambda" => qualify_fn(ctx, children, span, shadows),
        "defn" | "defn-" => qualify_defn(ctx, children, span, shadows),
        "match" => qualify_match(ctx, children, span, shadows),
        _ => unreachable!("invariant: is_binding_form gates qualify_binding_form"),
    }
}

/// Fallback: qualify every child under the unchanged scope (the shape did not
/// match the binding form's expected structure; the AST builder reports it).
fn qualify_children_unchanged(
    ctx: &QualifyScope,
    children: Vec<Sexp>,
    span: Span,
    shadows: &HashSet<String>,
) -> Sexp {
    let qc: Vec<Sexp> = children
        .into_iter()
        .map(|c| qualify_scoped(ctx, c, shadows))
        .collect();
    Sexp::List(qc, span)
}

/// `(let [name val …] body)` — each binding NAME is a binder (held verbatim),
/// each VALUE qualified in the scope so far (sequential `let*`), body qualified
/// with every bound name shadowing. Mirrors `expander::expand_let`.
fn qualify_let(
    ctx: &QualifyScope,
    children: Vec<Sexp>,
    span: Span,
    shadows: &HashSet<String>,
) -> Sexp {
    if children.len() != 3 {
        return qualify_children_unchanged(ctx, children, span, shadows);
    }
    let Sexp::Bracket(bind_items, bracket_span) = children[1].clone() else {
        return qualify_children_unchanged(ctx, children, span, shadows);
    };
    let mut scope = shadows.clone();
    let mut new_items: Vec<Sexp> = Vec::with_capacity(bind_items.len());
    let mut i = 0;
    while i < bind_items.len() {
        // Binding NAME — a fresh local binder; held verbatim, never qualified.
        let binder = match &bind_items[i] {
            Sexp::Symbol(n, _) => Some(n.clone()),
            _ => None,
        };
        new_items.push(bind_items[i].clone());
        i += 1;
        // Optional `:Type` annotations on the value are held verbatim.
        while i < bind_items.len() && super::is_annotation_symbol(&bind_items[i]) {
            new_items.push(bind_items[i].clone());
            i += 1;
        }
        // The value expression is qualified in the scope so far (the binder is
        // NOT yet in scope for its own RHS — sequential `let`).
        if i < bind_items.len() {
            let v = qualify_scoped(ctx, bind_items[i].clone(), &scope);
            new_items.push(v);
            i += 1;
        }
        // The binder now shadows subsequent bindings and the body.
        if let Some(b) = binder {
            scope.insert(b);
        }
    }
    let body = qualify_scoped(ctx, children[2].clone(), &scope);
    Sexp::List(
        vec![
            children[0].clone(),
            Sexp::Bracket(new_items, bracket_span),
            body,
        ],
        span,
    )
}

/// `(fn [params] body)` / `(lambda [params] body)` — param bracket held verbatim
/// (binder names), body qualified with the params shadowing. Mirrors
/// `expander::expand_fn`.
fn qualify_fn(
    ctx: &QualifyScope,
    children: Vec<Sexp>,
    span: Span,
    shadows: &HashSet<String>,
) -> Sexp {
    if children.len() != 3 {
        return qualify_children_unchanged(ctx, children, span, shadows);
    }
    let Sexp::Bracket(param_items, _) = &children[1] else {
        return qualify_children_unchanged(ctx, children, span, shadows);
    };
    let scope = super::params_scope(param_items, shadows);
    let body = qualify_scoped(ctx, children[2].clone(), &scope);
    Sexp::List(vec![children[0].clone(), children[1].clone(), body], span)
}

/// `(defn name "doc"? [params] body…)` / multi-arity `(defn name (…) …)` — head,
/// name, docstring held verbatim; each variant's params verbatim and its body
/// qualified with the params (and the defn NAME, §2.5) shadowing. Mirrors
/// `expander::expand_defn`.
///
/// Also serves `(defmacro …)`/`(defmacro-)` (§2.6 shield): the clause shape is
/// identical — head, name, optional docstring, param bracket(s), bodies — so the
/// defmacro shield is this function, not a second copy.
fn qualify_defn(
    ctx: &QualifyScope,
    children: Vec<Sexp>,
    span: Span,
    shadows: &HashSet<String>,
) -> Sexp {
    if children.len() < 3 {
        return qualify_children_unchanged(ctx, children, span, shadows);
    }
    let mut out: Vec<Sexp> = Vec::with_capacity(children.len());
    out.push(children[0].clone()); // defn / defn- / defmacro / defmacro-
    out.push(children[1].clone()); // name (a binder — verbatim)
    // S115 (FIXME 0718 / `expansion-qualification-scope.md` §2.5): the defn NAME
    // is in scope inside its own body. Without this seeding a first-definition
    // self-call `(defn f [x] (f x))` mis-qualifies to `dm/f` whenever a defining
    // module also provides `f` — the current-module availability skip in
    // `qualify_free_symbol` cannot fire, because `f` is being defined this
    // instant. `expander::expand_defn` carries the identical seeding (P7).
    let shadows = &match &children[1] {
        Sexp::Symbol(n, _) => {
            let mut s = shadows.clone();
            s.insert(n.clone());
            s
        }
        _ => shadows.clone(),
    };
    let mut idx = 2;
    if let Some(Sexp::Str(..)) = children.get(idx) {
        out.push(children[idx].clone()); // docstring
        idx += 1;
    }
    match children.get(idx) {
        // Single arity: [params] followed by the body form(s).
        Some(Sexp::Bracket(param_items, _)) => {
            let scope = super::params_scope(param_items, shadows);
            out.push(children[idx].clone()); // params verbatim
            for c in &children[idx + 1..] {
                out.push(qualify_scoped(ctx, c.clone(), &scope));
            }
        }
        // Multi arity: each remaining child is a `([params] body)` variant.
        Some(Sexp::List(..)) => {
            for c in &children[idx..] {
                out.push(qualify_defn_variant(ctx, c, shadows));
            }
        }
        // Unexpected shape — qualify generically (the AST builder reports it).
        _ => {
            for c in &children[idx..] {
                out.push(qualify_scoped(ctx, c.clone(), shadows));
            }
        }
    }
    Sexp::List(out, span)
}

/// A single multi-arity `defn` variant `([params] body)` — params verbatim, body
/// qualified with the params shadowing. Mirrors `expander::expand_defn_variant`.
fn qualify_defn_variant(ctx: &QualifyScope, sexp: &Sexp, shadows: &HashSet<String>) -> Sexp {
    let Sexp::List(items, vspan) = sexp else {
        return qualify_scoped(ctx, sexp.clone(), shadows);
    };
    let Some(Sexp::Bracket(param_items, _)) = items.first() else {
        return qualify_scoped(ctx, sexp.clone(), shadows);
    };
    if items.len() != 2 {
        return qualify_scoped(ctx, sexp.clone(), shadows);
    }
    let scope = super::params_scope(param_items, shadows);
    let body = qualify_scoped(ctx, items[1].clone(), &scope);
    Sexp::List(vec![items[0].clone(), body], *vspan)
}

/// `(match scrutinee… [pat body …])` — scrutinee qualified in the current scope;
/// each arm PATTERN held verbatim (its variables are binders), each arm BODY
/// qualified with those pattern variables shadowing. Mirrors
/// `expander::expand_match`.
fn qualify_match(
    ctx: &QualifyScope,
    children: Vec<Sexp>,
    span: Span,
    shadows: &HashSet<String>,
) -> Sexp {
    if children.len() < 3 {
        return qualify_children_unchanged(ctx, children, span, shadows);
    }
    let last = children.len() - 1;
    let Sexp::Bracket(arm_items, arms_span) = children[last].clone() else {
        return qualify_children_unchanged(ctx, children, span, shadows);
    };
    let mut out: Vec<Sexp> = Vec::with_capacity(children.len());
    out.push(children[0].clone()); // match
    // Scrutinee region (possibly a `:Type form` pair) — ordinary reads.
    for c in &children[1..last] {
        out.push(qualify_scoped(ctx, c.clone(), shadows));
    }
    if !arm_items.len().is_multiple_of(2) {
        // Malformed arms — qualify generically (the AST builder reports it).
        let qualified: Vec<Sexp> = arm_items
            .into_iter()
            .map(|c| qualify_scoped(ctx, c, shadows))
            .collect();
        out.push(Sexp::Bracket(qualified, arms_span));
        return Sexp::List(out, span);
    }
    let mut new_arms: Vec<Sexp> = Vec::with_capacity(arm_items.len());
    let mut i = 0;
    while i + 1 < arm_items.len() {
        let pattern = &arm_items[i];
        let body = &arm_items[i + 1];
        let mut scope = shadows.clone();
        scope.extend(super::pattern_binders(pattern));
        new_arms.push(pattern.clone()); // pattern verbatim (binders, not reads)
        new_arms.push(qualify_scoped(ctx, body.clone(), &scope));
        i += 2;
    }
    out.push(Sexp::Bracket(new_arms, arms_span));
    Sexp::List(out, span)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Qualify a whole expansion against `defining_module` with no call-site scope.
    fn qualify_expanded_sexp(
        symbol_tables: &dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable>,
        current_module: &ModuleFullPath,
        defining_module: &ModuleFullPath,
        sexp: Sexp,
    ) -> Sexp {
        qualify_expansion(
            QualifyScope {
                symbol_tables,
                current_module,
                defining_module,
                caller_text: &HashSet::new(),
            },
            sexp,
            &HashSet::new(),
        )
    }

    // -----------------------------------------------------------------------
    // FIXME 0670 — the expansion-seam qualify pass is scope-aware.
    //
    // Live-defect demonstration (the RED→GREEN unit flip that replaces the
    // evaporated e2e flip, `design/int/expansion-qualification-scope.md` §3): the fixture's
    // `defining_modules`/table state is constructed so the incidental
    // "available in the current module" skip-guard does NOT fire — the binder
    // name `name` is present in a DEFINING module but absent from the current
    // module. Against the scope-BLIND pass every one of these mis-qualifies the
    // binder (`name` → `dm/name`, which the frontend then rejects at the param
    // "a binder must be bare"); the scope-aware pass holds binders + local reads
    // verbatim and qualifies only free defining-module references.
    // -----------------------------------------------------------------------

    /// A one-module table set whose `module` publicly defines each of `names`
    /// (as slot-less user fns — the qualify pass only reads presence + kind).
    fn tables_with_defs(
        module: &str,
        names: &[&str],
    ) -> dashmap::DashMap<ModuleFullPath, crate::code::SessionSymbolTable> {
        let path = ModuleFullPath::from(module);
        let mut st = crate::code::SessionSymbolTable::new_with_params(path.clone());
        for n in names {
            let _ = crate::repl::test_support::install_userfn(
                &mut st,
                n,
                None,
                cranelisp_types::Visibility::Public,
            );
        }
        let tables = dashmap::DashMap::new();
        tables.insert(path, st);
        tables
    }

    /// Parse `src` to its single top-level sexp (the expanded-shape fixture).
    fn parse_one(src: &str) -> Sexp {
        cranelisp_frontend::parse(src).unwrap().remove(0)
    }

    // spec: expansion-qualification-scope.md §3 —
    // `qualify_skips_value_binders_and_local_reads`.
    #[test]
    fn qualify_skips_value_binders_and_local_reads() {
        // `dm` defines both the colliding binder name `name` AND the foreign
        // helper `wrap`; the current module `user` defines NEITHER, so the
        // availability skip cannot mask the binder mis-qualification.
        let tables = tables_with_defs("dm", &["name", "wrap"]);
        let current = ModuleFullPath::from("user");
        let dms = ModuleFullPath::from("dm");
        let input = parse_one("(defn greet [name] (wrap \"hi\" name))");

        let out = qualify_expanded_sexp(&tables, &current, &dms, input);
        let flat = out.format_flat();

        // The param BINDER stays bare and the body LOCAL READ stays bare.
        assert!(
            !flat.contains("dm/name"),
            "binder/local-read `name` must NOT be qualified: {flat}"
        );
        // The FREE foreign-helper reference IS qualified to its defining module.
        assert!(
            flat.contains("dm/wrap"),
            "free reference `wrap` must be qualified: {flat}"
        );
    }

    // spec: expansion-qualification-scope.md §3 —
    // `qualify_skips_let_and_match_binders`.
    #[test]
    fn qualify_skips_let_and_match_binders() {
        let tables = tables_with_defs("dm", &["name", "wrap"]);
        let current = ModuleFullPath::from("user");
        let dms = ModuleFullPath::from("dm");

        // let: binding NAME `name` + its body local read held bare; `wrap` free.
        let let_out = qualify_expanded_sexp(
            &tables,
            &current,
            &dms,
            parse_one("(let [name 1] (wrap name))"),
        );
        let lf = let_out.format_flat();
        assert!(
            !lf.contains("dm/name"),
            "let binder/read must stay bare: {lf}"
        );
        assert!(
            lf.contains("dm/wrap"),
            "free `wrap` must qualify (let): {lf}"
        );

        // match: var-pattern `name` + arm body local read held bare; `wrap` free.
        let match_out = qualify_expanded_sexp(
            &tables,
            &current,
            &dms,
            parse_one("(match 0 [name (wrap name)])"),
        );
        let mf = match_out.format_flat();
        assert!(
            !mf.contains("dm/name"),
            "match binder/read must stay bare: {mf}"
        );
        assert!(
            mf.contains("dm/wrap"),
            "free `wrap` must qualify (match): {mf}"
        );
    }

    // Completeness twin (the shared-enumeration matrix): one cell per value-level
    // binder form. A per-form fix that greened one but diverged a sibling would
    // fail its cell — the matrix pressures the ONE shared enumeration.
    // spec: expansion-qualification-scope.md §3 — completeness twin.
    #[test]
    fn qualify_binder_completeness_matrix_defn_fn_let_match() {
        let tables = tables_with_defs("dm", &["x", "wrap"]);
        let current = ModuleFullPath::from("user");
        let dms = ModuleFullPath::from("dm");
        // (form-source, label) — each binds `x` and reads it; `wrap` is free.
        let cells = [
            ("(defn f [x] (wrap x))", "defn"),
            ("(fn [x] (wrap x))", "fn"),
            ("(lambda [x] (wrap x))", "lambda"),
            ("(let [x 1] (wrap x))", "let"),
            ("(match 0 [x (wrap x)])", "match"),
        ];
        for (src, label) in cells {
            let out = qualify_expanded_sexp(&tables, &current, &dms, parse_one(src));
            let flat = out.format_flat();
            assert!(
                !flat.contains("dm/x"),
                "[{label}] binder/local-read `x` must stay bare: {flat}"
            );
            assert!(
                flat.contains("dm/wrap"),
                "[{label}] free `wrap` must be qualified: {flat}"
            );
        }
    }

    // Negative-direction fence: a genuinely FREE defining-module reference (not
    // shadowed by any binder) still qualifies — the fix must not over-shield.
    // spec: expansion-qualification-scope.md §2.1 — free references qualify.
    #[test]
    fn qualify_still_qualifies_free_reference_not_shadowed() {
        let tables = tables_with_defs("dm", &["helper"]);
        let current = ModuleFullPath::from("user");
        let dms = ModuleFullPath::from("dm");
        // No binder introduces `helper`; it is a free defining-module reference.
        let out =
            qualify_expanded_sexp(&tables, &current, &dms, parse_one("(let [y 1] (helper y))"));
        let flat = out.format_flat();
        assert!(
            flat.contains("dm/helper"),
            "a free defining-module reference must still qualify: {flat}"
        );
    }

    // -----------------------------------------------------------------------
    // FIXME 0718 — the three residual qualify-walk asymmetries
    // (`expansion-qualification-scope.md` §2.4/§2.5/§2.6). Each fixture puts
    // the colliding name in a DEFINING module and NOT in the current module, so
    // the `qualify_free_symbol` availability skip cannot mask the defect;
    // fail-on-revert holds for all three.
    // -----------------------------------------------------------------------

    // spec: expansion-qualification-scope.md §2.4 — the quote shield (Rule Q).
    // A symbol inside quoted DATA is not a reference; qualifying it would change
    // a runtime VALUE (`'(name)` -> `'(dm/name)`).
    #[test]
    fn qualify_holds_quoted_datum_verbatim() {
        let tables = tables_with_defs("dm", &["name", "wrap"]);
        let current = ModuleFullPath::from("user");
        let dms = ModuleFullPath::from("dm");
        let out = qualify_expanded_sexp(
            &tables,
            &current,
            &dms,
            parse_one("(defn f [] (wrap (quote (name))))"),
        );
        let flat = out.format_flat();
        assert!(
            !flat.contains("dm/name"),
            "a symbol inside quoted data must stay bare: {flat}"
        );
        // Discriminating control: the SAME name outside the quote still
        // qualifies, so the shield is scoped to quoted data, not a blanket skip.
        assert!(
            flat.contains("dm/wrap"),
            "a free reference outside the quote must still qualify: {flat}"
        );
    }

    // spec: expansion-qualification-scope.md §2.4 — the quasiquote shield
    // (Rule QQ): template body verbatim, LIVE unquote bodies re-entered.
    #[test]
    fn qualify_quasiquote_holds_template_but_qualifies_live_unquote() {
        let tables = tables_with_defs("dm", &["name", "wrap"]);
        let current = ModuleFullPath::from("user");
        let dms = ModuleFullPath::from("dm");
        let out = qualify_expanded_sexp(
            &tables,
            &current,
            &dms,
            parse_one("(defn f [] (quasiquote (name (unquote (wrap 1)))))"),
        );
        let flat = out.format_flat();
        assert!(
            !flat.contains("dm/name"),
            "a template symbol under quasiquote must stay bare: {flat}"
        );
        assert!(
            flat.contains("dm/wrap"),
            "a LIVE unquote body is ordinary expression position and must \
             qualify: {flat}"
        );
    }

    // spec: expansion-qualification-scope.md §2.4 — nesting math: an unquote
    // under a NESTED quasiquote is not live, so its body stays verbatim.
    #[test]
    fn qualify_quasiquote_nested_unquote_is_not_live() {
        let tables = tables_with_defs("dm", &["wrap", "helper"]);
        let current = ModuleFullPath::from("user");
        let dms = ModuleFullPath::from("dm");
        let out = qualify_expanded_sexp(
            &tables,
            &current,
            &dms,
            parse_one("(helper (quasiquote (quasiquote (unquote (wrap 1)))))"),
        );
        let flat = out.format_flat();
        assert!(
            !flat.contains("dm/wrap"),
            "an unquote under a nested quasiquote is not live; its body must \
             stay verbatim: {flat}"
        );
        // Discriminating control (FIXME 0792): the free `helper` OUTSIDE the
        // quasiquote still qualifies, so this cell fails under a blanket
        // "qualify nothing here" regression instead of being rescued by a
        // sibling cell's control.
        assert!(
            flat.contains("dm/helper"),
            "control: a free reference outside the quasiquote must still \
             qualify: {flat}"
        );
    }

    // spec: expansion-qualification-scope.md §2.5 — the defn name is in scope in
    // its own body, so a first-definition self-call is never qualified away.
    #[test]
    fn qualify_seeds_defn_name_into_its_body_scope() {
        // `dm` provides `f`; `user` does not yet (the defn is being defined now),
        // so the current-module availability skip cannot fire.
        let tables = tables_with_defs("dm", &["f", "wrap"]);
        let current = ModuleFullPath::from("user");
        let dms = ModuleFullPath::from("dm");
        let out = qualify_expanded_sexp(
            &tables,
            &current,
            &dms,
            parse_one("(defn f [x] (f (wrap x)))"),
        );
        let flat = out.format_flat();
        assert!(
            !flat.contains("dm/f"),
            "a recursive self-call refers to the defn being defined and must \
             stay bare: {flat}"
        );
        // Discriminating control (FIXME 0792): a free defining-module reference
        // in the SAME body still qualifies — the seeding is defn-name-scoped,
        // not a blanket "qualify nothing in a defn body".
        assert!(
            flat.contains("dm/wrap"),
            "control: a free reference in the same body must still qualify: {flat}"
        );
    }

    // spec: expansion-qualification-scope.md §2.5 — multi-arity variants share
    // the same self-name scope.
    #[test]
    fn qualify_seeds_defn_name_into_multi_arity_variant_bodies() {
        let tables = tables_with_defs("dm", &["f", "wrap"]);
        let current = ModuleFullPath::from("user");
        let dms = ModuleFullPath::from("dm");
        let out = qualify_expanded_sexp(
            &tables,
            &current,
            &dms,
            parse_one("(defn f ([x] (f x)) ([x y] (f (wrap x))))"),
        );
        let flat = out.format_flat();
        assert!(
            !flat.contains("dm/f"),
            "multi-arity variant bodies must also see the defn self-name: {flat}"
        );
        // Discriminating control (FIXME 0792): a free defining-module reference
        // inside a VARIANT body still qualifies.
        assert!(
            flat.contains("dm/wrap"),
            "control: a free reference in a variant body must still qualify: {flat}"
        );
    }

    // spec: expansion-qualification-scope.md §2.6 — the defmacro shield: a
    // macro-emitted `(defmacro name ...)` keeps a BARE name/params (a qualified
    // binder head is a frontend wrong-reject), while clause bodies still qualify.
    #[test]
    fn qualify_holds_defmacro_name_and_params_verbatim() {
        let tables = tables_with_defs("dm", &["name", "x", "wrap"]);
        let current = ModuleFullPath::from("user");
        let dms = ModuleFullPath::from("dm");
        let out = qualify_expanded_sexp(
            &tables,
            &current,
            &dms,
            parse_one("(defmacro name [x] (wrap x))"),
        );
        let flat = out.format_flat();
        assert!(
            !flat.contains("dm/name"),
            "the emitted defmacro NAME is a binder and must stay bare: {flat}"
        );
        assert!(
            !flat.contains("dm/x"),
            "the emitted defmacro PARAM (and its body read) must stay bare: {flat}"
        );
        assert!(
            flat.contains("dm/wrap"),
            "a free reference in a clause body must still qualify: {flat}"
        );
    }
}
