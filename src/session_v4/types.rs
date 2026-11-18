// session_v4::types — data-transfer + pure-helper layer (S87 §2.1).
//
// Every value type the binary surface passes around (settings, results,
// introspection DTOs, symbol-display DTOs, the run-mode enum) plus the leaf
// pure functions (`parens_balanced`, the dedup/extract/comment/type helpers,
// the worker-count clamp). Zero session-state dependency — all are `&self`-free
// or operate on borrowed args. Moved verbatim from `session_v4.rs` (S87 §2.1).

use std::path::PathBuf;

use cranelisp_types::{
    CodegenBehaviour, CranelispError, ErrorLocation, FQSymbol, ModuleFullPath, Sexp, Span, Symbol,
    TopLevel, Type, Warning, WrittenTraitImpl,
};

// ---------------------------------------------------------------------------
// RunMode (D1 ruling — design/arch/d1-introspection-repl-only.md §4)
// ---------------------------------------------------------------------------

/// Which CLI verb launched this session — the explicit run-mode carrier that
/// replaces the `introspection.is_some()` proxy (D1 ruling §4).
///
/// `RunMode` is an **int-internal** property of the running session; it is NOT
/// a `cranelisp-types` boundary type (frontend / typecheck / backend never see
/// it). It is deliberately **distinct** from backend's
/// `CompileMode::{Interactive, Batch, Release}` codegen-strategy axis (which
/// governs GOT-indirect-vs-direct codegen, not REPL-vs-batch session
/// behaviour). Do not conflate the two.
///
/// Two consumers:
/// - `populates_introspection()` — introspection is a REPL slash-command
///   facility (`/sig`, `/doc`, `/source`, `/clif`) and is populated ONLY in
///   `Repl` mode. The compile pipeline reads nothing from it; compile-necessary
///   data (macro `sexp`) lives on the symbol table.
/// - `is_repl()` — the platform layout-hash gate's REPL discriminator (REPL
///   warns-and-loads on drift; `--run`/`--link` refuse).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RunMode {
    /// `cranelisp` with no/REPL target — interactive prompt; populates
    /// introspection; layout-hash drift WARNS-AND-LOADS.
    Repl,
    /// `cranelisp --run <file>` — batch execute then `process::exit`;
    /// no introspection; layout-hash drift REFUSES. `cranelisp --test <file>`
    /// compiles in this mode too, then runs the program's tests instead of
    /// `main`.
    Run,
    /// `cranelisp --link <file>` — produce a standalone executable;
    /// no introspection; layout-hash drift REFUSES.
    Link,
}

impl RunMode {
    /// Introspection is REPL-only.
    pub fn populates_introspection(self) -> bool {
        matches!(self, RunMode::Repl)
    }

    /// The layout-hash gate's `is_repl` discriminator (REPL warns; Run/Link
    /// refuse).
    pub fn is_repl(self) -> bool {
        matches!(self, RunMode::Repl)
    }
}

// ---------------------------------------------------------------------------
// SessionSettings (pipeline-v4.md §10)
// ---------------------------------------------------------------------------

/// Session configuration. CLI flags override cranelisp.toml values.
pub struct SessionSettings {
    pub no_color: bool,
    pub no_cache: bool,
    pub codegen_behaviour: CodegenBehaviour,
    pub priority_workers: usize,
    pub nice_workers: usize,
    /// Which CLI verb launched the session (D1 ruling §4). Threaded onto
    /// `SharedState.run_mode`; the explicit REPL-vs-batch signal replacing the
    /// `introspection.is_some()` proxy.
    pub run_mode: RunMode,
}

// ---------------------------------------------------------------------------
// CommandResult (pipeline-v4.md §6.1)
// ---------------------------------------------------------------------------

/// Result of processing a REPL input line through `process_commands`.
pub enum CommandResult {
    /// Blank line, comment, or side-effect-only command.
    Nothing,
    /// Session should exit.
    Quit,
    /// Command that produces displayable output (e.g., /sig, /list).
    Final(String),
    /// Raw source text to submit for compilation.
    Compile(String),
}

// ---------------------------------------------------------------------------
// EvalResult (pipeline-v4.md §6.2)
// ---------------------------------------------------------------------------

/// Result of evaluating one input via `CompilerSession::eval()`.
///
/// Either an ordered batch of published definitions, a display-only candidate
/// listing, or a computed value. Every variant carries zero or more
/// warnings.
pub enum EvalResult {
    /// A genuine definition turn. Every symbol introduced by the entered
    /// statement is retained in emitted order; the producer invariant is that
    /// `symbols` is non-empty. This avoids selecting one arbitrary "primary"
    /// definition when a macro invocation emits several definitions.
    Definitions {
        symbols: Vec<FQSymbol>,
        warnings: Vec<Warning>,
    },
    /// A display-only lookup: every in-scope canonical candidate the entered
    /// spelling denotes (`repl/spec/04-self-documentation.md` §4.1.11), each
    /// rendered by its own §4.1 class rule.
    ///
    /// Introspection is not definition, and this variant carries identities
    /// only — no `defined` flag to get wrong, and no single type to invent for
    /// a set. That makes the Matrix E recording rule (FIXME 0486,
    /// `design/int/s102-defect-wave.md` §7.3) hold by construction: a lookup
    /// cannot write the turn's text over the authored `(defn …)` form that
    /// `/info` and `/source` serve, and cannot trigger §15.1 regeneration.
    Candidates {
        symbols: Vec<FQSymbol>,
        warnings: Vec<Warning>,
    },
    /// An expression was evaluated to a value.
    ///
    /// The value is NOT a loose `(i64, Type)` pair: it rides the ONE
    /// program-result owner (`design/int/result-owner.md` §4.2), armed across
    /// this boundary so the REPL driver can format it first and release it
    /// exactly once afterwards. `value()` / `ty()` read THROUGH the owner —
    /// there is no second copy of the owned word to leak or double-release.
    Val {
        result: crate::result_owner::OwnedProgramResult,
        warnings: Vec<Warning>,
    },
    /// A syntactically bare polymorphic value whose type is known but which
    /// cannot be executed because its `__expr` wrapper is a slot-less
    /// template. The REPL renders the authored value form by introspection;
    /// no runtime word or program-result owner is fabricated.
    DisplayValue {
        ty: Type,
        form: Sexp,
        warnings: Vec<Warning>,
    },
}

/// Stack-owned collection of the definitions emitted by one entered REPL
/// statement. Macro checkpoints can become durable before the ordinary HM
/// batch, so each row records whether its own publication boundary has
/// completed. An `impl` row is recorded by its form and keyed at publication
/// ([`Self::settle`]). The collection never enters shared/session state.
#[derive(Default)]
pub(crate) struct TurnDefinitions {
    rows: Vec<TurnDefinition>,
}

struct TurnDefinition {
    identity: BuiltIdentity,
    published: bool,
}

impl TurnDefinitions {
    pub(crate) fn record(&mut self, identity: BuiltIdentity, published: bool) {
        if let Some(existing) = self.rows.iter_mut().find(|row| row.identity == identity) {
            existing.published |= published;
            return;
        }
        self.rows.push(TurnDefinition {
            identity,
            published,
        });
    }

    /// Key every `impl` row from its writer record, in place, so the receipt
    /// keeps the emitted order. Rows that settle to one identity merge.
    pub(crate) fn settle(&mut self, identities: &ImplIdentities) -> Result<(), CranelispError> {
        let mut settled: Vec<TurnDefinition> = Vec::with_capacity(self.rows.len());
        for row in self.rows.drain(..) {
            let identity = BuiltIdentity::Keyed(identities.key_of(&row.identity)?);
            match settled.iter_mut().find(|kept| kept.identity == identity) {
                Some(kept) => kept.published |= row.published,
                None => settled.push(TurnDefinition {
                    identity,
                    published: row.published,
                }),
            }
        }
        self.rows = settled;
        Ok(())
    }

    /// Mark an ordinary batch published without inventing receipt rows. Every
    /// symbol must already have been recorded at its emitted position; a
    /// missing row means the source-order collector and typed program diverged.
    pub(crate) fn mark_published(&mut self, symbols: &[FQSymbol]) -> bool {
        let row_for = |row: &TurnDefinition, symbol: &FQSymbol| matches!(&row.identity, BuiltIdentity::Keyed(keyed) if keyed == symbol);
        if symbols
            .iter()
            .any(|symbol| !self.rows.iter().any(|row| row_for(row, symbol)))
        {
            return false;
        }
        for symbol in symbols {
            if let Some(row) = self.rows.iter_mut().find(|row| row_for(row, symbol)) {
                row.published = true;
            }
        }
        true
    }

    pub(crate) fn published_symbols(&self) -> Vec<FQSymbol> {
        self.rows
            .iter()
            .filter(|row| row.published)
            .filter_map(|row| match &row.identity {
                BuiltIdentity::Keyed(symbol) => Some(symbol.clone()),
                BuiltIdentity::Impl(_) => None,
            })
            .collect()
    }
}

/// The canonical identity one built top-level definition form introduces, as
/// the build stage knows it (`design/int/int.md` §6.13).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum BuiltIdentity {
    /// A `defn`, `deftrait` or `deftype`, keyed by its declared name at build.
    Keyed(FQSymbol),
    /// An `impl`, keyed only once typecheck has written its record: by the
    /// one writer record that carries the form's authored label.
    Impl(ImplForm),
}

/// An `impl` form awaiting its writer record: its authored label, and the
/// form's span for the invariant error when no single record carries it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ImplForm {
    label: Symbol,
    span: Span,
}

/// The identity a built top-level form introduces; `None` for an expression.
/// Derived from the typed top-level representation, never from spelling
/// conventions or an ambient symbol-table scan.
pub(crate) fn definition_identity(
    module: &ModuleFullPath,
    top: &TopLevel,
) -> Option<BuiltIdentity> {
    let keyed = |symbol: Symbol| {
        Some(BuiltIdentity::Keyed(FQSymbol {
            module: module.clone(),
            symbol,
        }))
    };
    match top {
        TopLevel::Defn(defn) => keyed(defn.name.clone()),
        TopLevel::TraitDecl(trait_decl) => keyed(Symbol::from(trait_decl.name.to_string())),
        TopLevel::TypeDef { name, .. } => keyed(Symbol::from(name.to_string())),
        TopLevel::TraitImpl(trait_impl) => Some(BuiltIdentity::Impl(ImplForm {
            label: trait_impl.authored_label(),
            span: trait_impl.span,
        })),
        TopLevel::Expr(_) => None,
    }
}

/// The canonical identity of a written implementation: its writer module and
/// the settled pair, held injectively by the types-owned key.
pub(crate) fn impl_identity(record: &WrittenTraitImpl) -> FQSymbol {
    FQSymbol {
        module: record.impl_module.clone(),
        symbol: cranelisp_types::trait_impl_key(&record.impl_type, &record.trait_name),
    }
}

/// What a keyed read of a writer's records by an authored label found.
#[derive(Debug)]
pub(crate) enum ImplRecordMatch<'r> {
    /// Exactly one record carries the label: the form's record.
    One(&'r WrittenTraitImpl),
    /// No record carries it.
    Unmatched,
    /// Several do. Never a pick: the label is not a key.
    Several,
}

/// The record among `writer`'s that carries `label`, under the exactly-one
/// rule (approved row D10, `design/arch/interfaces.md`): none or several is no
/// match.
pub(crate) fn match_impl_record<'r>(
    records: &'r [WrittenTraitImpl],
    writer: &ModuleFullPath,
    label: &Symbol,
) -> ImplRecordMatch<'r> {
    let mut carrying = records
        .iter()
        .filter(|record| record.impl_module == *writer && record.authored_label == *label);
    match (carrying.next(), carrying.next()) {
        (Some(record), None) => ImplRecordMatch::One(record),
        (None, _) => ImplRecordMatch::Unmatched,
        (Some(_), Some(_)) => ImplRecordMatch::Several,
    }
}

/// The identities of one cluster's `impl` forms, read by authored label from
/// the records its check wrote (Principle 26: derived once they have settled).
#[derive(Debug, Default)]
pub(crate) struct ImplIdentities {
    by_label: Vec<(Symbol, FQSymbol)>,
}

impl ImplIdentities {
    /// Key every `impl` form of `program` from `writer`'s `records`. A form
    /// that no single record carries is a located invariant error: no fixed
    /// source produces one (spec §8.6.5, §8.6.4).
    pub(crate) fn settle(
        writer: &ModuleFullPath,
        records: &[WrittenTraitImpl],
        program: &[TopLevel],
    ) -> Result<Self, CranelispError> {
        let mut by_label: Vec<(Symbol, FQSymbol)> = Vec::new();
        for top in program {
            let Some(BuiltIdentity::Impl(form)) = definition_identity(writer, top) else {
                continue;
            };
            if by_label.iter().any(|(label, _)| *label == form.label) {
                continue;
            }
            match match_impl_record(records, writer, &form.label) {
                ImplRecordMatch::One(record) => by_label.push((form.label, impl_identity(record))),
                found => return Err(unkeyed_impl(writer, &form, &found)),
            }
        }
        Ok(ImplIdentities { by_label })
    }

    /// The settled identity of a built definition.
    pub(crate) fn key_of(&self, identity: &BuiltIdentity) -> Result<FQSymbol, CranelispError> {
        match identity {
            BuiltIdentity::Keyed(symbol) => Ok(symbol.clone()),
            BuiltIdentity::Impl(form) => self
                .by_label
                .iter()
                .find(|(label, _)| *label == form.label)
                .map(|(_, symbol)| symbol.clone())
                .ok_or_else(|| CranelispError::CodegenError {
                    message: format!(
                        "internal: the `impl` form labelled `{}` was not keyed at publication",
                        form.label
                    ),
                    location: ErrorLocation::from_span(form.span),
                }),
        }
    }
}

fn unkeyed_impl(
    writer: &ModuleFullPath,
    form: &ImplForm,
    found: &ImplRecordMatch<'_>,
) -> CranelispError {
    let count = match found {
        ImplRecordMatch::Unmatched => "no",
        _ => "more than one",
    };
    CranelispError::CodegenError {
        message: format!(
            "internal: {count} implementation record written by module '{writer}' carries the \
             `impl` form's label `{}`, so the form has no identity",
            form.label
        ),
        location: ErrorLocation::from_span(form.span),
    }
}

impl EvalResult {
    pub fn warnings(&self) -> &[Warning] {
        match self {
            EvalResult::Definitions { warnings, .. } => warnings,
            EvalResult::Candidates { warnings, .. } => warnings,
            EvalResult::Val { warnings, .. } => warnings,
            EvalResult::DisplayValue { warnings, .. } => warnings,
        }
    }

    pub fn warnings_mut(&mut self) -> &mut Vec<Warning> {
        match self {
            EvalResult::Definitions { warnings, .. } => warnings,
            EvalResult::Candidates { warnings, .. } => warnings,
            EvalResult::Val { warnings, .. } => warnings,
            EvalResult::DisplayValue { warnings, .. } => warnings,
        }
    }

    /// The raw i64 value, borrowed from the result owner for observation.
    /// Returns 0 for definition and display-only results. Reading
    /// this is a READ, never a transfer — only
    /// [`Self::release_program_result`] finalizes the word.
    pub fn value(&self) -> i64 {
        match self {
            EvalResult::Val { result, .. } => result.observed_value(),
            EvalResult::Definitions { .. }
            | EvalResult::Candidates { .. }
            | EvalResult::DisplayValue { .. } => 0,
        }
    }

    /// Release the turn's owning result exactly once, AFTER the turn's
    /// display has been fully built (`design/int/result-owner.md` §4.2 — the
    /// value feedback must be complete before the release). A no-op for every
    /// other variant and for an inert (scalar/value-layout) result. The
    /// owner's `Drop` backstop covers any path that never reaches here.
    pub fn release_program_result(&mut self) {
        if let EvalResult::Val { result, .. } = self {
            result.release_in_place();
        }
    }

    /// The inferred type of a result that has exactly one value/display
    /// subject. A definition batch and a candidate listing have no single
    /// truthful type, so both return `None`.
    pub fn ty(&self) -> Option<&Type> {
        match self {
            EvalResult::Val { result, .. } => Some(result.ty()),
            EvalResult::DisplayValue { ty, .. } => Some(ty),
            EvalResult::Definitions { .. } | EvalResult::Candidates { .. } => None,
        }
    }

    /// Whether this turn GENUINELY (re)defined a symbol — the regeneration
    /// trigger (repl/spec.md §15.1: regeneration fires on successful
    /// DEFINITIONS only). A bare lookup is [`Self::Candidates`] and is
    /// therefore not a defining turn by construction: regenerating on a pure
    /// lookup rewrote the backing file (S102 W5 review F6 — with a
    /// hand-authored adopted `user.cl` that was a data-loss surface, not a
    /// harmless no-op).
    pub fn is_defining(&self) -> bool {
        matches!(self, EvalResult::Definitions { .. })
    }
}

#[cfg(test)]
mod eval_result_tests {
    use super::*;
    use cranelisp_types::ModuleFullPath;

    // spec: repl/spec.md §15.1 — regen triggers on successful definitions
    // only; a bare-lookup candidate listing MUST NOT trigger regen (F6 cell:
    // regen-silence on bare lookup, pinned at the predicate seam both regen
    // sites — main.rs and agent/pull.rs — gate on).
    #[test]
    fn is_defining_true_only_for_genuine_definition() {
        let fq = FQSymbol {
            module: ModuleFullPath::from("user"),
            symbol: cranelisp_types::Symbol::from("f"),
        };
        let batch = EvalResult::Definitions {
            symbols: vec![fq.clone()],
            warnings: Vec::new(),
        };
        let lookup = EvalResult::Candidates {
            symbols: vec![fq],
            warnings: Vec::new(),
        };
        let val = EvalResult::Val {
            result: crate::result_owner::OwnedProgramResult::inert(1, Type::Int),
            warnings: Vec::new(),
        };
        let display_value = EvalResult::DisplayValue {
            ty: Type::Var(0),
            form: Sexp::Bracket(Vec::new(), cranelisp_types::Span::SYNTHETIC),
            warnings: Vec::new(),
        };
        assert!(batch.is_defining());
        assert!(!lookup.is_defining(), "bare lookup must not trigger regen");
        assert!(!val.is_defining());
        assert!(!display_value.is_defining());
        assert_eq!(
            lookup.ty(),
            None,
            "a candidate listing has no single truthful type"
        );
    }

    // design: design/int/s117-conformance-recovery.md §6.2 — retrying the
    // ordinary prefix around an already-published macro checkpoint must not
    // duplicate or reorder the turn's definition receipt.
    #[test]
    fn turn_definitions_preserve_emitted_order_across_retry() {
        let ordinary_before = FQSymbol {
            module: ModuleFullPath::from("user"),
            symbol: cranelisp_types::Symbol::from("backing"),
        };
        let macro_checkpoint = FQSymbol {
            module: ModuleFullPath::from("user"),
            symbol: cranelisp_types::Symbol::from("binding"),
        };
        let ordinary_after = FQSymbol {
            module: ModuleFullPath::from("user"),
            symbol: cranelisp_types::Symbol::from("later"),
        };

        let keyed = |symbol: &FQSymbol| BuiltIdentity::Keyed(symbol.clone());
        let mut definitions = TurnDefinitions::default();
        definitions.record(keyed(&ordinary_before), false);
        definitions.record(keyed(&macro_checkpoint), true);

        // Retry replays the uncommitted ordinary prefix but not the macro.
        definitions.record(keyed(&ordinary_before), false);
        definitions.record(keyed(&ordinary_after), false);
        definitions.mark_published(&[ordinary_before.clone(), ordinary_after.clone()]);

        assert_eq!(
            definitions.published_symbols(),
            vec![ordinary_before, macro_checkpoint, ordinary_after]
        );
    }

    #[test]
    fn turn_definitions_refuse_unrecorded_publication() {
        let recorded = FQSymbol {
            module: ModuleFullPath::from("user"),
            symbol: cranelisp_types::Symbol::from("recorded"),
        };
        let missing = FQSymbol {
            module: ModuleFullPath::from("user"),
            symbol: cranelisp_types::Symbol::from("missing"),
        };
        let mut definitions = TurnDefinitions::default();
        definitions.record(BuiltIdentity::Keyed(recorded), false);

        assert!(!definitions.mark_published(&[missing]));
        assert!(definitions.published_symbols().is_empty());
    }

    fn impl_top(source: &str) -> TopLevel {
        let sexp = cranelisp_frontend::parse(source).unwrap().remove(0);
        crate::worker::build_program_compat(std::slice::from_ref(&sexp))
            .unwrap()
            .remove(0)
    }

    fn written(type_home: &str, type_name: &str, label: &str) -> cranelisp_types::WrittenTraitImpl {
        cranelisp_types::WrittenTraitImpl::new(
            cranelisp_types::FQTraitName::new("prelude".into(), "Show".into()),
            cranelisp_types::FQTypeName::new(type_home.into(), type_name.into()),
            "user".into(),
            vec![cranelisp_types::Symbol::from("show")],
            cranelisp_types::Visibility::Public,
            label.into(),
        )
    }

    // spec: design/int/int.md §6.13 — the live turn keys an `impl` from the
    // writer record carrying its authored label: a form whose head is the
    // renamed `B` takes the record's settled `lib/Box`, held injectively, and
    // the receipt row recorded at build settles in place.
    #[test]
    fn live_turn_keys_an_impl_from_its_writer_record() {
        let user = ModuleFullPath::from("user");
        let program = vec![
            impl_top("(impl Show B (defn show [x] \"lib\"))"),
            impl_top("(impl Show Box (defn show [x] \"local\"))"),
        ];
        let records = [
            written("user", "Box", "Show.Box"),
            written("lib", "Box", "Show.B"),
        ];
        let identities = ImplIdentities::settle(&user, &records, &program).unwrap();

        let keys: Vec<FQSymbol> = program
            .iter()
            .map(|top| {
                identities
                    .key_of(&definition_identity(&user, top).unwrap())
                    .unwrap()
            })
            .collect();
        assert_eq!(
            keys,
            vec![impl_identity(&records[1]), impl_identity(&records[0])]
        );
        assert_ne!(keys[0], keys[1], "same-named types stay two identities");

        let mut definitions = TurnDefinitions::default();
        for top in &program {
            definitions.record(definition_identity(&user, top).unwrap(), false);
        }
        assert!(
            definitions.published_symbols().is_empty(),
            "an unsettled impl row is never published"
        );
        definitions.settle(&identities).unwrap();
        assert!(definitions.mark_published(&keys));
        assert_eq!(definitions.published_symbols(), keys);
    }

    // spec: design/int/int.md §6.13 — none or several records carrying the
    // form's label is the live turn's located invariant error, never a pick.
    // The records are planted directly: no fixed source produces them.
    #[test]
    fn live_turn_refuses_an_impl_with_no_single_record() {
        let user = ModuleFullPath::from("user");
        let source = "(impl Show B (defn show [x] 1))";
        let program = vec![impl_top(source)];
        let span = match &program[0] {
            TopLevel::TraitImpl(trait_impl) => trait_impl.span,
            other => panic!("expected an impl, got {other:?}"),
        };

        let one = [written("lib", "Box", "Show.B")];
        assert!(
            ImplIdentities::settle(&user, &one, &program).is_ok(),
            "control"
        );

        let several = [
            written("lib", "Box", "Show.B"),
            written("alt", "Box", "Show.B"),
        ];
        let unmatched = [written("lib", "Box", "Show.lib/Box")];
        for records in [&several[..], &unmatched[..]] {
            match ImplIdentities::settle(&user, records, &program) {
                Err(CranelispError::CodegenError { message, location }) => {
                    assert!(message.contains("`Show.B`"), "{message}");
                    assert_eq!(location.span, span, "located at the impl form");
                }
                other => panic!("expected the invariant error, got {other:?}"),
            }
        }
    }

    // API: a definition batch deliberately has no singular inferred type.
    #[test]
    fn definition_batch_has_no_singular_type() {
        let result = EvalResult::Definitions {
            symbols: vec![FQSymbol {
                module: ModuleFullPath::from("user"),
                symbol: cranelisp_types::Symbol::from("f"),
            }],
            warnings: Vec::new(),
        };
        assert_eq!(result.ty(), None);
    }

    // -----------------------------------------------------------------------
    // §6 row 4 — REPL display: the result owner rides `EvalResult::Val` armed
    // across the execution/formatting boundary, and the turn releases it after
    // the display read (`design/int/result-owner.md` §4.2).
    // -----------------------------------------------------------------------

    use crate::result_owner::OwnedProgramResult;
    use crate::result_owner::test_support::{RecordingResolver, record, take_events};

    fn armed_val(value: i64) -> EvalResult {
        let tables: cranelisp_types::SymbolTables<crate::code::Code, ()> = dashmap::DashMap::new();
        let result = OwnedProgramResult::new(
            value,
            Type::String,
            None,
            &ModuleFullPath::from("user"),
            &tables,
            &RecordingResolver::new(),
        )
        .expect("String is an owning result");
        EvalResult::Val {
            result,
            warnings: Vec::new(),
        }
    }

    // spec: design/int/result-owner.md §4.2 — the formatter READS the word
    // through the armed owner; the release happens after the display is
    // complete, and exactly once.
    #[test]
    fn val_display_read_precedes_the_single_release() {
        let _ = take_events();
        let mut val = armed_val(77);
        record(format!("display-read({})", val.value()));
        assert_eq!(
            val.ty(),
            Some(&Type::String),
            "type reads through the owner too"
        );
        val.release_program_result();
        record("prompt-returns");
        drop(val);
        assert_eq!(
            take_events(),
            vec![
                "display-read(77)".to_string(),
                "glue(77)".to_string(),
                "prompt-returns".to_string(),
            ],
            "the display must be read before the release, and the release must \
             happen exactly once even though the carrier is dropped afterwards"
        );
    }

    // spec: design/int/result-owner.md §5 — a second release is a no-op: the
    // owner disarmed at the first, and there is one chokepoint.
    #[test]
    fn val_double_release_is_a_no_op() {
        let _ = take_events();
        let mut val = armed_val(5);
        val.release_program_result();
        val.release_program_result();
        drop(val);
        assert_eq!(take_events(), vec!["glue(5)".to_string()]);
    }

    // spec: design/int/result-owner.md §6 (REPL row negatives) — a bare-symbol
    // candidate listing and a display-only polymorphic value fabricate no
    // ownership and release nothing.
    #[test]
    fn non_runtime_turns_release_nothing() {
        let _ = take_events();
        let mut display_only = EvalResult::Candidates {
            symbols: vec![FQSymbol {
                module: ModuleFullPath::from("user"),
                symbol: cranelisp_types::Symbol::from("f"),
            }],
            warnings: Vec::new(),
        };
        display_only.release_program_result();
        let mut display_value = EvalResult::DisplayValue {
            ty: Type::Var(0),
            form: Sexp::Bracket(Vec::new(), cranelisp_types::Span::SYNTHETIC),
            warnings: Vec::new(),
        };
        display_value.release_program_result();
        assert_eq!(display_only.value(), 0, "a lookup turn carries no value");
        assert_eq!(
            display_value.value(),
            0,
            "display syntax is not a runtime word"
        );
        assert_eq!(display_value.ty(), Some(&Type::Var(0)));
        assert!(
            take_events().is_empty(),
            "non-runtime result variants must never invoke result glue"
        );
    }

    // spec: design/int/result-owner.md §4.2 — a scalar REPL result stays
    // call-free: nothing is armed, so the turn's release is a typed no-op.
    #[test]
    fn scalar_val_turn_is_release_free() {
        let _ = take_events();
        let mut val = EvalResult::Val {
            result: OwnedProgramResult::inert(9, Type::Int),
            warnings: Vec::new(),
        };
        assert_eq!(val.value(), 9);
        val.release_program_result();
        assert!(take_events().is_empty());
    }
}

// ---------------------------------------------------------------------------
// Slash command types (pipeline-v4.md §6.1)
// ---------------------------------------------------------------------------

/// Check if parentheses are balanced in input (for multi-line continuation).
/// Exposed as `parens_balanced_pub` for use by the REPL loop in main.rs.
pub fn parens_balanced_pub(input: &str) -> bool {
    parens_balanced(input)
}

pub(crate) fn parens_balanced(input: &str) -> bool {
    let mut depth: i32 = 0;
    let mut in_string = false;
    let mut in_comment = false;
    let mut prev_char = '\0';

    for ch in input.chars() {
        if in_comment {
            if ch == '\n' {
                in_comment = false;
            }
            prev_char = ch;
            continue;
        }
        if in_string {
            if ch == '"' && prev_char != '\\' {
                in_string = false;
            }
            prev_char = ch;
            continue;
        }
        match ch {
            ';' => in_comment = true,
            '"' => in_string = true,
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            _ => {}
        }
        prev_char = ch;
    }
    depth <= 0
}

// ---------------------------------------------------------------------------
// Target data model types (session-restructure.md)
// ---------------------------------------------------------------------------

/// TARGET STATE: per-module typecheck product. Replaces TC-internal storage.
/// Populated by typecheck or deserialized from .meta.json on cache hit.
/// Permanent for session lifetime. See session-restructure.md.
///
/// Sprint 56 Wave 0 (§9.8 G7 pull-forward): the per-module GOT table moved
/// onto `SymbolTable.got`. Readers who previously read `tp.got` now read
/// `symbol_tables[m].got` directly. The `got` field is deleted from this
/// struct. Sprint 56 Wave 2 retired `SessionCompilationEnv` entirely — the
/// only survivors on this struct are `file_path` (used by `/source`) and
/// `source_text` (used for sexp-span slicing in introspection).
pub struct TypecheckProduct {
    pub file_path: Option<PathBuf>,
    /// Module source text, retained in --repl mode for /source introspection.
    /// Sexp spans index into this string. None for cache-hit modules and batch mode.
    pub source_text: Option<String>,
    /// The 0611 carrier — return-poly dispatch sites still UNRESOLVED at
    /// finalize for THIS module (`design/typecheck/return-poly-dispatch-signal.md`;
    /// carrier (A), `design/arch/bounded-contexts.md` §2). EMPTY for every valid
    /// module. `src/exe.rs::validate_main` reads it for the entry module (the
    /// `--run`/`--link` leg of class (b), Principle 19): a `(defn main [] (Pure
    /// (zed)))` whose IO payload never resolved dies with the §3.11 ambiguity
    /// instead of leaking `main has no GOT slot`. Written at the cluster commit
    /// seam (`worker::process_cluster_with_staging`), overwritten per re-check.
    pub unresolved_dispatch: Vec<cranelisp_typecheck::UnresolvedDispatchSite>,
}

// Sprint 58 Wave 3b (Decision 35): the `KeptJit` wrapper struct (Sprint 57
// Wave 2 G6) was deleted along with the `kept_jits` retention pool it served.
// Its `Send + Sync` rationale lives on at `src/code.rs` for the `Code` enum
// that subsumed its role (per-entry `Arc<Jit>` retention on `ModuleEntry::Def
// .code`).

/// REPL-only per-symbol introspection data.
/// Not populated during batch. See session-restructure.md.
#[derive(Debug, Clone, Default)]
pub struct Introspection {
    pub source: Option<String>,
    pub sexp: Option<Sexp>,
    pub expanded: Option<Sexp>,
    pub ast: Option<cranelisp_types::Defn>,
    pub clif_ir: Option<String>,
    pub code_size: Option<usize>,
}

/// Why a module stands failed (`design/int/repl-lifecycle.md` §1.3.1). Each
/// cause names its own remedy in the session-lock refusal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum FailureCause {
    /// The saved source did not compile: any failure other than a refused type.
    FailedSource,
    /// The reload was refused because it changes this live type's structure,
    /// which only a restart can establish (`repl/spec/14-file-watching.md` §14.8).
    RestartRequired(cranelisp_types::FQTypeName),
}

/// A module standing failed: the file whose save the session awaits, and why.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FailedModule {
    pub(crate) file: PathBuf,
    pub(crate) cause: FailureCause,
}

/// How notifications and the session-lock refusal name `module`'s `file`:
/// its bare file name (`design/int/repl-lifecycle.md` §1.4).
pub(crate) fn file_display_name<'a>(
    file: &'a std::path::Path,
    module: &'a ModuleFullPath,
) -> &'a str {
    file.file_name()
        .and_then(|name| name.to_str())
        .unwrap_or_else(|| module.as_ref())
}

/// The outcome of a failed REPL startup's recovery
/// (`design/int/repl-lifecycle.md` §1.3.1, Startup).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StartupRecovery {
    pub(crate) report: Option<String>,
    pub(crate) entry_compiled: bool,
}

impl StartupRecovery {
    /// One notification per module standing failed, to print before the
    /// banner; `None` when no module stands failed.
    pub fn report(&self) -> Option<&str> {
        self.report.as_deref()
    }
}

// ---------------------------------------------------------------------------
// Sprint 67 W3 — Facade-prescribed introspection record types
// (FIXME 0176 partial close; `facades/int.md` §"Introspection records")
// ---------------------------------------------------------------------------

/// Symbol category for facade-level introspection. A coarser classification
/// than `ModuleEntry` itself — used by `list_user_definitions` and the
/// `/list` / `/exports` commands to bucket symbols for REPL display.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolCategory {
    Module,
    Macro,
    Trait,
    Type,
    Fn,
    SpecialForm,
    Constructor,
}

/// Brief symbol record — name + category + optional scheme + optional doc.
/// Returned by `CompilerSession::list_user_definitions()`.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub struct SymbolInfo {
    pub name: cranelisp_types::Symbol,
    pub category: SymbolCategory,
    pub scheme: Option<cranelisp_types::Scheme>,
    pub docstring: Option<String>,
}

/// Resolve the effective priority-worker count from a `SessionSettings`
/// request. `0` → auto-detect (`available_parallelism()-1`, clamped to
/// `[1, 8]`); any non-zero value is clamped to `[1, 8]`. Per
/// `persistent-workers.md` §5.1.
pub(crate) fn resolve_priority_worker_count(requested: usize) -> usize {
    if requested == 0 {
        std::thread::available_parallelism()
            .map(|n| n.get().saturating_sub(1))
            .unwrap_or(1)
            .clamp(1, 8)
    } else {
        requested.clamp(1, 8)
    }
}

/// The outcome of `CompilerSession::introduce_module` (FIXME 0192 Residual
/// Task 2 — 4-branch lifecycle).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleIntroductionOutcome {
    /// The module was already present; no change.
    AlreadyPresent,
    /// The cached metadata + `.o` was decoded and installed atomically.
    CachedLoad,
    /// No cache entry but a source file is registered; caller should
    /// schedule compilation (the orchestrator does not invoke the scheduler).
    SourceLoad,
    /// Neither cache nor source — an empty symbol table was created.
    Blank,
}

/// Deduplicate platform names by identity, preserving first-seen order.
///
/// `SharedState::kept_dlls` carries one `LoadedPlatform` per *processed*
/// `(platform <P>)` form. Because the S78 cluster orchestration re-processes
/// the entry module's forms on every retry-from-top dependency drive, a
/// multi-module `(platform <P>)` program enumerates the SAME platform once per
/// retry. The backend startup-stub emitter trusts its input is already deduped
/// (it `define_data`s one `__cranelisp_expected_hash_<P>` symbol per entry), so
/// the enumeration MUST be deduped by platform name before it reaches the
/// backend — otherwise the duplicate entries collide on the same symbol
/// ("Duplicate definition of identifier", DEF-4). Order is preserved so the
/// manifest-index ↔ rlib ↔ layout-check correspondence stays stable.
pub(crate) fn dedup_platform_names_preserving_order<'a>(
    names: impl Iterator<Item = &'a str>,
) -> Vec<String> {
    let mut seen = std::collections::HashSet::new();
    let mut out = Vec::new();
    for name in names {
        if seen.insert(name) {
            out.push(name.to_string());
        }
    }
    out
}

/// Check if input is a comment-only line.
pub(crate) fn is_comment_only(input: &str) -> bool {
    input.lines().all(|line| {
        let trimmed = line.trim();
        trimmed.is_empty() || trimmed.starts_with(';')
    })
}

pub(crate) fn intrinsic_type_from_name(name: &str) -> Option<Type> {
    match name {
        "Int" => Some(Type::Int),
        "Bool" => Some(Type::Bool),
        "Float" => Some(Type::Float),
        "String" => Some(Type::String),
        _ => None,
    }
}
