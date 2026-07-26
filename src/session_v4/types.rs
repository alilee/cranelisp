// session_v4::types — data-transfer + pure-helper layer (S87 §2.1).
//
// Every value type the binary surface passes around (settings, results,
// introspection DTOs, symbol-display DTOs, the run-mode enum) plus the leaf
// pure functions (`parens_balanced`, the dedup/extract/comment/type helpers,
// the worker-count clamp). Zero session-state dependency — all are `&self`-free
// or operate on borrowed args. Moved verbatim from `session_v4.rs` (S87 §2.1).

use std::path::PathBuf;

use cranelisp_types::{CodegenBehaviour, FQSymbol, Sexp, Type, Warning};

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
    /// no introspection; layout-hash drift REFUSES.
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
/// Either a definition (which introduced a symbol) or a value (which
/// was computed). Both carry zero or more warnings.
pub enum EvalResult {
    /// A definition was processed (defn, deftype, deftrait, impl, defmacro)
    /// — or a bare symbol was introspected (a DISPLAY-ONLY `Def`, marked by
    /// `defined: false`).
    Def {
        symbol: FQSymbol,
        ty: Type,
        warnings: Vec<Warning>,
        /// `true` iff this turn genuinely (re)defined the symbol. `false`
        /// for display-only results (bare-symbol lookup / introspection —
        /// `check_bare_symbol_introspection`). Matrix E recording rule
        /// (FIXME 0486, design/int/s102-defect-wave.md §7.3): only a genuine
        /// definition turn may write the turn's text to the symbol's
        /// introspection `source` — a bare lookup MUST NOT touch the record
        /// (`/info`/`/source` render what introspection hands them).
        defined: bool,
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
    /// An expression TRAPPED at runtime — a `(runtime_panic …)`-raised error
    /// (a broken symbol's trap stub, an exhaustiveness failure, an empty
    /// `(select [])`, …). Distinct from a compiler error (`Err(CranelispError)`)
    /// so the printer can render it as the bare `runtime error: {message}`
    /// §18.5 line — no `Error: ` / `codegen error at 0..0:` wrapper chain
    /// (`repl/spec.md` §18.5; `pipeline::ExprOutcome::Trap` is the source).
    /// `message` is the §18.5 payload WITHOUT the `runtime error: ` category
    /// prefix (`format_eval_result_body` adds it).
    RuntimeError {
        message: String,
        warnings: Vec<Warning>,
    },
}

impl EvalResult {
    pub fn warnings(&self) -> &[Warning] {
        match self {
            EvalResult::Def { warnings, .. } => warnings,
            EvalResult::Val { warnings, .. } => warnings,
            EvalResult::RuntimeError { warnings, .. } => warnings,
        }
    }

    pub fn warnings_mut(&mut self) -> &mut Vec<Warning> {
        match self {
            EvalResult::Def { warnings, .. } => warnings,
            EvalResult::Val { warnings, .. } => warnings,
            EvalResult::RuntimeError { warnings, .. } => warnings,
        }
    }

    /// The raw i64 value, borrowed from the result owner for observation.
    /// Returns 0 for `Def` and `RuntimeError` (a trapped expression produced
    /// no value). Reading this is a READ, never a transfer — only
    /// [`Self::release_program_result`] finalizes the word.
    pub fn value(&self) -> i64 {
        match self {
            EvalResult::Val { result, .. } => result.observed_value(),
            EvalResult::Def { .. } | EvalResult::RuntimeError { .. } => 0,
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

    /// The inferred type. A trapped expression has no value type; `Int` is the
    /// inert placeholder (nothing reads it — the printer renders the message).
    pub fn ty(&self) -> &Type {
        static TRAP_TY: Type = Type::Int;
        match self {
            EvalResult::Val { result, .. } => result.ty(),
            EvalResult::Def { ty, .. } => ty,
            EvalResult::RuntimeError { .. } => &TRAP_TY,
        }
    }

    /// Whether this turn GENUINELY (re)defined a symbol — the regeneration
    /// trigger (repl/spec.md §15.1: regeneration fires on successful
    /// DEFINITIONS only). A display-only `Def` (bare-symbol lookup,
    /// `defined: false`) is NOT a defining turn: regenerating on it rewrote
    /// the backing file on pure lookups (S102 W5 review F6 — with a
    /// hand-authored adopted `user.cl` that was a data-loss surface, not a
    /// harmless no-op). Replaces the shape-only `is_def()` so no caller can
    /// key regen on the variant alone.
    pub fn is_defining(&self) -> bool {
        matches!(self, EvalResult::Def { defined: true, .. })
    }
}

#[cfg(test)]
mod eval_result_tests {
    use super::*;
    use cranelisp_types::ModuleFullPath;

    // spec: repl/spec.md §15.1 — regen triggers on successful definitions
    // only; a display-only bare-lookup Def MUST NOT trigger regen (F6 cell:
    // regen-silence on bare lookup, pinned at the predicate seam both regen
    // sites — main.rs and agent/pull.rs — gate on).
    #[test]
    fn is_defining_true_for_genuine_def_false_for_display_only_and_val() {
        let fq = FQSymbol {
            module: ModuleFullPath::from("user"),
            symbol: cranelisp_types::Symbol::from("f"),
        };
        let genuine = EvalResult::Def {
            symbol: fq.clone(),
            ty: Type::Int,
            warnings: Vec::new(),
            defined: true,
        };
        let display_only = EvalResult::Def {
            symbol: fq,
            ty: Type::Int,
            warnings: Vec::new(),
            defined: false,
        };
        let val = EvalResult::Val {
            result: crate::result_owner::OwnedProgramResult::inert(1, Type::Int),
            warnings: Vec::new(),
        };
        assert!(genuine.is_defining());
        assert!(
            !display_only.is_defining(),
            "bare lookup must not trigger regen"
        );
        assert!(!val.is_defining());
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
        assert_eq!(val.ty(), &Type::String, "type reads through the owner too");
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

    // spec: design/int/result-owner.md §6 (REPL row negatives) — a
    // display-only `Def` (bare-symbol lookup) and a runtime trap fabricate no
    // ownership and release nothing.
    #[test]
    fn def_and_trap_turns_release_nothing() {
        let _ = take_events();
        let mut display_only = EvalResult::Def {
            symbol: FQSymbol {
                module: ModuleFullPath::from("user"),
                symbol: cranelisp_types::Symbol::from("f"),
            },
            ty: Type::Int,
            warnings: Vec::new(),
            defined: false,
        };
        display_only.release_program_result();
        let mut trap = EvalResult::RuntimeError {
            message: "boom".to_string(),
            warnings: Vec::new(),
        };
        trap.release_program_result();
        assert_eq!(display_only.value(), 0, "a Def turn carries no value");
        assert_eq!(trap.value(), 0, "a trapped turn produced no value");
        assert!(
            take_events().is_empty(),
            "neither a display-only Def nor a trap may invoke result glue"
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

/// One backing-file form that failed the degraded form-by-form startup load
/// (`repl/spec.md` §18.8 restart floor; FIXME 0489,
/// `design/int/s102-defect-wave.md` §5.2). Retained on
/// `CompilerSession.failed_forms` so that:
///
///  (a) the startup report can NAME the broken symbol (§18.8's naming MUST —
///      unachievable from the raw batch-cluster error, it falls out of the
///      form grain);
///  (b) `regenerate_backing_file` re-emits the verbatim authored text until
///      the symbol is repaired or the user removes it externally — ordinary
///      regen rebuilds the file from the live table, which the failed forms
///      never entered, so a regen that ignored them would silently DROP the
///      broken definition from the user's file (the §18.8 silent-drop MUST
///      NOT; the §15.4.7 authorship invariant applied to forms that never
///      compiled: authored text is the authority, compile success is not a
///      persistence gate);
///  (c) the §14.4 expression gate knows when the module is repaired (the set
///      empties → the module leaves `error_modules`).
#[derive(Debug, Clone)]
pub(crate) struct FailedForm {
    /// The defining form's name when the form is a defining special form
    /// (`defn`/`defn-`/`defmacro`/`defmacro-`/`deftype`/`deftrait`); `None`
    /// for structural / expression / unparseable forms (those clear only via
    /// an external file fix).
    pub symbol: Option<cranelisp_types::Symbol>,
    /// First line of the load error (report display).
    pub error: String,
    /// Verbatim source text of the form (regen re-emission).
    pub text: String,
}

// ---------------------------------------------------------------------------
// Sprint 67 W3 — Facade-prescribed introspection record types
// (FIXME 0176 partial close; `facades/int.md` §"Introspection records")
// ---------------------------------------------------------------------------

/// Symbol category for facade-level introspection. A coarser classification
/// than `ModuleEntry` itself — used by `describe_symbol` /
/// `list_user_definitions` to bucket symbols for REPL display.
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

/// Full symbol description — `SymbolInfo` plus source text + FQ symbol.
/// Returned by `CompilerSession::describe_symbol(name)`.
///
/// The `related` field carries cross-reference FQSymbols (defn, impl, match
/// arms, etc.) per `facades/int.md` L403 + `repl/spec.md` §3.6's
/// related-symbol comment lines. Populated as an empty Vec at first wiring
/// (Sprint 67 Wave 4) — full population is tracked by FIXME 0194.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub struct SymbolDescription {
    pub fq: FQSymbol,
    pub category: SymbolCategory,
    pub scheme: Option<cranelisp_types::Scheme>,
    pub docstring: Option<String>,
    pub source: Option<String>,
    pub related: Vec<FQSymbol>,
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

pub(crate) fn extract_def_name_from_sexp(sexp: &Sexp) -> Option<String> {
    if let Sexp::List(items, _) = sexp
        && items.len() >= 2
        && let Sexp::Symbol(head, _) = &items[0]
    {
        match head.as_str() {
            "defmacro" => {
                if let Sexp::Symbol(name, _) = &items[1] {
                    return Some(name.to_string());
                }
            }
            "import" | "platform" | "mod" => {
                // These don't define a named symbol in the usual sense.
                return None;
            }
            _ => {}
        }
    }
    None
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
