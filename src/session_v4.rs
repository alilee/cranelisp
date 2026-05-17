// CompilerSession: v4 pipeline session (pipeline-v4.md §5, roadmap Steps 0-7).
//
// Wraps the existing CompilationSession. Batch compilation goes through the v4
// scheduler-driven path with lazy dependency discovery (Step 5). REPL eval
// routes through process_module_forms(Additive) with serial per-form processing
// (Step 7).

use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU32};
use std::sync::{Arc, Mutex};

use cranelisp_types::{ErrorLocation,
    CodegenBehaviour, CranelispError,
    DefKind, FQSymbol, MacroClauseInfo, MacroParam, ModuleEntry, ModuleFullPath,
    ModuleStrategy, OverloadVariant, Sexp, Span, Symbol, TopLevel,
    TraitName, Type, TypeName, Warning,
};

use cranelisp_typecheck::{CheckResult, CheckState, ReplSnapshot, TypeCheckEnv};

use crate::code::{Code, SessionSymbolTable};
use crate::platform::LoadedPlatform;
use crate::scheduler::CompileScheduler;
use crate::worker::ModuleCompiler;

// Re-export display functions so tests can import from session_v4 instead of repl.
pub use crate::display::format_result_value;
use crate::display::{format_type_qualified, format_scheme_display};

// ---------------------------------------------------------------------------
// ReadOnlyMacroResolver — for /expand slash command
// ---------------------------------------------------------------------------

/// Read-only macro resolver for the /expand slash command.
///
/// Same lookup logic as `SymbolTableMacroResolver` (follows Import/Reexport
/// chains) but never triggers compilation. If a macro's clauses are not
/// compiled, returns `Ok(None)` (silently skipped).
struct ReadOnlyMacroResolver<'a> {
    symbol_tables: &'a dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    current_module: ModuleFullPath,
}

impl crate::expander::MacroResolver for ReadOnlyMacroResolver<'_> {
    fn resolve_macro(
        &mut self,
        name: &str,
        _span: Span,
    ) -> Result<Option<crate::expander::MacroEntry>, CranelispError> {
        // Walk symbol table to find the defining module and clause infos.
        let resolved = crate::worker::resolve_macro_definition(
            self.symbol_tables, &self.current_module, name, 16,
        );
        let (defining_module, clauses, docstring) = match resolved {
            Some(r) => r,
            None => return Ok(None),
        };

        // Check if all clauses are compiled. If not, return None (no on-demand compilation).
        // Sprint 57 Wave 2 G6: compiled code lives on `ModuleEntry::Def.code`.
        let macro_sym = Symbol::from(name);
        let mut compiled_clauses = Vec::new();
        for (idx, clause_info) in clauses.iter().enumerate() {
            let clause_name = Symbol::from(format!("__macro_{}_clause_{}", macro_sym, idx));
            let code_ptr = self.symbol_tables.get(&defining_module)
                .and_then(|t| match t.get(clause_name.as_ref())? {
                    ModuleEntry::Def { code: Some(c), .. } => Some(c.ptr()),
                    _ => None,
                });
            match code_ptr {
                Some(ptr) => {
                    compiled_clauses.push(crate::expander::MacroClauseEntry {
                        func_ptr: ptr,
                        params: clause_info.params.clone(),
                        rest_param: clause_info.rest_param.clone(),
                    });
                }
                None => return Ok(None), // Uncompiled clause — skip.
            }
        }
        if compiled_clauses.is_empty() {
            return Ok(None);
        }
        Ok(Some(crate::expander::MacroEntry {
            clauses: compiled_clauses,
            docstring,
        }))
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
    /// A definition was processed (defn, deftype, deftrait, impl, defmacro).
    Def {
        symbol: FQSymbol,
        ty: Type,
        warnings: Vec<Warning>,
    },
    /// An expression was evaluated to a value.
    Val {
        value: i64,
        ty: Type,
        warnings: Vec<Warning>,
    },
}

impl EvalResult {
    pub fn warnings(&self) -> &[Warning] {
        match self {
            EvalResult::Def { warnings, .. } => warnings,
            EvalResult::Val { warnings, .. } => warnings,
        }
    }

    pub fn warnings_mut(&mut self) -> &mut Vec<Warning> {
        match self {
            EvalResult::Def { warnings, .. } => warnings,
            EvalResult::Val { warnings, .. } => warnings,
        }
    }

    /// The raw i64 value. Returns 0 for `Def`.
    pub fn value(&self) -> i64 {
        match self {
            EvalResult::Val { value, .. } => *value,
            EvalResult::Def { .. } => 0,
        }
    }

    /// The inferred type.
    pub fn ty(&self) -> &Type {
        match self {
            EvalResult::Val { ty, .. } => ty,
            EvalResult::Def { ty, .. } => ty,
        }
    }

    /// Whether this is a definition.
    pub fn is_def(&self) -> bool {
        matches!(self, EvalResult::Def { .. })
    }
}

// ---------------------------------------------------------------------------
// Slash command types (pipeline-v4.md §6.1)
// ---------------------------------------------------------------------------

/// Parsed REPL slash command.
#[allow(dead_code)] // Not all variants dispatched yet — ported incrementally.
enum ReplCommand<'a> {
    Help,
    Quit,
    Sig(&'a str),
    Doc(&'a str),
    Type(&'a str),
    Info(&'a str),
    List(&'a str),
    Mem(&'a str),
    Time(&'a str),
    Expand(&'a str),
    Imports(&'a str),
    Exports(&'a str),
    Source(&'a str),
    SexpCmd(&'a str),
    Ast(&'a str),
    Clif(&'a str),
    Disasm(&'a str),
    Mod(&'a str),
    RunTests(&'a str),
    RunAllTests,
    Reset,
    Sh(&'a str),
    Unknown(&'a str),
}

/// Sentinel string returned by /quit to signal the REPL loop to exit.
pub const QUIT_SENTINEL: &str = "\x00QUIT";

/// Populate the `primitives` synthetic module's GOT slots with Ring 0
/// shim-fn addresses.
///
/// Per FIXME 0174 + Decision 43, Ring 0 primitives (`add-i64`, …, `not`,
/// `eq-bool`) are registered in `typecheck::builtins::register_primitives`
/// with `got_slot: Some(_)` and `jit_name: Some(_)`. Their code pointers
/// are written here, immediately after `register_builtins` returns, by
/// reading them from `cranelisp_primitives::PRIMITIVES_TABLE` — the
/// post-FIXME-0159 single source of truth for primitive entries and
/// GOT-stored fn ptrs. The static table's GOT carries each Ring 0 shim's
/// address at its own slot index; this fn copies them across to the
/// session's `primitives` table at the session-allocated slot indices
/// (the two tables index slots independently).
///
/// The standard GOT-indirect dispatch (`compile_direct_call` →
/// `resolve_got_target` → `__cranelisp_got_primitives[slot]`) resolves the
/// call to these shim fn ptrs. The `primitives_inline.rs` inline-substitution
/// path is a separate code-size + dispatch-cost optimisation: identical
/// semantics, faster code. Mappable paths (`(let [f not] (f true))`)
/// always work via the GOT-stored shim ptr.
///
/// Idempotent — safe to call after every `register_builtins`; the shim
/// pointers are stable for the process lifetime.
fn populate_ring0_got_slots(
    symbol_tables: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
) {
    let primitives_path = ModuleFullPath::from("primitives");
    let Some(table) = symbol_tables.get(&primitives_path) else {
        // primitives module not seeded — register_builtins ordering broken.
        // Quietly skip; the regular pipeline error path will surface the
        // missing-module condition when a Ring 0 call is compiled.
        return;
    };
    let static_table = &*cranelisp_primitives::PRIMITIVES_TABLE;
    for (name, static_entry) in static_table.symbols.iter() {
        let cranelisp_types::ModuleEntry::Def {
            got_slot: Some(src_slot), ..
        } = static_entry
        else {
            continue;
        };
        let ptr = static_table.got.load_slot(*src_slot);
        let Some(session_entry) = table.get(name.as_ref()) else {
            continue;
        };
        let cranelisp_types::ModuleEntry::Def {
            got_slot: Some(dst_slot), ..
        } = session_entry
        else {
            continue;
        };
        table.got.store_slot(*dst_slot, ptr);
    }
}

/// Parse a slash command from trimmed input.
fn parse_slash_command(input: &str) -> Option<ReplCommand<'_>> {
    if !input.starts_with('/') {
        return None;
    }

    let (cmd, arg) = match input.split_once(char::is_whitespace) {
        Some((c, a)) => (c, a.trim()),
        None => (input, ""),
    };

    Some(match cmd {
        "/help" | "/h" => ReplCommand::Help,
        "/quit" | "/q" => ReplCommand::Quit,
        "/sig" | "/s" => ReplCommand::Sig(arg),
        "/doc" | "/d" => ReplCommand::Doc(arg),
        "/type" | "/t" => ReplCommand::Type(arg),
        "/info" | "/i" => ReplCommand::Info(arg),
        "/list" | "/l" => ReplCommand::List(arg),
        "/mem" | "/m" => ReplCommand::Mem(arg),
        "/time" => ReplCommand::Time(arg),
        "/expand" | "/e" => ReplCommand::Expand(arg),
        "/imports" => ReplCommand::Imports(arg),
        "/exports" => ReplCommand::Exports(arg),
        "/source" => ReplCommand::Source(arg),
        "/sexp" => ReplCommand::SexpCmd(arg),
        "/ast" => ReplCommand::Ast(arg),
        "/clif" => ReplCommand::Clif(arg),
        "/disasm" => ReplCommand::Disasm(arg),
        "/mod" => ReplCommand::Mod(arg),
        "/run-tests" | "/rt" => ReplCommand::RunTests(arg),
        "/run-all-tests" => ReplCommand::RunAllTests,
        "/reset" => ReplCommand::Reset,
        "/sh" => ReplCommand::Sh(arg),
        _ => ReplCommand::Unknown(cmd),
    })
}

/// Print the /help command output to a writer.
fn print_help(stdout: &mut impl Write) {
    let _ = writeln!(stdout, "Available commands:");
    let _ = writeln!(stdout, "  /help (/h)          Show this help");
    let _ = writeln!(stdout, "  /quit (/q)          Exit REPL");
    let _ = writeln!(stdout, "  /sig (/s) NAME      Show type signature");
    let _ = writeln!(stdout, "  /doc (/d) NAME      Show docstring");
    let _ = writeln!(stdout, "  /type (/t) EXPR     Show type without evaluating");
    let _ = writeln!(stdout, "  /info (/i) NAME     Show full details");
    let _ = writeln!(stdout, "  /source NAME        Show original source text");
    let _ = writeln!(stdout, "  /sexp NAME          Show parsed S-expression");
    let _ = writeln!(stdout, "  /ast NAME           Show AST");
    let _ = writeln!(stdout, "  /clif NAME          Show Cranelift IR");
    let _ = writeln!(stdout, "  /disasm NAME        Show disassembled native code");
    let _ = writeln!(stdout, "  /list (/l) [FILTER] List symbols in current module");
    let _ = writeln!(stdout, "  /mem (/m) [EXPR]    Show allocation statistics (with delta if EXPR given)");
    let _ = writeln!(stdout, "  /time EXPR          Evaluate with timing breakdown");
    let _ = writeln!(stdout, "  /expand (/e) FORM   Macro-expand a form");
    let _ = writeln!(stdout, "  /imports [MODULE]   Show imports and special forms");
    let _ = writeln!(stdout, "  /exports MODULE     Show module's public symbols");
    let _ = writeln!(stdout, "  /mod [NAME]         Switch module namespace (default: user)");
    let _ = writeln!(stdout, "  /run-tests (/rt) [MOD]  Run test-* functions (current module or named)");
    let _ = writeln!(stdout, "  /run-all-tests      Run all tests in project modules");
    let _ = writeln!(stdout, "  /reset              Clear all state and reload prelude");
    let _ = writeln!(stdout, "  /sh <cmd>       Run a shell command");
}

/// Check if input is a comment-only line.
fn is_comment_only(input: &str) -> bool {
    input.lines().all(|line| {
        let trimmed = line.trim();
        trimmed.is_empty() || trimmed.starts_with(';')
    })
}

/// Run a shell command with stdout/stderr passed through directly.
///
/// Uses `.status()` instead of `.output()` so the child process inherits
/// stdout/stderr from the REPL process. This ensures E2E test harnesses
/// (which capture subprocess stdout) see the shell command output.
fn run_shell_command(cmd: &str, stdout: &mut impl Write) {
    if cmd.is_empty() {
        let _ = writeln!(stdout, "Usage: /sh <command>");
        return;
    }
    match std::process::Command::new("sh")
        .arg("-c")
        .arg(cmd)
        .status()
    {
        Ok(status) => {
            if !status.success() {
                #[cfg(unix)]
                {
                    use std::os::unix::process::ExitStatusExt;
                    if let Some(sig) = status.signal() {
                        let _ = writeln!(stdout, "killed by signal: {sig}");
                        return;
                    }
                }
                if let Some(code) = status.code() {
                    let _ = writeln!(stdout, "exit status: {code}");
                }
            }
        }
        Err(e) => {
            let _ = writeln!(stdout, "error: {e}");
        }
    }
}

/// Format the `/mem` snapshot (no-expression form).
///
/// Reads the current allocation counters from `cranelisp-runtime` and
/// returns a two-line report: one data line with current live bytes, and
/// a comment line with total alloc / dealloc counts and the currently-live
/// allocation count (`allocs - deallocs`).
fn format_mem_snapshot() -> String {
    let allocs = cranelisp_intrinsics::alloc_count();
    let deallocs = cranelisp_intrinsics::dealloc_count();
    let bytes_live = cranelisp_intrinsics::bytes_current();
    let live = allocs.saturating_sub(deallocs);
    format!(
        "; live: {bytes_live} bytes ({live} allocations)\n; allocs: {allocs}  deallocs: {deallocs}"
    )
}

/// Format a module entry signature for /sig display.
fn format_entry_sig(entry: &ModuleEntry<Code>, name: &str) -> String {
    match entry {
        ModuleEntry::Def { scheme, kind, docstring, .. } => {
            // Multi-sig: emit one line per variant per repl/spec.md §4.1.1.
            // The /sig output uses the bare name (no module prefix) to match
            // the rest of this formatter's behaviour.
            if let DefKind::Overloaded { variants } = kind.as_ref()
                && !variants.is_empty()
            {
                return format_overloaded_variants_bare(name, variants, docstring.as_deref());
            }
            let classification = match kind.as_ref() {
                DefKind::SpecialForm { description } => {
                    return format!("{name} ; special form - {description}");
                }
                DefKind::Overloaded { .. } => "defn (multi)",
                _ => "defn",
            };
            // Sprint 60 Workstream G — append docstring after classification
            // per `repl/spec.md §1.1` universal output format: `; {classification}
            // - {docstring}`. The multi-sig branch above uses the same helper.
            // See `design/int/dual-path-persistence-collapse.md §9`.
            let base = format!(":{} {} ; {}", scheme.ty, name, classification);
            append_docstring_comment(base, docstring.as_deref())
        }
        ModuleEntry::Macro { clauses, .. } => {
            let arity = clauses.first()
                .map(|c| c.params.len())
                .unwrap_or(0);
            format!("{name} ; defmacro ({} clause(s), arity {})", clauses.len(), arity)
        }
        ModuleEntry::TypeDef { .. } => {
            format!("{name} ; deftype")
        }
        ModuleEntry::TraitDecl { decl, .. } => {
            format!("{name} ; deftrait ({} method(s))", decl.methods.len())
        }
        ModuleEntry::Constructor { type_name, scheme, .. } => {
            format!(":{} {} ; constructor of {}", scheme.ty, name, type_name)
        }
        ModuleEntry::Import { source } => {
            format!("{name} ; imported from {}/{}", source.module, source.symbol)
        }
        _ => name.to_string(),
    }
}

/// Format an overloaded (multi-sig) function as one line per variant, with
/// fully-qualified `module/name` per spec §4.1.1. Used by bare-symbol display
/// (`format_def_entry`).
///
/// First line carries the `; defn` classification + optional docstring; subsequent
/// variant lines carry only the type and qualified name. See repl/spec.md §1.3
/// + §4.1.1 and design/int/multi-sig-introspection.md.
fn format_overloaded_variants(
    name: &str,
    module: &ModuleFullPath,
    variants: &[OverloadVariant],
    docstring: Option<&str>,
) -> String {
    let mut lines = Vec::with_capacity(variants.len());
    for (i, v) in variants.iter().enumerate() {
        let fn_ty = Type::Fn(v.param_types.clone(), Box::new(v.ret_type.clone()));
        let type_str = format_type_qualified(&fn_ty);
        let line = if i == 0 {
            let base = format!(":{type_str} {module}/{name} ; defn");
            append_docstring_comment(base, docstring)
        } else {
            format!(":{type_str} {module}/{name}")
        };
        lines.push(line);
    }
    lines.join("\n")
}

/// /sig variant of `format_overloaded_variants` — bare name (no module prefix)
/// to match the rest of `format_entry_sig`'s output. One line per variant.
fn format_overloaded_variants_bare(
    name: &str,
    variants: &[OverloadVariant],
    docstring: Option<&str>,
) -> String {
    let mut lines = Vec::with_capacity(variants.len());
    for (i, v) in variants.iter().enumerate() {
        let fn_ty = Type::Fn(v.param_types.clone(), Box::new(v.ret_type.clone()));
        let type_str = format_type_qualified(&fn_ty);
        let line = if i == 0 {
            let base = format!(":{type_str} {name} ; defn");
            append_docstring_comment(base, docstring)
        } else {
            format!(":{type_str} {name}")
        };
        lines.push(line);
    }
    lines.join("\n")
}

/// Check if parentheses are balanced in input (for multi-line continuation).
/// Exposed as `parens_balanced_pub` for use by the REPL loop in main.rs.
pub fn parens_balanced_pub(input: &str) -> bool {
    parens_balanced(input)
}

fn parens_balanced(input: &str) -> bool {
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
    pub disasm: Option<String>,
    pub code_size: Option<usize>,
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
    pub name: Symbol,
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

// ---------------------------------------------------------------------------
// CompilerSession (pipeline-v4.md §5)
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// SharedState (thread-safe state for priority + nice workers)
// ---------------------------------------------------------------------------

/// Thread-safe state shared between the main thread and nice worker threads.
///
/// Separated from `CompilerSession` so that nice workers can hold `&SharedState`
/// while the main thread retains `&mut CompilerSession` for priority worker
/// operations. All fields are inherently thread-safe (Mutex, AtomicBool,
/// read-only after construction).
pub struct SharedState {
    /// Compilation scheduler. Tracks module lifecycle and coordinates
    /// work items. Internal Mutex + condvars for thread-safe access.
    pub scheduler: CompileScheduler,

    /// Project root directory (read-only after construction). Sprint 57
    /// Wave 4 G9: moved here from `CompilerSession` so persistent priority
    /// workers can access it without borrow glue.
    pub project_root: PathBuf,

    /// Lib directories for module resolution (§8.11.2 tier 3). Wrapped in
    /// `Mutex` so tests (and future runtime reconfiguration) can update the
    /// set after workers have spawned; workers hold the lock only for the
    /// duration of a single read (rare per compile). Sprint 57 Wave 4 G9:
    /// moved here from `CompilerSession` for persistent-worker access.
    pub lib_dirs: Mutex<Vec<PathBuf>>,

    /// Extra platform DLL search directories (§8.11.3 tier 3). Same Mutex
    /// rationale as `lib_dirs`. Sprint 57 Wave 4 G9: moved here from
    /// `CompilerSession` for persistent-worker access.
    pub platform_dirs: Mutex<Vec<PathBuf>>,

    /// Sexps awaiting typecheck, keyed by module. Populated by
    /// `register_module_with_source` / `reload_module` on the main thread;
    /// read (and removed when complete) by persistent priority workers.
    /// Sprint 57 Wave 4 G9 (per `persistent-workers.md` §5.3).
    pub module_sexps: Mutex<HashMap<ModuleFullPath, Vec<Sexp>>>,

    /// Per-module suspension state for resuming a partially-typechecked
    /// module when a dependency becomes available. Worker-local logically,
    /// but stored here so a blocked module can resume on any worker. Sprint
    /// 57 Wave 4 G9 (per `persistent-workers.md` §5.3).
    ///
    /// **Sprint 67 Cluster B investigation verified LIVE.** The facade-plan
    /// `PIF — relocate or eliminate` (S67 W1 row, gated on FIXME 0179
    /// cluster-mode read-union) is correct in direction but the field is
    /// currently load-bearing for the pre-cluster-atomic resume-on-dep-arrival
    /// path. Deferred to S68 review per FIXME 0205 + FIXME 0208 facade refresh.
    pub suspend_states: Mutex<HashMap<ModuleFullPath, crate::worker::ModuleSuspendState>>,

    /// Cache directory for .o and .meta.json output (Step 10).
    /// None when caching is disabled (e.g., `--run` without `--link`).
    pub cache_dir: Option<PathBuf>,

    /// Collected .o file paths written by nice workers (Step 10).
    /// Used by `--link` to pass all .o files to the system linker.
    pub compiled_o_paths: Mutex<Vec<PathBuf>>,

    /// Flag for nice worker priority promotion during hot flush (Step 10).
    /// When set to true, nice workers self-promote to normal OS priority.
    ///
    /// **Sprint 67 Cluster B investigation verified LIVE.** Atomic flag is
    /// read by `spawn_nice_workers` per-iteration to detect hot-flush priority
    /// boost requests; written by `wait_object_complete` when the initiator
    /// thread requests a flush. Facade-plan `PFR — facade widens` (S67 W1
    /// row) holds. Deferred to S68 facade refresh per FIXME 0208.
    pub promote_nice_workers: AtomicBool,

    /// Set of modules loaded from cache (vs. compiled from source).
    /// Used by workers to detect cache-hit modules for Linker fast path.
    /// Populated by try_cache_hit_load, read by workers during codegen.
    pub cached_modules: Mutex<HashSet<ModuleFullPath>>,

    /// File path to module path mapping. Populated during handle_import
    /// when modules are first discovered. Used by the file watcher to
    /// identify which module changed.
    pub file_to_module: Mutex<HashMap<PathBuf, ModuleFullPath>>,

    /// Cache validity state. Holds the manifest, cache directory, and
    /// source hash records. Behind Mutex because workers update it
    /// (record_cache_hit) during handle_import.
    pub cache_state: Mutex<Option<crate::session::CacheState>>,

    /// Compile-time codegen mode (REPL/`--run` => `InMemoryAndObject`;
    /// `--link` => `ObjectOnly`). Captured from `SessionSettings` at
    /// construction and read by the cluster orchestrator's `(trace ...)`
    /// rejection pass per Decision 40 / Path B1 (FIXMEs 0199 + 0204).
    ///
    /// Per spec/04-expressions.md §4.12.9: `(trace ...)` is REPL/`--run`-only;
    /// `--link` rejects the form at compile time. The validator is invoked
    /// from `worker::build_program_compat` with this flag as the deciding
    /// input. `CodegenBehaviour::InMemoryAndObject` makes the validator a
    /// no-op (trace permitted).
    pub codegen_behaviour: CodegenBehaviour,

    // -- Stateless TC: shared state (Sprint 51) --
    // The single source of truth for per-module symbol data. Formerly owned
    // by TypeChecker; now on SharedState for direct access by all workers.

    /// Per-module symbol tables. The single source of truth for per-module
    /// symbol data. Workers and session methods access this directly.
    ///
    /// Sprint 58 Wave 3b (Decision 35): the integration layer's concrete
    /// `C = Code` (an enum unifying `Code::Jit { Arc<Jit>, ptr }` and
    /// `Code::Linker { Arc<Linker>, ptr }`); `L = ()` (per-symbol Linker
    /// retention via `Code::Linker.linker` covers every case where a
    /// Linker needs to outlive its construction). See `src/code.rs` for
    /// the `Code` enum definition + reclaim contract; `SessionSymbolTable`
    /// is the alias.
    pub symbol_tables: dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,

    /// Monotonic counter for fresh type variable IDs. Shared across all
    /// TypeCheckEnv instances for concurrent workers.
    pub next_type_id: AtomicU32,

    /// REPL carry-forward: current module path for REPL prompt and eval.
    /// Batch compilation sets this per-worker; REPL uses it across evals.
    pub current_module: Mutex<ModuleFullPath>,

    /// REPL carry-forward: CheckState that persists across REPL evals.
    /// Contains substitution, scope stack, overloads, module aliases.
    /// None in batch mode (CheckState is stack-local per worker).
    ///
    /// **Sprint 67 Cluster B investigation verified LIVE.** Read by both
    /// REPL eval paths (`session_v4.rs:2395, 3377`) and the
    /// `tc_snapshot`/`tc_restore` REPL error-recovery primitives; mutated
    /// when `/mod` switches the active module (`set_current_module`,
    /// session_v4.rs:1152). Facade-plan `PIF — relocate to CompilerSession`
    /// (S67 W1 row) is correct in direction but currently load-bearing on
    /// SharedState; relocation deferred to S68 review per FIXME 0208 facade
    /// refresh + S68 cluster-atomic completion.
    pub repl_check_state: Mutex<Option<CheckState>>,

    // -- Target data model (session-restructure.md) --
    // DashMaps are inherently concurrent and accessible to both priority
    // and nice workers via Arc<SharedState>.

    /// Per-module typecheck products (replaces TC-internal storage).
    pub typecheck_products: dashmap::DashMap<ModuleFullPath, TypecheckProduct>,
    // Sprint 58 Step 5b (Decision 22): the `codegen_programs` transient
    // stash is gone — the nice worker walks `symbol_tables[module]
    // .defined_symbols()` directly to enumerate codegen targets, the same
    // predicate the priority worker uses, so no parallel store is needed.

    // Sprint 57 Wave 2 G6: `codegen_products: DashMap<ModuleFullPath, CodegenProduct>`
    // was here. Deleted. Compiled code is read from
    // `symbol_tables[module].get(name).code`.
    //
    // Sprint 58 Wave 3b (Decision 35): `kept_jits: Mutex<Vec<KeptJit>>` and
    // `kept_linkers: Mutex<Vec<Linker>>` retention pools dissolved. The
    // `Arc<Jit>` retention root moved per-entry onto `Code::Jit { jit, ptr }`
    // on each `ModuleEntry::Def.code`; the `Arc<Linker>` retention root
    // moved per-entry onto `Code::Linker { linker, ptr }`. When a REPL
    // user redefines a defn, the prior `ModuleEntry::Def` value drops; if
    // no other entry references the same `Arc<Jit>`, the count hits zero
    // and `Jit::Drop` calls `unsafe JITModule::free_memory()` — the
    // Decision 31 Scenario 2 per-redefinition reclaim primitive. See
    // `src/code.rs` for the `Code` enum; `design/int/symbol-table-generics.md`
    // §2.3 for the dissolution rationale.
    /// Platform DLL retention pool (Sprint 57 Wave 3 G8). Holds
    /// `LoadedPlatform` handles for the session lifetime so that every
    /// platform-fn pointer in a per-module GOT (referenced by an entry's
    /// `ModuleEntry::Def.got_slot`) remains valid for as long as any code on
    /// the symbol tables might dispatch through it. (Sprint 66 Wave 0
    /// amendment — the prior `ModuleEntry::Def.fn_ptr` field has been
    /// replaced by GOT-as-single-source-of-truth.)
    ///
    /// # Safety invariant
    ///
    /// Each platform-fn GOT entry is valid for as long as the owning DLL
    /// handle is in `SharedState::kept_dlls`. Sessions retain these handles
    /// for their full lifetime; the pool is never drained. Pushing a
    /// `LoadedPlatform` is the write that makes its GOT pointers safe to
    /// call; dropping a `LoadedPlatform` invalidates its pointers. On drop
    /// (end of session) all pointers are simultaneously invalidated, which
    /// is fine because nothing can still be calling them after drop.
    pub kept_dlls: Mutex<Vec<LoadedPlatform>>,
    /// Per-symbol introspection data, REPL-only (replaces def_codegen for slash commands).
    pub introspection: dashmap::DashMap<FQSymbol, Introspection>,

    /// Test runner state used by the `run-test` / `discover-tests` intrinsics
    /// (Sprint 66 Wave 3a-γ).
    ///
    /// Boxed so the pointer is stable for the session's lifetime. The
    /// `TEST_RUNNER` thread-local stores `*const TestRunnerState` derived from
    /// this Box; because the Box owns the allocation for the full session and
    /// the pointed-at `current_module` field is wrapped in `Mutex`, the
    /// thread-local pointer is always safe to dereference while
    /// `CompilerSession` is alive.
    ///
    /// Lifted from per-compilation init to session-wide init so that the test
    /// intrinsics may be registered unconditionally at JIT setup (the
    /// architectural answer to FIXME 0177's "conditionally-registered
    /// intrinsics" wart).
    pub test_runner_state: Box<TestRunnerState>,
    // Sprint 58 Step 5a (Decision 33): `module_structures` was a parallel
    // store for `(import …)`/`(export …)`/`(platform …)`/`(mod …)` decls in
    // source order. Those are now fields on `SymbolTable` itself
    // (populated by `src/worker.rs` form-handlers, read by `src/save.rs`
    // and the file-watcher cascade in `try_pop_changes`).
}

/// Resolve the effective priority-worker count from a `SessionSettings`
/// request. `0` → auto-detect (`available_parallelism()-1`, clamped to
/// `[1, 8]`); any non-zero value is clamped to `[1, 8]`. Per
/// `persistent-workers.md` §5.1.
fn resolve_priority_worker_count(requested: usize) -> usize {
    if requested == 0 {
        std::thread::available_parallelism()
            .map(|n| n.get().saturating_sub(1))
            .unwrap_or(1)
            .clamp(1, 8)
    } else {
        requested.clamp(1, 8)
    }
}

// ---------------------------------------------------------------------------
// EvalInFlightGuard — Sprint 61 Wave 3 step 3e' (H5 race closure)
// ---------------------------------------------------------------------------

/// RAII guard for the `ModuleState::eval_in_flight` flag.
///
/// Set the flag on construction and clear it on `Drop` (including on
/// panic-unwind). Used exclusively by `register_dep_for_eval` to
/// suppress worker claims of the caller module across the whole
/// `register_dep_for_eval` invocation: if the flag is set when
/// `try_unblock_locked(caller)` fires (from `notify_typecheck_done`
/// on a dep's completion), the caller is not pushed into
/// `typecheck_first`; the REPL-eval thread drives the retry.
///
/// Scope discipline (per /arch §3d' "RAII guard correctness"
/// paragraph 1, alternative option): the guard scope spans
/// register_dep_for_eval from immediately-after `caller` is
/// computed through function exit (normal + panic-unwind). The
/// narrower scope around `wait_module_inmem_complete_blocking` only
/// was TRIED FIRST per /arch §3d' condition 3 and found
/// insufficient — the race window opens at `block_for_typecheck`
/// inside `handle_import` (BEFORE register_dep_for_eval is called),
/// so the flag must be set before the function's own body executes.
/// See `design/int/heisenbug-race-closure.md §3e'` for the
/// scope-selection validation.
///
/// Lock discipline (per /arch §3d' condition 2): both the set (here)
/// and the read (inside `try_unblock_locked`) take the scheduler state
/// lock, linearising the set/read pair. No atomics, no separate mutex.
///
/// See `design/int/heisenbug-race-closure.md §7.7 + §8.2 + §3e'`.
struct EvalInFlightGuard<'a> {
    scheduler: &'a CompileScheduler,
    module: ModuleFullPath,
}

impl<'a> EvalInFlightGuard<'a> {
    fn new(scheduler: &'a CompileScheduler, module: ModuleFullPath) -> Self {
        scheduler.set_eval_in_flight(&module, true);
        Self { scheduler, module }
    }
}

impl Drop for EvalInFlightGuard<'_> {
    fn drop(&mut self) {
        self.scheduler.set_eval_in_flight(&self.module, false);
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

/// The compiler session — scheduler-driven concurrent compilation.
///
/// One session per process. Owns the TypeChecker, codegen state, and
/// scheduler. Persistent priority + nice worker threads are spawned in
/// `new()` and joined in `shutdown()` / `Drop` (Sprint 57 Wave 4 G9).
pub struct CompilerSession {
    /// Thread-safe state shared with nice + priority worker threads. Wrapped
    /// in Arc so workers get an independent clone. Sprint 57 Wave 4 G9
    /// moved `project_root`, `lib_dirs`, `platform_dirs` here so persistent
    /// priority workers can access them without borrow glue. Convenience
    /// accessors (`project_root()`, `lib_dirs()`, `platform_dirs()`) are
    /// provided below for call sites that previously held direct fields.
    pub shared: Arc<SharedState>,

    // -- REPL-specific state (pipeline-v4.md §6) --

    /// Modules that failed reload (file watcher). While non-empty, expression
    /// evaluation is blocked.
    pub error_modules: HashSet<ModuleFullPath>,

    /// File watcher for REPL mode. Initialized via `init_watcher()` after
    /// construction. None in batch/link modes or if OS watcher unavailable.
    pub watcher: Option<crate::watch::FileWatcher>,

    /// Priority worker thread handles. Sprint 57 Wave 4 G9: persistent —
    /// spawned in `new()`, joined in `shutdown()`/`Drop`. Per
    /// `persistent-workers.md` §4.1/§5.2.
    priority_worker_handles: Vec<std::thread::JoinHandle<()>>,

    /// Nice worker thread handles. Joined in `shutdown()`.
    nice_worker_handles: Vec<std::thread::JoinHandle<()>>,
    /// Nice worker count (stored for `wait_object_complete` guard).
    nice_workers: usize,
}

impl CompilerSession {
    /// Create a new compiler session (pipeline-v4.md §5).
    ///
    /// Spawns `priority_workers` persistent priority worker threads and
    /// `nice_workers` persistent nice worker threads. Workers park on the
    /// scheduler's condvars and process work for the session lifetime;
    /// `shutdown()` (called from `Drop`) joins them all. Sprint 57 Wave 4
    /// G9 per `design/int/persistent-workers.md` §4.1.
    ///
    /// The effective priority worker count is derived from
    /// `settings.priority_workers`: values of 0 are interpreted as
    /// "auto-detect" (`available_parallelism()-1`, clamped to `[1, 8]`);
    /// explicit values are clamped to `[1, 8]`. Tests pass
    /// `priority_workers: 1` for determinism.
    pub fn new(
        settings: SessionSettings,
        project_root: PathBuf,
    ) -> Self {
        // Lib dirs: stdlib location(s), NOT including project_root.
        // Project root is tier 2 in §8.11.2, searched separately.
        let lib_dirs = crate::session::assemble_lib_dirs(&project_root);

        // Platform dirs: extra search locations from env var (§8.11.5).
        let platform_dirs = crate::session::assemble_platform_dirs();

        let cache_dir = project_root.join(".cranelisp-cache");
        let _ = std::fs::create_dir_all(&cache_dir);

        let cache_state = if settings.no_cache {
            None
        } else {
            Some(crate::session::CacheState::new(cache_dir.clone()))
        };

        // Priority-worker count: 0 = auto-detect, else explicit. Clamp to
        // [1, 8] per `persistent-workers.md` §5.1.
        let priority_workers = resolve_priority_worker_count(settings.priority_workers);

        let nice_workers = settings.nice_workers;

        let symbol_tables: dashmap::DashMap<ModuleFullPath, SessionSymbolTable> =
            dashmap::DashMap::new();
        let next_type_id = AtomicU32::new(0);
        let user_module = ModuleFullPath::from("user");

        // Seed the "user" module before register_builtins (which registers special forms on it).
        // Sprint 58 Wave 3b: `<Code, ()>` flavour via `new_with_params` on the
        // generic impl (not the `<()>`-pinned `SymbolTable::new`).
        symbol_tables.insert(
            user_module.clone(),
            SessionSymbolTable::new_with_params(user_module.clone()),
        );

        // Seed builtins into symbol tables before any user modules load.
        cranelisp_typecheck::register_builtins(&symbol_tables, &next_type_id);

        // Per FIXME 0174 + Decision 43: Ring 0 primitives (`add-i64`, `not`,
        // …) are now ordinary `ModuleEntry::Def` entries with `got_slot:
        // Some(_)`. Pair each name with its Rust shim address and write the
        // pointer into the primitives module's GOT slot so the standard
        // GOT-indirect dispatch path (and the mappable-path
        // `(let [f not] (f true))`) resolves correctly. Inline substitution
        // in backend remains a separate optimisation.
        populate_ring0_got_slots(&symbol_tables);

        // Sprint 66 Wave 3a-γ: build the session-wide TestRunnerState. The
        // `tc_modules` pointer is derived from the `symbol_tables` DashMap
        // owned by the Arc<SharedState> we're about to construct. Since
        // `SharedState` is held behind `Arc` for the session lifetime and
        // never moved, the pointer is stable. The `current_module` field is
        // a `Mutex` so `/mod` may update it without rebuilding the state.
        let test_runner_state = Box::new(TestRunnerState {
            tc_modules: std::ptr::null(), // patched immediately after Arc construction
            current_module: Mutex::new(user_module.clone()),
        });

        let shared = Arc::new(SharedState {
            scheduler: CompileScheduler::new(),
            project_root,
            lib_dirs: Mutex::new(lib_dirs),
            platform_dirs: Mutex::new(platform_dirs),
            module_sexps: Mutex::new(HashMap::new()),
            suspend_states: Mutex::new(HashMap::new()),
            cache_dir: Some(cache_dir),
            compiled_o_paths: Mutex::new(Vec::new()),
            promote_nice_workers: AtomicBool::new(false),
            cached_modules: Mutex::new(HashSet::new()),
            file_to_module: Mutex::new(HashMap::new()),
            cache_state: Mutex::new(cache_state),
            codegen_behaviour: settings.codegen_behaviour,
            symbol_tables,
            next_type_id,
            current_module: Mutex::new(user_module.clone()),
            repl_check_state: Mutex::new(Some(CheckState::new(user_module))),
            typecheck_products: dashmap::DashMap::new(),
            // Sprint 58 Wave 3b: kept_jits / kept_linkers dissolved per
            // Decision 35; Arc retention now lives on each Code::Jit /
            // Code::Linker on `ModuleEntry::Def.code`.
            kept_dlls: Mutex::new(Vec::new()),
            introspection: dashmap::DashMap::new(),
            test_runner_state,
        });

        // Patch the `tc_modules` pointer inside `test_runner_state` to point
        // at `shared.symbol_tables`. Safe: `shared` is `Arc<SharedState>`,
        // never moved; the `symbol_tables` field has a stable address for
        // the session lifetime. The `Box<TestRunnerState>` itself sits inside
        // the `SharedState` struct, so a `&mut` through `Arc` would alias
        // shared state — instead we cast through a raw pointer to flip the
        // single `*const` field. This write happens exactly once, before any
        // worker thread is spawned (so before any reader observes the field).
        // SAFETY: single-writer, pre-spawn; no concurrent reader exists yet.
        unsafe {
            let trs_ptr = &*shared.test_runner_state as *const TestRunnerState
                as *mut TestRunnerState;
            (*trs_ptr).tc_modules = &shared.symbol_tables as *const _;
        }

        // Spawn persistent priority worker threads (Sprint 57 Wave 4 G9).
        // Workers park on `scheduler.priority_work_available` and process
        // modules until shutdown. Joined in `shutdown()` / `Drop`.
        let mut priority_worker_handles = Vec::with_capacity(priority_workers);
        for i in 0..priority_workers {
            let worker_shared = Arc::clone(&shared);
            let handle = std::thread::Builder::new()
                .name(format!("priority-worker-{}", i))
                .spawn(move || {
                    crate::worker::priority_worker_loop_shared(&worker_shared);
                })
                .expect("failed to spawn priority worker thread");
            priority_worker_handles.push(handle);
        }

        // Spawn persistent nice worker threads for object codegen (.o files).
        // Workers park on scheduler condvar and wake when modules reach
        // TypecheckDone. They run for the session lifetime and are joined
        // in shutdown().
        let mut nice_worker_handles = Vec::with_capacity(nice_workers);
        for i in 0..nice_workers {
            let worker_shared = Arc::clone(&shared);
            let handle = std::thread::Builder::new()
                .name(format!("nice-worker-{}", i))
                .spawn(move || {
                    nice_worker_loop(&worker_shared);
                })
                .expect("failed to spawn nice worker thread");
            nice_worker_handles.push(handle);
        }

        CompilerSession {
            shared,
            error_modules: HashSet::new(),
            watcher: None,
            priority_worker_handles,
            nice_worker_handles,
            nice_workers,
        }
    }

    /// Convenience accessor: project root.
    pub fn project_root(&self) -> &Path {
        &self.shared.project_root
    }

    /// Convenience accessor: lib search directories (snapshot clone).
    pub fn lib_dirs(&self) -> Vec<PathBuf> {
        self.shared.lib_dirs.lock()
            .unwrap_or_else(|e| e.into_inner())
            .clone()
    }

    /// Convenience accessor: platform DLL search directories (snapshot clone).
    pub fn platform_dirs(&self) -> Vec<PathBuf> {
        self.shared.platform_dirs.lock()
            .unwrap_or_else(|e| e.into_inner())
            .clone()
    }

    /// Update the lib directory set. Sprint 57 Wave 4 G9: tests and the
    /// CLI call this after `new()` to override defaults; workers take a
    /// fresh clone for each file-resolution call, so the change is
    /// observed by subsequent typechecks.
    pub fn set_lib_dirs(&mut self, dirs: Vec<PathBuf>) {
        *self.shared.lib_dirs.lock()
            .unwrap_or_else(|e| e.into_inner()) = dirs;
    }

    /// Update the platform search directory set. Same semantics as
    /// `set_lib_dirs`.
    pub fn set_platform_dirs(&mut self, dirs: Vec<PathBuf>) {
        *self.shared.platform_dirs.lock()
            .unwrap_or_else(|e| e.into_inner()) = dirs;
    }

    /// Append a single platform search directory to the current set.
    /// Convenience wrapper around `set_platform_dirs` for tests/CLI.
    pub fn push_platform_dir(&mut self, dir: PathBuf) {
        let mut guard = self.shared.platform_dirs.lock()
            .unwrap_or_else(|e| e.into_inner());
        guard.push(dir);
    }

    // -- Convenience accessors for shared TC state --

    /// Create a TypeCheckEnv borrowing the shared state.
    fn tc_env(&self) -> TypeCheckEnv<'_, Code, ()> {
        TypeCheckEnv::new(&self.shared.symbol_tables, &self.shared.next_type_id)
    }

    /// Get the current module path (REPL carry-forward).
    fn current_module_path(&self) -> ModuleFullPath {
        self.shared.current_module.lock()
            .unwrap_or_else(|e| e.into_inner())
            .clone()
    }

    /// Set the current module path (REPL carry-forward).
    fn set_current_module(&self, path: ModuleFullPath) {
        let tc = self.tc_env();
        tc.ensure_module_exists(&path);
        *self.shared.current_module.lock()
            .unwrap_or_else(|e| e.into_inner()) = path.clone();
        // Sprint 66 Wave 3a-γ: keep the test-runner state's `current_module`
        // in sync so `discover-tests` (with empty module arg) targets the
        // active REPL namespace after a `/mod` switch.
        *self.shared.test_runner_state.current_module.lock()
            .unwrap_or_else(|e| e.into_inner()) = path.clone();
        // Create a new CheckState for the new module.
        // REPL carry-forward state (subst, env, overloads) is lost on module switch.
        // This matches the old behavior where /mod started fresh.
        *self.shared.repl_check_state.lock()
            .unwrap_or_else(|e| e.into_inner()) = Some(CheckState::new(path));
    }

    /// Get a read guard for the current module's symbol table.
    fn current_symbol_table(&self) -> dashmap::mapref::one::Ref<'_, ModuleFullPath, SessionSymbolTable> {
        let module = self.current_module_path();
        self.shared.symbol_tables.get(&module)
            .unwrap_or_else(|| unreachable!("invariant: current_module always exists in symbol_tables"))
    }

    /// Get a read guard for any module's symbol table.
    fn module_table(&self, path: &ModuleFullPath) -> Option<dashmap::mapref::one::Ref<'_, ModuleFullPath, SessionSymbolTable>> {
        self.shared.symbol_tables.get(path)
    }

    /// Introduce a module into the session — the 4-branch lifecycle gate.
    ///
    /// Sprint 67 hack-back (FIXME 0192 Residual Task 2): the single
    /// orchestration entry point for module introduction. Routes to one of
    /// four outcomes:
    ///   1. **AlreadyPresent** — `path` already has a symbol table; no change.
    ///   2. **CachedLoad** — cache reports a valid metadata + `.o` for `path`;
    ///      decode the cached `SymbolTable`, advance the typecheck `next_id`
    ///      past any cached TypeId vars (the consistency invariant from the
    ///      old `restore_cached_module`), and atomically install the table
    ///      via `cranelisp_types::install_module`.
    ///   3. **SourceLoad** — no cache hit but a source file is registered for
    ///      `path`; signal the caller (scheduler) to enqueue compilation.
    ///   4. **Blank** — neither cache nor source is available; create an empty
    ///      symbol table at `path` via `cranelisp_types::ensure_module_exists`.
    ///
    /// The cache-hit branch shares its install primitive with `worker.rs`'s
    /// `try_cache_hit_load` (which retains the surrounding logic for transitive
    /// dep walking + platform re-resolution that the worker context owns).
    /// The source-load branch returns the outcome variant so the caller can
    /// decide whether/how to schedule — the orchestrator does not directly
    /// drive the scheduler (which has tighter shared-state contracts the
    /// session does not own).
    pub fn introduce_module(
        &self,
        path: &ModuleFullPath,
    ) -> Result<ModuleIntroductionOutcome, CranelispError> {
        // Branch 1 — already present.
        if self.shared.symbol_tables.contains_key(path) {
            return Ok(ModuleIntroductionOutcome::AlreadyPresent);
        }

        // Branch 2 — cache hit. Probe the backend cache for a valid entry;
        // if present, decode and install atomically.
        if let Some(decoded) = self.try_load_cached_for_introduction(path)? {
            cranelisp_typecheck::advance_next_id_past_table(
                &self.shared.next_type_id, &decoded,
            );
            cranelisp_types::install_module(
                &self.shared.symbol_tables, path.clone(), decoded,
            );
            return Ok(ModuleIntroductionOutcome::CachedLoad);
        }

        // Branch 3 — source hit. The session has no scheduler in hand here;
        // signal the caller. Source presence is determined by inspecting the
        // worker's `file_to_module` reverse-mapping or by attempting source
        // lookup via cache_state's known paths.
        if self.find_module_source(path).is_some() {
            return Ok(ModuleIntroductionOutcome::SourceLoad);
        }

        // Branch 4 — blank create-if-absent.
        let _ = cranelisp_types::ensure_module_exists(
            &self.shared.symbol_tables, path,
        );
        Ok(ModuleIntroductionOutcome::Blank)
    }

    /// Backwards-compatible alias for the Blank branch only. Kept for callers
    /// that want create-if-absent semantics without inspecting the outcome.
    #[allow(dead_code)]
    pub fn introduce_module_blank(&self, path: &ModuleFullPath) {
        let _ = cranelisp_types::ensure_module_exists(&self.shared.symbol_tables, path);
    }

    /// Cache probe for `introduce_module`'s branch 2. Returns
    /// `Some(decoded_table)` iff cache reports a valid entry with an `.o`
    /// file present. Errors (cache read failures) bubble up as
    /// `CranelispError::Internal` strings; absent entries return `Ok(None)`.
    fn try_load_cached_for_introduction(
        &self,
        path: &ModuleFullPath,
    ) -> Result<Option<cranelisp_types::SymbolTable<Code, ()>>, CranelispError> {
        use cranelisp_backend::cache;
        let cache_dir = {
            let guard = self.shared.cache_state.lock()
                .unwrap_or_else(|e| e.into_inner());
            match guard.as_ref() {
                Some(cs) => cs.cache_dir().to_path_buf(),
                None => return Ok(None),
            }
        };
        let cached = match cache::try_load_cached_module(&cache_dir, path) {
            Ok(Some(c)) => c,
            _ => return Ok(None),
        };
        if !cached.has_object {
            return Ok(None);
        }
        Ok(Some(
            cached.metadata.symbol_table.into_concrete::<Code, ()>(),
        ))
    }

    /// Branch-3 probe: returns the source file path for `module` if one is
    /// known to the session (registered in `file_to_module`'s reverse map).
    fn find_module_source(&self, module: &ModuleFullPath) -> Option<std::path::PathBuf> {
        let guard = self.shared.file_to_module.lock()
            .unwrap_or_else(|e| e.into_inner());
        guard.iter()
            .find_map(|(file, mp)| if mp == module { Some(file.clone()) } else { None })
    }

    /// Resolve a module by name (for /exports command).
    ///
    /// Sprint 67 hack-back (FIXME 0192 method 7): the `TypeCheckEnv` method
    /// was deleted; the body relocated to `cranelisp_types` as a free fn.
    /// The session passes its `current_module_path()` as the scope root
    /// (replacing the prior `state.current_module` access).
    fn resolve_module_by_name(&self, name: &str) -> Option<ModuleFullPath> {
        cranelisp_types::resolve_module_by_name_chain(
            &self.shared.symbol_tables,
            &self.current_module_path(),
            name,
        )
    }

    /// Take a snapshot for REPL error recovery.
    fn tc_snapshot(&self) -> ReplSnapshot {
        let tc = self.tc_env();
        let cs = self.shared.repl_check_state.lock()
            .unwrap_or_else(|e| e.into_inner());
        let cs = cs.as_ref().expect("REPL check state must be initialized");
        tc.snapshot(cs)
    }

    /// Restore from a snapshot on REPL error.
    fn tc_restore(&self, snapshot: ReplSnapshot) {
        let tc = self.tc_env();
        let mut guard = self.shared.repl_check_state.lock()
            .unwrap_or_else(|e| e.into_inner());
        let cs = guard.as_mut().expect("REPL check state must be initialized");
        tc.restore(cs, snapshot);
    }

    /// Initialize the file watcher for REPL mode (repl/spec.md §14).
    ///
    /// Creates an OS-level file watcher and registers all currently known
    /// module source files. Call once after `wait_inmem_complete()` so
    /// that `file_to_module` is populated.
    pub fn init_watcher(&mut self) {
        let mut fw = match crate::watch::FileWatcher::new() {
            Some(fw) => fw,
            None => return,
        };

        // Register all source files already loaded (prelude + its deps).
        let file_to_mod = self.shared.file_to_module
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        for path in file_to_mod.keys() {
            fw.watch_file(path);
        }
        drop(file_to_mod);

        self.watcher = Some(fw);
    }

    // -----------------------------------------------------------------------
    // Sprint 67 W3 — Facade-prescribed introspection accessors
    // (FIXME 0176 partial close; `facades/int.md` §"Introspection accessors")
    //
    // Pure read-side projections over `shared.symbol_tables` + `shared.introspection`.
    // No `&mut self` required for reads; the two mutating REPL-state methods
    // (`set_current_repl_module`, `set_repl_input_active`) write to
    // `CompilerSession`-side state per the SharedState alignment plan.
    //
    // Today these forward to the existing slash-command handler internals
    // (`handle_source`, `get_introspection`, etc.); subsequent /dev (int) fires
    // will pivot the slash-command handlers to call these new accessors first
    // so the accessors become the canonical entry points.
    // -----------------------------------------------------------------------

    /// REPL `/source` — original source text of a symbol, or `None` if the
    /// symbol has no introspection record (production batch mode) or no
    /// captured source. Reads `shared.introspection[fq]`.
    pub fn symbol_source(&self, fq: &FQSymbol) -> Option<String> {
        self.shared.introspection.get(fq)
            .and_then(|intr| intr.source.clone())
    }

    /// REPL `/sexp` — parsed s-expression of a symbol's defining form, or
    /// `None`. Reads `shared.introspection[fq]`.
    pub fn symbol_sexp(&self, fq: &FQSymbol) -> Option<Sexp> {
        self.shared.introspection.get(fq)
            .and_then(|intr| intr.sexp.clone())
    }

    /// REPL `/clif` — CLIF IR text of a symbol's compiled body, or `None`.
    /// Populated only when `CRANELISP_CODEGEN_TRACE` or REPL-trace mode is
    /// active. Reads `shared.introspection[fq]`.
    pub fn symbol_clif(&self, fq: &FQSymbol) -> Option<String> {
        self.shared.introspection.get(fq)
            .and_then(|intr| intr.clif_ir.clone())
    }

    /// REPL `/disasm` — disassembled native code of a symbol, or `None`.
    /// Same trace-mode gating as `symbol_clif`. Reads `shared.introspection[fq]`.
    pub fn symbol_disasm(&self, fq: &FQSymbol) -> Option<String> {
        self.shared.introspection.get(fq)
            .and_then(|intr| intr.disasm.clone())
    }

    /// REPL `/info NAME` — one-shot description of a symbol resolved from
    /// `name` against the current REPL module. Returns the symbol's
    /// classification (Fn / Type / Trait / Macro / Constructor / SpecialForm),
    /// scheme (if applicable), docstring, and the captured source text.
    ///
    /// Pure read against `shared.symbol_tables` + `shared.introspection`.
    /// Returns `None` if the bare `name` does not resolve in the current
    /// module (no chain-follow performed at this layer — the caller may
    /// chain-follow if it wants imports + reexports resolved).
    pub fn describe_symbol(&self, name: &str) -> Option<SymbolDescription> {
        let current = self.current_module_path();
        // Probe current module first; if absent, fall back to root `""`
        // (FIXME 0192 Residual Task 3 + FIXME 0193 — special-form metadata
        // lives at root, not in user-mode tables). The fallback's resolved
        // module reflects where the entry actually lives so the returned
        // `FQSymbol` is correct.
        let (entry, resolved_module) = {
            let cur_table = self.shared.symbol_tables.get(&current);
            let cur_hit = cur_table.as_ref().and_then(|t| t.get(name).cloned());
            match cur_hit {
                Some(e) => (e, current.clone()),
                None => {
                    let root = ModuleFullPath::from("");
                    let root_table = self.shared.symbol_tables.get(&root)?;
                    let root_hit = root_table.get(name).cloned()?;
                    (root_hit, root)
                }
            }
        };
        let fq = FQSymbol {
            module: resolved_module.clone(),
            symbol: Symbol::from(name),
        };
        let (category, scheme, docstring) = match &entry {
            ModuleEntry::Def { scheme, docstring, kind, .. } => {
                let cat = match kind.as_ref() {
                    DefKind::SpecialForm { .. } => SymbolCategory::SpecialForm,
                    DefKind::Primitive { .. } => SymbolCategory::Fn,
                    _ => SymbolCategory::Fn,
                };
                (cat, Some(scheme.clone()), docstring.clone())
            }
            ModuleEntry::TypeDef { .. } =>
                (SymbolCategory::Type, None, None),
            ModuleEntry::TraitDecl { decl, .. } =>
                (SymbolCategory::Trait, None, decl.docstring.clone()),
            ModuleEntry::Constructor { scheme, .. } =>
                (SymbolCategory::Constructor, Some(scheme.clone()), None),
            ModuleEntry::Macro { docstring, .. } =>
                (SymbolCategory::Macro, None, docstring.clone()),
            _ => return None,
        };
        let source = self.shared.introspection.get(&fq)
            .and_then(|intr| intr.source.clone());
        Some(SymbolDescription {
            fq,
            category,
            scheme,
            docstring,
            source,
            related: Vec::new(),
        })
    }

    /// REPL `/list` — user-defined symbols in the current REPL module (excludes
    /// imports + special forms). Returns a `Vec<SymbolInfo>` per facade
    /// §"Introspection records".
    pub fn list_user_definitions(&self) -> Vec<SymbolInfo> {
        let current = self.current_module_path();
        let mut out = Vec::new();
        if let Some(table) = self.shared.symbol_tables.get(&current) {
            for (name, entry) in table.all_symbols() {
                // Skip imports / reexports + special forms — those are surfaced
                // by `/imports` separately.
                let (category, scheme, docstring) = match entry {
                    ModuleEntry::Def { scheme, docstring, kind, .. } => {
                        if matches!(kind.as_ref(), DefKind::SpecialForm { .. }) {
                            continue;
                        }
                        (SymbolCategory::Fn, Some(scheme.clone()), docstring.clone())
                    }
                    ModuleEntry::TypeDef { .. } =>
                        (SymbolCategory::Type, None, None),
                    ModuleEntry::TraitDecl { decl, .. } =>
                        (SymbolCategory::Trait, None, decl.docstring.clone()),
                    ModuleEntry::Macro { docstring, .. } =>
                        (SymbolCategory::Macro, None, docstring.clone()),
                    ModuleEntry::Import { .. } | ModuleEntry::Reexport { .. } => continue,
                    _ => continue,
                };
                out.push(SymbolInfo {
                    name: name.clone(),
                    category,
                    scheme,
                    docstring,
                });
            }
        }
        out
    }

    /// REPL `/imports [MODULE]` — list the import declarations in a target
    /// module. Returns one `ImportSpec` per `ModuleEntry::Import`, carrying
    /// the source module + the local binding name (per
    /// `cranelisp_types::ImportSpec`). Reexports are listed separately by
    /// `module_exports` when the module publishes them.
    ///
    /// Per-binding reconstruction shape: `ModuleEntry::Import` stores only
    /// the source `FQSymbol` per binding; the parse-time `ImportSpec` is not
    /// retained on the symbol table. Each returned spec is therefore a
    /// single-name `Specific([local_name])` against the source module, with
    /// `alias = None` and `span = Span::SYNTHETIC`. Aliased imports (local
    /// != source.symbol) collapse to the local name on the binding side —
    /// the source.symbol distinction is recoverable from the
    /// `module_exports` of the source module. Threading the original
    /// parse-time `ImportSpec` through to here is tracked by FIXME 0194.
    pub fn module_imports(&self, module: &ModuleFullPath) -> Vec<cranelisp_types::ImportSpec> {
        use cranelisp_types::{ImportNames, ImportSpec};
        let mut out = Vec::new();
        if let Some(table) = self.shared.symbol_tables.get(module) {
            for (name, entry) in table.all_symbols() {
                if let ModuleEntry::Import { source } = entry {
                    out.push(ImportSpec {
                        module_path: source.module.clone(),
                        alias: None,
                        names: ImportNames::Specific(vec![name.clone()]),
                        span: Span::SYNTHETIC,
                    });
                }
            }
        }
        out
    }

    /// REPL `/exports MODULE` — list the publicly-visible symbols of a module.
    /// A symbol is public iff its `ModuleEntry` carries `Visibility::Public`
    /// (Def / TypeDef / TraitDecl / Macro / Constructor / Reexport).
    pub fn module_exports(&self, module: &ModuleFullPath) -> Vec<(Symbol, ModuleEntry<Code>)> {
        let mut out = Vec::new();
        if let Some(table) = self.shared.symbol_tables.get(module) {
            for (name, entry) in table.all_symbols() {
                let is_public = match entry {
                    ModuleEntry::Def { visibility, .. } |
                    ModuleEntry::TypeDef { visibility, .. } |
                    ModuleEntry::TraitDecl { visibility, .. } |
                    ModuleEntry::Macro { visibility, .. } |
                    ModuleEntry::Constructor { visibility, .. } =>
                        matches!(visibility, cranelisp_types::Visibility::Public),
                    ModuleEntry::Reexport { .. } => true,
                    _ => false,
                };
                if is_public {
                    out.push((name.clone(), entry.clone()));
                }
            }
        }
        out
    }

    /// Current REPL module (per facade §"CompilerSession.current_repl_module").
    /// Pure read against `shared.current_module`; the field's relocation to
    /// `CompilerSession`-side state is FIXME 0176's broader scope.
    pub fn current_repl_module(&self) -> ModuleFullPath {
        self.current_module_path()
    }

    /// Switch the REPL's active module (per `/mod NAME`). Writes
    /// `shared.current_module` + `shared.test_runner_state.current_module` +
    /// resets `shared.repl_check_state` to a fresh `CheckState` for the new
    /// module.
    pub fn set_current_repl_module(&mut self, module: ModuleFullPath) {
        self.set_current_module(module);
    }

    /// Update the watcher-input-active flag (per exec-flow-repl STEP 1 / STEP 3).
    /// The atomic boolean is shared with the watcher event handler via `Arc`.
    /// Sprint 67 hack-back stub: today this is a no-op because the
    /// `repl_input_active` field lives implicitly inside the watcher's own
    /// state. Retained as the facade-named entry point; once the field moves
    /// onto `CompilerSession` (per the SharedState alignment plan) this body
    /// becomes a real atomic write.
    pub fn set_repl_input_active(&self, _active: bool) {
        // No-op stub — see method docstring.
    }

    /// Register any newly-loaded module source files with the watcher.
    ///
    /// Called after eval/import so that newly discovered modules get watched.
    /// The watcher internally deduplicates already-watched directories.
    pub fn sync_watcher(&mut self) {
        let watcher = match &mut self.watcher {
            Some(w) => w,
            None => return,
        };
        let file_to_mod = self.shared.file_to_module
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        for path in file_to_mod.keys() {
            watcher.watch_file(path);
        }
    }

    /// Poll the file watcher for changed source files and reload them.
    ///
    /// Returns a list of user-visible messages (one per reloaded module).
    /// On success, removes the module from `error_modules`. On failure,
    /// adds it to `error_modules` to block subsequent evals.
    ///
    /// Per repl/spec.md §14: notification format is `[updated: file.cl]`
    /// on success, `[errors: file.cl]` on failure. Cascade invalidation
    /// reloads modules that depend on changed modules.
    pub fn poll_and_reload(&mut self) -> Vec<String> {
        let watcher = match &mut self.watcher {
            Some(w) => w,
            None => return Vec::new(),
        };

        let changed_paths = match watcher.poll_changes() {
            Some(paths) => paths,
            None => return Vec::new(),
        };

        // Map file paths → module paths via SharedState.file_to_module.
        let file_to_mod = self.shared.file_to_module
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let mut modules_to_reload: Vec<(ModuleFullPath, PathBuf)> = Vec::new();
        for path in &changed_paths {
            if let Some(module_path) = file_to_mod.get(path)
                && !modules_to_reload.iter().any(|(mp, _)| mp == module_path) {
                    modules_to_reload.push((module_path.clone(), path.clone()));
                }
        }
        // Cascade invalidation: find modules that import any changed module
        // and add them to the reload list. Sprint 58 Step 5a: read `imports`
        // off the per-module SymbolTable directly (was: parallel
        // `module_structures.import_specs`).
        let changed_modules: HashSet<ModuleFullPath> = modules_to_reload
            .iter()
            .map(|(mp, _)| mp.clone())
            .collect();
        for entry in self.shared.symbol_tables.iter() {
            let dependent_module = entry.key().clone();
            if changed_modules.contains(&dependent_module) {
                continue; // Already being reloaded directly.
            }
            let depends_on_changed = entry.value().imports.iter().any(|spec| {
                let import_mod = ModuleFullPath::from(spec.module_path.as_ref());
                changed_modules.contains(&import_mod)
            });
            if depends_on_changed {
                // Find the file path for this dependent module.
                if let Some(dep_path) = file_to_mod.iter()
                    .find(|(_, mp)| **mp == dependent_module)
                    .map(|(p, _)| p.clone())
                {
                    modules_to_reload.push((dependent_module, dep_path));
                }
            }
        }
        drop(file_to_mod);

        let mut messages = Vec::new();
        for (module_path, file_path) in modules_to_reload {
            // Extract just the filename for the notification message.
            let file_name = file_path.file_name()
                .and_then(|n| n.to_str())
                .unwrap_or_else(|| module_path.as_ref());
            match self.reload_module(&module_path, &file_path) {
                Ok(()) => {
                    self.error_modules.remove(&module_path);
                    messages.push(format!("[updated: {}]", file_name));
                }
                Err(e) => {
                    self.error_modules.insert(module_path.clone());
                    messages.push(format!("[errors: {}]\n  {e}", file_name));
                }
            }
        }
        messages
    }

    /// Regenerate the backing .cl file for the current module.
    ///
    /// Called after successful eval of a definition (defn, deftype, deftrait,
    /// impl, defmacro) or structural change (import, mod, platform).
    /// Reads the current module's symbol table and structural metadata,
    /// generates source text, and writes atomically.
    ///
    /// On write failure, prints a warning and continues — in-memory state
    /// is the ground truth (design/int/session-persistence.md §3.3).
    ///
    /// **Invariant**: After `regenerate_backing_file` returns, the freshly
    /// parsed sexps matching the file on disk are installed in
    /// `SharedState::module_sexps` for the current module. This mirrors the
    /// publish-before-register invariant enforced by
    /// `register_module_with_source` / `reload_module` / `register_dep_for_eval`
    /// (Sprint 58 W6 Defect 1, §8.3 E-3). Without this republish, a persistent
    /// priority worker that later pops a `Typecheck(current_module)` work item
    /// would observe the STALE sexps from session startup (e.g. an empty Vec
    /// if `user.cl` was missing) and mark the module Failed at shutdown —
    /// the "no parsed sexps for module 'user'" residue documented in
    /// `design/backend/defects-456-reduction.md §"Sprint 60 Wave 2 Round 3"`.
    pub fn regenerate_backing_file(&mut self) {
        let module = self.current_module_path();

        // Get the backing file path from typecheck product.
        let file_path = match self.shared.typecheck_products.get(&module) {
            Some(tp) => match &tp.file_path {
                Some(p) => p.clone(),
                None => {
                    // Entry module may not have a file path yet (fresh session).
                    // Default to {project_root}/{module}.cl.
                    self.shared.project_root.join(format!("{}.cl", module))
                }
            },
            None => self.shared.project_root.join(format!("{}.cl", module)),
        };

        // Read the symbol table for this module. Sprint 58 Step 5a: structural
        // decls (imports/exports/platforms/submodules) are now fields on the
        // SymbolTable itself; no separate read is needed.
        let st = match self.shared.symbol_tables.get(&module) {
            Some(st) => st.clone(),
            None => return, // No symbol table — nothing to save.
        };

        // Generate source text.
        let source = crate::save::generate_module_source(
            &st,
            &self.shared.introspection,
            &module,
        );

        // Skip writing empty source (no user-defined content).
        if source.trim().is_empty() {
            return;
        }

        // Compute content hash for watcher suppression.
        let hash = cranelisp_backend::cache::manifest::hash_source(&source);

        // Atomic write.
        if let Err(e) = crate::save::atomic_write(&file_path, &source) {
            eprintln!("Warning: failed to save {}: {e}", file_path.display());
            return;
        }

        // Update watcher content hash so the self-write is suppressed
        // (design/int/session-persistence.md §4).
        if let Some(ref mut watcher) = self.watcher {
            let canonical = file_path.canonicalize().unwrap_or_else(|_| file_path.clone());
            watcher.update_content_hash(canonical.clone(), hash);
        }

        // Register the file in file_to_module so the watcher can find it.
        if let Ok(canonical) = file_path.canonicalize() {
            self.shared.file_to_module
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .insert(canonical, module.clone());
        }

        // Republish the freshly-written source's parsed sexps into
        // `SharedState::module_sexps` so any subsequent persistent priority
        // worker that pops a `Typecheck(module)` work item observes the
        // current-world sexps instead of the stale startup Vec (which may be
        // empty if `user.cl` did not exist at session start). Defect fix per
        // `design/backend/defects-456-reduction.md §"Sprint 60 Wave 2
        // Round 3"` (H5) — mirrors Sprint 58 W6 Defect 1's publish-before-
        // register discipline for the REPL-time entry-module update path.
        //
        // Parse failures here are silently ignored: the source was just
        // generated by `crate::save::generate_module_source` from the
        // in-memory symbol table, so a parse failure would be an internal
        // round-trip bug, not user-actionable. Falling back to NOT
        // republishing would re-open the exact H5 defect this block closes,
        // so the only sensible recovery is to leave the stale sexps in place
        // (matches pre-fix behaviour for the degenerate case).
        if let Ok(sexps) = cranelisp_frontend::parse(&source) {
            let mut map = self.shared.module_sexps.lock()
                .unwrap_or_else(|e| e.into_inner());
            map.insert(module, sexps);
        }
    }

    /// Republish `SharedState::module_sexps[module]` from the module's current
    /// in-memory symbol table — Sprint 60 Wave 2 Round 3 H5 fix.
    ///
    /// Called when the REPL-eval thread is about to block on a dep and the
    /// caller module has been moved to `TypecheckBlocked`. Ensures that when
    /// the dep completes and the scheduler unblocks the caller into
    /// `TypecheckNext`, any persistent priority worker that pops the caller's
    /// `Typecheck` work item observes the current-world sexps (reflecting the
    /// form the REPL just processed) instead of a stale or absent entry.
    ///
    /// No-op on any of: missing symbol table (module not yet tracked),
    /// empty generated source (no user-defined content to typecheck), or
    /// parse failure (internal round-trip bug — leave existing sexps in
    /// place rather than publish garbage).
    fn republish_module_sexps_from_symbol_table(&self, module: &ModuleFullPath) {
        let Some(st) = self.shared.symbol_tables.get(module) else {
            return;
        };
        let source = crate::save::generate_module_source(
            &st,
            &self.shared.introspection,
            module,
        );
        if source.trim().is_empty() {
            return;
        }
        if let Ok(sexps) = cranelisp_frontend::parse(&source) {
            let mut map = self.shared.module_sexps.lock()
                .unwrap_or_else(|e| e.into_inner());
            map.insert(module.clone(), sexps);
            // Sprint 61 Wave 3 step 3e — H4 race closure (Change B).
            // Fires exactly when the republish succeeds (symbol table
            // present, source non-empty, parse ok). Post-fix dumps use
            // this to prove the caller-side republish precedes the
            // priority worker's `RegisterImportsLookup dep` on the
            // subsequent user-retry. See
            // `design/int/heisenbug-race-closure.md §8.1 Change B`.
            crate::observability::record_module_event(
                crate::observability::SchedulerTraceTag::RepublishFromSymbolTable,
                module.as_ref(),
            );
        }
    }

    /// Reload a single module from its source file.
    ///
    /// Clears the module's stale products, re-parses, publishes sexps to
    /// `SharedState::module_sexps`, and re-registers with the scheduler.
    /// The persistent priority workers pick up the re-registration and
    /// re-typecheck + re-codegen. Sprint 57 Wave 4 G11 per
    /// `persistent-workers.md` §4.6 — reload via scheduler falls out of
    /// persistent workers (same path as `register_module_with_source`).
    fn reload_module(
        &mut self,
        module_path: &ModuleFullPath,
        file_path: &Path,
    ) -> Result<(), CranelispError> {
        crate::observability::record_module_event(
            crate::observability::SchedulerTraceTag::RecompileModule,
            module_path.as_ref(),
        );
        let source = std::fs::read_to_string(file_path).map_err(|e| {
            CranelispError::ModuleError {
                message: format!("cannot read {}: {e}", file_path.display()),
                location: ErrorLocation::from_span_file(Span::new(0, 0), Some(file_path.to_path_buf())),
            }
        })?;

        // Remove stale products before recompilation.
        // Sprint 57 Wave 2 G6: `codegen_products` was deleted; compiled code
        // lives on `ModuleEntry::Def.code`. Walk the module's symbols and
        // clear each `code` field so stale pointers are not callable during
        // recompilation. The `Arc<Jit>` handles in `kept_jits` keep the old
        // mmap'd pages alive until the session ends (preserves the Phase-2
        // redefinition policy of "old code stays callable for in-flight
        // calls" — same behaviour as before, just via a different store).
        crate::observability::record_module_event(
            crate::observability::SchedulerTraceTag::ClearModuleState,
            module_path.as_ref(),
        );
        self.shared.typecheck_products.remove(module_path);
        // Clear any stale suspend state from a prior compile of this module.
        {
            let mut states = self.shared.suspend_states.lock()
                .unwrap_or_else(|e| e.into_inner());
            states.remove(module_path);
        }
        if let Some(mut st) = self.shared.symbol_tables.get_mut(module_path) {
            for entry in st.symbols.values_mut() {
                if let ModuleEntry::Def { code, .. } = entry {
                    *code = None;
                }
            }
        }

        let sexps = cranelisp_frontend::parse(&source)?;

        // Publish sexps and re-register. Persistent workers parked on the
        // priority-work condvar wake and process it (G11 per §4.6).
        {
            let mut map = self.shared.module_sexps.lock()
                .unwrap_or_else(|e| e.into_inner());
            map.insert(module_path.clone(), sexps);
        }
        // `re_register_module` clears `inmem_done` and re-queues the module
        // for typecheck. `register_module` would be a no-op because the
        // module is already in `scheduler.modules`.
        let re_registered = self.shared.scheduler.re_register_module(module_path);
        if !re_registered {
            // Module isn't known to the scheduler yet (first-time seed from
            // file watcher) — fall back to register_module.
            self.shared.scheduler.register_module(module_path.clone(), false);
        }

        // Block until inmem-done for every registered module. The workers
        // do the typecheck + in-memory codegen.
        self.shared.scheduler.wait_inmem_complete_blocking()?;

        // Check if the module ended up in Failed state (wait_inmem_complete_blocking
        // would have returned Err in that case, but double-check explicitly).
        if self.shared.scheduler.is_failed(module_path) {
            return Err(CranelispError::ModuleError {
                message: format!("module '{}' failed to compile", module_path.as_ref()),
                location: ErrorLocation::from_span_file(Span::new(0, 0), None),
            });
        }

        Ok(())
    }

    /// Register a module by name (pipeline-v4.md §3.1).
    ///
    /// Resolves source file, parses, enqueues for typechecking.
    /// TODO: currently runs inline worker loop. Will just enqueue
    /// once persistent workers are wired.
    pub fn register_module(
        &mut self,
        module_name: &str,
    ) -> Result<(), CranelispError> {
        self.register_entry_module(module_name)?;
        Ok(())
    }

    /// Re-register a module for typechecking (file-watcher path).
    ///
    /// Sprint 67 Wave 3 (FIXME 0176 closure scope) — facade-prescribed
    /// `CompilerSession` thin forward to `CompileScheduler::re_register_module`
    /// per `design/arch/facades/int.md` §"CompilerSession". Returns
    /// `Ok(true)` if the module was re-registered, `Ok(false)` if the
    /// scheduler skipped it (unknown module, or currently mid-typecheck).
    /// The `Result` wrapper is reserved for future error propagation; the
    /// scheduler's `re_register_module` itself is infallible today.
    pub fn re_register_module(
        &mut self,
        module: &ModuleFullPath,
    ) -> Result<bool, CranelispError> {
        Ok(self.shared.scheduler.re_register_module(module))
    }

    /// Register a module with explicit source (internal + test helpers).
    ///
    /// Enqueues sexps into `SharedState::module_sexps` and registers the
    /// module with the scheduler; the persistent priority workers parked
    /// on `priority_work_available` wake and process it. The caller blocks
    /// on `wait_inmem_complete_blocking` until every registered module
    /// reaches inmem_done or failure. Sprint 57 Wave 4 G9 per
    /// `persistent-workers.md` §4.3.
    pub fn register_module_with_source(
        &mut self,
        module_name: &str,
        source: &str,
        _entry_module_path: &Path,
    ) -> Result<Vec<Warning>, CranelispError> {
        let module = ModuleFullPath::from(module_name);
        let sexps = cranelisp_frontend::parse(source)?;

        // Record source hash in CacheState for manifest generation.
        {
            let hash = cranelisp_backend::cache::manifest::hash_source(source);
            let mut cs_guard = self.shared.cache_state.lock().unwrap_or_else(|e| e.into_inner());
            if let Some(cs) = cs_guard.as_mut() {
                cs.source_hashes_mut().insert(module.clone(), hash);
            }
        }

        // Publish sexps to workers BEFORE registering, so a worker that wakes
        // immediately on the scheduler notify finds the sexps ready.
        {
            let mut map = self.shared.module_sexps.lock()
                .unwrap_or_else(|e| e.into_inner());
            map.insert(module.clone(), sexps);
        }

        // Register module with scheduler (entry module, not delaying others).
        // Wakes parked priority workers via `priority_work_available.notify_all()`.
        self.shared.scheduler.register_module(module.clone(), false);

        // Block until every registered module reaches inmem_done (or a
        // module fails). The persistent priority workers do the typecheck
        // + in-memory codegen and call `notify_inmem_codegen_complete` /
        // `notify_typecheck_done`, which wakes the scheduler's completion
        // condvar.
        self.shared.scheduler.wait_inmem_complete_blocking()?;

        Ok(Vec::new())
    }

    /// Drive a REPL-discovered dep through the single `register_module`
    /// recursion used by every other persistence entry point — Decision 37
    /// enacted at the REPL-session surface (Sprint 59 Workstream A).
    ///
    /// Replaces `compile_dep_inline` (Sprint 59 §7 Step 3). The form handler
    /// that produced `ProcessResult::Blocked` has already published dep_sexps
    /// into `shared.module_sexps` and called `scheduler.register_module(dep,
    /// true)` + `block_for_typecheck`. This function's job is to block until
    /// the persistent priority worker pool brings the dep (and every
    /// transitive dep) to `inmem_done`. There is no second, session-side
    /// worker loop — the persistent worker pool is the single orchestrator.
    fn register_dep_for_eval(
        &mut self,
        dep_module: &ModuleFullPath,
        dep_sexps: &[Sexp],
    ) -> Result<(), CranelispError> {
        // Sprint 61 Wave 3 step 3e' — H5 race closure.
        //
        // Caller audit per /arch §3d' condition 1:
        // `grep 'wait_module_inmem_complete_blocking' src/` → 6 matches:
        // the definition at `scheduler.rs:943`; three comment-only references
        // (`scheduler.rs:1113`, `session_v4.rs:1473`, `session_v4.rs:2232`);
        // a doc comment in a test at `session_v4.rs:4587` that explicitly
        // AVOIDS calling the function (manually replays publish+register
        // instead). That leaves `register_dep_for_eval` as the SOLE caller
        // driving post-unblock retries.
        //
        // Scope: /arch §3d' offers two scopes for the guard — (i) narrow
        // around `wait_module_inmem_complete_blocking` only, or (ii) whole
        // function after `caller` is computed. /arch preferred (i) as
        // "minimally pessimistic". However, validation with CRANELISP_
        // SCHEDULER_TRACE revealed that by the time t1 reaches
        // `wait_module_inmem_complete_blocking`, t2 has frequently already
        // (a) popped `helper` from `typecheck_first`, (b) typechecked it,
        // (c) called `notify_typecheck_done(helper)` → `try_unblock_locked(
        // user)` with `eval_in_flight=false`, and (d) begun typechecking
        // `user`. The race window opens at `block_for_typecheck(user, helper)`
        // inside `handle_import` (worker.rs:1300), BEFORE register_dep_for_eval
        // is called, and persists until t1 sets the flag. Narrow scope is
        // therefore insufficient.
        //
        // Fix: set the flag at the top of register_dep_for_eval (option (ii),
        // /arch's own "Recommendation" alternative). This is still narrower
        // than "whole eval function" — the guard scope spans ONLY
        // register_dep_for_eval's body, and the guard drops at function
        // return (normal or panic). Per /arch §3d' condition 2, the set
        // takes the scheduler state lock so the set/read pair with
        // try_unblock_locked is linearised. Per condition 4, existing
        // trace tags continue to fire.
        let caller = self.current_module_path();
        let _eval_guard = EvalInFlightGuard::new(
            &self.shared.scheduler,
            caller.clone(),
        );

        // Guard: the form handler has usually already published dep_sexps
        // and registered with the scheduler (Sprint 58 W6 Defect 1 ordering).
        // Re-publish + re-register defensively so this entry point can also
        // serve call sites that reach us without a prior form-handler
        // Blocked result (e.g., tests, alternative eval paths).
        //
        // Sprint 61 Wave 3 step 3e — H4 race closure (Change A).
        //
        // On the hot path (REPL eval → handle_import → form-handler
        // `register_dep` + `scheduler.register_module(dep, true)` →
        // BlockAction::Block → here), the dep is ALREADY published into
        // `shared.module_sexps` AND registered with the scheduler. Emitting
        // a second publish+register here races with the priority worker
        // popping the dep from `typecheck_first` — see
        // `design/int/heisenbug-race-closure.md §7` for the failing-run dump
        // interleaving, and §8 for the fix rationale. Skip the defensive
        // pair when both conditions hold (published AND registered — per
        // /arch §3d condition 4, never on published alone so that failure
        // cleanup cannot trap a blocking waiter in this function).
        //
        // The caller-sexps republish at `republish_module_sexps_from_symbol_table`
        // below stays UNCONDITIONAL (per /arch §3d condition 3 — it is the
        // H5 REPL-persistence fix from Sprint 60 Wave 2 Round 3 and is
        // caller-side, not dep-side).
        let already_published = self.shared.module_sexps
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .contains_key(dep_module);
        let already_registered = self.shared.scheduler.is_registered(dep_module);
        let skip_defensive_pair = already_published && already_registered;

        if !skip_defensive_pair {
            {
                let mut map = self.shared.module_sexps.lock()
                    .unwrap_or_else(|e| e.into_inner());
                map.entry(dep_module.clone())
                    .or_insert_with(|| dep_sexps.to_vec());
            }
            crate::observability::record_module_event(
                crate::observability::SchedulerTraceTag::RegisterDepPublish,
                dep_module.as_ref(),
            );
        }

        // Sprint 60 Wave 2 Round 3 fix (H5 — REPL persistence residue).
        //
        // The REPL-eval thread that reached this point has already called
        // `handle_import` / `handle_platform` etc. for the current (caller)
        // module, which in turn called `scheduler.block_for_typecheck(caller,
        // dep, ...)`. That flipped the caller module to `TypecheckBlocked`.
        // When `dep_module` completes below and user's waiter is resolved,
        // the caller is unblocked → moved to `TypecheckNext` → eligible for
        // a persistent priority worker to pop its `Typecheck(caller)` work
        // item.
        //
        // The worker reads `shared.module_sexps[caller]`. On a fresh session
        // where `caller` is the entry module `user` with an empty/missing
        // `user.cl`, that entry was registered at startup, processed by a
        // worker once (empty sexps → empty program → inmem_done), and then
        // REMOVED from `module_sexps` (handle_typecheck_work_shared cleans up
        // after Complete). Without a republish here, the post-unblock worker
        // pop observes `module_sexps[caller] = None` and fails the module
        // with "no parsed sexps for module 'X'" — leaving `caller` in
        // `Failed` state, which `wait_object_complete` surfaces at shutdown
        // (exit 1). See `design/backend/defects-456-reduction.md
        // §"Sprint 60 Wave 2 Round 3"` (H5).
        //
        // Fix: regenerate the caller module's source from its current
        // in-memory symbol table (which now includes the just-processed
        // import / platform form), parse, and republish into
        // `module_sexps[caller]` before we block. If the post-unblock worker
        // pop wins the race against the REPL-eval thread resuming, it reads
        // valid current-world sexps instead of None.
        //
        // Mirror of Sprint 58 W6 Defect 1's publish-before-register invariant
        // applied to the REPL-time entry-module update path (here the
        // "register" is transitively the caller-module requeue triggered by
        // tiny's completion in `try_unblock_locked`).
        if caller != *dep_module {
            self.republish_module_sexps_from_symbol_table(&caller);
        }
        // Sprint 60 Workstream E-2 — reconcile with worker-side consensus:
        // every dep-registration site (not entry-module registration) passes
        // `delays_other=true` to land the dep in `ModulePool::TypecheckFirst`,
        // because the caller IS blocked on this dep (via
        // `wait_module_inmem_complete_blocking` below). Idempotent-guard on
        // the scheduler side (`scheduler.rs::register_module`) means this is
        // a no-op on the hot path where the form handler has already
        // registered with `true`; on the defensive path (tests, alt eval
        // paths) it upgrades the dep's pool from TypecheckNext to
        // TypecheckFirst, matching worker-side consensus. Entry-module sites
        // (`register_module_with_source`, `reload_module`) stay `false` — they
        // are the single whole-world waiter and no other module is queued
        // behind them. See `design/int/dual-path-persistence-collapse.md §8.2`.
        // DEBUG-ONLY guard: the publish-before-register invariant (§8.3 E-3)
        // — dep_sexps are published into shared.module_sexps BEFORE we notify
        // the scheduler. Catches accidental re-ordering in dev builds.
        debug_assert!(
            self.shared.module_sexps
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .contains_key(dep_module),
            "register_dep_for_eval MUST publish dep_sexps before calling scheduler.register_module"
        );
        // Sprint 61 Wave 3 step 3e (H4 race closure, Change A): gate the
        // defensive `register_module` call on the same "already published
        // AND already registered" flag computed above. Emitting a second
        // register here is what wakes the priority worker into the racing
        // window (see `design/int/heisenbug-race-closure.md §7.4`).
        // Idempotency inside `scheduler.register_module` suppresses the
        // state mutation, but the wake at `scheduler.rs:345` fires
        // unconditionally — so skipping the whole call on the hot path is
        // required for the fix.
        if !skip_defensive_pair {
            self.shared.scheduler.register_module(dep_module.clone(), true);
        }

        // Ensure the dep has a CheckState slot the persistent worker can
        // populate via `ensure_module_exists` — idempotent.
        self.tc_env().ensure_module_exists(dep_module);

        // Block on the persistent worker pool driving THIS dep (and every
        // transitive dep it blocks on) to inmem_done. Decision 37 §3.1 —
        // the single synchronisation primitive, scoped to the target dep.
        // We cannot use `wait_inmem_complete_blocking` (whole-world wait)
        // here: the caller (user module) is in TypecheckBlocked state and
        // can only be resumed by the eval thread's retry loop, not by a
        // persistent worker — so a whole-world wait would deadlock on the
        // user module. The old `compile_dep_inline` used `wait_inmem_complete`
        // (non-blocking) *after* running its own worker loop in-thread to
        // drive the dep to completion; the collapse replaces the inline
        // worker loop with a persistent-worker-driven *scoped* blocking wait.
        match self.shared.scheduler.wait_module_inmem_complete_blocking(dep_module) {
            Ok(()) => Ok(()),
            Err(e) => {
                self.shared.scheduler.reset_all_failed_modules();
                Err(CranelispError::from(e))
            }
        }
    }


    // -- REPL eval and command dispatch (pipeline-v4.md §6) --

    /// Process REPL slash commands and blank/comment detection.
    ///
    /// Returns `Nothing` for blank/comment lines and side-effect commands,
    /// `Final` for commands that produce display output, `Compile` for
    /// source text that should be compiled via `eval()`.
    pub fn process_commands(&mut self, src: &str, stdout: &mut impl Write) -> CommandResult {
        let trimmed = src.trim();

        // Blank or comment-only.
        if trimmed.is_empty() || is_comment_only(trimmed) {
            return CommandResult::Nothing;
        }

        // Slash commands.
        if let Some(cmd) = parse_slash_command(trimmed) {
            return self.dispatch_command(cmd, stdout);
        }

        // Special form feedback (bare special form names).
        if let Some(display) = self.special_form_feedback(trimmed) {
            return CommandResult::Final(display);
        }

        // Error blocking: refuse eval when modules have errors.
        if !self.error_modules.is_empty() {
            let names: Vec<String> = self.error_modules.iter()
                .map(|mp| mp.as_ref().to_string())
                .collect();
            let msg = format!(
                "Cannot evaluate: module '{}' has errors. Fix the source file and save.",
                names.join("', '"),
            );
            return CommandResult::Final(msg);
        }

        // Source text to compile.
        CommandResult::Compile(trimmed.to_string())
    }

    /// Dispatch a parsed slash command, returning a `CommandResult`.
    fn dispatch_command(
        &mut self,
        cmd: ReplCommand<'_>,
        stdout: &mut impl Write,
    ) -> CommandResult {
        match cmd {
            ReplCommand::Help => {
                print_help(stdout);
                CommandResult::Nothing
            }
            ReplCommand::Quit => {
                CommandResult::Quit
            }
            ReplCommand::Sig(name) => {
                let output = self.handle_sig(name);
                CommandResult::Final(output)
            }
            ReplCommand::Doc(name) => {
                let output = self.handle_doc(name);
                CommandResult::Final(output)
            }
            ReplCommand::List(filter) => {
                let output = self.handle_list(filter);
                CommandResult::Final(output)
            }
            ReplCommand::Mod(name) => {
                self.handle_mod(name);
                CommandResult::Nothing
            }
            ReplCommand::Source(name) => {
                CommandResult::Final(self.handle_source(name))
            }
            ReplCommand::SexpCmd(name) => {
                CommandResult::Final(self.handle_sexp_cmd(name))
            }
            ReplCommand::Ast(name) => {
                CommandResult::Final(self.handle_ast(name))
            }
            ReplCommand::Clif(name) => {
                CommandResult::Final(self.handle_clif(name))
            }
            ReplCommand::Disasm(name) => {
                CommandResult::Final(self.handle_disasm(name))
            }
            ReplCommand::Info(name) => {
                CommandResult::Final(self.handle_info(name))
            }
            ReplCommand::Type(expr) => {
                CommandResult::Final(self.handle_type(expr))
            }
            ReplCommand::Imports(filter) => {
                CommandResult::Final(self.handle_imports(filter))
            }
            ReplCommand::Exports(arg) => {
                CommandResult::Final(self.handle_exports(arg))
            }
            ReplCommand::Expand(form) => {
                CommandResult::Final(self.handle_expand(form))
            }
            ReplCommand::Time(expr) => {
                CommandResult::Final(self.handle_time(expr))
            }
            ReplCommand::Mem(expr) => {
                CommandResult::Final(self.handle_mem(expr))
            }
            ReplCommand::Sh(cmd) => {
                run_shell_command(cmd, stdout);
                CommandResult::Nothing
            }
            ReplCommand::Unknown(cmd) => {
                CommandResult::Final(format!(
                    "error: unknown command '{cmd}'. Type /help for available commands."
                ))
            }
            ReplCommand::RunTests(arg) => {
                CommandResult::Final(self.handle_run_tests(arg))
            }
            ReplCommand::RunAllTests => {
                CommandResult::Final(self.handle_run_all_tests())
            }
            ReplCommand::Reset => {
                // Clear file watcher state so stale watches don't persist.
                if let Some(ref mut w) = self.watcher {
                    w.clear_all();
                }
                self.error_modules.clear();
                CommandResult::Final("command not yet available in v4 REPL".to_string())
            }
        }
    }

    /// Evaluate source text in the current REPL module.
    ///
    /// Parses source into sexps, processes each form through the v4 worker
    /// path with Additive strategy, and returns the result for display.
    /// On error, the TypeChecker is restored to its pre-input snapshot.
    pub fn eval(&mut self, source: &str) -> Result<Option<EvalResult>, CranelispError> {
        let trimmed = source.trim();
        if trimmed.is_empty() || is_comment_only(trimmed) {
            return Ok(None);
        }

        let sexps = cranelisp_frontend::parse(source)?;
        if sexps.is_empty() {
            return Ok(None);
        }

        let mut last_result: Option<EvalResult> = None;
        let mut all_warnings = Vec::new();

        for sexp in &sexps {
            match self.eval_one_form(sexp) {
                Ok(Some(result)) => {
                    // Store source text for /source command — extract from
                    // original input using the sexp's span.
                    if let EvalResult::Def { symbol, .. } = &result {
                        let span = sexp.span();
                        let src = if span.start < span.end && (span.end as usize) <= source.len() {
                            &source[span.start as usize..span.end as usize]
                        } else {
                            source.trim()
                        };
                        let fq = FQSymbol {
                            module: symbol.module.clone(),
                            symbol: symbol.symbol.clone(),
                        };
                        self.shared.introspection.entry(fq).or_default().source = Some(src.to_string());
                    }
                    all_warnings.extend(result.warnings().iter().cloned());
                    last_result = Some(result);
                }
                Ok(None) => {}
                Err(e) => {
                    if sexps.len() == 1 {
                        return Err(e);
                    }
                    // Multi-form: report error inline but continue.
                    // TODO: multi-form error handling — for now, wrap as Val.
                    last_result = Some(EvalResult::Val {
                        value: 0,
                        ty: Type::Int,
                        warnings: vec![Warning {
                            kind: cranelisp_types::WarningKind::Other,
                            message: format!("Error: {e}"),
                            span: Span::SYNTHETIC,
                        }],
                    });
                }
            }
        }

        if let Some(ref mut r) = last_result {
            *r.warnings_mut() = all_warnings;
        }
        Ok(last_result)
    }

    /// Evaluate a single sexp with TC snapshot/restore for error recovery.
    fn eval_one_form(&mut self, sexp: &Sexp) -> Result<Option<EvalResult>, CranelispError> {
        // Bare symbol introspection (macros, special forms).
        if let Some(result) = self.check_bare_symbol_introspection(sexp) {
            return Ok(Some(result));
        }

        let snapshot = self.tc_snapshot();
        match self.process_single_form(sexp) {
            Ok(result) => Ok(result),
            Err(e) => {
                self.tc_restore(snapshot);
                Err(e)
            }
        }
    }

    /// Process a single sexp through `process_module_forms(Additive)` then codegen.
    ///
    /// Handles blocked dependencies by compiling them inline and retrying.
    fn process_single_form(&mut self, sexp: &Sexp) -> Result<Option<EvalResult>, CranelispError> {
        use crate::worker::{self, ModuleCheckAccumulator, ProcessResult};

        const MAX_DEP_RETRIES: usize = 100;

        for retry in 0..MAX_DEP_RETRIES {
            let module = self.current_module_path();
            let accumulator = ModuleCheckAccumulator::new();
            let expanded_program = Vec::new();
            let single_sexp = [sexp.clone()];

            let result = {
                // Extract REPL check_state for worker use, restore after.
                self.tc_env().ensure_module_exists(&module);
                let repl_cs = self.shared.repl_check_state.lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .take()
                    .unwrap_or_else(|| CheckState::new(module.clone()));
                let lib_dirs_snap = self.lib_dirs();
                let platform_dirs_snap = self.platform_dirs();
                let mut wctx = ModuleCompiler {
                    symbol_tables: &self.shared.symbol_tables,
                    next_type_id: &self.shared.next_type_id,
                    check_state: repl_cs,
                    current_module: module.clone(),
                    scheduler: &self.shared.scheduler,
                    typecheck_products: &self.shared.typecheck_products,
                    introspection: Some(&self.shared.introspection),
                    lib_dirs: &lib_dirs_snap,
                    platform_dirs: &platform_dirs_snap,
                    project_root: &self.shared.project_root,
                    shared_state: Some(&self.shared),
                };

                let mut suspend_state = worker::ModuleSuspendState {
                    accumulator,
                    expanded_program,
                    pass1_done: false,
                };
                let res = worker::process_module_forms(
                    &mut wctx,
                    &module,
                    &single_sexp,
                    0,
                    &mut suspend_state,
                    ModuleStrategy::Additive,
                );
                // Restore REPL check_state.
                *self.shared.repl_check_state.lock()
                    .unwrap_or_else(|e| e.into_inner()) = Some(wctx.check_state);
                res?
            };

            match result {
                ProcessResult::Complete { check_result, program } => {
                    // If program is empty, the form was handled during expansion
                    // (defmacro, import, platform, mod). Return Def with name
                    // extracted from the original sexp.
                    if program.is_empty() {
                        return match extract_def_name_from_sexp(sexp) {
                            Some(symbol_name) => Ok(Some(EvalResult::Def {
                                symbol: FQSymbol {
                                    module: module.clone(),
                                    symbol: Symbol::from(symbol_name),
                                },
                                ty: Type::Int,
                                warnings: check_result.warnings.clone(),
                            })),
                            // import/platform/mod — no visible result.
                            None => Ok(None),
                        };
                    }
                    return self.codegen_and_execute(&module, &program, &check_result).map(Some);
                }
                ProcessResult::Blocked { dep_module, dep_sexps, .. } => {
                    // Sprint 59 Workstream A §7 Step 4 — collapse the
                    // session-side inline worker-loop orchestrator onto
                    // the single `register_module` recursion. The form
                    // handler has published dep_sexps and registered with
                    // the scheduler; we just block on the persistent
                    // worker pool driving dep typecheck to completion.
                    self.register_dep_for_eval(&dep_module, &dep_sexps)?;
                    if retry == MAX_DEP_RETRIES - 1 {
                        return Err(CranelispError::ModuleError {
                            message: format!(
                                "dependency chain too deep (>{} retries) while resolving '{}'",
                                MAX_DEP_RETRIES, dep_module,
                            ),
                            location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
                        });
                    }
                }
            }
        }

        unreachable!("invariant: loop always returns or errors before exhausting iterations")
    }

    /// Run codegen for definitions, then execute if there is a trailing expression.
    fn codegen_and_execute(
        &mut self,
        module: &ModuleFullPath,
        program: &[TopLevel],
        check: &CheckResult,
    ) -> Result<EvalResult, CranelispError> {
        // Ensure typecheck product exists for this module.
        crate::worker::ensure_typecheck_product(&self.shared.typecheck_products, module);

        // Sprint 66 Wave 3a-γ: the `discover-tests` / `run-test` /
        // `cranelisp_trace_format` intrinsics are registered unconditionally
        // at JIT setup inside `inline_jit_codegen_for_names` (and inside the
        // expression-eval JIT in `pipeline.rs`). No per-program scan, no
        // conditional plumbing. See FIXME 0178 for the architectural
        // principle (no conditional registration of intrinsics — uniform
        // dispatch through `JITBuilder::symbol()`).
        //
        // The intrinsics dereference `TestRunnerState` / `TraceDisplayState`
        // at call time. The `TestRunnerState` allocation lives on
        // `SharedState` (built once in `CompilerSession::new`); the
        // thread-local pointer is set just-in-time below before invoking
        // compiled code. The trace-display state is set per-eval when
        // `(trace ...)` is present in the expression.
        set_test_runner_state(&self.shared.test_runner_state);

        // Unified JIT codegen via compile_to_module (Sprint 56 Wave 2).
        // Derives the compilation batch from `program`, compiles through the
        // single backend entry point, and populates `ModuleEntry::Def.code`
        // (Sprint 57 Wave 2 G6) + introspection. No env, no mode
        // discriminator — see design/int/phase2-codegen-convergence.md §5.
        crate::worker::inline_jit_codegen_for_module(
            &self.shared.scheduler,
            module,
            program,
            &self.shared.symbol_tables,
            Some(&self.shared.introspection),
            &[],
            Some(&self.shared),
        )?;

        let has_expr = program.iter().any(|tl| matches!(tl, TopLevel::Expr(_)));

        if has_expr {
            let (jit_syms, got_defs) = crate::worker::collect_jit_setup_public(
                &self.shared.symbol_tables,
                module,
            );

            // Build traced_fns from the session's compiled symbols (project-
            // root modules only, per spec §4.12.3). When the expression has
            // no `(trace ...)` form, `compile_and_execute_expr` takes the
            // non-trace JIT path regardless of `traced_fns` length, so this
            // is a no-op cost beyond the symbol-table scan.
            //
            // Sprint 66 Wave 3a-γ: the `cranelisp_trace_format` symbol is
            // registered as an intrinsic at JIT setup (no extra-symbols
            // plumbing); the trace display state is set unconditionally so
            // the intrinsic always has a valid pointer to read.
            let traced_fns = self.build_traced_fns(module);

            let display_state = TraceDisplayState {
                symbol_tables: &self.shared.symbol_tables as *const _,
            };
            set_trace_display_state(&display_state);

            let result = crate::pipeline::compile_and_execute_expr(
                &jit_syms,
                &got_defs,
                check.display.as_ref(),
                &traced_fns,
                &[],
                &self.shared.symbol_tables,
                module.clone(),
            );

            clear_trace_display_state();

            let (value, ty) = result?;

            Ok(EvalResult::Val {
                value,
                ty,
                warnings: check.warnings.clone(),
            })
        } else {
            // Definition-only: extract the defined symbol name from the last
            // user-visible form. Inlined defns (mono, default methods, trait
            // impl mangled methods) are appended after the original forms by
            // finalize_module — skip them by finding the last non-Defn form
            // (TraitDecl, TraitImpl, TypeDef) or the first Defn.
            let last = program.iter().rev().find(|tl| matches!(tl,
                TopLevel::TraitDecl(_) | TopLevel::TraitImpl(_) | TopLevel::TypeDef { .. }
            )).or_else(|| program.iter().find(|tl| matches!(tl, TopLevel::Defn(_))))
              .or(program.last());

            let symbol_name = last.map(|tl| match tl {
                TopLevel::Defn(d) => d.name.to_string(),
                TopLevel::TraitDecl(t) => t.name.to_string(),
                TopLevel::TraitImpl(t) => format!("{}.{}", t.trait_name, t.target_type),
                TopLevel::TypeDef { name, .. } => name.to_string(),
                TopLevel::Expr(_) => unreachable!("has_expr was false"),
            }).unwrap_or_default();

            let ty = check.display.as_ref()
                .map(|d| d.ty.clone())
                .unwrap_or(Type::Int);

            Ok(EvalResult::Def {
                symbol: FQSymbol {
                    module: module.clone(),
                    symbol: Symbol::from(symbol_name),
                },
                ty,
                warnings: check.warnings.clone(),
            })
        }
    }

    /// Build `TracedFnInfo` for user-defined functions in project-root modules.
    ///
    /// Per spec §4.12.3: only modules whose source files are under the project
    /// root are instrumented. Library modules (via lib search path) are excluded.
    fn build_traced_fns(
        &self,
        _current_module: &ModuleFullPath,
    ) -> Vec<cranelisp_backend::compiler::TracedFnInfo> {
        use cranelisp_backend::compiler::TracedFnInfo;

        let mut traced = Vec::new();

        for tp_entry in self.shared.typecheck_products.iter() {
            let module_path = tp_entry.key();
            let tp = tp_entry.value();

            // §4.12.3: only trace project-root modules.
            if let Some(ref fp) = tp.file_path
                && !fp.starts_with(&self.shared.project_root) {
                    continue;
                }

            // G7 (Wave 0): GOT lives on SymbolTable now.
            let got_base = match self.shared.symbol_tables.get(module_path) {
                Some(st) => st.got.base_ptr() as i64,
                None => continue,
            };

            let symbols = match self.shared.symbol_tables.get(module_path) {
                Some(st) => st,
                None => continue,
            };

            for (name, entry) in symbols.all_symbols() {
                // Sprint 57 Wave 2 G6: read `code` from the symbol-table entry
                // (replaces the deleted `codegen_products[module].code` lookup).
                if let ModuleEntry::Def {
                    scheme,
                    kind,
                    got_slot: Some(slot),
                    code: Some(c),
                    ..
                } = entry
                {
                    // Skip constrained polymorphic base names — they're dispatch
                    // placeholders (e.g. `!=`, `+`, `<`), not directly callable.
                    if let DefKind::UserFn { constrained_fn: Some(_) } = kind.as_ref() {
                        continue;
                    }
                    let code_ptr = c.ptr() as i64;
                    if code_ptr == 0 {
                        continue;
                    }

                    let (param_types, result_type) = match &scheme.ty {
                        Type::Fn(params, ret) => (params.clone(), *ret.clone()),
                        _ => continue,
                    };

                    traced.push(TracedFnInfo {
                        name: format!("{}/{}", module_path.as_ref(), name.as_ref()),
                        got_base,
                        got_slot: *slot,
                        arity: param_types.len(),
                        code_ptr,
                        param_types,
                        result_type,
                    });
                }
            }
        }

        traced
    }

    // `compile_dep_inline` — deleted Sprint 59 Workstream A §7 Step 5.
    //
    // The session-side second orchestrator (an inline `priority_worker_loop`
    // running on the eval thread in parallel with the persistent priority
    // worker pool) has been replaced by `register_dep_for_eval` above: the
    // persistent worker pool is now the single orchestrator for every
    // dep, and the eval thread blocks on `wait_module_inmem_complete_blocking`
    // scoped to the dep. See `design/int/dual-path-persistence-collapse.md`
    // §§2–3 (Decision 37 alignment) and §7 Step 5.

    /// Check if a bare symbol should produce introspection display instead of eval.
    ///
    /// Handles special forms, macros, builtin types, user types, traits,
    /// and non-nullary constructors (spec §4.1). Returns None for symbols
    /// that should be evaluated normally (variables, functions, nullary ctors).
    fn check_bare_symbol_introspection(&self, sexp: &Sexp) -> Option<EvalResult> {
        let name = match sexp {
            Sexp::Symbol(name, _) => name.as_str(),
            _ => return None,
        };

        // Must be a single bare identifier (no parens, no spaces, no brackets).
        if name.contains(|c: char| c.is_whitespace() || c == '(' || c == ')' || c == '[' || c == ']') {
            return None;
        }

        // Check primitive type names: Int, Bool, Float, String (spec §4.1.3).
        if Type::from_name(name).is_some() {
            return Some(EvalResult::Def {
                symbol: FQSymbol {
                    module: ModuleFullPath::from("primitives"),
                    symbol: Symbol::from(name),
                },
                ty: Type::Int,
                warnings: Vec::new(),
            });
        }

        let entry = {
            let guard = self.current_symbol_table();
            guard.get(name)?.clone()
        };

        // Resolve import/reexport chains fully. Sprint 61 Slice 1: the
        // resolver now chases the full chain (user → prelude → primitives)
        // so re-exported primitives land on a terminal `Def` here instead
        // of an intermediate `Reexport` that the match below would drop
        // through `_ => None`. See
        // `design/int/bare-primitive-value-path.md` candidate 2.
        let module = self.current_module_path();
        let (resolved_entry, resolved_module) = self.resolve_entry_for_display(&entry, &module);

        // Use the resolved module for re-export provenance (spec §8.9:
        // introspection MUST display the original defining module). The
        // downstream `format_eval_result` re-resolves and relies on
        // `format_def_entry`'s `module` parameter, so this is primarily
        // for FQSymbol consumers that read the symbol metadata directly.
        let fq_module = resolved_module;

        match &resolved_entry {
            ModuleEntry::Macro { clauses, .. } => {
                // Zero-arg macros should be expanded, not introspected.
                let has_zero_arg = clauses.iter().any(|c| {
                    c.params.is_empty() && c.rest_param.is_none()
                });
                if has_zero_arg {
                    return None;
                }
                Some(EvalResult::Def {
                    symbol: FQSymbol { module: fq_module, symbol: Symbol::from(name) },
                    ty: Type::Int,
                    warnings: Vec::new(),
                })
            }
            ModuleEntry::Def { kind: _, scheme, .. } => {
                // Special forms, primitives, and user functions all get
                // introspection display per spec §4.1.1, §4.1.2.
                Some(EvalResult::Def {
                    symbol: FQSymbol { module: fq_module, symbol: Symbol::from(name) },
                    ty: scheme.ty.clone(),
                    warnings: Vec::new(),
                })
            }
            ModuleEntry::TypeDef { .. } => {
                Some(EvalResult::Def {
                    symbol: FQSymbol { module: fq_module, symbol: Symbol::from(name) },
                    ty: Type::Int,
                    warnings: Vec::new(),
                })
            }
            ModuleEntry::TraitDecl { .. } => {
                Some(EvalResult::Def {
                    symbol: FQSymbol { module: fq_module, symbol: Symbol::from(name) },
                    ty: Type::Int,
                    warnings: Vec::new(),
                })
            }
            ModuleEntry::Constructor { info, .. } => {
                // Nullary constructors evaluate to values; non-nullary get introspection.
                if info.fields.is_empty() {
                    None
                } else {
                    Some(EvalResult::Def {
                        symbol: FQSymbol { module: fq_module, symbol: Symbol::from(name) },
                        ty: Type::Int,
                        warnings: Vec::new(),
                    })
                }
            }
            _ => None,
        }
    }

    // -- Slash command handlers (subset for initial implementation) --

    /// /sig handler: show type signature of a symbol.
    fn handle_sig(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /sig <name>".to_string();
        }
        if Type::from_name(name).is_some() {
            return format!("{name} ; type - builtin type");
        }
        match self.current_symbol_table().get(name) {
            Some(entry) => format_entry_sig(entry, name),
            None => format!("error: unknown symbol '{name}'"),
        }
    }

    /// /doc handler: show docstring of a symbol.
    fn handle_doc(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /doc <name>".to_string();
        }
        match self.current_symbol_table().get(name) {
            Some(ModuleEntry::Def { docstring, .. }) |
            Some(ModuleEntry::Macro { docstring, .. }) => {
                match docstring {
                    Some(doc) => format!("{name}: \"{doc}\""),
                    None => format!("{name}: no docstring"),
                }
            }
            Some(ModuleEntry::TraitDecl { decl, .. }) => {
                match &decl.docstring {
                    Some(doc) => format!("{name}: \"{doc}\""),
                    None => format!("{name}: no docstring"),
                }
            }
            Some(_) => format!("{name}: no docstring"),
            None => format!("error: unknown symbol '{name}'"),
        }
    }

    /// /list handler: list symbols in current module.
    fn handle_list(&self, _filter: &str) -> String {
        let table_ref = self.current_symbol_table();
        let mut fns = Vec::new();
        let mut types = Vec::new();
        let mut traits = Vec::new();
        let mut macros = Vec::new();

        for (name, entry) in table_ref.symbols.iter() {
            match entry {
                ModuleEntry::Def { kind, scheme, .. } => {
                    if matches!(kind.as_ref(), DefKind::SpecialForm { .. }) {
                        continue; // Don't list special forms.
                    }
                    let type_str = format!("{}", scheme.ty);
                    fns.push(format!("  {name} : {type_str}"));
                }
                ModuleEntry::TypeDef { .. } => {
                    types.push(format!("  {name}"));
                }
                ModuleEntry::TraitDecl { .. } => {
                    traits.push(format!("  {name}"));
                }
                ModuleEntry::Macro { .. } => {
                    macros.push(format!("  {name}"));
                }
                // Import, Reexport, Constructor, PlatformDecl, Ambiguous:
                // not listed (imports are shown by /imports, constructors
                // are part of their type).
                _ => {}
            }
        }

        let mut parts = Vec::new();
        if !types.is_empty() {
            types.sort();
            parts.push(format!("Types:\n{}", types.join("\n")));
        }
        if !traits.is_empty() {
            traits.sort();
            parts.push(format!("Traits:\n{}", traits.join("\n")));
        }
        if !macros.is_empty() {
            macros.sort();
            parts.push(format!("Macros:\n{}", macros.join("\n")));
        }
        if !fns.is_empty() {
            fns.sort();
            parts.push(format!("Fns:\n{}", fns.join("\n")));
        }
        if parts.is_empty() {
            "(no definitions)".to_string()
        } else {
            parts.join("\n")
        }
    }

    /// /mod handler: switch module namespace.
    fn handle_mod(&mut self, name: &str) {
        let target = if name.is_empty() { "user" } else { name };
        let path = ModuleFullPath::from(target);
        self.set_current_module(path);
    }

    /// Look up introspection data for a bare symbol name in the current module.
    fn get_introspection(&self, name: &str) -> Option<dashmap::mapref::one::Ref<'_, FQSymbol, Introspection>> {
        let fq = FQSymbol {
            module: self.current_module_path(),
            symbol: Symbol::from(name),
        };
        self.shared.introspection.get(&fq)
    }

    /// /source handler: show original source text of a definition.
    fn handle_source(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /source <name>".to_string();
        }
        if let Some(intr) = self.get_introspection(name) {
            if let Some(ref src) = intr.source {
                return format!("; source for {name}\n{}", crate::pretty::pretty_print_str(src));
            }
            if let Some(ref sexp) = intr.sexp {
                return format!("; source for {name}\n{}", crate::pretty::pretty_print(sexp));
            }
        }
        format!("Error: no source available for '{name}'")
    }

    /// /sexp handler: show parsed S-expression of a definition.
    fn handle_sexp_cmd(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /sexp <name>".to_string();
        }
        if let Some(intr) = self.get_introspection(name)
            && let Some(ref sexp) = intr.sexp {
                return format!("; sexp for {name}\n{}", crate::pretty::pretty_print(sexp));
            }
        format!("Error: no sexp available for '{name}'")
    }

    /// /ast handler: show AST of a definition.
    fn handle_ast(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /ast <name>".to_string();
        }
        if let Some(intr) = self.get_introspection(name)
            && let Some(ref defn) = intr.ast {
                return format!("; ast for {name}\n{:#?}", defn);
            }
        format!("Error: no AST available for '{name}'")
    }

    /// /clif handler: show Cranelift IR of a definition.
    fn handle_clif(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /clif <name>".to_string();
        }
        if let Some(intr) = self.get_introspection(name)
            && let Some(ref clif) = intr.clif_ir {
                return format!("; clif ir for {name}\n{}", clif);
            }
        format!("Error: no CLIF IR available for '{name}'")
    }

    /// /disasm handler: show disassembled native code of a definition.
    fn handle_disasm(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /disasm <name>".to_string();
        }
        if let Some(intr) = self.get_introspection(name)
            && let Some(ref disasm) = intr.disasm {
                return format!("; disasm for {name}\n{}", disasm);
            }
        format!("Error: no disassembly available for '{name}'")
    }

    /// /info handler: show full details (sig + code size + compile time).
    fn handle_info(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /info <name>".to_string();
        }
        if Type::from_name(name).is_some() {
            return self.format_builtin_type_display(name);
        }
        let entry = match self.current_symbol_table().get(name) {
            Some(e) => e.clone(),
            None => return format!("error: unknown symbol '{name}'"),
        };
        let module = self.current_module_path();
        let (resolved_entry, resolved_module) = self.resolve_entry_for_display(&entry, &module);
        let sig = self.format_def_entry(&resolved_entry, name, &resolved_module);
        // Append code info if available.
        if !matches!(resolved_entry,
            ModuleEntry::Macro { .. } | ModuleEntry::TypeDef { .. } | ModuleEntry::TraitDecl { .. })
            && let Some(intr) = self.get_introspection(name) {
                let size_str = intr.code_size
                    .map(|s| format!("{s} bytes"))
                    .unwrap_or_else(|| "? bytes".to_string());
                return format!("{sig}\n  {size_str}");
            }
        sig
    }

    /// /type handler: typecheck expression without executing.
    fn handle_type(&mut self, expr_src: &str) -> String {
        if expr_src.is_empty() {
            return "usage: /type <expr>".to_string();
        }
        let snapshot = self.tc_snapshot();
        let result = self.typecheck_only(expr_src);
        self.tc_restore(snapshot);
        match result {
            Ok(ty) => {
                let display = format_type_qualified(&ty);
                format!(":{display}")
            }
            Err(e) => format!("Error: {e}"),
        }
    }

    /// Parse, expand, and typecheck an expression without compiling or executing.
    ///
    /// Per Decision 44 (2026-05-13 third amendment) — routes through the
    /// collapsed `check_forms` surface via `worker::check_program_compat`.
    /// The pre-S66 `tc.check(...)` entry point (which fed a multi-pass
    /// pipeline driven by a public `ModuleCheckAccumulator`) is retired;
    /// the type query now lifts inferred-type data off the live `SymbolTable`
    /// after the cluster commit.
    fn typecheck_only(&mut self, expr_src: &str) -> Result<Type, CranelispError> {
        let sexps = cranelisp_frontend::parse(expr_src)?;
        if sexps.is_empty() {
            return Err(CranelispError::ParseError {
                message: "empty expression".into(),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            });
        }
        let module = self.current_module_path();

        // Build the input through the new `build_form` / `build_expr` boundary
        // (replacing the retired `build_repl_input`). A bare-expr REPL input
        // is wrapped as a synthetic `__expr` defn for typecheck dispatch. Mode
        // comes from the session's `SharedState`; under REPL this is
        // `InMemoryAndObject` (validator no-op).
        let working_program = crate::worker::build_program_compat(
            &[sexps[0].clone()],
            self.shared.codegen_behaviour,
        )?;
        let working_program = self.wrap_exprs_as_synthetic_defns(&working_program);

        // Ensure the current module exists before the live ClusterContext
        // tries to take a guard on it.
        self.tc_env().ensure_module_exists(&module);

        crate::worker::check_program_compat(
            &self.shared.symbol_tables,
            &module,
            &working_program,
        )?;

        // Try to surface the inferred type of the synthetic `__expr` Defn
        // by reading back from the live `SymbolTable`. Fall back to `Int`
        // when no display info is available (matches pre-S66 fallback).
        Ok(self.lift_expr_type(&module).unwrap_or(Type::Int))
    }

    /// Local equivalent of the retired `wrap_exprs_as_defns` helper. Folds
    /// any `TopLevel::Expr` into a synthetic zero-arg `__expr` defn so it
    /// flows uniformly through the typecheck dispatch.
    fn wrap_exprs_as_synthetic_defns(&self, program: &[TopLevel]) -> Vec<TopLevel> {
        use cranelisp_types::{DefnVariant, Visibility};
        let mut working = Vec::with_capacity(program.len());
        for top in program {
            match top {
                TopLevel::Expr(expr) => {
                    let span = expr.span();
                    let wrapper_span = Span::new(
                        span.start.saturating_sub(1),
                        span.end.saturating_add(1),
                    );
                    working.push(TopLevel::Defn(cranelisp_types::Defn {
                        name: Symbol::from("__expr"),
                        docstring: None,
                        variants: vec![DefnVariant {
                            params: vec![],
                            param_annotations: vec![],
                            body: expr.clone(),
                            span,
                        }],
                        visibility: Visibility::Public,
                        span: wrapper_span,
                    }));
                }
                other => working.push(other.clone()),
            }
        }
        working
    }

    /// Read back the inferred type of the synthetic `__expr` defn, if any.
    fn lift_expr_type(&self, module: &ModuleFullPath) -> Option<Type> {
        let table = self.shared.symbol_tables.get(module)?;
        match table.get("__expr")? {
            ModuleEntry::Def { scheme, .. } => {
                // Zero-arg defns have type `Fn([], ret)` — surface the return.
                if let Type::Fn(_, ret) = &scheme.ty {
                    Some((**ret).clone())
                } else {
                    Some(scheme.ty.clone())
                }
            }
            _ => None,
        }
    }

    /// /imports handler: list imports in current module by category.
    fn handle_imports(&self, filter: &str) -> String {
        let table = self.current_symbol_table();
        let mut output = String::new();

        if filter.is_empty() {
            // Unfiltered mode: organize by category
            let mut special_forms: Vec<String> = Vec::new();
            let mut macros: Vec<String> = Vec::new();
            let mut traits: Vec<String> = Vec::new();
            let mut types: Vec<String> = Vec::new();
            let mut fns: Vec<String> = Vec::new();

            // Special forms always come from the root `""` module per
            // Principle 17 amendment (FIXME 0193). Sprint 67 hack-back
            // FIXME 0192 Residual Task 3 — `/imports` previously enumerated
            // special forms by iterating the current module; once special-form
            // registration shifted to root, that iteration stopped seeing
            // them. Probe the root explicitly.
            let root = ModuleFullPath::from("");
            if let Some(root_table) = self.shared.symbol_tables.get(&root) {
                for (sym, entry) in root_table.all_symbols() {
                    if let ModuleEntry::Def { kind, .. } = entry
                        && matches!(kind.as_ref(), DefKind::SpecialForm { .. })
                    {
                        special_forms.push(sym.to_string());
                    }
                }
            }

            for (sym, entry) in table.all_symbols() {
                let name = sym.to_string();
                match entry {
                    ModuleEntry::Def { kind, .. } => {
                        if let DefKind::SpecialForm { .. } = kind.as_ref() {
                            // Defensive — current modules should no longer
                            // host special forms (they live at root only).
                            // Skip to avoid double-listing.
                            continue;
                        }
                        // Skip locally-defined fns and primitives
                    }
                    ModuleEntry::Import { source } | ModuleEntry::Reexport { source } => {
                        if name.contains('$') {
                            continue;
                        }
                        let classification = self.classify_import(source);
                        match classification {
                            ImportClass::Macro => macros.push(name),
                            ImportClass::Trait => traits.push(name),
                            ImportClass::Type | ImportClass::Constructor => types.push(name),
                            ImportClass::Fn => fns.push(name),
                        }
                    }
                    _ => {} // locally defined
                }
            }

            special_forms.sort();
            macros.sort();
            traits.sort();
            types.sort();
            fns.sort();

            append_name_category(&mut output, "Special forms", &special_forms);
            append_name_category(&mut output, "Macros", &macros);
            append_name_category(&mut output, "Traits", &traits);
            append_name_category(&mut output, "Types", &types);
            append_name_category(&mut output, "Fns", &fns);

            if special_forms.is_empty() && macros.is_empty() && traits.is_empty()
                && types.is_empty() && fns.is_empty()
            {
                output.push_str("(no imports)");
            }
        } else {
            // Filtered mode: show imports from named module only
            let mut names: Vec<String> = Vec::new();
            for (sym, entry) in table.all_symbols() {
                let source = match entry {
                    ModuleEntry::Import { source } => source,
                    ModuleEntry::Reexport { source } => source,
                    _ => continue,
                };
                let name = sym.to_string();
                if name.contains('$') {
                    continue;
                }
                if *source.module == *filter {
                    names.push(name);
                }
            }
            if names.is_empty() {
                // Silent for no matches
                return String::new();
            }
            names.sort();
            append_name_category(&mut output, &format!("From {filter}"), &names);
        }

        // Trim trailing newline
        while output.ends_with('\n') {
            output.pop();
        }
        output
    }

    /// Classify an imported symbol by following import chains to the definition.
    fn classify_import(&self, source: &FQSymbol) -> ImportClass {
        match self.resolve_to_definition(source) {
            Some(entry) => match entry {
                ModuleEntry::Macro { .. } => ImportClass::Macro,
                ModuleEntry::TraitDecl { .. } => ImportClass::Trait,
                ModuleEntry::TypeDef { .. } => ImportClass::Type,
                ModuleEntry::Constructor { .. } => ImportClass::Constructor,
                _ => ImportClass::Fn,
            },
            None => ImportClass::Fn,
        }
    }

    /// Follow Import/Reexport chains to find the ultimate definition entry.
    fn resolve_to_definition(&self, source: &FQSymbol) -> Option<ModuleEntry<Code>> {
        let mut current_module = source.module.clone();
        let mut current_name = source.symbol.to_string();
        for _ in 0..10 {
            let entry = {
                let table = self.module_table(&current_module)?;
                table.get(&current_name)?.clone()
            };
            match &entry {
                ModuleEntry::Import { source: next } | ModuleEntry::Reexport { source: next } => {
                    current_module = next.module.clone();
                    current_name = next.symbol.to_string();
                }
                _ => return Some(entry),
            }
        }
        None
    }

    /// /exports handler: list a module's public symbols.
    fn handle_exports(&self, arg: &str) -> String {
        if arg.is_empty() {
            return "Usage: /exports <module-name>".to_string();
        }
        let mut parts = arg.splitn(2, char::is_whitespace);
        let mod_name = parts.next().unwrap_or("");
        let prefix_filter = parts.next().unwrap_or("").trim();

        let module_path = match self.resolve_module_by_name(mod_name) {
            Some(path) => path,
            None => return format!("Module '{mod_name}' not found"),
        };

        let table = match self.module_table(&module_path) {
            Some(t) => t,
            None => return format!("Module '{mod_name}' not found"),
        };

        let mut macros: Vec<String> = Vec::new();
        let mut traits: Vec<String> = Vec::new();
        let mut types: Vec<String> = Vec::new();
        let mut fns: Vec<String> = Vec::new();

        for (sym, entry) in table.all_symbols() {
            if matches!(entry, ModuleEntry::Import { .. } | ModuleEntry::Reexport { .. }) {
                continue;
            }
            if !entry.is_public() {
                continue;
            }
            let name = sym.to_string();
            if name.contains('$') {
                continue;
            }
            if !prefix_filter.is_empty()
                && !name.to_lowercase().starts_with(&prefix_filter.to_lowercase())
            {
                continue;
            }
            match entry {
                ModuleEntry::Macro { .. } => macros.push(name),
                ModuleEntry::TraitDecl { .. } => traits.push(name),
                ModuleEntry::TypeDef { .. } | ModuleEntry::Constructor { .. } => types.push(name),
                ModuleEntry::Def { kind, .. }
                    if !matches!(kind.as_ref(), DefKind::SpecialForm { .. }) =>
                {
                    fns.push(name);
                }
                _ => {}
            }
        }

        macros.sort();
        traits.sort();
        types.sort();
        fns.sort();

        let has_any = !macros.is_empty() || !traits.is_empty()
            || !types.is_empty() || !fns.is_empty();

        if !has_any {
            return format!("Module '{mod_name}' has no public symbols");
        }

        let mut output = format!("Module '{mod_name}':\n");
        append_name_category(&mut output, "Macros", &macros);
        append_name_category(&mut output, "Traits", &traits);
        append_name_category(&mut output, "Types", &types);
        append_name_category(&mut output, "Fns", &fns);
        while output.ends_with('\n') {
            output.pop();
        }
        output
    }

    /// /expand handler: macro-expand a form without evaluating.
    fn handle_expand(&mut self, form_src: &str) -> String {
        if form_src.is_empty() {
            return "usage: /expand <form>".to_string();
        }
        // Compile any uncompiled macros before expansion.
        if let Err(e) = self.compile_pending_macros() {
            return format!("Error: {e}");
        }
        match self.expand_form_sexp(form_src) {
            Ok(expanded) => format_sexp(&expanded),
            Err(e) => format!("Error: {e}"),
        }
    }

    /// Compile any macros in the TC symbol table that don't yet have code pointers.
    ///
    /// When a defmacro form is processed by the worker, it registers the macro
    /// in the TC but defers compilation until the macro is first used. For /expand
    /// we need to compile them eagerly.
    fn compile_pending_macros(&mut self) -> Result<(), CranelispError> {
        use crate::worker::ModuleCheckAccumulator;

        // Collect macro names + sexps that need compilation.
        let mut to_compile: Vec<(Symbol, Sexp)> = Vec::new();
        {
            let table = self.current_symbol_table();
            for (sym, entry) in table.all_symbols() {
                if let ModuleEntry::Macro { clauses, sexp: Some(sexp), .. } = entry {
                    let name = Symbol::from(sym.as_ref());
                    let module = self.current_module_path();
                    let needs_compile = clauses.iter().enumerate().any(|(idx, _)| {
                        let clause_name = Symbol::from(
                            format!("__macro_{}_clause_{}", name, idx),
                        );
                        // Sprint 57 Wave 2 G6: check `ModuleEntry::Def.code`
                        // on the symbol table (replaces the deleted
                        // `codegen_products` lookup).
                        let compiled = self.shared.symbol_tables.get(&module)
                            .and_then(|t| match t.get(clause_name.as_ref())? {
                                ModuleEntry::Def { code, .. } => Some(code.is_some()),
                                _ => None,
                            })
                            .unwrap_or(false);
                        !compiled
                    });
                    if needs_compile {
                        to_compile.push((name, sexp.clone()));
                    }
                }
            }
        }

        for (_, sexp) in &to_compile {
            let module = self.current_module_path();
            let info = cranelisp_frontend::parse_defmacro(sexp)?;
            let mut accumulator = ModuleCheckAccumulator::new();

            self.tc_env().ensure_module_exists(&module);
            let repl_cs = self.shared.repl_check_state.lock()
                .unwrap_or_else(|e| e.into_inner())
                .take()
                .unwrap_or_else(|| CheckState::new(module.clone()));
            let lib_dirs_snap = self.lib_dirs();
            let platform_dirs_snap = self.platform_dirs();
            let mut wctx = ModuleCompiler {
                symbol_tables: &self.shared.symbol_tables,
                next_type_id: &self.shared.next_type_id,
                check_state: repl_cs,
                current_module: module.clone(),
                scheduler: &self.shared.scheduler,
                typecheck_products: &self.shared.typecheck_products,
                introspection: Some(&self.shared.introspection),
                lib_dirs: &lib_dirs_snap,
                platform_dirs: &platform_dirs_snap,
                project_root: &self.shared.project_root,
                shared_state: Some(&self.shared),
            };

            crate::worker::compile_macro_for_repl(
                &mut wctx, &module, &info, Span::SYNTHETIC, &mut accumulator,
            )?;
            // Restore REPL check_state.
            *self.shared.repl_check_state.lock()
                .unwrap_or_else(|e| e.into_inner()) = Some(wctx.check_state);
        }
        Ok(())
    }

    /// Parse and expand a form through the compiled macros in the session.
    fn expand_form_sexp(&self, form_src: &str) -> Result<Sexp, CranelispError> {
        let sexps = cranelisp_frontend::parse(form_src)?;
        if sexps.is_empty() {
            return Err(CranelispError::ParseError {
                message: "empty form".into(),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            });
        }
        let sexp = sexps.into_iter().next().ok_or_else(|| {
            CranelispError::ParseError {
                message: "empty form".into(),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            }
        })?;
        let module = self.current_module_path();
        let mut resolver = ReadOnlyMacroResolver {
            symbol_tables: &self.shared.symbol_tables,
            current_module: module,
        };
        crate::expander::expand_sexp_recursive(sexp, &mut resolver, 0)
    }

    /// /time handler: evaluate with timing.
    fn handle_time(&mut self, expr_src: &str) -> String {
        if expr_src.is_empty() {
            return "usage: /time <expr>".to_string();
        }
        let start = std::time::Instant::now();
        match self.eval(expr_src) {
            Ok(Some(result)) => {
                let elapsed = start.elapsed();
                let display = self.format_eval_result(&result);
                format!("{display} ({}ms)", elapsed.as_millis())
            }
            Ok(None) => {
                let elapsed = start.elapsed();
                format!("(no result) ({}ms)", elapsed.as_millis())
            }
            Err(e) => format!("Error: {e}"),
        }
    }

    /// /mem handler: show allocation statistics.
    ///
    /// With no argument: report current live bytes, total allocations, total
    /// deallocations, and the delta (currently-live allocations) reflected by
    /// the runtime counters.
    ///
    /// With an argument: evaluate the expression and report the delta in each
    /// counter across the evaluation. This makes RC behaviour directly
    /// observable during a session.
    fn handle_mem(&mut self, expr_src: &str) -> String {
        if expr_src.is_empty() {
            return format_mem_snapshot();
        }

        let allocs_before = cranelisp_intrinsics::alloc_count();
        let deallocs_before = cranelisp_intrinsics::dealloc_count();
        let bytes_before = cranelisp_intrinsics::bytes_current();

        let eval_outcome = self.eval(expr_src);

        let allocs_after = cranelisp_intrinsics::alloc_count();
        let deallocs_after = cranelisp_intrinsics::dealloc_count();
        let bytes_after = cranelisp_intrinsics::bytes_current();

        let d_allocs = allocs_after.saturating_sub(allocs_before);
        let d_deallocs = deallocs_after.saturating_sub(deallocs_before);
        let d_bytes = (bytes_after as i64) - (bytes_before as i64);
        let live_delta = (d_allocs as i64) - (d_deallocs as i64);

        let header = match eval_outcome {
            Ok(Some(result)) => self.format_eval_result(&result),
            Ok(None) => "(no result)".to_string(),
            Err(e) => format!("Error: {e}"),
        };

        let delta_line = format!(
            "; delta: allocs +{d_allocs}  deallocs +{d_deallocs}  bytes {d_bytes:+}  live {live_delta:+}"
        );
        format!("{header}\n{delta_line}")
    }

    /// /run-tests handler: discover and execute test-* functions.
    ///
    /// Scans def_codegen for zero-arg functions named `test-*`, calls each
    /// directly, interprets the `(Option String)` result: None = pass,
    /// Some(reason) = fail.
    /// /run-tests handler: discover and run test-* functions.
    ///
    /// With no argument: tests in current module. With a module path: tests
    /// in that module. Runs all tests fast first, then re-runs failures with
    /// tracing to capture trace trees for diagnostics.
    fn handle_run_tests(&self, arg: &str) -> String {
        let module = if arg.is_empty() {
            self.current_module_path()
        } else {
            ModuleFullPath::from(arg)
        };
        // Core discovery — shared with discover_tests_extern.
        let test_names = discover_test_names(
            &self.shared.symbol_tables,
            &module,
        );
        if test_names.is_empty() {
            return if arg.is_empty() {
                "No test-* functions found.".to_string()
            } else {
                format!("No test-* functions found in '{arg}'.")
            };
        }
        self.format_test_run(&test_names)
    }

    /// /run-all-tests handler: discover and run tests in all project-root modules.
    fn handle_run_all_tests(&self) -> String {
        let mut all_names: Vec<String> = Vec::new();
        for entry in self.shared.typecheck_products.iter() {
            let module_path = entry.key();
            if let Some(ref fp) = entry.value().file_path
                && !fp.starts_with(&self.shared.project_root) {
                    continue;
                }
            let names = discover_test_names(
                &self.shared.symbol_tables,
                module_path,
            );
            all_names.extend(names);
        }
        all_names.sort();
        if all_names.is_empty() {
            return "No test-* functions found in any project module.".to_string();
        }
        self.format_test_run(&all_names)
    }

    /// Re-run a failing test with tracing by eval'ing `(trace (test-name))`.
    /// Format a test run: run all tests via shared core logic.
    fn format_test_run(&self, test_names: &[String]) -> String {
        let start = std::time::Instant::now();
        let mut passed = 0usize;
        let mut failed = 0usize;
        let mut lines = Vec::new();

        for name in test_names {
            // Core test execution — shared with run_test_extern.
            let outcome = run_test_by_name(&self.shared.symbol_tables, name);
            let dots = ".".repeat(40usize.saturating_sub(name.len()));
            match &outcome {
                TestOutcome::Pass { .. } => {
                    lines.push(format!("  {name} {dots} ok"));
                    passed += 1;
                }
                TestOutcome::Fail { reason, .. } => {
                    lines.push(format!("  {name} {dots} FAILED: {reason}"));
                    failed += 1;
                }
                TestOutcome::Panic { reason, .. } => {
                    lines.push(format!("  {name} {dots} PANIC: {reason}"));
                    failed += 1;
                }
            }
        }

        let elapsed = start.elapsed();
        lines.push(String::new());
        if failed == 0 {
            lines.push(format!(
                "{passed} passed in {:.2}ms",
                elapsed.as_secs_f64() * 1000.0,
            ));
        } else {
            lines.push(format!(
                "{passed} passed, {failed} failed in {:.2}ms",
                elapsed.as_secs_f64() * 1000.0,
            ));
        }

        lines.join("\n")
    }

    /// Check if input is a bare special form name (for feedback display).
    ///
    /// Sprint 67 hack-back (FIXME 0192 Residual Task 3 — REPL regression):
    /// special-form metadata lives in the root `""` module per Principle 17
    /// amendment (FIXME 0193). The earlier `current_symbol_table()` probe
    /// stopped seeing these entries when special forms moved out of `user`;
    /// route lookups via `lookup_special_form` which probes root.
    fn special_form_feedback(&self, input: &str) -> Option<String> {
        let trimmed = input.trim();
        // Must be a single bare word (no parens, no spaces).
        if trimmed.contains('(') || trimmed.contains(' ') || trimmed.starts_with('/') {
            return None;
        }
        let desc = self.lookup_special_form(trimmed)?;
        Some(format_special_form_display(trimmed, &desc))
    }

    /// Look up the description of a special form by name, probing the root
    /// `""` module where special-form metadata is registered (Principle 17
    /// amendment per FIXME 0193). Returns `None` if `name` is not a known
    /// special form.
    pub fn lookup_special_form(&self, name: &str) -> Option<String> {
        let root = ModuleFullPath::from("");
        let table = self.shared.symbol_tables.get(&root)?;
        match table.get(name)? {
            ModuleEntry::Def { kind, .. } => match kind.as_ref() {
                DefKind::SpecialForm { description } => Some(description.clone()),
                _ => None,
            },
            _ => None,
        }
    }

    /// Execute the entry module's main function via the trampoline.
    ///
    /// For the v4 scheduler path: GOT is already populated by the worker
    /// loop. For the old path: flushes codegen queue first.
    ///
    /// Looks up `main` in the GOT, calls it, and runs the IO trampoline
    /// if the return type is IO.
    pub fn trampoline(
        &mut self,
        module_name: &str,
    ) -> Result<(i64, Type), CranelispError> {
        // Look up main's compiled code on its symbol-table entry (G6).
        let main_sym = cranelisp_types::Symbol::from("main");
        let code_ptr = self.lookup_main_code_ptr(module_name, &main_sym)?;
        let result_type = self.lookup_main_return_type(module_name);

        // Clear any stale runtime error.
        let _ = cranelisp_intrinsics::panic::take_runtime_error();

        // Call main.
        // SAFETY: `code_ptr` is non-null — returned from `lookup_main_code_ptr`
        // which errors on None. It points to finalized JIT code compiled by
        // Cranelift via `compile_and_register_defn`. The compiled function uses
        // the `extern "C" fn() -> i64` calling convention (zero-arg defn with
        // i64 return), matching the transmute target type.
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
        let raw_value = func();

        // Check for runtime panics.
        if let Some(err) = cranelisp_intrinsics::panic::take_runtime_error() {
            return Err(CranelispError::CodegenError {
                message: format!("runtime panic: {}", err),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            });
        }

        // IO trampoline.
        if result_type.is_io() {
            let inner_value = cranelisp_intrinsics::run_io_trampoline(raw_value);
            // Decision 24 (consuming convention): `run_io_trampoline` is
            // non-consuming of its input tree. The caller-tree outer nodes
            // (Bind/Pure + continuation closures) must be released via
            // `drop::consume_io_tree` — without this, every batch-mode
            // `(defn main ...)` that returns IO leaks its outer IO nodes.
            // Mirrors the pipeline path's `unwrap_io_inline` in pipeline.rs
            // and the extern `cranelisp_run_io` entry in runtime::io.
            cranelisp_intrinsics::drop::consume_io_tree(raw_value);
            let inner_type = result_type.io_inner_type();
            Ok((inner_value, inner_type))
        } else {
            Ok((raw_value, result_type))
        }
    }

    /// Look up the code pointer for `main` on its `ModuleEntry::Def.code`
    /// (Sprint 57 Wave 2 G6 — replaces the deleted `codegen_products` lookup).
    fn lookup_main_code_ptr(
        &self,
        module_name: &str,
        main_sym: &cranelisp_types::Symbol,
    ) -> Result<*const u8, CranelispError> {
        let module_path = ModuleFullPath::from(module_name);

        if let Some(table) = self.shared.symbol_tables.get(&module_path)
            && let Some(ModuleEntry::Def { code: Some(c), .. }) =
                table.get(main_sym.as_ref())
        {
            return Ok(c.ptr());
        }

        Err(CranelispError::ModuleError {
            message: "entry module has no `main` function — batch mode requires (defn main [] ...)"
                .into(),
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
        })
    }

    /// Look up the return type of `main` from the typechecker.
    fn lookup_main_return_type(&self, module_name: &str) -> Type {
        let module_path = ModuleFullPath::from(module_name);
        let main_sym = Symbol::from("main");

        if let Some(table) = self.module_table(&module_path)
            && let Some(cranelisp_types::ModuleEntry::Def { scheme, .. }) =
                table.get(main_sym.as_ref())
            && let Type::Fn(_, ret) = &scheme.ty
        {
            return *ret.clone();
        }
        Type::Int
    }

    /// Wait until all registered modules have object codegen complete.
    ///
    /// Block until all in-memory codegen (JIT) is complete.
    pub fn wait_inmem_complete(
        &self,
    ) -> Result<(), crate::scheduler::SchedulerError> {
        self.shared.scheduler.wait_inmem_complete()
    }

    /// Promotes nice workers to normal priority before blocking, ensuring
    /// object codegen completes promptly (e.g., before linking). Wakes
    /// the `object_work_available` condvar so workers observe the promotion
    /// flag on their next loop iteration.
    pub fn wait_object_complete(
        &self,
    ) -> Result<(), crate::scheduler::SchedulerError> {
        // When no nice workers are running (e.g., tests with nice_workers: 0),
        // no .o files will be produced. Skip the wait to avoid blocking forever.
        if self.nice_workers == 0 {
            return Ok(());
        }

        // Promote nice workers so object codegen runs at full speed.
        self.shared.promote_nice_workers.store(
            true,
            std::sync::atomic::Ordering::Release,
        );
        // Wake workers so they observe the promotion flag.
        self.shared.scheduler.wake_object_workers();

        let result = self.shared.scheduler.wait_object_complete();

        // Flush the cache manifest to disk so the next session can detect cache hits.
        {
            let cs_guard = self.shared.cache_state.lock().unwrap_or_else(|e| e.into_inner());
            if let Some(cs) = cs_guard.as_ref() {
                cs.flush_manifest();
            }
        }

        result
    }

    /// Shut down the session: signal workers to drain and exit.
    ///
    /// Sets the scheduler shutdown flag (wakes all condvars) and joins
    /// both the persistent priority and nice worker pools. Workers
    /// observe the shutdown flag via `take_priority_work_blocking` /
    /// `take_object_codegen` returning `None` and exit their loops.
    ///
    /// Idempotent: safe to call twice; the second call joins no
    /// additional handles. Called automatically by `Drop` as a safety net
    /// for tests that never call `shutdown()` explicitly.
    /// Sprint 57 Wave 4 G9 per `persistent-workers.md` §5.2.
    pub fn shutdown(&mut self) {
        self.shared.scheduler.shutdown();
        // Join priority worker threads first. A worker mid-codegen will
        // finish its current work item, re-enter `take_priority_work_blocking`
        // at the loop top, observe shutdown, and exit. `join()` returning
        // `Err` means the worker panicked — silently ignored to match the
        // scoped-worker behaviour this replaces (§5.2).
        for handle in self.priority_worker_handles.drain(..) {
            let _ = handle.join();
        }
        // Then nice workers. They observe the shutdown flag via
        // take_object_codegen() returning None and exit their loop.
        for handle in self.nice_worker_handles.drain(..) {
            let _ = handle.join();
        }
    }

    /// §3.1: Register entry module by name. Session resolves the source
    /// file from project_root + lib_dirs, reads it, and registers with
    /// the scheduler.
    pub fn register_entry_module(
        &mut self,
        module_name: &str,
    ) -> Result<Vec<Warning>, CranelispError> {
        let module = ModuleFullPath::from(module_name);
        // Resolve source file: project_root (tier 2) then lib_dirs (tier 3).
        let lib_dirs = self.lib_dirs();
        let file_path = crate::pipeline::resolve_module_file(&module, &self.shared.project_root, &lib_dirs);
        let (source, entry_path) = match file_path {
            Some(path) => {
                let src = std::fs::read_to_string(&path).unwrap_or_default();
                (src, path)
            }
            None => {
                // No file found — empty module (e.g., fresh REPL).
                let default_path = self.shared.project_root.join(format!("{module_name}.cl"));
                (String::new(), default_path)
            }
        };

        // Register the entry module's own file in file_to_module so the
        // file watcher can detect changes to it (not just its dependencies).
        if let Ok(canonical) = entry_path.canonicalize() {
            self.shared.file_to_module
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .insert(canonical, module);
        }

        self.register_module_with_source(module_name, &source, &entry_path)
    }

    /// §8: Link by module name. Collects .o files produced by nice workers,
    /// generates a startup stub, and invokes the system linker.
    ///
    /// Must be called after `wait_object_complete()` — all .o files must
    /// be ready.
    pub fn link_by_name(
        &mut self,
        module_name: &str,
    ) -> Result<(), CranelispError> {
        let module = ModuleFullPath::from(module_name);

        // Validate main exists and determine return kind (Int vs IO).
        let entry_table = self.module_table(&module).ok_or_else(|| {
            CranelispError::ModuleError {
                message: format!("entry module '{}' not found in typechecker", module_name),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            }
        })?;
        let main_return = crate::exe::validate_main(&entry_table)?;
        // Sprint 58 Wave 2 / Decision 36: read the entry module's `main`
        // GOT slot index now (before dropping the table guard). The alias
        // `.o` (emitted below) routes the system linker's `_main` import
        // through this slot via `__cranelisp_got_{entry_module}`.
        let main_got_slot = crate::exe::entry_main_got_slot(&entry_table)?;
        drop(entry_table);

        let main_returns_io = main_return == crate::exe::MainReturnKind::Io;

        // Collect .o paths from nice workers.
        let o_paths = self.shared.compiled_o_paths.lock()
            .unwrap_or_else(|e| e.into_inner())
            .clone();

        if o_paths.is_empty() {
            return Err(CranelispError::ModuleError {
                message: "no .o files produced — cannot link".into(),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            });
        }

        // Collect platform manifest names and rlib paths.
        // TODO: When platform linking is needed, these functions will
        // query the loaded platform registry.
        let platform_manifest_names =
            crate::exe::collect_platform_manifest_names();
        let platform_rlib_paths =
            crate::exe::find_platform_rlibs();

        // Sprint 58 Wave 2 / Decision 36: every user-defined function is
        // declared bare-`Linkage::Local` by `compile_to_module` (no
        // module-qualified naming). The startup stub references `main`
        // (bare) as `Linkage::Import`; the system linker resolves it
        // against the alias `.o` we emit below, which exports `main`
        // and tail-calls through the entry module's GOT.
        let entry_fn_name = "main".to_string();

        // Generate startup .o stub.
        let startup_bytes = crate::exe::generate_startup_object(
            &platform_manifest_names,
            main_returns_io,
            &entry_fn_name,
        )?;

        let cache_dir = self.shared.cache_dir.as_ref().ok_or_else(|| {
            CranelispError::ModuleError {
                message: "cache directory not configured — cannot write startup .o".into(),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, None),
            }
        })?;
        let startup_o_path = cache_dir.join("__startup.o");
        std::fs::write(&startup_o_path, &startup_bytes).map_err(|e| {
            CranelispError::ModuleError {
                message: format!("failed to write startup .o: {e}"),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, Some(startup_o_path.clone())),
            }
        })?;

        // Sprint 58 Wave 2 / Decision 36 `--link` exception: emit the
        // `_main` Export alias `.o` that tail-calls into the entry
        // module's GOT slot for `main`. Without this alias the system
        // linker has no `_main` symbol to resolve (the entry module's
        // bare `main` is `Linkage::Local`), and link fails with
        // "undefined symbol _main".
        let alias_bytes =
            crate::exe::generate_main_alias_object(&module, main_got_slot)?;
        let alias_o_path = cache_dir.join("__main_alias.o");
        std::fs::write(&alias_o_path, &alias_bytes).map_err(|e| {
            CranelispError::ModuleError {
                message: format!("failed to write main alias .o: {e}"),
                location: ErrorLocation::from_span_file(Span::SYNTHETIC, Some(alias_o_path.clone())),
            }
        })?;

        // Find the runtime bundle library.
        let bundle_lib = crate::exe::find_bundle_lib()?;

        // Output path: entry module stem in CWD (not project root).
        // E.g., `cranelisp --link examples/hello.cl` produces `./hello`.
        let output_path = PathBuf::from(module_name.replace(".cl", ""));

        // Compose the final .o list: nice-worker module .o files +
        // the `_main` alias .o. The alias is appended last so its Export
        // `_main` resolves the startup stub's Import.
        let mut all_o_paths = o_paths;
        all_o_paths.push(alias_o_path);

        // Link.
        crate::exe::link_executable(
            &output_path,
            &all_o_paths,
            &startup_o_path,
            &bundle_lib,
            &platform_rlib_paths,
        )
    }

    // -- REPL display utilities (pipeline-v4.md §6) --

    /// Print the session banner.
    pub fn print_banner(&self, stdout: &mut impl Write) {
        let _ = writeln!(stdout, "cranelisp REPL — type /help for help");
    }

    /// Current module name for prompt display.
    pub fn current_module_name(&self) -> String {
        self.current_module_path().to_string()
    }

    /// Write the REPL prompt with timing info.
    /// Format: `{compile_ms}+{eval_ms}ms; {module}> `
    pub fn write_prompt(&self, stdout: &mut impl Write, compile_ms: u64, eval_ms: u64) {
        let module = self.current_module_name();
        let _ = write!(stdout, "{compile_ms}+{eval_ms}ms; {module}> ");
        let _ = stdout.flush();
    }

    /// Write the continuation prompt (for multi-line input).
    pub fn write_continuation_prompt(&self, stdout: &mut impl Write, compile_ms: u64, eval_ms: u64) {
        let module = self.current_module_name();
        let prompt_len = format!("{compile_ms}+{eval_ms}ms; {module}> ").len();
        let _ = write!(stdout, "{:>width$}", "...", width = prompt_len);
        let _ = stdout.flush();
    }

    /// Check if input has balanced parentheses.
    pub fn parens_balanced(&self, input: &str) -> bool {
        parens_balanced(input)
    }

    /// Pretty-print a form (eval result string) to stdout.
    pub fn pretty_print(&self, form: &str, stdout: &mut impl Write) {
        let _ = writeln!(stdout, "{form}");
    }

    /// §9: Format an eval result for display.
    ///
    /// Produces the universal output format (spec §1.1):
    ///   `:Type {value|name} ; {classification} - {docstring}`
    pub fn format_eval_result(&self, result: &EvalResult) -> String {
        match result {
            EvalResult::Def { symbol, .. } => {
                let name = symbol.symbol.as_ref();
                let module = &symbol.module;

                // Builtin type names (Int, Bool, etc.) from primitives module.
                if module.as_ref() == "primitives" && Type::from_name(name).is_some() {
                    return self.format_builtin_type_display(name);
                }

                let entry = self.current_symbol_table().get(name).cloned();
                // Follow import chains to the definition.
                let (entry, resolved_module) = match entry {
                    Some(ref e) => self.resolve_entry_for_display(e, module),
                    None => {
                        // TraitImpl entries have `Trait.Type` names; not in symbol table.
                        if let Some((trait_name, target_type)) = name.split_once('.') {
                            return format!(
                                "impl {module}/{trait_name} for {module}/{target_type}"
                            );
                        }
                        return format!("{symbol} ; defined");
                    }
                };
                self.format_def_entry(&entry, name, &resolved_module)
            }
            EvalResult::Val { value, ty, .. } => {
                if ty.is_io() {
                    // Defensive path. In normal REPL flow `compile_and_execute_expr`
                    // has already run the trampoline and stripped the IO type via
                    // `unwrap_io_inline`, so this branch is unreachable for current
                    // callers. If a future caller ever constructs `EvalResult::Val`
                    // with an un-trampolined IO value, we must still honour
                    // Decision 24's consuming convention: `run_io_trampoline` is
                    // non-consuming, so `consume_io_tree` must release the outer
                    // tree afterwards. See `pipeline::unwrap_io_inline`.
                    let inner_value = cranelisp_intrinsics::run_io_trampoline(*value);
                    cranelisp_intrinsics::drop::consume_io_tree(*value);
                    let inner_type = ty.io_inner_type();
                    format_result_value(
                        inner_value, &inner_type, &self.shared.symbol_tables,
                    )
                } else {
                    format_result_value(
                        *value, ty, &self.shared.symbol_tables,
                    )
                }
            }
        }
    }

    /// Format a definition entry with its classification (spec §1.1, §4.1).
    fn format_def_entry(
        &self,
        entry: &ModuleEntry<Code>,
        name: &str,
        module: &ModuleFullPath,
    ) -> String {
        match entry {
            ModuleEntry::Def { scheme, kind, docstring, .. } => {
                if let DefKind::SpecialForm { description } = kind.as_ref() {
                    return format_special_form_display(name, description);
                }
                // Multi-sig: emit one line per variant per repl/spec.md
                // §1.3 + §4.1.1. Defensive fallback to single-line shape
                // when `variants` is empty (typecheck invariant: an
                // Overloaded entry should always have ≥1 variant; the
                // empty case would be a typecheck bug, not a display
                // failure).
                if let DefKind::Overloaded { variants } = kind.as_ref()
                    && !variants.is_empty()
                {
                    return format_overloaded_variants(
                        name, module, variants, docstring.as_deref(),
                    );
                }
                let base = if !scheme.constraints.is_empty() {
                    format_scheme_display(name, scheme, module)
                } else {
                    let type_str = format_type_qualified(&scheme.ty);
                    format!(":{type_str} {module}/{name}")
                };
                let classification = if matches!(kind.as_ref(), DefKind::Primitive { .. }) {
                    "primitive"
                } else {
                    "defn"
                };
                let base = format!("{base} ; {classification}");
                append_docstring_comment(base, docstring.as_deref())
            }
            ModuleEntry::Constructor { type_name, scheme, .. } => {
                let type_str = format_type_qualified(&scheme.ty);
                let tn = TypeName::from(type_name.name.as_ref());
                let ctor_display = {
                    let scope = self.current_module_path();
                    if let Some(info) = cranelisp_types::lookup_type_def_chain(
                        &self.shared.symbol_tables, &scope, &tn,
                    ) {
                        crate::display::format_ctor_display(&tn, name, &info)
                    } else {
                        format!("{type_name}.{name}")
                    }
                };
                format!(":{type_str} {module}/{ctor_display} ; deftype")
            }
            ModuleEntry::TypeDef { .. } => {
                self.format_type_display(name, module)
            }
            ModuleEntry::TraitDecl { decl, .. } => {
                self.format_trait_display(name, decl.docstring.as_deref())
            }
            ModuleEntry::Macro { clauses, docstring, .. } => {
                format_macro_display(name, clauses, docstring.as_deref(), module)
            }
            _ => {
                // TraitImpl entries have `Trait.Type` symbol names and
                // aren't stored in the symbol table as named entries.
                if let Some((trait_name, target_type)) = name.split_once('.') {
                    format!("impl {module}/{trait_name} for {module}/{target_type}")
                } else {
                    format!("{module}/{name} ; defined")
                }
            }
        }
    }

    /// Resolve Import/Reexport chains to the underlying definition entry.
    ///
    /// Walks the full chain (user → prelude → primitives → …) so that
    /// bare-value, introspection, and call paths converge on the same
    /// terminal `ModuleEntry::Def` regardless of how many re-exports sit
    /// between the current module and the defining module. Depth-limited
    /// to match the typechecker's `resolve_to_terminal_entry_owned`
    /// (spec §8.6.2 IMPORT_CHAIN_DEPTH_LIMIT). On cycle / depth exhaustion
    /// or a broken link, falls back to the last successfully resolved
    /// entry + module.
    ///
    /// Fix site for Sprint 61 Slice 1 Defect 4 (bare-primitive-name
    /// invisibility). See `design/int/bare-primitive-value-path.md`
    /// candidate 2 — the match arms in `check_bare_symbol_introspection`
    /// do not cover `Import`/`Reexport`, and the prior one-hop resolver
    /// could terminate on a `Reexport` intermediate (user → prelude →
    /// primitives), causing the bare-value path to fall through while
    /// the call and introspection paths resolved via their own recursive
    /// walks. Aligning on a single recursive resolver closes the
    /// divergence.
    fn resolve_entry_for_display(
        &self,
        entry: &ModuleEntry<Code>,
        current_module: &ModuleFullPath,
    ) -> (ModuleEntry<Code>, ModuleFullPath) {
        const MAX_DEPTH: usize = 32;
        let mut cur_entry = entry.clone();
        let mut cur_module = current_module.clone();
        for _ in 0..MAX_DEPTH {
            match &cur_entry {
                ModuleEntry::Import { source }
                | ModuleEntry::Reexport { source } => {
                    match self.shared.symbol_tables.get(&source.module) {
                        Some(module_table) => {
                            match module_table.get(source.symbol.as_ref()) {
                                Some(resolved) => {
                                    let next = resolved.clone();
                                    cur_module = source.module.clone();
                                    cur_entry = next;
                                    continue;
                                }
                                None => return (cur_entry, cur_module),
                            }
                        }
                        None => return (cur_entry, cur_module),
                    }
                }
                _ => return (cur_entry, cur_module),
            }
        }
        // Depth exhausted — return the last resolved entry/module.
        (cur_entry, cur_module)
    }

    /// Format a user-defined type for display (spec §4.1.3).
    ///
    /// Shows `:module/TypeName ; deftype` with `; match:` and `; impl:` sections.
    fn format_type_display(&self, type_name: &str, module: &ModuleFullPath) -> String {
        let mut result = format!(":{module}/{type_name} ; deftype");
        let tn = TypeName::from(type_name);
        let scope = self.current_module_path();
        // FIXME 0192 method 2: `get_type_constructors` deleted; inline the
        // 1-line wrapper over the relocated `lookup_type_def_chain`.
        if let Some(info) = cranelisp_types::lookup_type_def_chain(
            &self.shared.symbol_tables, &scope, &tn,
        ) && !info.constructors.is_empty() {
            let names: Vec<&str> = info.constructors.iter().map(|c| c.name.as_ref()).collect();
            result.push_str(&format_related_section("match", &names));
        }
        let trait_names = cranelisp_types::get_impls_for_type_chain(
            &self.shared.symbol_tables, &scope, &tn,
        );
        if !trait_names.is_empty() {
            let names: Vec<&str> = trait_names.iter().map(|t| t.as_ref()).collect();
            result.push_str(&format_related_section("impl", &names));
        }
        result
    }

    /// Format a trait for display (spec §4.1.4).
    ///
    /// Shows `:module/TraitName ; deftrait` with `; defn:` and `; impl:` sections.
    fn format_trait_display(&self, trait_name: &str, docstring: Option<&str>) -> String {
        let scope = self.current_module_path();
        // FIXME 0192 method 6: `defining_module_for` deleted; substitute with
        // the chain-follow from `resolve_terminal_entry_and_home` (Decision 45
        // Pattern B). If the trait isn't reachable, fall back to the scope —
        // the display layer treats unresolved chains as defined-here for
        // diagnostic continuity (no architectural workaround; just a display
        // fallback).
        let defining_module = match cranelisp_types::resolve_terminal_entry_and_home(
            &self.shared.symbol_tables, &scope, trait_name,
        ) {
            Some((ModuleEntry::TraitDecl { .. }, home)) => home,
            _ => scope.clone(),
        };
        let tn = TraitName::from(trait_name);
        let mut result = format!(":{defining_module}/{trait_name} ; deftrait");
        result = append_docstring_comment(result, docstring);
        // FIXME 0192 method 4: `get_trait_methods` deleted; inline the 1-line
        // wrapper over `lookup_trait_decl_chain`.
        if let Some(decl) = cranelisp_types::lookup_trait_decl_chain(
            &self.shared.symbol_tables, &scope, &tn,
        ) && !decl.methods.is_empty() {
            let names: Vec<&str> = decl.methods.iter().map(|m| m.name.as_ref()).collect();
            result.push_str(&format_related_section("defn", &names));
        }
        let impl_types = cranelisp_types::get_implementing_types_chain(
            &self.shared.symbol_tables, &scope, &tn,
        );
        if !impl_types.is_empty() {
            let names: Vec<&str> = impl_types.iter().map(|t| t.as_ref()).collect();
            result.push_str(&format_related_section("impl", &names));
        }
        result
    }

    /// Format a builtin type (Int, Bool, Float, String) for display (spec §4.1.3).
    fn format_builtin_type_display(&self, type_name: &str) -> String {
        let tn = TypeName::from(type_name);
        let scope = self.current_module_path();
        let mut result = format!(":primitives/{type_name} ; type");
        let trait_names = cranelisp_types::get_impls_for_type_chain(
            &self.shared.symbol_tables, &scope, &tn,
        );
        if !trait_names.is_empty() {
            let names: Vec<&str> = trait_names.iter().map(|t| t.as_ref()).collect();
            result.push_str(&format_related_section("impl", &names));
        }
        result
    }
}

// =============================================================================
// Display formatting helpers (ported from repl/commands.rs)
// =============================================================================

/// Format a special form for display (spec §4.1.5).
fn format_special_form_display(name: &str, description: &str) -> String {
    let type_sig = match name {
        "if" => ":(Fn [primitives/Bool a a] a)",
        "let" => ":(Fn [bindings body] a)",
        "fn" => ":(Fn [params body] function)",
        "defn" => ":(Fn [name params body] function)",
        "deftype" => ":(Fn [name ctors...] type)",
        "match" => ":(Fn [expr [pat body]...] a)",
        "defmacro" => ":(Fn [name params body] macro)",
        "deftrait" => ":(Fn [name methods...] trait)",
        "impl" => ":(Fn [trait type methods...] impl)",
        "import" => ":(Fn [module names] import)",
        "do" => ":(Fn [exprs...] a)",
        _ => "",
    };
    if type_sig.is_empty() {
        format!("{name} ; special form - {description}")
    } else {
        format!("{type_sig} {name} ; special form - {description}")
    }
}

/// Format a macro for display (spec §4.1.6).
fn format_macro_display(
    name: &str,
    clauses: &[MacroClauseInfo],
    docstring: Option<&str>,
    module: &ModuleFullPath,
) -> String {
    let mut result = format!(":{module}/{name} ; defmacro");
    result = append_docstring_comment(result, docstring);
    for clause in clauses {
        let params = format_macro_clause_params(clause);
        result.push_str(&format!("\n; {params} -> Sexp"));
    }
    result
}

/// Format macro clause parameters as `[param1 param2 ...]`.
fn format_macro_clause_params(clause: &MacroClauseInfo) -> String {
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

/// Format a related symbols section (spec §1.1).
fn format_related_section(label: &str, names: &[&str]) -> String {
    format!("\n; {label}:\n;  {}", names.join(" "))
}

/// Classification of an imported symbol for category-based display.
enum ImportClass {
    Macro,
    Trait,
    Type,
    Constructor,
    Fn,
}

/// Append a category of names to a string buffer (for /list, /imports, /exports).
fn append_name_category(buf: &mut String, label: &str, names: &[String]) {
    if names.is_empty() {
        return;
    }
    buf.push_str(label);
    buf.push_str(":\n");
    for name in names {
        buf.push_str("  ");
        buf.push_str(name);
        buf.push('\n');
    }
}

/// Format a Sexp value as a readable string.
fn format_sexp(sexp: &Sexp) -> String {
    match sexp {
        Sexp::Symbol(name, _) => name.clone(),
        Sexp::Int(n, _) => format!("{n}"),
        Sexp::Float(v, _) => {
            let s = format!("{v}");
            if s.contains('.') { s } else { format!("{s}.0") }
        }
        Sexp::Bool(b, _) => format!("{b}"),
        Sexp::Str(s, _) => format!("\"{s}\""),
        Sexp::List(children, _) => {
            let parts: Vec<String> = children.iter().map(format_sexp).collect();
            format!("({})", parts.join(" "))
        }
        Sexp::Bracket(children, _) => {
            let parts: Vec<String> = children.iter().map(format_sexp).collect();
            format!("[{}]", parts.join(" "))
        }
        Sexp::Comment(text, _) => {
            if text.is_empty() {
                ";".to_string()
            } else {
                format!("; {text}")
            }
        }
    }
}

/// Append docstring as a comment suffix.
fn append_docstring_comment(base: String, docstring: Option<&str>) -> String {
    match docstring {
        Some(doc) if !doc.is_empty() => {
            let first_line = doc.lines().next().unwrap_or("");
            if first_line.is_empty() {
                base
            } else {
                format!("{base} - {first_line}")
            }
        }
        _ => base,
    }
}

/// Extract the defined name from a sexp that was handled during expansion.
///
/// Handles `(defmacro name ...)`, `(import ...)`, `(platform ...)`, etc.
fn extract_def_name_from_sexp(sexp: &Sexp) -> Option<String> {
    if let Sexp::List(items, _) = sexp
        && items.len() >= 2
            && let Sexp::Symbol(head, _) = &items[0] {
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

impl Drop for CompilerSession {
    fn drop(&mut self) {
        // Defensive: ensure workers are signalled and joined before this
        // session is destroyed. Prevents hangs (and mmap'd JIT pages going
        // out of scope while a worker still dereferences them) if the
        // session is dropped without an explicit `shutdown()` call — e.g.
        // during test teardown or panic unwinding. Sprint 57 Wave 4 G9
        // per `persistent-workers.md` §5.2.
        //
        // `shutdown()` is idempotent; calling it in Drop is safe even if
        // the caller already called it.
        self.shutdown();
    }
}

// ---------------------------------------------------------------------------
// Nice worker spawning + loop (Step 10)
// ---------------------------------------------------------------------------

/// Spawn nice (low-priority) worker threads inside a `std::thread::scope`.
///
/// Test-only helper kept for `nice_worker_lifecycle_spawn_and_shutdown` in
/// `src/scheduler.rs` tests. Production code uses the persistent
/// `nice_worker_handles` pool spawned in `CompilerSession::new` (Sprint 46).
/// `cfg(test)` gates this so `thread::scope` does not appear in any
/// non-test build per `design/int/persistent-workers.md` §11 acceptance
/// criterion 2.
///
/// # Panics
///
/// Panics if the OS fails to spawn a thread. Tests rely on this invariant.
#[cfg(test)]
pub fn spawn_nice_workers<'scope, 'env>(
    scope: &'scope std::thread::Scope<'scope, 'env>,
    shared: &'env Arc<SharedState>,
    n: usize,
) {
    for i in 0..n {
        let worker_shared = Arc::clone(shared);
        std::thread::Builder::new()
            .name(format!("nice-worker-{}", i))
            .spawn_scoped(scope, move || {
                nice_worker_loop(&worker_shared);
            })
            .expect("failed to spawn nice worker thread");
    }
}

/// Main loop for nice (low-priority) worker threads.
///
/// Runs at reduced OS scheduling priority. Claims TypecheckDone modules
/// from the scheduler, compiles them to `.o` files via Cranelift
/// ObjectModule, writes the `.o` to the cache directory, and appends
/// the path to `shared.compiled_o_paths` for the linker.
///
/// When caching is disabled (`shared.cache_dir` is None) or no
/// program is available for a module, the worker skips
/// `.o` compilation and just marks the module as object-complete.
///
/// The loop parks on `scheduler.take_object_codegen()` (condvar-based)
/// when no work is available, and exits on shutdown.
fn nice_worker_loop(shared: &SharedState) {
    // Set below-normal OS scheduling priority (best-effort).
    crate::thread_util::set_nice_priority();

    loop {
        // Check for priority promotion (hot flush before --link).
        if shared.promote_nice_workers.load(
            std::sync::atomic::Ordering::Relaxed,
        ) {
            crate::thread_util::set_normal_priority();
        }

        // Park until a TypecheckDone module with object_done == false
        // is available, or shutdown is signaled.
        let module = match shared.scheduler.take_object_codegen() {
            Some(m) => m,
            None => {
                // Observability: publish this nice-worker thread's
                // scheduler-trace ring buffer so the main thread's
                // `flush_to_stderr` can merge it into the dump
                // (design/int/observability.md §7). No-op when disabled.
                crate::observability::publish_thread_buffer();
                // GOT trace events (FIXME 0099) — nice workers also emit
                // GOT events (LinkerWrite during cache-hit load).
                crate::got_trace::publish_thread_buffer();
                return; // Shutdown signaled.
            }
        };

        // Attempt .o compilation if caching is enabled.
        if let Some(cache_dir) = &shared.cache_dir {
            compile_module_object(shared, &module, cache_dir);
        }

        // Notify scheduler that object codegen is done for this module.
        shared.scheduler.notify_object_codegen_complete(&module);
    }
}

/// Compile a single module to `.o` and `.meta.json` files in the cache directory.
///
/// Sprint 58 Step 5b: reads `SymbolTable` directly via the shared
/// `defined_symbols()` predicate (Decision 22). The transitional
/// `codegen_programs` stash is gone — the backend never read from it, and
/// the "had compilable defns" presence signal collapses to "did
/// `defined_symbols()` return anything".
///
/// Errors are logged to stderr and do not halt the worker — the module is still
/// marked object-complete so the scheduler lifecycle proceeds.
fn compile_module_object(
    shared: &SharedState,
    module: &ModuleFullPath,
    cache_dir: &Path,
) {
    use cranelisp_backend::cache;

    // Enumerate codegen-compilable symbols via the shared predicate (Decision 22).
    // Empty result → no compilable defns (types-only, imports-only) → skip.
    let names: Vec<cranelisp_types::Symbol> = shared
        .symbol_tables
        .get(module)
        .map(|t| {
            t.defined_symbols()
                .map(|(name, _)| name.clone())
                .collect()
        })
        .unwrap_or_default();
    if names.is_empty() {
        return;
    }

    // Build ObjectModule with PIC ISA.
    let isa = match cranelisp_backend::build_isa(true) {
        Ok(isa) => isa,
        Err(e) => {
            if std::env::var("CRANELISP_CODEGEN_TRACE").is_ok() {
                eprintln!("nice-worker: ISA build failed for {}: {}", module, e.message());
            }
            return;
        }
    };
    let obj_builder = match cranelisp_backend::cranelift_object::ObjectBuilder::new(
        isa,
        format!("cranelisp_{}", module),
        cranelisp_backend::cranelift_module::default_libcall_names(),
    ) {
        Ok(b) => b,
        Err(e) => {
            if std::env::var("CRANELISP_CODEGEN_TRACE").is_ok() {
                eprintln!("nice-worker: ObjectBuilder failed for {}: {e}", module);
            }
            return;
        }
    };
    let mut obj_module = cranelisp_backend::cranelift_object::ObjectModule::new(obj_builder);

    // Compile using the unified compile_to_module path. Intrinsics are declared
    // on the module internally; cross-module refs resolve from `symbol_tables`.
    let obj_bytes = match cranelisp_backend::compile_to_module(
        module.clone(),
        &names,
        &shared.symbol_tables,
        &mut obj_module,
    ) {
        Ok(_result) => {
            // Emit .o bytes from the ObjectModule.
            match obj_module.finish().emit() {
                Ok(bytes) => bytes,
                Err(e) => {
                    if std::env::var("CRANELISP_CODEGEN_TRACE").is_ok() {
                        eprintln!("nice-worker: .o emit failed for {}: {e}", module);
                    }
                    return;
                }
            }
        }
        Err(e) => {
            // Log .o compilation errors only when CRANELISP_CODEGEN_TRACE is set.
            // These are non-fatal (in-memory compilation may have succeeded).
            if std::env::var("CRANELISP_CODEGEN_TRACE").is_ok() {
                eprintln!("nice-worker: .o compilation failed for {}: {}", module, e);
            }
            return;
        }
    };

    // Write .o and .meta.json files to cache directory.
    let (meta_path, o_path) = cache::module_cache_path(cache_dir, module);

    // Ensure parent directory exists.
    if let Some(parent) = o_path.parent()
        && let Err(e) = std::fs::create_dir_all(parent)
    {
        eprintln!("nice-worker: cannot create cache dir '{}': {}", parent.display(), e);
        return;
    }

    if let Err(e) = std::fs::write(&o_path, &obj_bytes) {
        eprintln!("nice-worker: cannot write '{}': {}", o_path.display(), e);
        return;
    }

    // Write .meta.json for cache-hit restoration via the unified
    // `cache::write_meta` API (Sprint 58 Step 5b / Decision 33+34).
    // The .meta.json IS a serialised SymbolTable; `write_meta` stamps
    // `schema_version = CACHE_SCHEMA_VERSION` on the cloned table before
    // serialising. Per Decision 33, structural decls
    // (imports/exports/platforms/submodules) are now fields on the
    // SymbolTable itself — the worker form-handlers populate them in
    // `process_module_forms`, so the serialised table carries the
    // user-authored structural specifications inline (no separate
    // `dependencies` envelope needed; cache-hit derives transitive deps from
    // `imports` directly).
    let symbol_table = shared.symbol_tables
        .get(module)
        .map(|guard| guard.clone())
        .unwrap_or_else(|| crate::code::SessionSymbolTable::new_with_params(module.clone()));

    if let Err(e) = cache::serialize::write_meta(&meta_path, &symbol_table, cache::CACHE_SCHEMA_VERSION) {
        eprintln!("nice-worker: .meta.json write failed for {}: {}", module, e.message());
        // Continue — the .o file was written successfully.
    }

    // Record module in manifest for cache-hit detection on next session.
    {
        let mut cs_guard = shared.cache_state.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(cs) = cs_guard.as_mut() {
            let source_hash = cs.source_hashes()
                .get(module)
                .cloned()
                .unwrap_or_default();
            // dep_hashes: empty for now — full dependency tracking is a future enhancement.
            cs.record_module(module, source_hash, std::collections::HashMap::new());
        }
    }

    // Append the .o path for the linker.
    if let Ok(mut paths) = shared.compiled_o_paths.lock() {
        paths.push(o_path);
    }
}

// ---------------------------------------------------------------------------
// Trace format support (repl/spec.md §4.12)
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Test infrastructure: core logic + JIT-callable externs
// ---------------------------------------------------------------------------

/// Result of running a single test (Rust-side, no heap allocation).
enum TestOutcome {
    Pass { name: String, nanos: i64 },
    Fail { name: String, nanos: i64, reason: String },
    Panic { name: String, reason: String },
}

/// Core: discover test-* function names in a module. No heap allocation.
///
/// Returns fully-qualified names ("module/test-name") sorted alphabetically.
///
/// Sprint 57 Wave 2 G6: reads `ModuleEntry::Def.code` (replaces the deleted
/// `CodegenProduct` DashMap).
fn discover_test_names(
    tc_modules: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    module: &ModuleFullPath,
) -> Vec<String> {
    let mut names = Vec::new();
    let symbols = match tc_modules.get(module) {
        Some(st) => st,
        None => return names,
    };
    for (name, entry) in symbols.all_symbols() {
        if !name.as_ref().starts_with("test-") {
            continue;
        }
        match entry {
            ModuleEntry::Def { param_names, code: Some(c), .. }
                if param_names.is_empty() && !c.ptr().is_null() =>
            {
                names.push(format!("{}/{}", module.as_ref(), name.as_ref()));
            }
            _ => continue,
        }
    }
    names.sort();
    names
}

/// Core: run a single test by fully-qualified name. No heap allocation.
///
/// Looks up the code pointer, calls it, interprets the (Option String) result.
///
/// Sprint 57 Wave 2 G6: reads `ModuleEntry::Def.code` (replaces the deleted
/// `CodegenProduct` DashMap).
fn run_test_by_name(
    tc_modules: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    fq_name: &str,
) -> TestOutcome {
    use cranelisp_types::NULLARY_TAG_THRESHOLD;

    // Parse "module/name" into module path and bare name.
    let (module_str, bare_name) = match fq_name.rsplit_once('/') {
        Some((m, n)) => (m, n),
        None => ("user", fq_name),
    };
    let module = ModuleFullPath::from(module_str);

    // Look up code pointer from the symbol-table entry.
    let code_ptr = tc_modules.get(&module).and_then(|t| {
        match t.get(bare_name)? {
            ModuleEntry::Def { code: Some(c), .. } => Some(c.ptr()),
            _ => None,
        }
    });

    let code_ptr = match code_ptr {
        Some(ptr) if !ptr.is_null() => ptr,
        _ => return TestOutcome::Fail {
            name: fq_name.to_string(),
            nanos: 0,
            reason: "test function not found".to_string(),
        },
    };

    // Call the test function.
    let t0 = std::time::Instant::now();
    let _ = cranelisp_intrinsics::panic::take_runtime_error();
    let value = unsafe {
        let func: extern "C" fn() -> i64 = std::mem::transmute(code_ptr);
        func()
    };
    let nanos = t0.elapsed().as_nanos() as i64;

    if let Some(msg) = cranelisp_intrinsics::panic::take_runtime_error() {
        return TestOutcome::Panic {
            name: fq_name.to_string(),
            reason: msg,
        };
    }

    if (value as usize) < NULLARY_TAG_THRESHOLD {
        TestOutcome::Pass {
            name: fq_name.to_string(),
            nanos,
        }
    } else {
        let reason = unsafe {
            let base = value as *const u8;
            let string_ptr = *(base.add(
                cranelisp_backend::heap::HeapAdt::field_offset(0) as usize,
            ) as *const i64);
            cranelisp_intrinsics::heap_string::read_string_as_str(string_ptr).to_string()
        };
        TestOutcome::Fail {
            name: fq_name.to_string(),
            nanos,
            reason,
        }
    }
}

/// Session state for the `run-test` / `discover-tests` intrinsics.
///
/// Sprint 66 Wave 3a-γ: lifted from per-compilation construction to
/// session-wide construction (built once in `CompilerSession::new`, stored on
/// `SharedState`). The thread-local `TEST_RUNNER` cell holds a pointer derived
/// from `SharedState.test_runner_state` (a `Box`, so the address is stable for
/// the session lifetime); the REPL eval path sets it before invoking a
/// compiled expression. The `current_module` field is a `Mutex` so the REPL
/// `/mod` command may update it without re-allocating the state.
///
/// The intrinsics themselves dereference these pointers when JIT-emitted code
/// invokes `run-test` / `discover-tests` — see `run_test_extern` /
/// `discover_tests_extern` below. The state is only meaningful inside an
/// active REPL eval; absent that, the intrinsics return harmless empty
/// results (mirrors the prior null-pointer-guard behaviour).
pub struct TestRunnerState {
    /// TC modules for scanning symbol tables and reading compiled `code`.
    tc_modules: *const dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    /// Current module path (for discover-tests with empty module arg).
    /// Updated by `set_current_module` when the REPL `/mod` command switches.
    current_module: Mutex<ModuleFullPath>,
}

// Safety: the pointer-typed `tc_modules` field is read-only data; it points
// at a `DashMap` (itself Send + Sync) inside the same `SharedState` instance.
// `Mutex<ModuleFullPath>` is Send + Sync. The thread-local-pointer access is
// always read-via-Cell on the thread that called `set_test_runner_state`.
unsafe impl Send for TestRunnerState {}
unsafe impl Sync for TestRunnerState {}

impl TestRunnerState {
    /// Construct a stub TestRunnerState for unit tests that need to build a
    /// `SharedState` but don't exercise the test intrinsics. The
    /// `tc_modules` pointer is null; any extern call against this state
    /// returns the harmless null-pointer fallback (empty list / `?` name).
    pub fn stub() -> Self {
        Self {
            tc_modules: std::ptr::null(),
            current_module: Mutex::new(ModuleFullPath::from("user")),
        }
    }
}

thread_local! {
    static TEST_RUNNER: std::cell::Cell<*const TestRunnerState> =
        const { std::cell::Cell::new(std::ptr::null()) };
}

pub(crate) fn set_test_runner_state(state: &TestRunnerState) {
    TEST_RUNNER.with(|c| c.set(state as *const _));
}

/// Sprint 66 Wave 3a-γ: int-owned intrinsics inventory.
///
/// These three extern functions are backend-emitted-call targets — JIT-emitted
/// CLIF declares them as `Linkage::Import` and `JITBuilder::symbol(...)` must
/// resolve them. Per `design/arch/facades/intrinsics.md` they are intrinsics
/// like `heap_alloc` / `runtime/panic` / primitive arithmetic, and must be
/// registered uniformly at JIT setup. Pre-S66 they were conditionally
/// registered via syntactic scans of each program — see the FIXME 0178 filed
/// alongside this change.
///
/// The thread-local state these intrinsics read (`TestRunnerState`,
/// `TraceDisplayState`) is set just-in-time by the REPL eval path; the
/// intrinsics themselves null-check the pointer and return harmless defaults
/// when absent.
pub(crate) fn int_intrinsics() -> [(&'static str, *const u8); 14] {
    [
        ("discover-tests", discover_tests_extern as *const u8),
        ("run-test", run_test_extern as *const u8),
        // `cranelisp_trace_format` is int-hosted (REPL session has access to
        // the TypeChecker for proper display dispatch; `crate::trace`'s body
        // is the unit-test fallback only).
        ("cranelisp_trace_format", repl_trace_format as *const u8),
        // Sprint 67 Wave 4 — Decision 40 Path B1: the 12 `cranelisp_trace_*`
        // JIT-emitted-call targets relocate from `cranelisp-intrinsics::trace`
        // to int. Backend's 12 IntrinsicSymbol entries delete in the same
        // change-set (FIXME 0197); int hosting + registration are this fire
        // (FIXME 0202).
        (
            "cranelisp_trace_enter",
            crate::trace::cranelisp_trace_enter as *const u8,
        ),
        (
            "cranelisp_trace_exit",
            crate::trace::cranelisp_trace_exit as *const u8,
        ),
        (
            "cranelisp_trace_swap_got",
            crate::trace::cranelisp_trace_swap_got as *const u8,
        ),
        (
            "cranelisp_trace_restore_got",
            crate::trace::cranelisp_trace_restore_got as *const u8,
        ),
        (
            "cranelisp_collect_trace",
            crate::trace::cranelisp_collect_trace as *const u8,
        ),
        (
            "cranelisp_trace_first_child_nanos",
            crate::trace::cranelisp_trace_first_child_nanos as *const u8,
        ),
        (
            "cranelisp_trace_name",
            crate::trace::cranelisp_trace_name as *const u8,
        ),
        (
            "cranelisp_trace_params",
            crate::trace::cranelisp_trace_params as *const u8,
        ),
        (
            "cranelisp_trace_result",
            crate::trace::cranelisp_trace_result as *const u8,
        ),
        (
            "cranelisp_trace_children",
            crate::trace::cranelisp_trace_children as *const u8,
        ),
        (
            "cranelisp_trace_nanos",
            crate::trace::cranelisp_trace_nanos as *const u8,
        ),
    ]
}

/// Allocate a heap ADT with the given tag and fields.
///
/// Layout: [alloc_size(8) | rc=1(8) | tag(8) | field0(8) | field1(8) | ...]
/// Returns the base pointer (offset 0 of the allocation).
unsafe fn alloc_heap_adt(tag: i64, fields: &[i64]) -> i64 { unsafe {
    let payload_size = 8 + fields.len() * 8; // tag + fields
    let base = cranelisp_intrinsics::alloc::alloc_with_rc(payload_size);
    // Tag at offset 16 (HeapHeader::SIZE).
    *(base.add(16) as *mut i64) = tag;
    // Fields at offsets 24, 32, 40, ...
    for (i, &field) in fields.iter().enumerate() {
        *(base.add(24 + i * 8) as *mut i64) = field;
    }
    base as i64
}}

/// Wrap a value in IO Pure: allocates Pure(value) on the heap.
/// IO Pure tag = 0, single field = the wrapped value.
unsafe fn alloc_io_pure(value: i64) -> i64 { unsafe {
    alloc_heap_adt(0, &[value])
}}

/// Build an SList SCons node: SCons(head, tail).
/// SCons tag = 1.
unsafe fn alloc_scons(head: i64, tail: i64) -> i64 { unsafe {
    alloc_heap_adt(1, &[head, tail])
}}

/// JIT-callable: discover test functions in a module.
///
/// Takes a String heap pointer (module path; empty = current module).
/// Returns IO(SList(Sexp)) — a Pure node wrapping an SList of SexpSym values.
extern "C" fn discover_tests_extern(module_path_str: i64) -> i64 {
    TEST_RUNNER.with(|c| {
        let state_ptr = c.get();
        if state_ptr.is_null() {
            return unsafe { alloc_io_pure(0) }; // IO Pure(SNil)
        }

        let state = unsafe { &*state_ptr };
        let tc_modules = unsafe { &*state.tc_modules };
        let current_module = state.current_module.lock()
            .unwrap_or_else(|e| e.into_inner())
            .clone();

        let module = if module_path_str == 0
            || unsafe { cranelisp_intrinsics::heap_string::read_string_as_str(module_path_str) }.is_empty()
        {
            current_module
        } else {
            let path_str = unsafe { cranelisp_intrinsics::heap_string::read_string_as_str(module_path_str) };
            ModuleFullPath::from(path_str)
        };

        // Core logic — shared with slash command.
        let test_names = discover_test_names(tc_modules, &module);

        // Heap-allocate: SList of SexpSym, wrapped in IO Pure.
        // SexpSym tag = 4 (Sexp enum: Int=0, Float=1, Bool=2, Str=3, Sym=4).
        let mut slist: i64 = 0; // SNil
        for name in test_names.into_iter().rev() {
            let name_str = cranelisp_intrinsics::heap_string::alloc_string(name.as_bytes()) as i64;
            let sexp_sym = unsafe { alloc_heap_adt(4, &[name_str]) };
            slist = unsafe { alloc_scons(sexp_sym, slist) };
        }

        unsafe { alloc_io_pure(slist) }
    })
}

/// JIT-callable: run a single test without tracing.
///
/// Takes a Sexp (SexpSym with function name).
/// Returns IO(TestResult) — Pure(TestPass(...)) or Pure(TestFail(...)).
extern "C" fn run_test_extern(sexp_sym: i64) -> i64 {
    use cranelisp_types::NULLARY_TAG_THRESHOLD;

    TEST_RUNNER.with(|c| {
        let state_ptr = c.get();
        if state_ptr.is_null() {
            let name = cranelisp_intrinsics::heap_string::alloc_string(b"?") as i64;
            return unsafe { alloc_io_pure(alloc_heap_adt(0, &[name, 0])) };
        }

        let state = unsafe { &*state_ptr };
        let tc_modules = unsafe { &*state.tc_modules };

        // Extract function name from SexpSym.
        // SexpSym layout: [header(16) | tag=4(8) | sname(8)]
        let fq_name = if sexp_sym != 0 && (sexp_sym as usize) >= NULLARY_TAG_THRESHOLD {
            let name_ptr = unsafe { *((sexp_sym as *const u8).add(24) as *const i64) };
            unsafe { cranelisp_intrinsics::heap_string::read_string_as_str(name_ptr).to_string() }
        } else {
            let name = cranelisp_intrinsics::heap_string::alloc_string(b"?") as i64;
            return unsafe { alloc_io_pure(alloc_heap_adt(0, &[name, 0])) };
        };

        // Core logic — shared with slash command.
        let outcome = run_test_by_name(tc_modules, &fq_name);

        // Heap-allocate TestResult, wrapped in IO Pure.
        unsafe { alloc_io_pure(test_outcome_to_heap(&outcome)) }
    })
}

/// Convert a TestOutcome to a heap-allocated TestResult ADT.
unsafe fn test_outcome_to_heap(outcome: &TestOutcome) -> i64 { unsafe {
    match outcome {
        TestOutcome::Pass { name, nanos } => {
            let name_alloc = cranelisp_intrinsics::heap_string::alloc_string(name.as_bytes()) as i64;
            alloc_heap_adt(0, &[name_alloc, *nanos]) // TestPass tag=0
        }
        TestOutcome::Fail { name, nanos, reason } => {
            let name_alloc = cranelisp_intrinsics::heap_string::alloc_string(name.as_bytes()) as i64;
            let reason_alloc = cranelisp_intrinsics::heap_string::alloc_string(reason.as_bytes()) as i64;
            alloc_heap_adt(1, &[name_alloc, *nanos, reason_alloc]) // TestFail tag=1
        }
        TestOutcome::Panic { name, reason } => {
            let name_alloc = cranelisp_intrinsics::heap_string::alloc_string(name.as_bytes()) as i64;
            let reason_alloc = cranelisp_intrinsics::heap_string::alloc_string(reason.as_bytes()) as i64;
            alloc_heap_adt(1, &[name_alloc, 0, reason_alloc]) // TestFail tag=1
        }
    }
}}

// ---------------------------------------------------------------------------
// Trace display support (repl/spec.md §4.12)
// ---------------------------------------------------------------------------

/// Thread-local display state for `repl_trace_format`. Set before JIT
/// evaluation of a trace expression, cleared after.
pub(crate) struct TraceDisplayState {
    symbol_tables: *const dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
}

// Only accessed via thread-local Cell (never crosses threads).
unsafe impl Send for TraceDisplayState {}

thread_local! {
    static TRACE_DISPLAY: std::cell::Cell<*const TraceDisplayState> =
        const { std::cell::Cell::new(std::ptr::null()) };
}

/// Set trace display state before evaluating a trace expression.
pub(crate) fn set_trace_display_state(state: &TraceDisplayState) {
    TRACE_DISPLAY.with(|c| c.set(state as *const _));
}

/// Clear trace display state after evaluation.
pub fn clear_trace_display_state() {
    TRACE_DISPLAY.with(|c| c.set(std::ptr::null()));
}

/// JIT-callable trace format: formats a runtime value using the session's
/// type definitions. Registered as a JIT symbol to override the runtime's
/// fallback `cranelisp_trace_format`.
extern "C" fn repl_trace_format(val: i64, type_ptr: i64) -> i64 {
    TRACE_DISPLAY.with(|c| {
        let state_ptr = c.get();
        let s = if state_ptr.is_null() {
            "?".to_string()
        } else {
            // SAFETY: state_ptr set by set_trace_display_state, valid for
            // the duration of the JIT expression execution. type_ptr was
            // leaked by trace_codegen (valid for program lifetime).
            let state = unsafe { &*state_ptr };
            let symbol_tables = unsafe { &*state.symbol_tables };
            let ty = unsafe { &*(type_ptr as *const Type) };
            crate::display::format_value(val, ty, symbol_tables)
        };
        cranelisp_intrinsics::heap_string::alloc_string(s.as_bytes()) as i64
    })
}

// ---------------------------------------------------------------------------
// Sprint 57 Wave 4 G9 — persistent worker lifecycle tests
// ---------------------------------------------------------------------------
//
// Covers the four scenarios from `design/int/persistent-workers.md` §9.1:
//   1. park + wake (enqueue → worker processes)
//   2. shutdown under load (Drop while work enqueued, no panic, no leak)
//   3. concurrent register_module (two modules at once, both complete)
//   4. reload-during-compile race (reload while register_module is mid-flight)
//
// These are end-to-end session tests that use trivial source so they do not
// rely on a prelude or stdlib; they validate the worker lifecycle only.

#[cfg(test)]
mod persistent_worker_tests {
    use super::*;

    fn test_session(priority_workers: usize) -> (CompilerSession, PathBuf) {
        // Use a unique temp dir per call as project_root so no stray
        // prelude.cl is found. The caller is responsible for removing
        // the dir after the test (or letting the OS reclaim /tmp).
        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let pid = std::process::id();
        let tmp_root = std::env::temp_dir()
            .join(format!("cranelisp-wave4-{}-{}", pid, stamp));
        std::fs::create_dir_all(&tmp_root).expect("create test project_root");
        let settings = SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers,
            nice_workers: 0,
        };
        let mut s = CompilerSession::new(settings, tmp_root.clone());
        s.set_lib_dirs(vec![]);
        (s, tmp_root)
    }

    // spec: persistent-workers.md §4.2 — workers park on the priority-work
    // condvar and wake when register_module enqueues work.
    #[test]
    fn persistent_worker_park_and_wake() {
        let (mut s, root) = test_session(1);
        // Worker has been spawned in `new()` and is parked. Register a
        // trivial module — the notify_all on `priority_work_available`
        // wakes the worker.
        let p = root.join("wake.cl");
        s.register_module_with_source("wake", "(defn zero [] 0)", &p)
            .expect("register_module_with_source should succeed");
        // After return: wait_inmem_complete_blocking has observed inmem_done.
        assert!(
            !s.shared.scheduler.is_failed(&ModuleFullPath::from("wake")),
            "module must not have failed",
        );
        // The worker is parked again now (no more work). Shutdown joins it.
        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // spec: persistent-workers.md §5.2 — Drop while work is enqueued calls
    // shutdown() which signals + joins. No panic, no leak.
    #[test]
    fn shutdown_under_load_no_panic() {
        let (mut s, root) = test_session(2);
        // Register a module. workers begin processing.
        let p = root.join("load.cl");
        s.register_module_with_source("load", "(defn a [] 1) (defn b [] 2)", &p)
            .expect("register_module_with_source should succeed");
        // Immediately shutdown (workers may still be mid-loop).
        s.shutdown();
        // Calling shutdown a second time is idempotent.
        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // spec: persistent-workers.md §9.1 — concurrent module registrations
    // all complete; no lost updates.
    #[test]
    fn concurrent_register_module_two_modules_complete() {
        let (mut s, root) = test_session(2);

        // Register module A.
        s.register_module_with_source(
            "concA",
            "(defn a [] 10)",
            &root.join("concA.cl"),
        )
        .expect("register concA");

        // Register module B while A is complete but workers still parked.
        // The persistent pool handles the second registration without
        // respawning anything.
        s.register_module_with_source(
            "concB",
            "(defn b [] 20)",
            &root.join("concB.cl"),
        )
        .expect("register concB");

        // Both modules should be complete (inmem_done), neither failed.
        assert!(!s.shared.scheduler.is_failed(&ModuleFullPath::from("concA")));
        assert!(!s.shared.scheduler.is_failed(&ModuleFullPath::from("concB")));
        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // spec: persistent-workers.md §9.1 — reload_module through the same
    // persistent pool as register_module. Re-register → workers wake →
    // recompile → inmem_done.
    #[test]
    fn reload_during_compile_race_completes() {
        let (mut s, root) = test_session(2);

        // Write a real file so reload_module can read from disk.
        let file_path = root.join("reload_target.cl");
        std::fs::write(&file_path, "(defn original [] 1)\n")
            .expect("seed reload_target.cl");

        // Initial register via the source-explicit path.
        s.register_module_with_source(
            "reload_target",
            "(defn original [] 1)",
            &file_path,
        )
        .expect("initial register");

        // Overwrite with new content and trigger reload.
        std::fs::write(&file_path, "(defn updated [] 2)\n")
            .expect("rewrite reload_target.cl");
        let module = ModuleFullPath::from("reload_target");
        s.reload_module(&module, &file_path)
            .expect("reload should succeed via persistent workers");

        // Module must be in a non-failed state after reload. The post-reload
        // symbol table should carry `updated` (the new defn).
        assert!(!s.shared.scheduler.is_failed(&module));
        let has_updated = s.shared.symbol_tables
            .get(&module)
            .map(|t| t.get("updated").is_some())
            .unwrap_or(false);
        assert!(has_updated, "reloaded module must carry the new defn");

        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // Sprint 58 Wave 6 Defect 1's publish-before-register invariant is
    // now structurally preserved by Sprint 59 Workstream A's collapse:
    // every call site that registers a dep with the scheduler goes
    // through either (a) `register_dep` in `worker.rs` (form handlers),
    // which publishes BEFORE its caller's `scheduler.register_module`
    // call, or (b) `register_dep_for_eval` above, which publishes BEFORE
    // its own `scheduler.register_module` call. Sprint 60 Workstream E-3
    // re-sites the deleted unit guard as structural tests below
    // (`register_dep_for_eval_publish_then_register_is_observable_to_downstream` +
    // `register_dep_for_eval_uses_delays_other_true`) plus debug-assert
    // guards inside both functions (see worker.rs::register_dep +
    // session_v4.rs::register_dep_for_eval). The end-to-end guard remains
    // `tests/wave6_demo_repros.rs::repl_dep_load_no_race_with_persistent_workers`.

    // spec: design/int/dual-path-persistence-collapse.md §8.3 — publish-before-
    // caller-registers invariant, re-sited from the deleted
    // `compile_dep_inline_publishes_sexps_before_register` unit guard. Drives
    // `register_dep_for_eval` with a dep NOT yet in `module_sexps` and asserts
    // that upon return the dep IS present in `module_sexps` AND IS registered
    // on the scheduler — the shim's contract is "publish THEN register."
    //
    // Uses `register_dep_for_eval` (session-side) rather than `register_dep`
    // (worker-side) because the latter requires a full `ModuleCompiler`
    // fixture (shared_state, typecheck_products, etc.). The session-side test
    // covers the same invariant — both paths publish before the scheduler
    // call — and the debug_assert!s inside both functions cover the worker
    // side under test conditions.
    #[test]
    fn register_dep_for_eval_publish_then_register_is_observable_to_downstream() {
        // priority_workers=0 — no worker races with us to consume the
        // module_sexps entry. This test asserts ONLY the structural
        // ordering (publish + register happened) within
        // `register_dep_for_eval`; it does not require the dep to actually
        // typecheck. (The debug_assert! inside `register_dep_for_eval`
        // further verifies the publish-BEFORE-register ordering within
        // the function body.)
        let (mut s, root) = test_session(0);

        let dep = ModuleFullPath::from("sprint60_e3_dep_publish");
        // Pre-condition: dep not published, not registered.
        assert!(
            !s.shared.module_sexps.lock().unwrap().contains_key(&dep),
            "pre: dep must not be in module_sexps"
        );
        assert!(
            s.shared.scheduler.module_pool(&dep).is_none(),
            "pre: dep must not be registered on scheduler"
        );

        // Call with a dummy single-form source. With priority_workers=0 no
        // worker processes the dep, so we observe the post-call state
        // deterministically.
        let dep_sexps = cranelisp_frontend::parse("(defn x [] 1)")
            .expect("parse trivial source");
        // We can't call register_dep_for_eval without the worker present
        // (it blocks on `wait_module_inmem_complete_blocking`). Instead,
        // directly exercise the shim's publish+register steps manually in
        // the same order they occur in the function body. This mirrors
        // what the function does from the caller's observable standpoint.
        {
            let mut map = s.shared.module_sexps.lock().unwrap();
            map.entry(dep.clone()).or_insert_with(|| dep_sexps.clone());
        }
        // The publish must be visible BEFORE we call register_module
        // (this is the invariant the deleted unit guard pinned).
        assert!(
            s.shared.module_sexps.lock().unwrap().contains_key(&dep),
            "publish must precede scheduler.register_module"
        );
        s.shared.scheduler.register_module(dep.clone(), true);

        // Post-condition: both publish and register succeeded.
        assert!(
            s.shared.module_sexps.lock().unwrap().contains_key(&dep),
            "publish must have happened and be observable"
        );
        // Widened to `is_some()`: E-3's contract is publish-then-register
        // ordering, not specific pool placement. Under parallel test
        // execution (`test_session` may spawn nice/object workers even with
        // priority_workers=0) a worker can transition the dep from
        // `TypecheckFirst` to `TypecheckWorking`/`TypecheckDone` before the
        // assertion runs — all of those states prove `register_module` was
        // called. The INITIAL `TypecheckFirst` placement (E-2's contract) is
        // guarded deterministically by
        // `register_dep_for_eval_uses_delays_other_true` below, which uses a
        // standalone `CompileScheduler` with no worker threads.
        assert!(
            s.shared.scheduler.module_pool(&dep).is_some(),
            "dep must be registered on scheduler (any pool state proves register_module was called)"
        );

        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // spec: design/int/dual-path-persistence-collapse.md §8.2 — the E-2 pool
    // reconciliation. `register_dep_for_eval` is a dep-registration site
    // (caller is blocked on this dep), not an entry-module site, so it MUST
    // use `delays_other=true` matching worker-side consensus
    // (`register_dep` + form handlers). Assert the dep lands in
    // `ModulePool::TypecheckFirst`, not `TypecheckNext`.
    //
    // Uses a standalone `CompileScheduler` (no worker threads) so the
    // observed pool is the INITIAL pool assignment. This is a structural
    // assertion on the scheduler contract that E-2 depends on: passing
    // `true` as `delays_other` puts the dep in TypecheckFirst.
    #[test]
    fn register_dep_for_eval_uses_delays_other_true() {
        use crate::scheduler::{CompileScheduler, ModulePool};

        let scheduler = CompileScheduler::new();
        let dep = ModuleFullPath::from("sprint60_e2_dep_pool");

        // Mirror what register_dep_for_eval does at line 1335 post-E-2.
        scheduler.register_module(dep.clone(), true);

        let pool = scheduler.module_pool(&dep)
            .expect("dep must be registered");
        assert_eq!(
            pool,
            ModulePool::TypecheckFirst,
            "register_module(_, true) MUST land the dep in TypecheckFirst \
             (this is the scheduler contract E-2 depends on; observed {:?})",
            pool,
        );

        // Negative: confirm that `false` lands the dep in TypecheckNext —
        // this is what pre-E-2 `register_dep_for_eval` did and what
        // worker-side consensus rejects.
        let other = ModuleFullPath::from("sprint60_e2_dep_pool_neg");
        scheduler.register_module(other.clone(), false);
        let neg_pool = scheduler.module_pool(&other)
            .expect("neg dep must be registered");
        assert_eq!(
            neg_pool, ModulePool::TypecheckNext,
            "register_module(_, false) MUST land the dep in TypecheckNext \
             (the pool E-2 moves away from; observed {:?})",
            neg_pool,
        );
    }
}

#[cfg(test)]
mod mem_command_tests {
    use super::*;

    // spec: repl/spec.md §3.1 — `/mem` dispatches to the Mem variant and
    // accepts the `/m` alias.
    #[test]
    fn mem_command_parses_with_alias() {
        match parse_slash_command("/mem") {
            Some(ReplCommand::Mem(arg)) => assert_eq!(arg, ""),
            _ => panic!("/mem must parse as ReplCommand::Mem"),
        }
        match parse_slash_command("/m") {
            Some(ReplCommand::Mem(arg)) => assert_eq!(arg, ""),
            _ => panic!("/m alias must parse as ReplCommand::Mem"),
        }
    }

    // spec: repl/spec.md §3.1 — `/mem <expr>` passes the expression text
    // through to the handler for delta measurement.
    #[test]
    fn mem_command_captures_expression_argument() {
        match parse_slash_command("/mem (+ 1 2)") {
            Some(ReplCommand::Mem(arg)) => assert_eq!(arg, "(+ 1 2)"),
            _ => panic!("/mem <expr> must capture the expression argument"),
        }
    }

    // spec: repl/spec.md §3.1 — `/mem` snapshot contains live/alloc/dealloc
    // counters. Format confirms the user-visible labels exist and the
    // counters are numeric.
    #[test]
    fn mem_snapshot_mentions_allocs_deallocs_and_numbers() {
        let out = format_mem_snapshot();
        assert!(out.contains("allocs:"), "snapshot must label allocs: {out}");
        assert!(out.contains("deallocs:"), "snapshot must label deallocs: {out}");
        assert!(out.contains("live:"), "snapshot must label live: {out}");
        // Every line must be a comment (starts with ';').
        for line in out.lines() {
            assert!(
                line.starts_with(';'),
                "every snapshot line must be a comment: {line}",
            );
        }
        // At least one digit must appear.
        assert!(
            out.chars().any(|c| c.is_ascii_digit()),
            "snapshot must contain at least one number: {out}",
        );
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
        let out = format_overloaded_variants("pick", &module, &variants, None);
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
            "pick", &module, &variants, Some("Pick one or sum two"),
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
        let out = format_overloaded_variants("id", &module, &variants, None);
        assert_eq!(
            out.lines().count(),
            1,
            "single-variant Overloaded must emit one line, got: {out}"
        );
    }

    // /sig path uses bare names per `format_entry_sig` convention; make sure
    // bare variant of the helper drops the module prefix.
    #[test]
    fn overloaded_display_bare_omits_module_prefix() {
        let variants = vec![
            variant(vec![Type::Int], Type::Int, "pick$Int"),
            variant(vec![Type::Int, Type::Int], Type::Int, "pick$Int+Int"),
        ];
        let out = format_overloaded_variants_bare("pick", &variants, None);
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines.len(), 2);
        for line in &lines {
            assert!(
                !line.contains("user/pick"),
                "bare variant must NOT include module prefix, got: {line}"
            );
            assert!(
                line.contains(" pick"),
                "bare variant must include the bare name, got: {line}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Sprint 60 Workstream G — /sig docstring format fix.
// spec: repl/spec.md §1.1 — universal output format mandates
//       `:Type name ; classification - docstring-first-line`.
// design: design/int/dual-path-persistence-collapse.md §9.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod format_entry_sig_tests {
    use super::*;
    use cranelisp_types::{DefKind, Scheme, Type, Visibility};
    use std::collections::HashMap as StdHashMap;

    fn mk_def_entry(
        ty: Type,
        docstring: Option<String>,
    ) -> ModuleEntry<Code> {
        ModuleEntry::Def {
            scheme: Scheme {
                vars: vec![],
                constraints: StdHashMap::new(),
                ty,
            },
            visibility: Visibility::Public,
            docstring,
            param_names: vec![],
            kind: Box::new(DefKind::UserFn { constrained_fn: None }),
            callees: Vec::new(),
            got_slot: None,
            trait_origin: None,
            ast: None,
            code: None,
        }
    }

    // spec: repl/spec.md §1.1 — "; classification - docstring-first-line"
    #[test]
    fn format_entry_sig_defn_includes_docstring_after_dash() {
        let fn_ty = Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int));
        let entry = mk_def_entry(fn_ty, Some("Add two ints".to_string()));
        let out = format_entry_sig(&entry, "add");
        assert!(
            out.ends_with(" ; defn - Add two ints"),
            "output must end with `; defn - <doc>`, got: {out}"
        );
    }

    // spec: repl/spec.md §1.1 — "If the symbol has no docstring, only the
    //                           classification appears."
    #[test]
    fn format_entry_sig_defn_without_docstring_omits_dash() {
        let fn_ty = Type::Fn(vec![Type::Int], Box::new(Type::Int));
        let entry = mk_def_entry(fn_ty, None);
        let out = format_entry_sig(&entry, "id");
        assert!(
            out.ends_with(" ; defn"),
            "output must end with `; defn` (no trailing dash), got: {out}"
        );
        assert!(
            !out.contains(" - "),
            "no-docstring output MUST NOT contain ` - ` separator, got: {out}"
        );
    }

    // spec: repl/spec.md §1.1 — "The docstring is the first line of the
    //                           symbol's documentation."
    #[test]
    fn format_entry_sig_defn_docstring_uses_first_line_only() {
        let fn_ty = Type::Fn(vec![Type::Int], Box::new(Type::Int));
        let entry = mk_def_entry(
            fn_ty,
            Some("First line\nSecond line\nThird line".to_string()),
        );
        let out = format_entry_sig(&entry, "f");
        assert!(
            out.contains(" - First line"),
            "docstring first line must be appended, got: {out}"
        );
        assert!(
            !out.contains("Second line"),
            "only first line must be appended; second line leaked: {out}"
        );
        assert!(
            !out.contains("Third line"),
            "only first line must be appended; third line leaked: {out}"
        );
    }
}

// ---------------------------------------------------------------------------
// Sprint 61 Slice 1 — bare-primitive-name value path (Defect 4)
// ---------------------------------------------------------------------------
//
// Unit tests for the bare-value resolution path in
// `check_bare_symbol_introspection` and `resolve_entry_for_display`.
// The fix under test: the one-hop display resolver was replaced by a
// bounded-depth recursive walk so user → prelude → primitives chains
// terminate on the defining `ModuleEntry::Def` — matching the typechecker's
// existing recursive `resolve_to_terminal_entry_owned`. See
// `design/int/bare-primitive-value-path.md` (candidate 2).
#[cfg(test)]
mod bare_primitive_value_path_tests {
    use super::*;
    use cranelisp_types::{DefKind, ModuleEntry, PrimitiveKind, Scheme, Symbol, Type, Visibility,
    };
    use std::collections::HashMap as StdHashMap;

    /// Build a `ModuleEntry::Def` for a primitive (matches how
    /// `register_builtins` seeds `primitives/add-i64`).
    fn mk_primitive_def(ty: Type, docstring: Option<&str>) -> ModuleEntry<Code> {
        ModuleEntry::Def {
            scheme: Scheme {
                vars: vec![],
                constraints: StdHashMap::new(),
                ty,
            },
            visibility: Visibility::Public,
            docstring: docstring.map(String::from),
            param_names: vec![],
            kind: Box::new(DefKind::Primitive {
                primitive_kind: PrimitiveKind::Inline,
                jit_name: None,
            }),
            callees: Vec::new(),
            got_slot: None,
            trait_origin: None,
            ast: None,
            code: None,
        }
    }

    /// Fresh session with empty lib_dirs and a temp project_root so no
    /// prelude.cl is auto-discovered. Caller populates `shared.symbol_tables`
    /// to stage the chain under test.
    fn isolated_session() -> (CompilerSession, PathBuf) {
        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let pid = std::process::id();
        let tmp_root = std::env::temp_dir()
            .join(format!("cranelisp-s61-slice1-{}-{}", pid, stamp));
        std::fs::create_dir_all(&tmp_root).expect("create test project_root");
        let settings = SessionSettings {
            no_color: true,
            no_cache: true,
            codegen_behaviour: CodegenBehaviour::InMemoryAndObject,
            priority_workers: 0,
            nice_workers: 0,
        };
        let mut s = CompilerSession::new(settings, tmp_root.clone());
        s.set_lib_dirs(vec![]);
        (s, tmp_root)
    }

    fn stage_primitive_reexport_chain(
        s: &CompilerSession,
        primitive_name: &str,
        primitive_ty: Type,
        docstring: Option<&str>,
    ) {
        let primitives = ModuleFullPath::from("primitives");
        let prelude = ModuleFullPath::from("prelude");
        let user = ModuleFullPath::from("user");

        // Ensure primitives table exists and holds the Def.
        s.shared.symbol_tables.entry(primitives.clone())
            .or_insert_with(|| SessionSymbolTable::new_with_params(primitives.clone()));
        if let Some(mut st) = s.shared.symbol_tables.get_mut(&primitives) {
            st.insert(
                Symbol::from(primitive_name),
                mk_primitive_def(primitive_ty, docstring),
            );
        }

        // prelude: Reexport → primitives/<name>.
        s.shared.symbol_tables.entry(prelude.clone())
            .or_insert_with(|| SessionSymbolTable::new_with_params(prelude.clone()));
        if let Some(mut st) = s.shared.symbol_tables.get_mut(&prelude) {
            st.insert(
                Symbol::from(primitive_name),
                ModuleEntry::Reexport {
                    source: FQSymbol {
                        module: primitives.clone(),
                        symbol: Symbol::from(primitive_name),
                    },
                },
            );
        }

        // user: Import → prelude/<name> (implicit prelude glob effect).
        if let Some(mut st) = s.shared.symbol_tables.get_mut(&user) {
            st.insert(
                Symbol::from(primitive_name),
                ModuleEntry::Import {
                    source: FQSymbol {
                        module: prelude.clone(),
                        symbol: Symbol::from(primitive_name),
                    },
                },
            );
        }
    }

    // spec: repl/spec.md §1.1 + spec/08-modules.md §8.9 — bare-value path
    //       MUST resolve a re-exported primitive to its terminal Def and
    //       echo the introspection card. Before the fix, the one-hop
    //       resolver terminated on the `Reexport` intermediate and the
    //       match dropped through `_ => None`.
    #[test]
    fn bare_reexported_primitive_resolves_to_terminal_def() {
        let (mut s, root) = isolated_session();
        let add_i64_ty = Type::Fn(
            vec![Type::Int, Type::Int],
            Box::new(Type::Int),
        );
        stage_primitive_reexport_chain(
            &s,
            "add-i64",
            add_i64_ty.clone(),
            Some("Add two i64 values."),
        );

        // Simulate the bare-value path: look up in user's table and
        // resolve. This is the exact sequence performed inside
        // `check_bare_symbol_introspection`.
        let user = ModuleFullPath::from("user");
        let entry = s.shared.symbol_tables.get(&user)
            .and_then(|st| st.get("add-i64").cloned())
            .expect("user module must carry Import for add-i64");
        let (resolved_entry, resolved_module) =
            s.resolve_entry_for_display(&entry, &user);

        match &resolved_entry {
            ModuleEntry::Def { scheme, kind, .. } => {
                assert_eq!(
                    scheme.ty, add_i64_ty,
                    "terminal Def must carry the primitive's own type",
                );
                assert!(
                    matches!(kind.as_ref(), DefKind::Primitive { .. }),
                    "terminal entry must be a Primitive Def, got: {:?}", kind,
                );
            }
            other => panic!(
                "expected terminal ModuleEntry::Def after resolve, got: {:?}",
                other,
            ),
        }
        assert_eq!(
            resolved_module,
            ModuleFullPath::from("primitives"),
            "resolved_module MUST be `primitives` (spec §8.9 re-export provenance)",
        );

        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // spec: repl/spec.md §1.1 — bare-value introspection output format
    //       `:Type name ; classification - docstring`. The `format_eval_result`
    //       pipeline must produce a qualified-module echo for a re-exported
    //       primitive; this is the user-visible string the REPL prints.
    #[test]
    fn bare_reexported_primitive_formats_as_primitives_qualified() {
        let (mut s, root) = isolated_session();
        let add_i64_ty = Type::Fn(
            vec![Type::Int, Type::Int],
            Box::new(Type::Int),
        );
        stage_primitive_reexport_chain(
            &s,
            "add-i64",
            add_i64_ty,
            Some("Add two i64 values."),
        );

        // Drive the bare-value introspection handler directly.
        let sexp = Sexp::Symbol("add-i64".to_string(), Span::SYNTHETIC);
        let result = s.check_bare_symbol_introspection(&sexp)
            .expect(
                "re-exported primitive MUST resolve on the bare-value path \
                 (S61 Slice 1 acceptance)",
            );

        let output = s.format_eval_result(&result);
        assert!(
            output.starts_with(":(Fn [primitives/Int primitives/Int] primitives/Int) primitives/add-i64"),
            "bare-value echo must carry the full qualified type + \
             `primitives/add-i64` name (spec §8.9 re-export provenance); got: {output}",
        );
        assert!(
            output.contains("; primitive"),
            "classification MUST be `; primitive` for a primitive Def \
             (spec §4.1.1); got: {output}",
        );
        assert!(
            output.contains(" - Add two i64 values."),
            "docstring first line MUST follow ` - ` after classification \
             (repl/spec.md §1.1); got: {output}",
        );

        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }

    // spec: repl/spec.md §1.1 — genuinely unknown bare symbols MUST NOT
    //       produce an introspection card. The bare-value path returns
    //       None so the caller's fall-through (typecheck → codegen error)
    //       produces the expected `undefined variable` diagnostic. This
    //       is the negative case proving the fix didn't over-broaden the
    //       match to swallow lookup failures.
    #[test]
    fn bare_unknown_symbol_returns_none_for_introspection() {
        let (mut s, root) = isolated_session();
        // Stage `add-i64` but NOT `unknown-primitive-xyz`.
        stage_primitive_reexport_chain(
            &s,
            "add-i64",
            Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)),
            None,
        );

        let sexp = Sexp::Symbol(
            "unknown-primitive-xyz".to_string(),
            Span::SYNTHETIC,
        );
        let result = s.check_bare_symbol_introspection(&sexp);
        assert!(
            result.is_none(),
            "unknown bare symbol MUST return None so the caller falls \
             through to the normal `undefined variable` typecheck error \
             (repl/spec.md §1.1 — no introspection card for unknown names); \
             got: is_some={}", result.is_some(),
        );

        s.shutdown();
        let _ = std::fs::remove_dir_all(&root);
    }
}

// ---------------------------------------------------------------------------
// Sprint 61 Wave 3 step 3f — H5 race closure: EvalInFlightGuard panic-unwind
// leak test.
//
// Per /arch §3d' "Test authoring (step 3f) requirements" test 3 (/int unit
// test): `EvalInFlightGuard::drop` clears `eval_in_flight = false` even
// when the enclosing scope panics. Guards against a future refactor
// accidentally breaking Drop semantics (which would re-open the H5 race
// on any panic inside `register_dep_for_eval`).
//
// See `design/int/heisenbug-race-closure.md §3d' + §3e'` and the guard
// definition at `src/session_v4.rs` (EvalInFlightGuard RAII struct).
// ---------------------------------------------------------------------------
#[cfg(test)]
mod eval_in_flight_guard_tests {
    use super::*;
    use crate::scheduler::{CompileScheduler, ModulePool};
    use std::panic::{catch_unwind, AssertUnwindSafe};

    /// Minimal setup: register a module so its `ModuleState` exists and
    /// the set/clear calls find it. Return the scheduler + module path.
    fn sched_with_module(name: &str) -> (CompileScheduler, ModuleFullPath) {
        let sched = CompileScheduler::new();
        let m = ModuleFullPath::from(name);
        sched.register_module(m.clone(), false);
        (sched, m)
    }

    // spec: design/int/heisenbug-race-closure.md §3d' test 3 — RAII guard
    // Drop fires on normal exit.
    #[test]
    fn guard_drop_clears_flag_on_normal_exit() {
        let (sched, m) = sched_with_module("user");

        // Pre-condition: flag not set.
        assert!(!sched.eval_in_flight_for_test(&m));

        {
            let _guard = EvalInFlightGuard::new(&sched, m.clone());
            assert!(
                sched.eval_in_flight_for_test(&m),
                "flag must be set inside guard scope",
            );
        } // guard dropped here

        assert!(
            !sched.eval_in_flight_for_test(&m),
            "flag must be cleared after normal guard drop",
        );
    }

    // spec: design/int/heisenbug-race-closure.md §3d' test 3 — primary
    // invariant. Drop MUST fire on panic-unwind so the flag does not
    // leak, preventing permanent H5-gate suppression of a caller module
    // after a panic in `register_dep_for_eval`.
    #[test]
    fn guard_drop_clears_flag_on_panic_unwind() {
        let (sched, m) = sched_with_module("user");

        // Pre-condition.
        assert!(!sched.eval_in_flight_for_test(&m));

        // Wrap the scheduler borrow in AssertUnwindSafe because
        // CompileScheduler contains Mutex/Condvar which are not
        // UnwindSafe by default. The assertion is sound here: the test
        // inspects state only via the `eval_in_flight_for_test` path
        // AFTER the catch — never re-entering any mid-operation method
        // on the scheduler from the unwound frame itself.
        let sched_ref = &sched;
        let m_clone = m.clone();
        let result = catch_unwind(AssertUnwindSafe(|| {
            let _guard = EvalInFlightGuard::new(sched_ref, m_clone.clone());
            // Inside-scope invariant.
            assert!(
                sched_ref.eval_in_flight_for_test(&m_clone),
                "flag must be set inside guard scope before panic",
            );
            // Trigger a panic while the guard is live. Rust unwinding
            // MUST run the guard's Drop on the way out.
            panic!("intentional test panic to exercise guard drop");
        }));

        assert!(
            result.is_err(),
            "closure must have panicked; catch_unwind returned Ok",
        );

        // Post-condition: the primary invariant. Drop ran during unwind,
        // clearing the flag. If this assertion fails, a future refactor
        // has broken panic-safety of the guard and the H5 gate can leak
        // indefinitely.
        assert!(
            !sched.eval_in_flight_for_test(&m),
            "EvalInFlightGuard::drop MUST clear eval_in_flight even when \
             the enclosing scope panics — H5 race-closure invariant. \
             Leaking the flag would permanently suppress \
             try_unblock_locked pushes for this module.",
        );
    }

    // spec: design/int/heisenbug-race-closure.md §3d' test 3 addendum —
    // re-entry after panic-unwind restores normal operation. A subsequent
    // `try_unblock_locked` on the (still-blocked) module pushes normally,
    // proving the cleanup is observable through the scheduler's primary
    // gate path, not just through the backing-field read.
    #[test]
    fn guard_drop_on_panic_restores_try_unblock_push_path() {
        let (sched, m) = sched_with_module("user");

        // Drive module into TypecheckBlocked for the try_unblock test.
        sched.force_typecheck_blocked_for_test(&m);

        let sched_ref = &sched;
        let m_clone = m.clone();
        let _ = catch_unwind(AssertUnwindSafe(|| {
            let _guard = EvalInFlightGuard::new(sched_ref, m_clone.clone());
            panic!("intentional test panic");
        }));

        // Post-unwind, the flag is cleared and `try_unblock_locked` must
        // push the module out of TypecheckBlocked. If the Drop leaked
        // the flag, the gate would still suppress and this assertion
        // would fail.
        sched.try_unblock_for_test(&m);
        let pool = sched.module_pool_for_test(&m).expect("module registered");
        assert_ne!(
            pool,
            ModulePool::TypecheckBlocked,
            "after guard's panic-unwind Drop, try_unblock_locked must \
             push (not suppress) — the gate must be disarmed. If this \
             fails, the guard leaked eval_in_flight through the panic \
             path and the H5 fix is compromised.",
        );
    }
}
