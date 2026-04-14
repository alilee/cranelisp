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

use cranelisp_types::{
    CheckResult, CodegenBehaviour, CranelispError,
    DefKind, FQSymbol, MacroClauseInfo, MacroParam, ModuleEntry, ModuleFullPath,
    ModuleStrategy, Sexp, Span, Symbol, SymbolTable, TopLevel,
    TraitName, Type, TypeName, Warning,
};

use cranelisp_typecheck::{CheckState, TypeCheckEnv};

use crate::platform::LoadedPlatform;
use crate::platform_registry::PlatformRegistry;
use crate::scheduler::CompileScheduler;
use crate::worker::ModuleCompiler;

// Re-export display functions so tests can import from session_v4 instead of repl.
pub use cranelisp_backend::display::format_result_value;
use cranelisp_backend::display::{format_type_qualified, format_scheme_display};

// ---------------------------------------------------------------------------
// ReadOnlyMacroResolver — for /expand slash command
// ---------------------------------------------------------------------------

/// Read-only macro resolver for the /expand slash command.
///
/// Same lookup logic as `SymbolTableMacroResolver` (follows Import/Reexport
/// chains) but never triggers compilation. If a macro's clauses are not
/// compiled, returns `Ok(None)` (silently skipped).
struct ReadOnlyMacroResolver<'a> {
    symbol_tables: &'a dashmap::DashMap<ModuleFullPath, SymbolTable>,
    codegen_products: &'a dashmap::DashMap<ModuleFullPath, CodegenProduct>,
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
        let macro_sym = Symbol::from(name);
        let mut compiled_clauses = Vec::new();
        for (idx, clause_info) in clauses.iter().enumerate() {
            let clause_name = Symbol::from(format!("__macro_{}_clause_{}", macro_sym, idx));
            match self.codegen_products.get(&defining_module)
                .and_then(|cp| cp.code.get(&clause_name).map(|c| c.ptr))
            {
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

/// Format a module entry signature for /sig display.
fn format_entry_sig(entry: &ModuleEntry, name: &str) -> String {
    match entry {
        ModuleEntry::Def { scheme, kind, .. } => {
            let classification = match kind.as_ref() {
                DefKind::SpecialForm { description } => {
                    return format!("{name} ; special form - {description}");
                }
                DefKind::Overloaded { .. } => "defn (multi)",
                _ => "defn",
            };
            format!(":{} {} ; {}", scheme.ty, name, classification)
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
pub struct TypecheckProduct {
    /// Per-module GOT table. Allocated at module registration, base address
    /// stable for process lifetime. Slot indices assigned during typecheck,
    /// code pointers filled during codegen. Arc-shared so codegen workers
    /// can read the base address concurrently.
    pub got: std::sync::Arc<cranelisp_backend::got::GotTable>,
    pub file_path: Option<PathBuf>,
    /// Module source text, retained in --repl mode for /source introspection.
    /// Sexp spans index into this string. None for cache-hit modules and batch mode.
    pub source_text: Option<String>,
}

/// Transient codegen input for a module.
/// Produced by typecheck, consumed by both JIT (priority workers) and .o (nice
/// workers) codegen. Removed when scheduler signals both `inmem_done` and
/// `object_done`. See session-restructure.md.
///
/// Stores the full `CheckResult` (including `constrained_fn_names`) so that
/// the nice worker gets the same information as the priority worker. This
/// fixes the pre-existing bug where `constrained_fn_names` was discarded at
/// stash time and the object path used an empty set.
pub struct CodegenInput {
    pub check: cranelisp_types::CheckResult,
    pub program: Vec<TopLevel>,
}

/// Per-module codegen output: compiled code + optional cache linker.
/// Entry created when codegen starts for a module. See session-restructure.md.
pub struct CodegenProduct {
    /// Some if loaded from cache .o; owns code_regions + data_regions.
    pub linker: Option<cranelisp_backend::cache::Linker>,
    /// Per-symbol codegen output. Additive for REPL redefinition over cache.
    pub code: dashmap::DashMap<Symbol, Code>,
}

impl Default for CodegenProduct {
    fn default() -> Self {
        CodegenProduct {
            linker: None,
            code: dashmap::DashMap::new(),
        }
    }
}

/// TARGET STATE: per-symbol compiled code. Replaces DefCodegen's code_ptr + kept jit_modules.
/// Owns the JIT mmap'd executable pages. See session-restructure.md.
pub struct Code {
    /// Cranelift JIT module — owns mmap'd executable pages. Dropping frees code.
    pub jit: cranelisp_backend::jit::Jit,
    /// Code pointer (also stored in GOT slot).
    pub ptr: *const u8,
}

// SAFETY: Code contains raw pointer (code_ptr) and Jit (which has mmap'd
// pages). Both are stable after JIT finalization, valid for process lifetime.
unsafe impl Send for Code {}
unsafe impl Sync for Code {}

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

    /// Cache directory for .o and .meta.json output (Step 10).
    /// None when caching is disabled (e.g., `--run` without `--link`).
    pub cache_dir: Option<PathBuf>,

    /// Collected .o file paths written by nice workers (Step 10).
    /// Used by `--link` to pass all .o files to the system linker.
    pub compiled_o_paths: Mutex<Vec<PathBuf>>,

    /// Flag for nice worker priority promotion during hot flush (Step 10).
    /// When set to true, nice workers self-promote to normal OS priority.
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

    // -- Stateless TC: shared state (Sprint 51) --
    // The single source of truth for per-module symbol data. Formerly owned
    // by TypeChecker; now on SharedState for direct access by all workers.

    /// Per-module symbol tables. The single source of truth for per-module
    /// symbol data. Workers and session methods access this directly.
    pub symbol_tables: dashmap::DashMap<ModuleFullPath, SymbolTable>,

    /// Monotonic counter for fresh type variable IDs. Shared across all
    /// TypeCheckEnv instances for concurrent workers.
    pub next_type_id: AtomicU32,

    /// REPL carry-forward: current module path for REPL prompt and eval.
    /// Batch compilation sets this per-worker; REPL uses it across evals.
    pub current_module: Mutex<ModuleFullPath>,

    /// REPL carry-forward: CheckState that persists across REPL evals.
    /// Contains substitution, scope stack, overloads, module aliases.
    /// None in batch mode (CheckState is stack-local per worker).
    pub repl_check_state: Mutex<Option<CheckState>>,

    // -- Target data model (session-restructure.md) --
    // DashMaps are inherently concurrent and accessible to both priority
    // and nice workers via Arc<SharedState>.

    /// Per-module typecheck products (replaces TC-internal storage).
    pub typecheck_products: dashmap::DashMap<ModuleFullPath, TypecheckProduct>,
    /// Transient codegen inputs (replaces module_outputs + object_codegen_inputs).
    pub codegen_inputs: dashmap::DashMap<ModuleFullPath, CodegenInput>,
    /// Per-module codegen products (replaces ModuleGotRegistry + def_codegen + kept_code).
    pub codegen_products: dashmap::DashMap<ModuleFullPath, CodegenProduct>,
    /// Per-symbol introspection data, REPL-only (replaces def_codegen for slash commands).
    pub introspection: dashmap::DashMap<FQSymbol, Introspection>,
    /// Per-module structural metadata for source regeneration (repl/spec.md §15).
    /// Tracks import/export/mod/platform specs. Populated during form processing.
    pub module_structures: dashmap::DashMap<ModuleFullPath, crate::save::ModuleStructure>,
}

/// The compiler session — scheduler-driven concurrent compilation.
///
/// One session per process. Owns the TypeChecker, codegen state, and
/// scheduler. `register_module` spawns scoped priority worker threads
/// that process modules from the scheduler's work queue.
pub struct CompilerSession {
    /// Lib directories for module resolution (§8.11.2 tier 3).
    /// Does NOT include project_root — that is tier 2 and searched separately.
    pub lib_dirs: Vec<PathBuf>,
    /// Extra platform DLL search directories (§8.11.3 tier 3).
    /// Searched after project_root/platforms/ and lib_dir/platforms/.
    pub platform_dirs: Vec<PathBuf>,
    /// Loaded platform DLL handles. Must remain alive for the process lifetime
    /// so that function pointers into the DLL code segments stay valid.
    pub loaded_platforms: Vec<LoadedPlatform>,

    /// Thread-safe state shared with nice worker threads. Wrapped in Arc
    /// so workers get an independent clone — no aliasing between `&mut self`
    /// (used by priority worker operations) and the shared reference held
    /// by nice workers. All SharedState fields are inherently thread-safe
    /// (Mutex, AtomicBool, DashMap, read-only).
    pub shared: Arc<SharedState>,

    /// Number of priority worker threads to spawn for module compilation.
    /// Defaults to 1 for determinism in tests; production uses num_cpus().
    priority_workers: usize,

    /// Project root directory (read-only after construction).
    pub project_root: PathBuf,

    /// Unified platform function registry (Step 8).
    /// Populated during platform loading, read-only during codegen.
    pub platform_registry: PlatformRegistry,

    // -- REPL-specific state (pipeline-v4.md §6) --

    /// Modules that failed reload (file watcher). While non-empty, expression
    /// evaluation is blocked.
    pub error_modules: HashSet<ModuleFullPath>,

    /// File watcher for REPL mode. Initialized via `init_watcher()` after
    /// construction. None in batch/link modes or if OS watcher unavailable.
    pub watcher: Option<crate::watch::FileWatcher>,

    /// Nice worker thread handles. Joined in `shutdown()`.
    nice_worker_handles: Vec<std::thread::JoinHandle<()>>,
    /// Nice worker count (stored for `wait_object_complete` guard).
    nice_workers: usize,
}

impl CompilerSession {
    /// Create a new compiler session (pipeline-v4.md §5).
    ///
    /// `settings.priority_workers` controls how many scoped threads are
    /// spawned per `register_module` call. Tests use 1 for determinism.
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

        let priority_workers = std::cmp::max(settings.priority_workers, 1);

        let nice_workers = settings.nice_workers;

        let symbol_tables = dashmap::DashMap::new();
        let next_type_id = AtomicU32::new(0);
        let user_module = ModuleFullPath::from("user");

        // Seed the "user" module before register_builtins (which registers special forms on it).
        symbol_tables.insert(user_module.clone(), SymbolTable::new(user_module.clone()));

        // Seed builtins into symbol tables before any user modules load.
        cranelisp_typecheck::register_builtins(&symbol_tables, &next_type_id);

        let shared = Arc::new(SharedState {
            scheduler: CompileScheduler::new(),
            cache_dir: Some(cache_dir),
            compiled_o_paths: Mutex::new(Vec::new()),
            promote_nice_workers: AtomicBool::new(false),
            cached_modules: Mutex::new(HashSet::new()),
            file_to_module: Mutex::new(HashMap::new()),
            cache_state: Mutex::new(cache_state),
            symbol_tables,
            next_type_id,
            current_module: Mutex::new(user_module.clone()),
            repl_check_state: Mutex::new(Some(CheckState::new(user_module))),
            typecheck_products: dashmap::DashMap::new(),
            codegen_inputs: dashmap::DashMap::new(),
            codegen_products: dashmap::DashMap::new(),
            introspection: dashmap::DashMap::new(),
            module_structures: dashmap::DashMap::new(),
        });

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
            lib_dirs,
            platform_dirs,
            loaded_platforms: Vec::new(),
            shared,
            priority_workers,
            project_root,
            platform_registry: PlatformRegistry::new(),
            error_modules: HashSet::new(),
            watcher: None,
            nice_worker_handles,
            nice_workers,
        }
    }

    // -- Convenience accessors for shared TC state --

    /// Create a TypeCheckEnv borrowing the shared state.
    fn tc_env(&self) -> TypeCheckEnv<'_> {
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
        // Create a new CheckState for the new module.
        // REPL carry-forward state (subst, env, overloads) is lost on module switch.
        // This matches the old behavior where /mod started fresh.
        *self.shared.repl_check_state.lock()
            .unwrap_or_else(|e| e.into_inner()) = Some(CheckState::new(path));
    }

    /// Get a read guard for the current module's symbol table.
    fn current_symbol_table(&self) -> dashmap::mapref::one::Ref<'_, ModuleFullPath, SymbolTable> {
        let module = self.current_module_path();
        self.shared.symbol_tables.get(&module)
            .unwrap_or_else(|| unreachable!("invariant: current_module always exists in symbol_tables"))
    }

    /// Get a read guard for any module's symbol table.
    fn module_table(&self, path: &ModuleFullPath) -> Option<dashmap::mapref::one::Ref<'_, ModuleFullPath, SymbolTable>> {
        self.shared.symbol_tables.get(path)
    }

    /// Resolve a module by name (for /exports command).
    fn resolve_module_by_name(&self, name: &str) -> Option<ModuleFullPath> {
        let tc = self.tc_env();
        let guard = self.shared.repl_check_state.lock()
            .unwrap_or_else(|e| e.into_inner());
        let cs = guard.as_ref()?;
        tc.resolve_module_by_name(cs, name)
    }

    /// Take a snapshot for REPL error recovery.
    fn tc_snapshot(&self) -> cranelisp_types::ReplSnapshot {
        let tc = self.tc_env();
        let cs = self.shared.repl_check_state.lock()
            .unwrap_or_else(|e| e.into_inner());
        let cs = cs.as_ref().expect("REPL check state must be initialized");
        tc.snapshot(cs)
    }

    /// Restore from a snapshot on REPL error.
    fn tc_restore(&self, snapshot: cranelisp_types::ReplSnapshot) {
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
        // and add them to the reload list. Uses module_structures to discover
        // reverse dependencies.
        let changed_modules: HashSet<ModuleFullPath> = modules_to_reload
            .iter()
            .map(|(mp, _)| mp.clone())
            .collect();
        for entry in self.shared.module_structures.iter() {
            let dependent_module = entry.key().clone();
            if changed_modules.contains(&dependent_module) {
                continue; // Already being reloaded directly.
            }
            let structure = entry.value();
            let depends_on_changed = structure.import_specs.iter().any(|spec| {
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
    pub fn regenerate_backing_file(&mut self) {
        let module = self.current_module_path();

        // Get the backing file path from typecheck product.
        let file_path = match self.shared.typecheck_products.get(&module) {
            Some(tp) => match &tp.file_path {
                Some(p) => p.clone(),
                None => {
                    // Entry module may not have a file path yet (fresh session).
                    // Default to {project_root}/{module}.cl.
                    self.project_root.join(format!("{}.cl", module))
                }
            },
            None => self.project_root.join(format!("{}.cl", module)),
        };

        // Read the symbol table for this module.
        let st = match self.shared.symbol_tables.get(&module) {
            Some(st) => st.clone(),
            None => return, // No symbol table — nothing to save.
        };

        // Read structural metadata.
        let structure = self.shared.module_structures
            .get(&module)
            .map(|s| s.clone())
            .unwrap_or_default();

        // Generate source text.
        let source = crate::save::generate_module_source(
            &st,
            &self.shared.introspection,
            &structure,
            &module,
        );

        // Skip writing empty source (no user-defined content).
        if source.trim().is_empty() {
            return;
        }

        // Compute content hash for watcher suppression.
        let hash = cranelisp_backend::cache::hash_source(&source);

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
                .insert(canonical, module);
        }
    }

    /// Reload a single module from its source file.
    ///
    /// Re-reads the file, re-parses, and re-compiles through the worker
    /// pipeline with the existing session state. The module must already
    /// be registered in the scheduler.
    fn reload_module(
        &mut self,
        module_path: &ModuleFullPath,
        file_path: &Path,
    ) -> Result<(), CranelispError> {
        let source = std::fs::read_to_string(file_path).map_err(|e| {
            CranelispError::ModuleError {
                message: format!("cannot read {}: {e}", file_path.display()),
                file: Some(file_path.to_path_buf()),
                span: Span::new(0, 0),
            }
        })?;

        // Re-register through the existing pipeline. The scheduler will
        // reset the module state and re-process it.
        self.shared.scheduler.reset_module(module_path);

        // Remove stale products before recompilation.
        self.shared.typecheck_products.remove(module_path);
        self.shared.codegen_inputs.remove(module_path);
        self.shared.codegen_products.remove(module_path);

        let sexps = cranelisp_frontend::parse(&source)?;

        let module_sexps = Mutex::new({
            let mut map = HashMap::new();
            map.insert(module_path.clone(), sexps);
            map
        });
        let suspend_states = Mutex::new(HashMap::new());

        let platform_registry = std::mem::replace(
            &mut self.platform_registry, PlatformRegistry::new(),
        );
        let platform_mutex = Mutex::new(platform_registry);

        let worker_shared = crate::worker::PriorityWorkerRefs {
            platform_registry: &platform_mutex,
            typecheck_products: &self.shared.typecheck_products,
            codegen_products: &self.shared.codegen_products,
            introspection: Some(&self.shared.introspection),
            scheduler: &self.shared.scheduler,
            module_sexps: &module_sexps,
            suspend_states: &suspend_states,
            lib_dirs: &self.lib_dirs,
            platform_dirs: &self.platform_dirs,
            project_root: &self.project_root,
            shared_state: Some(&self.shared),
        };

        let num_workers = self.priority_workers;
        std::thread::scope(|s| {
            for i in 0..num_workers {
                let shared_ref = &worker_shared;
                std::thread::Builder::new()
                    .name(format!("reload-worker-{}", i))
                    .spawn_scoped(s, move || {
                        crate::worker::priority_worker_thread(shared_ref, i);
                    })
                    .expect("failed to spawn reload worker thread");
            }
        });

        // Move PlatformRegistry back.
        self.platform_registry = platform_mutex.into_inner().unwrap_or_else(|e| e.into_inner());

        // Check if the module ended up in Failed state.
        if self.shared.scheduler.is_failed(module_path) {
            return Err(CranelispError::ModuleError {
                message: format!("module '{}' failed to compile", module_path.as_ref()),
                file: None,
                span: Span::new(0, 0),
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

    /// Register a module with explicit source (internal + test helpers).
    ///
    /// Spawns scoped priority worker threads that process the module and
    /// its dependencies via the scheduler's work queue. Workers park on
    /// blocked modules and pick up ready ones, preventing deadlocks on
    /// multi-module dependency chains.
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
            let hash = cranelisp_backend::cache::hash_source(source);
            let mut cs_guard = self.shared.cache_state.lock().unwrap_or_else(|e| e.into_inner());
            if let Some(cs) = cs_guard.as_mut() {
                cs.source_hashes_mut().insert(module.clone(), hash);
            }
        }

        // Register module with scheduler (entry module, not delaying others).
        self.shared.scheduler.register_module(module.clone(), false);

        // Build shared maps for worker threads.
        let module_sexps = Mutex::new({
            let mut map = HashMap::new();
            map.insert(module.clone(), sexps);
            map
        });
        let suspend_states = Mutex::new(HashMap::new());

        // Temporarily move PlatformRegistry into Mutex so worker
        // threads can lock it. Moved back after the scope exits.
        let platform_registry = std::mem::replace(
            &mut self.platform_registry, PlatformRegistry::new(),
        );
        let platform_mutex = Mutex::new(platform_registry);

        // Build shared worker context for scoped threads.
        let worker_shared = crate::worker::PriorityWorkerRefs {
            platform_registry: &platform_mutex,
            typecheck_products: &self.shared.typecheck_products,
            codegen_products: &self.shared.codegen_products,
            introspection: Some(&self.shared.introspection),
            scheduler: &self.shared.scheduler,
            module_sexps: &module_sexps,
            suspend_states: &suspend_states,
            lib_dirs: &self.lib_dirs,
            platform_dirs: &self.platform_dirs,
            project_root: &self.project_root,
            shared_state: Some(&self.shared),
        };

        // Spawn scoped priority worker threads. They block on the scheduler's
        // condvar when no work is available, and exit when all modules reach
        // TypecheckDone/Complete/Failed (or on shutdown).
        let num_workers = self.priority_workers;
        std::thread::scope(|s| {
            for i in 0..num_workers {
                let shared_ref = &worker_shared;
                std::thread::Builder::new()
                    .name(format!("priority-worker-{}", i))
                    .spawn_scoped(s, move || {
                        crate::worker::priority_worker_thread(shared_ref, i);
                    })
                    .expect("failed to spawn priority worker thread");
            }
            // Scope exits here — all workers join before continuing.
        });

        // Move PlatformRegistry back from Mutex.
        self.platform_registry = platform_mutex.into_inner()
            .unwrap_or_else(|e| e.into_inner());

        // Check scheduler completion — all workers have exited, so this
        // is a non-blocking status check (not a wait).
        self.shared.scheduler.wait_inmem_complete()?;

        Ok(Vec::new())
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
        use crate::worker::{self, ProcessResult};
        use cranelisp_typecheck::ModuleCheckAccumulator;

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
                let mut wctx = ModuleCompiler {
                    symbol_tables: &self.shared.symbol_tables,
                    next_type_id: &self.shared.next_type_id,
                    check_state: repl_cs,
                    current_module: module.clone(),
                    scheduler: &self.shared.scheduler,
                    platform_registry: &mut self.platform_registry,
                    typecheck_products: &self.shared.typecheck_products,
                    codegen_products: &self.shared.codegen_products,
                    introspection: Some(&self.shared.introspection),
                    lib_dirs: &self.lib_dirs,
                    platform_dirs: &self.platform_dirs,
                    project_root: &self.project_root,
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
                    self.compile_dep_inline(&dep_module, &dep_sexps)?;
                    if retry == MAX_DEP_RETRIES - 1 {
                        return Err(CranelispError::ModuleError {
                            message: format!(
                                "dependency chain too deep (>{} retries) while resolving '{}'",
                                MAX_DEP_RETRIES, dep_module,
                            ),
                            file: None,
                            span: Span::SYNTHETIC,
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

        // Build per-module CompilationEnv for both defn codegen and expr eval.
        let env_impl = crate::worker::SessionCompilationEnv {
            tc_modules: &self.shared.symbol_tables,
            typecheck_products: &self.shared.typecheck_products,
            current_module: module.clone(),
        };

        // Codegen: compile definitions directly to codegen_products DashMap.
        crate::worker::codegen_module_symbols(
            &self.platform_registry,
            &self.shared.scheduler,
            module,
            program,
            check,
            &self.shared.symbol_tables,
            &self.shared.typecheck_products,
            &self.shared.codegen_products,
            Some(&self.shared.introspection),
        )?;

        let has_expr = program.iter().any(|tl| matches!(tl, TopLevel::Expr(_)));

        if has_expr {
            let program_vec = program.to_vec();
            let (mut jit_syms, got_defs) = env_impl.collect_jit_setup_for_module(&self.platform_registry);

            // Build traced_fns if the expression contains (trace ...).
            let traced_fns = if Self::program_needs_trace(program) {
                self.build_traced_fns(module)
            } else {
                Vec::new()
            };

            // Trace format override: provide rich formatting via session's type defs.
            let mut trace_extra_symbols: Vec<(String, *const u8)> = Vec::new();
            if !traced_fns.is_empty() {
                trace_extra_symbols.push((
                    "cranelisp_trace_format".to_string(),
                    repl_trace_format as *const u8,
                ));
            }

            // Register test infrastructure externs as JIT symbols.
            let needs_test_externs = Self::program_uses_test_forms(program);
            if needs_test_externs {
                jit_syms.push((
                    "discover-tests".to_string(),
                    discover_tests_extern as *const u8,
                ));
                jit_syms.push((
                    "run-test".to_string(),
                    run_test_extern as *const u8,
                ));
            }

            // Set trace display state so repl_trace_format can access symbol tables.
            let display_state = TraceDisplayState {
                symbol_tables: &self.shared.symbol_tables as *const _,
            };
            if !traced_fns.is_empty() {
                set_trace_display_state(&display_state);
            }

            // Set test runner state for discover-tests/run-test externs.
            let current_module_for_tests = module.clone();
            let test_state = TestRunnerState {
                codegen_products: &self.shared.codegen_products as *const _,
                tc_modules: &self.shared.symbol_tables as *const _,
                current_module: &current_module_for_tests as *const _,
            };
            if needs_test_externs {
                set_test_runner_state(&test_state);
            }

            let result = crate::pipeline::compile_and_execute_expr(
                &jit_syms,
                &got_defs,
                &program_vec,
                check,
                &env_impl,
                &traced_fns,
                &trace_extra_symbols,
                &self.shared.symbol_tables,
                module.clone(),
            );

            if needs_test_externs {
                clear_test_runner_state();
            }
            if !traced_fns.is_empty() {
                clear_trace_display_state();
            }

            let (value, ty) = result?;

            Ok(EvalResult::Val {
                value,
                ty,
                warnings: check.warnings.clone(),
            })
        } else {
            // Definition-only: extract the defined symbol name.
            let last = program.last();

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

    /// Check if a program uses discover-tests or run-test special forms.
    fn program_uses_test_forms(program: &[TopLevel]) -> bool {
        program.iter().any(|tl| {
            if let TopLevel::Expr(e) = tl {
                Self::expr_uses_test_forms(e)
            } else {
                false
            }
        })
    }

    fn expr_uses_test_forms(expr: &cranelisp_types::Expr) -> bool {
        use cranelisp_types::Expr;
        match expr {
            Expr::Apply { callee, args, .. } => {
                if let Expr::Var { name, .. } = callee.as_ref() {
                    let n = name.as_ref();
                    if n == "discover-tests" || n == "run-test" {
                        return true;
                    }
                }
                Self::expr_uses_test_forms(callee) || args.iter().any(Self::expr_uses_test_forms)
            }
            Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
                bindings.iter().any(|(_, e)| Self::expr_uses_test_forms(e))
                    || Self::expr_uses_test_forms(body)
            }
            Expr::If { cond, then_branch, else_branch, .. } => {
                Self::expr_uses_test_forms(cond)
                    || Self::expr_uses_test_forms(then_branch)
                    || Self::expr_uses_test_forms(else_branch)
            }
            Expr::Lambda { body, .. } => Self::expr_uses_test_forms(body),
            Expr::Match { scrutinee, arms, .. } => {
                Self::expr_uses_test_forms(scrutinee)
                    || arms.iter().any(|arm| Self::expr_uses_test_forms(&arm.body))
            }
            Expr::Annotate { expr, .. } => Self::expr_uses_test_forms(expr),
            Expr::VecLit { elements, .. } => elements.iter().any(Self::expr_uses_test_forms),
            Expr::Trace { body, .. } => Self::expr_uses_test_forms(body),
            _ => false,
        }
    }

    /// Check if a program contains `Expr::Trace` that needs
    /// traced function info for GOT-swap codegen.
    fn program_needs_trace(program: &[TopLevel]) -> bool {
        program.iter().any(|tl| {
            if let TopLevel::Expr(e) = tl {
                Self::expr_needs_trace(e)
            } else {
                false
            }
        })
    }

    /// Recursively check if an expression contains trace or run-tests.
    fn expr_needs_trace(expr: &cranelisp_types::Expr) -> bool {
        use cranelisp_types::Expr;
        match expr {
            Expr::Trace { .. } => true,
            Expr::Apply { callee, args, .. } => {
                Self::expr_needs_trace(callee) || args.iter().any(Self::expr_needs_trace)
            }
            Expr::Let { bindings, body, .. } | Expr::ParBind { bindings, body, .. } => {
                bindings.iter().any(|(_, e)| Self::expr_needs_trace(e))
                    || Self::expr_needs_trace(body)
            }
            Expr::If { cond, then_branch, else_branch, .. } => {
                Self::expr_needs_trace(cond)
                    || Self::expr_needs_trace(then_branch)
                    || Self::expr_needs_trace(else_branch)
            }
            Expr::Lambda { body, .. } => Self::expr_needs_trace(body),
            Expr::Match { scrutinee, arms, .. } => {
                Self::expr_needs_trace(scrutinee)
                    || arms.iter().any(|arm| Self::expr_needs_trace(&arm.body))
            }
            Expr::Annotate { expr, .. } => Self::expr_needs_trace(expr),
            Expr::VecLit { elements, .. } => elements.iter().any(Self::expr_needs_trace),
            _ => false,
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
                && !fp.starts_with(&self.project_root) {
                    continue;
                }

            let got_base = tp.got.base_ptr() as i64;

            let cp = match self.shared.codegen_products.get(module_path) {
                Some(cp) => cp,
                None => continue,
            };

            let symbols = match self.shared.symbol_tables.get(module_path) {
                Some(st) => st,
                None => continue,
            };

            for (name, entry) in symbols.all_symbols() {
                if let ModuleEntry::Def { scheme, kind, got_slot: Some(slot), .. } = entry {
                    // Skip constrained polymorphic base names — they're dispatch
                    // placeholders (e.g. `!=`, `+`, `<`), not directly callable.
                    if let DefKind::UserFn { constrained_fn: Some(_) } = kind.as_ref() {
                        continue;
                    }
                    let code_ptr = match cp.code.get(name) {
                        Some(code) => code.ptr as i64,
                        None => continue,
                    };
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

    /// Compile a dependency module inline (for blocked REPL eval).
    fn compile_dep_inline(
        &mut self,
        dep_module: &ModuleFullPath,
        dep_sexps: &[Sexp],
    ) -> Result<(), CranelispError> {
        self.shared.scheduler.register_module(dep_module.clone(), false);

        let mut module_sexps = HashMap::new();
        module_sexps.insert(dep_module.clone(), dep_sexps.to_vec());

        self.tc_env().ensure_module_exists(dep_module);
        let repl_cs = self.shared.repl_check_state.lock()
            .unwrap_or_else(|e| e.into_inner())
            .take()
            .unwrap_or_else(|| CheckState::new(dep_module.clone()));
        let mut ctx = ModuleCompiler {
            symbol_tables: &self.shared.symbol_tables,
            next_type_id: &self.shared.next_type_id,
            check_state: repl_cs,
            current_module: dep_module.clone(),
            scheduler: &self.shared.scheduler,
            platform_registry: &mut self.platform_registry,
            typecheck_products: &self.shared.typecheck_products,
            codegen_products: &self.shared.codegen_products,
            introspection: Some(&self.shared.introspection),
            lib_dirs: &self.lib_dirs,
            platform_dirs: &self.platform_dirs,
            project_root: &self.project_root,
            shared_state: Some(&self.shared),
        };

        crate::worker::priority_worker_loop(&mut ctx, &mut module_sexps)?;
        // Restore REPL check_state.
        *self.shared.repl_check_state.lock()
            .unwrap_or_else(|e| e.into_inner()) = Some(ctx.check_state);

        match self.shared.scheduler.wait_inmem_complete() {
            Ok(()) => Ok(()),
            Err(e) => {
                self.shared.scheduler.reset_all_failed_modules();
                Err(CranelispError::from(e))
            }
        }
    }

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

        // Resolve import/reexport chains.
        let module = self.current_module_path();
        let (resolved_entry, _resolved_module) = self.resolve_entry_for_display(&entry, &module);

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
                    symbol: FQSymbol { module, symbol: Symbol::from(name) },
                    ty: Type::Int,
                    warnings: Vec::new(),
                })
            }
            ModuleEntry::Def { kind: _, scheme, .. } => {
                // Special forms, primitives, and user functions all get
                // introspection display per spec §4.1.1, §4.1.2.
                Some(EvalResult::Def {
                    symbol: FQSymbol { module, symbol: Symbol::from(name) },
                    ty: scheme.ty.clone(),
                    warnings: Vec::new(),
                })
            }
            ModuleEntry::TypeDef { .. } => {
                Some(EvalResult::Def {
                    symbol: FQSymbol { module, symbol: Symbol::from(name) },
                    ty: Type::Int,
                    warnings: Vec::new(),
                })
            }
            ModuleEntry::TraitDecl { .. } => {
                Some(EvalResult::Def {
                    symbol: FQSymbol { module, symbol: Symbol::from(name) },
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
                        symbol: FQSymbol { module, symbol: Symbol::from(name) },
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
    fn typecheck_only(&mut self, expr_src: &str) -> Result<Type, CranelispError> {
        let sexps = cranelisp_frontend::parse(expr_src)?;
        if sexps.is_empty() {
            return Err(CranelispError::ParseError {
                message: "empty expression".into(),
                span: Span::SYNTHETIC,
            });
        }
        let input = cranelisp_frontend::build_repl_input(&sexps[0])?;
        let module = self.current_module_path();
        let ctx = cranelisp_types::CompileContext {
            module,
            codegen: CodegenBehaviour::InMemoryAndObject,
        };
        let tc = self.tc_env();
        let mut guard = self.shared.repl_check_state.lock()
            .unwrap_or_else(|e| e.into_inner());
        let cs = guard.as_mut().expect("REPL check state must be initialized");
        let check_result = tc.check(cs, &[input], &ctx, ModuleStrategy::Additive)?;
        Ok(check_result.display.as_ref()
            .map(|d| d.ty.clone())
            .unwrap_or(Type::Int))
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

            for (sym, entry) in table.all_symbols() {
                let name = sym.to_string();
                match entry {
                    ModuleEntry::Def { kind, .. } => {
                        if let DefKind::SpecialForm { .. } = kind.as_ref() {
                            special_forms.push(name);
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
    fn resolve_to_definition(&self, source: &FQSymbol) -> Option<ModuleEntry> {
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
        use cranelisp_typecheck::ModuleCheckAccumulator;

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
                        !self.shared.codegen_products
                            .get(&module)
                            .map(|p| p.code.contains_key(&clause_name))
                            .unwrap_or(false)
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
            let mut wctx = ModuleCompiler {
                symbol_tables: &self.shared.symbol_tables,
                next_type_id: &self.shared.next_type_id,
                check_state: repl_cs,
                current_module: module.clone(),
                scheduler: &self.shared.scheduler,
                platform_registry: &mut self.platform_registry,
                typecheck_products: &self.shared.typecheck_products,
                codegen_products: &self.shared.codegen_products,
                introspection: Some(&self.shared.introspection),
                lib_dirs: &self.lib_dirs,
                platform_dirs: &self.platform_dirs,
                project_root: &self.project_root,
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
                span: Span::SYNTHETIC,
            });
        }
        let sexp = sexps.into_iter().next().ok_or_else(|| {
            CranelispError::ParseError {
                message: "empty form".into(),
                span: Span::SYNTHETIC,
            }
        })?;
        let module = self.current_module_path();
        let mut resolver = ReadOnlyMacroResolver {
            symbol_tables: &self.shared.symbol_tables,
            codegen_products: &self.shared.codegen_products,
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
            &self.shared.codegen_products,
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
                && !fp.starts_with(&self.project_root) {
                    continue;
                }
            let names = discover_test_names(
                &self.shared.codegen_products,
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
            let outcome = run_test_by_name(&self.shared.codegen_products, name);
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
    fn special_form_feedback(&self, input: &str) -> Option<String> {
        let trimmed = input.trim();
        // Must be a single bare word (no parens, no spaces).
        if trimmed.contains('(') || trimmed.contains(' ') || trimmed.starts_with('/') {
            return None;
        }
        let table = self.current_symbol_table();
        if let Some(ModuleEntry::Def { kind, .. }) = table.get(trimmed)
            && let DefKind::SpecialForm { description } = kind.as_ref() {
                return Some(format_special_form_display(trimmed, description));
            }
        None
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
        // Look up main in codegen_products.
        let main_sym = cranelisp_types::Symbol::from("main");
        let code_ptr = self.lookup_main_code_ptr(module_name, &main_sym)?;
        let result_type = self.lookup_main_return_type(module_name);

        // Clear any stale runtime error.
        let _ = cranelisp_runtime::panic::take_runtime_error();

        // Call main.
        // SAFETY: `code_ptr` is non-null — returned from `lookup_main_code_ptr`
        // which errors on None. It points to finalized JIT code compiled by
        // Cranelift via `compile_and_register_defn`. The compiled function uses
        // the `extern "C" fn() -> i64` calling convention (zero-arg defn with
        // i64 return), matching the transmute target type.
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
        let raw_value = func();

        // Check for runtime panics.
        if let Some(err) = cranelisp_runtime::panic::take_runtime_error() {
            return Err(CranelispError::CodegenError {
                message: format!("runtime panic: {}", err),
                span: Span::SYNTHETIC,
            });
        }

        // IO trampoline.
        if result_type.is_io() {
            let inner_value = cranelisp_runtime::run_io_trampoline(raw_value);
            let inner_type = result_type.io_inner_type();
            Ok((inner_value, inner_type))
        } else {
            Ok((raw_value, result_type))
        }
    }

    /// Look up the code pointer for `main` in codegen_products.
    fn lookup_main_code_ptr(
        &self,
        module_name: &str,
        main_sym: &cranelisp_types::Symbol,
    ) -> Result<*const u8, CranelispError> {
        let module_path = ModuleFullPath::from(module_name);

        // Check codegen_products for the compiled Code.
        if let Some(product) = self.shared.codegen_products.get(&module_path)
            && let Some(code) = product.code.get(main_sym) {
                return Ok(code.ptr);
            }

        Err(CranelispError::ModuleError {
            message: "entry module has no `main` function — batch mode requires (defn main [] ...)"
                .into(),
            file: None,
            span: Span::SYNTHETIC,
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
    /// Sets the scheduler shutdown flag and wakes all condvars so nice
    /// workers observe shutdown and return. Scoped threads are joined
    /// automatically when the scope exits.
    pub fn shutdown(&mut self) {
        self.shared.scheduler.shutdown();
        // Join nice worker threads. They observe the shutdown flag via
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
        let file_path = crate::pipeline::resolve_module_file(&module, &self.project_root, &self.lib_dirs);
        let (source, entry_path) = match file_path {
            Some(path) => {
                let src = std::fs::read_to_string(&path).unwrap_or_default();
                (src, path)
            }
            None => {
                // No file found — empty module (e.g., fresh REPL).
                let default_path = self.project_root.join(format!("{module_name}.cl"));
                (String::new(), default_path)
            }
        };
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
                file: None,
                span: Span::SYNTHETIC,
            }
        })?;
        let main_return = crate::exe::validate_main(&entry_table)?;
        drop(entry_table);

        let main_returns_io = main_return == crate::exe::MainReturnKind::Io;

        // Collect .o paths from nice workers.
        let o_paths = self.shared.compiled_o_paths.lock()
            .unwrap_or_else(|e| e.into_inner())
            .clone();

        if o_paths.is_empty() {
            return Err(CranelispError::ModuleError {
                message: "no .o files produced — cannot link".into(),
                file: None,
                span: Span::SYNTHETIC,
            });
        }

        // Collect platform manifest names and rlib paths.
        // TODO: When platform linking is needed, these functions will
        // query the loaded platform registry.
        let platform_manifest_names =
            crate::exe::collect_platform_manifest_names();
        let platform_rlib_paths =
            crate::exe::find_platform_rlibs();

        // Generate startup .o stub.
        let startup_bytes = crate::exe::generate_startup_object(
            &platform_manifest_names,
            main_returns_io,
        )?;

        let cache_dir = self.shared.cache_dir.as_ref().ok_or_else(|| {
            CranelispError::ModuleError {
                message: "cache directory not configured — cannot write startup .o".into(),
                file: None,
                span: Span::SYNTHETIC,
            }
        })?;
        let startup_o_path = cache_dir.join("__startup.o");
        std::fs::write(&startup_o_path, &startup_bytes).map_err(|e| {
            CranelispError::ModuleError {
                message: format!("failed to write startup .o: {e}"),
                file: Some(startup_o_path.clone()),
                span: Span::SYNTHETIC,
            }
        })?;

        // Find the runtime bundle library.
        let bundle_lib = crate::exe::find_bundle_lib()?;

        // Output path: entry module stem in CWD (not project root).
        // E.g., `cranelisp --link examples/hello.cl` produces `./hello`.
        let output_path = PathBuf::from(module_name.replace(".cl", ""));

        // Link.
        crate::exe::link_executable(
            &output_path,
            &o_paths,
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
                    let inner_value = cranelisp_runtime::run_io_trampoline(*value);
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
        entry: &ModuleEntry,
        name: &str,
        module: &ModuleFullPath,
    ) -> String {
        match entry {
            ModuleEntry::Def { scheme, kind, docstring, .. } => {
                if let DefKind::SpecialForm { description } = kind.as_ref() {
                    return format_special_form_display(name, description);
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
                let ctor_display =
                    if let Some(info) = self.tc_env().lookup_type_def(&tn) {
                        cranelisp_backend::display::format_ctor_display(&tn, name, &info)
                    } else {
                        format!("{type_name}.{name}")
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
    fn resolve_entry_for_display(
        &self,
        entry: &ModuleEntry,
        current_module: &ModuleFullPath,
    ) -> (ModuleEntry, ModuleFullPath) {
        match entry {
            ModuleEntry::Import { source }
            | ModuleEntry::Reexport { source } => {
                if let Some(module_table) = self.shared.symbol_tables.get(&source.module)
                    && let Some(resolved) = module_table.get(source.symbol.as_ref()) {
                        return (resolved.clone(), source.module.clone());
                    }
                (entry.clone(), current_module.clone())
            }
            _ => (entry.clone(), current_module.clone()),
        }
    }

    /// Format a user-defined type for display (spec §4.1.3).
    ///
    /// Shows `:module/TypeName ; deftype` with `; match:` and `; impl:` sections.
    fn format_type_display(&self, type_name: &str, module: &ModuleFullPath) -> String {
        let mut result = format!(":{module}/{type_name} ; deftype");
        let tn = TypeName::from(type_name);
        if let Some(ctors) = self.tc_env().get_type_constructors(&tn)
            && !ctors.is_empty() {
                let names: Vec<&str> = ctors.iter().map(|c| c.name.as_ref()).collect();
                result.push_str(&format_related_section("match", &names));
            }
        let trait_names = self.tc_env().get_impls_for_type(&tn);
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
        let tc = self.tc_env();
        let guard = self.shared.repl_check_state.lock()
            .unwrap_or_else(|e| e.into_inner());
        let cs = guard.as_ref().expect("REPL check state must be initialized");
        let defining_module = tc.defining_module_for(cs, trait_name);
        let tn = TraitName::from(trait_name);
        let mut result = format!(":{defining_module}/{trait_name} ; deftrait");
        result = append_docstring_comment(result, docstring);
        if let Some(methods) = self.tc_env().get_trait_methods(&tn)
            && !methods.is_empty() {
                let names: Vec<&str> = methods.iter().map(|m| m.as_ref()).collect();
                result.push_str(&format_related_section("defn", &names));
            }
        let impl_types = self.tc_env().get_implementing_types(&tn);
        if !impl_types.is_empty() {
            let names: Vec<&str> = impl_types.iter().map(|t| t.as_ref()).collect();
            result.push_str(&format_related_section("impl", &names));
        }
        result
    }

    /// Format a builtin type (Int, Bool, Float, String) for display (spec §4.1.3).
    fn format_builtin_type_display(&self, type_name: &str) -> String {
        let tn = TypeName::from(type_name);
        let mut result = format!(":primitives/{type_name} ; type");
        let trait_names = self.tc_env().get_impls_for_type(&tn);
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
                format!("{base} ; {first_line}")
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
        // Defensive shutdown: ensure the scheduler signals all condvars
        // before this session is destroyed. This prevents hangs if the
        // session is dropped without an explicit shutdown() call (e.g.,
        // during test teardown or panic unwinding).
        self.shared.scheduler.shutdown();
    }
}

// ---------------------------------------------------------------------------
// Nice worker spawning + loop (Step 10)
// ---------------------------------------------------------------------------

/// Spawn nice (low-priority) worker threads inside a `std::thread::scope`.
///
/// Takes `&Arc<SharedState>` and clones the Arc for each worker thread.
/// Workers hold independent Arc references — no aliasing with the caller's
/// `&mut CompilerSession`.
///
/// Workers park on the scheduler's `object_work_available` condvar and wake
/// when modules reach TypecheckDone or on shutdown. The scope guarantees
/// all threads join before it exits.
///
/// # Panics
///
/// Panics if the OS fails to spawn a thread. This is a setup-time
/// invariant: if the OS cannot create threads, the compiler cannot
/// function.
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
/// `CodegenInput` is available for a module, the worker skips
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
            None => return, // Shutdown signaled.
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
/// Reads the module's `CodegenInput` from the shared `codegen_inputs` DashMap
/// (stashed by the priority worker). Reads `SymbolTable` from `typecheck_products`
/// for .meta.json serialization.
///
/// Errors are logged to stderr and do not halt the worker — the module is still
/// marked object-complete so the scheduler lifecycle proceeds.
fn compile_module_object(
    shared: &SharedState,
    module: &ModuleFullPath,
    cache_dir: &Path,
) {
    use cranelisp_backend::cache;

    // Take the stashed input (remove entry to release memory).
    let Some((_, input)) = shared.codegen_inputs.remove(module) else {
        // No data stashed — module may have had no compilable defns.
        return;
    };

    // Skip modules with no compilable defns (types-only, imports-only).
    if !crate::session::has_compilable_defns(&input.program) {
        return;
    }

    // Use the full CheckResult stashed by the priority worker.
    // This includes constrained_fn_names, fixing the pre-existing bug
    // where the object path used an empty set.
    let check = input.check;

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

    // Compile using the unified compile_to_module path.
    // Intrinsics, CompilationEnv, and cross-module refs are derived internally.
    let obj_bytes = match cranelisp_backend::compile_to_module(
        module.clone(),
        &input.program,
        &check,
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
                eprintln!("nice-worker: .o compilation failed for {}: {}", module, e.message());
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

    // Build and write .meta.json for cache-hit restoration.
    // GOT slot assignments are on ModuleEntry::Def in the SymbolTable,
    // so only the symbol table needs serializing.
    let symbol_table = shared.symbol_tables
        .get(module)
        .map(|guard| guard.clone())
        .unwrap_or_else(|| cranelisp_types::SymbolTable::new(module.clone()));

    // Extract dependency module paths from Import entries for recursive
    // cache loading on future cache hits (Sprint 53 — transitive deps).
    let dependencies: Vec<String> = {
        let mut deps = std::collections::HashSet::new();
        for (_name, entry) in symbol_table.all_symbols() {
            if let cranelisp_types::ModuleEntry::Import { source } = entry {
                let mod_path = source.module.as_ref();
                if mod_path != "primitives" && mod_path != "macros" {
                    deps.insert(mod_path.to_string());
                }
            }
        }
        deps.into_iter().collect()
    };
    let metadata = cache::CacheMetadata {
        symbol_table,
        dependencies,
    };
    if let Err(e) = cache::write_cached_metadata(&meta_path, &metadata) {
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
fn discover_test_names(
    codegen_products: &dashmap::DashMap<ModuleFullPath, CodegenProduct>,
    tc_modules: &dashmap::DashMap<ModuleFullPath, SymbolTable>,
    module: &ModuleFullPath,
) -> Vec<String> {
    let mut names = Vec::new();
    let cp = match codegen_products.get(module) {
        Some(cp) => cp,
        None => return names,
    };
    let symbols = match tc_modules.get(module) {
        Some(st) => st,
        None => return names,
    };
    for (name, entry) in symbols.all_symbols() {
        if !name.as_ref().starts_with("test-") {
            continue;
        }
        if let ModuleEntry::Def { param_names, .. } = entry {
            if !param_names.is_empty() {
                continue;
            }
        } else {
            continue;
        }
        if let Some(code) = cp.code.get(name)
            && !code.ptr.is_null() {
                names.push(format!("{}/{}", module.as_ref(), name.as_ref()));
            }
    }
    names.sort();
    names
}

/// Core: run a single test by fully-qualified name. No heap allocation.
///
/// Looks up the code pointer, calls it, interprets the (Option String) result.
fn run_test_by_name(
    codegen_products: &dashmap::DashMap<ModuleFullPath, CodegenProduct>,
    fq_name: &str,
) -> TestOutcome {
    use cranelisp_types::NULLARY_TAG_THRESHOLD;

    // Parse "module/name" into module path and bare name.
    let (module_str, bare_name) = match fq_name.rsplit_once('/') {
        Some((m, n)) => (m, n),
        None => ("user", fq_name),
    };
    let module = ModuleFullPath::from(module_str);

    // Look up code pointer.
    let code_ptr = codegen_products.get(&module)
        .and_then(|cp| cp.code.get(&Symbol::from(bare_name)).map(|c| c.ptr));

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
    let _ = cranelisp_runtime::panic::take_runtime_error();
    let value = unsafe {
        let func: extern "C" fn() -> i64 = std::mem::transmute(code_ptr);
        func()
    };
    let nanos = t0.elapsed().as_nanos() as i64;

    if let Some(msg) = cranelisp_runtime::panic::take_runtime_error() {
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
            cranelisp_runtime::read_string_as_str(string_ptr).to_string()
        };
        TestOutcome::Fail {
            name: fq_name.to_string(),
            nanos,
            reason,
        }
    }
}

/// Session state for test externs. Set before JIT evaluation of expressions
/// containing discover-tests/run-test, cleared after.
struct TestRunnerState {
    /// Codegen products for looking up test function code pointers.
    codegen_products: *const dashmap::DashMap<ModuleFullPath, CodegenProduct>,
    /// TC modules for scanning symbol tables.
    tc_modules: *const dashmap::DashMap<ModuleFullPath, SymbolTable>,
    /// Current module path (for discover-tests with empty module arg).
    current_module: *const ModuleFullPath,
}

unsafe impl Send for TestRunnerState {}

thread_local! {
    static TEST_RUNNER: std::cell::Cell<*const TestRunnerState> =
        const { std::cell::Cell::new(std::ptr::null()) };
}

fn set_test_runner_state(state: &TestRunnerState) {
    TEST_RUNNER.with(|c| c.set(state as *const _));
}

fn clear_test_runner_state() {
    TEST_RUNNER.with(|c| c.set(std::ptr::null()));
}

/// Allocate a heap ADT with the given tag and fields.
///
/// Layout: [alloc_size(8) | rc=1(8) | tag(8) | field0(8) | field1(8) | ...]
/// Returns the base pointer (offset 0 of the allocation).
unsafe fn alloc_heap_adt(tag: i64, fields: &[i64]) -> i64 { unsafe {
    let payload_size = 8 + fields.len() * 8; // tag + fields
    let base = cranelisp_runtime::alloc::alloc_with_rc(payload_size);
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
        let codegen_products = unsafe { &*state.codegen_products };
        let tc_modules = unsafe { &*state.tc_modules };
        let current_module = unsafe { &*state.current_module };

        let module = if module_path_str == 0
            || unsafe { cranelisp_runtime::read_string_as_str(module_path_str) }.is_empty()
        {
            current_module.clone()
        } else {
            let path_str = unsafe { cranelisp_runtime::read_string_as_str(module_path_str) };
            ModuleFullPath::from(path_str)
        };

        // Core logic — shared with slash command.
        let test_names = discover_test_names(codegen_products, tc_modules, &module);

        // Heap-allocate: SList of SexpSym, wrapped in IO Pure.
        // SexpSym tag = 4 (Sexp enum: Int=0, Float=1, Bool=2, Str=3, Sym=4).
        let mut slist: i64 = 0; // SNil
        for name in test_names.into_iter().rev() {
            let name_str = cranelisp_runtime::alloc_string(name.as_bytes()) as i64;
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
            let name = cranelisp_runtime::alloc_string(b"?") as i64;
            return unsafe { alloc_io_pure(alloc_heap_adt(0, &[name, 0])) };
        }

        let state = unsafe { &*state_ptr };
        let codegen_products = unsafe { &*state.codegen_products };

        // Extract function name from SexpSym.
        // SexpSym layout: [header(16) | tag=4(8) | sname(8)]
        let fq_name = if sexp_sym != 0 && (sexp_sym as usize) >= NULLARY_TAG_THRESHOLD {
            let name_ptr = unsafe { *((sexp_sym as *const u8).add(24) as *const i64) };
            unsafe { cranelisp_runtime::read_string_as_str(name_ptr).to_string() }
        } else {
            let name = cranelisp_runtime::alloc_string(b"?") as i64;
            return unsafe { alloc_io_pure(alloc_heap_adt(0, &[name, 0])) };
        };

        // Core logic — shared with slash command.
        let outcome = run_test_by_name(codegen_products, &fq_name);

        // Heap-allocate TestResult, wrapped in IO Pure.
        unsafe { alloc_io_pure(test_outcome_to_heap(&outcome)) }
    })
}

/// Convert a TestOutcome to a heap-allocated TestResult ADT.
unsafe fn test_outcome_to_heap(outcome: &TestOutcome) -> i64 { unsafe {
    match outcome {
        TestOutcome::Pass { name, nanos } => {
            let name_alloc = cranelisp_runtime::alloc_string(name.as_bytes()) as i64;
            alloc_heap_adt(0, &[name_alloc, *nanos]) // TestPass tag=0
        }
        TestOutcome::Fail { name, nanos, reason } => {
            let name_alloc = cranelisp_runtime::alloc_string(name.as_bytes()) as i64;
            let reason_alloc = cranelisp_runtime::alloc_string(reason.as_bytes()) as i64;
            alloc_heap_adt(1, &[name_alloc, *nanos, reason_alloc]) // TestFail tag=1
        }
        TestOutcome::Panic { name, reason } => {
            let name_alloc = cranelisp_runtime::alloc_string(name.as_bytes()) as i64;
            let reason_alloc = cranelisp_runtime::alloc_string(reason.as_bytes()) as i64;
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
    symbol_tables: *const dashmap::DashMap<ModuleFullPath, SymbolTable>,
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
            cranelisp_backend::display::format_value(val, ty, symbol_tables)
        };
        cranelisp_runtime::alloc_string(s.as_bytes()) as i64
    })
}

