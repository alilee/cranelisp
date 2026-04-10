// CompilerSession: v4 pipeline session (pipeline-v4.md §5, roadmap Steps 0-7).
//
// Wraps the existing CompilationSession. Batch compilation goes through the v4
// scheduler-driven path with lazy dependency discovery (Step 5). REPL eval
// routes through process_module_forms(Additive) with serial per-form processing
// (Step 7).

use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;
use std::sync::{Arc, Mutex};

use cranelisp_types::{
    CheckResult, CodegenBehaviour, CranelispError,
    DefKind, FQSymbol, MacroClauseInfo, MacroParam, ModuleEntry, ModuleFullPath,
    ModuleStrategy, ModuleStructure, Sexp, Span, Symbol, SymbolTable, TopLevel,
    TraitName, Type, TypeName, Warning,
};

use crate::platform::LoadedPlatform;
use crate::platform_registry::PlatformRegistry;
use crate::scheduler::CompileScheduler;
use crate::worker::ModuleCompiler;

// Re-export display functions so tests can import from session_v4 instead of repl.
pub use cranelisp_backend::display::format_result_value;
use cranelisp_backend::display::{format_type_qualified, format_scheme_display};

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
    Reset,
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
        "/reset" => ReplCommand::Reset,
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
    let _ = writeln!(stdout, "  /run-tests (/rt)    Discover and run test-* functions");
    let _ = writeln!(stdout, "  /reset              Clear all state and reload prelude");
    let _ = writeln!(stdout, "  ;#! <cmd>           Run a shell command");
}

/// Check if input is a comment-only line.
fn is_comment_only(input: &str) -> bool {
    input.lines().all(|line| {
        let trimmed = line.trim();
        trimmed.is_empty() || trimmed.starts_with(';')
    })
}

/// Run a shell command and print output.
fn run_shell_command(cmd: &str, stdout: &mut impl Write) {
    if cmd.is_empty() {
        let _ = writeln!(stdout, "usage: ;#! <command>");
        return;
    }
    match std::process::Command::new("sh")
        .arg("-c")
        .arg(cmd)
        .output()
    {
        Ok(output) => {
            let _ = stdout.write_all(&output.stdout);
            let _ = stdout.write_all(&output.stderr);
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
        _ => format!("{name}"),
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
    pub symbols: SymbolTable,
    /// Per-module GOT table. Allocated at module registration, base address
    /// stable for process lifetime. Slot indices assigned during typecheck,
    /// code pointers filled during codegen. Arc-shared so codegen workers
    /// can read the base address concurrently.
    pub got: std::sync::Arc<cranelisp_backend::got::GotTable>,
    pub file_path: Option<PathBuf>,
}

/// Transient codegen input for a module.
/// Produced by typecheck, consumed by both JIT (priority workers) and .o (nice
/// workers) codegen. Removed when scheduler signals both `inmem_done` and
/// `object_done`. See session-restructure.md.
pub struct CodegenInput {
    pub method_resolutions: cranelisp_types::MethodResolutions,
    pub expr_types: HashMap<Span, Type>,
    pub mono_defns: Vec<cranelisp_types::MonoDefn>,
    pub default_method_defns: Vec<cranelisp_types::Defn>,
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

/// TARGET STATE: REPL-only per-symbol introspection data. Replaces DefCodegen's introspection fields.
/// Not populated during batch. See session-restructure.md.
#[derive(Debug, Clone, Default)]
pub struct Introspection {
    pub source: Option<String>,
    pub sexp: Option<Sexp>,
    pub defn: Option<cranelisp_types::Defn>,
    pub clif_ir: Option<String>,
    pub disasm: Option<String>,
    pub code_size: Option<usize>,
    pub compile_duration: Option<std::time::Duration>,
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
}

/// The compiler session — scheduler-driven concurrent compilation.
///
/// One session per process. Owns the TypeChecker, codegen state, and
/// scheduler. `register_module` spawns scoped priority worker threads
/// that process modules from the scheduler's work queue.
pub struct CompilerSession {
    /// Type checker state (persists across forms).
    pub tc: cranelisp_typecheck::TypeChecker,
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

    /// LEGACY: replaced by scheduler state (tracks Failed modules). See session-restructure.md.
    /// Modules that failed reload (file watcher). While non-empty, expression
    /// evaluation is blocked.
    pub error_modules: HashSet<ModuleFullPath>,

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

        let tc = cranelisp_typecheck::TypeChecker::new();
        let cache_dir = project_root.join(".cranelisp-cache");
        let _ = std::fs::create_dir_all(&cache_dir);

        let cache_state = if settings.no_cache {
            None
        } else {
            Some(crate::session::CacheState::new(cache_dir.clone()))
        };

        let priority_workers = std::cmp::max(settings.priority_workers, 1);

        let nice_workers = settings.nice_workers;

        let shared = Arc::new(SharedState {
            scheduler: CompileScheduler::new(),
            cache_dir: Some(cache_dir),
            compiled_o_paths: Mutex::new(Vec::new()),
            promote_nice_workers: AtomicBool::new(false),
            cached_modules: Mutex::new(HashSet::new()),
            file_to_module: Mutex::new(HashMap::new()),
            cache_state: Mutex::new(cache_state),
            typecheck_products: dashmap::DashMap::new(),
            codegen_inputs: dashmap::DashMap::new(),
            codegen_products: dashmap::DashMap::new(),
            introspection: dashmap::DashMap::new(),
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
            tc,
            lib_dirs,
            platform_dirs,
            loaded_platforms: Vec::new(),
            shared,
            priority_workers,
            project_root,
            platform_registry: PlatformRegistry::new(),
            error_modules: HashSet::new(),
            nice_worker_handles,
            nice_workers,
        }
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

        // Register module with scheduler (entry module, not delaying others).
        self.shared.scheduler.register_module(module.clone(), false);

        // Build shared maps for worker threads.
        let module_sexps = Mutex::new({
            let mut map = HashMap::new();
            map.insert(module.clone(), sexps);
            map
        });
        let suspend_states = Mutex::new(HashMap::new());

        // Temporarily move TC and PlatformRegistry into Mutexes so worker
        // threads can lock them. Moved back after the scope exits.
        let tc = std::mem::replace(&mut self.tc, cranelisp_typecheck::TypeChecker::new());
        let tc_mutex = Mutex::new(tc);
        let platform_registry = std::mem::replace(
            &mut self.platform_registry, PlatformRegistry::new(),
        );
        let platform_mutex = Mutex::new(platform_registry);

        // Build shared worker context for scoped threads.
        let worker_shared = crate::worker::PriorityWorkerRefs {
            tc: &tc_mutex,
            platform_registry: &platform_mutex,
            typecheck_products: &self.shared.typecheck_products,
            codegen_products: &self.shared.codegen_products,
            introspection: &self.shared.introspection,
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

        // Move TC and PlatformRegistry back from Mutexes.
        self.tc = tc_mutex.into_inner().unwrap_or_else(|e| e.into_inner());
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

        // Shell escape: ;#! lines run as shell commands.
        if let Some(stripped) = trimmed.strip_prefix(";#!") {
            run_shell_command(stripped.trim(), stdout);
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
            ReplCommand::Unknown(cmd) => {
                CommandResult::Final(format!(
                    "error: unknown command '{cmd}'. Type /help for available commands."
                ))
            }
            ReplCommand::RunTests(prefix) => {
                CommandResult::Final(self.handle_run_tests(prefix))
            }
            ReplCommand::Reset => {
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

        let snapshot = self.tc.snapshot();
        match self.process_single_form(sexp) {
            Ok(result) => Ok(result),
            Err(e) => {
                self.tc.restore(snapshot);
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
            let module = self.tc.current_module_path().clone();
            let mut accumulator = ModuleCheckAccumulator::new();
            let mut expanded_program = Vec::new();
            let single_sexp = [sexp.clone()];

            let result = {
                let mut wctx = ModuleCompiler {
                    tc: &mut self.tc,
                    scheduler: &self.shared.scheduler,
                    platform_registry: &mut self.platform_registry,
                    typecheck_products: &self.shared.typecheck_products,
                    codegen_products: &self.shared.codegen_products,
                    introspection: &self.shared.introspection,
                    lib_dirs: &self.lib_dirs,
                    platform_dirs: &self.platform_dirs,
                    project_root: &self.project_root,
                    shared_state: Some(&self.shared),
                };

                let mut pass1_done = false;
                worker::process_module_forms(
                    &mut wctx,
                    &module,
                    &single_sexp,
                    0,
                    &mut accumulator,
                    &mut expanded_program,
                    ModuleStrategy::Additive,
                    &mut pass1_done,
                )?
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
        let tc_modules = self.tc.modules_ref();
        let env_impl = crate::worker::SessionCompilationEnv {
            tc_modules,
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
            tc_modules,
            &self.shared.typecheck_products,
            &self.shared.codegen_products,
        )?;

        let has_expr = program.iter().any(|tl| matches!(tl, TopLevel::Expr(_)));

        if has_expr {
            let program_vec = program.to_vec();
            let (jit_syms, got_defs) = env_impl.collect_jit_setup_for_module(&self.platform_registry);
            let (value, ty) = crate::pipeline::compile_and_execute_expr(
                &jit_syms,
                &got_defs,
                &program_vec,
                check,
                &env_impl,
                &[], // traced_fns (empty — trace set up by REPL when re-enabled)
                &[], // trace_extra_symbols
            )?;

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

    /// Compile a dependency module inline (for blocked REPL eval).
    fn compile_dep_inline(
        &mut self,
        dep_module: &ModuleFullPath,
        dep_sexps: &[Sexp],
    ) -> Result<(), CranelispError> {
        self.shared.scheduler.register_module(dep_module.clone(), false);

        let mut module_sexps = HashMap::new();
        module_sexps.insert(dep_module.clone(), dep_sexps.to_vec());

        let mut ctx = ModuleCompiler {
            tc: &mut self.tc,
            scheduler: &self.shared.scheduler,
            platform_registry: &mut self.platform_registry,
            typecheck_products: &self.shared.typecheck_products,
            codegen_products: &self.shared.codegen_products,
            introspection: &self.shared.introspection,
            lib_dirs: &self.lib_dirs,
            platform_dirs: &self.platform_dirs,
            project_root: &self.project_root,
            shared_state: Some(&self.shared),
        };

        crate::worker::priority_worker_loop(&mut ctx, &mut module_sexps)?;

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
            let guard = self.tc.symbol_table();
            guard.get(name)?.clone()
        };

        // Resolve import/reexport chains.
        let module = self.tc.current_module_path().clone();
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
            ModuleEntry::Def { kind, scheme, .. } => {
                if let DefKind::SpecialForm { .. } = kind.as_ref() {
                    Some(EvalResult::Def {
                        symbol: FQSymbol { module, symbol: Symbol::from(name) },
                        ty: scheme.ty.clone(),
                        warnings: Vec::new(),
                    })
                } else {
                    None // Regular functions evaluate normally.
                }
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

    /// Build type→module mapping on-demand from the typechecker's module tables.
    pub fn build_type_modules(&self) -> HashMap<TypeName, ModuleFullPath> {
        let mut map = HashMap::new();
        for entry in self.tc.modules().iter() {
            let module_path = entry.key().clone();
            for (sym, me) in entry.value().all_symbols() {
                if matches!(me, ModuleEntry::TypeDef { .. }) {
                    map.insert(
                        TypeName::from(sym.as_ref()),
                        module_path.clone(),
                    );
                }
            }
        }
        map
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
        match self.tc.symbol_table().get(name) {
            Some(entry) => format_entry_sig(entry, name),
            None => format!("error: unknown symbol '{name}'"),
        }
    }

    /// /doc handler: show docstring of a symbol.
    fn handle_doc(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /doc <name>".to_string();
        }
        match self.tc.symbol_table().get(name) {
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
        let table_ref = self.tc.symbol_table();
        let mut fns = Vec::new();
        let mut types = Vec::new();
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
                ModuleEntry::Macro { .. } => {
                    macros.push(format!("  {name}"));
                }
                _ => {}
            }
        }

        let mut parts = Vec::new();
        if !types.is_empty() {
            types.sort();
            parts.push(format!("Types:\n{}", types.join("\n")));
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
            "No definitions in current module.".to_string()
        } else {
            parts.join("\n")
        }
    }

    /// /mod handler: switch module namespace.
    fn handle_mod(&mut self, name: &str) {
        let target = if name.is_empty() { "user" } else { name };
        let path = ModuleFullPath::from(target);
        self.tc.set_current_module(path);
    }

    /// Look up introspection data for a bare symbol name in the current module.
    fn get_introspection(&self, name: &str) -> Option<dashmap::mapref::one::Ref<'_, FQSymbol, Introspection>> {
        let module = self.tc.current_module_path().clone();
        let fq = FQSymbol {
            module,
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
        if let Some(intr) = self.get_introspection(name) {
            if let Some(ref sexp) = intr.sexp {
                return format!("; sexp for {name}\n{}", crate::pretty::pretty_print(sexp));
            }
        }
        format!("Error: no sexp available for '{name}'")
    }

    /// /ast handler: show AST of a definition.
    fn handle_ast(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /ast <name>".to_string();
        }
        if let Some(intr) = self.get_introspection(name) {
            if let Some(ref defn) = intr.defn {
                return format!("; ast for {name}\n{:#?}", defn);
            }
        }
        format!("Error: no AST available for '{name}'")
    }

    /// /clif handler: show Cranelift IR of a definition.
    fn handle_clif(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /clif <name>".to_string();
        }
        if let Some(intr) = self.get_introspection(name) {
            if let Some(ref clif) = intr.clif_ir {
                return format!("; clif ir for {name}\n{}", clif);
            }
        }
        format!("Error: no CLIF IR available for '{name}'")
    }

    /// /disasm handler: show disassembled native code of a definition.
    fn handle_disasm(&self, name: &str) -> String {
        if name.is_empty() {
            return "usage: /disasm <name>".to_string();
        }
        if let Some(intr) = self.get_introspection(name) {
            if let Some(ref disasm) = intr.disasm {
                return format!("; disasm for {name}\n{}", disasm);
            }
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
        let entry = match self.tc.symbol_table().get(name) {
            Some(e) => e.clone(),
            None => return format!("error: unknown symbol '{name}'"),
        };
        let module = self.tc.current_module_path().clone();
        let (resolved_entry, resolved_module) = self.resolve_entry_for_display(&entry, &module);
        let type_modules = self.build_type_modules();
        let sig = self.format_def_entry(&resolved_entry, name, &resolved_module, &type_modules);
        // Append code info if available.
        if !matches!(resolved_entry,
            ModuleEntry::Macro { .. } | ModuleEntry::TypeDef { .. } | ModuleEntry::TraitDecl { .. })
        {
            if let Some(intr) = self.get_introspection(name) {
                let size_str = intr.code_size
                    .map(|s| format!("{s} bytes"))
                    .unwrap_or_else(|| "? bytes".to_string());
                let time_str = intr.compile_duration
                    .map(|d| format!("{}ms", d.as_millis()))
                    .unwrap_or_else(|| "?ms".to_string());
                return format!("{sig}\n  {size_str}, {time_str}");
            }
        }
        sig
    }

    /// /type handler: typecheck expression without executing.
    fn handle_type(&mut self, expr_src: &str) -> String {
        if expr_src.is_empty() {
            return "usage: /type <expr>".to_string();
        }
        let snapshot = self.tc.snapshot();
        let result = self.typecheck_only(expr_src);
        self.tc.restore(snapshot);
        match result {
            Ok(ty) => {
                let type_modules = self.build_type_modules();
                let display = format_type_qualified(&ty, &type_modules);
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
        let module = self.tc.current_module_path().clone();
        let ctx = cranelisp_types::CompileContext {
            module,
            codegen: CodegenBehaviour::InMemoryAndObject,
        };
        let check_result = self.tc.check(&[input], &ctx, ModuleStrategy::Additive)?;
        Ok(check_result.display.as_ref()
            .map(|d| d.ty.clone())
            .unwrap_or(Type::Int))
    }

    /// /imports handler: list imports in current module by category.
    fn handle_imports(&self, filter: &str) -> String {
        let table = self.tc.symbol_table();
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
                let table = self.tc.module_table(&current_module)?;
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

        let module_path = match self.tc.resolve_module_by_name(mod_name) {
            Some(path) => path,
            None => return format!("Module '{mod_name}' not found"),
        };

        let table = match self.tc.module_table(&module_path) {
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
            let table = self.tc.symbol_table();
            for (sym, entry) in table.all_symbols() {
                if let ModuleEntry::Macro { clauses, sexp: Some(sexp), .. } = entry {
                    let name = Symbol::from(sym.as_ref());
                    let module = self.tc.current_module_path().clone();
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
            let module = self.tc.current_module_path().clone();
            let info = cranelisp_frontend::parse_defmacro(sexp)?;
            let mut accumulator = ModuleCheckAccumulator::new();

            let mut wctx = ModuleCompiler {
                tc: &mut self.tc,
                scheduler: &self.shared.scheduler,
                platform_registry: &mut self.platform_registry,
                typecheck_products: &self.shared.typecheck_products,
                codegen_products: &self.shared.codegen_products,
                introspection: &self.shared.introspection,
                lib_dirs: &self.lib_dirs,
                platform_dirs: &self.platform_dirs,
                project_root: &self.project_root,
                shared_state: Some(&self.shared),
            };

            crate::worker::compile_macro_for_repl(
                &mut wctx, &module, &info, Span::SYNTHETIC, &mut accumulator,
            )?;
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
        // Build macro map from persistent macros (compiled in prior evals).
        let macro_map = self.build_macro_map()?;
        crate::expander::expand_sexp_recursive(sexp, &macro_map, 0)
    }

    /// Build a macro map from compiled macros in the GOT and TC symbol table.
    fn build_macro_map(&self) -> Result<HashMap<Symbol, crate::expander::MacroEntry>, CranelispError> {
        use crate::expander::{MacroEntry, MacroClauseEntry};

        let current_module = self.tc.current_module_path().clone();
        let mut map = HashMap::new();
        let table = self.tc.symbol_table();

        for (sym, entry) in table.all_symbols() {
            let (clauses, docstring, defining_module) = match entry {
                ModuleEntry::Macro { clauses, docstring, .. } => {
                    (clauses.clone(), docstring.clone(), current_module.clone())
                }
                ModuleEntry::Import { source } => {
                    // Follow import to find macro entry in defining module.
                    if let Some(module_table) = self.tc.module_table(&source.module) {
                        if let Some(ModuleEntry::Macro { clauses, docstring, .. }) =
                            module_table.get(source.symbol.as_ref())
                        {
                            (clauses.clone(), docstring.clone(), source.module.clone())
                        } else {
                            continue;
                        }
                    } else {
                        continue;
                    }
                }
                _ => continue,
            };

            let name = Symbol::from(sym.as_ref());
            // Check if all clauses have code pointers in codegen_products.
            let mut compiled_clauses = Vec::new();
            let mut all_compiled = true;
            if let Some(cp) = self.shared.codegen_products.get(&defining_module) {
                for (idx, clause_info) in clauses.iter().enumerate() {
                    let clause_name = Symbol::from(format!("__macro_{}_clause_{}", name, idx));
                    if let Some(code) = cp.code.get(&clause_name) {
                        compiled_clauses.push(MacroClauseEntry {
                            func_ptr: code.ptr,
                            params: clause_info.params.clone(),
                            rest_param: clause_info.rest_param.clone(),
                        });
                    } else {
                        all_compiled = false;
                        break;
                    }
                }
            } else {
                all_compiled = false;
            }
            if all_compiled && !compiled_clauses.is_empty() {
                map.insert(name, MacroEntry {
                    clauses: compiled_clauses,
                    docstring,
                });
            }
        }
        Ok(map)
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
    fn handle_run_tests(&self, prefix: &str) -> String {
        use cranelisp_types::NULLARY_TAG_THRESHOLD;

        // Discover test functions from codegen_products.
        let module = self.tc.current_module_path().clone();
        let mut tests: Vec<(String, *const u8)> = Vec::new();
        if let Some(cp) = self.shared.codegen_products.get(&module) {
            for entry in cp.code.iter() {
                let name: &str = entry.key().as_ref();
                if !name.starts_with("test-") {
                    continue;
                }
                if !prefix.is_empty() && !name.starts_with(&format!("test-{prefix}")) {
                    continue;
                }
                let ptr = entry.value().ptr;
                if ptr.is_null() {
                    continue;
                }
                // Check arity from TC symbol table (test fns must be zero-arg).
                let table = self.tc.symbol_table();
                if let Some(ModuleEntry::Def { param_names, .. }) = table.get(name) {
                    if !param_names.is_empty() {
                        continue;
                    }
                }
                tests.push((name.to_string(), ptr));
            }
        }
        tests.sort_by(|a, b| a.0.cmp(&b.0));

        if tests.is_empty() {
            return if prefix.is_empty() {
                "No test-* functions found.".to_string()
            } else {
                format!("No test-* functions found matching '{prefix}'.")
            };
        }

        // Run each test.
        let start = std::time::Instant::now();
        let mut passed = 0usize;
        let mut failed = 0usize;
        let mut lines = Vec::new();

        for (name, code_ptr) in &tests {
            let _ = cranelisp_runtime::panic::take_runtime_error();
            let value = unsafe {
                let func: extern "C" fn() -> i64 = std::mem::transmute(*code_ptr);
                func()
            };

            let dots = ".".repeat(40usize.saturating_sub(name.len()));

            if let Some(msg) = cranelisp_runtime::panic::take_runtime_error() {
                lines.push(format!("  {name} {dots} PANIC: {msg}"));
                failed += 1;
            } else if (value as usize) < NULLARY_TAG_THRESHOLD {
                // None = pass
                lines.push(format!("  {name} {dots} ok"));
                passed += 1;
            } else {
                // Some(reason_string)
                let reason = unsafe {
                    let base = value as *const u8;
                    let string_ptr = *(base.add(
                        cranelisp_backend::heap::HeapAdt::field_offset(0) as usize,
                    ) as *const i64);
                    cranelisp_runtime::read_string_as_str(string_ptr)
                };
                lines.push(format!("  {name} {dots} FAILED: {reason}"));
                failed += 1;
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
        let table = self.tc.symbol_table();
        if let Some(ModuleEntry::Def { kind, .. }) = table.get(trimmed) {
            if let DefKind::SpecialForm { description } = kind.as_ref() {
                return Some(format_special_form_display(trimmed, description));
            }
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
        if let Some(product) = self.shared.codegen_products.get(&module_path) {
            if let Some(code) = product.code.get(main_sym) {
                return Ok(code.ptr);
            }
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

        if let Some(table) = self.tc.module_table(&module_path)
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

        self.shared.scheduler.wait_object_complete()
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
        let entry_table = self.tc.module_table(&module).ok_or_else(|| {
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
        // TODO: LoadedPlatform doesn't currently store ModuleStructure.
        // When platform linking is needed, add module_path + structure
        // fields to LoadedPlatform. For now, empty — non-platform programs
        // link correctly.
        let module_structures: Vec<(ModuleFullPath, ModuleStructure)> = vec![];
        let platform_manifest_names =
            crate::exe::collect_platform_manifest_names(&module_structures);
        let platform_rlib_paths =
            crate::exe::find_platform_rlibs(&module_structures);

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

        // Output path: entry module name without extension, in project root.
        let output_path = self.project_root.join(module_name.replace(".cl", ""));

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
    pub fn current_module_name(&self) -> &str {
        &self.tc.current_module_path()
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
        let type_modules = self.build_type_modules();
        match result {
            EvalResult::Def { symbol, .. } => {
                let name = symbol.symbol.as_ref();
                let module = &symbol.module;

                // Builtin type names (Int, Bool, etc.) from primitives module.
                if module.as_ref() == "primitives" && Type::from_name(name).is_some() {
                    return self.format_builtin_type_display(name);
                }

                let entry = self.tc.symbol_table().get(name).cloned();
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
                self.format_def_entry(&entry, name, &resolved_module, &type_modules)
            }
            EvalResult::Val { value, ty, .. } => {
                let type_def_reg = self.tc.type_def_registry();
                let type_defs = type_def_reg.as_map();
                if ty.is_io() {
                    let inner_value = cranelisp_runtime::run_io_trampoline(*value);
                    let inner_type = ty.io_inner_type();
                    format_result_value(
                        inner_value, &inner_type, type_defs, &type_modules,
                    )
                } else {
                    format_result_value(
                        *value, ty, type_defs, &type_modules,
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
        type_modules: &HashMap<TypeName, ModuleFullPath>,
    ) -> String {
        match entry {
            ModuleEntry::Def { scheme, kind, docstring, .. } => {
                if let DefKind::SpecialForm { description } = kind.as_ref() {
                    return format_special_form_display(name, description);
                }
                let base = if !scheme.constraints.is_empty() {
                    format_scheme_display(name, scheme, module, type_modules)
                } else {
                    let type_str = format_type_qualified(&scheme.ty, type_modules);
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
                let type_str = format_type_qualified(&scheme.ty, type_modules);
                let tn = TypeName::from(type_name.0.as_str());
                let ctor_display =
                    if let Some(info) = self.tc.type_def_registry().get(&tn) {
                        cranelisp_backend::display::format_ctor_display(&tn, name, info)
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
                if let Some(module_table) = self.tc.modules().get(&source.module) {
                    if let Some(resolved) = module_table.get(source.symbol.as_ref()) {
                        return (resolved.clone(), source.module.clone());
                    }
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
        if let Some(ctors) = self.tc.get_type_constructors(&tn) {
            if !ctors.is_empty() {
                let names: Vec<&str> = ctors.iter().map(|c| c.name.as_ref()).collect();
                result.push_str(&format_related_section("match", &names));
            }
        }
        let trait_names = self.tc.get_impls_for_type(&tn);
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
        let defining_module = self.tc.defining_module_for(trait_name);
        let tn = TraitName::from(trait_name);
        let mut result = format!(":{defining_module}/{trait_name} ; deftrait");
        result = append_docstring_comment(result, docstring);
        if let Some(methods) = self.tc.get_trait_methods(&tn) {
            if !methods.is_empty() {
                let names: Vec<&str> = methods.iter().map(|m| m.as_ref()).collect();
                result.push_str(&format_related_section("defn", &names));
            }
        }
        let impl_types = self.tc.get_implementing_types(&tn);
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
        let trait_names = self.tc.get_impls_for_type(&tn);
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
    if let Sexp::List(items, _) = sexp {
        if items.len() >= 2 {
            if let Sexp::Symbol(head, _) = &items[0] {
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

    // Reconstruct a CheckResult for the object codegen pipeline.
    // FIXME(/arch): object codegen should accept CodegenInput directly
    // instead of requiring a full CheckResult.
    let check_result = CheckResult {
        method_resolutions: input.method_resolutions,
        constrained_fn_names: HashSet::new(),
        mono_defns: input.mono_defns,
        expr_types: input.expr_types,
        default_method_defns: input.default_method_defns,
        warnings: Vec::new(),
        type_defs: HashMap::new(),
        constructor_to_type: HashMap::new(),
        display: None,
    };

    // Build the ObjectCompileInput from the stashed data.
    let object_input = crate::pipeline::build_object_compile_input(
        module,
        Some(&input.program),
        Some(&check_result),
        &[], // cross_module_func_sigs not accumulated in v4 path yet
    );

    // Compile to .o bytes via Cranelift ObjectModule.
    let obj_bytes = match cache::compile_module_to_object(&object_input, &object_input) {
        Ok(bytes) => bytes,
        Err(e) => {
            eprintln!("nice-worker: .o compilation failed for {}: {}", module, e.message());
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
    let codegen_state = crate::pipeline::build_codegen_state_for_cache(
        &input.program,
        &check_result,
    );

    // Read symbol table from typecheck_products (populated by priority worker).
    let symbol_table = shared.typecheck_products
        .get(module)
        .map(|tp| tp.symbols.clone())
        .unwrap_or_else(|| cranelisp_types::SymbolTable::new(module.clone()));

    // Build a minimal ModuleStructure for cache metadata.
    // The v4 pipeline stores real data on the symbol table;
    // a stub structure with the module path is sufficient.
    let module_structure = cranelisp_types::ModuleStructure {
        path: module.clone(),
        file_path: None,
        mod_decls: Vec::new(),
        import_specs: Vec::new(),
        export_specs: Vec::new(),
        platform_specs: Vec::new(),
        impl_sexps: Vec::new(),
        impls: Vec::new(),
        dll_path: None,
    };

    let metadata = cache::CacheMetadata {
        symbol_table,
        module_structure,
        codegen_state,
    };
    if let Err(e) = cache::write_cached_metadata(&meta_path, &metadata) {
        eprintln!("nice-worker: .meta.json write failed for {}: {}", module, e.message());
        // Continue — the .o file was written successfully.
    }

    // Append the .o path for the linker.
    if let Ok(mut paths) = shared.compiled_o_paths.lock() {
        paths.push(o_path);
    }
}

