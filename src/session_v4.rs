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
use std::time::{Duration, Instant};

use cranelisp_types::{
    CheckResult, CodegenBehaviour, CompileContext, CranelispError,
    DefKind, ModuleEntry, ModuleFullPath, ModuleStrategy, ModuleStructure,
    Sexp, Span, Symbol, SymbolTable, TopLevel, Type, TypeDefInfo,
    TypeName, Warning,
};

use crate::expander::MacroEnv;
use crate::platform::LoadedPlatform;
use crate::platform_registry::PlatformRegistry;
use crate::scheduler::CompileScheduler;
use crate::session::{CompilationSession, InMemWorkerState};
use crate::worker::WorkerContext;

// ---------------------------------------------------------------------------
// CommandResult (pipeline-v4.md §6.1)
// ---------------------------------------------------------------------------

/// Result of processing a REPL input line through `process_commands`.
///
/// Mirrors the v4 design: slash commands are handled inline, blank/comment
/// lines produce Nothing, and source text is returned for compilation.
pub enum CommandResult {
    /// Blank line, comment, or side-effect-only command (e.g., /quit).
    Nothing,
    /// Command that produces displayable output (e.g., /sig, /list).
    Final(String),
    /// Raw source text to submit for compilation.
    Compile(String),
}

// ---------------------------------------------------------------------------
// EvalResult (pipeline-v4.md §6.2)
// ---------------------------------------------------------------------------

/// Result of evaluating one REPL input via `CompilerSession::eval()`.
pub struct EvalResult {
    /// The i64 result value (raw bits; interpret per type).
    pub value: i64,
    /// The inferred type of the input.
    pub ty: Type,
    /// Whether this was a definition (defn/deftype) rather than an expression.
    pub is_definition: bool,
    /// Non-fatal warnings.
    pub warnings: Vec<Warning>,
    /// Override display string for definitions (deftrait, impl, constrained fn).
    pub definition_display: Option<String>,
    /// Time spent executing the compiled function pointer (excludes compilation).
    pub eval_duration: Duration,
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

/// Format macro display for bare-symbol introspection.
fn format_macro_display(
    name: &str,
    clauses: &[cranelisp_types::MacroClauseInfo],
    docstring: Option<&str>,
    _module: &ModuleFullPath,
) -> String {
    let clause_count = clauses.len();
    let doc_part = docstring.map_or(String::new(), |d| format!(" - {d}"));
    format!("{name} ; defmacro ({clause_count} clause(s)){doc_part}")
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
// CompilerSession (pipeline-v4.md §5)
// ---------------------------------------------------------------------------

/// Snapshot of typecheck + program data for a module, stored by the priority
/// worker after codegen so that nice workers can compile the `.o` file.
pub struct ObjectCodegenInput {
    pub check_result: CheckResult,
    pub program: Vec<TopLevel>,
    /// Cross-module function signatures accumulated up to this module.
    /// Each entry is (qualified_name, param_count).
    pub cross_module_func_sigs: Vec<(Symbol, usize)>,
    /// Cloned symbol table for .meta.json serialization.
    pub symbol_table: SymbolTable,
    /// Module structure for .meta.json serialization.
    pub module_structure: ModuleStructure,
}

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

    /// Module data for nice worker .o compilation. Populated by the priority
    /// worker after in-memory codegen completes; consumed by nice workers.
    pub object_codegen_inputs: Mutex<HashMap<ModuleFullPath, ObjectCodegenInput>>,

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
}

/// The v4 compiler session — the permanent session type for scheduler-driven
/// concurrent compilation.
///
/// Currently wraps `CompilationSession` and delegates all operations to the
/// old path. Each roadmap step progressively replaces delegation with native
/// v4 logic. The `--v4` CLI flag enables this session for testing.
pub struct CompilerSession {
    /// The wrapped old-path session. Kept alive for `link()` and prelude
    /// loading which still use `compile_unit()`. Will be removed in Step 15.
    pub inner: Option<CompilationSession>,

    /// Type checker state (persists across forms).
    pub tc: cranelisp_typecheck::TypeChecker,
    /// In-memory codegen worker state (GOT, JIT lifetimes, trace).
    pub inmem_worker: InMemWorkerState,
    /// Macro environment (persists across forms — macros accumulate).
    pub macro_env: MacroEnv,
    /// Directories to search when resolving module imports.
    pub lib_dirs: Vec<PathBuf>,
    /// Loaded platform DLL handles. Must remain alive for the process lifetime
    /// so that function pointers into the DLL code segments stay valid.
    pub loaded_platforms: Vec<LoadedPlatform>,

    /// Thread-safe state shared with nice worker threads. Wrapped in Arc
    /// so workers get an independent clone — no aliasing between `&mut self`
    /// (used by priority worker operations) and the shared reference held
    /// by nice workers. All SharedState fields are inherently thread-safe
    /// (Mutex, AtomicBool, read-only).
    pub shared: Arc<SharedState>,

    /// Project root directory (read-only after construction).
    pub project_root: PathBuf,

    /// Unified platform function registry (Step 8).
    /// Populated during platform loading, read-only during codegen.
    pub platform_registry: PlatformRegistry,

    // -- REPL-specific state (pipeline-v4.md §6) --

    /// Accumulated type definitions from all inputs (for ADT value display).
    pub type_defs: HashMap<TypeName, TypeDefInfo>,
    /// Maps type names to the module they were defined in (for qualified display).
    pub type_modules: HashMap<TypeName, ModuleFullPath>,
    /// Module structure for the current REPL module (tracks imports, exports,
    /// impl_sexps as they accumulate interactively). Used for persistence.
    pub current_module_structure: ModuleStructure,
    /// Modules that failed reload (file watcher). While non-empty, expression
    /// evaluation is blocked.
    pub error_modules: HashSet<ModuleFullPath>,
}

impl CompilerSession {
    /// Create a new v4 session wrapping the existing compilation path.
    ///
    /// Sets up lib_dirs, project_root, and interactive mode on the inner
    /// session, matching the old `new_session()` helper in main.rs.
    pub fn new(
        _no_color: bool,
        project_root: PathBuf,
        entry_path: &Path,
    ) -> Self {
        let lib_dirs = crate::session::assemble_lib_dirs(&project_root);

        let entry_dir = entry_path
            .canonicalize()
            .ok()
            .and_then(|p| p.parent().map(|d| d.to_path_buf()));

        let mut all_lib_dirs: Vec<PathBuf> = Vec::new();
        if let Some(dir) = &entry_dir {
            all_lib_dirs.push(dir.clone());
        }
        all_lib_dirs.extend(lib_dirs);
        let resolved_project_root = entry_dir.unwrap_or_else(|| project_root.clone());

        // Initialize direct fields (same defaults as CompilationSession::new()).
        let tc = cranelisp_typecheck::TypeChecker::new();
        let inmem_worker = InMemWorkerState::new();
        let macro_env = MacroEnv::new();

        // Also keep an inner CompilationSession for methods still using
        // the old path (link, hot_flush, shutdown_codegen).
        let mut inner = CompilationSession::new();
        inner.interactive = true;
        inner.lib_dirs = all_lib_dirs.clone();
        inner.project_root = resolved_project_root.clone();

        let cache_dir = project_root.join(".cranelisp-cache");
        let _ = std::fs::create_dir_all(&cache_dir);

        let cache_state = crate::session::CacheState::new(cache_dir.clone());

        CompilerSession {
            inner: Some(inner),
            tc,
            inmem_worker,
            macro_env,
            lib_dirs: all_lib_dirs,
            loaded_platforms: Vec::new(),
            shared: Arc::new(SharedState {
                scheduler: CompileScheduler::new(),
                cache_dir: Some(cache_dir),
                compiled_o_paths: Mutex::new(Vec::new()),
                promote_nice_workers: AtomicBool::new(false),
                object_codegen_inputs: Mutex::new(HashMap::new()),
                cached_modules: Mutex::new(HashSet::new()),
                file_to_module: Mutex::new(HashMap::new()),
                cache_state: Mutex::new(Some(cache_state)),
            }),
            project_root,
            platform_registry: PlatformRegistry::new(),
            type_defs: HashMap::new(),
            type_modules: HashMap::new(),
            current_module_structure: ModuleStructure {
                path: ModuleFullPath::from("user"),
                file_path: None,
                mod_decls: vec![],
                import_specs: vec![],
                export_specs: vec![],
                platform_specs: vec![],
                impl_sexps: vec![],
                impls: vec![],
                dll_path: None,
            },
            error_modules: HashSet::new(),
        }
    }

    /// Create a v4 session for link mode with caching enabled.
    pub fn new_for_link(
        project_root: PathBuf,
        entry_path: &Path,
        cache_dir: PathBuf,
    ) -> Result<Self, CranelispError> {
        let lib_dirs = crate::session::assemble_lib_dirs(&project_root);

        let canonical_entry = entry_path.canonicalize().map_err(|e| {
            CranelispError::ModuleError {
                message: format!("cannot canonicalize '{}': {}", entry_path.display(), e),
                file: Some(entry_path.to_path_buf()),
                span: Span::SYNTHETIC,
            }
        })?;

        std::fs::create_dir_all(&cache_dir).map_err(|e| CranelispError::ModuleError {
            message: format!("cannot create cache dir '{}': {}", cache_dir.display(), e),
            file: None,
            span: Span::SYNTHETIC,
        })?;

        let entry_dir = canonical_entry.parent().map(|p| p.to_path_buf());
        let mut all_lib_dirs: Vec<PathBuf> = Vec::new();
        if let Some(dir) = &entry_dir {
            all_lib_dirs.push(dir.clone());
        }
        all_lib_dirs.extend(lib_dirs);
        let resolved_project_root = entry_dir.unwrap_or_else(|| project_root.clone());

        // Initialize direct fields.
        let tc = cranelisp_typecheck::TypeChecker::new();
        let inmem_worker = InMemWorkerState::new();
        let macro_env = MacroEnv::new();

        // Inner session for link mode (uses compile_unit + async codegen).
        let mut inner = CompilationSession::new_async_with_cache(cache_dir.clone());
        inner.interactive = true;
        inner.lib_dirs = all_lib_dirs.clone();
        inner.project_root = resolved_project_root;

        let cache_state = crate::session::CacheState::new(cache_dir.clone());

        Ok(CompilerSession {
            inner: Some(inner),
            tc,
            inmem_worker,
            macro_env,
            lib_dirs: all_lib_dirs,
            loaded_platforms: Vec::new(),
            shared: Arc::new(SharedState {
                scheduler: CompileScheduler::new(),
                cache_dir: Some(cache_dir.clone()),
                compiled_o_paths: Mutex::new(Vec::new()),
                promote_nice_workers: AtomicBool::new(false),
                object_codegen_inputs: Mutex::new(HashMap::new()),
                cached_modules: Mutex::new(HashSet::new()),
                file_to_module: Mutex::new(HashMap::new()),
                cache_state: Mutex::new(Some(cache_state)),
            }),
            project_root,
            platform_registry: PlatformRegistry::new(),
            type_defs: HashMap::new(),
            type_modules: HashMap::new(),
            current_module_structure: ModuleStructure {
                path: ModuleFullPath::from("user"),
                file_path: None,
                mod_decls: vec![],
                import_specs: vec![],
                export_specs: vec![],
                platform_specs: vec![],
                impl_sexps: vec![],
                impls: vec![],
                dll_path: None,
            },
            error_modules: HashSet::new(),
        })
    }

    /// Register a module for compilation via the v4 scheduler-driven path.
    ///
    /// All programs go through the v4 path with lazy dependency discovery.
    /// The C2 filter and old delegation path are deleted (Step 5).
    ///
    /// Returns warnings from compilation. Codegen results are available
    /// via GOT after `scheduler.wait_inmem_complete()`.
    pub fn register_module(
        &mut self,
        module_name: &str,
        source: &str,
        _entry_module_path: &Path,
    ) -> Result<Vec<Warning>, CranelispError> {
        let module = ModuleFullPath::from(module_name);
        let sexps = cranelisp_frontend::parse(source)?;

        // Register module with scheduler (entry module, not delaying others).
        self.shared.scheduler.register_module(module.clone(), false);

        // Build sexp map for the worker loop.
        let mut module_sexps = HashMap::new();
        module_sexps.insert(module.clone(), sexps);

        // Extract shared codegen state from InMemWorkerState for the worker loop.
        // This bridges the old InMemWorkerState with the new SharedCodegenState
        // + WorkerJitState types. After the loop, state is synced back.
        let shared_codegen =
            crate::session::SharedCodegenState::extract_from(&mut self.inmem_worker);
        let mut worker_jit = crate::session::WorkerJitState::new();

        // Build WorkerContext bundling all worker parameters.
        let mut ctx = WorkerContext {
            tc: &mut self.tc,
            scheduler: &self.shared.scheduler,
            shared_codegen: &shared_codegen,
            worker_jit: &mut worker_jit,
            platform_registry: &mut self.platform_registry,
            lib_dirs: &self.lib_dirs,
            project_root: &self.project_root,
            object_codegen_stash: Some(&self.shared.object_codegen_inputs),
            shared_state: Some(&self.shared),
        };

        // Run the priority worker loop inline (single-threaded).
        let loop_result = crate::worker::priority_worker_loop(
            &mut ctx,
            &mut module_sexps,
        );

        // Drain per-worker JIT state to shared before syncing back.
        worker_jit.drain_to_shared(&shared_codegen);

        // Sync shared codegen state back to InMemWorkerState.
        shared_codegen.sync_back_to(&mut self.inmem_worker);

        // Propagate any error from the worker loop.
        loop_result?;

        // Check scheduler completion.
        self.shared.scheduler.wait_inmem_complete()?;

        // Register module aliases for GOT lookup by unqualified name.
        crate::session::register_module_aliases_filtered(
            &mut self.inmem_worker,
            &module,
            None,
        );

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
                // Signal quit via special Final string.
                CommandResult::Final(QUIT_SENTINEL.to_string())
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
            ReplCommand::Unknown(cmd) => {
                CommandResult::Final(format!(
                    "error: unknown command '{cmd}'. Type /help for available commands."
                ))
            }
            // Commands not yet ported — show not-yet-implemented message.
            _ => {
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
                    all_warnings.extend(result.warnings.clone());
                    last_result = Some(result);
                }
                Ok(None) => {}
                Err(e) => {
                    if sexps.len() == 1 {
                        return Err(e);
                    }
                    // Multi-form: report error inline but continue.
                    last_result = Some(EvalResult {
                        value: 0,
                        ty: Type::Int,
                        is_definition: false,
                        warnings: Vec::new(),
                        definition_display: Some(format!("Error: {e}")),
                        eval_duration: Duration::ZERO,
                    });
                }
            }
        }

        // Sync type definitions for ADT value display.
        self.sync_type_defs();

        if let Some(ref mut r) = last_result {
            r.warnings = all_warnings;
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
            Ok(result) => Ok(Some(result)),
            Err(e) => {
                self.tc.restore(snapshot);
                Err(e)
            }
        }
    }

    /// Process a single sexp through `process_module_forms(Additive)` then codegen.
    ///
    /// Handles blocked dependencies by compiling them inline and retrying.
    fn process_single_form(&mut self, sexp: &Sexp) -> Result<EvalResult, CranelispError> {
        use crate::worker::{self, ProcessResult};
        use cranelisp_typecheck::ModuleCheckAccumulator;

        const MAX_DEP_RETRIES: usize = 100;

        for retry in 0..MAX_DEP_RETRIES {
            let module = self.tc.current_module_path().clone();
            let mut accumulator = ModuleCheckAccumulator::new();
            let mut expanded_program = Vec::new();
            let single_sexp = [sexp.clone()];

            let result = {
                let shared_codegen =
                    crate::session::SharedCodegenState::extract_from(&mut self.inmem_worker);
                let mut worker_jit = crate::session::WorkerJitState::new();

                let mut wctx = WorkerContext {
                    tc: &mut self.tc,
                    scheduler: &self.shared.scheduler,
                    shared_codegen: &shared_codegen,
                    worker_jit: &mut worker_jit,
                    platform_registry: &mut self.platform_registry,
                    lib_dirs: &self.lib_dirs,
                    project_root: &self.project_root,
                    object_codegen_stash: None,
                    shared_state: None,
                };

                let r = worker::process_module_forms(
                    &mut wctx,
                    &module,
                    &single_sexp,
                    0,
                    &mut accumulator,
                    &mut expanded_program,
                    ModuleStrategy::Additive,
                );

                worker_jit.drain_to_shared(&shared_codegen);
                shared_codegen.sync_back_to(&mut self.inmem_worker);
                r?
            };

            match result {
                ProcessResult::Complete { check_result, program } => {
                    return self.codegen_and_execute(&module, &program, &check_result);
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
        // Codegen: compile definitions, register in GOT.
        {
            let shared_codegen =
                crate::session::SharedCodegenState::extract_from(&mut self.inmem_worker);
            let mut worker_jit = crate::session::WorkerJitState::new();
            let result = crate::worker::codegen_module_symbols(
                &shared_codegen,
                &mut worker_jit,
                &self.platform_registry,
                &self.shared.scheduler,
                module,
                program,
                check,
            );
            worker_jit.drain_to_shared(&shared_codegen);
            shared_codegen.sync_back_to(&mut self.inmem_worker);
            result?;
        }

        let has_expr = program.iter().any(|tl| matches!(tl, TopLevel::Expr(_)));

        if has_expr {
            let program_vec = program.to_vec();
            let eval_start = Instant::now();
            let ps = self.platform_registry.jit_symbols_owned();
            let (value, ty) = crate::pipeline::compile_and_execute_expr(
                &mut self.inmem_worker,
                &ps,
                &program_vec,
                check,
            )?;
            let eval_duration = eval_start.elapsed();

            Ok(EvalResult {
                value,
                ty,
                is_definition: false,
                warnings: check.warnings.clone(),
                definition_display: None,
                eval_duration,
            })
        } else {
            // Definition-only: build display text.
            let display = check.display.as_ref().and_then(|d| {
                d.scheme.as_ref().map(|s| format!(":{} ; defined", s.ty))
            });

            let ty = check.display.as_ref()
                .map(|d| d.ty.clone())
                .unwrap_or(Type::Int);

            Ok(EvalResult {
                value: 0,
                ty,
                is_definition: true,
                warnings: check.warnings.clone(),
                definition_display: display,
                eval_duration: Duration::ZERO,
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

        let shared_codegen =
            crate::session::SharedCodegenState::extract_from(&mut self.inmem_worker);
        let mut worker_jit = crate::session::WorkerJitState::new();

        let mut ctx = WorkerContext {
            tc: &mut self.tc,
            scheduler: &self.shared.scheduler,
            shared_codegen: &shared_codegen,
            worker_jit: &mut worker_jit,
            platform_registry: &mut self.platform_registry,
            lib_dirs: &self.lib_dirs,
            project_root: &self.project_root,
            object_codegen_stash: None,
            shared_state: None,
        };

        let loop_result = crate::worker::priority_worker_loop(&mut ctx, &mut module_sexps);
        worker_jit.drain_to_shared(&shared_codegen);
        shared_codegen.sync_back_to(&mut self.inmem_worker);
        loop_result?;

        match self.shared.scheduler.wait_inmem_complete() {
            Ok(()) => Ok(()),
            Err(e) => {
                self.shared.scheduler.reset_all_failed_modules();
                Err(CranelispError::from(e))
            }
        }
    }

    /// Check if a bare symbol should produce introspection display instead of eval.
    fn check_bare_symbol_introspection(&self, sexp: &Sexp) -> Option<EvalResult> {
        let name = match sexp {
            Sexp::Symbol(name, _) => name,
            _ => return None,
        };

        let entry = {
            let guard = self.tc.symbol_table();
            guard.get(name.as_str())?.clone()
        };

        match &entry {
            ModuleEntry::Macro { clauses, docstring, .. } => {
                // Zero-arg macros should be expanded, not introspected.
                let has_zero_arg = clauses.iter().any(|c| {
                    c.params.is_empty() && c.rest_param.is_none()
                });
                if has_zero_arg {
                    return None;
                }
                let module = self.tc.current_module_path().clone();
                let display = format_macro_display(name, clauses, docstring.as_deref(), &module);
                Some(EvalResult {
                    value: 0,
                    ty: Type::Int,
                    is_definition: true,
                    warnings: Vec::new(),
                    definition_display: Some(display),
                    eval_duration: Duration::ZERO,
                })
            }
            ModuleEntry::Def { kind, .. } => {
                if let DefKind::SpecialForm { description } = kind.as_ref() {
                    let display = format!("{name} ; special form - {description}");
                    Some(EvalResult {
                        value: 0,
                        ty: Type::Int,
                        is_definition: true,
                        warnings: Vec::new(),
                        definition_display: Some(display),
                        eval_duration: Duration::ZERO,
                    })
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Sync type definitions from the typechecker for ADT value display.
    fn sync_type_defs(&mut self) {
        for (name, info) in self.tc.type_def_registry().iter() {
            self.type_defs.insert(name.clone(), info.clone());
        }
    }

    /// Load prelude into this session for REPL mode.
    ///
    /// Compiles an empty source for the user module via the inner
    /// CompilationSession, which triggers the auto-prelude mechanism.
    /// Then swaps the inner session's state (TC, inmem_worker, macro_env)
    /// into the CompilerSession's direct fields for v4 eval.
    pub fn load_prelude(&mut self) -> Result<(), CranelispError> {
        let inner = self.inner.as_mut().ok_or_else(|| CranelispError::ModuleError {
            message: "inner session required for prelude loading".into(),
            file: None,
            span: Span::SYNTHETIC,
        })?;

        let user_ctx = CompileContext {
            module: ModuleFullPath::from("user"),
            codegen: CodegenBehaviour::InMemoryAndObject,
        };
        let unit_result = inner.compile_unit("", &user_ctx, ModuleStrategy::Additive)?;
        crate::pipeline::codegen_and_execute_via_session(inner, &unit_result, &user_ctx)?;
        inner.flush_cache_writes();
        if let Some(cs) = &inner.object_worker.cache_state {
            cs.flush_manifest();
        }

        // Swap the inner session's state into our direct fields.
        // This moves ownership — the inner session's fields become defaults.
        std::mem::swap(&mut self.tc, &mut inner.tc);
        std::mem::swap(&mut self.inmem_worker, &mut inner.inmem_worker);
        std::mem::swap(&mut self.macro_env, &mut inner.macro_env);

        // Sync type defs for ADT display.
        self.sync_type_defs();

        // Switch back to user module.
        self.tc.set_current_module(ModuleFullPath::from("user"));

        // Ensure the scheduler is initialized for REPL eval.
        self.shared.scheduler.register_module(
            ModuleFullPath::from("user"), false,
        );

        Ok(())
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
                return Some(format!("{trimmed} ; special form - {description}"));
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
        // Flush old-path codegen queue (no-op if queue is empty, i.e. v4 path).
        if let Some(ref mut inner) = self.inner {
            let _ = inner.hot_flush_in_mem_queue()?;
            inner.shutdown_codegen();
        }

        // Look up main in GOT.
        let main_sym = cranelisp_types::Symbol::from("main");
        let qualified_main =
            cranelisp_types::Symbol::from(format!("{}/main", module_name));

        let code_ptr = self.lookup_main_code_ptr(&main_sym, &qualified_main)?;
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

    /// Look up the code pointer for `main` in the GOT.
    fn lookup_main_code_ptr(
        &self,
        main_sym: &cranelisp_types::Symbol,
        qualified_main: &cranelisp_types::Symbol,
    ) -> Result<*const u8, CranelispError> {
        let got = &self.inmem_worker.got_state;

        // Try unqualified name first, then qualified.
        if let Some(entry) = got.def_codegen.get(main_sym)
            && let Some(ptr) = entry.code_ptr
        {
            return Ok(ptr);
        }
        if let Some(entry) = got.def_codegen.get(qualified_main)
            && let Some(ptr) = entry.code_ptr
        {
            return Ok(ptr);
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

    /// Link all compiled modules into an executable.
    ///
    /// Delegates to the old link path. In v4, this will use the scheduler's
    /// module tracking to collect .o files (Step 9+).
    pub fn link(
        &mut self,
        entry_path: &Path,
    ) -> Result<(), CranelispError> {
        // The old link_mode is a standalone function in main.rs that creates
        // its own session. For Step 0, we delegate by using the inner session
        // fields directly, matching the old link_mode logic.
        let inner = self.inner.as_mut().ok_or_else(|| CranelispError::ModuleError {
            message: "link mode requires inner CompilationSession".into(),
            file: None,
            span: Span::SYNTHETIC,
        })?;
        let graph = crate::pipeline::discover_module_graph(
            entry_path,
            &inner.lib_dirs,
        )?;
        let order = crate::pipeline::toposort(&graph)?;

        let mut all_warnings: Vec<Warning> = Vec::new();

        // Compile each module in topo order.
        for module_path in &order {
            let node = &graph.nodes[module_path];
            let source = std::fs::read_to_string(&node.file_path).map_err(|e| {
                CranelispError::ModuleError {
                    message: format!("cannot read '{}': {}", node.file_path.display(), e),
                    file: Some(node.file_path.clone()),
                    span: Span::SYNTHETIC,
                }
            })?;

            let ctx = CompileContext {
                module: module_path.clone(),
                codegen: CodegenBehaviour::InMemoryAndObject,
            };

            let unit_result =
                inner.compile_unit(&source, &ctx, ModuleStrategy::Replace)?;
            all_warnings.extend(unit_result.warnings.clone());
            inner.send_codegen(unit_result, ctx);
            let codegen_results = inner.flush_codegen()?;
            for cr in codegen_results {
                all_warnings.extend(cr.warnings);
            }
        }

        // Shut down workers, flush .o writes.
        inner.shutdown_codegen();
        inner.flush_cache_writes();
        let module_o_paths = inner.object_worker.compiled_o_paths.clone();

        // Validate main, generate startup, link executable.
        inner.tc.set_current_module(graph.entry.clone());
        let entry_symbols = inner.tc.symbol_table().clone();
        let module_structures = inner.object_worker.compiled_module_structures.clone();

        for w in &all_warnings {
            eprintln!("warning: {}", w.message);
        }

        let cache_dir = self.project_root.join(".cranelisp-cache");
        let main_return = crate::exe::validate_main(&entry_symbols)?;
        let platform_names =
            crate::exe::collect_platform_manifest_names(&module_structures);
        let main_returns_io = main_return == crate::exe::MainReturnKind::Io;
        let startup_bytes =
            crate::exe::generate_startup_object(&platform_names, main_returns_io)?;
        let startup_o_path = cache_dir.join("_startup.o");
        std::fs::write(&startup_o_path, &startup_bytes).map_err(|e| {
            CranelispError::ModuleError {
                message: format!("cannot write startup object: {}", e),
                file: Some(startup_o_path.clone()),
                span: Span::SYNTHETIC,
            }
        })?;
        let bundle_lib = crate::exe::find_bundle_lib()?;
        let platform_rlibs = crate::exe::find_platform_rlibs(&module_structures);
        let output_path = PathBuf::from(
            entry_path
                .file_stem()
                .unwrap_or(std::ffi::OsStr::new("a.out")),
        );
        crate::exe::link_executable(
            &output_path,
            &module_o_paths,
            &startup_o_path,
            &bundle_lib,
            &platform_rlibs,
        )?;
        eprintln!("; Linked: {}", output_path.display());
        Ok(())
    }

    /// Run a batch compilation with priority and nice worker threads.
    ///
    /// Spawns `priority_count` priority workers and `nice_count` nice
    /// workers in a single `std::thread::scope`. The calling thread
    /// parses the entry module, registers it with the scheduler, and
    /// waits for completion. Workers perform typecheck + JIT codegen.
    ///
    /// The TypeChecker and PlatformRegistry are temporarily moved into
    /// Mutex wrappers accessible by priority workers. After the scope
    /// exits (all workers joined), they are moved back to `self.inner`.
    ///
    /// Returns the module name for use by the caller (e.g., trampoline).
    pub fn run_with_workers(
        &mut self,
        priority_count: usize,
        nice_count: usize,
        module_name: &str,
        source: &str,
    ) -> Result<Vec<Warning>, CranelispError> {
        let module = ModuleFullPath::from(module_name);
        let sexps = cranelisp_frontend::parse(source)?;

        // Move TC and PlatformRegistry into Mutex for worker access.
        let tc = std::mem::replace(
            &mut self.tc,
            cranelisp_typecheck::TypeChecker::new(),
        );
        let tc_mutex = Mutex::new(tc);

        let platform_registry = std::mem::replace(
            &mut self.platform_registry,
            crate::platform_registry::PlatformRegistry::new(),
        );
        let platform_mutex = Mutex::new(platform_registry);

        // Extract shared codegen state from InMemWorkerState.
        let shared_codegen =
            crate::session::SharedCodegenState::extract_from(&mut self.inmem_worker);

        // Shared sexp and suspend state maps for workers.
        let module_sexps_map: Mutex<HashMap<ModuleFullPath, Vec<cranelisp_types::Sexp>>> = {
            let mut map = HashMap::new();
            map.insert(module.clone(), sexps);
            Mutex::new(map)
        };
        let suspend_states: Mutex<HashMap<ModuleFullPath, crate::worker::ModuleSuspendState>> =
            Mutex::new(HashMap::new());

        let shared_arc = Arc::clone(&self.shared);

        let worker_shared = crate::worker::PriorityWorkerShared {
            tc: &tc_mutex,
            platform_registry: &platform_mutex,
            shared_codegen: &shared_codegen,
            scheduler: &self.shared.scheduler,
            module_sexps: &module_sexps_map,
            suspend_states: &suspend_states,
            lib_dirs: &self.lib_dirs,
            project_root: &self.project_root,
            object_codegen_stash: &self.shared.object_codegen_inputs,
            shared_state: Some(&self.shared),
        };

        // Register module with scheduler — workers will pick it up.
        self.shared.scheduler.register_module(module.clone(), false);

        let result: Result<(), CranelispError> = std::thread::scope(|scope| {
            // Spawn priority workers.
            for i in 0..priority_count {
                let ws = &worker_shared;
                std::thread::Builder::new()
                    .name(format!("priority-worker-{}", i))
                    .spawn_scoped(scope, move || {
                        crate::worker::priority_worker_thread(ws, i);
                    })
                    .expect("failed to spawn priority worker thread");
            }

            // Spawn nice workers.
            spawn_nice_workers(scope, &shared_arc, nice_count);

            // Block until all in-memory codegen is complete.
            // This parks on the completion condvar, woken when workers
            // call notify_inmem_codegen_complete or on failure/shutdown.
            let wait_result = self.shared.scheduler
                .wait_inmem_complete_blocking()
                .map_err(|e| CranelispError::ModuleError {
                    message: format!("scheduler error: {:?}", e),
                    file: None,
                    span: Span::SYNTHETIC,
                });

            // Wait for nice workers to finish .o compilation.
            let _ = self.wait_object_complete();
            self.shared.scheduler.shutdown();

            wait_result
        });

        // Move TC and PlatformRegistry back.
        self.tc = tc_mutex.into_inner()
            .unwrap_or_else(|e| e.into_inner());
        self.platform_registry = platform_mutex.into_inner()
            .unwrap_or_else(|e| e.into_inner());

        // Sync shared codegen state back to InMemWorkerState.
        shared_codegen.sync_back_to(&mut self.inmem_worker);

        // Register module aliases for GOT lookup by unqualified name.
        crate::session::register_module_aliases_filtered(
            &mut self.inmem_worker,
            &module,
            None,
        );

        result?;
        Ok(Vec::new())
    }

    /// Run a closure with nice worker threads only (no priority workers).
    ///
    /// Used by paths that run the priority worker loop inline (e.g., link
    /// mode which uses the old compile_unit path).
    pub fn run_with_nice_workers<T>(
        &mut self,
        n: usize,
        f: impl FnOnce(&mut Self) -> Result<T, CranelispError>,
    ) -> Result<T, CranelispError> {
        let shared_arc = Arc::clone(&self.shared);

        std::thread::scope(|scope| {
            spawn_nice_workers(scope, &shared_arc, n);
            let result = f(self);
            let _ = self.wait_object_complete();
            self.shared.scheduler.shutdown();
            result
        })
    }

    /// Wait until all registered modules have object codegen complete.
    ///
    /// Promotes nice workers to normal priority before blocking, ensuring
    /// object codegen completes promptly (e.g., before linking). Wakes
    /// the `object_work_available` condvar so workers observe the promotion
    /// flag on their next loop iteration.
    pub fn wait_object_complete(
        &self,
    ) -> Result<(), crate::scheduler::SchedulerError> {
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
        // Inner session's Drop handles legacy codegen worker shutdown.
    }
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
/// `ObjectCodegenInput` is available for a module, the worker skips
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
/// Retrieves the module's `ObjectCodegenInput` (stashed by the priority worker),
/// builds an `ObjectCompileInput`, calls `compile_module_to_object()`, writes
/// the `.o` bytes, builds `CacheMetadata`, and writes `.meta.json`. Appends the
/// `.o` path to `shared.compiled_o_paths`.
///
/// Errors are logged to stderr and do not halt the worker — the module is still
/// marked object-complete so the scheduler lifecycle proceeds.
fn compile_module_object(
    shared: &SharedState,
    module: &ModuleFullPath,
    cache_dir: &Path,
) {
    use cranelisp_backend::cache;

    // Take the stashed input (lock briefly, remove entry to release memory).
    let input = {
        let mut inputs = shared.object_codegen_inputs.lock()
            .unwrap_or_else(|e| e.into_inner());
        inputs.remove(module)
    };

    let Some(input) = input else {
        // No data stashed — module may have had no compilable defns.
        return;
    };

    // Skip modules with no compilable defns (types-only, imports-only).
    if !crate::session::has_compilable_defns(&input.program) {
        return;
    }

    // Build the ObjectCompileInput from the stashed data.
    let object_input = crate::pipeline::build_object_compile_input(
        module,
        Some(&input.program),
        Some(&input.check_result),
        &input.cross_module_func_sigs,
    );

    // Compile to .o bytes via Cranelift ObjectModule.
    let obj_bytes = match cache::compile_module_to_object(&object_input) {
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
        &input.check_result,
    );
    let metadata = cache::CacheMetadata {
        symbol_table: input.symbol_table,
        module_structure: input.module_structure,
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

