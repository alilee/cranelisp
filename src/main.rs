// cranelisp main — pipeline-v3.md §2.2 north star.
//
// The control flow matches the target architecture exactly. Methods
// marked todo!() are filled in by subsequent waves of Sprint 40a.
// Methods with real implementations preserve current functionality.

use std::path::{Path, PathBuf};
use std::process;

use cranelisp_types::{
    CodegenBehaviour, CompileContext, ModuleFullPath, ModuleStrategy, Symbol, Type,
};

use cranelisp::session::CompilationSession;

// ---------------------------------------------------------------------------
// Action enum (pipeline-v3.md §2.1)
// ---------------------------------------------------------------------------

#[allow(dead_code)]
enum Action {
    Run,
    Link,
    Release,
    Repl,
}

// ---------------------------------------------------------------------------
// Settings (pipeline-v3.md §11)
// ---------------------------------------------------------------------------

#[allow(dead_code)]
struct Settings {
    no_color: bool,
    no_cache: bool,
}

// ---------------------------------------------------------------------------
// Main (pipeline-v3.md §2.2)
// ---------------------------------------------------------------------------

fn main() {
    match run() {
        Ok(code) => process::exit(code),
        Err(e) => {
            eprintln!("error: {e}");
            process::exit(1);
        }
    }
}

fn run() -> Result<i32, String> {
    let (action, entry_module_path, settings) = parse_args()?;

    cranelisp::style::init_color(settings.no_color);

    let project_root = entry_module_path
        .parent()
        .ok_or("entry module path has no parent")?
        .to_path_buf();
    let mut s = CompilationSession::new_async();
    s.new_placeholder(&project_root, &settings)?;

    if let Action::Release = action {
        s.build_release(&entry_module_path)
    } else {
        let src = read_file(&entry_module_path)?;

        let ctx = CompileContext {
            module: ModuleFullPath::derive_from(entry_module_path, project_root),
            codegen: (&action).into(),
        };

        s.compile_unit(&src, &ctx, ModuleStrategy::Replace).e()?;

        match action {
            Action::Run | Action::Repl => s.spawn_hot_inmem_codegen()?,
            _ => {}
        }
        s.spawn_nice_object_codegen()?;

        match action {
            Action::Repl => {
                s.spawn_file_watcher()?;
                loop {
                    let src = read_line()?;
                    s.pause_watcher_codegen()?;
                    s.hot_flush_in_mem_queue().e()?;
                    if let Some(form) = match s.process_commands(&src)? {
                        CommandResult::Quit => break,
                        CommandResult::Nothing => None,
                        CommandResult::Final(form) => Some(form),
                        CommandResult::Compile(src) => {
                        match s.compile_unit(&src, &ctx, ModuleStrategy::Additive) {
                            Ok(_result) => todo!("convert CompileUnitResult to Form"),
                            Err(e) => { eprintln!("{e}"); None }
                        }
                    }
                    } {
                        pretty_print_form(form);
                    }
                    s.resume_watcher_codegen()?;
                }
                s.hot_flush_object_queue().e()?;
                Ok(0)
            }
            Action::Run => {
                s.hot_flush_in_mem_queue().e()?;
                let result = s.trampoline(&ctx);
                s.hot_flush_object_queue().e()?;
                result
            }
            Action::Link => {
                s.hot_flush_object_queue().e()?;
                s.link(&ctx)
            }
            Action::Release => unreachable!(),
        }
    }
}

// ---------------------------------------------------------------------------
// Command result (pipeline-v3.md §7.1)
// ---------------------------------------------------------------------------

pub enum CommandResult {
    Quit,
    Nothing,
    Final(Form),
    Compile(String),
}

pub struct Form {
    // TODO: value, type, display metadata, source sexp
}

// ---------------------------------------------------------------------------
// Stub methods on CompilationSession — filled in by later waves.
//
// These are declared here temporarily. As each wave lands, the real
// implementations move to session.rs / pipeline.rs and these stubs are
// deleted.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// North-star methods on CompilationSession.
//
// Methods with real implementations preserve current functionality.
// Methods with todo!() are filled in by later waves.
// As waves land, these move to session.rs / pipeline.rs.
// ---------------------------------------------------------------------------

trait NorthStarMethods {
    fn new_placeholder(&mut self, project_root: &Path, settings: &Settings) -> Result<(), String>;
    fn spawn_file_watcher(&mut self) -> Result<(), String>;
    fn pause_watcher_codegen(&self) -> Result<(), String>;
    fn resume_watcher_codegen(&self) -> Result<(), String>;
    fn process_commands(&mut self, input: &str) -> Result<CommandResult, String>;
    fn trampoline(&mut self, ctx: &CompileContext) -> Result<i32, String>;
    fn link(&mut self, ctx: &CompileContext) -> Result<i32, String>;
    fn build_release(&mut self, entry_module_path: &Path) -> Result<i32, String>;
}

impl NorthStarMethods for CompilationSession {
    fn new_placeholder(&mut self, project_root: &Path, settings: &Settings) -> Result<(), String> {
        self.interactive = true;
        let lib_dirs = cranelisp::session::assemble_lib_dirs(project_root);
        let mut all_lib_dirs = vec![project_root.to_path_buf()];
        all_lib_dirs.extend(lib_dirs);
        self.lib_dirs = all_lib_dirs;
        self.project_root = project_root.to_path_buf();
        Ok(())
    }

    fn spawn_file_watcher(&mut self) -> Result<(), String> {
        todo!("Wave 4: move file watcher from ReplSession to CompilerSession")
    }

    fn pause_watcher_codegen(&self) -> Result<(), String> {
        // TODO Wave 3: pause watcher codegen enqueuing for GOT stability.
        Ok(())
    }

    fn resume_watcher_codegen(&self) -> Result<(), String> {
        // TODO Wave 3: resume watcher codegen enqueuing.
        Ok(())
    }

    fn process_commands(&mut self, _input: &str) -> Result<CommandResult, String> {
        todo!("Wave 4: move process_commands from ReplSession to CompilerSession")
    }

    fn trampoline(&mut self, ctx: &CompileContext) -> Result<i32, String> {
        let codegen_results = self.hot_flush_in_mem_queue().map_err(|e| format!("{e}"))?;
        self.shutdown_codegen();

        let result = codegen_results
            .into_iter()
            .last()
            .ok_or("no codegen result")?;

        // Verify main exists.
        let module_name = ctx.module.as_ref();
        let main_sym = Symbol::from("main");
        let qualified_main = Symbol::from(format!("{module_name}/main"));
        let main_exists = self
            .inmem_worker.lock().unwrap()
            .got_state
            .def_codegen
            .contains_key(&main_sym)
            || self
                .inmem_worker.lock().unwrap()
                .got_state
                .def_codegen
                .contains_key(&qualified_main);
        if !main_exists {
            return Err(
                "entry module has no `main` function — batch mode requires (defn main [] ...)"
                    .into(),
            );
        }

        let raw_value = result
            .value
            .ok_or("entry module produced no result value")?;
        let result_type = result.result_type.unwrap_or(Type::Int);

        // IO trampoline.
        let (value, ty) = if result_type.is_io() {
            (
                cranelisp_runtime::run_io_trampoline(raw_value),
                result_type.io_inner_type(),
            )
        } else {
            (raw_value, result_type)
        };

        // Display warnings and result.
        for w in &result.warnings {
            eprintln!("warning: {}", w.message);
        }
        let display = cranelisp::repl::format_result(value, &ty);
        println!("{display}");

        Ok(cranelisp::session::determine_exit_code(value, &ty))
    }

    fn link(&mut self, _ctx: &CompileContext) -> Result<i32, String> {
        todo!("Wave 4: collect .o paths, generate startup, invoke system linker")
    }

    fn build_release(&mut self, _entry_module_path: &Path) -> Result<i32, String> {
        Err("not implemented: build_release".into())
    }
}

fn pretty_print_form(_form: Form) {
    todo!("Wave 4: universal output format from repl/spec.md")
}

fn read_line() -> Result<String, String> {
    todo!("Wave 4: line editor integration")
}

// ---------------------------------------------------------------------------
// Conversions
// ---------------------------------------------------------------------------

impl From<&Action> for CodegenBehaviour {
    fn from(action: &Action) -> Self {
        match action {
            Action::Link => CodegenBehaviour::ObjectOnly,
            _ => CodegenBehaviour::InMemoryAndObject,
        }
    }
}

/// Extension trait to map CranelispError to String for `?` in run().
trait MapErrStr<T> {
    fn e(self) -> Result<T, String>;
}

impl<T> MapErrStr<T> for Result<T, cranelisp_types::CranelispError> {
    fn e(self) -> Result<T, String> {
        self.map_err(|e| format!("{e}"))
    }
}

fn read_file(path: &Path) -> Result<String, String> {
    if !path.exists() {
        // For REPL with no user.cl, empty source is valid.
        return Ok(String::new());
    }
    std::fs::read_to_string(path).map_err(|e| format!("cannot read '{}': {}", path.display(), e))
}

// ---------------------------------------------------------------------------
// Argument parsing
// ---------------------------------------------------------------------------

fn parse_args() -> Result<(Action, PathBuf, Settings), String> {
    let args: Vec<String> = std::env::args().collect();
    let mut no_color = false;
    let mut no_cache = false;
    let mut run_file: Option<String> = None;
    let mut link_file: Option<String> = None;
    let mut i = 1;

    while i < args.len() {
        match args[i].as_str() {
            "--no-cache" => {
                no_cache = true;
                i += 1;
            }
            "--no-color" => {
                no_color = true;
                i += 1;
            }
            "--run" => {
                if i + 1 < args.len() {
                    run_file = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    return Err("--run requires a file argument".into());
                }
            }
            "--link" => {
                if i + 1 < args.len() {
                    link_file = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    return Err("--link requires a file argument".into());
                }
            }
            other => {
                return Err(format!(
                    "unexpected argument: {other}\nusage: cranelisp [--run <file.cl>] [--link <file.cl>] [--no-color]"
                ));
            }
        }
    }

    if run_file.is_some() && link_file.is_some() {
        return Err("--run and --link cannot be used together".into());
    }

    let settings = Settings { no_color, no_cache };
    let cwd = std::env::current_dir().map_err(|e| format!("cannot get cwd: {e}"))?;

    if let Some(path) = link_file {
        let full = cwd.join(&path);
        return Ok((Action::Link, full, settings));
    }
    if let Some(path) = run_file {
        let full = cwd.join(&path);
        return Ok((Action::Run, full, settings));
    }

    // REPL default: user.cl in cwd (may not exist yet).
    Ok((Action::Repl, cwd.join("user.cl"), settings))
}
