// cranelisp main: pipeline-v4.md §2.2 structure.
//
// Three modes: Run (--run), Link (--link), Repl (default).
// One CompilerSession, one code path. Workers are persistent.

use std::path::{Path, PathBuf};
use std::process;

use cranelisp_types::{CodegenBehaviour, CranelispError, Span};

use cranelisp::session_v4::{CommandResult, CompilerSession, SessionSettings};

// ---------------------------------------------------------------------------
// Action enum (pipeline-v4.md §2.1)
// ---------------------------------------------------------------------------

enum Action {
    Run,
    Link,
    Repl,
}

impl Action {
    fn codegen_behaviour(&self) -> CodegenBehaviour {
        match self {
            Action::Link => CodegenBehaviour::ObjectOnly,
            _ => CodegenBehaviour::InMemoryAndObject,
        }
    }
}

// ---------------------------------------------------------------------------
// Main (pipeline-v4.md §2.2)
// ---------------------------------------------------------------------------

fn main() {
    let (action, entry_module_path, settings) = parse_args();
    cranelisp::style::init_color(settings.no_color);

    if let Err(e) = run(action, &entry_module_path, settings) {
        eprintln!("error: {e}");
        process::exit(1);
    }
}

// ---------------------------------------------------------------------------
// run() — the single pipeline entry point (pipeline-v4.md §2.2)
// ---------------------------------------------------------------------------

/// One CompilerSession, one code path. Workers are persistent for the
/// session lifetime. Run/Link/REPL differ only in what happens after
/// compilation.
fn run(
    action: Action,
    entry_module_path: &Path,
    settings: SessionSettings,
) -> Result<(), CranelispError> {
    use std::io::{self, BufRead, Write};

    let entry_module_name = slug(entry_module_path);
    let project_root = base_dir(entry_module_path);

    // §2.2: CompilerSession::new(settings, project_root).
    // Workers are spawned and parked on condvars immediately.
    let mut s = CompilerSession::new(settings, project_root);

    // §3.1: Register the entry module. Front-end work (resolve, parse,
    // extract declarations) then enqueue for typechecking. Workers wake
    // and do expand+typecheck+codegen.
    s.register_module(&entry_module_name)?;

    match action {
        // §7: Run mode.
        Action::Run => {
            s.wait_inmem_complete()?;
            s.trampoline(&entry_module_name)?;
            s.wait_object_complete()?;
        }
        // §8: Link mode.
        Action::Link => {
            s.wait_object_complete()?;
            s.link_by_name(&entry_module_name)?;
        }
        // §6: REPL mode.
        Action::Repl => {
            let stdin = io::stdin();
            let stdout = io::stdout();
            let mut stdout = stdout.lock();

            // Wait for entry module (prelude) to be ready.
            s.wait_inmem_complete()?;

            s.print_banner(&mut stdout);

            let mut buffer = String::new();
            s.write_prompt(&mut stdout);

            for line in stdin.lock().lines() {
                let line = match line {
                    Ok(l) => l,
                    Err(_) => break,
                };

                buffer.push_str(&line);

                if !s.parens_balanced(&buffer) {
                    buffer.push('\n');
                    s.write_continuation_prompt(&mut stdout);
                    continue;
                }

                let input = buffer.trim().to_string();
                buffer.clear();

                match s.process_commands(&input, &mut stdout) {
                    CommandResult::Nothing => {}
                    CommandResult::Quit => break,
                    CommandResult::Final(text) => {
                        s.pretty_print(&text, &mut stdout);
                    }
                    CommandResult::Compile(src) => match s.eval(&src) {
                        Ok(Some(result)) => {
                            let text = s.format_eval_result(&result);
                            s.pretty_print(&text, &mut stdout);
                        }
                        Ok(None) => {}
                        Err(e) => {
                            let _ = writeln!(stdout, "Error: {e}");
                        }
                    },
                }

                s.write_prompt(&mut stdout);
            }

            let _ = writeln!(stdout);
            s.wait_object_complete()?;
        }
    }

    s.shutdown();
    Ok(())
}

// ---------------------------------------------------------------------------
// Argument parsing
// ---------------------------------------------------------------------------

fn parse_args() -> (Action, PathBuf, SessionSettings) {
    let args: Vec<String> = std::env::args().collect();
    let mut no_color = false;
    let mut no_cache = false;
    let mut priority_workers: Option<usize> = None;
    let mut nice_workers: Option<usize> = None;
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
            "--priority-workers" => {
                if i + 1 < args.len() {
                    priority_workers = Some(args[i + 1].parse().unwrap_or_else(|_| {
                        eprintln!("error: --priority-workers requires a number");
                        process::exit(1);
                    }));
                    i += 2;
                } else {
                    eprintln!("error: --priority-workers requires a number");
                    process::exit(1);
                }
            }
            "--nice-workers" => {
                if i + 1 < args.len() {
                    nice_workers = Some(args[i + 1].parse().unwrap_or_else(|_| {
                        eprintln!("error: --nice-workers requires a number");
                        process::exit(1);
                    }));
                    i += 2;
                } else {
                    eprintln!("error: --nice-workers requires a number");
                    process::exit(1);
                }
            }
            "--run" => {
                if i + 1 < args.len() {
                    run_file = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    eprintln!("error: --run requires a file argument");
                    process::exit(1);
                }
            }
            "--link" => {
                if i + 1 < args.len() {
                    link_file = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    eprintln!("error: --link requires a file argument");
                    process::exit(1);
                }
            }
            other => {
                eprintln!("error: unexpected argument: {other}");
                eprintln!(
                    "usage: cranelisp [--run <file.cl>] [--link <file.cl>] [--no-color] \
                     [--no-cache] [--priority-workers N] [--nice-workers N]"
                );
                process::exit(1);
            }
        }
    }

    // Determine codegen behaviour from action.
    let codegen_behaviour = if link_file.is_some() {
        CodegenBehaviour::ObjectOnly
    } else {
        CodegenBehaviour::InMemoryAndObject
    };

    // Default worker counts: 1 for now (single-threaded-per-pool for
    // initial debugging). Will default to num_cpus() once stable.
    let default_priority = 1;
    let default_nice = 1;

    let settings = SessionSettings {
        no_color,
        no_cache,
        codegen_behaviour,
        priority_workers: priority_workers.unwrap_or(default_priority),
        nice_workers: nice_workers.unwrap_or(default_nice),
    };

    if run_file.is_some() && link_file.is_some() {
        eprintln!("error: --run and --link cannot be used together");
        process::exit(1);
    }

    if let Some(path) = link_file {
        return (Action::Link, PathBuf::from(path), settings);
    }

    match run_file {
        Some(path) => (Action::Run, PathBuf::from(path), settings),
        None => (Action::Repl, PathBuf::from("user.cl"), settings),
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Derive module name from file path (file stem).
fn slug(path: &Path) -> String {
    path.file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("main")
        .to_string()
}

/// Derive project root from file path (parent directory).
fn base_dir(path: &Path) -> PathBuf {
    path.parent()
        .map(|p| p.to_path_buf())
        .unwrap_or_else(|| std::env::current_dir().unwrap_or_else(|_| PathBuf::from(".")))
}

/// Read source file.
#[allow(dead_code)] // Will be used by register_module or tests.
fn read_file(path: &Path) -> Result<String, CranelispError> {
    if !path.exists() {
        return Err(CranelispError::ModuleError {
            message: format!("file not found: {}", path.display()),
            file: Some(path.to_path_buf()),
            span: Span::SYNTHETIC,
        });
    }
    std::fs::read_to_string(path).map_err(|e| CranelispError::ModuleError {
        message: format!("cannot read '{}': {}", path.display(), e),
        file: Some(path.to_path_buf()),
        span: Span::SYNTHETIC,
    })
}
