// cranelisp main: pipeline-v4.md §2.2 structure.
//
// Three modes: Run (--run), Link (--link), Repl (default).
// One CompilerSession, one code path. Workers are persistent.

use std::path::{Path, PathBuf};
use std::process;
use std::time::Instant;

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
    let (action, project_root, entry_module, settings) = parse_args();
    cranelisp::style::init_color(settings.no_color);

    if let Err(e) = run(action, &project_root, &entry_module, settings) {
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
    project_root: &Path,
    entry_module_name: &str,
    settings: SessionSettings,
) -> Result<(), CranelispError> {
    use std::io::{self, BufRead, Write};

    // §2.2: CompilerSession::new(settings, project_root).
    // Workers are spawned and parked on condvars immediately.
    let mut s = CompilerSession::new(settings, project_root.to_path_buf());

    // §3.1: Register the entry module. Front-end work (resolve, parse,
    // extract declarations) then enqueue for typechecking. Workers wake
    // and do expand+typecheck+codegen.
    s.register_module(entry_module_name)?;

    match action {
        // §7: Run mode (spec §12.6).
        // main returns IO _. Exit code is the inner Int value, or 0 for
        // non-Int IO results and non-IO main (pre-Ring-4 compatibility).
        Action::Run => {
            s.wait_inmem_complete()?;
            let (value, ty) = s.trampoline(entry_module_name)?;
            s.wait_object_complete()?;
            s.shutdown();
            let exit_code = if ty == cranelisp_types::Type::Int {
                value as i32
            } else {
                0
            };
            process::exit(exit_code);
        }
        // §8: Link mode.
        Action::Link => {
            s.wait_object_complete()?;
            s.link_by_name(entry_module_name)?;
        }
        // §6: REPL mode.
        Action::Repl => {
            let stdin = io::stdin();
            let stdout = io::stdout();
            let mut stdout = stdout.lock();

            // Wait for entry module (prelude) to be ready.
            s.wait_inmem_complete()?;

            // Initialize file watcher now that modules are loaded.
            s.init_watcher();

            s.print_banner(&mut stdout);

            let mut buffer = String::new();
            let mut compile_ms: u64 = 0;
            let mut eval_ms: u64 = 0;
            s.write_prompt(&mut stdout, compile_ms, eval_ms);

            for line in stdin.lock().lines() {
                let line = match line {
                    Ok(l) => l,
                    Err(_) => break,
                };

                buffer.push_str(&line);

                // Slash commands are complete on a single line regardless of
                // paren balance — their arguments may contain unbalanced parens
                // (e.g., `/sh echo '(broken' > file.cl`).
                if !buffer.trim_start().starts_with('/') && !s.parens_balanced(&buffer) {
                    buffer.push('\n');
                    s.write_continuation_prompt(&mut stdout, compile_ms, eval_ms);
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
                    CommandResult::Compile(src) => {
                        let t0 = Instant::now();
                        match s.eval(&src) {
                            Ok(Some(result)) => {
                                let t1 = Instant::now();
                                let text = s.format_eval_result(&result);
                                let t2 = Instant::now();
                                compile_ms = (t1 - t0).as_millis() as u64;
                                eval_ms = (t2 - t1).as_millis() as u64;
                                s.pretty_print(&text, &mut stdout);
                                // Persist definitions to backing file (repl/spec.md §15).
                                if result.is_def() {
                                    s.regenerate_backing_file();
                                }
                            }
                            Ok(None) => {
                                compile_ms = t0.elapsed().as_millis() as u64;
                                eval_ms = 0;
                                // Structural changes (import, mod, platform) also
                                // need persistence. Regenerate if the module has content.
                                s.regenerate_backing_file();
                            }
                            Err(e) => {
                                compile_ms = t0.elapsed().as_millis() as u64;
                                eval_ms = 0;
                                let _ = writeln!(stdout, "Error: {e}");
                            }
                        }
                    }
                }

                // Sync watcher with any newly-loaded modules (e.g. from import).
                s.sync_watcher();

                // Poll file watcher for changed source files (repl/spec.md §14).
                for msg in s.poll_and_reload() {
                    let _ = writeln!(stdout, "{msg}");
                }

                s.write_prompt(&mut stdout, compile_ms, eval_ms);
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

fn parse_args() -> (Action, PathBuf, String, SessionSettings) {
    let args: Vec<String> = std::env::args().collect();
    let mut no_color = false;
    let mut no_cache = false;
    let mut priority_workers: Option<usize> = None;
    let mut nice_workers: Option<usize> = None;
    let mut action_run = false;
    let mut action_link = false;
    let mut target: Option<String> = None;
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
                action_run = true;
                i += 1;
            }
            "--link" => {
                action_link = true;
                i += 1;
            }
            arg if arg.starts_with("--") => {
                eprintln!("error: unknown flag: {arg}");
                eprintln!(
                    "usage: cranelisp [target] [--run | --link] [--no-color] \
                     [--no-cache] [--priority-workers N] [--nice-workers N]"
                );
                process::exit(1);
            }
            _ => {
                if target.is_some() {
                    eprintln!("error: unexpected argument: {}", args[i]);
                    eprintln!(
                        "usage: cranelisp [target] [--run | --link] [--no-color] \
                         [--no-cache] [--priority-workers N] [--nice-workers N]"
                    );
                    process::exit(1);
                }
                target = Some(args[i].clone());
                i += 1;
            }
        }
    }

    if action_run && action_link {
        eprintln!("error: --run and --link cannot be used together");
        process::exit(1);
    }

    if no_cache && action_link {
        eprintln!("error: --no-cache is not supported with --link");
        process::exit(1);
    }

    let action = if action_link {
        Action::Link
    } else if action_run {
        Action::Run
    } else {
        Action::Repl
    };

    // Resolve (project_root, entry_module) per spec §0.5.1.
    let (project_root, entry_module) = resolve_target(target.as_deref());

    let codegen_behaviour = action.codegen_behaviour();

    let settings = SessionSettings {
        no_color,
        no_cache,
        codegen_behaviour,
        priority_workers: priority_workers.unwrap_or(1),
        nice_workers: nice_workers.unwrap_or(1),
    };

    (action, project_root, entry_module, settings)
}

/// Resolve a positional target to (project_root, entry_module) per spec §0.5.1.
///
/// Rules:
/// 1. No target → (cwd, "user")
/// 2. Target has `/` → (directory portion, final component)
/// 3. Target is an existing directory → (target, "user")
/// 4. Bare name → (cwd, target)
///
/// The `.cl` extension is stripped if present. Project root is resolved to
/// an absolute path.
fn resolve_target(target: Option<&str>) -> (PathBuf, String) {
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

    let target = match target {
        None => return (cwd, "user".to_string()),
        Some(t) => t,
    };

    // Strip .cl extension if present.
    let target = target.strip_suffix(".cl").unwrap_or(target);

    let path = Path::new(target);

    if target.contains('/') {
        // Rule 2: has directory component.
        let dir = path.parent().unwrap_or(Path::new("."));
        let module = path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or("user")
            .to_string();
        let project_root = make_absolute(dir, &cwd);
        (project_root, module)
    } else if cwd.join(target).is_dir() {
        // Rule 3: existing directory.
        let project_root = make_absolute(Path::new(target), &cwd);
        (project_root, "user".to_string())
    } else {
        // Rule 4: bare name.
        (cwd, target.to_string())
    }
}

/// Resolve a possibly-relative path to absolute using a base directory.
fn make_absolute(path: &Path, base: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        base.join(path)
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

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
