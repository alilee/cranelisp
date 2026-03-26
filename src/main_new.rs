// cranelisp: CLI entry point.

use std::path::{Path, PathBuf};
use std::process;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let (mode, no_color) = parse_args(&args);

    /* params
    entry-module.cl|user-directory    // entry module to load (or create if not exists). if directory then path/user.cl, otherwise cwd/user.cl
    --run | --link | --release        // to that module: compile and run it, or link and exe for it, or build an optimised release for it. otherwise repl with entry module as starting point
    --lib_search lib_path{,lib_path}+ // add lib search path/s from cli
    */

    let action = Action::Run|Link|Release|Repl;
    let entry_module_path = ...;

    let entry_module_name = slug(entry_module_path);
    let project root = base_dir(entry_module_path);

    let settings = Settings::read_from_toml(project_root); // for lib search paths (so far)
    let mut s = CompilerSession::new(settings, project_root);

    let src = read_file(entry_module_path);
    let codegen_behaviour = match action {
        Link => ObjectOnly,
        _ => InMemoryAndObject,
    };
    let ctx = Context::new(entry_module_name, codegen_behaviour);

    if let Release = action {
        return s.build_release(&ctx);
    }

    let _ = s.compile_unit(&src, &ctx, Replace);

    match action {
        Run | Repl => {
            s.spawn_hot_inmem_codegen();
        },
        _ => ,
    }
    s.spawn_nice_object_codegen();

    if let Repl = action {
        s.spawn_file_watcher(move |s, file_path| {
            if let Some((module, src)) = s.read_module(file_path) {
                let ctx = Context::new(module, InMemoryAndObject);
                let _ = s.compile_unit(&src, &ctx, Replace);
            }
        });
    };

    match action {
        Repl => {
            loop {
                let src = read_line();
                // file watcher will have typechecked and enqueued for codegen by here
                s.hot_flush_in_mem_queue();
                if let Some(result) = match s.process_commands(&src) {
                    Nothing => None,
                    Final(result) => Some(result),
                    Compile(form) => Some(s.compile_unit(&form, &ctx, Additive)),   // what does compile unit do if there are errored files?
                } {
                    pretty_print_form(result);
                }
            }
            s.hot_flush_object_queue();
        },
        Run => {
            s.hot_flush_in_mem_queue(); // can't start until compiled
            s.trampoline(&ctx);
            // nice object codegen was running in background
            s.hot_flush_object_queue();
        },
        Link => {
            s.hot_flush_object_queue();
            s.link(&ctx)
        },
        Release => ,
    }
}

// ---------------------------------------------------------------------------
// CLI parsing
// ---------------------------------------------------------------------------

enum Mode {
    Repl,
    Run { path: String },
    Link { path: String },
}

fn parse_args(args: &[String]) -> (Mode, bool) {
    let mut no_color = false;
    let mut run_path: Option<String> = None;
    let mut link_path: Option<String> = None;
    let mut i = 1;

    while i < args.len() {
        match args[i].as_str() {
            "--no-color" => {
                no_color = true;
                i += 1;
            }
            "--run" => {
                if i + 1 < args.len() {
                    run_path = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    die("--run requires a file argument");
                }
            }
            "--link" => {
                if i + 1 < args.len() {
                    link_path = Some(args[i + 1].clone());
                    i += 2;
                } else {
                    die("--link requires a file argument");
                }
            }
            other => die(&format!("unexpected argument: {other}")),
        }
    }

    if run_path.is_some() && link_path.is_some() {
        die("--run and --link cannot be used together");
    }

    let mode = if let Some(path) = link_path {
        Mode::Link { path }
    } else if let Some(path) = run_path {
        Mode::Run { path }
    } else {
        Mode::Repl
    };

    (mode, no_color)
}

fn die(msg: &str) -> ! {
    eprintln!("error: {msg}");
    eprintln!("usage: cranelisp [--run <file.cl>] [--link <file.cl>] [--no-color]");
    process::exit(1);
}

// ---------------------------------------------------------------------------
// Shared setup
// ---------------------------------------------------------------------------

fn project_root() -> PathBuf {
    std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."))
}

fn require_file(path: &str) -> Result<PathBuf, String> {
    let p = Path::new(path);
    if !p.exists() {
        return Err(format!("file not found: {path}"));
    }
    Ok(p.to_path_buf())
}

fn print_warnings(warnings: &[cranelisp_types::Warning]) {
    for w in warnings {
        eprintln!("warning: {}", w.message);
    }
}
