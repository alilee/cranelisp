# Sprint 49: Pipeline v4 Step 15 — Delete Legacy Code

**Status**: COMPLETE
**Ring**: — (structural / pipeline v4 migration)
**Goal**: Write a clean `run()` function matching pipeline-v4.md §2.2 target state. No ReplSession. No CompilationSession. One session struct, one main, one compilation path.

## Target State (from pipeline-v4.md §2.2)

```rust
fn run() -> Result<(), CranelispError> {
    let (action, entry_module_path, settings) = parse_args();
    let project_root = base_dir(&entry_module_path);
    let s = CompilerSession::new(settings, project_root);
    s.register_module(&entry_module_name);

    match action {
        Run => {
            s.scheduler.wait_inmem_complete()?;
            s.trampoline(&entry_module_name);
            s.scheduler.wait_object_complete()?;
        }
        Link => {
            s.scheduler.wait_object_complete()?;
            s.link(&entry_module_name);
        }
        Repl => {
            loop {
                let src = read_line();
                match s.process_commands(&src) {
                    Nothing => {}
                    Final(sexp) => pretty_print(sexp),
                    Compile(src) => match s.eval(&src) {
                        Ok(Some(sexp)) => pretty_print(sexp),
                        Ok(None) => {}
                        Err(e) => print_error(e),
                    },
                }
            }
        }
    }
    s.shutdown();
    Ok(())
}

fn main() {
    if let Err(e) = run() {
        eprintln!("error: {e}");
        process::exit(1);
    }
}
```

Key properties:
- **One `CompilerSession`** — no CompilationSession, no ReplSession
- **`eval()` and `process_commands()` are methods on CompilerSession**
- **Prelude is not special** — discovered lazily when user module imports it
- **REPL loop is in `run()`** — REPL-specific display/watcher/persistence is helper functions, not a wrapper struct
- **`run()` returns `Result`** — main handles the error

## Current Wave: Write clean run()

### Task

Write `run()` from scratch matching the target state. Put it behind `--v4` flag for coexistence with the old path. The old path stays untouched. `run()` must be completely clean — no references to CompilationSession, ReplSession, or any v3 types.

This means `CompilerSession` needs:
- `eval(&mut self, src: &str) -> Result<Option<EvalResult>, CranelispError>` — submit source to current REPL module via scheduler, return display result
- `process_commands(&self, input: &str) -> CommandResult` — slash commands + blank detection
- REPL-specific state that currently lives on ReplSession (type_defs for ADT display, file watcher, persistence, error_modules) either moves to CompilerSession or becomes local state in the REPL loop

### What stays on CompilerSession

- `eval()` — compilation core (already partially implemented as eval_one_form_v4)
- `process_commands()` — command dispatch
- `type_defs` / `type_modules` — needed for display formatting after eval
- File watcher state — optional, created in REPL mode
- Session persistence — save/restore user.cl

### What becomes free functions / loop-local

- Display formatting (`format_result`, `format_repl_display`) — already free functions
- Line reading, prompt formatting, banner — loop-local
- Shell escape handling — loop-local

## Prior attempts (lessons)

1. First agent: migrated ReplSession to wrap CompilerSession instead of CompilationSession. Wrong — preserved the wrong abstraction. Fixed 265 test failures but left 27 regressions and didn't touch main.
2. ReplSession is not in the v4 design. `eval()` and `process_commands()` belong on CompilerSession.
3. Agent ran `git stash` and lost work. NEVER allow destructive git commands in agents.
4. The defmacro REPL test (`test_repl_defmacro_and_use`) needs attention — v4 eval path's macro persistence across evals differs from old path. The previous agent added macro persistence code to worker.rs that should be reviewed.
5. Link mode must not use compile_unit — use register_module + nice workers.

## Outcome (verified 2026-04-11)

### Delivered
- One `CompilerSession`, one `run()` in `main.rs`, all modes (Run, Link, REPL)
- `eval()` and `process_commands()` are methods on `CompilerSession`
- `ReplSession` deleted from production (moved to `tests/helpers/mod.rs` as test adapter)
- `CompilationSession`, `MacroEnv`, `ModuleCodegenState`, `ModuleStructure` deleted
- `src/repl/` directory deleted (~5,400 lines)
- Session restructure phases A–F: TypecheckProduct, CodegenProduct, Code, Introspection on SharedState DashMaps
- Unified GOT literal pool (JIT and object paths share one codegen pattern)
- Introspection fully populated (source, sexp, expanded, ast, clif_ir, disasm, code_size), gated on `--repl`
- Nice workers spawned as persistent threads, `.o` production working
- `--link` mode fully implemented
- File watcher extracted to `src/watch.rs`, wired into REPL loop
- `--v4` CLI flag removed
- ~12k+ lines of legacy code deleted total

### Outstanding
- **Macro/prelude regression**: session restructure broke macro symbol availability. ~120 of 137 test failures trace to this. Was 54/54 stdlib at commit `17a9906`, now 24/54.
- **Dead code**: `ObjectWorkerState` in `src/session.rs` (35 lines, never used)

### Deferred
- Persistent priority workers (Step 11) — design improvement, scoped workers are correct
- FQTypeName migration — ~182 call sites, no functional impact
- BL range fix — only manifests on large codebases

### Findings
- `git stash` in agents destroys uncommitted work — never allow
- ReplSession was the wrong abstraction to preserve; `eval`/`process_commands` belong on CompilerSession
- Session restructure (GOT unification, DashMap migration) introduced a macro regression that wasn't caught until after multiple refactoring commits landed
