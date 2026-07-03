// cranelisp main: pipeline-v4.md §2.2 structure.
//
// Three modes: Run (--run), Link (--link), Repl (default).
// One CompilerSession, one code path. Workers are persistent.
//
// Embedded agent (REPL-only). The optional LLM advisor is compiled in ONLY
// with the `agent` Cargo feature, which is off by default — a default
// `cargo build` has no agent at all (`cargo build --features agent` to
// include it). It is configured entirely through the ENVIRONMENT, never
// `Cranelisp.toml`: `CRANELISP_AGENT_PROVIDER` selects the backend
// (`anthropic` or `ollama`), `CRANELISP_AGENT_MODEL` the model-id,
// `ANTHROPIC_API_KEY` (or `CRANELISP_AGENT_KEY`) the Anthropic key, and
// `OLLAMA_API_BASE_URL` the Ollama endpoint (local, no key — the offline
// path). With the feature compiled in but no provider configured/reachable,
// the agent stays dormant and `/ask` renders a notice. The `--agent` /
// `--no-agent` flags are the runtime half of the opt-in (off by default,
// `--no-agent` wins on conflict) and are accepted no-ops in a feature-off
// build. See `repl/spec.md §17.10` for the full normative enable+config scheme.

// Sprint 99 Wave 0.2 — thread-caching global allocator (parallelism-perf
// measurement pre-wave). Feature-gated + OFF by default: with the feature
// absent this entire item does not exist, NO allocator static is emitted, and
// the default system allocator is used — byte-identical to a build without this
// change (arch ruling 4 + R2, `sprints/SPRINT.md` Wave 0). `#[global_allocator]`
// MUST bind at the binary root, which is this crate (`[[bin]] cranelisp`,
// path = "src/main.rs"); the `--run` JIT path the Wave-0.3 harness measures
// executes entirely in-process here. (`cranelisp-exe-bundle` is a `staticlib`
// library crate, not a binary root, so it is intentionally NOT touched.)
//
// The harness builds this variant with:
//     cargo build --release --features thread-caching-alloc
// or runs it directly with:
//     cargo run --release --features thread-caching-alloc -- --run <fixture>
#[cfg(feature = "thread-caching-alloc")]
#[global_allocator]
static GLOBAL_ALLOC: mimalloc::MiMalloc = mimalloc::MiMalloc;

use std::path::{Path, PathBuf};
use std::process;
use std::time::Instant;

use cranelisp_types::{ErrorLocation, CodegenBehaviour, CranelispError, Span};

use cranelisp::observability;
use cranelisp::session_v4::{CommandResult, CompilerSession, RunMode, SessionSettings};
use cranelisp::{got_trace, io_trace};

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

    /// The session's run-mode (D1 ruling §4). This is the ONLY legitimate place
    /// `Action` becomes `RunMode`; it is threaded onto `SharedState` as the
    /// explicit REPL-vs-batch signal (introspection gating + layout-hash gate),
    /// replacing the former `introspection.is_some()` proxy.
    fn run_mode(&self) -> RunMode {
        match self {
            Action::Run => RunMode::Run,
            Action::Link => RunMode::Link,
            Action::Repl => RunMode::Repl,
        }
    }
}

// ---------------------------------------------------------------------------
// Main (pipeline-v4.md §2.2)
// ---------------------------------------------------------------------------

fn main() {
    // Observability — flush scheduler + IO traces on normal exit AND panic.
    // Guards fire on `main()` return (Drop); panic hook fires on unwind.
    // NOTE: `std::process::exit` below bypasses Drop — the matching
    // `flush_traces()` call is invoked explicitly before every such call
    // site (Run-mode exit-code escape + early-error paths). See
    // `design/int/observability.md §7.1` for the wiring rationale.
    io_trace::install_panic_hook();
    got_trace::install_panic_hook();
    observability::install_panic_hook();
    // Wire the typecheck-crate `SymbolTableEnsure` trace hook through
    // to this crate's scheduler-trace sink. Cross-crate install: the
    // typecheck crate cannot depend on this binary, so the forwarding
    // function pointer is installed here. See
    // `design/int/heisenbug-race-closure.md §3d''` (Sprint 61 Wave 3,
    // H6 race-closure fix).
    observability::install_symbol_table_ensure_hook_to_scheduler_trace();
    // Register observability observers per FIXMEs 0099 + 0103 (Decision 40).
    // No-op when their respective env vars are unset; the producer-side
    // emit hot path is a relaxed-load null check.
    io_trace::install_if_enabled();
    got_trace::install_if_enabled();
    // S101: arm the intrinsics `[RC_STATS]` at-exit printer when the env var
    // is set. The printer registers lazily on the FIRST tallied RC/alloc op
    // (`cranelisp-intrinsics/src/rc.rs::ensure_stats_atexit`), so a session
    // whose heap traffic is all static literals would exit silently and a
    // stats-reading harness (e.g. the L-R1(f) bounded-leak fence) could not
    // distinguish "no ops" from "died before exit". Poking the exported
    // tally hook once guarantees the line is emitted whenever the env var is
    // on; the single +1 on `rc_inc` is uniform across sessions and the
    // alloc/dealloc fields the fences read are untouched.
    if std::env::var_os("CRANELISP_RC_STATS").is_some() {
        unsafe extern "C" {
            #[link_name = "runtime/rc_stat_inc"]
            fn cranelisp_arm_rc_stats() -> i64;
        }
        // SAFETY: `runtime/rc_stat_inc` is a zero-arg statically-linked
        // export from cranelisp-intrinsics; calling it only bumps an atomic
        // counter and registers the atexit printer.
        unsafe {
            cranelisp_arm_rc_stats();
        }
    }
    let _io_flush = io_trace::IoTraceFlushGuard::new();
    let _got_flush = got_trace::GotTraceFlushGuard::new();
    let _sched_flush = observability::SchedulerTraceFlushGuard::new();

    let (action, project_root, entry_module, settings, agent_enabled, auto_accept, is_rule3) =
        parse_args();
    cranelisp::style::init_color(settings.no_color);

    if let Err(e) = run(
        action,
        &project_root,
        &entry_module,
        settings,
        agent_enabled,
        auto_accept,
        is_rule3,
    ) {
        let entry_file = project_root.join(format!("{entry_module}.cl"));
        eprintln!("{}", format_error(&e, &entry_file));
        flush_traces();
        process::exit(1);
    }
}

/// Format a `CranelispError` with a `file:line:col` prefix derived from the
/// error's `ErrorLocation`. Per Decision 39 + 42 (FIXME 0104), the
/// integration-layer formatter is the consumer-side surface that turns
/// coordinates-as-data into user-visible source coordinates.
///
/// Strategy:
/// 1. If `location.file` is set, use it. Otherwise fall back to the entry
///    module's source file (the most common case for batch errors where
///    location.file gets dropped along error-construction chains).
/// 2. If `location.line_col` is set, use it. Otherwise compute line:col from
///    `location.span.start` by reading the source file (best-effort; if the
///    file can't be read, omit the line:col and emit just the file path).
/// 3. Fall back to the default `Display` impl when no file is available
///    (preserves the pre-Wave-3b error shape for non-file errors).
fn format_error(err: &CranelispError, entry_file: &Path) -> String {
    // `location()` now returns `&ErrorLocation` directly (every error carries
    // a location). The prior `Option` fallback is no longer reachable.
    let loc = err.location();
    // Prefer the location's own file; fall back to the entry file.
    let file: PathBuf = match &loc.file {
        Some(p) => p.clone(),
        None => entry_file.to_path_buf(),
    };
    // Line:col — prefer the location's own line_col; otherwise derive from
    // span by reading the file.
    let (line, col) = if let Some(lc) = &loc.line_col {
        (lc.start.line, lc.start.col)
    } else {
        derive_line_col(&file, loc.span.start as usize)
    };
    // Friendly filename: prefer file name only when its parent matches cwd.
    let display_file = match (std::env::current_dir().ok(), file.file_name()) {
        (Some(cwd), Some(fname)) if file.parent() == Some(&cwd) => {
            fname.to_string_lossy().into_owned()
        }
        _ => file.to_string_lossy().into_owned(),
    };
    format!("{display_file}:{line}:{col}: error: {err}")
}

/// Convert a byte offset within a source file into 1-based (line, column).
/// Returns `(1, 1)` when the file can't be read or the offset is past EOF
/// (best-effort fallback so the error surface always has coordinates).
fn derive_line_col(file: &Path, byte_offset: usize) -> (u32, u32) {
    let Ok(src) = std::fs::read_to_string(file) else {
        return (1, 1);
    };
    let mut line: u32 = 1;
    let mut col: u32 = 1;
    for (i, ch) in src.char_indices() {
        if i >= byte_offset {
            return (line, col);
        }
        if ch == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    // Offset past EOF — return last position.
    (line, col)
}

/// Explicitly drain all observability traces to stderr. Must be called
/// immediately before any `std::process::exit` site that would otherwise
/// bypass the RAII guards held in `main()`. Safe to call when the traces
/// are disabled — each `flush_to_stderr` short-circuits on the filter.
fn flush_traces() {
    observability::flush_to_stderr();
    io_trace::flush_to_stderr();
    got_trace::flush_to_stderr();
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
    agent_enabled: bool,
    auto_accept: bool,
    is_rule3: bool,
) -> Result<(), CranelispError> {
    use std::io::{self, BufRead, Write};

    // `agent_enabled` / `auto_accept` are consumed by the REPL arm's
    // `s.enable_agent` only under `#[cfg(feature="agent")]`; feature-off they are
    // accepted no-ops (the `--agent` / `--yes` flags are still recognised, so a
    // script written for an agent build runs unchanged).
    #[cfg(not(feature = "agent"))]
    let _ = (agent_enabled, auto_accept);

    // §2.2: CompilerSession::new(settings, project_root, entry_module_name).
    // Workers are spawned and parked on condvars immediately. S78 §1: the
    // entry module name (the CLI target, or `"user"` default) seeds the REPL
    // cursor / check-state / test-runner "home" — the entry module is ordinary,
    // `"user"` is only its default name.
    let mut s = CompilerSession::new(settings, project_root.to_path_buf(), entry_module_name);

    // §3.1: Register the entry module. Front-end work (resolve, parse,
    // extract declarations) then enqueue for typechecking. Workers wake
    // and do expand+typecheck+codegen.
    //
    // S102 CS-0489 (repl/spec.md §18.8): the startup outcome is CAUGHT, not
    // `?`-propagated — REPL mode degrades a broken backing file to a
    // form-by-form entry load and still reaches a prompt (the repair path);
    // `--run`/`--link` keep the exit-1 contract (the `startup?` re-raise in
    // their arms below).
    let startup = s.register_module(entry_module_name);

    match action {
        // §7: Run mode (spec §12.6).
        // main : IO _ is enforced upstream (a non-IO main is rejected before
        // this point), so what reaches here is always an IO result. The exit
        // code is the inner Int value when main is `IO Int`; any other inner
        // IO result yields exit code 0.
        Action::Run => {
            startup?;
            s.wait_inmem_complete()?;
            let (value, ty) = s.trampoline(entry_module_name)?;
            s.wait_object_complete()?;
            s.shutdown();
            let exit_code = if ty == cranelisp_types::Type::Int {
                value as i32
            } else {
                0
            };
            // Observability: drain traces before `process::exit` bypasses
            // the RAII guards held in `main()` (design/int/observability.md §7.1).
            flush_traces();
            process::exit(exit_code);
        }
        // §8: Link mode.
        Action::Link => {
            startup?;
            s.wait_object_complete()?;
            s.link_by_name(entry_module_name)?;
        }
        // §6: REPL mode.
        Action::Repl => {
            let stdin = io::stdin();
            let stdout = io::stdout();
            let mut stdout = stdout.lock();

            // Wait for entry module (prelude) to be ready. §18.8 restart
            // floor (S102 CS-0489): an entry-restore failure MUST NOT
            // prevent the REPL from starting — catch it and degrade to the
            // form-by-form entry load (green forms commit; failed forms are
            // retained + reported below, and the module enters the §14.4
            // error-blocked state with the definition-turn carve-out).
            let startup = match startup {
                Ok(()) => s.wait_inmem_complete().map_err(CranelispError::from),
                Err(e) => Err(e),
            };
            let degraded_report = match startup {
                Ok(()) => None,
                Err(_) => s.recover_startup_failure(entry_module_name),
            };

            // S78 §3 / B1: startup typecheck is done — the eval thread now
            // becomes the entry module's SOLE orchestrator. Transfer ownership
            // so the scheduler never requeues the entry onto the pool for a
            // concurrent re-typecheck while the eval thread drives it.
            s.mark_entry_eval_owned();

            // Initialize file watcher now that modules are loaded.
            s.init_watcher();

            // S91 Pillar 3: arm the importable-symbol burn-down EAGERLY at REPL
            // start-up (R17 — eager-from-REPL-startup). REPL-only by
            // construction: this is the SOLE arming point, so `--run`/`--link`/
            // `--release` never enumerate the worklist (batch-mode-inert, R9).
            // The nice workers drain it BEHIND object codegen (index warm-up in
            // the slack); a `/search` issued before the burn-down completes
            // serves partial results + an "indexing N modules…" note.
            s.arm_importable_index();

            // S88 W3: wire the embedded agent (the S1 `_agent_enabled` seam).
            // REPL-only; selects the runtime provider (anthropic / ollama / stub
            // by config) or stays dormant. Feature-off this call does not exist
            // and `agent_enabled` is an accepted no-op (the `--agent` flag is
            // still recognised so a script written for an agent build runs).
            #[cfg(feature = "agent")]
            s.enable_agent(agent_enabled, auto_accept);

            // S91 FIXME 0410: scaffold a default `Cranelisp.toml` when the REPL
            // is pointed at a §0.5 rule-3 project-root directory lacking one.
            // REPL-only (this arm) + rule-3-only (the `is_rule3` gate) + never
            // overwrite + graceful on a read-only dir — all enforced by
            // `scaffold_project_config`. A new file emits the §0.5.7
            // `[created Cranelisp.toml]` notice; an existing file is a silent
            // no-op. The scaffold is resolution-neutral (every key commented).
            // A newly-created file (Ok(true)) emits the §0.5.7 notice; an
            // existing file (Ok(false)) or a graceful write failure is a
            // silent no-op — never fatal, the REPL launch proceeds regardless.
            if is_rule3 && matches!(s.scaffold_project_config(), Ok(true)) {
                let _ = writeln!(stdout, "[created Cranelisp.toml]");
            }

            // §18.8/§5.1: the degraded-load report — one error line per
            // failed form, naming the broken symbol — prints before the
            // banner, so the first thing a locked-out user used to see (the
            // fatal load error) is now the same information followed by a
            // usable prompt.
            if let Some(report) = &degraded_report {
                let _ = writeln!(stdout, "{report}");
            }

            s.print_banner(&mut stdout);

            let mut buffer = String::new();
            let mut compile_ms: u64 = 0;
            let mut eval_ms: u64 = 0;
            s.write_prompt(&mut stdout, compile_ms, eval_ms);

            // Hold the stdin line iterator explicitly (not a `for`) so the agent
            // confirm-gate (§15.2 step 2) can pull the NEXT line of the SAME stdin
            // as its `y`/`n` consent answer — the synchronous prompt-read at the
            // REPL cadence. Feature-off this is byte-identical to a plain
            // line-loop (no agent path reads it).
            let mut lines = stdin.lock().lines();
            while let Some(line) = lines.next() {
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

                // §5.3 dispatch classifier (design/int/agent.md §2.4,
                // repl/spec.md §17.1). Feature-OFF this whole block is absent and
                // the `process_commands` path below is byte-identical to today —
                // the divergence is the `Agent` arm only, which fires solely on
                // input that today produces a parse-error diagnostic anyway.
                //
                // §15.2 — `/ask` is ALSO intercepted here (feature-on) so the
                // Build write gate has the consent line-reader (the next stdin
                // line). The reader is a `FnConsent` closure over `&mut lines`,
                // alive only for the agent call, dropped before the loop's next
                // `lines.next()`. Feature-off `/ask` still flows through
                // `process_commands` (the dispatch body prints "not built in").
                #[cfg(feature = "agent")]
                {
                    let ask_text: Option<String> = input
                        .strip_prefix("/ask")
                        .filter(|r| r.is_empty() || r.starts_with(char::is_whitespace))
                        .map(|r| r.trim().to_string());
                    // §5.3/§7.4 dormant fall-through (arch ruling e3f7d57): the
                    // `Classify::Agent` route DIVERTS only when the agent is ACTIVE
                    // (a provider is reachable). Dormant / `--agent` OFF ⇒ the input
                    // flows through `process_commands`/`eval` exactly as the
                    // feature-OFF build does (bare-unbound → `eval.rs` undefined-
                    // symbol introspection; non-paren parse-error → `format_error`).
                    // The dormant short-circuit inside `agent_turn` stays the guard
                    // for the explicit `/ask` door ONLY (`ask_text` is unconditional).
                    let agent_text: Option<String> = if s.agent_is_active() {
                        match s.classify_for_agent(&input) {
                            cranelisp::agent::Classify::Agent(text) => Some(text),
                            _ => None,
                        }
                    } else {
                        None
                    };
                    if let Some(text) = ask_text.or(agent_text) {
                        let mut consent = cranelisp::agent::types::FnConsent(|| {
                            lines.next().and_then(|r| r.ok())
                        });
                        s.agent_turn(&text, &mut stdout, &mut consent);
                        drop(consent);
                        s.sync_watcher();
                        for msg in s.poll_and_reload() {
                            let _ = writeln!(stdout, "{msg}");
                        }
                        s.write_prompt(&mut stdout, compile_ms, eval_ms);
                        continue;
                    }
                }

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
                                let mut text = s.format_eval_result(&result);
                                // S101 (repl/spec.md §18.3): the cascade
                                // report renders after the §1.3 confirmation.
                                if let Some(report) = s.take_cascade_report() {
                                    text.push('\n');
                                    text.push_str(&report);
                                }
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

            // EOF reached. If a form was still being accumulated (unbalanced
            // parens awaiting a continuation line that never came), it is an
            // incomplete submission — report the parser's diagnostic rather
            // than silently discarding it. A complete form at the prompt is
            // submitted/executed, so an incomplete form at EOF MUST error
            // (repl/spec.md §5.1 + spec/05-definitions.md §5.13.2; user ruling
            // 2026-06-09; FIXME 0142). Slash commands and whitespace/comment-
            // only buffers are not incomplete forms.
            let pending = buffer.trim();
            if !pending.is_empty()
                && !pending.starts_with('/')
                && !s.parens_balanced(&buffer)
            {
                match s.eval(&buffer) {
                    Err(e) => {
                        let _ = writeln!(stdout, "Error: {e}");
                    }
                    // The parser should reject an unbalanced form; if it
                    // somehow parses, surface any result for symmetry with the
                    // in-loop path.
                    Ok(Some(result)) => {
                        let mut text = s.format_eval_result(&result);
                        if let Some(report) = s.take_cascade_report() {
                            text.push('\n');
                            text.push_str(&report);
                        }
                        s.pretty_print(&text, &mut stdout);
                    }
                    Ok(None) => {}
                }
            }

            let _ = writeln!(stdout);
            // S101 R18: pin the final `.o`/`.meta` persist to the session's
            // FINAL table state (expression turns mutate the table without a
            // per-turn persist trigger), then drain it deterministically.
            s.flush_final_persist();
            s.wait_object_complete()?;
        }
    }

    s.shutdown();
    Ok(())
}

// ---------------------------------------------------------------------------
// Argument parsing
// ---------------------------------------------------------------------------

fn parse_args() -> (Action, PathBuf, String, SessionSettings, bool, bool, bool) {
    let args: Vec<String> = std::env::args().collect();
    let mut no_color = false;
    let mut no_cache = false;
    let mut priority_workers: Option<usize> = None;
    let mut nice_workers: Option<usize> = None;
    let mut action_run = false;
    let mut action_link = false;
    // §0.6.1 agent toggle. `Some(true)` = `--agent`, `Some(false)` = `--no-agent`,
    // `None` = default (off). When both flags are given, `--no-agent` wins (the
    // safe default — off), enforced after the parse loop. In Wave 2 this is an
    // accepted no-op in both builds; Wave 3 (agent feature) consumes it.
    let mut agent_on = false;
    let mut agent_off = false;
    // §0.6.2 `--yes` / `-y` autonomous-submit toggle (S89 §20.1). Accepted in
    // BOTH builds: a no-op on a default / non-agent build (sibling to `--agent`),
    // and threaded onto `AgentState.auto_accept` when the agent is active. The
    // `-y` SHORT form must be recognised as a FLAG here, NOT swallowed as the
    // REPL target (the `-y` false-green trap — it does not start with `--`).
    let mut yes = false;
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
            // §0.6.1: `--agent` / `--no-agent` are the runtime half of the
            // agent's opt-in-twice discipline. REPL-only. A binary built WITHOUT
            // the agent feature MUST accept them as recognised flags (so a script
            // written for an agent-enabled build does not break) and treat them as
            // no-ops — never "unknown flag". Off by default. The agent feature
            // build (Wave 3) wires these to the runtime agent toggle; in Wave 2
            // they are accepted no-ops in BOTH builds.
            "--agent" => {
                agent_on = true;
                i += 1;
            }
            "--no-agent" => {
                agent_off = true;
                i += 1;
            }
            // §0.6.2 `--yes` (long) / `-y` (short) — accepted-no-op discipline
            // identical to `--agent` (§20.1). The `-y` arm MUST live here, in the
            // recognised-flag set, NOT in the `_` target-capture arm below — else
            // `-y` (which does not start with `--`) is swallowed as the REPL
            // target and the session runs in a `-y>` context (the false-green
            // trap the B.5 short-flag test guards).
            "--yes" | "-y" => {
                yes = true;
                i += 1;
            }
            arg if arg.starts_with("--") => {
                eprintln!("error: unknown flag: {arg}");
                eprintln!(
                    "usage: cranelisp [target] [--run | --link] [--no-color] \
                     [--no-cache] [--priority-workers N] [--nice-workers N] \
                     [--agent | --no-agent] [--yes]"
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

    // §0.6.1: resolve the agent toggle. `--no-agent` wins when both are present;
    // default is off. The agent is a REPL-only, dev-session capability — it
    // never participates in `--run`/`--link`, so the resolved value is only
    // meaningful in REPL mode. The flags are accepted no-ops in a feature-off
    // build (so a script written for an agent build runs); the `agent` feature
    // build (S88 W3) threads `agent_enabled` into `s.enable_agent` (the runtime
    // half of opt-in-twice — §6.4). Returned to `run`.
    let agent_enabled = agent_on && !agent_off && matches!(action, Action::Repl);

    // §20.1: `--yes` is meaningful ONLY with an active agent (it auto-answers the
    // write-consent gate). Off by default; REPL-only (gated by `agent_enabled`,
    // already Action::Repl). On a default / non-agent build it is a parsed no-op
    // (this resolves to `false` and the consuming `enable_agent` is `#[cfg]`-gated).
    let auto_accept = yes && agent_enabled;

    // Resolve (project_root, entry_module) per spec §0.5.1. `is_rule3` flags
    // the directory-as-project launch (the §0.5.7 scaffold trigger).
    let (project_root, entry_module, is_rule3) = resolve_target(target.as_deref());

    let codegen_behaviour = action.codegen_behaviour();
    let run_mode = action.run_mode();

    let settings = SessionSettings {
        no_color,
        no_cache,
        codegen_behaviour,
        priority_workers: priority_workers.unwrap_or(1),
        nice_workers: nice_workers.unwrap_or(1),
        run_mode,
    };

    (action, project_root, entry_module, settings, agent_enabled, auto_accept, is_rule3)
}

/// Resolve a positional target to (project_root, entry_module) per spec §0.5.1.
///
/// Rules:
/// 1. No target → (cwd, "user")
/// 2. Target has `/` → (directory portion, final component)
/// 3. Target is an existing directory *and not a `.cl` file* → (target, "user")
/// 4. Bare name → (cwd, target)
///
/// The `.cl` extension is stripped if present. Project root is resolved to
/// an absolute path.
fn resolve_target(target: Option<&str>) -> (PathBuf, String, bool) {
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    resolve_target_from(target, &cwd)
}

/// Core of `resolve_target`, with the base directory passed explicitly so the
/// rules are unit-testable independent of the process cwd.
///
/// Rule 3 (directory-as-project) fires only when the target names a directory
/// AND there is no `<target>.cl` file beside it. Per spec §8.11.1 the project
/// root is the directory *containing the entry file*; a `.cl` file passed as
/// the target IS the entry, and a same-named directory is its submodule
/// directory (§8.2.5 child-directory resolution), not a project-root override.
/// Without this precedence, a project whose entry file declares `(mod child)`
/// — which creates a sibling `<entry>/` directory — would be misread as a
/// directory target and the compiler would hunt for a non-existent
/// `<entry>/user.cl` (FIXME 0121).
///
/// The third tuple element is `true` only when Rule 3 (directory-as-project)
/// fired — the §0.5.7 scaffold trigger. Rules 1/2/4 return `false` (the bare
/// no-target REPL and entry-`.cl` launches MUST NOT scaffold).
fn resolve_target_from(target: Option<&str>, cwd: &Path) -> (PathBuf, String, bool) {
    let target = match target {
        None => return (cwd.to_path_buf(), "user".to_string(), false),
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
        let project_root = make_absolute(dir, cwd);
        (project_root, module, false)
    } else if cwd.join(target).is_dir() && !cwd.join(format!("{target}.cl")).is_file() {
        // Rule 3: existing directory with no same-named entry file. This is the
        // §0.5.7 scaffold trigger (`is_rule3 = true`).
        let project_root = make_absolute(Path::new(target), cwd);
        (project_root, "user".to_string(), true)
    } else {
        // Rule 4: bare name (resolves to `{cwd}/{target}.cl`), which also
        // covers the case where both `{target}.cl` and `{target}/` exist —
        // the file is the entry, the directory holds its submodules.
        (cwd.to_path_buf(), target.to_string(), false)
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
            location: ErrorLocation::from_span_file(Span::SYNTHETIC, Some(path.to_path_buf())),
        });
    }
    std::fs::read_to_string(path).map_err(|e| CranelispError::ModuleError {
        message: format!("cannot read '{}': {}", path.display(), e),
        location: ErrorLocation::from_span_file(Span::SYNTHETIC, Some(path.to_path_buf())),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Spec §8.11.1: the project root is the directory *containing the entry
    /// file*. When the target names a `<name>.cl` file in cwd, that file is the
    /// entry (project root = cwd, module = name) — even if a `<name>/`
    /// directory also exists holding the file's submodules. This is the FIXME
    /// 0121 root: a `(mod child)` entry creates a sibling `<entry>/` directory,
    /// and Rule 3 must NOT mistake it for a directory-as-project target.
    #[test]
    fn entry_cl_file_wins_over_same_named_submodule_directory() {
        let tmp = tempfile::tempdir().unwrap();
        let cwd = tmp.path();
        std::fs::write(cwd.join("main.cl"), "(mod child)\n(defn main [] 0)").unwrap();
        std::fs::create_dir(cwd.join("main")).unwrap();
        std::fs::write(cwd.join("main/child.cl"), "(defn helper [] 1)").unwrap();

        // Both `main.cl` (with extension) and bare `main` must resolve to the
        // FILE as the entry, with project root = cwd.
        for target in ["main.cl", "main"] {
            let (root, module, is_rule3) = resolve_target_from(Some(target), cwd);
            assert_eq!(root, cwd, "target {target:?}: project root must be cwd");
            assert_eq!(module, "main", "target {target:?}: entry module must be 'main'");
            assert!(
                !is_rule3,
                "target {target:?}: an entry-`.cl` launch is NOT a rule-3 scaffold trigger"
            );
        }
    }

    /// Rule 3 still fires for a genuine directory target with no same-named
    /// `.cl` file beside it: `cranelisp myproj` → (myproj, "user").
    #[test]
    fn directory_target_without_entry_file_resolves_to_user() {
        let tmp = tempfile::tempdir().unwrap();
        let cwd = tmp.path();
        std::fs::create_dir(cwd.join("myproj")).unwrap();
        std::fs::write(cwd.join("myproj/user.cl"), "(defn main [] 0)").unwrap();

        let (root, module, is_rule3) = resolve_target_from(Some("myproj"), cwd);
        assert_eq!(root, cwd.join("myproj"));
        assert_eq!(module, "user");
        assert!(
            is_rule3,
            "a directory-as-project target IS the §0.5.7 scaffold trigger"
        );
    }

    /// Rule 1: no target → (cwd, "user"). NOT a scaffold trigger — the bare
    /// no-target REPL launch MUST NOT scaffold (§0.5.7 rule-1 MUST NOT).
    #[test]
    fn no_target_resolves_to_cwd_user() {
        let tmp = tempfile::tempdir().unwrap();
        let (root, module, is_rule3) = resolve_target_from(None, tmp.path());
        assert_eq!(root, tmp.path());
        assert_eq!(module, "user");
        assert!(!is_rule3, "the bare no-target launch is NOT a rule-3 trigger");
    }

    /// Rule 2: a target with a directory component splits into
    /// (directory, final-component). NOT a rule-3 scaffold trigger.
    #[test]
    fn target_with_directory_component_splits() {
        let tmp = tempfile::tempdir().unwrap();
        let cwd = tmp.path();
        let (root, module, is_rule3) = resolve_target_from(Some("examples/hello.cl"), cwd);
        assert_eq!(root, cwd.join("examples"));
        assert_eq!(module, "hello");
        assert!(!is_rule3, "a directory-component target is NOT a rule-3 trigger");
    }

    /// Rule 4: a bare name that matches neither a directory nor a file still
    /// resolves to (cwd, name) — the session reports the missing file later.
    /// NOT a rule-3 scaffold trigger.
    #[test]
    fn bare_name_resolves_to_cwd_module() {
        let tmp = tempfile::tempdir().unwrap();
        let cwd = tmp.path();
        let (root, module, is_rule3) = resolve_target_from(Some("nope"), cwd);
        assert_eq!(root, cwd);
        assert_eq!(module, "nope");
        assert!(!is_rule3, "a bare missing-name target is NOT a rule-3 trigger");
    }
}
