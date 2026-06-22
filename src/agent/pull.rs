// agent/pull.rs — pull-as-visible-commands (design/int/agent.md §4, the keystone).
//
// A pull is the agent issuing a REPL command on the user's behalf. The model's
// "tools" are EXACTLY a small read-only subset of REPL commands (§4.2): there is
// NO private tool registry — the pull surface IS `dispatch_command`. A tool-call
// is synthesized into a command STRING (e.g. `/source foo`), run through the
// SAME `process_commands` path a keystroke uses, rendered as-if-typed, and its
// result fed back to the model.
//
// Safety: the allowlist is the consent gate (§4.2). In read-only Advise mode the
// agent CANNOT synthesize a write — `synthesize_command` rejects any command not
// in the read-only set, rendering a refusal rather than running it. This is how
// "auto-approve reads only" (§7.4) is structurally enforced this wave: writes are
// unconstructable.

#![cfg(feature = "agent")]

use std::io::Write;

use crate::agent::types::{ToolCallRequest, ToolCallResult, ToolDef};
use crate::session_v4::{CommandResult, CompilerSession};

/// The read-only command allowlist (§4.2) — the ONLY tools the agent may emit.
/// Each entry is `(tool-name, leading-slash command, one-line description)`. The
/// `slash` is the actual command word `process_commands` dispatches; `name` is
/// what the model emits as a tool call. They are the same word here (no slash on
/// the model side). Writes / `/sh` / submit are deliberately ABSENT — they are
/// unconstructable in read-only Advise mode (the MVP consent boundary).
const ALLOWLIST: &[(&str, &str)] = &[
    ("source", "Show the source of a defined symbol: source <name>"),
    ("sexp", "Show the parsed s-expression of a symbol: sexp <name>"),
    ("info", "Show a symbol's type, kind, and related info: info <name>"),
    ("sig", "Show a symbol's type signature: sig <name>"),
    ("doc", "Show a symbol's (or module's) docstring: doc <name>"),
    ("type", "Show the inferred type of an expression: type <expr>"),
    ("imports", "List the current module's imports: imports"),
    ("exports", "List a module's exports: exports <module>"),
    ("list", "List symbols in scope: list"),
    ("refs", "List definitions whose body references a symbol: refs <name>"),
    (
        "tests-for",
        "List test functions referencing a symbol: tests-for <name>",
    ),
];

/// The tool definitions offered to the model in every request (§4.2, §6.1).
/// Built from the allowlist so the model is told exactly the read-only command
/// surface — and nothing else.
pub fn tool_defs() -> Vec<ToolDef> {
    ALLOWLIST
        .iter()
        .map(|(name, desc)| ToolDef {
            name: (*name).to_string(),
            description: (*desc).to_string(),
        })
        .collect()
}

/// Is `name` (a bare tool/command word) in the read-only allowlist?
fn is_allowed(name: &str) -> bool {
    ALLOWLIST.iter().any(|(n, _)| *n == name)
}

/// Synthesize a REPL command STRING from a model tool-call, enforcing the
/// read-only allowlist (§4.2). Returns:
///   - `Ok(cmd_string)` — an allowed command, e.g. `"/source foo"`.
///   - `Err(refusal)` — a non-read command: a refusal notice (never a command).
///
/// A command not in the allowlist (a write, `/sh`, a `(defn …)` submission, or
/// any unknown name) is REFUSED at synthesis — the agent's capability surface is
/// the allowlist, so a write is structurally unconstructable (the consent gate).
pub fn synthesize_command(call: &ToolCallRequest) -> Result<String, String> {
    let name = call.name.trim().trim_start_matches('/');
    if !is_allowed(name) {
        return Err(format!(
            "agent attempted a non-read command '{}' — refused (read-only Advise mode)",
            call.name
        ));
    }
    let arg = call.argument.trim();
    if arg.is_empty() {
        Ok(format!("/{name}"))
    } else {
        Ok(format!("/{name} {arg}"))
    }
}

impl CompilerSession {
    /// Run a single model tool-call as a visible REPL command (§4.1).
    ///
    /// Synthesizes the command (allowlist-gated), runs it through the SAME
    /// `process_commands` path a keystroke uses, renders it as-if-typed to
    /// `stdout`, and returns the `ToolCallResult` to feed back to the model. A
    /// refused (non-read) command renders the refusal and feeds it back as the
    /// result — nothing is executed.
    pub(crate) fn run_pull(
        &mut self,
        call: &ToolCallRequest,
        stdout: &mut impl Write,
    ) -> ToolCallResult {
        match synthesize_command(call) {
            Err(refusal) => {
                // Render the refusal in normal REPL style (it is deterministic
                // output, not agent prose — §3.5). Fed back so the model sees it
                // was denied.
                let _ = writeln!(stdout, "{refusal}");
                ToolCallResult {
                    id: call.id.clone(),
                    command: format!("(refused: {})", call.name),
                    output: refusal,
                }
            }
            Ok(cmd) => {
                // Echo the command as if the user typed it (§4.4, §3.5 — agent
                // commands render in NORMAL REPL style, only prose is framed).
                let _ = writeln!(stdout, "{cmd}");
                // Run through the SAME path a keystroke uses. Read-only commands
                // return `Final(text)` (or `Nothing`); a read can never reach the
                // `Compile` arm (the allowlist excludes eval/write).
                let result = self.process_commands(&cmd, stdout);
                let output = match result {
                    CommandResult::Final(text) => {
                        // Render the result so it appears in the transcript, then
                        // feed it back to the model.
                        let _ = writeln!(stdout, "{text}");
                        text
                    }
                    CommandResult::Nothing => String::new(),
                    // A read-only command cannot produce these. Guard defensively
                    // so a future allowlist mistake fails closed (no eval).
                    CommandResult::Compile(_) | CommandResult::Quit => {
                        let msg = "(command produced no readable result)".to_string();
                        let _ = writeln!(stdout, "{msg}");
                        msg
                    }
                };
                ToolCallResult {
                    id: call.id.clone(),
                    command: cmd,
                    output,
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn call(name: &str, arg: &str) -> ToolCallRequest {
        ToolCallRequest {
            id: "c1".to_string(),
            name: name.to_string(),
            argument: arg.to_string(),
        }
    }

    // A read command synthesizes to a slash command string.
    #[test]
    fn read_command_synthesizes() {
        assert_eq!(synthesize_command(&call("source", "foo")).unwrap(), "/source foo");
        assert_eq!(synthesize_command(&call("list", "")).unwrap(), "/list");
        // A leading slash on the model side is tolerated.
        assert_eq!(synthesize_command(&call("/info", "bar")).unwrap(), "/info bar");
    }

    // A write / non-read command is refused at synthesis — unconstructable.
    #[test]
    fn write_command_refused() {
        assert!(synthesize_command(&call("sh", "rm -rf /")).is_err());
        assert!(synthesize_command(&call("submit", "(defn evil [] 0)")).is_err());
        assert!(synthesize_command(&call("def", "x 1")).is_err());
        // An unknown tool is also refused (fail closed).
        assert!(synthesize_command(&call("frobnicate", "x")).is_err());
    }

    // The tool-def set is exactly the allowlist (no writes leak in).
    #[test]
    fn tool_defs_are_read_only() {
        let defs = tool_defs();
        assert!(defs.iter().any(|d| d.name == "source"));
        assert!(!defs.iter().any(|d| d.name == "sh"));
        assert!(!defs.iter().any(|d| d.name == "submit"));
        assert_eq!(defs.len(), ALLOWLIST.len());
    }
}
