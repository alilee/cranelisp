> [REPL specification index](index.md)

## 13. Shell Escape [R4 S52]

The REPL supports a `/sh` slash command for running operating system commands without leaving the REPL session. This is useful for checking file contents, running external tools, or verifying output during iterative development.

### 13.1 Syntax [R4 S52]

The shell escape command is `/sh <command>`:

```
user> /sh ls -la
```

`/sh` follows the same slash-command convention as all other REPL commands (§3). Everything after `/sh` and optional whitespace is the shell command string.

### 13.2 Execution [Tested tests/repl_shell::shell_escape_basic_echo_command_runs]

The command string (everything after `/sh` and optional whitespace) MUST be passed to the system shell for execution. On Unix-like systems, this means invoking `/bin/sh -c "<command>"`. The REPL MUST NOT attempt to parse or interpret the command itself.

The command runs synchronously — the REPL blocks until the command completes. The REPL prompt is not displayed until the command finishes.

### 13.3 Output Handling [Tested tests/repl_shell::shell_escape_quoted_args_pass_through_to_stdout]

The command's stdout and stderr MUST be passed through directly to the terminal. The REPL does NOT capture, buffer, or reformat the output. The user sees exactly what the command produces, interleaved as the OS delivers it.

```
user> /sh echo "hello from shell"
hello from shell
0+0ms; user>
```

### 13.4 Exit Code Display [Tested+Neg tests/repl_shell::shell_escape_nonzero_exit_code_is_displayed]

If the command exits with a non-zero status, the REPL MUST display the exit code after the command output:

```
user> /sh false
exit status: 1
0+0ms; user>
```

If the command exits with status 0, no exit code is displayed — silence means success.

If the command is terminated by a signal (e.g., SIGKILL), the REPL SHOULD display the signal information:

```
user> /sh kill -9 $$
killed by signal: 9
0+0ms; user>
```

### 13.5 No REPL State Interaction [Tested+Neg tests/repl_shell::shell_escape_does_not_disturb_repl_state]

Shell escape is a pure passthrough. The command MUST NOT affect REPL state in any way:
- No variables, definitions, or imports are modified.
- The current module is unchanged.
- The typechecker, code cache, and compilation state are untouched.
- Environment variables set by the command do NOT propagate back to the REPL process (the command runs in a child process).

### 13.6 Edge Cases [Tested+Neg tests/repl_shell::shell_escape_neg_empty_command_does_not_error_or_crash]

**No arguments:** `/sh` with no command (or only whitespace) MUST print a usage hint: `Usage: /sh <command>`. [R4 S52]

```
user> /sh
Usage: /sh <command>
0+0ms; user>
```

**Command not found:** If the shell cannot find the command, the shell's own error message is passed through (since stdout/stderr are not captured). The exit code is displayed per §13.4.

```
user> /sh nonexistent-command
/bin/sh: nonexistent-command: command not found
exit status: 127
0+0ms; user>
```

**Multi-line:** Shell escape does NOT support continuation lines. Each `/sh` invocation is a self-contained command. For multi-statement commands, use shell syntax (e.g., `/sh echo a && echo b`).

**Timing:** The prompt after a shell escape MUST show `0+0ms` — shell commands are not Cranelisp evaluations and do not contribute to compile/eval timing.

### 13.7 `/help` Integration [Tested tests/repl_shell::shell_escape_listed_in_help_output]

`/sh` MUST appear in `/help` output as:

```
  /sh <cmd>       Run a shell command
```
