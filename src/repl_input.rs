//! REPL input abstraction — one interface, two implementations
//! (`repl/spec.md` §10.8; FIXMEs 0544 + 0551, Sprint 106).
//!
//! The REPL read loop threads a single [`ReplInput`] with a TTY impl and a
//! non-TTY impl, gated on [`IsTerminal`] for **stdin**:
//!
//! - **TTY** ([`ReplInput::Tty`]) — a `rustyline` editor: up/down history recall,
//!   inline editing (default Emacs bindings), and per-project history persistence
//!   to `<project_root>/.cranelisp_history` (loaded at start, saved on exit,
//!   bounded at [`HISTORY_CAP`]). Graceful-degrade: an unreadable/unwritable
//!   history file is a non-fatal warning, and a failed editor construction falls
//!   back to the non-TTY reader (no line editing, but the REPL still runs).
//!
//! - **Non-TTY** ([`ReplInput::Piped`]) — piped/redirected stdin (the e2e harness
//!   and scripted input). `rustyline` is **never instantiated**; the output stays
//!   **byte-for-byte identical** to pre-S106 (the prompt is written verbatim, then
//!   a line is read). The reader reads **fd 0 directly, one byte at a time up to
//!   the newline** — it does NOT hold a read-ahead buffer. This is load-bearing
//!   for FIXME 0551: the poll-shape `read-line` platform leaf shares fd 0 with the
//!   REPL host, and a read-ahead buffer (`stdin.lock().lines()`, an 8 KiB
//!   `BufReader`) would swallow the line a subsequent `read-line` turn should
//!   consume, leaking it back to the REPL reader as an undefined-variable error.
//!   Reading exactly up to the delimiter leaves the remainder on the fd for
//!   whichever consumer reads next, and line-splitting matches `BufRead::lines`
//!   byte-for-byte (including preserving a `\r` on an unterminated final line).
//!   `WouldBlock`/`EINTR` are **retried, never treated as EOF** (FIXME 0551 (B),
//!   the host half — the old `Err(_) => break` conflated a transient error with
//!   genuine EOF and ended the session).
//!
//! The **agent write-consent line read** (§15.2 write gate) goes through the SAME
//! abstraction ([`ReplInput::read_consent_line`]) — the same editor instance on
//! TTY, the same single fd-0 reader on non-TTY — so raw/cooked line discipline
//! never desyncs against a parallel reader.

use std::io::{self, IsTerminal, Write};
use std::path::{Path, PathBuf};

/// Bounded history length (`repl/spec.md` §10.8) — FIFO, oldest dropped first.
const HISTORY_CAP: usize = 1000;

/// The per-project history file name, resolved under `<project_root>`.
const HISTORY_FILE: &str = ".cranelisp_history";

/// The outcome of reading one input line.
pub enum ReadOutcome {
    /// A line of input (newline stripped).
    Line(String),
    /// End of input — no further lines (genuine EOF / editor closed).
    Eof,
}

/// Classification of a single `read(2)` result (FIXME 0551 (B)). Pure over
/// `(n, errno)` so the retryable-vs-EOF distinction is unit-testable.
#[derive(Debug, PartialEq, Eq)]
enum ReadKind {
    /// `n > 0` — one byte was read.
    Byte,
    /// `n == 0` — genuine end of input.
    Eof,
    /// `n < 0` with a transient errno (`EINTR`/`EAGAIN`/`EWOULDBLOCK`) — retry,
    /// NOT EOF.
    Retry,
    /// `n < 0` with a hard errno — terminal (treated EOF-shaped).
    Fatal,
}

fn classify_read(n: isize, errno: i32) -> ReadKind {
    if n > 0 {
        ReadKind::Byte
    } else if n == 0 {
        ReadKind::Eof
    } else if errno == libc::EINTR || errno == libc::EAGAIN || errno == libc::EWOULDBLOCK {
        ReadKind::Retry
    } else {
        ReadKind::Fatal
    }
}

/// Clear `O_NONBLOCK` on fd 0 (defensive host-side self-heal, FIXME 0551 (B)): if
/// a poll-shape `read-line` turn left fd 0 non-blocking (the platform (A) fix
/// restores it, but the host owns stdin robustly across IO turns too), the
/// blocking line read below would otherwise spin on `EWOULDBLOCK`.
fn clear_stdin_nonblocking() {
    // SAFETY: `F_GETFL`/`F_SETFL` on fd 0 are sound; idempotent.
    unsafe {
        let flags = libc::fcntl(0, libc::F_GETFL);
        if flags >= 0 && (flags & libc::O_NONBLOCK) != 0 {
            libc::fcntl(0, libc::F_SETFL, flags & !libc::O_NONBLOCK);
        }
    }
}

/// Read one line from `fd`, one byte at a time up to the newline — no read-ahead
/// past the delimiter (FIXME 0551, the shared-fd invariant). Returns
/// [`ReadOutcome::Eof`] only on a genuine terminal with no bytes accumulated.
///
/// Line-splitting matches `BufRead::lines` exactly: a trailing `\n` is dropped,
/// and a `\r` immediately before that `\n` is dropped too — but a `\r` at the end
/// of a **final, unterminated** line (no delimiting `\n`) is **preserved**, since
/// `.lines()` only strips the `\r` inside the `\n`-was-present branch. Byte-identity
/// with the pre-S106 reader on such an input is a §10.8 MUST.
fn read_raw_line_fd(fd: i32) -> ReadOutcome {
    let mut line: Vec<u8> = Vec::new();
    let mut saw_newline = false;
    loop {
        let mut b = [0u8; 1];
        // SAFETY: `fd` is valid; `b` is a valid 1-byte out-buffer.
        let n = unsafe { libc::read(fd, b.as_mut_ptr() as *mut libc::c_void, 1) };
        let errno = if n < 0 {
            // SAFETY: read errno after a failed `read`.
            unsafe { *libc::__errno_location() }
        } else {
            0
        };
        match classify_read(n, errno) {
            ReadKind::Byte => {
                if b[0] == b'\n' {
                    saw_newline = true;
                    break;
                }
                line.push(b[0]);
            }
            ReadKind::Retry => continue,
            ReadKind::Eof | ReadKind::Fatal => {
                if line.is_empty() {
                    return ReadOutcome::Eof;
                }
                break; // final unterminated line before the terminal
            }
        }
    }
    // Strip the trailing `\r` ONLY when a `\n` delimited the line — matching
    // `BufRead::lines`. An unterminated final `...\r` (or a lone `\r`) is kept.
    if saw_newline && line.last() == Some(&b'\r') {
        line.pop();
    }
    ReadOutcome::Line(String::from_utf8_lossy(&line).into_owned())
}

/// Read one line from fd 0 (the non-TTY REPL reader). `None` at EOF.
fn read_raw_line() -> Option<String> {
    clear_stdin_nonblocking();
    match read_raw_line_fd(0) {
        ReadOutcome::Line(l) => Some(l),
        ReadOutcome::Eof => None,
    }
}

/// The interactive-TTY editor (rustyline) plus its per-project history file.
pub struct TtyInput {
    editor: rustyline::DefaultEditor,
    history_path: Option<PathBuf>,
}

impl TtyInput {
    /// Construct the editor and load `<project_root>/.cranelisp_history`. Returns
    /// `None` if the editor cannot be constructed (caller falls back to non-TTY).
    fn new(project_root: &Path, stdout: &mut impl Write) -> Option<Self> {
        use rustyline::config::Configurer;
        let mut editor = rustyline::DefaultEditor::new().ok()?;
        // Bound history (FIFO); ignore the rare failure — a smaller default cap is
        // still fine.
        let _ = editor.set_max_history_size(HISTORY_CAP);

        let history_path = project_root.join(HISTORY_FILE);
        // Graceful-degrade: an unreadable history file is a non-fatal warning,
        // never a failed launch (`repl/spec.md` §10.8).
        if history_path.exists()
            && let Err(e) = editor.load_history(&history_path)
        {
            let _ = writeln!(
                stdout,
                "[history: could not load {}: {e}]",
                history_path.display()
            );
        }
        Some(TtyInput {
            editor,
            history_path: Some(history_path),
        })
    }

    fn readline(&mut self, prompt: &str) -> ReadOutcome {
        use rustyline::error::ReadlineError;
        match self.editor.readline(prompt) {
            Ok(line) => {
                if !line.trim().is_empty() {
                    // rustyline dedups consecutive identical entries itself.
                    let _ = self.editor.add_history_entry(line.as_str());
                }
                ReadOutcome::Line(line)
            }
            // Ctrl-C cancels the current line — a fresh empty line, not EOF.
            Err(ReadlineError::Interrupted) => ReadOutcome::Line(String::new()),
            // Ctrl-D (EOF) or any hard error ends input.
            Err(ReadlineError::Eof) => ReadOutcome::Eof,
            Err(_) => ReadOutcome::Eof,
        }
    }

    /// Consent-line read (§15.2) — the agent already printed the `[y/N]` prompt,
    /// so read with an empty prompt on the SAME editor; consent answers are not
    /// added to history. Only reached from the agent write gate (feature-gated).
    #[cfg_attr(not(feature = "agent"), allow(dead_code))]
    fn readline_consent(&mut self) -> Option<String> {
        self.editor.readline("").ok()
    }

    fn save_history(&mut self, stdout: &mut impl Write) {
        if let Some(path) = &self.history_path
            && let Err(e) = self.editor.save_history(path)
        {
            let _ = writeln!(stdout, "[history: could not save {}: {e}]", path.display());
        }
    }
}

/// The REPL input source — TTY (editor-backed) or non-TTY (raw fd-0 line reads).
pub enum ReplInput {
    Tty(Box<TtyInput>),
    Piped,
}

impl ReplInput {
    /// Select the impl from stdin's terminal-ness. A TTY whose editor fails to
    /// construct degrades to the non-TTY reader (the REPL still runs).
    pub fn new(project_root: &Path, stdout: &mut impl Write) -> Self {
        if io::stdin().is_terminal() {
            match TtyInput::new(project_root, stdout) {
                Some(t) => ReplInput::Tty(Box::new(t)),
                None => ReplInput::Piped,
            }
        } else {
            ReplInput::Piped
        }
    }

    /// Read one input line. On the non-TTY branch the `prompt` is written to
    /// `stdout` verbatim first (byte-identical to the pre-S106 `write_prompt`),
    /// then a line is read from fd 0; on the TTY branch the editor owns the prompt.
    pub fn read_line(&mut self, prompt: &str, stdout: &mut impl Write) -> ReadOutcome {
        match self {
            ReplInput::Tty(t) => t.readline(prompt),
            ReplInput::Piped => {
                let _ = write!(stdout, "{prompt}");
                let _ = stdout.flush();
                match read_raw_line() {
                    Some(l) => ReadOutcome::Line(l),
                    None => ReadOutcome::Eof,
                }
            }
        }
    }

    /// Read the agent write-consent line (§15.2) from the SAME input source. The
    /// `[y/N]` prompt was already printed by the agent, so no prompt is written
    /// here. `None` at EOF (the gate declines). Only reached from the agent write
    /// gate (feature-gated).
    #[cfg_attr(not(feature = "agent"), allow(dead_code))]
    pub fn read_consent_line(&mut self) -> Option<String> {
        match self {
            ReplInput::Tty(t) => t.readline_consent(),
            ReplInput::Piped => read_raw_line(),
        }
    }

    /// True on the interactive-TTY branch (a rustyline editor). The async
    /// `search index complete.` notice (§17.19.3, S108) is emitted ONLY here:
    /// a non-TTY (piped/redirected) session has no interactive line editor and
    /// no user watching a burn-down, and MUST stay byte-identical (§10.8) — an
    /// async completion line landing at a timing-dependent prompt boundary would
    /// perturb the scripted/piped-output contract. The `main.rs` poll site gates
    /// on this so the completion path is unreachable on the non-TTY branch.
    pub fn is_interactive(&self) -> bool {
        matches!(self, ReplInput::Tty(_))
    }

    /// Persist history on session end (TTY only; non-fatal on failure). Covers
    /// both `/quit` and Ctrl-D since both exit the read loop.
    pub fn save_history(&mut self, stdout: &mut impl Write) {
        if let ReplInput::Tty(t) = self {
            t.save_history(stdout);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pipe() -> (i32, i32) {
        let mut fds = [0i32; 2];
        assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0, "pipe() failed");
        (fds[0], fds[1])
    }

    // spec: repl/spec.md §17.19.3 (S108, I-3) — the async `search index
    // complete.` notice is gated on `is_interactive()` at the `main.rs` poll
    // site so the completion path is UNREACHABLE on the non-TTY branch (the
    // byte-identical scripted/piped contract, §10.8, must not be perturbed by a
    // timing-dependent async line). This pins the gate deterministically: the
    // non-TTY (`Piped`) branch is never interactive, so the poll short-circuits
    // before `take_search_index_completion_notice` can print.
    #[test]
    fn piped_input_is_not_interactive_so_completion_notice_is_gated_off() {
        assert!(
            !ReplInput::Piped.is_interactive(),
            "non-TTY session must never emit the async completion notice (§10.8)"
        );
    }

    // FIXME 0551 (B), host half: a would-block / EINTR read is a RETRY, not EOF.
    // The old `Err(_) => break` conflated the two and ended the session; this pins
    // the distinction at the classification seam.
    #[test]
    fn classify_read_distinguishes_retryable_from_eof() {
        assert_eq!(classify_read(1, 0), ReadKind::Byte);
        assert_eq!(classify_read(0, 0), ReadKind::Eof);
        assert_eq!(classify_read(-1, libc::EAGAIN), ReadKind::Retry);
        assert_eq!(classify_read(-1, libc::EWOULDBLOCK), ReadKind::Retry);
        assert_eq!(classify_read(-1, libc::EINTR), ReadKind::Retry);
        assert_eq!(classify_read(-1, libc::EIO), ReadKind::Fatal);
    }

    // The non-TTY reader parses lines byte-wise: strips `\r\n` on a `\n`-delimited
    // line, returns the final unterminated line before EOF, then reports EOF
    // distinctly.
    #[test]
    fn read_raw_line_fd_parses_lines_strips_cr_and_reports_eof() {
        let (r, w) = pipe();
        let data = b"foo\r\nbar";
        assert_eq!(
            unsafe { libc::write(w, data.as_ptr() as *const libc::c_void, data.len()) },
            data.len() as isize
        );
        unsafe { libc::close(w) }; // "bar" then EOF (no trailing newline)
        match read_raw_line_fd(r) {
            ReadOutcome::Line(s) => assert_eq!(s, "foo", "\\r before \\n stripped"),
            ReadOutcome::Eof => panic!("expected first line"),
        }
        match read_raw_line_fd(r) {
            ReadOutcome::Line(s) => assert_eq!(s, "bar", "final unterminated line returned"),
            ReadOutcome::Eof => panic!("expected final line"),
        }
        assert!(matches!(read_raw_line_fd(r), ReadOutcome::Eof));
        unsafe { libc::close(r) };
    }

    // §10.8 byte-identity guard (review IMPORTANT-1): `BufRead::lines` strips a
    // trailing `\r` ONLY when a `\n` also delimited the line. A final,
    // unterminated line ending in `\r` MUST keep the `\r` — matching the pre-S106
    // `stdin.lock().lines()` reader (which yields `"foo\r"`, not `"foo"`).
    #[test]
    fn read_raw_line_fd_preserves_cr_on_unterminated_final_line() {
        let (r, w) = pipe();
        let data = b"foo\r"; // no trailing newline
        unsafe {
            libc::write(w, data.as_ptr() as *const libc::c_void, data.len());
            libc::close(w);
        }
        match read_raw_line_fd(r) {
            ReadOutcome::Line(s) => assert_eq!(s, "foo\r", "unterminated final line keeps CR"),
            ReadOutcome::Eof => panic!("expected line"),
        }
        unsafe { libc::close(r) };
    }

    // A lone `\r` at EOF (classic-Mac-style final line, no `\n`) is preserved as
    // `"\r"`, exactly as `.lines()` yields it.
    #[test]
    fn read_raw_line_fd_preserves_lone_cr_at_eof() {
        let (r, w) = pipe();
        let data = b"\r";
        unsafe {
            libc::write(w, data.as_ptr() as *const libc::c_void, data.len());
            libc::close(w);
        }
        match read_raw_line_fd(r) {
            ReadOutcome::Line(s) => assert_eq!(s, "\r", "lone CR at EOF preserved"),
            ReadOutcome::Eof => panic!("expected line"),
        }
        unsafe { libc::close(r) };
    }

    // Shared-fd invariant (FIXME 0551): the reader consumes exactly one line and
    // leaves the remainder on the fd for the next consumer — it does NOT read
    // ahead (which is what let the platform `read-line` leak the next line).
    #[test]
    fn read_raw_line_fd_does_not_read_ahead_past_the_line() {
        let (r, w) = pipe();
        let data = b"first\nsecond\n";
        unsafe {
            libc::write(w, data.as_ptr() as *const libc::c_void, data.len());
        }
        match read_raw_line_fd(r) {
            ReadOutcome::Line(s) => assert_eq!(s, "first"),
            ReadOutcome::Eof => panic!("expected first line"),
        }
        // `second` is still on the fd — not stolen into a private read-ahead buffer.
        let mut peek = [0u8; 6];
        let n = unsafe { libc::read(r, peek.as_mut_ptr() as *mut libc::c_void, 6) };
        assert_eq!(&peek[..n as usize], b"second");
        unsafe {
            libc::close(r);
            libc::close(w);
        }
    }
}
