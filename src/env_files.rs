//! The startup supply of the process environment from environment files
//! (`repl/spec/00-cli-invocation.md` §0.8; `design/int/environment.md` §2).
//!
//! [`supply`] runs once, before any thread starts and before anything reads
//! the environment. It copies each admitted key that the process environment
//! does not define from the project `.env`, else from the user file. After it,
//! every reader keeps reading `std::env`.
//!
//! Everything except the final `set_var` loop is a pure function over strings
//! and an injected environment view, so the module tests set no process
//! environment. The loop runs only over a [`settable`] plan, which has already
//! refused every value the process environment cannot hold.

use std::collections::BTreeMap;
use std::ffi::OsString;
use std::fmt;
use std::path::{Path, PathBuf};

/// Disables both files when set to exactly `1`.
const NO_ENV_VAR: &str = "CRANELISP_NO_ENV";
/// Replaces the project file's location.
const ENV_FILE_VAR: &str = "CRANELISP_ENV_FILE";
/// Replaces the user file's location.
const USER_ENV_FILE_VAR: &str = "CRANELISP_USER_ENV_FILE";
const LOADER_CONTROLS: [&str; 3] = [NO_ENV_VAR, ENV_FILE_VAR, USER_ENV_FILE_VAR];

const ADMITTED_PREFIX: &str = "CRANELISP_";
const ADMITTED_NAMES: [&str; 3] = ["NO_COLOR", "ANTHROPIC_API_KEY", "OLLAMA_API_BASE_URL"];

const PROJECT_FILE_NAME: &str = ".env";
/// The user file, relative to the configuration directory.
const USER_FILE_RELATIVE: &str = "cranelisp/env";

/// Why startup stops. The message names the file and, when the fault is on a
/// line, the line; it never contains a value (`design/int/environment.md` §2.7).
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct SupplyError {
    path: PathBuf,
    kind: SupplyErrorKind,
}

#[derive(Debug, PartialEq, Eq)]
enum SupplyErrorKind {
    Unreadable(String),
    Malformed(Malformed),
    /// The value chosen for `key` contains a NUL byte, which `set_var` would
    /// reject by panicking with the value in its message.
    Unrepresentable {
        line: usize,
        key: String,
    },
}

impl fmt::Display for SupplyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let path = self.path.display();
        match &self.kind {
            SupplyErrorKind::Unreadable(reason) => {
                write!(f, "cannot read environment file {path}: {reason}")
            }
            SupplyErrorKind::Malformed(m) => {
                write!(
                    f,
                    "{path}:{}: malformed environment file: {}",
                    m.line, m.reason
                )
            }
            SupplyErrorKind::Unrepresentable { line, key } => write!(
                f,
                "{path}:{line}: the value of {key} contains a NUL byte, \
                 which the process environment cannot hold"
            ),
        }
    }
}

/// A malformed line, located by its 1-based number.
#[derive(Debug, PartialEq, Eq)]
struct Malformed {
    line: usize,
    reason: MalformedReason,
}

#[derive(Debug, PartialEq, Eq)]
enum MalformedReason {
    NotAnAssignment,
    InvalidKey,
    UnterminatedQuote,
    TextAfterQuote,
}

impl fmt::Display for MalformedReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            MalformedReason::NotAnAssignment => "the line is not a KEY=VALUE assignment",
            MalformedReason::InvalidKey => {
                "the key must be ASCII letters, digits and `_`, not starting with a digit"
            }
            MalformedReason::UnterminatedQuote => "the quoted value is not terminated",
            MalformedReason::TextAfterQuote => "unexpected text after the quoted value",
        })
    }
}

/// One assignment, in file order, with the 1-based line it starts on.
#[derive(Debug, PartialEq, Eq)]
struct Entry {
    key: String,
    value: String,
    line: usize,
}

/// One loaded file: its assignments and where they came from.
#[derive(Debug, PartialEq, Eq)]
struct EnvFile {
    path: PathBuf,
    entries: Vec<Entry>,
}

/// The assignment resolution chose for a key, with its file.
#[derive(Debug, PartialEq, Eq)]
struct Chosen<'a> {
    path: &'a Path,
    entry: &'a Entry,
}

/// The files the supply reads; either may be absent.
#[derive(Debug, PartialEq, Eq)]
struct Locations {
    project: PathBuf,
    user: Option<PathBuf>,
}

/// Supply the process environment from the project file and the user file.
///
/// Must run before any other thread exists and before anything reads the
/// environment: it calls `set_var`, which is sound only then.
pub(crate) fn supply(project_root: &Path) -> Result<(), SupplyError> {
    let process = |key: &str| std::env::var_os(key);
    let Some(locations) = locate(&process, project_root) else {
        return Ok(());
    };
    let project = load(&locations.project)?;
    let user = locations.user.as_deref().map(load).transpose()?;
    let chosen = resolve(&process, &project, user.as_ref());
    for (key, value) in settable(&chosen)? {
        // SAFETY: `main` calls this before it starts any thread or reads the
        // environment (`design/int/environment.md` §2.1), so nothing reads or
        // writes the environment concurrently.
        unsafe { std::env::set_var(key, value) };
    }
    Ok(())
}

/// The admission predicate (`design/int/environment.md` §2.6).
fn is_admitted(key: &str) -> bool {
    (key.starts_with(ADMITTED_PREFIX) || ADMITTED_NAMES.contains(&key))
        && !LOADER_CONTROLS.contains(&key)
}

/// The value of `key` in `env`, treating an empty value as unset.
fn non_empty(env: &dyn Fn(&str) -> Option<OsString>, key: &str) -> Option<OsString> {
    env(key).filter(|v| !v.is_empty())
}

/// Where the files are, from the process environment only; `None` when the
/// supply is disabled.
fn locate(env: &dyn Fn(&str) -> Option<OsString>, project_root: &Path) -> Option<Locations> {
    if env(NO_ENV_VAR).is_some_and(|v| v == "1") {
        return None;
    }
    let project = non_empty(env, ENV_FILE_VAR)
        .map(PathBuf::from)
        .unwrap_or_else(|| project_root.join(PROJECT_FILE_NAME));
    let user = non_empty(env, USER_ENV_FILE_VAR)
        .map(PathBuf::from)
        .or_else(|| {
            non_empty(env, "XDG_CONFIG_HOME").map(|dir| PathBuf::from(dir).join(USER_FILE_RELATIVE))
        })
        .or_else(|| {
            non_empty(env, "HOME")
                .map(|home| PathBuf::from(home).join(".config").join(USER_FILE_RELATIVE))
        });
    Some(Locations { project, user })
}

/// Read and parse one file. A file that does not exist contributes nothing.
fn load(path: &Path) -> Result<EnvFile, SupplyError> {
    let unreadable = |reason: String| SupplyError {
        path: path.to_path_buf(),
        kind: SupplyErrorKind::Unreadable(reason),
    };
    let file = |entries| EnvFile {
        path: path.to_path_buf(),
        entries,
    };
    let bytes = match std::fs::read(path) {
        Ok(bytes) => bytes,
        Err(e)
            if matches!(
                e.kind(),
                std::io::ErrorKind::NotFound | std::io::ErrorKind::NotADirectory
            ) =>
        {
            return Ok(file(Vec::new()));
        }
        Err(e) => return Err(unreadable(e.to_string())),
    };
    let text = String::from_utf8(bytes).map_err(|_| unreadable("it is not UTF-8".to_string()))?;
    parse(&text).map(file).map_err(|m| SupplyError {
        path: path.to_path_buf(),
        kind: SupplyErrorKind::Malformed(m),
    })
}

/// The assignments to apply: for each admitted key the process environment
/// does not define, the project file's, else the user file's. Within one file
/// the last occurrence wins.
fn resolve<'a>(
    env: &dyn Fn(&str) -> Option<OsString>,
    project: &'a EnvFile,
    user: Option<&'a EnvFile>,
) -> BTreeMap<&'a str, Chosen<'a>> {
    let mut chosen = BTreeMap::new();
    // The user file first, so a project value overwrites it; each file's later
    // lines overwrite its earlier ones.
    for file in user.into_iter().chain([project]) {
        for entry in &file.entries {
            if is_admitted(&entry.key) && env(&entry.key).is_none() {
                let path = file.path.as_path();
                chosen.insert(entry.key.as_str(), Chosen { path, entry });
            }
        }
    }
    chosen
}

/// The `(key, value)` pairs to set, or the first chosen value the process
/// environment cannot hold, located by its file and line.
fn settable<'a>(
    chosen: &BTreeMap<&'a str, Chosen<'a>>,
) -> Result<Vec<(&'a str, &'a str)>, SupplyError> {
    chosen
        .iter()
        .map(|(&key, chosen)| {
            let value = chosen.entry.value.as_str();
            if value.contains('\0') {
                return Err(SupplyError {
                    path: chosen.path.to_path_buf(),
                    kind: SupplyErrorKind::Unrepresentable {
                        line: chosen.entry.line,
                        key: key.to_string(),
                    },
                });
            }
            Ok((key, value))
        })
        .collect()
}

/// Parse the dotenv core (`repl/spec/00-cli-invocation.md` §0.8).
fn parse(text: &str) -> Result<Vec<Entry>, Malformed> {
    let lines: Vec<&str> = text
        .split('\n')
        .map(|l| l.strip_suffix('\r').unwrap_or(l))
        .collect();
    let mut entries = Vec::new();
    let mut index = 0;
    while index < lines.len() {
        let line_number = index + 1;
        let line = lines[index].trim_start();
        index += 1;
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let malformed = |reason| Malformed {
            line: line_number,
            reason,
        };
        let line = strip_export(line);
        let (key, raw) = line
            .split_once('=')
            .ok_or(malformed(MalformedReason::NotAnAssignment))?;
        let key = key.trim();
        if !is_valid_key(key) {
            return Err(malformed(MalformedReason::InvalidKey));
        }
        let rest = raw.trim_start();
        let value = if let Some(quoted) = rest.strip_prefix('\'') {
            let (value, after) = quoted
                .split_once('\'')
                .ok_or(malformed(MalformedReason::UnterminatedQuote))?;
            require_blank_or_comment(after).map_err(malformed)?;
            value.to_string()
        } else if let Some(quoted) = rest.strip_prefix('"') {
            let (value, after) = double_quoted(quoted, &lines, &mut index)
                .ok_or(malformed(MalformedReason::UnterminatedQuote))?;
            require_blank_or_comment(&after).map_err(malformed)?;
            value
        } else {
            // Untrimmed, so a ` #` straight after `=` still begins a comment.
            unquoted(raw)
        };
        entries.push(Entry {
            key: key.to_string(),
            value,
            line: line_number,
        });
    }
    Ok(entries)
}

fn strip_export(line: &str) -> &str {
    match line.strip_prefix("export") {
        Some(rest) if rest.starts_with([' ', '\t']) => rest.trim_start(),
        _ => line,
    }
}

fn is_valid_key(key: &str) -> bool {
    let mut chars = key.chars();
    chars
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// An unquoted value: to the end of the line, cut at a ` #` comment, with
/// surrounding whitespace removed.
fn unquoted(rest: &str) -> String {
    let mut previous_blank = false;
    for (i, c) in rest.char_indices() {
        if c == '#' && previous_blank {
            return rest[..i].trim().to_string();
        }
        previous_blank = c.is_whitespace();
    }
    rest.trim().to_string()
}

fn require_blank_or_comment(after: &str) -> Result<(), MalformedReason> {
    let after = after.trim_start();
    if after.is_empty() || after.starts_with('#') {
        Ok(())
    } else {
        Err(MalformedReason::TextAfterQuote)
    }
}

/// A double-quoted value starting after its opening quote, continuing onto
/// later lines (advancing `next_line`) until the closing quote. Returns the
/// value and the text after the closing quote; `None` when unterminated.
fn double_quoted(first: &str, lines: &[&str], next_line: &mut usize) -> Option<(String, String)> {
    let mut value = String::new();
    let mut current = first;
    loop {
        let mut chars = current.char_indices();
        while let Some((i, c)) = chars.next() {
            match c {
                '"' => return Some((value, current[i + 1..].to_string())),
                '\\' => match chars.next() {
                    Some((_, 'n')) => value.push('\n'),
                    Some((_, '"')) => value.push('"'),
                    Some((_, '\\')) => value.push('\\'),
                    Some((_, other)) => {
                        value.push('\\');
                        value.push(other);
                    }
                    None => value.push('\\'),
                },
                other => value.push(other),
            }
        }
        current = lines.get(*next_line)?;
        *next_line += 1;
        value.push('\n');
    }
}

#[cfg(test)]
mod tests;
