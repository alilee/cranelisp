//! Child-process cells for behaviour that ends the process.
//!
//! A parent test re-executes this test binary, selecting one child body by its
//! libtest name and naming it in [`CHILD_SELECTOR`]. Each child body is an
//! ordinary test that returns at once unless [`selected`] names it, so the
//! ordinary suite runs every body inertly. Children start from a cleared
//! environment plus the values the parent names.

use std::process::Command;

const CHILD_SELECTOR: &str = "INTRINSICS_TEST_CHILD";

/// Whether this process was started to run the child body `name`.
pub(crate) fn selected(name: &str) -> bool {
    std::env::var(CHILD_SELECTOR).as_deref() == Ok(name)
}

/// How a child ended.
pub(crate) struct Ending {
    pub(crate) code: Option<i32>,
    pub(crate) stdout: String,
    pub(crate) stderr: String,
}

impl Ending {
    /// The stderr lines that are language-panic reports.
    pub(crate) fn report_lines(&self) -> Vec<&str> {
        self.stderr
            .lines()
            .filter(|l| l.starts_with(crate::panic::PANIC_REPORT_PREFIX))
            .collect()
    }

    /// Assert the child ended by exactly one language panic reporting `message`.
    #[track_caller]
    pub(crate) fn assert_panicked_with(&self, message: &str) {
        assert_eq!(
            self.code,
            Some(crate::panic::PANIC_EXIT_STATUS),
            "the panic status, not a signal or success:\n{}",
            self.stderr
        );
        let expected = format!("{}{message}", crate::panic::PANIC_REPORT_PREFIX);
        assert_eq!(self.report_lines(), [expected.as_str()], "{}", self.stderr);
    }
}

/// `module_path!()` of the calling test module plus `name`, crate-relative.
pub(crate) fn child_path(module: &str, name: &str) -> String {
    let module = module
        .split_once("::")
        .map(|(_, rest)| rest)
        .unwrap_or(module);
    format!("{module}::{name}")
}

fn command(path: &str, env: &[(&str, &str)]) -> Command {
    let mut cmd = Command::new(std::env::current_exe().expect("current_exe"));
    cmd.env_clear();
    if let Some(p) = std::env::var_os("LD_LIBRARY_PATH") {
        cmd.env("LD_LIBRARY_PATH", p);
    }
    let name = path.rsplit("::").next().unwrap_or(path);
    cmd.env(CHILD_SELECTOR, name);
    for (k, v) in env {
        cmd.env(k, v);
    }
    cmd.args([path, "--exact", "--nocapture", "--test-threads=1"]);
    cmd
}

/// Run the child at libtest path `path` with `env`, capturing each stream.
pub(crate) fn run(path: &str, env: &[(&str, &str)]) -> Ending {
    let out = command(path, env).output().expect("spawn child");
    Ending {
        code: out.status.code(),
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
    }
}

/// Run the child with stdout and stderr on one pipe, so their order is
/// observable.
pub(crate) fn run_merged(path: &str) -> String {
    use std::io::Read;
    let (mut reader, writer) = std::io::pipe().expect("pipe");
    let mut cmd = command(path, &[]);
    cmd.stdout(writer.try_clone().expect("clone pipe"))
        .stderr(writer);
    let mut child = cmd.spawn().expect("spawn child");
    drop(cmd);
    let mut merged = String::new();
    reader.read_to_string(&mut merged).expect("read merged");
    child.wait().expect("wait child");
    merged
}
