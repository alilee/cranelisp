//! Child-process cells for emitted code that ends the process.
//!
//! A raise ends the process (`design/backend/backend.md` §7), so a cell that
//! runs a panicking JIT body cannot observe the outcome in its own process. A
//! parent test re-executes this test binary, selecting one child body by its
//! libtest name and naming it in [`CHILD_SELECTOR`]. Each child body is an
//! ordinary test that returns at once unless [`selected`] names it, so the
//! ordinary suite runs every body inertly. Children start from a cleared
//! environment plus the values the parent names.
//!
//! Modelled on `cranelisp-intrinsics`' crate-private harness of the same name.

use std::process::Command;

use cranelisp_intrinsics::panic::{PANIC_EXIT_STATUS, PANIC_REPORT_PREFIX};

const CHILD_SELECTOR: &str = "BACKEND_TEST_CHILD";

/// Whether this process was started to run the child body `name`.
pub(crate) fn selected(name: &str) -> bool {
    std::env::var(CHILD_SELECTOR).as_deref() == Ok(name)
}

/// A value the parent passed to the child, parsed.
#[track_caller]
pub(crate) fn arg<T: std::str::FromStr>(key: &str) -> T {
    std::env::var(key)
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or_else(|| panic!("child argument {key} missing or malformed"))
}

/// How a child ended.
pub(crate) struct Ending {
    pub(crate) code: Option<i32>,
    pub(crate) stdout: String,
    pub(crate) stderr: String,
}

impl Ending {
    /// Assert the child ended by exactly one language panic reporting
    /// `message`, and that nothing the child body prints after the raise ran.
    #[track_caller]
    pub(crate) fn assert_panicked_with(&self, message: &str, what: &str) {
        assert_eq!(
            self.code,
            Some(PANIC_EXIT_STATUS),
            "{what}: the panic status, not a signal or success\nstderr:\n{}",
            self.stderr
        );
        let reports: Vec<&str> = self
            .stderr
            .lines()
            .filter(|l| l.starts_with(PANIC_REPORT_PREFIX))
            .collect();
        let expected = format!("{PANIC_REPORT_PREFIX}{message}");
        assert_eq!(reports, [expected.as_str()], "{what}\n{}", self.stderr);
        assert!(
            !self.stdout.contains(RESUMED),
            "{what}: the child resumed after the raise\n{}",
            self.stdout
        );
    }
}

/// What a child body prints when control returns from the raising call. A
/// raise that resumes its caller shows as this marker on the child's stdout.
pub(crate) const RESUMED: &str = "BACKEND_CHILD_RESUMED_AFTER_RAISE";

/// `module_path!()` of the calling test module plus `name`, crate-relative.
pub(crate) fn child_path(module: &str, name: &str) -> String {
    let module = module
        .split_once("::")
        .map(|(_, rest)| rest)
        .unwrap_or(module);
    format!("{module}::{name}")
}

/// Run the child at libtest path `path` with `env`, capturing each stream.
pub(crate) fn run(path: &str, env: &[(&str, String)]) -> Ending {
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
    let out = cmd.output().expect("spawn child");
    Ending {
        code: out.status.code(),
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
    }
}
