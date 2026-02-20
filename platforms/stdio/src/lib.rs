//! Stdio platform for cranelisp — standalone cdylib.
//!
//! Implements the "stdio" platform as a dynamically-loaded library:
//! - `print`: String -> IO Int — print a string followed by a newline
//! - `read-line`: () -> IO String — read a line from stdin
//!
//! Uses the `cranelisp-platform` shared crate for ABI types, wrapper
//! types (`CLString`, `CLInt`, `CLIO`), and the `declare_platform!` macro.

use cranelisp_platform::*;

static HOST: HostContext = HostContext::new();

/// Print a string followed by a newline. Returns IO-wrapped 0.
#[unsafe(export_name = "cranelisp_print")]
pub extern "C" fn print_string(s: CLString) -> CLIO<CLInt> {
    println!("{}", s.as_str());
    0i64.into()
}

/// Read a line from stdin. Returns an IO-wrapped heap-allocated string.
///
/// Trims trailing newline/carriage return.
#[unsafe(export_name = "cranelisp_read_line")]
pub extern "C" fn read_line() -> CLIO<CLString> {
    let mut buf = String::new();
    std::io::stdin().read_line(&mut buf).unwrap_or(0);
    buf.trim_end_matches(&['\n', '\r'][..]).to_string().into()
}

declare_platform! {
    name: "stdio",
    version: "0.1.0",
    host: HOST,
    functions: [
        print_string {
            cl_name: "print",
            sig: "(Fn [String] (IO Int))",
            doc: "Print a string followed by a newline",
            params: [s],
        },
        read_line {
            cl_name: "read-line",
            sig: "(Fn [] (IO String))",
            doc: "Read a line from stdin",
            params: [],
        },
    ]
}
