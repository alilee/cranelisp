//! Stdio platform for cranelisp -- standalone cdylib.
//!
//! Implements the "stdio" platform as a dynamically-loaded library:
//! - `print`: String -> IO Int -- print a string followed by a newline
//! - `read-line`: () -> IO String -- read a line from stdin
//!
//! Uses the `cranelisp-platform` shared crate for ABI types, wrapper
//! types (`CLString`, `CLInt`, `CLIO`), and the `declare_platform!` macro.

use cranelisp_platform::*;

static HOST: HostContext = HostContext::new();

/// Print a string followed by a newline. Returns a deferred IO Effect.
///
/// Uses the consuming capture-RC protocol (Decision 24): `into_owned_consuming`
/// takes ownership of the caller's transferred reference and releases it on
/// drop when the Effect thunk runs. See `design/backend/ring2-rc.md` §10.4.
pub extern "C" fn print_string(s: CLString) -> CLIO<CLInt> {
    let owned = s.into_owned_consuming();
    CLIO::effect(move || {
        println!("{}", owned.as_str());
        CLInt::from(0i64)
    })
}

/// Read a line from stdin. Returns a deferred IO Effect.
///
/// Trims trailing newline/carriage return. No capture-RC needed
/// because this function takes no heap parameters.
pub extern "C" fn read_line() -> CLIO<CLString> {
    CLIO::effect(move || {
        let mut buf = String::new();
        std::io::stdin().read_line(&mut buf).unwrap_or(0);
        buf.trim_end_matches(&['\n', '\r'][..])
            .to_string()
            .into()
    })
}

declare_platform! {
    name: "stdio",
    version: "0.1.0",
    host: HOST,
    functions: [
        print_string {
            cl_name: "print",
            sig: "(Fn [primitives/String] (primitives/IO primitives/Int))",
            doc: "Print a string followed by a newline",
            params: [s],
            scheduling: SchedulingClass::Sequential,
        },
        read_line {
            cl_name: "read-line",
            sig: "(Fn [] (primitives/IO primitives/String))",
            doc: "Read a line from stdin",
            params: [],
            scheduling: SchedulingClass::Sequential,
        },
    ]
}
