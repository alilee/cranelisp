//! Test-capture platform for cranelisp — standalone cdylib.
//!
//! Replaces stdio with in-memory buffers for testing:
//! - `print`: appends to a captured output buffer instead of printing to stdout
//! - `read-line`: returns pre-configured input strings instead of reading from stdin
//!
//! Also exports test utility functions (NOT platform functions) for setup/teardown:
//! - `test_capture_set_input`: queue input lines for read-line
//! - `test_capture_get_output`: retrieve all captured print output
//! - `test_capture_reset`: clear both input queue and output buffer

use cranelisp_platform::*;
use std::collections::VecDeque;
use std::sync::Mutex;

static HOST: HostContext = HostContext::new();

/// Captured print output: each call to print appends one entry.
static OUTPUT: Mutex<Vec<String>> = Mutex::new(Vec::new());

/// Pre-configured input lines: each call to read-line pops from the front.
static INPUT: Mutex<VecDeque<String>> = Mutex::new(VecDeque::new());

/// Capture print output instead of writing to stdout.
pub extern "C" fn capture_print(s: CLString) -> CLIO<CLInt> {
    OUTPUT.lock().unwrap().push(s.as_str().to_string());
    0i64.into()
}

/// Return pre-configured input instead of reading from stdin.
///
/// Pops the first queued line. If the queue is empty, returns an empty string.
pub extern "C" fn scripted_read_line() -> CLIO<CLString> {
    let line = INPUT
        .lock()
        .unwrap()
        .pop_front()
        .unwrap_or_default();
    line.into()
}

declare_platform! {
    name: "test-capture",
    version: "0.1.0",
    host: HOST,
    functions: [
        capture_print {
            cl_name: "print",
            sig: "(Fn [String] (IO Int))",
            doc: "Print a string (captured for testing)",
            params: [s],
        },
        scripted_read_line {
            cl_name: "read-line",
            sig: "(Fn [] (IO String))",
            doc: "Read a line from scripted input (for testing)",
            params: [],
        },
    ]
}

// ── Test utility functions (NOT platform functions) ────────────────────────
// These are exported from the cdylib for direct use by Rust test code via
// libloading. They are NOT registered with the JIT.

/// Set up input lines for the next test run.
///
/// `lines` is an array of `count` C-string pointers, `lens` is a parallel
/// array of lengths. Each entry is pushed onto the input queue.
#[unsafe(no_mangle)]
pub extern "C" fn test_capture_set_input(
    lines: *const *const u8,
    lens: *const usize,
    count: usize,
) {
    let mut input = INPUT.lock().unwrap();
    input.clear();
    for i in 0..count {
        let bytes = unsafe { std::slice::from_raw_parts(*lines.add(i), *lens.add(i)) };
        if let Ok(s) = std::str::from_utf8(bytes) {
            input.push_back(s.to_string());
        }
    }
}

/// Get captured output as a newline-separated string.
///
/// Writes the pointer and length of the resulting byte buffer to `out_ptr`
/// and `out_len`. The caller is responsible for freeing the buffer via
/// `test_capture_free_output`.
#[unsafe(no_mangle)]
pub extern "C" fn test_capture_get_output(out_ptr: *mut *const u8, out_len: *mut usize) {
    let output = OUTPUT.lock().unwrap();
    let joined = output.join("\n");
    let bytes = joined.into_bytes();
    let len = bytes.len();
    let ptr = Box::into_raw(bytes.into_boxed_slice()) as *const u8;
    unsafe {
        *out_ptr = ptr;
        *out_len = len;
    }
}

/// Free a buffer returned by `test_capture_get_output`.
#[unsafe(no_mangle)]
pub extern "C" fn test_capture_free_output(ptr: *mut u8, len: usize) {
    if !ptr.is_null() && len > 0 {
        unsafe {
            let _ = Box::from_raw(std::slice::from_raw_parts_mut(ptr, len));
        }
    }
}

/// Clear captured output and input queue.
#[unsafe(no_mangle)]
pub extern "C" fn test_capture_reset() {
    OUTPUT.lock().unwrap().clear();
    INPUT.lock().unwrap().clear();
}
