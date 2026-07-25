//! Test-capture platform for cranelisp -- standalone cdylib.
//!
//! Replaces stdio with in-memory buffers for testing:
//! - `print`: appends to a captured output buffer instead of printing to stdout
//! - `read-line`: returns pre-configured input strings instead of reading from stdin
//!
//! Also provides scheduling-class test functions:
//! - `commutative-noop`: Commutative, takes no args, returns `(IO Int)` with `Pure 0`
//! - `commutative-sleep-ms`: Commutative, takes Int ms, sleeps then returns the duration
//! - `resource-serial-noop`: ResourceSerial, takes Int token, sets resource token, returns 0
//! - `resource-serial-sleep-ms`: ResourceSerial, takes Int token + Int ms, sets resource token,
//!   sleeps then returns the duration (witnesses same-token serialization vs diff-token concurrency)
//! - `fault-now`: Sequential, takes no args, panics inside the IO Effect body when forced
//!   (raises a dispatch fault DURING the trampoline; witnesses the S81 fault funnel end-to-end)
//!
//! Also exports test utility functions (NOT platform functions) for setup/teardown:
//! - `test_capture_set_input`: queue input lines for read-line
//! - `test_capture_get_output`: retrieve all captured print output
//! - `test_capture_free_output`: free buffer from get_output
//! - `test_capture_reset`: clear both input queue and output buffer

use cranelisp_platform::*;
use std::collections::VecDeque;
use std::sync::Mutex;

static HOST: HostContext = HostContext::new();

/// Captured print output: each call to print appends one entry.
static OUTPUT: Mutex<Vec<String>> = Mutex::new(Vec::new());

/// Pre-configured input lines: each call to read-line pops from the front.
static INPUT: Mutex<VecDeque<String>> = Mutex::new(VecDeque::new());

/// Capture print output instead of writing to stdout. Returns a deferred IO Effect.
///
/// Uses the consuming capture-RC protocol (Decision 24): `into_owned_consuming`
/// takes ownership of the caller's transferred reference and releases it on
/// drop when the Effect thunk runs. See `design/backend/ring2-rc.md` §10.4.
pub extern "C" fn capture_print(s: CLString) -> CLIO<CLInt> {
    let owned = s.into_owned_consuming();
    CLIO::effect(move || {
        OUTPUT
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .push(owned.as_str().to_string());
        CLInt::from(0i64)
    })
}

/// Return pre-configured input instead of reading from stdin. Returns a deferred IO Effect.
///
/// Pops the first queued line. If the queue is empty, returns an empty string.
pub extern "C" fn scripted_read_line() -> CLIO<CLString> {
    CLIO::effect(move || {
        let line = INPUT
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .pop_front()
            .unwrap_or_default();
        line.into()
    })
}

/// Commutative no-op: does nothing, returns Pure 0. Marked Commutative so the
/// compiler can identify commutative pairs and insert Par nodes.
pub extern "C" fn commutative_noop() -> CLIO<CLInt> {
    CLIO::effect(|| CLInt::from(0i64))
}

/// Commutative sleep: sleeps for `ms` milliseconds and returns the duration.
/// Marked Commutative for parallelism verification tests (timing-based).
pub extern "C" fn commutative_sleep_ms(ms: CLInt) -> CLIO<CLInt> {
    let duration = i64::from(ms);
    CLIO::effect(move || {
        std::thread::sleep(std::time::Duration::from_millis(duration as u64));
        CLInt::from(duration)
    })
}

/// Faulting Effect: panics inside the deferred Effect body when forced. The S81
/// fault funnel (`CLIO::effect`'s DLL-local `catch_unwind`) converts the panic
/// into an `EffectOutcome` carrying a `fault_cause`, which the IO trampoline
/// surfaces as a `PlatformError::DispatchError { fn_name: "fault-now" }` in the
/// host. The signature is `(Fn [] (IO Int))` so a free-standing program can call
/// it directly. Sequential + IO Effect ⇒ the fault is raised DURING the
/// trampoline (not at thunk-construction), witnessing the during-IO
/// dispatch-fault path end-to-end (FIXME 0401). Returns `(IO Int)` only on the
/// (unreachable) clean path — the body always panics.
pub extern "C" fn fault_now() -> CLIO<CLInt> {
    CLIO::effect(|| {
        panic!("test-capture fault-now: deliberate dispatch fault");
        #[allow(unreachable_code)]
        CLInt::from(0i64)
    })
}

/// Resource-serial no-op: sets the resource token on the Effect node and returns 0.
/// Marked ResourceSerial for testing resource token serialization.
pub extern "C" fn resource_serial_noop(token: CLInt) -> CLIO<CLInt> {
    let resource_token = i64::from(token);
    CLIO::effect_on_resource(resource_token, || CLInt::from(0i64))
}

/// Resource-serial sleep: places the resource token on the Effect node AND sleeps
/// `ms` milliseconds before returning the duration. The union of
/// `resource_serial_noop`'s token mechanism and `commutative_sleep_ms`'s timing
/// observability: same non-zero token ⇒ the trampoline serializes data-independent
/// calls (witnessable as ~2× wall-clock); different tokens ⇒ concurrent (~1×).
/// Marked ResourceSerial for end-to-end token-serialization verification
/// (spec §10.12.4).
pub extern "C" fn resource_serial_sleep_ms(token: CLInt, ms: CLInt) -> CLIO<CLInt> {
    let resource_token = i64::from(token);
    let duration = i64::from(ms);
    CLIO::effect_on_resource(resource_token, move || {
        std::thread::sleep(std::time::Duration::from_millis(duration as u64));
        CLInt::from(duration)
    })
}

declare_platform! {
    name: "test-capture",
    version: "0.1.0",
    host: HOST,
    functions: [
        capture_print {
            cl_name: "print",
            sig: "(Fn [primitives/String] (primitives/IO primitives/Int))",
            doc: "Print a string (captured for testing)",
            params: [s],
            scheduling: SchedulingClass::Sequential,
        },
        scripted_read_line {
            cl_name: "read-line",
            sig: "(Fn [] (primitives/IO primitives/String))",
            doc: "Read a line from scripted input (for testing)",
            params: [],
            scheduling: SchedulingClass::Sequential,
        },
        commutative_noop {
            cl_name: "commutative-noop",
            sig: "(Fn [] (primitives/IO primitives/Int))",
            doc: "No-op (Commutative scheduling class, for testing)",
            params: [],
            scheduling: SchedulingClass::Commutative,
        },
        commutative_sleep_ms {
            cl_name: "commutative-sleep-ms",
            sig: "(Fn [primitives/Int] (primitives/IO primitives/Int))",
            doc: "Sleep for ms milliseconds and return the duration (Commutative, for testing)",
            params: [ms],
            scheduling: SchedulingClass::Commutative,
        },
        fault_now {
            cl_name: "fault-now",
            sig: "(Fn [] (primitives/IO primitives/Int))",
            doc: "Panic inside the IO Effect body when forced (raises a dispatch fault during the trampoline, for testing fault surfacing)",
            params: [],
            scheduling: SchedulingClass::Sequential,
        },
        resource_serial_noop {
            cl_name: "resource-serial-noop",
            sig: "(Fn [primitives/Int] (primitives/IO primitives/Int))",
            doc: "No-op with resource token (ResourceSerial scheduling class, for testing)",
            params: [token],
            scheduling: SchedulingClass::ResourceSerial,
        },
        resource_serial_sleep_ms {
            cl_name: "resource-serial-sleep-ms",
            sig: "(Fn [primitives/Int primitives/Int] (primitives/IO primitives/Int))",
            doc: "Sleep for ms milliseconds with a resource token, returning the duration (ResourceSerial scheduling class, for testing token serialization)",
            params: [token, ms],
            scheduling: SchedulingClass::ResourceSerial,
        },
    ]
}

// -- Test utility functions (NOT platform functions) --
// These are exported from the cdylib for direct use by Rust test code via
// libloading. They are NOT registered with the JIT.

/// Set up input lines for the next test run.
///
/// `lines` is an array of `count` C-string pointers, `lens` is a parallel
/// array of lengths. Each entry is pushed onto the input queue.
///
/// # Safety
/// `lines` must point to `count` valid `*const u8` pointers.
/// `lens` must point to `count` valid `usize` values.
/// Each `lines[i]` must point to `lens[i]` valid bytes of UTF-8.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn test_capture_set_input(
    lines: *const *const u8,
    lens: *const usize,
    count: usize,
) {
    let mut input = INPUT.lock().unwrap_or_else(|e| e.into_inner());
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
///
/// # Safety
/// `out_ptr` and `out_len` must be valid, aligned, writable pointers.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn test_capture_get_output(out_ptr: *mut *const u8, out_len: *mut usize) {
    let output = OUTPUT.lock().unwrap_or_else(|e| e.into_inner());
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
///
/// # Safety
/// `ptr` must be a pointer previously returned by `test_capture_get_output`,
/// and `len` must be the corresponding length.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn test_capture_free_output(ptr: *mut u8, len: usize) {
    if !ptr.is_null() && len > 0 {
        unsafe {
            let _ = Box::from_raw(std::ptr::slice_from_raw_parts_mut(ptr, len));
        }
    }
}

/// Clear captured output and input queue.
#[unsafe(no_mangle)]
pub extern "C" fn test_capture_reset() {
    OUTPUT.lock().unwrap_or_else(|e| e.into_inner()).clear();
    INPUT.lock().unwrap_or_else(|e| e.into_inner()).clear();
}
