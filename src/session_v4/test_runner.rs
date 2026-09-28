// session_v4::test_runner — the shared test runner (`design/int/test-runner.md`).
//
// `/run-tests`, `/run-all-tests` and `--test` are one runner: `discovery` is
// the one eligibility scan, `selection` chooses modules, and `run` prepares,
// executes and reports. This parent holds the REPL-only `discover-tests`
// extern, its `TestRunnerState` and the heap marshalling it needs; the only
// session-side coupling is the `tc_modules` raw pointer patched in
// `CompilerSession::new` via `set_tc_modules`.

use std::sync::Mutex;

use cranelisp_types::ModuleFullPath;

use crate::code::SessionSymbolTable;

mod discovery;
mod run;
mod selection;

pub(crate) use self::discovery::{TestDefinition, classify_test_definition};
pub use self::run::TestRunReport;

/// Session state for the `discover-tests` extern, built once in
/// `CompilerSession::new` and stored on `SharedState`.
///
/// The thread-local `TEST_RUNNER` cell holds a pointer derived from
/// `SharedState.test_runner_state` (a `Box`, so the address is stable for the
/// session lifetime); the REPL eval path sets it before invoking a compiled
/// expression. The `current_module` field is a `Mutex` so the REPL `/mod`
/// command may update it without re-allocating the state.
///
/// `discover_tests_extern` dereferences these pointers when JIT-emitted code
/// calls `discover-tests`. The state is only meaningful inside an active REPL
/// eval; absent that, the extern returns an empty list.
pub struct TestRunnerState {
    /// TC modules for scanning symbol tables and reading compiled `code`.
    tc_modules: *const dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    /// Current module path (for discover-tests with empty module arg).
    /// Updated by `set_current_module` when the REPL `/mod` command switches.
    pub(crate) current_module: Mutex<ModuleFullPath>,
}

// Safety: the pointer-typed `tc_modules` field is read-only data; it points
// at a `DashMap` (itself Send + Sync) inside the same `SharedState` instance.
// `Mutex<ModuleFullPath>` is Send + Sync. The thread-local-pointer access is
// always read-via-Cell on the thread that called `set_test_runner_state`.
unsafe impl Send for TestRunnerState {}
unsafe impl Sync for TestRunnerState {}

impl TestRunnerState {
    /// Construct with a null `tc_modules` pointer; patched immediately after
    /// `Arc<SharedState>` construction via `set_tc_modules`. The
    /// `current_module` field seeds off the entry module name (S78 §1).
    pub(crate) fn new(current_module: ModuleFullPath) -> Self {
        Self {
            tc_modules: std::ptr::null(),
            current_module: Mutex::new(current_module),
        }
    }

    /// Patch the `tc_modules` raw pointer to point at the session's
    /// `symbol_tables` DashMap (S87 §2.2 — encapsulates the unsafe write with
    /// the type rather than exposing the field).
    ///
    /// # Safety
    ///
    /// The caller MUST guarantee single-writer access before any worker thread
    /// is spawned (so before any reader observes the field). In
    /// `CompilerSession::new` this is the pre-spawn patch: `shared` is
    /// `Arc<SharedState>`, never moved, and the `symbol_tables` field has a
    /// stable address for the session lifetime. This write happens exactly
    /// once, before `spawn_worker_threads`, so no concurrent reader exists yet.
    pub(crate) unsafe fn set_tc_modules(
        &self,
        ptr: *const dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    ) {
        // SAFETY: single-writer, pre-spawn; no concurrent reader exists yet
        // (see method doc + `CompilerSession::new` call site). The `Box`
        // owning this state sits inside `SharedState` behind `Arc`, so a `&mut`
        // through `Arc` would alias shared state — instead we cast through a
        // raw pointer to flip the single `*const` field.
        unsafe {
            let trs_ptr = self as *const TestRunnerState as *mut TestRunnerState;
            (*trs_ptr).tc_modules = ptr;
        }
    }

    /// Construct a stub TestRunnerState for unit tests that need to build a
    /// `SharedState` but don't exercise the test intrinsics. The
    /// `tc_modules` pointer is null; any extern call against this state
    /// returns the harmless null-pointer fallback (empty list / `?` name).
    pub fn stub() -> Self {
        Self {
            tc_modules: std::ptr::null(),
            current_module: Mutex::new(ModuleFullPath::from("user")),
        }
    }
}

thread_local! {
    static TEST_RUNNER: std::cell::Cell<*const TestRunnerState> =
        const { std::cell::Cell::new(std::ptr::null()) };
}

pub(crate) fn set_test_runner_state(state: &TestRunnerState) {
    TEST_RUNNER.with(|c| c.set(state as *const _));
}

/// Allocate a heap ADT with the given tag and fields.
///
/// Layout: [alloc_size(8) | rc=1(8) | tag(8) | field0(8) | field1(8) | ...]
/// (mirrors `HeapAdt` in `cranelisp-backend::heap`). Returns the base pointer.
unsafe fn alloc_heap_adt(tag: i64, fields: &[i64]) -> i64 {
    unsafe {
        let payload_size = 8 + fields.len() * 8; // tag + fields
        let base = cranelisp_intrinsics::alloc::alloc_with_rc(payload_size);
        // Tag at offset 16 (HeapHeader::SIZE).
        *(base.add(16) as *mut i64) = tag;
        // Fields at offsets 24, 32, 40, ...
        for (i, &field) in fields.iter().enumerate() {
            *(base.add(24 + i * 8) as *mut i64) = field;
        }
        base as i64
    }
}

/// The late-bound test-wrapper closure body — `extern "C" fn(env_ptr) -> i64`.
///
/// The closure layout is `[header(16) | code_ptr=this(8) | drop_glue=0(8) |
/// slot_addr(8)]` (a `HeapClosure` with one capture). The single capture is the
/// **address of the test's GOT slot** (`GotTable::base_ptr() + slot*8`), which
/// is stable for the module's lifetime; its *contents* are the test's current
/// code pointer (updated in place on redefinition). So the wrapper:
///
/// 1. loads the captured slot-address from the closure env (capture offset 0 =
///    base + 32);
/// 2. loads the current code pointer from that slot-address (late-binding — a
///    redefined test runs its new body through the same wrapper);
/// 3. calls `extern "C" fn() -> i64` and returns the `(Option String)` result.
///
/// A null slot (test not yet compiled) returns the sentinel `0` (`None`).
extern "C" fn discovered_test_wrapper(env_ptr: i64) -> i64 {
    if env_ptr == 0 {
        return 0;
    }
    unsafe {
        // capture[0] at offset 32 (HeapClosure::CAPTURES_START).
        let slot_addr = *((env_ptr as *const u8).add(32) as *const i64);
        if slot_addr == 0 {
            return 0;
        }
        let code_ptr = (slot_addr as *const *const u8).read();
        if code_ptr.is_null() {
            return 0;
        }
        let func: extern "C" fn() -> i64 = std::mem::transmute(code_ptr);
        func()
    }
}

/// Allocate a late-bound test-wrapper closure capturing `slot_addr` (the stable
/// address of the test's GOT slot). Layout matches a zero-capture-shape
/// `compile_lambda` closure with one capture, so the language sees it as an
/// ordinary `(Fn [] (Option String))` value.
unsafe fn alloc_test_wrapper_closure(slot_addr: i64) -> i64 {
    unsafe {
        // payload = code_ptr(8) + drop_glue_ptr(8) + 1 capture(8) = 24 bytes.
        let base = cranelisp_intrinsics::alloc::alloc_with_rc(24);
        *(base.add(16) as *mut i64) = discovered_test_wrapper as *const u8 as i64; // code_ptr
        *(base.add(24) as *mut i64) = 0; // drop_glue_ptr (no heap captures)
        *(base.add(32) as *mut i64) = slot_addr; // capture[0] = GOT slot address
        base as i64
    }
}

/// An eligible test for the fn-value return: its FQ name and the stable
/// address of its GOT slot, which the late-bound wrapper captures.
struct EligibleTest {
    fq_name: String,
    slot_addr: i64,
}

/// The shared scan's tests in `modules` that have a GOT slot, with that
/// slot's address (`got.base_ptr() + slot * 8`, stable for the module
/// lifetime and updated in place on redefinition). The extern runs inside
/// compiled code and has no warning channel, so the scan's warnings are
/// dropped here (`design/int/test-runner.md` §12).
fn discover_eligible_tests(
    tc_modules: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    modules: &[ModuleFullPath],
) -> Vec<EligibleTest> {
    discovery::scan_modules(tc_modules, modules)
        .tests
        .into_iter()
        .filter_map(|id| {
            let table = tc_modules.get(&id.module)?;
            let slot = table.get(id.symbol.as_ref())?.callable_got_slot()?;
            Some(EligibleTest {
                fq_name: id.to_string(),
                slot_addr: table.got.base_ptr() as i64 + (slot as i64) * 8,
            })
        })
        .collect()
}

#[cfg(test)]
mod discover_tests_extern_tests;

#[cfg(test)]
mod session_tests;

/// JIT-callable host-promised extern: discover eligible test functions across
/// the given module paths and return fn-value pairs.
///
/// Argument: a heap `(Vec String)` of module paths. A null pointer or an empty
/// vector falls back to the current module.
///
/// Returns a heap `(Vec (Pair String (Fn [] (Option String))))`: each pair is a
/// heap `Pair` ADT (tag 0, fields `[name_string, callable_closure]`); the
/// callable is a late-bound wrapper closure (see `discovered_test_wrapper`).
///
/// Registered as `discover-tests` via `Jit::define_symbol` in
/// `worker::build_session_jit` (host-promised `RustPrimitive`, test-discovery.md §6).
pub(crate) extern "C" fn discover_tests_extern(modules_vec: i64) -> i64 {
    TEST_RUNNER.with(|c| {
        let state_ptr = c.get();
        if state_ptr.is_null() {
            return unsafe { alloc_empty_vec() };
        }
        let state = unsafe { &*state_ptr };
        let tc_modules = unsafe { &*state.tc_modules };

        // Decode the (Vec String) argument into module paths. A null/empty Vec
        // falls back to the current module.
        let module_paths = unsafe { read_module_paths(modules_vec) };
        let module_paths = if module_paths.is_empty() {
            vec![
                state
                    .current_module
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .clone(),
            ]
        } else {
            module_paths
        };

        // Build the (Vec (Pair String callable)).
        let pair_ptrs: Vec<i64> = discover_eligible_tests(tc_modules, &module_paths)
            .into_iter()
            .map(|t| unsafe {
                let name_str =
                    cranelisp_intrinsics::heap_string::alloc_string(t.fq_name.as_bytes()) as i64;
                let callable = alloc_test_wrapper_closure(t.slot_addr);
                // Pair ctor tag=0, fields [first=name, second=callable].
                alloc_heap_adt(0, &[name_str, callable])
            })
            .collect();
        unsafe { alloc_vec_from(&pair_ptrs) }
    })
}

/// Read a heap `(Vec String)` into owned `ModuleFullPath`s. A null pointer or a
/// zero-length vec yields an empty list.
unsafe fn read_module_paths(vec_ptr: i64) -> Vec<ModuleFullPath> {
    unsafe {
        if vec_ptr == 0 {
            return Vec::new();
        }
        // HeapVec layout: [header(16) | len(8)@16 | cap(8)@24 | data_ptr(8)@32].
        let base = vec_ptr as *const u8;
        let len = *(base.add(16) as *const i64);
        let data_ptr = *(base.add(32) as *const i64) as *const i64;
        if len <= 0 || data_ptr.is_null() {
            return Vec::new();
        }
        let mut out = Vec::with_capacity(len as usize);
        for i in 0..len as usize {
            let elem = *data_ptr.add(i); // heap String pointer
            if elem == 0 {
                continue;
            }
            let s = cranelisp_intrinsics::heap_string::read_string_as_str(elem);
            out.push(ModuleFullPath::from(s));
        }
        out
    }
}

/// Allocate an empty heap `Vec` (len=0, cap=0, data_ptr=null) via the runtime
/// `vec_new` so the layout + data-buffer allocation convention match exactly
/// what backend codegen and `vec_drop` expect.
unsafe fn alloc_empty_vec() -> i64 {
    cranelisp_intrinsics::vec_runtime::vec_new(0)
}

/// Allocate a heap `Vec` whose elements are the given i64 values, using the
/// runtime `vec_new(cap)` (which allocates the data buffer with the canonical
/// convention — a raw buffer pointed at by `data_ptr`) and then writing the
/// elements + len directly. This keeps the buffer reclaimable by `vec_drop`.
unsafe fn alloc_vec_from(elems: &[i64]) -> i64 {
    unsafe {
        let n = elems.len();
        let base = cranelisp_intrinsics::vec_runtime::vec_new(n as i64) as *mut u8;
        if n == 0 {
            return base as i64;
        }
        // HeapVec: len@16, cap@24, data_ptr@32; data buffer holds `cap` i64 slots.
        let data_ptr = *(base.add(32) as *const i64) as *mut i64;
        for (i, &e) in elems.iter().enumerate() {
            *data_ptr.add(i) = e;
        }
        *(base.add(16) as *mut i64) = n as i64; // len
        base as i64
    }
}
