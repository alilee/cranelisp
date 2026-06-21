// session_v4::test_runner — test-discovery subsystem (S87 §2.1).
//
// The host-promised `discover-tests` extern + its `TestRunnerState` + the
// late-bound wrapper-closure machinery + the heap-marshalling helpers.
// Self-contained per `src/CLAUDE.md §"Test discovery"`; the only session-side
// coupling is the `tc_modules` raw pointer patched in `CompilerSession::new`
// (which stays in `lifecycle.rs`) via the `set_tc_modules` setter below.
// Moved verbatim from `session_v4.rs` (S87 §2.1).

use std::sync::Mutex;

use cranelisp_types::{ModuleEntry, ModuleFullPath};

use crate::code::SessionSymbolTable;

// ---------------------------------------------------------------------------
// Test infrastructure: core logic + JIT-callable externs
// ---------------------------------------------------------------------------

/// Result of running a single test (Rust-side, no heap allocation). Consumed by
/// the `/run-tests` slash-command formatter (`format_test_run`); the test name
/// is held by the caller (the FQ name being run) so it is not duplicated here.
pub(crate) enum TestOutcome {
    Pass,
    Fail { reason: String },
    Panic { reason: String },
}

/// Core: discover test-* function names in a module. No heap allocation.
///
/// Returns fully-qualified names ("module/test-name") sorted alphabetically.
///
/// Sprint 57 Wave 2 G6: reads `ModuleEntry::Def.code` (replaces the deleted
/// `CodegenProduct` DashMap).
pub(crate) fn discover_test_names(
    tc_modules: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    module: &ModuleFullPath,
) -> Vec<String> {
    let mut names = Vec::new();
    let symbols = match tc_modules.get(module) {
        Some(st) => st,
        None => return names,
    };
    for (name, entry) in symbols.all_symbols() {
        if !name.as_ref().starts_with("test-") {
            continue;
        }
        // The callable slot rides on the `DefKind` variant (S83 reshape,
        // FIXME 0356/0357) — read it via the `callable_got_slot()` chokepoint.
        match entry {
            ModuleEntry::Def {
                param_names,
                code: Some(_),
                ..
            } if param_names.is_empty()
                && entry
                    .callable_got_slot()
                    .is_some_and(|slot| !symbols.got.load_slot(slot).is_null()) =>
            {
                names.push(format!("{}/{}", module.as_ref(), name.as_ref()));
            }
            _ => continue,
        }
    }
    names.sort();
    names
}

/// Core: run a single test by fully-qualified name. No heap allocation.
///
/// Looks up the code pointer, calls it, interprets the (Option String) result.
///
/// Sprint 57 Wave 2 G6: reads `ModuleEntry::Def.code` (replaces the deleted
/// `CodegenProduct` DashMap).
pub(crate) fn run_test_by_name(
    tc_modules: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    fq_name: &str,
    default_module: &ModuleFullPath,
) -> TestOutcome {
    use cranelisp_types::NULLARY_TAG_THRESHOLD;

    // Parse "module/name" into module path and bare name. S78 §1.4: an
    // unqualified name defaults to the current/entry module, NOT a hardcoded
    // "user" — for a non-`user` entry program a hardcoded "user" mis-routes
    // the lookup to a non-existent table.
    let (module, bare_name) = match fq_name.rsplit_once('/') {
        Some((m, n)) => (ModuleFullPath::from(m), n),
        None => (default_module.clone(), fq_name),
    };

    // Look up the code pointer from the entry's GOT slot (D41/D35 — GOT is
    // the single source of callable addresses; no `Code::ptr`).
    let code_ptr = tc_modules.get(&module).and_then(|t| {
        // The callable slot rides on the `DefKind` variant (S83 reshape,
        // FIXME 0356/0357) — read it via the `callable_got_slot()` chokepoint.
        let entry = t.get(bare_name)?;
        let ModuleEntry::Def { code: Some(_), .. } = entry else {
            return None;
        };
        let slot = entry.callable_got_slot()?;
        let ptr = t.got.load_slot(slot);
        if ptr.is_null() {
            None
        } else {
            Some(ptr)
        }
    });

    let code_ptr = match code_ptr {
        Some(ptr) if !ptr.is_null() => ptr,
        _ => return TestOutcome::Fail {
            reason: "test function not found".to_string(),
        },
    };

    // Call the test function.
    let _ = cranelisp_intrinsics::panic::take_runtime_error();
    let value = unsafe {
        let func: extern "C" fn() -> i64 = std::mem::transmute(code_ptr);
        func()
    };

    if let Some(msg) = cranelisp_intrinsics::panic::take_runtime_error() {
        return TestOutcome::Panic { reason: msg };
    }

    if (value as usize) < NULLARY_TAG_THRESHOLD {
        TestOutcome::Pass
    } else {
        let reason = unsafe {
            let base = value as *const u8;
            let string_ptr = *(base.add(
                cranelisp_backend::heap::HeapAdt::field_offset(0) as usize,
            ) as *const i64);
            cranelisp_intrinsics::heap_string::read_string_as_str(string_ptr).to_string()
        };
        TestOutcome::Fail { reason }
    }
}

/// Session state for the `run-test` / `discover-tests` intrinsics.
///
/// Sprint 66 Wave 3a-γ: lifted from per-compilation construction to
/// session-wide construction (built once in `CompilerSession::new`, stored on
/// `SharedState`). The thread-local `TEST_RUNNER` cell holds a pointer derived
/// from `SharedState.test_runner_state` (a `Box`, so the address is stable for
/// the session lifetime); the REPL eval path sets it before invoking a
/// compiled expression. The `current_module` field is a `Mutex` so the REPL
/// `/mod` command may update it without re-allocating the state.
///
/// The intrinsics themselves dereference these pointers when JIT-emitted code
/// invokes `run-test` / `discover-tests` — see `run_test_extern` /
/// `discover_tests_extern` below. The state is only meaningful inside an
/// active REPL eval; absent that, the intrinsics return harmless empty
/// results (mirrors the prior null-pointer-guard behaviour).
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

// `int_intrinsics()` + `run_test_extern` + the SList/IO/TestResult marshalling
// helpers DELETED (S76 FIXME 0271). `run-test` is subsumed — running a test is
// invoking a discovered late-bound wrapper under `catch-runtime-error`. The
// surviving `discover-tests` extern is host-promised via `Jit::define_symbol`
// (registered in `worker::build_session_jit`), not a parked-table entry. The
// trace half of the old table left earlier (FIXME 0256); the table is now gone.

/// Allocate a heap ADT with the given tag and fields.
///
/// Layout: [alloc_size(8) | rc=1(8) | tag(8) | field0(8) | field1(8) | ...]
/// (mirrors `HeapAdt` in `cranelisp-backend::heap`). Returns the base pointer.
unsafe fn alloc_heap_adt(tag: i64, fields: &[i64]) -> i64 { unsafe {
    let payload_size = 8 + fields.len() * 8; // tag + fields
    let base = cranelisp_intrinsics::alloc::alloc_with_rc(payload_size);
    // Tag at offset 16 (HeapHeader::SIZE).
    *(base.add(16) as *mut i64) = tag;
    // Fields at offsets 24, 32, 40, ...
    for (i, &field) in fields.iter().enumerate() {
        *(base.add(24 + i * 8) as *mut i64) = field;
    }
    base as i64
}}

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
unsafe fn alloc_test_wrapper_closure(slot_addr: i64) -> i64 { unsafe {
    // payload = code_ptr(8) + drop_glue_ptr(8) + 1 capture(8) = 24 bytes.
    let base = cranelisp_intrinsics::alloc::alloc_with_rc(24);
    *(base.add(16) as *mut i64) = discovered_test_wrapper as *const u8 as i64; // code_ptr
    *(base.add(24) as *mut i64) = 0; // drop_glue_ptr (no heap captures)
    *(base.add(32) as *mut i64) = slot_addr; // capture[0] = GOT slot address
    base as i64
}}

/// An eligible test discovered for the fn-value return: the FQ name and the
/// stable address of its GOT slot (for the late-bound wrapper capture).
struct EligibleTest {
    fq_name: String,
    slot_addr: i64,
}

/// Scan a module for eligible `test-*` fns: prefix `test-` AND the EXACT scheme
/// `(Fn [] (Option String))` (test-discovery.md q-eligibility). A mis-typed
/// `test-*` is excluded; the warning is surfaced at the REPL/`--run` boundary
/// (the extern runs in compiled code and cannot push a Warning, so the warn is
/// the slash-command path's concern — here we silently exclude).
///
/// Returns the eligible tests sorted by FQ name. The slot address is
/// `got.base_ptr() + slot*8` — stable for the module lifetime, contents updated
/// in place on redefinition (late binding).
fn discover_eligible_tests(
    tc_modules: &dashmap::DashMap<ModuleFullPath, SessionSymbolTable>,
    module: &ModuleFullPath,
) -> Vec<EligibleTest> {
    let mut out = Vec::new();
    let Some(symbols) = tc_modules.get(module) else {
        return out;
    };
    let got_base = symbols.got.base_ptr() as i64;
    for (name, entry) in symbols.all_symbols() {
        if !name.as_ref().starts_with("test-") {
            continue;
        }
        // The callable slot rides on the `DefKind` variant (S83 reshape,
        // FIXME 0356/0357) — read it via the `callable_got_slot()` chokepoint.
        let ModuleEntry::Def { scheme, .. } = entry else {
            continue;
        };
        let Some(slot) = entry.callable_got_slot() else {
            continue;
        };
        if !test_scheme_is_eligible(scheme) {
            continue; // mis-typed test-* — excluded (q-eligibility).
        }
        out.push(EligibleTest {
            fq_name: format!("{}/{}", module.as_ref(), name.as_ref()),
            // slot address = base + slot * size_of::<AtomicPtr<u8>>() (8).
            slot_addr: got_base + (slot as i64) * 8,
        });
    }
    out.sort_by(|a, b| a.fq_name.cmp(&b.fq_name));
    out
}


/// True iff `scheme` is exactly `(Fn [] (Option String))` — zero-arg returning
/// `(Option String)` (test-discovery.md q-eligibility). Quantified vars are
/// permitted only if they do not appear (a monomorphic test); the structural
/// shape is what matters.
fn test_scheme_is_eligible(scheme: &cranelisp_types::Scheme) -> bool {
    let cranelisp_types::Type::Fn(params, ret) = &scheme.ty else {
        return false;
    };
    if !params.is_empty() {
        return false;
    }
    let cranelisp_types::Type::ADT(fqtn, args) = ret.as_ref() else {
        return false;
    };
    fqtn.name.as_ref() == "Option"
        && fqtn.module.as_ref() == "primitives"
        && args.len() == 1
        && matches!(args[0], cranelisp_types::Type::String)
}

#[cfg(test)]
mod discover_tests_extern_tests;

/// JIT-callable host-promised extern: discover eligible test functions across
/// the given module paths and return fn-value pairs.
///
/// Argument: a heap `(Vec String)` of module paths (the no-arg / single-String
/// sugar shapes are normalised to this by the stdlib macro — FIXME 0273). A
/// null/absent arg falls back to the current module.
///
/// Returns a heap `(Vec (Pair String (Fn [] (Option String))))`: each pair is a
/// heap `Pair` ADT (tag 0, fields `[name_string, callable_closure]`); the
/// callable is a late-bound wrapper closure (see `discovered_test_wrapper`).
///
/// Registered as `discover-tests` via `Jit::define_symbol` in
/// `worker::build_session_jit` (`DefKind::PrimitiveExtern`, test-discovery.md §6).
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
            vec![state
                .current_module
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .clone()]
        } else {
            module_paths
        };

        // Union the eligible tests across the named modules.
        let mut eligible: Vec<EligibleTest> = Vec::new();
        for module in &module_paths {
            eligible.extend(discover_eligible_tests(tc_modules, module));
        }

        // Build the (Vec (Pair String callable)).
        let pair_ptrs: Vec<i64> = eligible
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
unsafe fn read_module_paths(vec_ptr: i64) -> Vec<ModuleFullPath> { unsafe {
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
}}

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
unsafe fn alloc_vec_from(elems: &[i64]) -> i64 { unsafe {
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
}}
