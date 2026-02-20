//! Integration tests for platform DLL loading.
//!
//! These tests require `cargo build -p cranelisp-test-capture -p cranelisp-stdio`
//! to have been run first (the justfile `test-platform` recipe handles this).
//!
//! Tests that use the test-capture DLL must run with `--test-threads=1` because
//! the DLL has global state (output buffer, input queue).

use std::path::PathBuf;

use cranelisp::error::CranelispError;
use cranelisp::jit::Jit;
use cranelisp::repl::ReplSession;

/// Path to the test-capture platform DLL.
fn test_capture_dylib_path() -> PathBuf {
    let ext = if cfg!(target_os = "macos") {
        "dylib"
    } else if cfg!(target_os = "windows") {
        "dll"
    } else {
        "so"
    };
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("debug")
        .join(format!("libcranelisp_test_capture.{}", ext))
}

/// Path to the stdio platform DLL.
fn stdio_dylib_path() -> PathBuf {
    let ext = if cfg!(target_os = "macos") {
        "dylib"
    } else if cfg!(target_os = "windows") {
        "dll"
    } else {
        "so"
    };
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("debug")
        .join(format!("libcranelisp_stdio.{}", ext))
}

/// RAII guard for the test-capture DLL: loads the library and provides
/// helper methods to call the test utility functions.
struct TestCapture {
    lib: libloading::Library,
}

impl TestCapture {
    fn new(path: &std::path::Path) -> Self {
        let lib = unsafe { libloading::Library::new(path) }
            .unwrap_or_else(|e| panic!("failed to load test-capture DLL: {}", e));
        TestCapture { lib }
    }

    /// Reset captured output and input queue.
    fn reset(&self) {
        unsafe {
            let func: libloading::Symbol<extern "C" fn()> =
                self.lib.get(b"test_capture_reset").unwrap();
            func();
        }
    }

    /// Set input lines that read-line will return.
    fn set_input(&self, lines: &[&str]) {
        let ptrs: Vec<*const u8> = lines.iter().map(|s| s.as_ptr()).collect();
        let lens: Vec<usize> = lines.iter().map(|s| s.len()).collect();
        unsafe {
            let func: libloading::Symbol<
                extern "C" fn(*const *const u8, *const usize, usize),
            > = self.lib.get(b"test_capture_set_input").unwrap();
            func(ptrs.as_ptr(), lens.as_ptr(), lines.len());
        }
    }

    /// Get all captured output as a single string (lines joined by newline).
    fn get_output(&self) -> String {
        let mut out_ptr: *const u8 = std::ptr::null();
        let mut out_len: usize = 0;
        unsafe {
            let get_fn: libloading::Symbol<extern "C" fn(*mut *const u8, *mut usize)> =
                self.lib.get(b"test_capture_get_output").unwrap();
            get_fn(&mut out_ptr, &mut out_len);
            if out_len == 0 {
                return String::new();
            }
            let bytes = std::slice::from_raw_parts(out_ptr, out_len);
            let result = String::from_utf8_lossy(bytes).to_string();
            // Free the buffer
            let free_fn: libloading::Symbol<extern "C" fn(*mut u8, usize)> =
                self.lib.get(b"test_capture_free_output").unwrap();
            free_fn(out_ptr as *mut u8, out_len);
            result
        }
    }
}

/// Build a ReplSession with the test-capture platform loaded.
/// Returns the session and the TestCapture helper.
fn build_test_capture_session() -> Result<(ReplSession, TestCapture), CranelispError> {
    let dll_path = test_capture_dylib_path();
    if !dll_path.exists() {
        panic!(
            "test-capture DLL not found at {:?}. Run `cargo build -p cranelisp-test-capture` first.",
            dll_path
        );
    }

    // Load the DLL for test utility access (separate load from Jit's load)
    let capture = TestCapture::new(&dll_path);
    capture.reset();

    let project_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut session = ReplSession::with_project_root(project_root)?;

    // Load the test-capture platform
    let (name, _version, descriptors) = session.jit.load_platform(&dll_path)?;
    session.tc.register_platform(&name, &descriptors)?;
    session.jit.populate_builtin_func_ids(&mut session.tc.modules);

    // Install platform bare names so print/read-line are accessible without import
    session.tc.install_platform_bare_names(&name);

    // Load prelude so we have access to standard library
    session.load_prelude();

    Ok((session, capture))
}

/// Compile and run a program using the given ReplSession.
/// The program must define `main :: (fn [] (IO a))`.
fn compile_and_call_main(
    session: &mut ReplSession,
    src: &str,
) -> Result<(), CranelispError> {
    use cranelisp::ast::TopLevel;
    use cranelisp::ast_builder::build_program;
    use cranelisp::macro_expand::{
        is_defmacro, parse_defmacro, compile_macro,
    };
    use cranelisp::module::CompiledModule;
    use cranelisp::names::{ModuleFullPath, Symbol};
    use cranelisp::sexp::parse_sexps;

    let sexps = parse_sexps(src)?;

    // Compile user macros
    for sexp in &sexps {
        if is_defmacro(sexp) {
            let info = parse_defmacro(sexp)?;
            let ptr = compile_macro(
                &mut session.tc,
                &mut session.jit,
                &info,
                Some(&session.macro_env),
            )?;
            session.macro_env.register(
                info.name,
                ptr,
                info.docstring,
                info.fixed_params,
                info.rest_param,
                Some(info.body_sexp),
            );
        }
    }

    // Expand macros
    let expanded = cranelisp::macro_expand::expand_sexps(sexps, &session.macro_env)?;

    // Build AST
    let items = build_program(&expanded)?;

    let mod_name = session.current_module.short_name().to_string();

    // Ensure current module has a GOT
    {
        let mod_path = ModuleFullPath::from(mod_name.as_str());
        let cm = session.tc.modules.entry(mod_path.clone())
            .or_insert_with(|| CompiledModule::new(mod_path));
        cm.ensure_got();
    }

    // Process each top-level item
    for item in &items {
        match item {
            TopLevel::TypeDef { .. } => {
                session.tc.register_type_def(item);
                session.jit.register_type_defs(&session.tc);
            }
            TopLevel::TraitDecl(td) => {
                for method in &td.methods {
                    session.jit.register_trait_method(&method.name);
                }
                session.tc.register_trait_public(td);
            }
            TopLevel::TraitImpl(ti) => {
                session.tc.validate_impl_public(ti)?;
                session.tc.register_impl(ti);
                let target = ti.impl_target_mangled();
                for method in &ti.methods {
                    let mangled = cranelisp::ast::Defn {
                        visibility: cranelisp::ast::Visibility::Public,
                        name: format!("{}${}", method.name, target),
                        docstring: None,
                        params: method.params.clone(),
                        param_annotations: method.param_annotations.clone(),
                        body: method.body.clone(),
                        span: method.span,
                    };
                    session.tc.check_defn(&mangled)?;
                    let mut mr = session.tc.resolve_methods()?;
                    session.tc.resolve_overloads(&mut mr)?;
                    let et = session.tc.resolve_expr_types();
                    let scheme = session.tc.finalize_defn_type(&mangled.name);
                    {
                        let mod_path = ModuleFullPath::from(mod_name.as_str());
                        if let Some(cm) = session.tc.modules.get_mut(&mod_path) {
                            cm.insert_def(
                                Symbol::from(mangled.name.as_str()),
                                scheme.clone(),
                                cranelisp::ast::Visibility::Public,
                                None,
                            );
                        }
                    }
                    let slot = {
                        let mod_path = ModuleFullPath::from(mod_name.as_str());
                        session.tc.modules.get_mut(&mod_path).unwrap()
                            .allocate_got_slot(mangled.span)?
                    };
                    {
                        let mod_path = ModuleFullPath::from(mod_name.as_str());
                        if let Some(cm) = session.tc.modules.get_mut(&mod_path) {
                            cm.pre_register_for_codegen(&mangled.name, slot, mangled.params.len());
                        }
                    }
                    let fn_slots = session.jit.build_fn_slots_from_modules(&session.tc.modules);
                    let compile_meta = session.jit.compile_defn(
                        &mangled,
                        &scheme,
                        &mr,
                        &et,
                        slot,
                        &fn_slots,
                        &session.tc.modules,
                    )?;
                    {
                        let mod_path = ModuleFullPath::from(mod_name.as_str());
                        if let Some(cm) = session.tc.modules.get_mut(&mod_path) {
                            cm.write_got_slot(slot, compile_meta.code_ptr);
                            cm.update_codegen(&mangled.name, &compile_meta, None, None, Some(&mangled));
                        }
                    }
                }
            }
            TopLevel::Defn(defn) => {
                session.tc.check_defn(defn)?;
                let mut mr = session.tc.resolve_methods()?;
                session.tc.resolve_overloads(&mut mr)?;
                let et = session.tc.resolve_expr_types();
                let scheme = session.tc.finalize_defn_type(&defn.name);
                {
                    let mod_path = ModuleFullPath::from(mod_name.as_str());
                    let cm = session
                        .tc
                        .modules
                        .entry(mod_path.clone())
                        .or_insert_with(|| CompiledModule::new(mod_path));
                    cm.ensure_got();
                    cm.insert_def(
                        Symbol::from(defn.name.as_str()),
                        scheme.clone(),
                        defn.visibility,
                        None,
                    );
                }
                let slot = {
                    let mod_path = ModuleFullPath::from(mod_name.as_str());
                    session.tc.modules.get_mut(&mod_path).unwrap()
                        .allocate_got_slot(defn.span)?
                };
                {
                    let mod_path = ModuleFullPath::from(mod_name.as_str());
                    if let Some(cm) = session.tc.modules.get_mut(&mod_path) {
                        cm.pre_register_for_codegen(&defn.name, slot, defn.params.len());
                    }
                }
                let fn_slots = session.jit.build_fn_slots_from_modules(&session.tc.modules);
                let compile_meta = session.jit.compile_defn(
                    defn,
                    &scheme,
                    &mr,
                    &et,
                    slot,
                    &fn_slots,
                    &session.tc.modules,
                )?;
                {
                    let mod_path = ModuleFullPath::from(mod_name.as_str());
                    if let Some(cm) = session.tc.modules.get_mut(&mod_path) {
                        cm.write_got_slot(slot, compile_meta.code_ptr);
                        cm.update_codegen(&defn.name, &compile_meta, None, None, Some(defn));
                    }
                }
            }
            TopLevel::DefnMulti { .. } => {
                // Not needed for these tests
            }
        }
    }

    // Call main
    session.jit.call_main(&session.tc.modules)
}

// ── Tests ──────────────────────────────────────────────────────────────────

#[test]
fn test_stdio_dll_loads_and_provides_manifest() {
    let dll_path = stdio_dylib_path();
    if !dll_path.exists() {
        eprintln!("stdio DLL not found, skipping test");
        return;
    }

    let mut jit = Jit::new().unwrap();
    let (name, version, descriptors) = jit.load_platform(&dll_path).unwrap();
    assert_eq!(name, "stdio");
    assert_eq!(version, "0.1.0");
    assert_eq!(descriptors.len(), 2);
    assert_eq!(descriptors[0].name, "print");
    assert_eq!(descriptors[1].name, "read-line");
    drop(jit);
}

#[test]
fn test_capture_dll_loads_and_provides_manifest() {
    let dll_path = test_capture_dylib_path();
    if !dll_path.exists() {
        eprintln!("test-capture DLL not found, skipping test");
        return;
    }

    let mut jit = Jit::new().unwrap();
    let (name, version, descriptors) = jit.load_platform(&dll_path).unwrap();
    assert_eq!(name, "test-capture");
    assert_eq!(version, "0.1.0");
    assert_eq!(descriptors.len(), 2);
    assert_eq!(descriptors[0].name, "print");
    assert_eq!(descriptors[0].jit_name, "cranelisp_print");
    assert_eq!(descriptors[1].name, "read-line");
    assert_eq!(descriptors[1].jit_name, "cranelisp_read_line");
    drop(jit);
}

#[test]
fn test_abi_version_matches() {
    let dll_path = test_capture_dylib_path();
    if !dll_path.exists() {
        eprintln!("test-capture DLL not found, skipping test");
        return;
    }

    // If ABI version mismatched, load_platform would return an error.
    // This test verifies successful loading implies matching ABI versions.
    let mut jit = Jit::new().unwrap();
    let result = jit.load_platform(&dll_path);
    assert!(result.is_ok(), "ABI version mismatch: {:?}", result.err());
}

#[test]
fn test_capture_print_hello() {
    let dll_path = test_capture_dylib_path();
    if !dll_path.exists() {
        eprintln!("test-capture DLL not found, skipping test");
        return;
    }

    let (mut session, capture) = build_test_capture_session().unwrap();

    compile_and_call_main(
        &mut session,
        r#"(defn main [] (print "hello"))"#,
    )
    .unwrap();

    let output = capture.get_output();
    assert_eq!(output, "hello");
}

#[test]
fn test_capture_print_multiple_lines() {
    let dll_path = test_capture_dylib_path();
    if !dll_path.exists() {
        eprintln!("test-capture DLL not found, skipping test");
        return;
    }

    let (mut session, capture) = build_test_capture_session().unwrap();

    compile_and_call_main(
        &mut session,
        r#"
        (defn main []
          (do
            (print "line one")
            (print "line two")
            (print "line three")))
        "#,
    )
    .unwrap();

    let output = capture.get_output();
    assert_eq!(output, "line one\nline two\nline three");
}

#[test]
fn test_capture_read_input() {
    let dll_path = test_capture_dylib_path();
    if !dll_path.exists() {
        eprintln!("test-capture DLL not found, skipping test");
        return;
    }

    let (mut session, capture) = build_test_capture_session().unwrap();

    // Pre-configure input: when read-line is called, return "Alice"
    capture.set_input(&["Alice"]);

    compile_and_call_main(
        &mut session,
        r#"
        (defn main []
          (bind! [name (read-line)]
            (print (str "Hello, " name "!"))))
        "#,
    )
    .unwrap();

    let output = capture.get_output();
    assert_eq!(output, "Hello, Alice!");
}

#[test]
fn test_capture_multiple_reads() {
    let dll_path = test_capture_dylib_path();
    if !dll_path.exists() {
        eprintln!("test-capture DLL not found, skipping test");
        return;
    }

    let (mut session, capture) = build_test_capture_session().unwrap();

    // Pre-configure two input lines
    capture.set_input(&["first", "second"]);

    compile_and_call_main(
        &mut session,
        r#"
        (defn main []
          (do
            (bind! [a (read-line)]
              (print a))
            (bind! [b (read-line)]
              (print b))))
        "#,
    )
    .unwrap();

    let output = capture.get_output();
    assert_eq!(output, "first\nsecond");
}

#[test]
fn test_capture_reset_clears_state() {
    let dll_path = test_capture_dylib_path();
    if !dll_path.exists() {
        eprintln!("test-capture DLL not found, skipping test");
        return;
    }

    let (mut session, capture) = build_test_capture_session().unwrap();

    // First run
    compile_and_call_main(
        &mut session,
        r#"(defn main [] (print "first run"))"#,
    )
    .unwrap();

    let output1 = capture.get_output();
    assert_eq!(output1, "first run");

    // Reset
    capture.reset();

    let output2 = capture.get_output();
    assert_eq!(output2, "");
}

#[test]
fn test_capture_empty_input_returns_empty_string() {
    let dll_path = test_capture_dylib_path();
    if !dll_path.exists() {
        eprintln!("test-capture DLL not found, skipping test");
        return;
    }

    let (mut session, capture) = build_test_capture_session().unwrap();

    // No input set — read-line should return empty string
    compile_and_call_main(
        &mut session,
        r#"
        (defn main []
          (bind! [line (read-line)]
            (print (str "got: [" line "]"))))
        "#,
    )
    .unwrap();

    let output = capture.get_output();
    assert_eq!(output, "got: []");
}
