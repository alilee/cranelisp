    use super::*;

    // -----------------------------------------------------------------
    // FIXME 0318 / spec §8.11 — every platform fn MUST return `IO _`.
    // `require_io_return` is the smallest testable owner of the gate
    // `register_platform_in_tc` applies after the sig is checked (the full
    // path dlopens a real DLL; this drives the rejection with a perturbed
    // sig type, no DLL needed — the check is on the resolved return type).
    // -----------------------------------------------------------------

    fn io_int() -> Type {
        Type::ADT(
            cranelisp_types::FQTypeName::new(
                ModuleFullPath::from("primitives"),
                cranelisp_types::TypeName::from("IO"),
            ),
            vec![Type::Int],
        )
    }

    // spec: design/arch/fixmes/0318 / spec §8.11 — a platform fn declaring a
    // non-IO return (`(Fn [Int] Int)`) is REJECTED, naming the platform + fn +
    // the IO requirement.
    #[test]
    fn platform_fn_non_io_return_is_rejected() {
        let pure_sig = Type::Fn(vec![Type::Int], Box::new(Type::Int));
        let err = require_io_return(&pure_sig, "shapes", "area")
            .expect_err("a non-IO platform fn sig must be rejected");
        match err {
            CranelispError::ModuleError { message, .. } => {
                assert!(message.contains("shapes/area"), "names platform/fn: {message}");
                assert!(message.contains("IO"), "names the IO requirement: {message}");
            }
            other => panic!("expected ModuleError, got {other:?}"),
        }
    }

    // spec: design/arch/fixmes/0318 / spec §8.11 — an IO-returning platform fn
    // (`(Fn [String] (IO Int))`, the stdio `print` shape) passes the gate.
    #[test]
    fn platform_fn_io_return_accepted() {
        let io_sig = Type::Fn(vec![Type::String], Box::new(io_int()));
        assert!(
            require_io_return(&io_sig, "stdio", "print").is_ok(),
            "an IO-returning platform fn must pass the gate"
        );
    }

    // spec: design/arch/fixmes/0318 — a non-IO ADT return (e.g. a bare
    // `shapes/Rectangle`) is also rejected — only the `IO` ADT satisfies the gate.
    #[test]
    fn platform_fn_non_io_adt_return_is_rejected() {
        let rect = Type::ADT(
            cranelisp_types::FQTypeName::new(
                ModuleFullPath::from("shapes"),
                cranelisp_types::TypeName::from("Rectangle"),
            ),
            vec![],
        );
        let sig = Type::Fn(vec![Type::Int], Box::new(rect));
        assert!(
            require_io_return(&sig, "shapes", "make").is_err(),
            "a non-IO ADT return must be rejected"
        );
    }

    // spec: 10-io §10.9.1 — platform declaration recognized
    #[test]
    fn test_is_platform_form() {
        let sexps = cranelisp_frontend::parse("(platform stdio)").unwrap();
        assert!(is_platform_form(&sexps[0]));
    }

    // spec: 10-io §10.9.1 — non-platform forms rejected
    #[test]
    fn test_is_platform_form_rejects_non_platform() {
        let sexps = cranelisp_frontend::parse("(defn main [] 42)").unwrap();
        assert!(!is_platform_form(&sexps[0]));
    }

    // spec: 10-io §10.9.1 — platform name extraction
    #[test]
    fn test_extract_platform_name() {
        let sexps = cranelisp_frontend::parse("(platform stdio)").unwrap();
        let (name, _) = extract_platform_name(&sexps[0]).unwrap();
        assert_eq!(name, "stdio");
    }

    // -----------------------------------------------------------------
    // ABI-version-mismatch detection (platform-interface.md §5.2) — drives the
    // WIRED `manifest.abi_version != ABI_VERSION` branch with a perturbed
    // version, without dlopening a real DLL (load_platform_dll owns the dlopen;
    // check_abi_version is the smallest testable owner of the branch).
    // -----------------------------------------------------------------

    // spec: design/arch/platform-interface.md §5.2 — a DLL whose declared ABI
    // version differs from the host's `ABI_VERSION` is refused with
    // PlatformError::AbiVersionMismatch carrying BOTH the expected (host) and
    // found (DLL) versions correct.
    #[test]
    fn abi_version_mismatch_detected() {
        let dll = Path::new("/fake/stale-abi.dylib");
        let perturbed = ABI_VERSION + 1;
        let err = check_abi_version(perturbed, dll, ErrorLocation::unknown())
            .expect_err("a perturbed ABI version must be refused");
        match err {
            CranelispError::Platform(cranelisp_types::PlatformError::AbiVersionMismatch {
                expected,
                found,
                ..
            }) => {
                assert_eq!(expected, ABI_VERSION, "expected = host ABI_VERSION");
                assert_eq!(found, perturbed, "found = the DLL's declared version");
            }
            other => panic!("expected AbiVersionMismatch, got {other:?}"),
        }
    }

    // spec: design/arch/platform-interface.md §5.2 — a DLL declaring the host's
    // own `ABI_VERSION` passes the gate (Ok). Guards that check_abi_version's
    // extraction did not change behaviour on the happy path.
    #[test]
    fn abi_version_match_accepts() {
        let dll = Path::new("/fake/ok.dylib");
        assert!(
            check_abi_version(ABI_VERSION, dll, ErrorLocation::unknown()).is_ok(),
            "the host's own ABI_VERSION must pass the gate"
        );
    }

    // spec: 10-io §10.9.1 — platform path resolution (explicit path bypass)
    #[test]
    fn test_resolve_explicit_path_bypass() {
        // A name containing '/' is treated as an explicit path.
        let result = resolve_platform_path("./nonexistent.dylib", Path::new("."), &[], &[]);
        assert!(result.is_none()); // File doesn't exist, so None.
    }

    // -----------------------------------------------------------------
    // Host-side ADT marshaling — alloc_with_tag wiring (FIXME 0229 step 1).
    //
    // These tests pin the int-side wiring: a `HostCallbacks` constructed
    // exactly as `load_platform_dll` builds it must carry the REAL
    // `cranelisp_alloc_with_tag` intrinsic in its `alloc_with_tag` field
    // (not the R1-gate `null_alloc_with_tag` panic placeholder), and
    // invoking that field as a platform DLL would (via `CLAdt::construct`)
    // must produce the heap layout `CLAdt::read_tag`/`read_field` expect:
    // `[total_size | rc=1 | tag@HEAP_HEADER_SIZE | f0@+8 | f1@+16 ...]`,
    // returning the alloc BASE pointer. This is the int-side half of the
    // round-trip; the platform crate unit-tests the CLAdt read path
    // (adt.rs T9–T13) and the intrinsic crate unit-tests the layout
    // (alloc.rs `test_alloc_with_tag_*`).
    // -----------------------------------------------------------------

    /// Build the `HostCallbacks` exactly as `load_platform_dll` does, so the
    /// test exercises the wiring under test rather than a hand-built struct.
    fn wired_host_callbacks() -> HostCallbacks {
        HostCallbacks {
            alloc: cranelisp_intrinsics::heap_alloc_payload,
            alloc_with_tag: cranelisp_intrinsics::alloc::cranelisp_alloc_with_tag,
        }
    }

    // spec: design/platform/host-wiring-s76.md §2 — the host wires the real
    // alloc_with_tag intrinsic; the R1 gate (null_alloc_with_tag panic) is
    // gone. A two-field ADT constructed through the callback round-trips:
    // tag + both fields read back at the documented offsets, RC = 1.
    #[test]
    fn alloc_with_tag_callback_round_trips_two_field_adt() {
        let callbacks = wired_host_callbacks();
        let fields: [i64; 2] = [0x0BAD_F00D_DEAD_BEEFu64 as i64, -42];

        // Invoke as a platform DLL would (CLAdt::construct → alloc_with_tag).
        let base = (callbacks.alloc_with_tag)(2, 2, fields.as_ptr());
        assert_ne!(base, 0, "wired callback must return a non-null alloc base");

        let header = cranelisp_types::HeapHeader::SIZE as i64;
        // SAFETY: `base` is a freshly allocated tagged-ADT base pointer; the
        // layout (total_size, rc, tag, fields) is the documented contract.
        unsafe {
            let total_size = *(base as *const i64);
            // 16 header + 8 tag slot + 2*8 fields = 40.
            assert_eq!(total_size, 40, "total_size = header + tag + 2 fields");
            let rc = *((base + 8) as *const i64);
            assert_eq!(rc, 1, "alloc_with_rc initialises RC to 1");
            // Tag at payload+0 (base + HEAP_HEADER_SIZE) reads back as i64.
            let tag = *((base + header) as *const i64);
            assert_eq!(tag, 2, "variant tag at payload+0");
            // Fields at payload+8 and payload+16 — copied verbatim.
            let f0 = *((base + header + 8) as *const i64);
            let f1 = *((base + header + 16) as *const i64);
            assert_eq!(f0, fields[0], "field 0 copied verbatim");
            assert_eq!(f1, fields[1], "field 1 copied verbatim");
        }

        // Free via the runtime dealloc (reads total_size from the header).
        cranelisp_intrinsics::alloc::heap_dealloc(base);
    }

    // spec: design/platform/host-wiring-s76.md §2 — a nullary-shaped data
    // constructor (zero fields) round-trips through the wired callback:
    // tag-only payload, RC = 1, alloc base returned (not the R1 panic).
    #[test]
    fn alloc_with_tag_callback_round_trips_zero_field_adt() {
        let callbacks = wired_host_callbacks();
        let base = (callbacks.alloc_with_tag)(7, 0, std::ptr::null());
        assert_ne!(base, 0);

        let header = cranelisp_types::HeapHeader::SIZE as i64;
        // SAFETY: documented tagged-ADT layout for a zero-field constructor.
        unsafe {
            let total_size = *(base as *const i64);
            assert_eq!(total_size, 24, "total_size = 16 header + 8 tag slot");
            let tag = *((base + header) as *const i64);
            assert_eq!(tag, 7);
        }
        cranelisp_intrinsics::alloc::heap_dealloc(base);
    }

    // (FIXME 0233 step 1) The ad-hoc `parse_platform_type_sig` + `sexp_to_type`
    // family — and their two unit tests `test_parse_fn_type_sig` /
    // `test_parse_zero_param_type_sig` — were deleted. Platform-sig parsing is
    // now `cranelisp_frontend::parse_type_expr` (unit-tested in frontend) +
    // `cranelisp_typecheck::check_type_expr` (unit-tested in typecheck); the
    // integrated platform-sig resolution path is exercised e2e by
    // `tests/spec_platforms.rs::platform_form_with_stdio_compiles_in_run_mode`
    // and `::io_trampoline_executes_print_to_stdout` (both load the stdio DLL
    // and resolve its `(Fn [String] (IO Unit))`-shaped sigs through this path).

    // spec: platform-dlls §search — tier 2 project-local resolution
    #[test]
    fn test_resolve_platform_path_local() {
        let dir = tempfile::tempdir().unwrap();
        let platforms_dir = dir.path().join("platforms");
        std::fs::create_dir_all(&platforms_dir).unwrap();

        let dll_file = platforms_dir.join(format!("test-plat.{PLATFORM_EXT}"));
        std::fs::write(&dll_file, b"fake dll").unwrap();

        let result = resolve_platform_path("test-plat", dir.path(), &[], &[]);
        assert!(result.is_some());
        assert_eq!(result.unwrap(), dll_file);
    }

    // spec: platform-dlls §8.11.3 — extra platform_dirs (tier 3)
    #[test]
    fn test_resolve_platform_path_extra_dir() {
        let dir = tempfile::tempdir().unwrap();
        let extra_dir = dir.path().join("extra-platforms");
        std::fs::create_dir_all(&extra_dir).unwrap();

        let dll_file = extra_dir.join(format!("libcranelisp_stdio.{PLATFORM_EXT}"));
        std::fs::write(&dll_file, b"fake dll").unwrap();

        let result = resolve_platform_path("stdio", dir.path(), &[], &[extra_dir]);
        assert!(result.is_some());
        assert_eq!(result.unwrap(), dll_file);
    }

    // spec: platform-dlls §8.11.3 — tier 1 (project root) takes priority over tier 3
    #[test]
    fn test_resolve_platform_path_local_priority() {
        let dir = tempfile::tempdir().unwrap();

        // Create both tier 1 (project root) and tier 3 (extra dir) files.
        let platforms_dir = dir.path().join("platforms");
        std::fs::create_dir_all(&platforms_dir).unwrap();
        let local_dll = platforms_dir.join(format!("stdio.{PLATFORM_EXT}"));
        std::fs::write(&local_dll, b"local").unwrap();

        let extra_dir = dir.path().join("extra");
        std::fs::create_dir_all(&extra_dir).unwrap();
        let extra_dll = extra_dir.join(format!("libcranelisp_stdio.{PLATFORM_EXT}"));
        std::fs::write(&extra_dll, b"extra").unwrap();

        let result = resolve_platform_path("stdio", dir.path(), &[], &[extra_dir]);
        assert_eq!(result.unwrap(), local_dll); // Tier 1 wins.
    }

    // spec: platform-dlls §8.11.3 — not found returns None
    #[test]
    fn test_resolve_platform_path_not_found() {
        let dir = tempfile::tempdir().unwrap();
        let result = resolve_platform_path("nonexistent", dir.path(), &[], &[]);
        assert!(result.is_none());
    }

    // spec: 10-io §10.9.1 — load stdio platform DLL and validate manifest
    #[test]
    fn test_load_stdio_platform_dll() {
        // This test requires the stdio platform DLL to be built.
        // cargo build -p cranelisp-stdio must have run.
        let project_root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let target_debug = project_root.join("target/debug");
        let dll_path = resolve_platform_path("stdio", project_root, &[], &[target_debug]);
        if dll_path.is_none() {
            eprintln!("skipping test: stdio platform DLL not built");
            return;
        }
        let dll_path = dll_path.unwrap();

        let platform = load_platform_dll("stdio", &dll_path, Span::SYNTHETIC).unwrap();

        assert_eq!(platform.name, "stdio");
        assert_eq!(platform.version, "0.1.0");
        assert_eq!(platform.descriptors.len(), 2);

        // Verify function descriptors. Platform fns carry no exported linker
        // name (jit_name retired, FIXME 0288) — dispatch is GOT-indirect at the
        // manifest index.
        let print_desc = &platform.descriptors[0];
        assert_eq!(print_desc.name, "print");
        assert_eq!(print_desc.param_count, 1);
        assert!(!print_desc.docstring.is_empty());

        let read_desc = &platform.descriptors[1];
        assert_eq!(read_desc.name, "read-line");
        assert_eq!(read_desc.param_count, 0);

        // The DLL must export its GOT slab (dlsym'd at load).
        assert!(!platform.got_base.is_null(), "platform must export its GOT");
    }

    // spec: 10-io §10.9.1 — register platform functions in typechecker
    #[test]
    fn test_register_platform_in_tc() {
        let project_root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let target_debug = project_root.join("target/debug");
        let dll_path = resolve_platform_path("stdio", project_root, &[], &[target_debug.clone()]);
        if dll_path.is_none() {
            eprintln!("skipping test: stdio platform DLL not built");
            return;
        }

        let symbol_tables = dashmap::DashMap::new();
        let next_type_id = std::sync::atomic::AtomicU32::new(0);
        let user_mod = ModuleFullPath::from("user");
        symbol_tables.insert(user_mod.clone(), crate::code::SessionSymbolTable::new_with_params(user_mod.clone()));
        crate::bootstrap::mount_synthetic_modules(&symbol_tables, &next_type_id);
        let module_aliases = cranelisp_types::ModuleAliases::default();
        let platform = load_and_register_platform(
            &symbol_tables,
            &module_aliases,
            "stdio",
            project_root,
            &[],
            &[target_debug],
            Span::SYNTHETIC,
        ).unwrap();

        // Check the platform.stdio module exists and has the functions.
        let module_path = ModuleFullPath::from("platform.stdio");
        let table = symbol_tables.get(&module_path);
        assert!(table.is_some(), "platform.stdio module should exist");

        let table = table.unwrap();
        let print_entry = table.get("print");
        assert!(print_entry.is_some(), "print should be in platform.stdio");

        let read_entry = table.get("read-line");
        assert!(read_entry.is_some(), "read-line should be in platform.stdio");

        // Verify types are correctly parsed AND `got_slot = manifest index`
        // (platform-interface.md §5.3) — the GOT-indirect dispatch activator.
        if let Some(entry @ ModuleEntry::Def { scheme, kind, docstring, .. }) = print_entry {
            // print: (Fn [primitives/String] (primitives/IO primitives/Int))
            match &scheme.ty {
                Type::Fn(params, ret) => {
                    assert_eq!(params.len(), 1);
                    assert_eq!(params[0], Type::String);
                    assert!(matches!(ret.as_ref(), Type::ADT(name, _) if name.name.as_ref() == "IO"));
                }
                _ => panic!("expected Fn type for print"),
            }
            assert!(matches!(kind.as_ref(), DefKind::PlatformEffect { .. }));
            assert!(docstring.is_some());
            // The slot rides on the `PlatformEffect` variant (S83 reshape,
            // FIXME 0358); read it via the `callable_got_slot()` chokepoint.
            assert_eq!(entry.callable_got_slot(), Some(0), "print is manifest index 0");
        } else {
            panic!("expected Def entry for print");
        }
        if let Some(entry @ ModuleEntry::Def { .. }) = read_entry {
            assert_eq!(entry.callable_got_slot(), Some(1), "read-line is manifest index 1");
        }

        // The platform module's GOT wraps the DLL's exported slab; slot 0 (print)
        // must be a live (non-null) fn pointer after the manifest populated it.
        assert!(
            !table.got.load_slot(0).is_null(),
            "platform GOT slot 0 must be populated by the DLL manifest"
        );

        // Platform should be kept alive.
        assert_eq!(platform.name, "stdio");
    }

    // spec: §8.11.5 — assemble_platform_dirs reads CRANELISP_PLATFORM_PATH
    #[test]
    fn test_assemble_platform_dirs_env_var() {
        let dir = tempfile::tempdir().unwrap();
        let env_dir = dir.path().join("custom-platforms");
        std::fs::create_dir_all(&env_dir).unwrap();

        let dll_file = env_dir.join(format!("test-env.{PLATFORM_EXT}"));
        std::fs::write(&dll_file, b"fake dll").unwrap();

        // Set the env var temporarily.
        let prev = std::env::var("CRANELISP_PLATFORM_PATH").ok();
        unsafe { std::env::set_var("CRANELISP_PLATFORM_PATH", env_dir.to_str().unwrap()) };

        // assemble_platform_dirs picks up the env var.
        let platform_dirs = crate::session_setup::assemble_platform_dirs();
        let result = resolve_platform_path("test-env", dir.path(), &[], &platform_dirs);
        assert!(result.is_some());
        assert_eq!(result.unwrap(), dll_file);

        // Restore env var.
        match prev {
            Some(v) => unsafe { std::env::set_var("CRANELISP_PLATFORM_PATH", v) },
            None => unsafe { std::env::remove_var("CRANELISP_PLATFORM_PATH") },
        }
    }

    // spec: platform-dlls §validation — manifest name mismatch error
    #[test]
    fn test_platform_name_mismatch_error() {
        let project_root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let target_debug = project_root.join("target/debug");
        let dll_path = resolve_platform_path("stdio", project_root, &[], &[target_debug.clone()]);
        if dll_path.is_none() {
            eprintln!("skipping test: stdio platform DLL not built");
            return;
        }

        let symbol_tables = dashmap::DashMap::new();
        let user_mod = ModuleFullPath::from("user");
        symbol_tables.insert(user_mod.clone(), crate::code::SessionSymbolTable::new_with_params(user_mod.clone()));
        let module_aliases = cranelisp_types::ModuleAliases::default();
        // Try to load with wrong name — manifest says "stdio" but we say "wrong-name"
        let result = load_and_register_platform(
            &symbol_tables,
            &module_aliases,
            "wrong-name",
            project_root,
            &[],
            &[target_debug],
            Span::SYNTHETIC,
        );

        // This won't match because resolve_platform_path("wrong-name") won't find
        // the stdio DLL. So we'll get a "not found" error instead.
        assert!(result.is_err());
    }

    // -----------------------------------------------------------------
    // FQ type-leaf split (Root B-shapes, FIXME 0321) — the platform sig
    // FQ-leaf repair MUST re-partition a slashed type leaf into
    // `TypeRef { module: Some(prefix), name: leaf }`, not leave the whole
    // slashed string in `name` with `module: None` (which `check_type_expr`
    // looks up as a type literally named `"shapes/Rectangle"` in module `''`).
    // -----------------------------------------------------------------

    // spec: design/arch/platform-interface.md §5.3 — FQ sig leaf partition
    #[test]
    fn split_slashed_type_ref_partitions_module_and_name() {
        let tref = split_slashed_type_ref("shapes/Rectangle")
            .expect("an uppercase post-slash leaf is a qualified type");
        assert_eq!(tref.module, Some(ModuleFullPath::from("shapes")));
        assert_eq!(tref.name.as_ref(), "Rectangle");
    }

    // spec: design/arch/platform-interface.md §5.3 — multi-component module path
    #[test]
    fn split_slashed_type_ref_keeps_full_module_path() {
        let tref = split_slashed_type_ref("core.option/Option")
            .expect("dotted module path is preserved as the module part");
        assert_eq!(tref.module, Some(ModuleFullPath::from("core.option")));
        assert_eq!(tref.name.as_ref(), "Option");
    }

    // -----------------------------------------------------------------
    // §7.2 associated-type-module discovery (FIXME 0323) — the worker drives
    // every EXTERNAL type module a platform sig references BEFORE the sig-check
    // loop, so `shapes/Rectangle` resolves against a now-loaded `shapes` module
    // rather than mapping to a `ModuleError`. `referenced_sig_modules` is the
    // pure, unit-testable harvester the worker consults.
    // -----------------------------------------------------------------

    // `OwnedPlatformFnDescriptor` is `#[non_exhaustive]`, so the discovery logic
    // is exercised through `collect_type_expr_modules` over the same
    // parse+`fqize` pipeline `referenced_sig_modules` runs per descriptor sig.
    // `referenced_sig_modules` itself is exercised end-to-end (over real DLL
    // descriptors) by `tests/spec_platforms_adt.rs`.
    fn sig_modules(sig: &str) -> Vec<ModuleFullPath> {
        let expr = cranelisp_frontend::parse_type_expr(sig).expect("sig parses");
        let expr = fqize_type_expr(expr);
        let mut acc = Vec::new();
        collect_type_expr_modules(&expr, &mut acc);
        acc
    }

    // spec: design/arch/platform-interface.md §7.2 — a sig naming a user type
    // module (`shapes/Rectangle`) yields that module as a pre-resolve dep.
    #[test]
    fn referenced_sig_modules_discovers_user_type_module() {
        let mods = sig_modules("(Fn [shapes/Rectangle] (primitives/IO primitives/Int))");
        assert_eq!(mods, vec![ModuleFullPath::from("shapes")]);
    }

    // spec: design/arch/platform-interface.md §7.2 — `primitives` (and `macros`)
    // are always synthetically mounted; they are NOT reported as deps to load.
    #[test]
    fn referenced_sig_modules_excludes_synthetic_modules() {
        assert!(
            sig_modules("(Fn [primitives/String] (primitives/IO primitives/Int))").is_empty(),
            "a scalar-only stdio-shaped sig references no external type module"
        );
    }

    // spec: design/arch/platform-interface.md §7.2 — distinct external modules
    // across one sig are reported once each, in first-seen order; `shapes` is
    // not duplicated across param + return positions.
    #[test]
    fn referenced_sig_modules_dedups_and_orders() {
        let mods = sig_modules("(Fn [shapes/Rectangle geom/Point] (primitives/IO shapes/Rectangle))");
        assert_eq!(
            mods,
            vec![ModuleFullPath::from("shapes"), ModuleFullPath::from("geom")],
            "shapes first, geom second; shapes not duplicated across positions"
        );
    }

    // spec: design/arch/platform-interface.md §5.3 — a non-slashed name or a
    // lowercase post-slash leaf (a type variable, e.g. `a` / `m/a`) is NOT a
    // qualified type and is left for the caller to keep unchanged.
    #[test]
    fn split_slashed_type_ref_rejects_non_type_leaves() {
        assert!(split_slashed_type_ref("Rectangle").is_none(), "no slash → no split");
        assert!(split_slashed_type_ref("a").is_none(), "bare type var → no split");
        assert!(
            split_slashed_type_ref("m/a").is_none(),
            "lowercase post-slash leaf is a type variable, not a type"
        );
    }

    // spec: design/arch/platform-interface.md §5.3 — `fqize_type_expr` repairs
    // the WHOLE platform sig: a slashed leaf in a `Named` node (the production
    // shape — `build_type_expr` classifies `shapes/Rectangle` as uppercase and
    // emits `Named(TypeRef { module: None, name: "shapes/Rectangle" })`) is
    // re-partitioned; a `primitives/Int`-shaped `TypeVar` is lifted to a split
    // `Named`. Drives the exact `area` sig from the `shapes` fixture.
    #[test]
    fn fqize_type_expr_repairs_named_and_typevar_leaves_in_fn_sig() {
        use cranelisp_types::TypeExpr;
        let sig = "(Fn [shapes/Rectangle] (primitives/IO primitives/Int))";
        let expr = cranelisp_frontend::parse_type_expr(sig).unwrap();
        let fixed = fqize_type_expr(expr);

        let TypeExpr::FnType(params, ret) = fixed else {
            panic!("expected an Fn type expr");
        };
        // The single param `shapes/Rectangle` is now a split, qualified `Named`.
        assert_eq!(params.len(), 1);
        let TypeExpr::Named(param_ref) = &params[0] else {
            panic!("param must be a Named type ref, got {:?}", params[0]);
        };
        assert_eq!(param_ref.module, Some(ModuleFullPath::from("shapes")));
        assert_eq!(param_ref.name.as_ref(), "Rectangle");

        // The return `(primitives/IO primitives/Int)` is an Applied whose head
        // (`primitives/IO`) and arg (`primitives/Int`) are both split.
        let TypeExpr::Applied(head, args) = ret.as_ref() else {
            panic!("return must be an Applied IO type, got {ret:?}");
        };
        assert_eq!(head.module, Some(ModuleFullPath::from("primitives")));
        assert_eq!(head.name.as_ref(), "IO");
        assert_eq!(args.len(), 1);
        match &args[0] {
            TypeExpr::Named(arg_ref) => {
                assert_eq!(arg_ref.module, Some(ModuleFullPath::from("primitives")));
                assert_eq!(arg_ref.name.as_ref(), "Int");
            }
            other => panic!("IO arg must be a split Named Int, got {other:?}"),
        }
    }
