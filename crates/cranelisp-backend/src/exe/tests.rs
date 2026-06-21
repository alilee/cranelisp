use super::*;

// spec: design/backend/executable-generation.md §4 — startup stub generation (no IO)
#[test]
fn generate_startup_object_no_io() {
    let bytes = generate_startup_object(&[], false, "main").unwrap();
    assert!(!bytes.is_empty(), "startup .o should not be empty");
}

// spec: design/backend/executable-generation.md §4 — startup stub with IO trampoline
#[test]
fn generate_startup_object_with_io() {
    let bytes = generate_startup_object(&[], true, "main").unwrap();
    assert!(!bytes.is_empty(), "startup .o should not be empty");
}

// spec: design/backend/executable-generation.md §4 — startup stub with platform init
#[test]
fn generate_startup_object_with_platform() {
    let manifest_names = vec!["cranelisp_platform_manifest_shapes".to_string()];
    let bytes = generate_startup_object(&manifest_names, false, "main").unwrap();
    assert!(!bytes.is_empty(), "startup .o should not be empty");
}

// spec: design/backend/executable-generation.md §4 — startup stub with platform + IO
#[test]
fn generate_startup_object_with_platform_and_io() {
    let manifest_names = vec!["cranelisp_platform_manifest_shapes".to_string()];
    let bytes = generate_startup_object(&manifest_names, true, "main").unwrap();
    assert!(!bytes.is_empty(), "startup .o should not be empty");
}

// spec: design/backend/executable-generation.md §4 — startup stub with module-qualified entry
#[test]
fn generate_startup_object_qualified_entry() {
    let bytes = generate_startup_object(&[], false, "hello/main").unwrap();
    assert!(!bytes.is_empty(), "startup .o with qualified entry should not be empty");
}

// spec: design/arch/platform-interface.md §5.5.4 `--link` gate / §7.3 — the
//       startup object bakes a per-platform layout-hash check (expected hash
//       + name as rodata) and a `cranelisp_check_layout_hash` call. The
//       emitted `.o` is non-empty and strictly larger than the no-check
//       baseline (the baked data + compare call add bytes).
#[test]
fn generate_startup_object_bakes_layout_check() {
    let manifest_names = vec!["cranelisp_platform_manifest_shapes".to_string()];
    let baseline = generate_startup_object(&manifest_names, false, "main").unwrap();

    let checks = vec![PlatformLayoutCheck {
        name: "shapes".to_string(),
        expected_hash: "deadbeefcafef00d".to_string(),
    }];
    let checked = generate_startup_object_checked(
        &manifest_names,
        false,
        "main",
        &checks,
    )
    .unwrap();

    assert!(!checked.is_empty(), "checked startup .o should not be empty");
    assert!(
        checked.len() > baseline.len(),
        "baking the layout-hash check + rodata must enlarge the .o \
         (checked={}, baseline={})",
        checked.len(),
        baseline.len(),
    );
    // The baked expected-hash string + the imported linked-hash symbol name
    // appear verbatim in the object bytes.
    let needle_hash = b"deadbeefcafef00d";
    assert!(
        checked
            .windows(needle_hash.len())
            .any(|w| w == needle_hash),
        "the baked expected hash must appear in the .o rodata",
    );
    let needle_sym = b"__cranelisp_layout_hash_shapes";
    assert!(
        checked
            .windows(needle_sym.len())
            .any(|w| w == needle_sym),
        "the imported linked-hash symbol must appear in the .o symbol table",
    );
}

// spec: design/arch/platform-interface.md §5.5.4 — the back-compat
//       `generate_startup_object` emits no layout check (the as-built
//       `--link` path); equivalent to the checked variant with no checks.
#[test]
fn generate_startup_object_no_checks_matches_wrapper() {
    let with_empty =
        generate_startup_object_checked(&[], false, "main", &[]).unwrap();
    let wrapper = generate_startup_object(&[], false, "main").unwrap();
    assert_eq!(
        with_empty, wrapper,
        "the wrapper is the no-check variant",
    );
}
