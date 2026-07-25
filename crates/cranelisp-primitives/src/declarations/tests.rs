use std::collections::HashSet;
use std::fs;
use std::path::Path;

use cranelisp_types::{DefKind, ModuleEntry, ModuleFullPath, PrimitiveBody, SymbolTable};

use super::{PrimitiveDecl, build_table, declarations, harvest_shims};

#[test]
fn production_inventory_projects_both_ways() {
    let declarations = declarations();
    let mut table = SymbolTable::<(), ()>::new_with_params(ModuleFullPath::from("test"));
    build_table(&mut table, &declarations);
    let harvest = harvest_shims(&declarations);

    let declared_users: HashSet<_> = declarations
        .iter()
        .filter_map(|row| match row {
            PrimitiveDecl::UserExtern { name, .. } | PrimitiveDecl::UserInline { name, .. } => {
                Some(*name)
            }
            PrimitiveDecl::HarvestExtern { .. } => None,
        })
        .collect();
    let table_names: HashSet<_> = table.symbols.keys().map(AsRef::as_ref).collect();
    assert_eq!(declared_users, table_names);

    let declared_externs: HashSet<_> = declarations
        .iter()
        .filter_map(|row| match row {
            PrimitiveDecl::UserExtern { name, .. } | PrimitiveDecl::HarvestExtern { name, .. } => {
                Some(*name)
            }
            PrimitiveDecl::UserInline { .. } => None,
        })
        .collect();
    let harvested: HashSet<_> = harvest.keys().copied().collect();
    assert_eq!(declared_externs, harvested);
}

#[test]
fn all_three_legal_variants_have_the_expected_got_shape() {
    let declarations = declarations();
    let mut table = SymbolTable::<(), ()>::new_with_params(ModuleFullPath::from("test"));
    build_table(&mut table, &declarations);

    let mut seen = [false; 3];
    for row in &declarations {
        match row {
            PrimitiveDecl::UserExtern { name, shim, .. } => {
                seen[0] = true;
                let slot = table.get(name).unwrap().callable_got_slot().unwrap();
                assert_eq!(table.got.load_slot(slot), *shim);
            }
            PrimitiveDecl::UserInline { name, .. } => {
                seen[1] = true;
                assert!(table.get(name).unwrap().callable_got_slot().is_none());
            }
            PrimitiveDecl::HarvestExtern { name, .. } => {
                seen[2] = true;
                assert!(table.get(name).is_none());
            }
        }
    }
    assert_eq!(seen, [true; 3]);
}

#[test]
fn every_callable_declaration_has_ownership_and_primitive_kind() {
    let declarations = declarations();
    let mut table = SymbolTable::<(), ()>::new_with_params(ModuleFullPath::from("test"));
    build_table(&mut table, &declarations);
    for row in declarations {
        let (name, ownership) = match row {
            PrimitiveDecl::UserExtern {
                name, ownership, ..
            }
            | PrimitiveDecl::UserInline {
                name, ownership, ..
            } => (name, ownership),
            PrimitiveDecl::HarvestExtern { .. } => continue,
        };
        assert!(!ownership.param_modes.is_empty());
        let ModuleEntry::Def { kind, .. } = table.get(name).unwrap() else {
            panic!("callable row did not project to a definition");
        };
        assert!(matches!(
            **kind,
            DefKind::Primitive {
                body: PrimitiveBody::Inline | PrimitiveBody::Extern { .. },
                mode_summary: Some(_),
            }
        ));
    }
}

#[test]
#[should_panic(expected = "duplicate primitive declaration")]
fn duplicate_callable_name_hard_fails_table_construction() {
    let mut declarations = declarations();
    let duplicate = declarations
        .iter()
        .find(|row| matches!(row, PrimitiveDecl::UserExtern { .. }))
        .unwrap()
        .clone();
    declarations.push(duplicate);
    let mut table = SymbolTable::<(), ()>::new_with_params(ModuleFullPath::from("test"));
    build_table(&mut table, &declarations);
}

#[test]
#[should_panic(expected = "duplicate harvested primitive")]
fn duplicate_extern_name_hard_fails_harvest() {
    let mut declarations = declarations();
    let duplicate = declarations
        .iter()
        .find(|row| matches!(row, PrimitiveDecl::UserExtern { .. }))
        .unwrap()
        .clone();
    declarations.push(duplicate);
    let _ = harvest_shims(&declarations);
}

#[test]
fn primitive_function_exports_exist_only_in_the_declaration_macro() {
    fn visit(path: &Path, hits: &mut Vec<(String, String)>) {
        for entry in fs::read_dir(path).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                visit(&path, hits);
            } else if path.extension().and_then(|ext| ext.to_str()) == Some("rs") {
                for line in fs::read_to_string(&path).unwrap().lines() {
                    if line.trim_start().starts_with("#[unsafe(export_name") {
                        hits.push((path.display().to_string(), line.trim().to_owned()));
                    }
                }
            }
        }
    }

    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut hits = Vec::new();
    visit(&root, &mut hits);
    assert_eq!(
        hits.len(),
        3,
        "unexpected direct export attributes: {hits:?}"
    );
    assert_eq!(
        hits.iter()
            .filter(|(path, _)| path.ends_with("declaration_macro.rs"))
            .count(),
        2,
        "both primitive wrapper export templates must live in declaration_macro.rs"
    );
    assert!(
        hits.iter().any(|(path, line)| {
            path.ends_with("lib.rs") && line.contains("__cranelisp_got_primitives")
        }),
        "the static GOT slab must be the sole direct non-macro export"
    );
}

fn fixture_line(row: &PrimitiveDecl) -> String {
    match row {
        PrimitiveDecl::UserExtern {
            name,
            scheme,
            param_names,
            docstring,
            ownership,
            shim_name,
            ..
        } => format!(
            "{name}|user-extern|{scheme:?}|{param_names:?}|{docstring:?}|{ownership:?}|{shim_name}"
        ),
        PrimitiveDecl::UserInline {
            name,
            scheme,
            param_names,
            docstring,
            ownership,
        } => format!("{name}|user-inline|{scheme:?}|{param_names:?}|{docstring:?}|{ownership:?}|-"),
        PrimitiveDecl::HarvestExtern {
            name, shim_name, ..
        } => format!("{name}|harvest-extern|-|-|-|-|{shim_name}"),
    }
}

#[test]
fn full_pre_migration_projection_fixture_is_unchanged() {
    let actual = declarations()
        .iter()
        .map(fixture_line)
        .collect::<Vec<_>>()
        .join("\n");
    assert_eq!(
        actual.trim(),
        include_str!("pre_migration_projection.txt").trim()
    );
}

#[test]
fn malformed_declaration_rows_do_not_compile() {
    use std::process::Command;

    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let out_dir =
        std::env::temp_dir().join(format!("cranelisp-primitives-ui-{}", std::process::id()));
    fs::create_dir_all(&out_dir).unwrap();
    for (case, expected) in [
        ("extern_without_shim.rs", "no rules expected `metadata`"),
        ("harvest_only_inline.rs", "no rules expected `metadata`"),
        ("callable_without_ownership.rs", "no rules expected `}`"),
    ] {
        let source = manifest.join("src/declarations/ui").join(case);
        let output = Command::new("rustc")
            .arg("--edition=2024")
            .arg(&source)
            .arg("--out-dir")
            .arg(&out_dir)
            .output()
            .unwrap();
        assert!(!output.status.success(), "{case} unexpectedly compiled");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains(expected),
            "{case} failed for the wrong reason; expected {expected:?}, got:\n{stderr}"
        );
    }
    fs::remove_dir_all(out_dir).unwrap();
}
