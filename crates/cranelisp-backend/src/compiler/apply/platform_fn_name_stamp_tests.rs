use std::collections::HashMap;

use super::{EFFECT_FN_NAME_ABS_OFFSET, PURE_GLUE_ABS_OFFSET, platform_fn_name_bytes};
use crate::test_support::*;
use cranelift_module::{FuncOrDataId, Module};
use cranelisp_types::{
    ConcreteType, FQSymbol, FQTypeName, HeapHeader, Scheme, TypeName, drop_glue_symbol_name,
};

// spec: design/arch/bounded-contexts.md §5 invariant 9 (S81 / FIXME 0327,
//       the fault-guarded dispatch funnel step 2/4) — the absolute byte
//       offset of the Effect node's fn-name field (field-3) MUST be composed
//       from the named ABI constants (HeapHeader::SIZE + the platform
//       payload offset), NEVER hard-coded. The Effect node base layout is
//       [HeapHeader(16) | tag | thunk_ptr | resource_token | fn_name_handle],
//       so field-3 sits at base+40. This pins the composition: if the header
//       size or the platform payload offset changes, this assertion catches
//       a stale hard-coded value.
#[test]
fn effect_fn_name_offset_is_composed_from_named_constants() {
    // Composed value equals header + payload offset.
    assert_eq!(
        EFFECT_FN_NAME_ABS_OFFSET,
        HeapHeader::SIZE as i64 + cranelisp_platform::IO_EFFECT_FN_NAME_OFFSET,
    );
    // And it lands one i64 past the resource token (base+40 today).
    assert_eq!(
        EFFECT_FN_NAME_ABS_OFFSET,
        HeapHeader::SIZE as i64 + cranelisp_platform::IO_EFFECT_RESOURCE_OFFSET + 8,
    );
}

// spec: design/arch/bounded-contexts.md §5 invariant 9 — the baked fn-name
//       handle is a NUL-terminated UTF-8 byte sequence (the C-string the
//       trampoline fault guard reads in step 3, degrading a null handle to
//       "<unknown>"). This is the same self-describing convention the
//       layout-hash gate bakes (int's src/exe.rs::define_cstr_data — the backend
//       copy was deleted S113 W2b, FIXME 0635 I3).
#[test]
fn baked_fn_name_is_nul_terminated_utf8() {
    let bytes = platform_fn_name_bytes("platform.shapes/rectangle-area");
    assert_eq!(*bytes.last().unwrap(), 0u8, "must be NUL-terminated");
    assert_eq!(
        &bytes[..bytes.len() - 1],
        b"platform.shapes/rectangle-area",
        "the name bytes precede the NUL terminator verbatim",
    );
    // An empty name still produces a valid (just-NUL) C string.
    assert_eq!(platform_fn_name_bytes(""), vec![0u8]);
}

fn io_type() -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("IO"))
}

/// Compile the single blocking-platform-call chokepoint with a concrete IO
/// payload. The DLL body is irrelevant at this emission tier: its GOT slot is
/// imported and the returned node is inspected in CLIF.
fn platform_return_probe(
    payload: Type,
) -> (String, cranelift_object::ObjectModule, ModuleFullPath) {
    let platform = ModuleFullPath::from("platform.probe");
    let user = ModuleFullPath::from("user");
    let call_span = Span::new(20, 27);
    let caller = Defn {
        name: Symbol::from("caller"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("probe"),
                    span: call_span,
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![],
                span: Span::new(19, 28),
                resolved_call: None,
                inferred_type: Some(Box::new(Type::ADT(io_type(), vec![payload.clone()]))),
            },
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };

    let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
    let mut platform_table = SymbolTable::new(platform.clone());
    platform_table
        .install_platform(
            Symbol::from("probe"),
            Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Fn(vec![], Box::new(Type::ADT(io_type(), vec![payload]))),
            },
            vec![],
            None,
            0,
            Default::default(),
            false,
            0,
            Visibility::Public,
        )
        .expect("install platform probe");
    tables.insert(platform.clone(), platform_table);

    let mut user_table = SymbolTable::new(user.clone());
    user_table
        .expose_candidate(
            Symbol::from("probe"),
            FQSymbol {
                module: platform.clone(),
                symbol: Symbol::from("probe"),
            },
            Visibility::Public,
        )
        .expect("expose platform probe");
    let mut targets = HashMap::new();
    targets.insert(
        call_span,
        FQSymbol {
            module: platform,
            symbol: Symbol::from("probe"),
        },
    );
    install_def_entry_at_slot_with_targets(&mut user_table, caller.clone(), 0, &targets);
    tables.insert(user.clone(), user_table);

    let mut module = make_object_module();
    let artifacts = compile_names_to_module(
        user.clone(),
        std::slice::from_ref(&caller.name),
        &tables,
        &mut module,
        true,
    )
    .expect("compile blocking platform-return probe");
    (artifacts.clif_ir, module, user)
}

fn instruction_text(line: &str) -> &str {
    line.trim().split("  ;").next().unwrap_or("").trim()
}

fn target_label(operand: &str) -> Option<&str> {
    let label = operand.trim().split('(').next()?;
    label
        .strip_prefix("block")
        .filter(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))?;
    Some(label)
}

/// Prove that the unique store at `offset` is admitted only by the true arm of
/// `tag == expected_tag`, where `tag` is loaded from the returned node at +16.
/// Returns the false-arm block so the caller can inspect the no-write path.
fn assert_tag_dominated_store(clif: &str, offset: i64, expected_tag: i64) -> String {
    let mut definitions = HashMap::<String, String>::new();
    let mut blocks = Vec::<(String, Vec<String>)>::new();
    for raw in clif.lines() {
        let line = instruction_text(raw);
        if line.is_empty() || line == "}" {
            continue;
        }
        if let Some(label) = line.strip_suffix(':').and_then(target_label) {
            blocks.push((label.to_string(), Vec::new()));
            continue;
        }
        if let Some((value, rhs)) = line.split_once(" = ") {
            definitions.insert(value.trim().to_string(), rhs.trim().to_string());
        }
        if let Some((_, instructions)) = blocks.last_mut() {
            instructions.push(line.to_string());
        }
    }

    let needle = format!("+{offset}");
    let stores: Vec<_> = blocks
        .iter()
        .filter(|(_, instructions)| {
            instructions
                .iter()
                .any(|line| line.starts_with("store ") && line.contains(&needle))
        })
        .collect();
    assert_eq!(stores.len(), 1, "expected one store at {needle}:\n{clif}");
    let store_block = &stores[0].0;

    let predecessors: Vec<_> = blocks
        .iter()
        .filter_map(|(_, instructions)| {
            let term = instructions.last()?;
            let rest = term.strip_prefix("brif ")?;
            let mut parts = rest.split(',').map(str::trim);
            let condition = parts.next()?;
            let taken = target_label(parts.next()?)?;
            let not_taken = target_label(parts.next()?)?;
            (taken == store_block).then(|| (condition, not_taken))
        })
        .collect();
    assert_eq!(
        predecessors.len(),
        1,
        "store block must have one predicate-true predecessor:\n{clif}"
    );
    let (condition, not_taken) = predecessors[0];
    let compare = definitions
        .get(condition)
        .unwrap_or_else(|| panic!("missing store guard definition for {condition}:\n{clif}"));
    let operands = compare
        .strip_prefix("icmp.i64 eq ")
        .or_else(|| compare.strip_prefix("icmp eq "))
        .unwrap_or_else(|| panic!("stamp guard is not equality: {compare}\n{clif}"));
    let (tag_value, expected_value) = operands.split_once(',').expect("icmp carries two operands");
    let tag_load = definitions
        .get(tag_value.trim())
        .unwrap_or_else(|| panic!("missing tag load: {tag_value}\n{clif}"));
    assert!(
        tag_load.starts_with("load.i64 ") && tag_load.contains("+16"),
        "stamp discriminator must load HeapAdt::TAG_OFFSET (+16): {tag_load}\n{clif}"
    );
    let expected = definitions
        .get(expected_value.trim())
        .unwrap_or_else(|| panic!("missing expected-tag constant:\n{clif}"));
    assert_eq!(expected, &format!("iconst.i64 {expected_tag}"));
    not_taken.to_string()
}

// spec: design/backend/s121-c4-visit.md §6.7 — the returned tag, not the
// platform-callable kind alone, licenses both stores. The String and Int
// instantiations discriminate canonical glue-address versus scalar sentinel.
#[test]
fn platform_return_stamps_are_tag_dominated_for_heap_and_scalar_payloads() {
    for payload in [Type::String, Type::Int] {
        let (clif, module, user) = platform_return_probe(payload.clone());
        let effect_false = assert_tag_dominated_store(
            &clif,
            EFFECT_FN_NAME_ABS_OFFSET,
            cranelisp_platform::IO_TAG_EFFECT,
        );
        let pure_false = assert_tag_dominated_store(
            &clif,
            PURE_GLUE_ABS_OFFSET,
            cranelisp_platform::IO_TAG_PURE,
        );
        assert_ne!(effect_false, pure_false, "the two predicates are sequenced");
        let no_write = clif
            .split(&format!("{pure_false}:"))
            .nth(1)
            .and_then(|tail| tail.split("\nblock").next())
            .expect("Pure false-arm block exists");
        assert!(
            !no_write.contains("store "),
            "unexpected-tag path writes:\n{clif}"
        );
        assert_eq!(
            clif.lines()
                .map(instruction_text)
                .filter(|line| line.starts_with("store "))
                .count(),
            2,
            "only the two licensed stamp stores may be emitted:\n{clif}"
        );

        match payload {
            Type::String => {
                assert!(
                    clif.contains("func_addr.i64"),
                    "String adoption needs glue:\n{clif}"
                );
                let symbol = drop_glue_symbol_name(&user, &ConcreteType::String);
                assert!(matches!(
                    module.get_name(symbol.as_ref()),
                    Some(FuncOrDataId::Func(_))
                ));
            }
            Type::Int => {
                assert!(
                    clif.contains("iconst.i64 0"),
                    "Int adoption stamps 0:\n{clif}"
                );
                assert!(!clif.contains("func_addr.i64"), "Int owns no glue:\n{clif}");
            }
            _ => unreachable!(),
        }
    }
}
