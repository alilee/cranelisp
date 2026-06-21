use super::*;

// spec: design/int/symbol-table-generics.md §3 Layer 3 + Decision 31
//       Scenario 2 reclaim primitive.
//
// Construct `Code::Jit(Arc<Jit>)`; assert `Arc::strong_count` semantics:
// cloning bumps the count, dropping decrements, and the underlying Jit
// drops only when the last Arc clone drops.
#[test]
// `Arc<Jit>` is intentionally not Send+Sync (Jit is not Sync) — this test
// exercises the production `Code::Jit(Arc<Jit>)` shape's refcount semantics,
// so the non-Send-Sync Arc IS the thing under test, not an oversight.
#[allow(clippy::arc_with_non_send_sync)]
fn code_enum_jit_variant_carries_arc_jit() {
    let jit = Arc::new(Jit::new_with_symbols(&[]).expect("Jit::new must succeed for test"));
    assert_eq!(Arc::strong_count(&jit), 1, "fresh Arc has refcount 1");

    let code1 = Code::jit(Arc::clone(&jit));
    assert_eq!(Arc::strong_count(&jit), 2, "Code::jit clones the Arc");
    assert!(matches!(code1, Code::Jit(_)), "Code::jit builds Code::Jit");

    let code2 = code1.clone();
    assert_eq!(Arc::strong_count(&jit), 3, "Code::clone bumps refcount");

    drop(code2);
    assert_eq!(Arc::strong_count(&jit), 2, "drop decrements refcount");

    drop(code1);
    assert_eq!(
        Arc::strong_count(&jit),
        1,
        "after dropping all Code::Jit clones, only the local Arc remains"
    );

    // Now drop the local Arc; the underlying Jit::drop fires (calling
    // unsafe JITModule::free_memory).
    let pre = crate::jit::jit_free_memory_call_count();
    drop(jit);
    let post = crate::jit::jit_free_memory_call_count();
    assert_eq!(
        post,
        pre + 1,
        "dropping the last Arc<Jit> must invoke Jit::drop's free_memory call"
    );
}

// spec: design/int/symbol-table-generics.md §2.1 — Code enum unifies
//       fresh-build (Jit) and cache-hit (Linker) into one shape.
#[test]
fn code_enum_linker_variant_constructible() {
    let linker = Arc::new(
        crate::cache::linker::Linker::new().expect("Linker::new must succeed for test"),
    );
    let code = Code::linker(Arc::clone(&linker));

    assert!(matches!(code, Code::Linker(_)), "Code::linker builds Code::Linker");
    assert_eq!(
        Arc::strong_count(&linker),
        2,
        "Code::linker clones the Arc"
    );

    drop(code);
    assert_eq!(
        Arc::strong_count(&linker),
        1,
        "dropping Code::Linker decrements the Arc"
    );
}

// spec: design/typecheck/ast-annotation.md §12 + Decision 32 —
//       SymbolTable<Code, ()> resolves; Code implements CodeStore via
//       the blanket impl.
#[test]
fn code_implements_code_store() {
    fn _requires_code_store<T: cranelisp_types::CodeStore>() {}
    _requires_code_store::<Code>();
}

// spec: design/int/symbol-table-generics.md §2.1 — `Code::Linker` carries
//       `Arc<Linker>`; one cache-loaded `.o` batch backs MULTIPLE `Def`
//       entries (each its own `Code::Linker` clone), all sharing one
//       `Arc<Linker>`. The batch's mmap'd regions reclaim only when the
//       LAST clone drops. S82 harvest of the legacy
//       `decision31_code_linker_session_scope_only` reg-guard (FIXME 0133):
//       the session-scope multi-entry-one-batch shape, lifted to the Code
//       layer (`Linker` reclaim is structural via `MmapMut::Drop`, with no
//       global counter — the guard is the `Arc::strong_count` lifecycle and
//       a clean drop chain).
#[test]
fn code_linker_multiple_entries_share_one_batch() {
    let linker = Arc::new(
        crate::cache::linker::Linker::new().expect("Linker::new must succeed for test"),
    );
    assert_eq!(Arc::strong_count(&linker), 1, "fresh Arc<Linker> refcount 1");

    // Two `Def` entries reference the same cache-loaded batch.
    let code1 = Code::linker(Arc::clone(&linker));
    let code2 = Code::linker(Arc::clone(&linker));
    assert_eq!(
        Arc::strong_count(&linker),
        3,
        "two Code::Linker clones each hold one Arc clone (1 local + 2 = 3)"
    );

    // Dropping one entry decrements but does NOT reclaim — the other entry
    // still references the batch.
    drop(code1);
    assert_eq!(
        Arc::strong_count(&linker),
        2,
        "dropping one entry's Code::Linker leaves the batch alive for the other"
    );

    drop(code2);
    assert_eq!(
        Arc::strong_count(&linker),
        1,
        "dropping the second entry leaves only the local Arc"
    );

    // Drop the last clone — the Linker (and its MmapMut regions) reclaims.
    // Reaching the end without a panic is the assertion: the drop chain
    // completed cleanly (a double-free / use-after-free in Linker::Drop
    // would abort here).
    drop(linker);
}
