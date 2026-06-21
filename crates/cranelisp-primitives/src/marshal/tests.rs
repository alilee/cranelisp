    use super::*;

    // spec: bounded-contexts.md §4a — heap-layout offsets single-sourced from
    // HeapHeader (Principle 7). Guards the HIGH-1 remediation (audit
    // 2026-06-14): the derived offsets MUST equal the canonical layout and the
    // RC offset MUST equal HeapHeader::RC_OFFSET. A future HeapHeader change
    // that shifts these breaks this test (and the `const _` asserts) rather
    // than silently corrupting the raw heap reads/writes.
    #[test]
    fn heap_offsets_derive_from_heap_header() {
        // Payload base is the header size; fields are i64-strided past it.
        assert_eq!(PAYLOAD_OFFSET, HeapHeader::SIZE);
        assert_eq!(FIELD0_OFFSET, HeapHeader::SIZE + core::mem::size_of::<i64>());
        assert_eq!(FIELD1_OFFSET, HeapHeader::SIZE + 2 * core::mem::size_of::<i64>());
        // Behaviour-preserving: identical to the pre-remediation literals.
        assert_eq!(PAYLOAD_OFFSET, 16);
        assert_eq!(FIELD0_OFFSET, 24);
        assert_eq!(FIELD1_OFFSET, 32);
        // shallow_rc_inc writes the RC field at HeapHeader::RC_OFFSET (was a
        // magic `.add(8)`); pin it to the canonical RC location.
        assert_eq!(HeapHeader::RC_OFFSET as usize, 8);
    }

    // spec: design/arch/CLAUDE.md Decision 24 — shallow_rc_inc increments the
    // RC field the marshal bodies share. Behaviour-preserving guard for the
    // HIGH-1 single-source change: an inc at the derived RC offset is observed
    // by consume_shallow (which reads the same canonical offset).
    #[test]
    fn shallow_rc_inc_targets_canonical_rc_field() {
        let allocs_before = cranelisp_intrinsics::alloc::alloc_count();
        let deallocs_before = cranelisp_intrinsics::alloc::dealloc_count();
        // Fresh heap cell, rc=1.
        let base = alloc_adt_2(TAG_SEXP_INT, 7);
        // Inc via the marshal helper (rc 1 -> 2).
        shallow_rc_inc(base);
        // First consume: rc 2 -> 1, NOT freed (the inc landed at the RC field).
        cranelisp_intrinsics::drop::consume_sexp(base);
        assert_eq!(
            cranelisp_intrinsics::alloc::dealloc_count() - deallocs_before,
            0,
            "inc must land on the RC field so the first dec does not free"
        );
        // Second consume: rc 1 -> 0, freed.
        cranelisp_intrinsics::drop::consume_sexp(base);
        assert_eq!(cranelisp_intrinsics::alloc::alloc_count() - allocs_before, 1);
        assert_eq!(
            cranelisp_intrinsics::alloc::dealloc_count() - deallocs_before,
            1,
            "value freed only after the inc'd reference is also released"
        );
    }

    #[test]
    fn test_sconcat_empty_empty() {
        let result = sconcat(TAG_SNIL, TAG_SNIL);
        assert_eq!(result, TAG_SNIL);
    }

    #[test]
    fn test_sconcat_empty_nonempty() {
        let ys = alloc_adt_3(TAG_SCONS, 42, TAG_SNIL);
        let result = sconcat(TAG_SNIL, ys);
        // Result should be ys (since xs is empty).
        let items = unsafe { read_slist(result) };
        assert_eq!(items, vec![42]);
    }

    #[test]
    fn test_sconcat_nonempty_empty() {
        let xs = alloc_adt_3(TAG_SCONS, 1, alloc_adt_3(TAG_SCONS, 2, TAG_SNIL));
        let result = sconcat(xs, TAG_SNIL);
        let items = unsafe { read_slist(result) };
        assert_eq!(items, vec![1, 2]);
    }

    #[test]
    fn test_sconcat_both_nonempty() {
        let xs = alloc_adt_3(TAG_SCONS, 1, alloc_adt_3(TAG_SCONS, 2, TAG_SNIL));
        let ys = alloc_adt_3(TAG_SCONS, 3, TAG_SNIL);
        let result = sconcat(xs, ys);
        let items = unsafe { read_slist(result) };
        assert_eq!(items, vec![1, 2, 3]);
    }

    // ---------------------------------------------------------------------
    // Decision 24 extern-consumption tests (Sprint 56 Step 2c)
    //
    // `sconcat` incs items of xs into new SCons nodes, deep-incs ys so the
    // result can splice it as a tail, then releases the original xs and ys
    // via `consume_slist`. The test verifies RC balance: after the caller
    // drops the result (also via consume_slist), no leaks or double-frees.
    // ---------------------------------------------------------------------

    // spec: design/arch/CLAUDE.md Decision 24 — consuming convention, extern sconcat
    #[test]
    fn decision24_sconcat_rc_balanced() {
        let allocs_before = cranelisp_intrinsics::alloc::alloc_count();
        let deallocs_before = cranelisp_intrinsics::alloc::dealloc_count();

        // xs = SCons(1, SCons(2, SNil))  — 2 SCons allocs, items are bare tags.
        // ys = SCons(3, SNil)            — 1 SCons alloc.
        let xs = alloc_adt_3(TAG_SCONS, 1, alloc_adt_3(TAG_SCONS, 2, TAG_SNIL));
        let ys = alloc_adt_3(TAG_SCONS, 3, TAG_SNIL);

        // sconcat:
        //   - deep_rc_inc_slist(ys): ys SCons rc 1→2, head=3 is bare tag.
        //   - builds 2 new SCons nodes holding items 1, 2 (bare tags —
        //     shallow_rc_inc no-op), tail chained to ys.
        //   - consume_slist(xs): last ref → frees both xs SCons nodes.
        //   - consume_slist(ys): rc 2→1, not freed.
        let result = sconcat(xs, ys);
        let items = unsafe { read_slist(result) };
        assert_eq!(items, vec![1, 2, 3]);

        // Caller releases the result (Decision 24 semantics — receiver owns).
        // consume_slist walks: frees the 2 new SCons, then ys SCons (rc 1→0).
        consume_slist(result);

        // allocs: 3 original (xs:2 + ys:1) + 2 new result SCons = 5
        // deallocs: same 5 — no leaks, no double-frees.
        assert_eq!(
            cranelisp_intrinsics::alloc::alloc_count() - allocs_before,
            5,
            "alloc count mismatch"
        );
        assert_eq!(
            cranelisp_intrinsics::alloc::dealloc_count() - deallocs_before,
            5,
            "dealloc count mismatch (leak or double-free)"
        );
    }
