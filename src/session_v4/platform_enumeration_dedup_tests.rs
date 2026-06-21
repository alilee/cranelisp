    use super::dedup_platform_names_preserving_order;

    // DEF-4 (S86 Wave E): the per-platform startup-stub layout-hash gate symbol
    // `__cranelisp_expected_hash_<P>` was emitted once per `kept_dlls` entry, and
    // a multi-module `(platform <P>)` program enumerated the SAME platform once
    // per retry-from-top dependency drive — so the backend tried to define the
    // same symbol twice ("Duplicate definition of identifier"). The fix dedups
    // the platform enumeration by identity (name) before it reaches the backend
    // startup-stub emitter. This pins that seam: a platform referenced N times
    // yields exactly ONE entry, regardless of how many `kept_dlls` rows carry it.
    #[test]
    fn multi_module_platform_enumeration_dedups_to_one_entry_per_platform() {
        // Same platform "web" enumerated three times (one per retry/module),
        // exactly the shape `kept_dlls` carries on a multi-module --link.
        let kept = ["web", "web", "web"];
        let deduped = dedup_platform_names_preserving_order(kept.iter().copied());
        assert_eq!(
            deduped,
            vec!["web".to_string()],
            "a platform referenced N times must yield exactly ONE layout-check / \
             kept-DLL entry — else exe.rs defines __cranelisp_expected_hash_web N times"
        );
    }

    #[test]
    fn distinct_platforms_dedup_preserves_first_seen_order() {
        // Mixed: distinct platforms each kept once, in first-seen order, even
        // when interleaved with duplicates. Order matters because the backend
        // relies on the manifest-index ↔ rlib ↔ layout-check correspondence.
        let kept = ["web", "stdio", "web", "shapes", "stdio"];
        let deduped = dedup_platform_names_preserving_order(kept.iter().copied());
        assert_eq!(
            deduped,
            vec!["web".to_string(), "stdio".to_string(), "shapes".to_string()],
            "dedup must preserve first-seen order of distinct platforms"
        );
    }

    #[test]
    fn empty_enumeration_yields_no_entries() {
        let kept: [&str; 0] = [];
        let deduped = dedup_platform_names_preserving_order(kept.iter().copied());
        assert!(deduped.is_empty(), "no platforms → no link entries");
    }
