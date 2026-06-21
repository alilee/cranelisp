use super::*;

fn layout_hash_mismatch() -> PlatformError {
    PlatformError::LayoutHashMismatch {
        dll: PathBuf::from("/some/path/libstdio.dylib"),
        platform: "stdio".to_string(),
        expected: "abc123".to_string(),
        found: "def456".to_string(),
        location: ErrorLocation::unknown(),
    }
}

#[test]
fn layout_hash_mismatch_message_includes_rebuild_guidance() {
    let err = layout_hash_mismatch();
    let msg = err.to_string();
    // The platform name, both hashes, and the rebuild guidance must all
    // appear so the user knows what is stale and what to do.
    assert!(msg.contains("stdio"), "names the platform: {msg}");
    assert!(msg.contains("abc123"), "names the expected hash: {msg}");
    assert!(msg.contains("def456"), "names the found hash: {msg}");
    assert!(
        msg.contains("/platform-schema"),
        "points at /platform-schema: {msg}"
    );
    assert!(
        msg.contains("rebuild the platform"),
        "tells the user to rebuild: {msg}"
    );
}

#[test]
fn layout_hash_mismatch_static_message() {
    let err = layout_hash_mismatch();
    assert_eq!(err.message_static(), "platform schema layout hash mismatch");
}

#[test]
fn layout_hash_mismatch_location_accessor() {
    let err = layout_hash_mismatch();
    // Every variant carries an ErrorLocation per Decision 0042.
    assert_eq!(err.location().span, Span::SYNTHETIC);
}

#[test]
fn layout_hash_mismatch_surfaces_through_cranelisp_error() {
    // The refusal reaches the formatter via CranelispError::Platform.
    let err: CranelispError = layout_hash_mismatch().into();
    let msg = err.to_string();
    assert!(msg.contains("stdio"), "delegates to PlatformError: {msg}");
    assert!(matches!(err, CranelispError::Platform(_)));
}
