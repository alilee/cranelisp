//! Bool-specific primitive functions.

/// Convert a boolean (0/1 i64) to "true" or "false". Returns a string pointer.
#[unsafe(export_name = "bool-to-string")]
pub extern "C" fn bool_to_string(value: i64) -> i64 {
    let s = if value != 0 { "true" } else { "false" };
    super::alloc_string(s.as_bytes())
}
