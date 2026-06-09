//! Docstrings for host-implemented builtins (`spec/appendix-a-builtins.md`
//! §A.5).
//!
//! §A.5 is a MUST: every primitive function "MUST have docstrings available at
//! runtime", surfaced both via `/doc` and in the `; classification - docstring`
//! suffix of the universal output format (`repl/spec.md` §1.1). The docstring
//! for each builtin is the Description-column text of the §A.3 tables (or "an
//! equivalent concise description").
//!
//! The `cranelisp-primitives` crate registers primitive `ModuleEntry::Def`
//! entries with `docstring: None` — its `PrimitiveDef` does not carry the
//! Description text, and that crate is outside the int boundary. So the
//! Appendix A.5 description is sourced here, at the int (REPL display) layer,
//! keyed by the spec primitive name. This is the single source the
//! bare-primitive value display and the `/doc` command both consult.
//!
//! When `spec/appendix-a-builtins.md` §A.3 gains/renames a primitive, add the
//! matching row here. A primitive with no entry falls through to `None`
//! (display shows the bare `; primitive` classification with no docstring,
//! per §1.1's "If the symbol has no docstring, only the classification
//! appears").

/// Description text for a `primitives`-module builtin, per
/// `spec/appendix-a-builtins.md` §A.3 / §A.5. Returns `None` for names with no
/// catalogued description.
pub(crate) fn builtin_docstring(name: &str) -> Option<&'static str> {
    let doc = match name {
        // Integer arithmetic (§A.3 Inline Primitives).
        "add-i64" => "Add",
        "sub-i64" => "Subtract",
        "mul-i64" => "Multiply",
        "div-i64" => "Integer division",
        // Integer comparison.
        "eq-i64" => "Equality",
        "neq-i64" => "Inequality",
        "lt-i64" => "Less than",
        "gt-i64" => "Greater than",
        "le-i64" => "Less than or equal",
        "ge-i64" => "Greater than or equal",
        // Float arithmetic.
        "add-f64" => "Add",
        "sub-f64" => "Subtract",
        "mul-f64" => "Multiply",
        "div-f64" => "Division",
        // Float comparison.
        "eq-f64" => "Equality",
        "neq-f64" => "Inequality",
        "lt-f64" => "Less than",
        "gt-f64" => "Greater than",
        "le-f64" => "Less than or equal",
        "ge-f64" => "Greater than or equal",
        // Boolean.
        "not" => "Boolean negation",
        "eq-bool" => "Equality",
        "neq-bool" => "Inequality",
        // Type conversion (§A.3 Extern Primitives).
        "int-to-string" => "Convert integer to decimal string",
        "float-to-string" => "Convert float to string",
        "bool-to-string" => "\"true\" or \"false\"",
        "string-identity" => "Identity for String (used by Display impl)",
        // String operations.
        "str-concat" => "Concatenate two strings",
        "str-eq" => "String equality (byte-wise)",
        "str-len" => "String length in bytes",
        "parse-int" => "Parse decimal integer; None on failure",
        "substring" => {
            "Extract substring from start (inclusive) to end (exclusive); \
             clamps out-of-bounds indices"
        }
        "char-at" => {
            "Character at byte index as single-character string; empty \
             string if out of bounds"
        }
        "split" => "Split string by separator",
        "join" => "Join strings with separator",
        "replace" => "Replace all occurrences of from with to",
        "trim" => "Trim leading and trailing whitespace",
        "starts-with?" => "Test if string starts with prefix",
        "ends-with?" => "Test if string ends with suffix",
        "contains?" => "Test if string contains substring",
        "to-upper" => "Convert to uppercase",
        "to-lower" => "Convert to lowercase",
        // Macro support.
        "quote-sexp" => "Convert a runtime Sexp value to constructor source code",
        "sconcat" => "Concatenate Sexp / SList values",
        // Vec operations.
        "vec-get" => "Index (bounds-checked; panics on out-of-bounds)",
        "vec-set" => "Return new Vec with element at index replaced",
        "vec-push" => "Return new Vec with element appended",
        "vec-len" => "Number of elements",
        _ => return None,
    };
    Some(doc)
}

#[cfg(test)]
mod tests {
    use super::*;

    // spec: spec/appendix-a-builtins.md §A.5 — every primitive function MUST
    // have a docstring available at runtime.
    #[test]
    fn ring0_arithmetic_has_descriptions() {
        assert_eq!(builtin_docstring("add-i64"), Some("Add"));
        assert_eq!(builtin_docstring("div-i64"), Some("Integer division"));
        assert_eq!(builtin_docstring("not"), Some("Boolean negation"));
    }

    // spec: spec/appendix-a-builtins.md §A.5 — Description column is the doc.
    #[test]
    fn string_ops_have_descriptions() {
        assert_eq!(builtin_docstring("str-concat"), Some("Concatenate two strings"));
        assert_eq!(builtin_docstring("str-len"), Some("String length in bytes"));
    }

    // spec: repl/spec.md §1.1 — "If the symbol has no docstring, only the
    // classification appears" — uncatalogued names return None.
    #[test]
    fn unknown_name_returns_none() {
        assert_eq!(builtin_docstring("definitely-not-a-primitive"), None);
    }
}
