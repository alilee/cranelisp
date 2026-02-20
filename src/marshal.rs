//! Marshalling between Rust `Sexp` values and JIT-runtime Sexp ADT representations.
//!
//! The synthetic `macros` module defines:
//! ```text
//! (deftype (SList a) SNil (SCons [:a head :(SList a) tail]))
//! (deftype Sexp
//!   (SexpSym [:String name])         ; tag 0
//!   (SexpInt [:Int val])             ; tag 1
//!   (SexpFloat [:Float val])         ; tag 2
//!   (SexpBool [:Bool val])           ; tag 3
//!   (SexpStr [:String val])          ; tag 4
//!   (SexpList [:(SList Sexp) items]) ; tag 5
//!   (SexpBracket [:(SList Sexp) items])) ; tag 6
//! ```
//!
//! All Sexp constructors are data constructors (no nullary).
//! Runtime layout: heap pointer to `[tag: i64, field0: i64, ...]`.
//!
//! SList runtime layout: SNil = bare i64 0, SCons = heap `[1, head, tail]`.

// Re-export runtime marshal items (tag constants, alloc_adt, build_runtime_list, quote_sexp)
pub use cranelisp_runtime::marshal::*;

use crate::primitives::alloc_string;
use crate::sexp::Sexp;

/// Convert a Rust `Sexp` tree into a JIT-runtime Sexp ADT value.
///
/// Allocates heap memory for each node. The caller is responsible for
/// ensuring the returned value is eventually freed (or managed by RC).
pub fn sexp_to_runtime(sexp: &Sexp) -> i64 {
    match sexp {
        Sexp::Symbol(name, _) => {
            let s = alloc_string(name.as_bytes());
            alloc_adt(TAG_SEXP_SYM, &[s])
        }
        Sexp::Int(val, _) => alloc_adt(TAG_SEXP_INT, &[*val]),
        Sexp::Float(val, _) => alloc_adt(TAG_SEXP_FLOAT, &[val.to_bits() as i64]),
        Sexp::Bool(val, _) => alloc_adt(TAG_SEXP_BOOL, &[if *val { 1 } else { 0 }]),
        Sexp::Str(val, _) => {
            let s = alloc_string(val.as_bytes());
            alloc_adt(TAG_SEXP_STR, &[s])
        }
        Sexp::List(children, _) => {
            let items: Vec<i64> = children.iter().map(sexp_to_runtime).collect();
            let list = build_runtime_list(&items);
            alloc_adt(TAG_SEXP_LIST, &[list])
        }
        Sexp::Bracket(children, _) => {
            let items: Vec<i64> = children.iter().map(sexp_to_runtime).collect();
            let list = build_runtime_list(&items);
            alloc_adt(TAG_SEXP_BRACKET, &[list])
        }
    }
}

/// Read a cranelisp string from a heap pointer (layout: `[i64 len][u8 bytes...]`).
///
/// # Safety
/// `ptr` must be a valid heap pointer to a cranelisp string.
unsafe fn read_string(ptr: i64) -> String {
    unsafe {
        let len = *(ptr as *const i64) as usize;
        let bytes = std::slice::from_raw_parts((ptr + 8) as *const u8, len);
        std::str::from_utf8(bytes)
            .unwrap_or("<invalid utf8>")
            .to_string()
    }
}

/// Walk a runtime SList (SCons chain) and collect elements as i64 values.
///
/// # Safety
/// `ptr` must be either 0 (SNil) or a valid heap pointer to a SCons cell.
unsafe fn read_runtime_list(ptr: i64) -> Vec<i64> {
    unsafe {
        let mut result = Vec::new();
        let mut current = ptr;
        loop {
            if current == TAG_SNIL {
                break;
            }
            let tag = *(current as *const i64);
            debug_assert_eq!(tag, TAG_SCONS, "expected SCons tag 1, got {}", tag);
            let head = *((current as *const i64).add(1));
            let tail = *((current as *const i64).add(2));
            result.push(head);
            current = tail;
        }
        result
    }
}

/// Convert a JIT-runtime Sexp ADT value back to a Rust `Sexp`.
///
/// All output spans are `(0, 0)` (synthetic).
///
/// # Safety
/// `val` must be a valid heap pointer to a Sexp ADT cell.
pub fn runtime_to_sexp(val: i64) -> Sexp {
    let tag = unsafe { *(val as *const i64) };
    let field0 = unsafe { *((val as *const i64).add(1)) };
    let span = (0, 0);

    match tag {
        TAG_SEXP_SYM => {
            let name = unsafe { read_string(field0) };
            Sexp::Symbol(name, span)
        }
        TAG_SEXP_INT => Sexp::Int(field0, span),
        TAG_SEXP_FLOAT => Sexp::Float(f64::from_bits(field0 as u64), span),
        TAG_SEXP_BOOL => Sexp::Bool(field0 != 0, span),
        TAG_SEXP_STR => {
            let val = unsafe { read_string(field0) };
            Sexp::Str(val, span)
        }
        TAG_SEXP_LIST => {
            let items = unsafe { read_runtime_list(field0) };
            let children: Vec<Sexp> = items.into_iter().map(runtime_to_sexp).collect();
            Sexp::List(children, span)
        }
        TAG_SEXP_BRACKET => {
            let items = unsafe { read_runtime_list(field0) };
            let children: Vec<Sexp> = items.into_iter().map(runtime_to_sexp).collect();
            Sexp::Bracket(children, span)
        }
        _ => panic!("unknown Sexp tag: {}", tag),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intrinsics::reset_counts;

    /// Helper: roundtrip a Sexp through runtime and back, comparing without spans.
    fn roundtrip(sexp: &Sexp) -> Sexp {
        let runtime = sexp_to_runtime(sexp);
        runtime_to_sexp(runtime)
    }

    /// Strip spans from a Sexp for comparison (all become (0,0)).
    fn strip_spans(sexp: &Sexp) -> Sexp {
        let span = (0, 0);
        match sexp {
            Sexp::Symbol(s, _) => Sexp::Symbol(s.clone(), span),
            Sexp::Int(v, _) => Sexp::Int(*v, span),
            Sexp::Float(v, _) => Sexp::Float(*v, span),
            Sexp::Bool(v, _) => Sexp::Bool(*v, span),
            Sexp::Str(s, _) => Sexp::Str(s.clone(), span),
            Sexp::List(children, _) => Sexp::List(children.iter().map(strip_spans).collect(), span),
            Sexp::Bracket(children, _) => {
                Sexp::Bracket(children.iter().map(strip_spans).collect(), span)
            }
        }
    }

    #[test]
    fn roundtrip_symbol() {
        reset_counts();
        let sexp = Sexp::Symbol("foo".to_string(), (5, 8));
        assert_eq!(roundtrip(&sexp), strip_spans(&sexp));
    }

    #[test]
    fn roundtrip_int() {
        reset_counts();
        let sexp = Sexp::Int(42, (0, 2));
        assert_eq!(roundtrip(&sexp), strip_spans(&sexp));
    }

    #[test]
    fn roundtrip_negative_int() {
        reset_counts();
        let sexp = Sexp::Int(-7, (0, 2));
        assert_eq!(roundtrip(&sexp), strip_spans(&sexp));
    }

    #[test]
    fn roundtrip_float() {
        reset_counts();
        let sexp = Sexp::Float(3.14, (0, 4));
        assert_eq!(roundtrip(&sexp), strip_spans(&sexp));
    }

    #[test]
    fn roundtrip_negative_float() {
        reset_counts();
        let sexp = Sexp::Float(-2.5, (0, 4));
        assert_eq!(roundtrip(&sexp), strip_spans(&sexp));
    }

    #[test]
    fn roundtrip_bool_true() {
        reset_counts();
        let sexp = Sexp::Bool(true, (0, 4));
        assert_eq!(roundtrip(&sexp), strip_spans(&sexp));
    }

    #[test]
    fn roundtrip_bool_false() {
        reset_counts();
        let sexp = Sexp::Bool(false, (0, 5));
        assert_eq!(roundtrip(&sexp), strip_spans(&sexp));
    }

    #[test]
    fn roundtrip_string() {
        reset_counts();
        let sexp = Sexp::Str("hello world".to_string(), (0, 13));
        assert_eq!(roundtrip(&sexp), strip_spans(&sexp));
    }

    #[test]
    fn roundtrip_empty_string() {
        reset_counts();
        let sexp = Sexp::Str(String::new(), (0, 2));
        assert_eq!(roundtrip(&sexp), strip_spans(&sexp));
    }

    #[test]
    fn roundtrip_empty_list() {
        reset_counts();
        let sexp = Sexp::List(vec![], (0, 2));
        assert_eq!(roundtrip(&sexp), strip_spans(&sexp));
    }

    #[test]
    fn roundtrip_list_of_atoms() {
        reset_counts();
        let sexp = Sexp::List(
            vec![
                Sexp::Symbol("+".to_string(), (1, 2)),
                Sexp::Int(1, (3, 4)),
                Sexp::Int(2, (5, 6)),
            ],
            (0, 7),
        );
        assert_eq!(roundtrip(&sexp), strip_spans(&sexp));
    }

    #[test]
    fn roundtrip_nested_list() {
        reset_counts();
        let sexp = Sexp::List(
            vec![
                Sexp::Symbol("defn".to_string(), (0, 4)),
                Sexp::Symbol("foo".to_string(), (5, 8)),
                Sexp::Bracket(vec![Sexp::Symbol("x".to_string(), (10, 11))], (9, 12)),
                Sexp::List(
                    vec![
                        Sexp::Symbol("+".to_string(), (14, 15)),
                        Sexp::Symbol("x".to_string(), (16, 17)),
                        Sexp::Int(1, (18, 19)),
                    ],
                    (13, 20),
                ),
            ],
            (0, 21),
        );
        assert_eq!(roundtrip(&sexp), strip_spans(&sexp));
    }

    #[test]
    fn roundtrip_empty_bracket() {
        reset_counts();
        let sexp = Sexp::Bracket(vec![], (0, 2));
        assert_eq!(roundtrip(&sexp), strip_spans(&sexp));
    }

    #[test]
    fn roundtrip_bracket_with_items() {
        reset_counts();
        let sexp = Sexp::Bracket(
            vec![
                Sexp::Symbol("x".to_string(), (1, 2)),
                Sexp::Symbol("y".to_string(), (3, 4)),
            ],
            (0, 5),
        );
        assert_eq!(roundtrip(&sexp), strip_spans(&sexp));
    }

    #[test]
    fn roundtrip_mixed_types() {
        reset_counts();
        let sexp = Sexp::List(
            vec![
                Sexp::Symbol("test".to_string(), (0, 0)),
                Sexp::Int(42, (0, 0)),
                Sexp::Float(3.14, (0, 0)),
                Sexp::Bool(true, (0, 0)),
                Sexp::Str("hello".to_string(), (0, 0)),
                Sexp::List(vec![], (0, 0)),
                Sexp::Bracket(vec![], (0, 0)),
            ],
            (0, 0),
        );
        assert_eq!(roundtrip(&sexp), strip_spans(&sexp));
    }

    #[test]
    fn roundtrip_deeply_nested() {
        reset_counts();
        let sexp = Sexp::List(
            vec![Sexp::List(
                vec![Sexp::List(vec![Sexp::Int(42, (0, 0))], (0, 0))],
                (0, 0),
            )],
            (0, 0),
        );
        assert_eq!(roundtrip(&sexp), strip_spans(&sexp));
    }
}
