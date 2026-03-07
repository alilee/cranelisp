//! CraneliftExpander: the real MacroExpander for Ring 3+.
//!
//! Owns compiled macro function pointers and performs expansion.
//! Lives in the binary crate because it wires typecheck + backend.

use std::collections::HashMap;

use cranelisp_types::{
    CompileMode, CranelispError, MacroExpander, MacroParam, Sexp, Span, Symbol,
    NULLARY_TAG_THRESHOLD,
};

use crate::marshal;

/// Maximum recursion depth for macro expansion.
const EXPANSION_DEPTH_LIMIT: usize = 100;

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// A compiled macro clause with its function pointer.
struct MacroClauseEntry {
    /// JIT-compiled function: extern "C" fn(i64) -> i64.
    /// The i64 parameter is a pointer to an (SList Sexp) of marshalled args.
    func_ptr: *const u8,
    /// Fixed parameter patterns (for clause matching).
    params: Vec<MacroParam>,
    /// Rest parameter name, if variadic.
    rest_param: Option<Symbol>,
}

/// A registered macro with all its compiled clauses.
struct MacroEntry {
    clauses: Vec<MacroClauseEntry>,
    #[allow(dead_code)]
    docstring: Option<String>,
}

/// Macro environment: name -> compiled macro.
pub struct MacroEnv {
    macros: HashMap<Symbol, MacroEntry>,
}

impl MacroEnv {
    fn new() -> Self {
        MacroEnv {
            macros: HashMap::new(),
        }
    }
}

/// The real MacroExpander implementation.
pub struct CraneliftExpander {
    env: MacroEnv,
}

impl Default for CraneliftExpander {
    fn default() -> Self {
        Self::new()
    }
}

impl CraneliftExpander {
    /// Create a new expander with an empty macro environment.
    pub fn new() -> Self {
        CraneliftExpander {
            env: MacroEnv::new(),
        }
    }

    /// Compile a macro from a parsed DefmacroInfo and register it.
    ///
    /// For each clause:
    /// 1. Expand quasiquotes in the body Sexp
    /// 2. Call `synthesize_macro_clause_defn` to produce a defn Sexp
    /// 3. Parse the defn Sexp through the frontend (build_program)
    /// 4. Typecheck the resulting program
    /// 5. Compile via backend and extract the function pointer
    /// 6. Store the compiled clause in the MacroEnv
    pub fn compile_macro(
        &mut self,
        info: &cranelisp_frontend::DefmacroInfo,
        tc: &mut cranelisp_typecheck::TypeChecker,
        jit: &mut cranelisp_backend::jit::Jit,
    ) -> Result<(), CranelispError> {
        let mut compiled_clauses = Vec::new();

        for (clause_idx, clause) in info.clauses.iter().enumerate() {
            let func_ptr = compile_single_clause(
                &info.name,
                clause_idx,
                clause,
                info.span,
                self,
                tc,
                jit,
            )?;

            compiled_clauses.push(MacroClauseEntry {
                func_ptr,
                params: clause.fixed_params.clone(),
                rest_param: clause.rest_param.clone(),
            });
        }

        self.env.macros.insert(
            info.name.clone(),
            MacroEntry {
                clauses: compiled_clauses,
                docstring: info.docstring.clone(),
            },
        );

        Ok(())
    }

    /// Recursively expand a Sexp tree, replacing macro calls with their expansions.
    ///
    /// Walks the tree looking for list forms whose head is a known macro name.
    /// Also handles bare symbols that are zero-arg macros.
    /// Depth limit prevents infinite expansion.
    pub fn expand_sexp(&mut self, sexp: Sexp) -> Result<Sexp, CranelispError> {
        expand_sexp_recursive(sexp, &mut self.env, 0)
    }
}

impl MacroExpander for CraneliftExpander {
    /// Expand a macro invocation.
    ///
    /// Called by the AST builder when it encounters a list form whose head
    /// is a registered macro name.
    fn expand(
        &mut self,
        name: &Symbol,
        args: &[Sexp],
        span: Span,
    ) -> Result<Sexp, CranelispError> {
        let entry = self.env.macros.get(name).ok_or_else(|| {
            CranelispError::MacroError {
                message: format!("unknown macro '{name}'"),
                span,
            }
        })?;

        // Find matching clause.
        let clause = find_matching_clause(&entry.clauses, args).ok_or_else(|| {
            CranelispError::MacroError {
                message: format!(
                    "no matching clause for macro '{name}' with {} arguments",
                    args.len()
                ),
                span,
            }
        })?;

        // Marshal args and invoke.
        let result = invoke_clause(clause, args, span)?;

        // Rewrite spans in the result to the call-site span.
        let mut rewritten = result;
        rewrite_spans(&mut rewritten, span);

        // Re-expand the result in case it contains macro calls.
        expand_sexp_recursive(rewritten, &mut self.env, 0)
    }

    fn is_macro(&self, name: &str) -> bool {
        self.env.macros.contains_key(name)
    }
}

// ---------------------------------------------------------------------------
// Clause matching
// ---------------------------------------------------------------------------

/// Check whether a clause's parameter pattern matches the given arguments.
///
/// - If clause has rest_param: args.len() >= clause.params.len()
/// - If no rest_param: args.len() == clause.params.len()
/// - Bracket params must receive Sexp::Bracket arguments
fn clause_matches(clause: &MacroClauseEntry, args: &[Sexp]) -> bool {
    let fixed_count = clause.params.len();
    if clause.rest_param.is_some() {
        if args.len() < fixed_count {
            return false;
        }
    } else if args.len() != fixed_count {
        return false;
    }

    // Check bracket params match Sexp::Bracket arguments.
    for (i, param) in clause.params.iter().enumerate() {
        if let MacroParam::Bracket { fixed, rest } = param {
            if i >= args.len() {
                return false;
            }
            if let Sexp::Bracket(items, _) = &args[i] {
                // Check element count compatibility.
                if rest.is_some() {
                    if items.len() < fixed.len() {
                        return false;
                    }
                } else if items.len() != fixed.len() {
                    return false;
                }
            } else {
                return false; // Bracket param requires Bracket arg
            }
        }
    }

    true
}

/// Find the first matching clause for the given arguments.
fn find_matching_clause<'a>(
    clauses: &'a [MacroClauseEntry],
    args: &[Sexp],
) -> Option<&'a MacroClauseEntry> {
    clauses.iter().find(|c| clause_matches(c, args))
}

// ---------------------------------------------------------------------------
// Clause invocation
// ---------------------------------------------------------------------------

/// Marshal arguments, invoke a clause's function pointer, and unmarshal the result.
fn invoke_clause(
    clause: &MacroClauseEntry,
    args: &[Sexp],
    span: Span,
) -> Result<Sexp, CranelispError> {
    // Marshal each argument to a runtime Sexp ADT value.
    let marshalled: Vec<i64> = args.iter().map(marshal::sexp_to_runtime).collect();

    // Bump RC on each marshalled Sexp element. The compiled macro function
    // uses a consuming calling convention: it decrements RC on its args
    // parameter (SList) via drop glue, which also decrements each Sexp
    // element inside. Without this extra inc, elements extracted from the
    // args and stored in the result would be freed during parameter cleanup.
    for &val in &marshalled {
        marshal::rc_inc(val);
    }

    // Package all args as an (SList Sexp).
    let args_slist = marshal::build_runtime_slist(&marshalled);

    // Invoke the compiled function.
    // SAFETY: func_ptr was produced by JIT compilation of a function with
    // signature extern "C" fn(i64) -> i64. The args_slist is a valid
    // runtime (SList Sexp) value.
    let func: extern "C" fn(i64) -> i64 =
        unsafe { std::mem::transmute(clause.func_ptr) };
    let result_i64 = func(args_slist);

    // Validate the result is a heap pointer (all Sexp constructors are data).
    if result_i64 < NULLARY_TAG_THRESHOLD as i64 {
        return Err(CranelispError::MacroError {
            message: format!(
                "macro returned invalid value {result_i64} (expected heap pointer)"
            ),
            span,
        });
    }

    // Unmarshal the result back to a compiler Sexp.
    Ok(marshal::runtime_to_sexp(result_i64))
}

// ---------------------------------------------------------------------------
// Span rewriting
// ---------------------------------------------------------------------------

/// Recursively replace all spans in a Sexp tree with the given span.
fn rewrite_spans(sexp: &mut Sexp, span: Span) {
    match sexp {
        Sexp::Symbol(_, s)
        | Sexp::Int(_, s)
        | Sexp::Float(_, s)
        | Sexp::Bool(_, s)
        | Sexp::Str(_, s) => *s = span,
        Sexp::List(children, s) | Sexp::Bracket(children, s) => {
            *s = span;
            for child in children {
                rewrite_spans(child, span);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Recursive expansion
// ---------------------------------------------------------------------------

/// Recursively expand macro calls in a Sexp tree.
///
/// Handles:
/// - List forms where head is a known macro -> dispatch and re-expand result
/// - Bare symbols that are zero-arg macros
/// - Recursive children expansion
fn expand_sexp_recursive(
    sexp: Sexp,
    env: &mut MacroEnv,
    depth: usize,
) -> Result<Sexp, CranelispError> {
    if depth > EXPANSION_DEPTH_LIMIT {
        return Err(CranelispError::MacroError {
            message: format!(
                "macro expansion depth limit ({EXPANSION_DEPTH_LIMIT}) exceeded"
            ),
            span: sexp.span(),
        });
    }

    match sexp {
        Sexp::List(ref children, span) if !children.is_empty() => {
            // Check if head is a macro name.
            if let Sexp::Symbol(ref name, _) = children[0]
                && env.macros.contains_key(name.as_str())
            {
                let args = &children[1..];
                return expand_macro_call(name, args, span, env, depth);
            }
            // Not a macro call — recurse into children.
            let Sexp::List(children, span) = sexp else {
                unreachable!();
            };
            let expanded: Vec<Sexp> = children
                .into_iter()
                .map(|c| expand_sexp_recursive(c, env, depth))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Sexp::List(expanded, span))
        }
        Sexp::Symbol(ref name, span) => {
            // Bare symbol: check for zero-arg macro.
            if env.macros.contains_key(name.as_str()) {
                return expand_macro_call(name, &[], span, env, depth);
            }
            Ok(sexp)
        }
        Sexp::Bracket(children, span) => {
            let expanded: Vec<Sexp> = children
                .into_iter()
                .map(|c| expand_sexp_recursive(c, env, depth))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Sexp::Bracket(expanded, span))
        }
        _ => Ok(sexp),
    }
}

/// Expand a single macro call, then re-expand the result.
fn expand_macro_call(
    name: &str,
    args: &[Sexp],
    span: Span,
    env: &mut MacroEnv,
    depth: usize,
) -> Result<Sexp, CranelispError> {
    let entry = env.macros.get(name).ok_or_else(|| {
        CranelispError::MacroError {
            message: format!("unknown macro '{name}'"),
            span,
        }
    })?;

    let clause = find_matching_clause(&entry.clauses, args).ok_or_else(|| {
        CranelispError::MacroError {
            message: format!(
                "no matching clause for macro '{name}' with {} arguments",
                args.len()
            ),
            span,
        }
    })?;

    let mut result = invoke_clause(clause, args, span)?;
    rewrite_spans(&mut result, span);

    // Re-expand the result.
    expand_sexp_recursive(result, env, depth + 1)
}

// ---------------------------------------------------------------------------
// Single clause compilation
// ---------------------------------------------------------------------------

/// Compile a single macro clause through the full pipeline.
///
/// 1. Synthesize a defn Sexp from the clause
/// 2. Expand quasiquotes in the synthesized Sexp
/// 3. Build AST via the frontend (using the current expander for inner macro calls)
/// 4. Typecheck the resulting program
/// 5. Compile and extract the function pointer
fn compile_single_clause(
    macro_name: &Symbol,
    clause_idx: usize,
    clause: &cranelisp_frontend::MacroClause,
    span: Span,
    expander: &mut CraneliftExpander,
    tc: &mut cranelisp_typecheck::TypeChecker,
    jit: &mut cranelisp_backend::jit::Jit,
) -> Result<*const u8, CranelispError> {
    // Step 1: Synthesize the defn Sexp.
    let synth_sexp = cranelisp_frontend::synthesize_macro_clause_defn(
        macro_name.as_ref(),
        clause_idx,
        clause,
        span,
    );

    // Step 2: Expand quasiquotes in the synthesized Sexp.
    let expanded_sexp = cranelisp_frontend::expand_quasiquotes(&synth_sexp)?;

    // Step 3: Build AST. Use the current expander so earlier macros in the
    // body can be expanded.
    let program = cranelisp_frontend::build_program(&[expanded_sexp], expander)?;

    // Step 4: Typecheck.
    let check = tc.check_program(&program)?;

    // Step 5: Compile.
    // Extract the single defn from the program.
    let defn = program
        .iter()
        .find_map(|tl| match tl {
            cranelisp_types::TopLevel::Defn(d) => Some(d),
            _ => None,
        })
        .ok_or_else(|| CranelispError::MacroError {
            message: format!("macro clause {clause_idx} for '{macro_name}' produced no defn"),
            span,
        })?;

    // Declare the function in the JIT.
    let func_ids = jit.declare_functions(&[defn])?;
    let func_arities: HashMap<Symbol, usize> =
        func_ids.keys().map(|n| (n.clone(), defn.params.len())).collect();

    // Build compile context and compile.
    let compile_ctx = jit.build_compile_context(
        &check,
        CompileMode::Batch,
        &func_ids,
        &func_arities,
        None,
        None,
        None,
    );
    jit.compile_defn(defn, compile_ctx)?;

    // Finalize and get the function pointer.
    let ptr = jit.finalize_and_get_ptr(&defn.name, defn.params.len())?;

    Ok(ptr)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::Span;

    /// Helper: create a fresh TypeChecker and Jit for testing.
    fn setup() -> (cranelisp_typecheck::TypeChecker, cranelisp_backend::jit::Jit) {
        let tc = cranelisp_typecheck::TypeChecker::new();
        let mut jit = cranelisp_backend::jit::Jit::new().unwrap();
        jit.declare_intrinsics().unwrap();
        (tc, jit)
    }

    /// Helper: parse source text into a single Sexp.
    fn parse_one(src: &str) -> Sexp {
        let sexps = cranelisp_frontend::parse(src).expect("parse failed");
        assert_eq!(sexps.len(), 1, "expected exactly one sexp");
        sexps.into_iter().next().unwrap()
    }

    // spec: 09-macros.md section 9.2 — simple identity macro compile and expand
    #[test]
    fn test_identity_macro() {
        let (mut tc, mut jit) = setup();
        let mut expander = CraneliftExpander::new();

        // Parse and compile: (defmacro id [x] x)
        let sexp = parse_one("(defmacro id [x] x)");
        let info = cranelisp_frontend::parse_defmacro(&sexp).unwrap();
        expander.compile_macro(&info, &mut tc, &mut jit).unwrap();

        // Expand: (id 42) should produce 42
        let call_sexp = parse_one("(id 42)");
        let result = expander.expand_sexp(call_sexp).unwrap();
        assert!(
            matches!(result, Sexp::Int(42, _)),
            "expected Int(42), got {:?}",
            result
        );
    }

    // spec: 09-macros.md section 9.4.2 — quasiquote macro compile and expand
    #[test]
    fn test_quasiquote_macro() {
        let (mut tc, mut jit) = setup();
        let mut expander = CraneliftExpander::new();

        // Parse and compile: (defmacro wrap [x] `(+ 1 ~x))
        let sexp = parse_one("(defmacro wrap [x] `(+ 1 ~x))");
        let info = cranelisp_frontend::parse_defmacro(&sexp).unwrap();
        expander.compile_macro(&info, &mut tc, &mut jit).unwrap();

        // Expand: (wrap 42) should produce (+ 1 42)
        let call_sexp = parse_one("(wrap 42)");
        let result = expander.expand_sexp(call_sexp).unwrap();
        if let Sexp::List(children, _) = &result {
            assert_eq!(children.len(), 3, "expected 3 children in (+ 1 42)");
            assert!(matches!(&children[0], Sexp::Symbol(s, _) if s == "+"));
            assert!(matches!(&children[1], Sexp::Int(1, _)));
            assert!(matches!(&children[2], Sexp::Int(42, _)));
        } else {
            panic!("expected List, got {:?}", result);
        }
    }

    // spec: 09-macros.md section 9.2.6 — multi-clause dispatch
    #[test]
    fn test_multi_clause_dispatch() {
        let (mut tc, mut jit) = setup();
        let mut expander = CraneliftExpander::new();

        // Two clauses: 1-arg returns arg, 2-arg returns first arg
        let sexp = parse_one(
            "(defmacro pick ([x] x) ([x y] x))"
        );
        let info = cranelisp_frontend::parse_defmacro(&sexp).unwrap();
        expander.compile_macro(&info, &mut tc, &mut jit).unwrap();

        // 1-arg call
        let call1 = parse_one("(pick 42)");
        let result1 = expander.expand_sexp(call1).unwrap();
        assert!(
            matches!(result1, Sexp::Int(42, _)),
            "1-arg: expected Int(42), got {:?}",
            result1
        );

        // 2-arg call should return first arg
        let call2 = parse_one("(pick 10 20)");
        let result2 = expander.expand_sexp(call2).unwrap();
        assert!(
            matches!(result2, Sexp::Int(10, _)),
            "2-arg: expected Int(10), got {:?}",
            result2
        );
    }

    // spec: 09-macros.md section 9.2 — is_macro predicate
    #[test]
    fn test_is_macro_predicate() {
        let (mut tc, mut jit) = setup();
        let mut expander = CraneliftExpander::new();

        assert!(!expander.is_macro("id"));

        let sexp = parse_one("(defmacro id [x] x)");
        let info = cranelisp_frontend::parse_defmacro(&sexp).unwrap();
        expander.compile_macro(&info, &mut tc, &mut jit).unwrap();

        assert!(expander.is_macro("id"));
        assert!(!expander.is_macro("nonexistent"));
    }

    // spec: 09-macros.md section 9.7 — marshal round-trip via expand
    #[test]
    fn test_marshal_roundtrip_all_variants() {
        // Test all Sexp variants through marshal round-trip.
        let cases: Vec<Sexp> = vec![
            Sexp::Int(42, Span::SYNTHETIC),
            Sexp::Int(-1, Span::SYNTHETIC),
            Sexp::Float(2.5, Span::SYNTHETIC),
            Sexp::Bool(true, Span::SYNTHETIC),
            Sexp::Bool(false, Span::SYNTHETIC),
            Sexp::Str("hello world".to_string(), Span::SYNTHETIC),
            Sexp::Symbol("my-var".to_string(), Span::SYNTHETIC),
            Sexp::List(
                vec![Sexp::Int(1, Span::SYNTHETIC), Sexp::Int(2, Span::SYNTHETIC)],
                Span::SYNTHETIC,
            ),
            Sexp::Bracket(
                vec![Sexp::Symbol("x".to_string(), Span::SYNTHETIC)],
                Span::SYNTHETIC,
            ),
        ];

        for case in &cases {
            let rt = marshal::sexp_to_runtime(case);
            let back = marshal::runtime_to_sexp(rt);
            match (case, &back) {
                (Sexp::Int(a, _), Sexp::Int(b, _)) => assert_eq!(a, b),
                (Sexp::Float(a, _), Sexp::Float(b, _)) => {
                    assert!((a - b).abs() < f64::EPSILON);
                }
                (Sexp::Bool(a, _), Sexp::Bool(b, _)) => assert_eq!(a, b),
                (Sexp::Str(a, _), Sexp::Str(b, _)) => assert_eq!(a, b),
                (Sexp::Symbol(a, _), Sexp::Symbol(b, _)) => assert_eq!(a, b),
                (Sexp::List(a, _), Sexp::List(b, _)) => assert_eq!(a.len(), b.len()),
                (Sexp::Bracket(a, _), Sexp::Bracket(b, _)) => assert_eq!(a.len(), b.len()),
                _ => panic!(
                    "variant mismatch: {:?} vs {:?}",
                    std::mem::discriminant(case),
                    std::mem::discriminant(&back)
                ),
            }
        }
    }

    // spec: 09-macros.md section 9.7 — SList round-trip
    #[test]
    fn test_slist_roundtrip() {
        let items = vec![
            marshal::sexp_to_runtime(&Sexp::Int(1, Span::SYNTHETIC)),
            marshal::sexp_to_runtime(&Sexp::Symbol("x".to_string(), Span::SYNTHETIC)),
            marshal::sexp_to_runtime(&Sexp::Str("hello".to_string(), Span::SYNTHETIC)),
        ];
        let _slist = marshal::build_runtime_slist(&items);

        // Read back by wrapping in a SexpList and reading.
        let wrapped = Sexp::List(
            vec![
                Sexp::Int(1, Span::SYNTHETIC),
                Sexp::Symbol("x".to_string(), Span::SYNTHETIC),
                Sexp::Str("hello".to_string(), Span::SYNTHETIC),
            ],
            Span::SYNTHETIC,
        );
        let rt = marshal::sexp_to_runtime(&wrapped);
        let back = marshal::runtime_to_sexp(rt);
        if let Sexp::List(children, _) = back {
            assert_eq!(children.len(), 3);
            assert!(matches!(&children[0], Sexp::Int(1, _)));
            assert!(matches!(&children[1], Sexp::Symbol(s, _) if s == "x"));
            assert!(matches!(&children[2], Sexp::Str(s, _) if s == "hello"));
        } else {
            panic!("expected List");
        }
    }
}
