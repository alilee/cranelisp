// spec_05_definitions.rs — Top-level definition forms (Sprint 64 Wave 5 Batch 2).
//
// Covers `spec/05-definitions.md`. Carries forward language-behaviour
// assertions from legacy integration-tier `tests/ring0.rs`, `tests/ring1.rs`,
// `tests/ring2.rs`, `tests/sketch_port.rs`, and `tests/e2e.rs`. REPL canonical
// per `tests/plan/PLAN.md §"Mode canonicalisation"`.
//
// What this file covers:
//   - defn (single-signature) — body, params (§5.1.1)
//   - defn (multi-signature) — arity dispatch (§5.1.2)
//   - Auto-currying (§5.1.3)
//   - deftype — product, sum, enum (§5.2)
//   - deftrait + impl (§5.3, §5.4)
//   - defmacro registration & display (§5.5 — surface only; full macro
//     coverage is in spec_09_macros.rs)
//   - const + def (§5.6, §5.7)
//   - Visibility (§5.11) — defn- private
//   - Docstrings (§5.12)
//   - Definition ordering (§5.13)

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{run_through_all_modes, Cranelisp, PreludeVariant};

fn repl_prims(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(lines)
        .output()
}

/// REPL with the `TestStandard` prelude (Num + `+`, Eq, Ord, Option, Result) —
/// used by the §11.4 constrained-poly × multi-sig cell (CP rows), whose
/// constrained clause needs the `Num`/`+` trait machinery.
fn repl_std(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .stdin(lines)
        .output()
}

// =============================================================================
// §5.1.1 Single-signature defn
// =============================================================================

// spec: spec/05-definitions.md §5.1.1 — defn binds + can be called
#[test]
fn defn_define_and_call() {
    repl_prims("(defn three [] 3)\n(three)\n").assert_stdout_contains(":primitives/Int 3");
}

// spec: spec/05-definitions.md §5.1.1 — defn with one param
#[test]
fn defn_one_param() {
    repl_prims("(defn id [x] x)\n(id 7)\n").assert_stdout_contains(":primitives/Int 7");
}

// spec: spec/05-definitions.md §5.1.1 — "The name MUST be a valid symbol."
// DEFECT (D-name, S87 Stage-C.2 /stdlib rollout): a `defn` whose name embeds
// `->` (e.g. `char->digit`) FAILS to parse — the reader tokenises the `->`
// inside the symbol as the threading-macro head, so the form after the name is
// no longer recognised as the params bracket:
//   `parse error … defn: expected params [...] or variant (...)` (at the `[`).
// A `defn` NAME is an opaque symbol regardless of any embedded `->`; the
// threading reader-macro must not fire inside a symbol token. The control test
// below (`chardigit`, no `->`) parses, isolating `->`-in-symbol as the trigger.
// Worked around in stdlib by shipping `char-to-digit`/`digit-to-char`.
// FAILING-NOT-IGNORED per memory/feedback_failing_not_ignored.md — RED today
// (parse error), GREEN when `->` no longer splits a symbol token.
// → /frontend (reader/symbol tokenisation).
#[test]
fn defn_name_with_arrow_in_symbol_parses() {
    repl_prims("(defn char->digit [c] c)\n")
        .assert_stdout_contains("user/char->digit");
}

// spec: spec/05-definitions.md §5.1.1 — CONTROL for D-name: the SAME defn shape
// with an `->`-free name parses and registers normally. Pins the embedded `->`
// (not the docstring or any other element) as the D-name trigger. GREEN today.
#[test]
fn defn_name_without_arrow_control_parses() {
    repl_prims("(defn chardigit \"d\" [c] c)\n")
        .assert_stdout_contains("user/chardigit");
}

// spec: spec/05-definitions.md §5 — "Declaration heads are binders" + §5.1.1 (user
// ruling 2026-07-18, TB-27 extended to defn): a `defn` head binds a NEW name into
// the CURRENT module, so it is a binder, NOT a reference, and MUST be a bare
// (unqualified) symbol. A qualified spelling `(defn fmt/foo [x] x)` is a compile-
// time error (the dual of the §8.5 reference rules — there is no mechanism for
// declaring a name into another module).
//
// PROBED LIVE (S112 rulings rider): TODAY this SILENTLY ACCEPTS — the REPL binds
// `user/fmt/foo` and echoes `; defn` with no error; under `--run` the defn accepts
// and the failure is deferred to the reference site as an incidental `module 'fmt'
// … not found` (a mode-divergent face). Both violate the binder principle. FAILING-
// NOT-IGNORED until /dev(frontend) rejects the qualified head at the declaration-
// head parse seam (`ast_builder.rs::get_defn_name`). [S113]
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs::get_defn_name found=S112 owner=/dev
#[test]
fn defn_qualified_head_rejected_binder_neg() {
    let out = repl_prims("(defn fmt/foo [x] x)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the qualified defn head `fmt/foo` MUST be a compile-time error (§5 binder \
         principle); today it silently accepts. got:\n{c}"
    );
    assert!(
        !out.stdout.contains("user/fmt/foo"),
        "the qualified head MUST NOT silently bind a `user/fmt/foo` name; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// BD-M1 — Binder-generalization matrix (spec/05-definitions.md §5, "Declaration
// heads are binders"; user ruling 2026-07-18 generalized to ALL native binder
// heads). ONE frontend seam (`reject_qualified_binder_head`, arch Q3); the matrix
// pressures that seam — a form whose cell fails differently has grown its own
// path. Each NATIVE binder form gets a {qualified-head reject, bare-head accept}
// twin. `defn` is pinned above; `deftrait` (bare + parenthesized + method-name)
// lives in spec_07_traits.rs. All qualified-head rejects are RED today (silent-
// accept); they flip at W3 when /dev(frontend) lands the shared reject seam. The
// located-reject proxy is `!contains("not found")` — a LOCATED binder reject at
// the head, never an incidental downstream `module … not found` resolution error.
// defect notation on the reject rows: the shared frontend seam, per arch Q3.
// =============================================================================

// BD-M1 defn- (private) — qualified head reject.
// spec: spec/05-definitions.md §5 — Declaration heads are binders (defn-).
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs::get_defn_name found=S113 owner=/dev
#[test]
fn defn_private_qualified_head_rejected_binder_neg() {
    let out = repl_prims("(defn- fmt/foo [x] x)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the qualified `defn-` head `fmt/foo` MUST be a compile-time error (§5 \
         binder principle); got:\n{c}"
    );
    assert!(
        !out.stdout.contains("user/fmt/foo"),
        "the qualified head MUST NOT silently bind; got:\n{}",
        out.stdout
    );
}

// BD-M1 defn- (private) — bare-head accept TWIN.
// spec: spec/05-definitions.md §5.11 — a bare `defn-` head binds normally.
#[test]
fn defn_private_bare_head_accepts_twin() {
    let out = repl_prims("(defn- helper2 [x] x)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.to_lowercase().contains("error"),
        "a bare `defn-` head MUST bind without error; got:\n{c}"
    );
}

// BD-M1 deftype — qualified head reject.
// spec: spec/05-definitions.md §5 — Declaration heads are binders (deftype).
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs found=S113 owner=/dev
#[test]
fn deftype_qualified_head_rejected_binder_neg() {
    let out = repl_prims("(deftype fmt/Color Red2)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the qualified `deftype` head `fmt/Color` MUST be a compile-time error \
         (§5 binder principle); got:\n{c}"
    );
    assert!(
        !c.contains("not found"),
        "the qualified head MUST be a LOCATED binder reject at the head, NOT an \
         incidental `module 'fmt' … not found` resolution error (the deftype head \
         is treated as a REFERENCE into module `fmt` today); got:\n{c}"
    );
    assert!(
        !out.stdout.contains("user/fmt/Color"),
        "the qualified head MUST NOT silently bind; got:\n{}",
        out.stdout
    );
}

// BD-M1 deftype — bare-head accept TWIN.
// spec: spec/05-definitions.md §5.2 — a bare `deftype` head binds normally.
#[test]
fn deftype_bare_head_accepts_twin() {
    let out = repl_prims("(deftype Colour Red3 Green3)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.to_lowercase().contains("error"),
        "a bare `deftype` head MUST bind without error; got:\n{c}"
    );
}

// BD-M1 deftype- (private) — qualified head reject.
// spec: spec/05-definitions.md §5 — Declaration heads are binders (deftype-).
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs found=S113 owner=/dev
#[test]
fn deftype_private_qualified_head_rejected_binder_neg() {
    let out = repl_prims("(deftype- fmt/Secret Hidden2)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the qualified `deftype-` head `fmt/Secret` MUST be a compile-time error \
         (§5 binder principle); got:\n{c}"
    );
    assert!(
        !c.contains("not found"),
        "the qualified head MUST be a LOCATED binder reject at the head, NOT an \
         incidental `module 'fmt' … not found` resolution error; got:\n{c}"
    );
    assert!(
        !out.stdout.contains("user/fmt/Secret"),
        "the qualified head MUST NOT silently bind; got:\n{}",
        out.stdout
    );
}

// BD-M1 deftype- (private) — bare-head accept TWIN.
// spec: spec/05-definitions.md §5.11 — a bare `deftype-` head binds normally.
#[test]
fn deftype_private_bare_head_accepts_twin() {
    let out = repl_prims("(deftype- Secret2 Hidden3)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.to_lowercase().contains("error"),
        "a bare `deftype-` head MUST bind without error; got:\n{c}"
    );
}

// BD-M1 defmacro — qualified head reject.
// spec: spec/05-definitions.md §5 — Declaration heads are binders (defmacro).
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs found=S113 owner=/dev
#[test]
fn defmacro_qualified_head_rejected_binder_neg() {
    let out = repl_prims("(defmacro fmt/mm [] 0)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the qualified `defmacro` head `fmt/mm` MUST be a compile-time error (§5 \
         binder principle); got:\n{c}"
    );
    assert!(
        !out.stdout.contains("user/fmt/mm"),
        "the qualified head MUST NOT silently bind; got:\n{}",
        out.stdout
    );
}

// BD-M1 defmacro — bare-head accept TWIN.
// spec: spec/05-definitions.md §5.5 — a bare `defmacro` head binds normally.
#[test]
fn defmacro_bare_head_accepts_twin() {
    let out = repl_prims("(defmacro mm2 [] 0)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.to_lowercase().contains("error"),
        "a bare `defmacro` head MUST bind without error; got:\n{c}"
    );
}

// BD-M1 defmacro- (private) — qualified head reject.
// spec: spec/05-definitions.md §5 — Declaration heads are binders (defmacro-).
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs found=S113 owner=/dev
#[test]
fn defmacro_private_qualified_head_rejected_binder_neg() {
    let out = repl_prims("(defmacro- fmt/mm [] 0)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the qualified `defmacro-` head `fmt/mm` MUST be a compile-time error (§5 \
         binder principle); got:\n{c}"
    );
    assert!(
        !out.stdout.contains("user/fmt/mm"),
        "the qualified head MUST NOT silently bind; got:\n{}",
        out.stdout
    );
}

// BD-M1 defmacro- (private) — bare-head accept TWIN.
// spec: spec/05-definitions.md §5.11 — a bare `defmacro-` head binds normally.
#[test]
fn defmacro_private_bare_head_accepts_twin() {
    let out = repl_prims("(defmacro- mm3 [] 0)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.to_lowercase().contains("error"),
        "a bare `defmacro-` head MUST bind without error; got:\n{c}"
    );
}

// BD-M2 (MACRO ROUTE — the distinct path to the same seam). An inline `defmacro`
// whose expansion emits a `defn` with a QUALIFIED head must reject after
// expansion, on the same §5 binder principle — a qualified binder head is illegal
// however it is produced. Stdlib-free: an inline macro, NOT stdlib `def`.
// Silent-accept today → RED; the reject flips at W3 (the shared frontend seam
// reaches macro-expansion output at `build_form`).
// spec: spec/05-definitions.md §5 — the binder rule reaches macro-expansion output.
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs (post-expansion binder reject) found=S113 owner=/dev
#[test]
fn macro_route_qualified_defn_head_rejected_binder_neg() {
    let out = repl_prims("(defmacro mkbad [] `(defn fmt/gen [x] x))\n(mkbad)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "a macro whose expansion emits a qualified `defn` head `fmt/gen` MUST be \
         rejected post-expansion (§5 binder principle reaches macro output); today \
         it silently accepts. got:\n{c}"
    );
    assert!(
        !out.stdout.contains("user/fmt/gen"),
        "the macro-route qualified head MUST NOT silently bind `user/fmt/gen`; \
         got:\n{}",
        out.stdout
    );
}

// Every `a..b` span appearing in `at N..M` positions in the output.
fn spans(s: &str) -> Vec<(u64, u64)> {
    let mut v = Vec::new();
    for seg in s.split("at ") {
        let a_digits: String = seg.chars().take_while(|c| c.is_ascii_digit()).collect();
        if a_digits.is_empty() {
            continue;
        }
        let rest = &seg[a_digits.len()..];
        if let Some(after) = rest.strip_prefix("..") {
            let b_digits: String = after.chars().take_while(|c| c.is_ascii_digit()).collect();
            if b_digits.is_empty() {
                continue;
            }
            if let (Ok(a), Ok(b)) = (a_digits.parse::<u64>(), b_digits.parse::<u64>()) {
                v.push((a, b));
            }
        }
    }
    v
}

// BD-M2 (span provenance cell) — when the macro-route reject fires, its diagnostic
// span MUST point at the USER's WRITTEN form, not the synthesized `defn`. Per
// `design/int/macro-diagnostic-reanchoring.md` (arch-approved option (a), FIXME
// 0650), int re-anchors the synthetic-located diagnostic from macro-expansion
// output to the origin form's span and appends an `in expansion of …` provenance.
// The W4 0650 seam LANDED — the diagnostic now reads `parse error at 0..8:
// 'fmt/gen2' …  in expansion of `(mkbad2)``. The span is turn-relative (each REPL
// line is its own turn with 0-based spans — the invocation `(mkbad2)` is
// legitimately at column 0, so `0..8` is a REAL span, not degenerate). Heuristic:
// a real `a..b` span (b > a), NOT the `0..0` degenerate band, NOT the ≥1_000_000
// synthetic band, NOT `__macro_` internals, and the `in expansion of` provenance
// present. (An earlier `start > 0` proxy was turn-relative-offset-blind and
// wrongly RED'd the correct `0..8` span.)
// spec: spec/05-definitions.md §5 — macro-route reject span points at the written form.
// defect: class=silent-accept locus=src/process_form.rs::reanchor_expansion_diagnostic (re-anchor synthetic diagnostic to origin span + append provenance, FIXME 0650) found=S113 owner=/dev
#[test]
fn macro_route_qualified_head_reject_span_at_written_form() {
    let program = "(defmacro mkbad2 [] `(defn fmt/gen2 [x] x))\n(mkbad2)\n";
    let out = repl_prims(program);
    let c = format!("{}{}", out.stdout, out.stderr);
    // Precondition: the reject must actually fire (shared with BD-M2 reject; W3).
    assert!(
        c.to_lowercase().contains("error"),
        "precondition: the macro-route qualified head must be rejected; got:\n{c}"
    );
    // Provenance: the re-anchoring appends the origin-form context.
    assert!(
        c.contains("in expansion of"),
        "the re-anchored diagnostic MUST append the `in expansion of …` provenance \
         (FIXME 0650 seam); got:\n{c}"
    );
    // Span heuristic: at least one REAL span (b > a), none degenerate `0..0`, none
    // in the ≥1_000_000 synthetic band, no `__macro_` internals.
    let sp = spans(&c);
    assert!(
        !c.contains("__macro_")
            && !sp.contains(&(0, 0))
            && sp.iter().all(|(a, b)| *a < 1_000_000 && *b < 1_000_000)
            && sp.iter().any(|(a, b)| b > a),
        "the macro-route reject diagnostic MUST re-anchor to the user's written \
         form — a real `a..b` span (NOT `0..0`, NOT the ≥1_000_000 synthetic band, \
         NOT `__macro_` internals) (FIXME 0650, W4 int seam); spans seen = {sp:?}; \
         got:\n{c}"
    );
}

// spec: spec/05-definitions.md §5.1.1 — defn with multiple params
#[test]
fn defn_multi_params() {
    repl_prims("(defn add3 [x y z] (add-i64 x (add-i64 y z)))\n(add3 1 2 3)\n")
        .assert_stdout_contains(":primitives/Int 6");
}

// spec: spec/05-definitions.md §5.1.1 — defn with annotated param types
#[test]
fn defn_annotated_params() {
    repl_prims("(defn f [:Int x] x)\n(f 42)\n").assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/05-definitions.md §5.1.1 — the `_` discard parameter is exempt
// from the duplicate-name check; multiple `_` parameters MAY appear in the
// same list (each is an independent, unreferenceable discard). Distinct from
// the duplicate-named-param rejection (`[x x]`), which IS an error.
// (carry: legacy/sketch_port.rs::sketch_run_tests_pass_fn_called — the sole
//  sketch_port assertion-shape not otherwise covered by the active suite.)
#[test]
fn defn_multiple_discard_params_accepted() {
    repl_prims("(defn f [_ _] 42)\n(f 1 2)\n").assert_stdout_contains(":primitives/Int 42");
}

// =============================================================================
// §5.1.2 Multi-signature defn
// =============================================================================

// spec: spec/05-definitions.md §5.1.2 — multi-clause arity dispatch
#[test]
fn defn_multi_clause_arity() {
    repl_prims(
        "(defn f ([] 0) ([x] x) ([x y] (add-i64 x y)))\n(f)\n(f 5)\n(f 3 4)\n",
    )
    .assert_stdout_contains_all(&[
        ":primitives/Int 0",
        ":primitives/Int 5",
        ":primitives/Int 7",
    ]);
}

// =============================================================================
// §5.1.3 Auto-Currying
// =============================================================================

// spec: spec/05-definitions.md §5.1.3 — calling with fewer args returns closure
#[test]
fn defn_auto_curry_call_with_fewer_args() {
    repl_prims(
        "(defn add [x y] (add-i64 x y))\n(let [inc (add 1)] (inc 4))\n",
    )
    .assert_stdout_contains(":primitives/Int 5");
}

// =============================================================================
// §5.1.2 Multi-Signature — additional shapes (Wave 5.6 sketch_port carry-forward)
// =============================================================================

// spec: spec/05-definitions.md §5.1.2 — multi-clause type-based dispatch
// (same arity, different parameter types). Distinct from arity-only dispatch
// already covered by `defn_multi_clause_arity`.
// (carry: legacy/sketch_port.rs::sketch_multi_sig_type_based_dispatch)
#[test]
fn defn_multi_clause_type_dispatch() {
    repl_prims(
        "(defn choose ([x y] (add-i64 x y)) ([x y] (if y x 0)))\n\
         (add-i64 (choose 10 20) (choose 5 true))\n",
    )
    .assert_stdout_contains(":primitives/Int 35");
}

// spec: spec/05-definitions.md §5.1.2 — duplicate clause signatures rejected.
// (carry: legacy/sketch_port.rs::sketch_multi_sig_duplicate_signature_error)
#[test]
fn defn_multi_clause_duplicate_sig_neg() {
    let out = repl_prims("(defn dup ([x] (add-i64 x 1)) ([y] (add-i64 y 2)))\n");
    assert!(
        out.stdout.to_lowercase().contains("error")
            || out.stdout.contains("duplicate"),
        "duplicate clause signature MUST error per §5.1.2; got:\n{}",
        out.stdout
    );
}

// =============================================================================
// §5.2 Type Definition (deftype)
// =============================================================================

// spec: spec/05-definitions.md §5.2 — enum (nullary constructors)
#[test]
fn deftype_enum_construct_and_match() {
    repl_prims(
        "(deftype Color Red Green Blue)\n(match Red [Red 0 Green 1 Blue 2 _ 99])\n",
    )
    .assert_stdout_contains(":primitives/Int 0");
}

// spec: spec/05-definitions.md §5.2 — sum type with field
#[test]
fn deftype_sum_with_field_match() {
    repl_prims(
        "(deftype (Maybe a) Nothing (Just [:a v]))\n(match (Just 5) [(Just x) x Nothing 0])\n",
    )
    .assert_stdout_contains(":primitives/Int 5");
}

// spec: spec/05-definitions.md §5.2 — a data constructor's fields are a
// bracketed [:Type name] list (grammar §5.2: constructor = name | '(' name
// docstring? field_list ')'; field_list = '[' field_def* ']'). A bare
// `(Ctor :Type)` — no brackets, no field name — is NOT a valid constructor.
// DEFECT (found S106 via the /int embedded agent; user-reported): the frontend
// SILENTLY ACCEPTS `(L :Int)`, parsing `:Int` as a type annotation on the
// constructor and DROPPING the field — L/R collapse to NULLARY constructors (a
// silent enum). `(deftype Rotation (L :Int) (R :Int))` thus registers an enum
// with nullary L/R instead of erroring, discarding both intended Int fields
// with no diagnostic (`L` then introspects as a value `:user/Rotation
// Rotation.L`, not `(Fn [Int] Rotation)`). Expected: a compile error naming the
// missing field name / brackets.
// FAILING-NOT-IGNORED per memory/feedback_failing_not_ignored.md — RED today
// (no error is emitted); GREEN when the frontend rejects the nameless field.
// FIXME(/frontend)
#[test]
fn deftype_ctor_nameless_type_field_rejected_neg() {
    let out = repl_prims("(deftype Rotation (L :Int) (R :Int))\n");
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "a constructor field `(L :Int)` — no brackets, no field name — MUST be a \
         compile error per §5.2 (fields are [:Type name] lists), not silently \
         accepted as a nullary constructor; got:\n{}",
        out.stdout
    );
}

// spec: spec/05-definitions.md §5.2 — POSITIVE companion to the nameless-field
// rejection (S107 item 1): a CORRECTLY-bracketed sum type still constructs. This
// guards that the frontend's rejection of a bare `(L :Int)` is NARROW — it MUST
// NOT break the well-formed `(L [:Int n])` constructor. `L` introspects as the
// unary constructor function `(Fn [primitives/Int] user/Rotation)` and `(L 5)`
// builds the value `(Rotation.L 5)`. GREEN today; MUST stay GREEN across the fix.
#[test]
fn deftype_sum_bracketed_field_still_constructs() {
    let out = repl_prims(
        "(deftype Rotation (L [:Int n]) (R [:Int n]))\n\
         L\n\
         (L 5)\n",
    );
    // L is a first-class unary constructor function, NOT a nullary value.
    out.assert_stdout_contains_all(&[
        ":(Fn [primitives/Int] user/Rotation) user/Rotation.L",
        // (L 5) builds a real value — the constructor is not degraded to an enum.
        ":user/Rotation (Rotation.L 5)",
    ]);
}

// spec: spec/05-definitions.md §5.2 — TIGHTER NEGATIVE for the silent-enum bug
// (S107 item 1). Companion to `deftype_ctor_nameless_type_field_rejected_neg`
// (which asserts the presence of an `error`); this pins the SPECIFIC symptom that
// MUST NOT occur: after the malformed `(deftype Rotation (L :Int) (R :Int))`, the
// bare `L` MUST NOT introspect as a NULLARY value `:user/Rotation Rotation.L`
// (the exact silent-enum collapse — the `:Int` field swallowed and `L` degraded
// to a fieldless constructor). FAILING-NOT-IGNORED per
// memory/feedback_failing_not_ignored.md — RED today (`L` introspects as the
// nullary `:user/Rotation Rotation.L`); GREEN when the frontend rejects the
// nameless field so `L` is never registered as a nullary ctor. FIXME(/frontend)
#[test]
fn deftype_ctor_nameless_field_not_nullary_neg() {
    let out = repl_prims(
        "(deftype Rotation (L :Int) (R :Int))\n\
         L\n",
    );
    // The nullary-value introspection is the silent-enum symptom the fix removes.
    assert!(
        !out.stdout.contains(":user/Rotation Rotation.L"),
        "after the malformed `(L :Int)` field, `L` MUST NOT introspect as a \
         nullary value `:user/Rotation Rotation.L` — the `:Int` field must not be \
         silently swallowed into a fieldless constructor (§5.2); got:\n{}",
        out.stdout
    );
}

// spec: spec/05-definitions.md §5.2 — a data constructor's grammar is
// `'(' name docstring? field_list ')'` — there is NOTHING legal after the
// `field_list`. A form appearing AFTER a valid `[:Type name]` field bracket
// therefore MUST be a compile error, not silently dropped.
// DEFECT (found S107 via code review; DISTINCT from the item-1 nameless-field
// case `deftype_ctor_nameless_type_field_rejected_neg` above): `build_constructor_def`
// in `cranelisp-frontend` only inspects the child immediately after the ctor name
// (`children[next]`) and IGNORES anything after the field bracket. So
// `(deftype Box (Box [:Int n] extra))` SILENTLY ACCEPTS `Box` as a one-field
// constructor and DISCARDS the trailing `extra` with no diagnostic — `Box`
// introspects as `(Fn [primitives/Int] user/Box)` exactly as if `extra` were
// never written. Expected: a compile error naming the unexpected trailing form.
// FAILING-NOT-IGNORED per memory/feedback_failing_not_ignored.md — RED today
// (the trailing form is silently dropped, no error is emitted); GREEN when
// `/frontend` rejects the trailing form after the field bracket.
// FIXME(/frontend)
#[test]
fn deftype_ctor_trailing_form_after_field_bracket_rejected_neg() {
    let out = repl_prims("(deftype Box (Box [:Int n] extra))\n");
    assert!(
        out.stdout.to_lowercase().contains("error"),
        "a constructor form after a valid `[:Type name]` field bracket \
         (`(Box [:Int n] extra)`) MUST be a compile error per §5.2 (grammar: \
         constructor = '(' name docstring? field_list ')' — nothing follows the \
         field_list), not silently dropped; got:\n{}",
        out.stdout
    );
}

// spec: spec/05-definitions.md §5.2 — product type
#[test]
fn deftype_product_construct_and_destructure() {
    repl_prims(
        "(deftype Point [:Int x :Int y])\n(match (Point 3 4) [(Point a b) (add-i64 a b)])\n",
    )
    .assert_stdout_contains(":primitives/Int 7");
}

// spec: spec/05-definitions.md §5.2.4 — bare-field-name shortcut syntax
// `(deftype Pair [first second])` — fresh type vars assigned to bare field
// names, no `:Type` annotation required. Distinct from explicitly-annotated
// product shape.
// (carry: legacy/sketch_port.rs::sketch_adt_shortcut_syntax)
#[test]
fn deftype_product_shortcut_field_names() {
    // This test validates the bare-field-name SHORTCUT SYNTAX itself, so it
    // must define its OWN `Pair` — reuse of the seeded `primitives/Pair` would
    // erase the syntax under test. `Pair` is prelude-seeded, so the deftype is
    // only legal with the prelude SUPPRESSED (§8.6.4). Run bare (no prelude):
    // `Pair` is then not in scope and the shortcut deftype is a fresh, legal
    // definition; the Int literal still displays as `:primitives/Int`.
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::None)
        .stdin(
            "(deftype Pair [first second])\n\
             (match (Pair 7 8) [(Pair a b) a])\n",
        )
        .output()
        .assert_stdout_contains(":primitives/Int 7");
}

// spec: spec/05-definitions.md §5.2 — constructor as first-class value
// (let-bound, then called as a function). Distinct from operator-as-value
// and defn-as-value first-class shapes.
// (carry: legacy/sketch_port.rs::sketch_adt_first_class_constructor)
//
// NOTE: `MySome` is a SUM constructor (ctor name `MySome` ≠ type name `MyOpt`),
// so it keys distinctly in the symbol table. The single-ctor PRODUCT case where
// ctor name == type name (the `R`/`R` collision) is the
// `single_ctor_product_constructor_as_first_class_value` guard below.
#[test]
fn deftype_constructor_as_first_class_value() {
    repl_prims(
        "(deftype (MyOpt a) MyNone (MySome [:a mval]))\n\
         (let [f MySome] (match (f 42) [MyNone 0 (MySome v) v]))\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/04-expressions.md §4.2.1 — a single-ctor PRODUCT constructor used
// as a first-class value (let-bound, then called as a function).
//
// This is the §4.2.1 spec-violation GUARD for the S79 Option-3 product-ctor-as-
// Def correction (FIXME 0319). For a single-ctor product `(deftype R [:Int w
// :Int h])` the constructor name `R` collides with the type name `R` on the
// symbol-table key. Before the dual-facet correction the surviving entry was the
// `TypeDef`, which carries no GOT slot and is absent from `defined_symbols()` —
// so referencing the product ctor as a VALUE (`(let [f R] ...)`, `(g R ...)`)
// failed to compile (`undefined variable: R` / no codegen). §4.2.1 says "data
// constructors ... evaluate to constructor functions ... a function value that
// ... can be ... bound with `let`, passed as an argument" — the product ctor
// MUST be a first-class value exactly like the sum ctor above. The correction
// makes the surviving `"R"` entry the got-slotted ctor `Def` carrying a type
// facet, so the product ctor flows through `defined_symbols()` and got-slots
// like any other ctor. This was RED before the correction; it is GREEN now.
#[test]
fn single_ctor_product_constructor_as_first_class_value() {
    // let-bound product ctor, then called: (f 3 4) builds (R 3 4), area = 7.
    repl_prims(
        "(deftype R [:Int w :Int h])\n\
         (defn add-fields [c] (match c [(R a b) (add-i64 a b)]))\n\
         (let [f R] (add-fields (f 3 4)))\n",
    )
    .assert_stdout_contains(":primitives/Int 7");
}

// spec: spec/04-expressions.md §4.2.1 — a single-ctor PRODUCT constructor passed
// as a higher-order argument (the `(map R …)`-style use). Companion to
// `single_ctor_product_constructor_as_first_class_value`: there the product ctor
// is let-bound; here it crosses a function-call boundary as an argument value
// (`(apply2 R 3 4)`), exercising the same "product ctor is a first-class value"
// requirement on the argument-passing path. Runs through `--run` (the product
// ctor's value must survive into batch codegen / `defined_symbols()`); exit = 7.
#[test]
fn single_ctor_product_constructor_passed_as_higher_order_arg() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Int add-i64 Pure]])\n\
             (deftype R [:Int w :Int h])\n\
             (defn apply2 [f a b] (f a b))\n\
             (defn area [c] (match c [(R w h) (add-i64 w h)]))\n\
             (defn main [] (Pure (area (apply2 R 3 4))))",
        )
        .run("main.cl")
        .output()
        .assert_exit(7);
}

// =============================================================================
// §5.3 + §5.4 deftrait + impl
// =============================================================================

// spec: spec/05-definitions.md §5.3 — deftrait + impl + invoke method
#[test]
fn deftrait_impl_and_dispatch() {
    // Per the impl syntax in spec/07-traits.md §7.3, methods inside impl
    // bodies use the (defn name [params] body) shape.
    repl_prims(
        "(deftrait Shape (area [self] Int))\n\
         (deftype Square [:Int side])\n\
         (impl Shape Square (defn area [s] (match s [(Square n) (mul-i64 n n)])))\n\
         (area (Square 5))\n",
    )
    .assert_stdout_contains(":primitives/Int 25");
}

// =============================================================================
// §5.5 defmacro (surface only — full coverage in spec_09_macros.rs)
// =============================================================================

// spec: spec/05-definitions.md §5.5 — defmacro registers and displays
#[test]
fn defmacro_registers_with_display() {
    repl_prims("(defmacro id [x] x)\n").assert_stdout_contains_all(&["user/id", "defmacro"]);
}

// =============================================================================
// §5.6 / §5.7 const + def — prelude macros, not in TestStandard fixture
// =============================================================================
//
// `const` and `def` are documented as prelude-provided macros (§5.6, §5.7).
// They live in the project's prelude (e.g., `stdlib/prelude.cl`), not in
// the `tests/fixtures/preludes/test-standard.cl` fixture. Coverage for
// these forms lives in `tests/spec_11_stdlib.rs` which is the named
// exception that loads the workspace stdlib.

// =============================================================================
// §5.11 Visibility (defn- private)
// =============================================================================

// spec: spec/05-definitions.md §5.11 — defn- callable from same module
#[test]
fn private_defn_callable_in_module() {
    repl_prims("(defn- helper [] 41)\n(defn main [] (add-i64 (helper) 1))\n(main)\n")
        .assert_stdout_contains(":primitives/Int 42");
}

// =============================================================================
// §5.12 Docstrings — registered, no observable effect on call
// =============================================================================

// spec: spec/05-definitions.md §5.12 — docstring on defn does not break call
#[test]
fn docstring_does_not_affect_call() {
    repl_prims("(defn inc \"Increment by one\" [x] (add-i64 x 1))\n(inc 9)\n")
        .assert_stdout_contains(":primitives/Int 10");
}

// =============================================================================
// §5.13 Definition Ordering — forward references between defns
// =============================================================================

// spec: spec/05-definitions.md §5.13 — defn forward reference to later defn
//
// Mode-specific exception: definition ordering is a module-compilation
// property (a module is compiled as a unit), not a per-form REPL property.
// We test through `--run` against an on-disk module so the spec property
// (forward references resolve when the whole module is compiled) is what
// is observed.
#[test]
fn forward_reference_between_defns() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (defn main [] (Pure (use-helper)))\n\
             (defn use-helper [] (helper-fn))\n\
             (defn helper-fn [] 5)",
        )
        .run("main.cl")
        .output()
        .assert_exit(5);
}

// spec: spec/05-definitions.md §5.13.1 — defns may reference each other
// across forward-decl ordering. Distinct from
// `forward_reference_between_defns` (single-direction chain a→b→c): this
// test exercises the bidirectional shape where two defns each reference
// the other via interleaved forward-references within a single module
// compilation unit.
// (carry: legacy/ring0.rs::mutual_forward_references)
#[test]
fn defns_mutual_forward_references() {
    // is-positive references gt-i64; classify references is-positive.
    // main combines two classify calls. Both functions are defined before
    // main — but is-positive is referenced by classify *before* the
    // body-of-classify is type-checked, exercising the module-as-unit
    // forward-reference resolution. (5+10) + 3 = 18.
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [*]])\n\
             (defn is-positive [n] (if (gt-i64 n 0) 1 0))\n\
             (defn classify [n] (if (eq-i64 (is-positive n) 1) (add-i64 n 10) (sub-i64 0 n)))\n\
             (defn main [] (Pure (add-i64 (classify 5) (classify (sub-i64 0 3)))))",
        )
        .run("main.cl")
        .output()
        .assert_exit(18);
}

// =============================================================================
// Wave 5.6 ring1.rs GAP-COVER carry-forwards (chunks 2-3)
// =============================================================================

// spec: spec/05-definitions.md §5.2.2 — closure-call result used as ctor
// argument: `(Some (f 41))`. Exercises the eval-order of arg vs ctor
// wrap, plus the heap-temp lifetime through the ctor wrap. Distinct from
// `closure_returning_adt` where the closure body wraps in the ctor
// (opposite ordering — here the ctor is OUTSIDE the closure body).
// (carry: legacy/ring1.rs::adt_containing_closure_result)
#[test]
fn data_constructor_arg_from_closure_call_result() {
    // Reuse the prelude-seeded `primitives/Option` (§8.6.4: a local Option
    // deftype under the Option-providing prelude is a define-over-prelude
    // collision). The ctor-arg-from-closure-result shape is unaffected.
    repl_prims(
        "(let [f (fn [x] (add-i64 x 1))]\n\
           (match (Some (f 41)) [(Some x) x None 0]))\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// spec: spec/05-definitions.md §5.2.6 — Generated Accessors.
// FAILING-NOT-IGNORED defect repro (FIXME 0351, target /typecheck, S83).
// Spec §5.2.6: "For each named field in a type definition, an accessor
// function is automatically generated in the enclosing scope. The
// accessor's name is the field name." Product accessors are total and
// MUST return the field value: `(v (Box 5))` -> 5. As-built the accessor
// `v` is not generated as a free callable — the call errors with
// `undefined variable: v`. Single-file, no module/super-import involved.
// This is the (b) repro of 0351; spec arbitration confirmed accessors ARE
// auto-generated free fns (not match-only), so this is a genuine defect.
#[test]
fn generated_field_accessor_resolves_as_free_callable() {
    repl_prims(
        "(deftype Box [:primitives/Int v])\n(v (Box 5))\n",
    )
    .assert_stdout_contains(":primitives/Int 5");
}

// spec: spec/05-definitions.md §5.2.6 — Generated Accessors are first-class.
// FAILING-NOT-IGNORED defect repro (FIXME 0351(a), target /typecheck, S83).
// Spec §5.2.6 closing sentence: "Accessor functions are first-class values
// and can be passed as arguments or bound to variables." This guards the
// first-class facet specifically: the synthesised product accessor `v` must
// be let-bindable (`(let [g v] ...)`) and then callable as an ordinary
// function value. As-built `v` is not synthesised as a free callable, so the
// `let`-binding fails with `undefined variable: v`. Companion to
// `generated_field_accessor_resolves_as_free_callable` (direct call); this
// test pins the value-passing path. The Wave-2 typecheck synthesis flips it.
#[test]
fn accessor_is_first_class_value_passable() {
    repl_prims(
        "(deftype Box [:primitives/Int v])\n(let [g v] (g (Box 7)))\n",
    )
    .assert_stdout_contains(":primitives/Int 7");
}

// spec: spec/05-definitions.md §5.2.6 — Generated Accessors, collision case.
// FAILING-NOT-IGNORED defect repro (FIXME 0351(a), target /typecheck, S83).
// Negative/safety guard: a user defines `(defn v ...)` BEFORE a `deftype`
// whose field name `v` would synthesise a colliding accessor. The disposition
// MUST be SAFE: the process exits normally (no SIGSEGV, no signal-kill, no
// silent memory corruption / wrong-dispatch). §5.2.6 specifies that accessors
// ARE synthesised but is SILENT on what happens when the synthesised name
// collides with an existing same-module binding.
//
// FAILING-FIRST design: TODAY no accessor is synthesised, so the user's
// `(defn v [x] 99)` silently absorbs the field name and `(v (Box 9))` answers
// 99 with NO acknowledgement that a colliding accessor `v` was suppressed —
// a SILENT collision. Once Wave-2 synthesises the accessor, the clash becomes
// live and the safe disposition is to SURFACE it rather than silently pick a
// winner: this guard requires a clear diagnostic naming the collision. That
// assertion is RED today (current output is the silent `:primitives/Int 99`
// with no diagnostic) and flips green when the Wave-2 fix detects and reports
// the clash. The no-crash floor is asserted alongside so a SIGSEGV/signal-kill
// can never be mistaken for a "pass".
//
// FIXME(/spec): §5.2.6 does not state the accessor-vs-existing-binding
// collision policy. This guard pins "clear diagnostic" as the safe
// disposition; if /spec instead rules deterministic last-wins (user binding
// wins, accessor suppressed — with the suppression made observable), retarget
// the diagnostic assertion to that determinate policy. The open question is
// flagged here as a code comment for the Wave-2 /typecheck implementer; the
// formal route is a numbered design/arch/fixmes entry if /dev hits the edge
// (per SPRINT §/design 0351(a) note: "Collision policy is an open edge").
#[test]
fn accessor_neg_synth_does_not_shadow_existing_binding() {
    let out = repl_prims(
        "(defn v [x] 99)\n\
         (deftype Box [:primitives/Int v])\n\
         (v (Box 9))\n",
    );
    // SAFETY floor: the REPL process must terminate normally — a SIGSEGV or
    // any signal-kill (status.code() == None) is the corruption mode this
    // guard forbids first and foremost.
    assert!(
        out.status.code().is_some(),
        "accessor/binding collision MUST NOT crash (SIGSEGV / signal-kill) \
         per §5.2.6 safety floor; the process was signalled. stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
    // SAFE-DISPOSITION pin (RED today): the collision MUST be surfaced with a
    // clear diagnostic rather than silently resolved. Today the accessor is
    // not synthesised so no clash is reported (`:primitives/Int 99` only) —
    // this assertion fails until Wave-2 detects and reports the collision.
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.to_lowercase().contains("error")
            || combined.to_lowercase().contains("collision")
            || combined.to_lowercase().contains("conflict")
            || combined.to_lowercase().contains("already")
            || combined.to_lowercase().contains("duplicate")
            || combined.to_lowercase().contains("shadow"),
        "accessor `v` synthesised over an existing `(defn v ...)` MUST surface \
         the collision with a clear diagnostic (safe disposition), not silently \
         pick a winner, per the §5.2.6 safety floor; got stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/05-definitions.md §5.2.6 — Generated Accessors, cross-type
// spec: spec/08-modules.md §8.6.5 — bare-name ambiguity (poisoning)
//
// Two product types `Box` and `Cup` in the SAME module each carry a field
// named `v`, so each generates an accessor named `v`. Per §5.2.6 + §8.6.5
// (user ruling S83 W2) the bare accessor `v` is **ambiguous (poisoned)** —
// NOT folded into an argument-type-dispatched overload and NOT first-wins
// shadowed. The ruled behaviour, asserted here against single-cluster
// `--run` (where the poison is realised; the REPL per-cluster path is the
// deferred cross-cluster-rehydration gap, FIXME 0364 → /design):
//
//   1. Defining BOTH deftypes does NOT error on the second `deftype` — both
//      types coexist; a program that defines both and reaches `v` only via
//      `match` type-checks and runs cleanly (sub-programs 2 & 3 prove this).
//   2. A **bare** use of the poisoned accessor `(v (Box 5))` is a
//      compile-time **ambiguity error** listing the qualified alternatives
//      (`ambiguous bare name 'v'`, `Box.v`, `Cup.v`).
//   3. The field stays reachable via `match` (§6): `(match (Box 5) [(Box v)
//      v])` -> 5 and `(match (Cup 9) [(Cup v) v])` -> 9. (`Box.v` dotted
//      accessor syntax is the deferred escape, FIXME 0365; today `match`
//      and module-qualification are the working escapes.)
#[test]
fn accessor_cross_type_duplicate_field_name() {
    // (1)+(2) Bare use of the poisoned accessor is a compile-time ambiguity
    //          error. The error proves the second deftype did NOT crash the
    //          module (it parsed + registered; the failure is at the USE
    //          site, not the second definition) and that the bare name is
    //          poisoned rather than silently first-wins/overload-folded.
    let bare = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(
            "(deftype Box [:primitives/Int v])\n\
             (deftype Cup [:primitives/Int v])\n\
             (defn main [] (Pure (v (Box 5))))",
        )
        .output();
    let bare_combined = format!("{}{}", bare.stdout, bare.stderr);
    assert!(
        bare_combined.contains("ambiguous bare name 'v'"),
        "bare use of the duplicate-field accessor `v` MUST be a compile-time \
         ambiguity error naming `ambiguous bare name 'v'` per §5.2.6 + \
         §8.6.5; got stdout={} stderr={}",
        bare.stdout,
        bare.stderr
    );
    // The ambiguity error lists the qualified alternatives.
    assert!(
        bare_combined.contains("Box.v") && bare_combined.contains("Cup.v"),
        "the ambiguity error MUST list the qualified alternatives `Box.v` \
         and `Cup.v` per §8.6.5; got stdout={} stderr={}",
        bare.stdout,
        bare.stderr
    );
    // It MUST NOT silently fold into an overload or pick a winner: a poisoned
    // bare use does not succeed (no value reaches the exit / stdout).
    assert!(
        !bare_combined.contains(":primitives/Int 5"),
        "the poisoned bare accessor MUST NOT silently dispatch to a value \
         (no overload, no first-wins winner) per §5.2.6; got stdout={} \
         stderr={}",
        bare.stdout,
        bare.stderr
    );

    // (3) The field stays reachable via `match`. Both deftypes coexist and the
    //     program runs cleanly — exit code carries the Pure-wrapped Int
    //     (post-S80 main:IO rule).
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(
            "(deftype Box [:primitives/Int v])\n\
             (deftype Cup [:primitives/Int v])\n\
             (defn main [] (Pure (match (Box 5) [(Box v) v])))",
        )
        .output()
        .assert_exit(5);

    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(
            "(deftype Box [:primitives/Int v])\n\
             (deftype Cup [:primitives/Int v])\n\
             (defn main [] (Pure (match (Cup 9) [(Cup v) v])))",
        )
        .output()
        .assert_exit(9);
}

// spec: spec/05-definitions.md §5.2.6 — Generated Accessors, cross-type
// spec: spec/08-modules.md §8.6.5 — bare-name ambiguity (poisoning)
//
// FAILING-NOT-IGNORED defect guard for the REPL/`--run` divergence in the
// same-module duplicate-field accessor ruling. See FIXME 0366
// (design/arch/fixmes/0366-typecheck-repl-cross-cluster-accessor-collision-rehydration.md).
//
// The single-cluster `--run`/`--link` path (asserted green in
// `accessor_cross_type_duplicate_field_name` above) poisons the bare
// accessor `v` correctly. The REPL processes each input as a SEPARATE
// cluster, and the duplicate-field poison classifier keys on the per-
// `CheckState` `synthesised_accessor_names` set (adt.rs) — which is empty on
// the cluster that defines `Cup` (the first accessor `v` from `Box` was
// committed in a PRIOR cluster, not in this `CheckState`). The collision is
// therefore missed and the REPL falls into the still-live suppress-and-
// first-wins path (program.rs `deferred_accessor_collisions`), emitting the
// warning "the accessor is suppressed and the existing binding is kept" and
// then resolving `(v (Box 5))` to `5`.
//
// The spec gives the REPL no exemption from §5.2.6 + §8.6.5: a bare use of a
// duplicate-field accessor MUST be a compile-time ambiguity error in EVERY
// mode. This test asserts the SPEC-CORRECT behaviour and therefore FAILS
// today (the REPL returns `:primitives/Int 5` + a warning, not the error).
// It flips green when the cross-cluster rehydration gap is fixed in
// cranelisp-typecheck (re-derive the accessor collision from the COMMITTED
// live symbol-table entry when synthesising in a later cluster — analogous
// to the staging+live union probe in commit b612532 for the non-accessor
// collision). Severity: low (REPL-only, niche), but a genuine
// spec-conformance divergence between modes.
#[test]
fn repl_cross_cluster_duplicate_field_accessor_is_ambiguous() {
    // SEPARATE REPL inputs => separate clusters: `Box` and `Cup` are defined
    // on distinct lines, then the bare poisoned accessor is used on a third.
    let out = repl_prims(
        "(deftype Box [:primitives/Int v])\n\
         (deftype Cup [:primitives/Int v])\n\
         (v (Box 5))\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);

    // The bare use of the duplicate-field accessor MUST be a compile-time
    // ambiguity error in the REPL, exactly as in `--run`/`--link`.
    assert!(
        combined.contains("ambiguous bare name 'v'"),
        "REPL bare use of the cross-cluster duplicate-field accessor `v` MUST \
         be a compile-time ambiguity error naming `ambiguous bare name 'v'` \
         per §5.2.6 + §8.6.5 (no REPL exemption); got stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
    // It MUST NOT silently first-wins: the poisoned bare use does not resolve
    // to a value. Today the REPL prints `:primitives/Int 5` here — the red.
    assert!(
        !combined.contains(":primitives/Int 5"),
        "the REPL MUST NOT silently first-wins-resolve the poisoned bare \
         accessor to `5` per §5.2.6; the cross-cluster collision must poison \
         `v` just as the single-cluster path does; got stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/05-definitions.md §5.2.6 — Generated Accessors, bare-field
// ambiguity DIAGNOSTIC QUALITY (S91 Phase 6, defect surfaced by /docs).
// FAILING-NOT-IGNORED defect repro — routes to /typecheck to improve the
// REPL ambiguity message.
//
// §5.2.6 requires that when two types share a field name, a BARE use of that
// field name produces "a compile-time error that lists the canonical
// alternatives (`Box.v`, `Cup.v`)". With `(deftype Box [:primitives/Int v])`
// and `(deftype Cup [:primitives/Bool v])` both defined, the BEHAVIOUR is
// already correct (bare `v` is rejected; canonical `Box.v`/`Cup.v` both work —
// see `type_member_field_accessor_disambiguates_poisoned_field`). Only the
// DIAGNOSTIC is below spec: the `--run` path lists both alternatives
// (`ambiguous bare name 'v' — use a qualified accessor (Box.v or Cup.v)`,
// guarded green by `accessor_cross_type_duplicate_field_name`), but the **REPL**
// path truncates the message to a bare `ambiguous bare name 'v'` with NEITHER
// canonical alternative listed. §5.2.6 gives the REPL no exemption — the error
// MUST list BOTH `Box.v` AND `Cup.v` in every mode so the user is told how to
// disambiguate. This is RED today (REPL message names neither alternative) and
// flips green when /typecheck threads the canonical-alternative list into the
// REPL-path diagnostic. The field types here differ (Int vs Bool) to match the
// exact shape /docs reported.
#[test]
fn bare_field_ambiguity_message_lists_both_alternatives() {
    let out = repl_prims(
        "(deftype Box [:primitives/Int v])\n\
         (deftype Cup [:primitives/Bool v])\n\
         (v (Box 7))\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    // The diagnostic MUST be framed as an ambiguity (not "undefined variable").
    assert!(
        combined.contains("ambiguous"),
        "bare use of the duplicate-field accessor `v` MUST be framed as an \
         ambiguity error (not \"undefined variable\") per §5.2.6; got stdout={} \
         stderr={}",
        out.stdout,
        out.stderr
    );
    // RED today (REPL path): the message MUST list BOTH canonical alternatives
    // `Box.v` AND `Cup.v` so the user learns how to disambiguate. The REPL today
    // emits only the bare `ambiguous bare name 'v'` with neither name.
    assert!(
        combined.contains("Box.v") && combined.contains("Cup.v"),
        "the ambiguity error MUST list BOTH canonical alternatives `Box.v` and \
         `Cup.v` per §5.2.6 (no REPL exemption); got stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/05-definitions.md §5.2.7 — constructor arity rejection:
// `(Point 1)` where Point expects two args. No prior spec_05 test
// isolated ADT-constructor arity rejection; `defn_multi_clause_arity`
// covers defn arity (positive). Ctor arity is a distinct lookup path.
// (carry: legacy/ring1.rs::error_adt_constructor_wrong_arg_count)
#[test]
fn deftype_product_constructor_arity_mismatch_neg() {
    let out = repl_prims(
        "(deftype Point [:Int x :Int y])\n\
         (Point 1)\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.to_lowercase().contains("error")
            || combined.to_lowercase().contains("arg")
            || combined.to_lowercase().contains("arity")
            || combined.to_lowercase().contains("expect"),
        "(Point 1) with Point [:Int x :Int y] MUST produce an arity-mismatch \
         diagnostic per §5.2.7; got stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/05-definitions.md §5.2.7 — constructor argument-type
// rejection: `(Point true 2)` where the first slot expects Int. The
// product-ctor-type-check angle is uncovered —
// `deftype_product_construct_and_destructure` is positive only.
// (carry: legacy/ring1.rs::error_adt_constructor_wrong_type)
#[test]
fn deftype_product_constructor_wrong_arg_type_neg() {
    let out = repl_prims(
        "(deftype Point [:Int x :Int y])\n\
         (match (Point true 2) [(Point x y) x])\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("Bool")
            || combined.contains("Int")
            || combined.to_lowercase().contains("type")
            || combined.to_lowercase().contains("error"),
        "(Point true 2) MUST produce a type-mismatch diagnostic naming \
         Bool / Int / type / error per §5.2.7; got stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/05-definitions.md §5.2 — undefined-constructor lookup:
// `(Foo 1 2)` where Foo is never defined. Distinct from
// `variable_reference_unbound_errors` (in spec_04) — constructor lookup
// is a different code path (constructor table vs symbol table).
// (carry: legacy/ring1.rs::error_undefined_constructor)
#[test]
fn data_constructor_undefined_lookup_neg() {
    let out = repl_prims("(Foo 1 2)\n");
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("Foo")
            || combined.to_lowercase().contains("undefined")
            || combined.to_lowercase().contains("unbound")
            || combined.to_lowercase().contains("error"),
        "(Foo 1 2) where Foo is never defined MUST produce a diagnostic \
         naming Foo / undefined / unbound / error per §5.2; got stdout={} \
         stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/05-definitions.md §5.2.2 — Vec containing ADT values:
// `[(Some 1) None (Some 3)]`, vec-get + match. Heap-element vec with
// mixed-tag ADTs. Distinct from all covered shapes — exercises ADT-in-vec
// lifetime + dispatch through match after vec-get.
// (carry: legacy/ring1.rs::vec_of_adts)
#[test]
fn vec_containing_adt_elements_get_and_match() {
    // Reuse the prelude-seeded `primitives/Option` (see §8.6.4 note above).
    repl_prims(
        "(match (vec-get [(Some 1) None (Some 3)] 0) [(Some x) x None 0])\n",
    )
    .assert_stdout_contains(":primitives/Int 1");
}

// =============================================================================
// Wave 5.6 ring1.rs GAP-COVER carry-forwards (chunk 4)
// =============================================================================

// spec: spec/05-definitions.md §5.2.7 — constructor with wrong-typed
// argument: `(Point true 2)` where `Point [:Int x :Int y]` expects
// `Int`. The diagnostic MUST name the offending actual type "Bool".
// Distinct from chunk-3 `error_adt_constructor_wrong_type` which
// asserts any of Bool/Int/type indicators; this is the strict
// Bool-naming variant per the U1.7 Wave 3 error-quality contract.
// (carry: legacy/ring1.rs::error_quality_constructor_wrong_type_names_bool)
#[test]
fn deftype_product_constructor_wrong_arg_type_names_bool_strict() {
    let out = repl_prims(
        "(deftype Point [:Int x :Int y])\n\
         (match (Point true 2) [(Point x y) x])\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains("Bool"),
        "diagnostic MUST name 'Bool' for the wrong-typed ctor arg, got: {combined}"
    );
}

// =============================================================================
// Wave 5.6 file 8 ring2.rs chunk 4 GAP-COVER carry-forwards.
// =============================================================================

// spec: spec/05-definitions.md §5.2.5 — a `deftype` MAY carry a docstring
// between the type name and the constructor list. The docstring MUST NOT
// affect construction or match dispatch. Existing
// `docstring_does_not_affect_call` covers defn-with-docstring; this is
// the deftype companion (no prior carry).
// (carry: legacy/ring2.rs::docstring_on_deftype)
#[test]
fn deftype_with_docstring_does_not_affect_construct_or_match() {
    repl_prims(
        "(deftype Color \"A primary color\" Red Green Blue)\n\
         (match Green [Red 1 Green 2 Blue 3])\n",
    )
    .assert_stdout_contains(":primitives/Int 2");
}

// spec: spec/05-definitions.md §5.3 + §5.12 — a `deftrait` MAY carry a
// docstring after the trait header AND each method MAY carry its own
// docstring. Neither MUST affect dispatch. No prior carry exercises
// deftrait-with-docstring + per-method docstring; this is the canonical
// completion of docstring coverage.
// Cross-ref: spec/07-traits.md §7.1.2 — Docstrings.
// (carry: legacy/ring2.rs::docstring_on_deftrait)
#[test]
fn deftrait_with_docstring_and_method_docstring_does_not_affect_dispatch() {
    // b1-migration (S112): off the never-applied `(Sizeable a)` head to the
    // settled bare-head + `self` form. Assertion subject UNCHANGED: BOTH
    // docstring positions (trait + method) survive and neither affects dispatch
    // — `(size 42)` = 42. `a` was a bare method-param type (the implementing
    // type) → `self`.
    repl_prims(
        "(deftrait Sizeable \"Types that have a size\"\n  (size \"Get the size\" [self] Int))\n\
         (impl Sizeable Int (defn size [x] x))\n\
         (size 42)\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// =============================================================================
// §5.1.2 — the 0432 Face-B unwind (UW-7, plan §2): unannotated multi-clause
// `defn` + cross-variant self-call. Under the DRIFTED §5.1.2 this was an
// `ambiguous type` error (the 1-arg clause "could not pin the recursion").
// Under the SETTLED rule (S111 `c9f05b64`) the delegating self-call
// `(sum-to n 0)` pins the 1-arg clause's `n : Int` through the 2-arg sibling
// (whose `eq-i64`/`add-i64` bodies fix it to `(Fn [Int Int] Int)`) — so the
// definition COMPILES and `(sum-to 5)` = 5+4+3+2+1+0 = 15.
//
// UNWIND note: 0432's list MISSED this trio; /qa caught it (plan UW-7). The
// three NEGATIVE facets survive the conversion verbatim — no monomorphiser
// panic banner / no `build_mangled_name`/`non-concrete param` leak, the session
// stays alive after the form, and REPL ≡ `--run` output. RED at HEAD (the
// pre-drain scan still rejects); GREEN at leg (a).
//
//   (defn sum-to ([n] (sum-to n 0))
//                ([n acc] (if (eq-i64 n 0) acc
//                             (sum-to (sub-i64 n 1) (add-i64 acc n)))))
// =============================================================================

/// The Face-B shape: unannotated multi-clause `defn` + cross-variant self-call.
/// Bare primitive names resolve through the PrimitivesOnly prelude. Under the
/// settled §5.1.2 it compiles; `(sum-to 5)` = 15.
const SUM_TO_FACE_B: &str =
    "(defn sum-to ([n] (sum-to n 0)) ([n acc] (if (eq-i64 n 0) acc (sum-to (sub-i64 n 1) (add-i64 acc n)))))";

// spec: spec/05-definitions.md §5.1.2 — UW-7.E1: the Face-B form via the REPL
// COMPILES and `(sum-to 5)` = 15; the session does NOT crash (no panic banner,
// a following form still evals). Preserved negatives: no monomorphiser panic /
// `build_mangled_name` / `non-concrete param` leak.
#[test]
fn multi_clause_defn_self_call_repl_accepts_and_runs() {
    let out = repl_prims(&format!("{SUM_TO_FACE_B}\n(sum-to 5)\n(add-i64 2 3)\n"));
    let combined = format!("{}{}", out.stdout, out.stderr);

    // (i) the back-flow makes the recursion compile and run to 15.
    assert!(
        out.stdout.contains(":primitives/Int 15"),
        "the Face-B self-call MUST COMPILE and `(sum-to 5)` = 15 under the \
         settled §5.1.2 (the 1-arg clause pins `n : Int` via the delegating \
         `(sum-to n 0)`); got stdout={} stderr={}",
        out.stdout,
        out.stderr
    );

    // (ii) PRESERVED negative: no monomorphiser panic escaped the eval thread.
    let lc = combined.to_lowercase();
    assert!(
        !lc.contains("panicked")
            && !combined.contains("build_mangled_name")
            && !combined.contains("non-concrete param")
            && !lc.contains("internal error"),
        "the monomorphiser MUST NOT panic on the Face-B form — a typecheck \
         panic on user input is a robustness defect; got stdout={} stderr={}",
        out.stdout,
        out.stderr
    );

    // (iii) PRESERVED negative: the session survived — the following independent
    // form still evals to 5.
    assert!(
        out.stdout.contains(":primitives/Int 5"),
        "the REPL MUST stay alive — the following `(add-i64 2 3)` must eval to \
         `:primitives/Int 5`; got stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/05-definitions.md §5.1.2 — UW-7.E2: the same Face-B form via
// `--run` COMPILES and computes 15 (exit 15). Preserved negative: NO panic /
// mangler leak on the batch path.
#[test]
fn multi_clause_defn_self_call_run_computes_15() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(&format!("{SUM_TO_FACE_B}\n(defn main [] (Pure (sum-to 5)))"))
        .output();
    let combined = format!("{}{}", out.stdout, out.stderr);

    assert!(
        out.status.code() == Some(15),
        "the Face-B self-call via `--run` MUST COMPILE and `(sum-to 5)` = 15 ⇒ \
         exit 15 per the settled §5.1.2; got exit {:?} stdout={} stderr={}",
        out.status.code(),
        out.stdout,
        out.stderr
    );
    let lc = combined.to_lowercase();
    assert!(
        !lc.contains("panicked")
            && !combined.contains("build_mangled_name")
            && !combined.contains("non-concrete param"),
        "the `--run` path MUST compile with NO panic / mangler leak; got \
         stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/05-definitions.md §5.1.2 — UW-7.E3 (+neg): REPL, `--run`, and
// `--link` produce the IDENTICAL observation (15) — NO mode divergence, no
// panic in any mode. The PRESERVED REPL≡run mode-equality negative, now on the
// accepting form.
#[test]
fn multi_clause_defn_self_call_repl_equals_run_neg() {
    run_through_all_modes(
        &format!("{SUM_TO_FACE_B}\n(defn main [] (Pure (sum-to 5)))\n"),
        PreludeVariant::PrimitivesOnly,
    )
    .assert_all_equal(15);
}

// =============================================================================
// §5.1.2 — FIXME 0432 Face A: ANNOTATED multi-clause `defn` self-call (S91
// Thread C repro-check)
// =============================================================================
//
// Face A (distinct from Face B above): a multi-clause `defn` whose params ARE
// annotated, so the recursion's type IS pinned (no ambiguity) — the form
// type-checks. The S89 flag was that the in-body self-call may lower to an
// `undefined function` at codegen (a possible mischaracterisation of the symptom).
// This is the cross-skill-handoff minimal repro (CLAUDE.md §"Cross-skill defect
// handoff requires minimal repro"): its result decides disposition —
//   RED  → a real codegen defect → retarget FIXME 0432 to /backend, carry the
//          repro as a known-red guard;
//   GREEN→ the annotated→codegen variant does NOT reproduce → close FIXME 0432
//          with the repro-pass record (Face B already closed S90).
// Authored RED-first per the plan; the run determines truth (the `defn_multi_
// clause_arity` floor above already proves multi-clause-with-no-self-call works).

// spec: spec/05-definitions.md §5.1.2 — 0432.FaceA: an ANNOTATED multi-clause
// `defn` with a cross-variant self-call compiles and runs. The in-body self-call
// `(sum-to n 0)` must lower to the dispatched mangled variant symbol, not an
// `undefined function`. `(sum-to 5)` = 5+4+3+2+1+0 = 15.
//
// REPRODUCES (S91 Wave-7 narrowing): RED with `codegen error: undefined function:
// sum-to`. The repro is REAL (Face A was previously unverified; this confirms it).
// See the minimal-repro + dimension controls below + the handoff brief.
#[test]
fn defn_multi_clause_annotated_self_call() {
    let out = repl_prims(
        "(defn sum-to \
            ([:primitives/Int n] (sum-to n 0)) \
            ([:primitives/Int n :primitives/Int acc] \
               (if (eq-i64 n 0) acc (sum-to (sub-i64 n 1) (add-i64 acc n)))))\n\
         (sum-to 5)\n",
    );
    // CORRECT: the annotated self-call dispatches and the recursion sums to 15.
    out.assert_stdout_contains(":primitives/Int 15");
}

// =============================================================================
// §5.1.2 — FIXME 0432 Face A: minimal repro + dimension narrowing (S91 Wave-7)
//
// The narrowing pins the EXACT triggering combination and the passing controls,
// per CLAUDE.md §"Cross-compiler-skill defect handoff requires minimal repro" +
// tests/CLAUDE.md §"Isolating Cross-Crate Failures". Each dimension was varied:
//
//   | shape                                            | result                  |
//   |--------------------------------------------------|-------------------------|
//   | single-clause annotated self-call (recursion)    | WORKS (control below)   |
//   | multi-clause annotated, NO self-call             | WORKS (`defn_multi_     |
//   |                                                  |  clause_arity` above)   |
//   | multi-clause UNannotated self-call               | clean `ambiguous type`  |
//   |                                                  | (Face B — not this bug) |
//   | multi-clause ANNOTATED + self-call (any clause)  | **`undefined function`  |
//   |                                                  | at codegen — THE BUG**  |
//
// All three of {multi-clause, annotated, self-call} are REQUIRED to trigger it;
// removing any one makes it pass (or gives the clean Face-B ambiguous-type error).
// The self-call fails identically in the first clause, a later clause, same-arity,
// or cross-arity — so the trigger is "any self-reference inside any clause body of
// a multi-clause annotated defn," not a specific clause position.
//
// LAYER DIAGNOSIS (handoff brief): the call REACHES codegen (typecheck succeeded —
// so this is NOT a typecheck *rejection* / frontend resolution error that would
// error pre-codegen). The visible error is `/backend`
// (`crates/cranelisp-backend/src/compiler/apply.rs` `undefined function`) because
// the self-call lowers to a call against the BARE name (`sum-to`) while the
// multi-clause clauses are compiled+registered ONLY under MANGLED variant names
// (`sum-to$Int` etc.) — so the bare name is never defined in the codegen module.
// The ROOT, however, is `/typecheck`: the in-body self-call's dispatch annotation
// (`resolved_call` / `SigDispatch { mangled_name }`) is never written back onto
// the self-call AST node, so the backend has nothing telling it which mangled
// variant to call and falls back to the bare name. Suspected seam:
// `crates/cranelisp-typecheck/src/program.rs` — the multi-sig re-annotation block
// looks up each variant by its INTERNAL name (`{name}__v{i}`) AFTER
// `register_mangled_variants` has already removed-and-reinserted those entries
// under their MANGLED names, so the lookup misses and the self-call resolution is
// never propagated into the AST. This is the "visible error belongs to one skill;
// underlying failure belongs to another" pattern (CLAUDE.md) — visible at
// /backend, owned by /typecheck. `/dev` should confirm at the seam with an
// isolating unit test (parse → build_program → check, assert the self-call node
// carries the `SigDispatch`/mangled `resolved_call`).
//
// SUSPECTED OWNING SKILL FOR THE FIX: /typecheck (the missing re-annotation),
// NOT /backend (the bare-name fallback is correct given no annotation). Disposition
// per FIXME 0432: REPRODUCES → routes to the owning skill; FIXME 0432 does NOT
// close as a non-repro.
// =============================================================================

// spec: spec/05-definitions.md §5.1.2 — MINIMAL REPRO. The smallest shape that
// triggers `undefined function`: a 2-clause annotated `defn` whose first clause
// self-calls the other. `(h 5)` should = `(add-i64 5 5)` = 10. RED today:
// `codegen error: undefined function: h`. FIXME(/typecheck) — the in-body
// self-call's mangled-variant dispatch is not re-annotated onto the AST (see the
// brief above); the backend falls back to the undefined bare name `h`.
#[test]
fn defn_multi_clause_annotated_self_call_minimal_repro() {
    let out = repl_prims(
        "(defn h \
            ([:primitives/Int n] (h n n)) \
            ([:primitives/Int a :primitives/Int b] (add-i64 a b)))\n\
         (h 5)\n",
    );
    out.assert_stdout_contains(":primitives/Int 10");
}

// spec: spec/05-definitions.md §5.1.2 — DIMENSION CONTROL (passes today): a
// SINGLE-clause annotated self-call (ordinary recursion) compiles and runs —
// `(fac 5)` = 120. Proves the self-call alone is NOT the trigger; the bug needs
// MULTIPLE clauses. (If this ever goes RED, the defect has widened beyond the
// multi-clause case — a stronger regression.)
#[test]
fn defn_single_clause_annotated_self_call_control() {
    let out = repl_prims(
        "(defn fac [:primitives/Int n] \
           (if (eq-i64 n 0) 1 (mul-i64 n (fac (sub-i64 n 1)))))\n\
         (fac 5)\n",
    );
    out.assert_stdout_contains(":primitives/Int 120");
}

// spec: spec/05-definitions.md §5.1.2 — DIMENSION CONTROL (passes today): a
// multi-clause annotated `defn` with NO self-call compiles and dispatches both
// arities — `(pick 5)` = 5, `(pick 5 10)` = 15. Proves multi-clause + annotations
// alone are NOT the trigger; the bug needs the self-call. (Companion to the
// `defn_multi_clause_arity` floor; this one carries explicit annotations to
// isolate the annotation dimension from the bug.)
#[test]
fn defn_multi_clause_annotated_no_self_call_control() {
    let out = repl_prims(
        "(defn pick \
            ([:primitives/Int n] n) \
            ([:primitives/Int n :primitives/Int acc] (add-i64 n acc)))\n\
         (pick 5)\n\
         (pick 5 10)\n",
    );
    out.assert_stdout_contains_all(&[":primitives/Int 5", ":primitives/Int 15"]);
}

// =============================================================================
// §8.5.2 / §5.2.6 / §7.3.1 — FIXME 0365: `Type.member` field accessors +
// impl-time collision rejection (S91 Thread C)
// =============================================================================
//
// The dotted form `Box.v` resolves the field accessor `v` of `Box` directly,
// bypassing bare-name lookup — the per-type escape hatch for same-module
// duplicate-field-name ambiguity (the bare `v` is poisoned when two types in one
// module each carry a field `v`; see `accessor_cross_type_duplicate_field_name`
// above for the bare-poison guard that still holds). RED-first: `Box.v` does not
// yet resolve as a field accessor (Wave 1 frontend transport + Wave 3 typecheck
// land it). Free-standing: PrimitivesOnly prelude, decimal literals only.

// spec: spec/08-modules.md §8.5.2 — `Type.member` field accessor disambiguates a
// poisoned duplicate field. With `(deftype Box [:Int v])` + `(deftype Cup [:Int
// v])` the bare `v` is poisoned, but `(Box.v (Box 5))` = 5 and `(Cup.v (Cup 9))`
// = 9 resolve directly to the per-type accessors.
#[test]
fn type_member_field_accessor_disambiguates_poisoned_field() {
    repl_prims(
        "(deftype Box [:primitives/Int v])\n\
         (deftype Cup [:primitives/Int v])\n\
         (Box.v (Box 5))\n\
         (Cup.v (Cup 9))\n",
    )
    .assert_stdout_contains_all(&[":primitives/Int 5", ":primitives/Int 9"]);
}

// spec: spec/08-modules.md §8.5.2 — a `Type.member` field accessor is first-class:
// typed `(Fn [Type] FieldType)`, may be bound to a variable and applied. `Box.v`
// bound via `let` and applied to `(Box 7)` yields 7.
#[test]
fn type_member_accessor_typed_fn_of_type() {
    repl_prims(
        "(deftype Box [:primitives/Int v])\n\
         (deftype Cup [:primitives/Int v])\n\
         (let [g Box.v] (g (Box 7)))\n",
    )
    .assert_stdout_contains(":primitives/Int 7");
}

// spec: spec/07-traits.md §7.3.1 — impl-time collision rejection (FIXME 0365,
// R3). A trait `impl` whose method name collides with the target type's existing
// field-accessor name MUST be rejected at impl time with a diagnostic naming the
// collision — the program does NOT run. Here `Box` has a field accessor `v`, and
// the impl tries to define a method `v` for `Box` → compile-time error.
#[test]
fn impl_method_colliding_with_field_accessor_rejected_neg() {
    let out = repl_prims(
        "(deftype Box [:primitives/Int v])\n\
         (deftrait HasV (v [x] :primitives/Int))\n\
         (impl HasV Box (defn v [x] 99))\n\
         (Box.v (Box 5))\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr).to_lowercase();
    // The collision MUST be surfaced as a compile-time error naming the clash.
    assert!(
        combined.contains("collision")
            || combined.contains("collide")
            || combined.contains("conflict")
            || combined.contains("already")
            || (combined.contains("error") && combined.contains("accessor")),
        "an impl method `v` colliding with `Box`'s field accessor `v` MUST be \
         rejected at impl time with a diagnostic naming the collision (§7.3.1, \
         FIXME 0365); got stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
    // Negative: the colliding impl MUST NOT silently win — `(Box.v (Box 5))`
    // MUST NOT return the method's `99` (the field accessor's 5 is the only
    // correct value, and only if the impl is rejected rather than overriding).
    out.assert_stdout_does_not_contain(":primitives/Int 99");
}

// =============================================================================
// Sprint 109 — SS-3/SS-4: §5.1.2 multi-arity each-variant-independent checking.
// Plan: tests/plan/PLAN.md §S109 §I.
// =============================================================================

// spec: spec/05-definitions.md §5.1.2 — UW-8 RETARGET (plan §2): the OLD SS-3
// asset asserted this delegating clause was an ambiguous-type ERROR (the drifted
// "sibling not consulted, no back-flow" reading). Under the SETTLED rule the
// 2-arg clause's delegating `(rp p rot 0)` pins `p : Position` and
// `rot : Rotation` through the 3-arg sibling — so the un-annotated delegating
// clause COMPILES as `(Fn [Position Rotation] Int)`. The old diagnostic-quality
// facet (names the clause/param, no `__expr` leak) MOVES to MS-7/MS-8's
// genuinely-unpinned fixture. RED at HEAD (still rejected); GREEN at leg (a).
#[test]
fn defn_multi_arity_unannotated_delegating_clause_backflow_compiles() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(
            "(import [primitives [Pure Int add-i64]])\n\
             (deftype Position PZero)\n\
             (deftype Rotation RZero)\n\
             (defn rp\n\
               ([p rot] (rp p rot 0))\n\
               ([:Position p :Rotation rot :Int idx] idx))\n\
             (defn main [] (Pure (add-i64 (rp PZero RZero) 7)))\n",
        )
        .output();
    let text = format!("{}\n{}", out.stdout, out.stderr);
    assert!(
        out.status.code() == Some(7),
        "the un-annotated delegating 2-arg clause `([p rot] (rp p rot 0))` MUST \
         COMPILE — its params are pinned to Position/Rotation through the 3-arg \
         sibling (settled §5.1.2). `(rp PZero RZero)` = idx = 0, +7 ⇒ exit 7; \
         got exit {:?}:\n{text}",
        out.status.code()
    );
}

// spec: spec/05-definitions.md §5.1.2 — the spec's CORRECT example: with each
// clause carrying its own annotations, the multi-arity `defn` compiles and the
// delegating 2-arg clause (calling the 3-arg sibling with `idx = 0`) returns the
// right value.
#[test]
fn defn_multi_arity_annotated_clauses_compile() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(
            "(import [primitives [Pure Int add-i64]])\n\
             (deftype Position PZero)\n\
             (deftype Rotation RZero)\n\
             (defn rp\n\
               ([:Position p :Rotation rot] (rp p rot 0))\n\
               ([:Position p :Rotation rot :Int idx] idx))\n\
             (defn main [] (Pure (add-i64 (rp PZero RZero) (rp PZero RZero 7))))\n",
        )
        .output()
        .assert_exit(7);
}

// =============================================================================
// §5.1.2 × §3.3 [S109 W6.3] — Written free vars in multi-arity clauses.
// Plan: tests/plan/PLAN.md §L.1 (C-4, FV-12).
//
// §3.3.1 MUST (a) crossed with §5.1.2 "each variant type-checked independently":
// each clause is a DISJOINT lexical scope, so its bare `:a` pins independently by
// its OWN body — the two different pins are the observable clause-independence
// guard. And a free-var annotation does NOT rescue a variant that stays unpinned
// by its own body — that is the §5.1.2 ambiguity error naming the clause, NEVER
// `unknown type`.
// =============================================================================

// spec: spec/03-types.md §3.3.1 — MUST (a) per clause + §5.1.2 clause
// independence (C-4, was FV-11; INVERTED under W6.3, restoring the original
// W6 positive): each clause's bare `:a` is pinned by ITS OWN body.
// `(defn h ([:a x] (add-i64 x 1)) ([:a x :Int n] (str-concat x x)))` — clause 1's
// body pins `a := Int` (`(h 5)` → 6), clause 2's body pins `a := String`
// (`(h "ab" 0)` → "abab"). The two DIFFERENT pins ARE the observable
// clause-independence guard (disjoint lexical scopes; §5.1.2). This INVERTS the
// superseded W6.2 per-clause skolem-escape reading. Never `unknown type`.
// defect: class=wrong-reject locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr + unify.rs::unify_with_rigid (W6.2 minted RIGID vars for BARE written names — spec-valid per-clause body pins rejected as skolem-escape; §3.3.1 puts rigidity on the constraint path only) found=S109 owner=/dev
#[test]
fn multi_arity_same_written_var_independent_per_clause() {
    // REPL: each clause pins its own `:a` — clause 1 → Int, clause 2 → String.
    let out = repl_prims(
        "(defn h ([:a x] (add-i64 x 1)) ([:a x :Int n] (str-concat x x)))\n\
         (h 5)\n\
         (h \"ab\" 0)\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("unknown type") && !combined.to_lowercase().contains("rigid"),
        "per-clause body pins MUST be ordinary unification, never a rigid/unknown \
         error (§3.3.1 MUST (a)); got:\n{combined}"
    );
    assert!(
        out.stdout.contains(":primitives/Int 6"),
        "clause 1's body `(add-i64 x 1)` pins its own `a := Int` → `(h 5)` = 6 \
         (§3.3.1 MUST (a), §5.1.2 clause independence); got:\n{}",
        out.stdout
    );
    assert!(
        out.stdout.contains(":primitives/String \"abab\""),
        "clause 2's body `(str-concat x x)` pins its own `a := String` → \
         `(h \"ab\" 0)` = \"abab\" — the DIFFERENT pin is the clause-independence \
         guard (§3.3.1 MUST (a), §5.1.2); got:\n{}",
        out.stdout
    );

    // NOTE: the `--run` end-to-end leg is intentionally NOT exercised here. A
    // multi-arity fn CALLED from `main` in batch `--run` mode hits the
    // pre-existing C-4 defect (`entry module has no \`main\` function` — a
    // batch-entry/overload-path failure that is INDEPENDENT of W6.3 written
    // type vars: it reproduces with fully-concrete `:Int` params). That defect
    // has its own minimal guard, `multi_arity_call_from_main_batch_no_main_neg`
    // below; coupling it here would mask the W6.3 semantics this test pins. The
    // REPL/type facets above are the correct, mode-agnostic W6.3 assertions.
}

// spec: spec/05-definitions.md §5.1.2 — Multi-Signature: a multi-arity fn
// CALLED from `main` in batch `--run` mode MUST compile and run like any other
// function. This was the C-4 defect, minimally reduced by /testing (S109 W6.3):
// calling a 2+-clause `defn` from `main`'s body in `--run` aborted with the
// misleading `entry module has no \`main\` function` even though `main` was
// plainly defined. FIXED at `303df28a` (S110) — a scoped reslot in typecheck's
// finalize pass collapses the spurious-poly `main` calling an overloaded fn, so
// it codegens as a real entry. The original int-side `lookup_main_code_ptr`
// mode-divergence attribution was REFUTED (`94038b09`): the batch entry was
// never emitted because typecheck left `main` spuriously polymorphic. Reduction
// facts (confirmed manually against target/debug/cranelisp at repro time):
//   - INDEPENDENT of W6.3 written type vars — reproduced with fully-concrete
//     `:Int` params (zero type vars);
//   - the multi-arity `defn` alone was fine; the trigger was CALLING it from
//     `main`'s body (a `main` that did not reference it exited 0);
//   - needed 2+ clauses — a single-clause parenthesised `([:Int x] x)` called
//     from `main` ran correctly;
//   - was mode-divergent as a SYMPTOM — `(defn h (…) (…))` + `(h 7)` evaluated
//     correctly in the REPL while batch `--run` failed — but the root cause was
//     the typecheck finalize gate/reslot ordering, not an int/backend GOT slot.
// The correct behaviour is exit 7 (`(h 7)` → clause 1 → 7 → `(Pure 7)`); this
// guard is now GREEN and guards against regression of the finalize reslot.
// defect: class=wrong-reject locus=crates/cranelisp-typecheck/src/program/finalize.rs::finalize_check_result_inner found=S110 owner=/dev
#[test]
fn multi_arity_call_from_main_batch_no_main_neg() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(
            "(defn h ([:Int x] x) ([:Int x :Int y] x))\n\
             (defn main [] (Pure (h 7)))\n",
        )
        .output();
    let text = format!("{}\n{}", out.stdout, out.stderr);
    assert!(
        !text.contains("has no `main` function"),
        "a multi-arity fn called from `main` in batch `--run` MUST NOT abort with \
         `entry module has no \\`main\\` function` — `main` is plainly defined \
         (C-4, §5.1.2); got:\n{text}"
    );
    // A `(Pure n)` `main` exits with code `n`, so the correct disposition is
    // exit 7 — NOT `status.success()` (which requires exit 0). The bug currently
    // yields exit 1 with the bogus no-`main` error.
    assert!(
        out.status.code() == Some(7),
        "`main` returns `(Pure (h 7))` = `(Pure 7)` ⇒ exit 7; got exit {:?}:\n{text}",
        out.status.code()
    );
}

// spec: spec/05-definitions.md §5.1.2 × spec/03-types.md §3.3 — UW-11 HARDEN
// (plan §2): I-C is SETTLED. The 2-arg delegating clause `([:a p :a rot]
// (rp p rot 0))` DOES pin `a := Int` — the delegating self-call resolves to the
// 3-arg `:Int` sibling and unifies the shared written var `a` with `Int`
// through that clause's signature, exactly as a call to a separate function
// would. So the definition COMPILES and `(rp 1 2)` = `(rp 1 2 0)` = idx = 0.
// The two HARD negatives survive: the acquisition is NEVER surfaced as
// `unknown type`, and the Int is acquired into the SAME written var `a` via
// delegation (a legitimate pin), never silently smuggled into a DIFFERENT var
// (no `<invalid`/heap-garbage read). RED at HEAD (still rejected); GREEN at leg (a).
#[test]
fn multi_arity_unpinned_free_var_variant_delegation_pins_accepts() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(
            "(import [primitives [Pure Int add-i64]])\n\
             (defn rp\n\
               ([:a p :a rot] (rp p rot 0))\n\
               ([:Int p :Int rot :Int idx] idx))\n\
             (defn main [] (Pure (add-i64 (rp 1 2) 5)))\n",
        )
        .output();
    let text = format!("{}\n{}", out.stdout, out.stderr);
    // HARD negative 1: never `unknown type` for the written free var.
    assert!(
        !text.contains("unknown type"),
        "the written free var `a` MUST be pinned by delegation, NEVER surfaced \
         as `unknown type` (§3.3.1); got:\n{text}"
    );
    // HARD negative 2: no memory-unsafe wrong-var acquisition.
    assert!(
        !text.contains("<invalid"),
        "the Int MUST be acquired into the SAME var `a` via the delegating call, \
         never smuggled into a different var producing a wrong-type read \
         (`<invalid:`); got:\n{text}"
    );
    // Accept + run: delegation pins ⇒ compiles; `(rp 1 2)` = 0, +5 ⇒ exit 5.
    assert!(
        out.status.code() == Some(5),
        "delegation pins `a := Int` ⇒ the defn COMPILES and `(rp 1 2)` = 0, +5 \
         ⇒ exit 5 (settled §5.1.2); got exit {:?}:\n{text}",
        out.status.code()
    );
}

// =============================================================================
// S112 (0628/I-C wave) — §5.1.1 same-arity-unifiable overlap + §3.11 twin
// discipline (plan §1: MS-5/MS-6/MS-7/MS-8).
// =============================================================================

// MS-5 — §5.1.1 same-arity-unifiable clauses WITH a call: `([:Int x] x)` and
// `([:a x] x)` can unify, so `(f 1)` is a dispatch-ambiguity error (≥2 variants
// match). GREEN at HEAD (the call-site check already fires) — a must-hold that
// the leg-(a) rework must not regress.
// spec: spec/05-definitions.md §5.1.1 — same-arity clauses whose signatures can
// unify are a dispatch-ambiguity error.
#[test]
fn same_arity_unifiable_clauses_call_site_ambiguous_neg() {
    // REPL facet.
    let out = repl_prims("(defn f ([:Int x] x) ([:a x] x))\n(f 1)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.contains("ambiguous call") || (c.contains("ambiguous") && c.contains("matching")),
        "`(f 1)` MUST be a dispatch-ambiguity error — the same-arity `[:Int x]` \
         and `[:a x]` clauses can unify (§5.1.1); got:\n{c}"
    );
    // `--run` facet: the ambiguity is mode-uniform.
    let run = run_prims_05(
        "(defn f ([:Int x] x) ([:a x] x))\n(defn main [] (Pure (f 1)))\n",
    );
    assert!(
        !run.status.success(),
        "the same-arity-unifiable call ambiguity MUST also fire under `--run` \
         (mode-uniform §5.1.1); got exit {:?}:\n{}{}",
        run.status.code(),
        run.stdout,
        run.stderr
    );
}

// MS-6 — §5.1.1 same-arity-unifiable at the DEFINITION (no call): `([:Int x] x)`
// + `([:a x] x)` MUST be a dispatch-ambiguity error reported AT the definition
// (both colliding clauses named), per the §5.1.2 MUST — "reported at the
// definition (both colliding clauses named)". RED at HEAD: the current impl only
// catches strict-EQUAL duplicates at the definition and accepts this
// can-unify pair silently (it errors only if later CALLED — MS-5). Owner:
// /dev(typecheck); trigger = this row + the §5.1.2 definition-site MUST.
// spec: spec/05-definitions.md §5.1.2 — dispatch-ambiguity reported at the
// definition, both colliding clauses named.
#[test]
fn same_arity_unifiable_clauses_definition_site_error_neg() {
    // REPL facet: the DEFN itself must be rejected (no call site).
    let out = repl_prims("(defn f ([:Int x] x) ([:a x] x))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.contains("; defn"),
        "same-arity `[:Int x]` and `[:a x]` clauses can unify — the DEFINITION \
         MUST be rejected as a dispatch-ambiguity error at the definition site \
         (§5.1.2 MUST), NOT accepted silently and deferred to the call; got:\n{c}"
    );
    // `--run` facet: the definition-site rejection is mode-uniform.
    let run = run_prims_05(
        "(defn f ([:Int x] x) ([:a x] x))\n(defn main [] (Pure 0))\n",
    );
    assert!(
        !run.status.success(),
        "the same-arity-unifiable definition-site rejection MUST also fire under \
         `--run` (mode-uniform §5.1.2); got exit {:?}:\n{}{}",
        run.status.code(),
        run.stdout,
        run.stderr
    );
}

// MS-7 — genuinely-unpinned local, the EQ-twin (the highest-signal shape): a
// multi-signature clause `([n] (let [u []] n))` and the standalone twin
// `(defn f1 [n] (let [u []] n))` MUST have the SAME disposition — the
// separate-mutually-recursive-functions equivalence is the invariant, robust to
// the monomorphic-let boundary. RED at HEAD: the two DIVERGE (the multi-sig half
// rejects the `[]` with the pre-drain scan, the standalone accepts it as
// `(Fn [a] a)`). When they error, the message MUST be §3.11-class, never the
// false "each arity clause is type-checked independently (§5.1.2)" rationale.
//
// PLAN NOTE (routed to /qa): plan §1 states "twin half expected GREEN, SAME
// assertion both = §3.11-class ambiguous diagnostic", but on HEAD the standalone
// twin ACCEPTS (`; defn`) rather than emitting a §3.11 error. The robust
// invariant this row therefore pins is DISPOSITION EQUALITY (multi ≡ standalone),
// which does not bet on the settled monomorphic-let accept-vs-reject outcome.
// spec: spec/05-definitions.md §5.1.2 — clause inference-equivalent to the
// standalone function; spec/03-types.md §3.11 — ambiguity is a use-site property.
#[test]
fn unpinned_local_in_clause_matches_standalone_twin_neg() {
    let multi = repl_prims("(defn f ([n] (let [u []] n)) ([a b] a))\n");
    let solo = repl_prims("(defn f1 [n] (let [u []] n))\n");
    let mc = format!("{}{}", multi.stdout, multi.stderr);
    let sc = format!("{}{}", solo.stdout, solo.stderr);
    let multi_accepted = mc.contains("; defn");
    let solo_accepted = sc.contains("; defn");
    assert_eq!(
        multi_accepted, solo_accepted,
        "the multi-signature clause `([n] (let [u []] n))` and the standalone \
         twin `(defn f1 [n] (let [u []] n))` MUST have the SAME disposition \
         (clause-equivalent to the standalone function, §5.1.2). They DIVERGE:\n\
         multi accepted={multi_accepted}\n{mc}\nsolo accepted={solo_accepted}\n{sc}"
    );
    // When the multi-sig half errors, it MUST be a §3.11-class ambiguity, never
    // the drifted "each arity clause is type-checked independently (§5.1.2)"
    // rationale (the false claim MS-8 also pins).
    if !multi_accepted {
        assert!(
            mc.contains("ambiguous type"),
            "an unpinned-local rejection MUST be a §3.11-class `ambiguous type` \
             error; got:\n{mc}"
        );
        assert!(
            !mc.contains("each arity clause is type-checked independently"),
            "the diagnostic MUST NOT claim the drifted §5.1.2 independence \
             rationale (superseded); got:\n{mc}"
        );
    }
}

// MS-8 — diagnostic re-grounding: the §3.11 multi-sig ambiguity diagnostic for a
// genuinely-unpinned clause local still NAMES the offending arity clause (kept),
// cites §3.11 (the standalone-equivalence ground), and MUST NOT claim "each arity
// clause is type-checked independently (§5.1.2)" — the false rationale, superseded
// by the settled inference-equivalence rule.
//
// RE-POINTED (W2.1): the prior fixture `(defn q ([x] (let [v x] v)) ([x y] x))` is
// ADMISSIBLE-poly under the settled §5.1.2 (the let-bound `v` is a genuinely-poly
// clause, `(Fn [a] a)`), so it now compiles and the diagnostic never fires — the
// test could no longer pin the message. The genuinely-ambiguous shape is a
// CONCRETE-signature clause with an internally-unpinned local: `([:Int n] (let [u
// []] n))` — the `[]` is unpinnable and reaches a codegen position, so the §3.11
// ambiguity is a genuine use-site property of THIS clause (not the whole defn).
// GREEN on the leg-(a) working tree (the re-grounded message already fires).
// spec: spec/05-definitions.md §5.1.2 — the settled inference-equivalence rule
// (standalone equivalence) replaces the drifted independence rationale;
// spec/03-types.md §3.11 — ambiguity is a use-site property.
#[test]
fn ambiguous_clause_diagnostic_cites_standalone_equivalence() {
    let out = repl_prims("(defn qq ([:Int n] (let [u []] n)) ([x y] x))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    // The structural facet is KEPT: the diagnostic names the offending arity
    // clause of `qq` (the re-grounded message: "… bound in the 1-arg arity clause
    // of `qq` (spec §3.11)").
    assert!(
        c.contains("clause") && c.contains("qq"),
        "the diagnostic MUST still name the offending arity clause of `qq`; \
         got:\n{c}"
    );
    // The RE-GROUNDING ground: it cites §3.11 (standalone-equivalence), NOT the
    // drifted §5.1.2-independence rationale.
    assert!(
        c.contains("§3.11"),
        "the diagnostic MUST cite §3.11 (the standalone-equivalence ground for \
         the ambiguity); got:\n{c}"
    );
    assert!(
        !c.contains("each arity clause is type-checked independently"),
        "the diagnostic MUST NOT claim the drifted rationale 'each arity clause \
         is type-checked independently (§5.1.2)' — superseded by the settled \
         inference-equivalence rule; got:\n{c}"
    );
    // No internal-name leak: neither the `__`-binder (0568) nor the
    // monomorphisation `$`-mangle may reach user text.
    assert!(
        !c.contains("__expr") && !c.contains("__v") && !c.contains("$Var"),
        "the diagnostic MUST NOT leak an internal binder (`__expr`/`__v`) or a \
         monomorphisation mangle (`$Var`); got:\n{c}"
    );
}

// =============================================================================
// S112 §11.4 — the constrained-poly × multi-sig cell (plan §5; USER-RULED
// in-scope). Prelude: TestStandard (Num + `+`). A constrained clause
// (`([:a x] (+ x x))`) is spec-admissible under the equivalence rule but
// rejected-by-construction at HEAD (`collect_defns` filters multi-sig out of
// `detect_constrained_fns`; the `ConstrainedFn` single-variant invariant).
// =============================================================================

// CP-1 — a constrained clause is admitted, dispatches, and monomorphises at TWO
// instantiations: `(defn g ([:a x] (+ x x)) ([:Int x :Int y] (add-i64 x y)))`;
// `(g 3)` → 6 (Int instance), `(g 1.5)` → 3.0 (Float instance — the SECOND mono
// instance of the same clause template), `(g 2 3)` → 5 (concrete 2-arg clause).
// RED at HEAD (the constrained clause is rejected-by-construction). GREEN when
// the §11.4 constrained-cell rework lands.
// spec: spec/05-definitions.md §5.1.2 — a constrained-polymorphic clause is
// admissible when non-overlapping; monomorphised per concrete use.
#[test]
fn constrained_clause_nonoverlapping_arity_dispatches_two_instantiations() {
    // Two-instantiation facet (REPL): the constrained `([:a x] (+ x x))` clause
    // monomorphises at Int AND Float.
    let out = repl_std("(defn g ([:a x] (+ x x)) ([:Int x :Int y] (add-i64 x y)))\n(g 3)\n(g 1.5)\n(g 2 3)\n");
    out.assert_stdout_contains_all(&[
        ":primitives/Int 6",       // constrained clause at Int
        ":primitives/Float 3.0",   // constrained clause at Float — 2nd instance
        ":primitives/Int 5",       // concrete 2-arg clause: 2+3
    ]);
    // Mode-×3 facet: the Int-summable observation is equivalent across modes.
    run_through_all_modes(
        "(defn g ([:a x] (+ x x)) ([:Int x :Int y] (add-i64 x y)))\n\
         (defn main [] (Pure (add-i64 (g 3) (g 2 3))))\n",
        PreludeVariant::TestStandard,
    )
    .assert_all_equal(11); // (g 3)=6, (g 2 3)=5 → 11
}

// CP-1b — [oracle] RC balance on constrained-clause dispatch: CP-1's `(g x)` in
// a loop under `CRANELISP_RC_STATS` (serial by construction — nextest runs each
// test in its own process). Assert the alloc/free balance is bounded (no leak).
// RED at HEAD (g rejected ⇒ the loop never runs the expected sum). Graduates
// into the S113 oracle lane.
// spec: spec/12-runtime.md §12.3.1 — heap values MUST be freed when unreachable;
// spec/05-definitions.md §5.1.2 — constrained-clause dispatch reaches codegen.
#[test]
fn constrained_clause_dispatch_loop_rc_balanced() {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::TestStandard)
        .env("CRANELISP_RC_STATS", "1")
        .stdin(
            "(defn g ([:a x] (+ x x)) ([:Int x :Int y] (add-i64 x y)))\n\
             (defn gloop [:primitives/Int n :primitives/Int acc] \
               (if (eq-i64 n 0) acc (gloop (sub-i64 n 1) (add-i64 acc (g n)))))\n\
             (gloop 200 0)\n",
        )
        .output();
    // Workload-ran facet (RED at HEAD): sum of `(g n)`=2n for n=1..200 = 40200.
    assert!(
        out.stdout.contains(":primitives/Int 40200"),
        "the constrained-clause dispatch loop MUST run: sum(2n, n=1..200) = \
         40200; got:\n{}{}",
        out.stdout,
        out.stderr
    );
    // Balance facet: allocs − deallocs is bounded (no per-iteration leak).
    let line = out
        .stderr
        .lines()
        .find(|l| l.contains("[RC_STATS]"))
        .unwrap_or_else(|| panic!("no [RC_STATS] line on stderr:\n{}", out.stderr));
    let field = |k: &str| -> i64 {
        line.split_whitespace()
            .find_map(|tok| tok.strip_prefix(&format!("{k}=")))
            .and_then(|v| v.parse().ok())
            .unwrap_or_else(|| panic!("no {k}= field in RC_STATS line: {line}"))
    };
    let imbalance = field("allocs") - field("deallocs");
    assert!(
        imbalance.abs() <= 16,
        "constrained-clause dispatch loop MUST be RC-balanced (bounded \
         alloc/free imbalance); got imbalance={imbalance} on line: {line}"
    );
}

// CP-2 — same-arity constrained × concrete OVERLAP still errors: `([:a x]
// (+ x x))` + `([:Int x] x)` can unify (the constrained `a` covers `Int`), so it
// is a dispatch-ambiguity (§5.1.2 overlap rule). RED at HEAD (rejected-by-
// construction with the false "each arity clause is type-checked independently"
// rationale, NOT the admitted-then-overlap error).
// spec: spec/05-definitions.md §5.1.2 — same-arity clauses whose signatures can
// unify are a dispatch-ambiguity error.
#[test]
fn constrained_clause_same_arity_concrete_overlap_ambiguous_neg() {
    // REPL facet.
    let out = repl_std("(defn g ([:a x] (+ x x)) ([:Int x] x))\n(g 5)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.contains("; defn"),
        "the same-arity constrained `([:a x] (+ x x))` and concrete `([:Int x] \
         x)` clauses overlap (can unify) — MUST be a dispatch-ambiguity error \
         (§5.1.2); got:\n{c}"
    );
    // RED-for-the-right-reason: the constrained clause is ADMITTED then found to
    // overlap — NOT rejected-by-construction with the drifted independence
    // rationale (the HEAD behaviour).
    assert!(
        !c.contains("each arity clause is type-checked independently"),
        "the overlap MUST be reported as a genuine same-arity dispatch-ambiguity \
         (constrained clause admitted, then overlap detected), NOT the drifted \
         'each arity clause is type-checked independently' construction reject; \
         got:\n{c}"
    );
    // `--run` facet: mode-uniform.
    let run = Cranelisp::new()
        .with_prelude(PreludeVariant::TestStandard)
        .run("user.cl")
        .user("(defn g ([:a x] (+ x x)) ([:Int x] x))\n(defn main [] (Pure (g 5)))\n")
        .output();
    assert!(
        !run.status.success(),
        "the same-arity overlap MUST also error under `--run` (mode-uniform); \
         got exit {:?}:\n{}{}",
        run.status.code(),
        run.stdout,
        run.stderr
    );
}

// CP-3 — unsatisfied constraint at the call site: `(g "s")` where String lacks
// `Num` → a clean constraint error, NOT a codegen leak. Uses CP-1's admissible
// `g`. RED at HEAD (g is rejected-by-construction, so its defn never publishes).
// spec: spec/05-definitions.md §5.1.2 — a constrained clause's call site checks
// the constraint; an unsatisfied constraint is a clean type error.
#[test]
fn constrained_clause_unsatisfied_constraint_call_rejected_neg() {
    let out = repl_std(
        "(defn g ([:a x] (+ x x)) ([:Int x :Int y] (add-i64 x y)))\n(g \"s\")\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    // g's defn is admitted (RED at HEAD until the constrained cell lands).
    assert!(
        c.contains("; defn"),
        "g's constrained clause MUST be ADMITTED (the §11.4 cell); got:\n{c}"
    );
    // `(g "s")` is a clean constraint error, never a backend codegen leak.
    assert!(
        !c.contains("undefined function") && !c.contains("codegen error"),
        "`(g \"s\")` (String lacks Num) MUST be a clean constraint/type error, \
         NEVER a backend `undefined function`/`codegen error` leak; got:\n{c}"
    );
}

/// `--run` helper for the S112 §5.1 rows (PrimitivesOnly). Named distinctly from
/// the file-wide `repl_prims` to keep the run-mode call sites explicit.
fn run_prims_05(user: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(user)
        .output()
}
