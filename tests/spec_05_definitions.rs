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

use helpers::e2e::{Cranelisp, PreludeVariant};

fn repl_prims(lines: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
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
    repl_prims(
        "(deftrait (Sizeable a) \"Types that have a size\"\n  (size \"Get the size\" [a] Int))\n\
         (impl Sizeable Int (defn size [x] x))\n\
         (size 42)\n",
    )
    .assert_stdout_contains(":primitives/Int 42");
}

// =============================================================================
// §5.1.2 — FIXME 0432: multi-clause `defn` self-call (Face B, unannotated)
//
// A multi-signature `defn` whose body cross-variant self-calls, with params
// UNANNOTATED, cannot pin the recursion's type → it is an `ambiguous type`.
// `design/arch/fixmes/0432-multi-clause-defn-self-call-codegen.md` Face B +
// `design/typecheck/monomorphisation.md §9`: the CORRECT outcome (both modes)
// is a clean ambiguous-type error pointing the user at an annotation — NEVER a
// monomorphiser panic (`monomorphise.rs build_mangled_name` `debug_assert!`).
//
// The §9 root fix is an early concreteness gate at `monomorphise_call` P1
// (before `build_mangled_name`) so REPL and `--run` converge on ONE clean
// diagnostic. These e2e rows are the cross-mode convergence guards the FIXME's
// two-face divergence demands (REPL panic-vs-clean / `--run` clean).
//
// The repro form is the minimal Face-B shape (no annotations, bare primitive
// names via the PrimitivesOnly prelude — free-standing, primitives only):
//   (defn sum-to ([n] (sum-to n 0))
//                ([n acc] (if (eq-i64 n 0) acc
//                             (sum-to (sub-i64 n 1) (add-i64 acc n)))))
// =============================================================================

/// The minimal Face-B repro: unannotated multi-clause `defn` + cross-variant
/// self-call. Bare primitive names resolve through the PrimitivesOnly prelude.
const FIXME_0432_FACE_B: &str =
    "(defn sum-to ([n] (sum-to n 0)) ([n acc] (if (eq-i64 n 0) acc (sum-to (sub-i64 n 1) (add-i64 acc n)))))";

// spec: spec/05-definitions.md §5.1.2 — 0432.E1: the Face-B form via the REPL
// produces a clean ambiguous-type error AND the session does NOT crash — no
// panic banner, and a FOLLOWING form still evals. The monomorphiser
// `debug_assert!` MUST NOT escape the eval thread (it fired in debug builds,
// crashing the REPL pre-fix). Post-§9-fix: clean error, session alive.
#[test]
fn multi_clause_defn_self_call_repl_clean_error_not_panic() {
    // Follow the failing defn with an independent, well-typed form: if the
    // session crashed on the defn, this second form never evals.
    let out = repl_prims(&format!("{FIXME_0432_FACE_B}\n(add-i64 2 3)\n"));
    let combined = format!("{}{}", out.stdout, out.stderr);

    // (i) the clean ambiguous-type error appears, pointing at an annotation.
    assert!(
        combined.contains("ambiguous type"),
        "the Face-B self-call MUST surface a clean `ambiguous type` error per \
         §5.1.2 / monomorphisation §9.4; got stdout={} stderr={}",
        out.stdout,
        out.stderr
    );

    // (ii) NO monomorphiser panic escaped the eval thread — the debug_assert!
    // (`build_mangled_name … non-concrete param`) and any Rust panic banner
    // must be absent (the robustness blocker the §9 root fix removes).
    let lc = combined.to_lowercase();
    assert!(
        !lc.contains("panicked")
            && !combined.contains("build_mangled_name")
            && !combined.contains("non-concrete param")
            && !lc.contains("internal error"),
        "the monomorphiser MUST NOT panic on the Face-B form — a typecheck \
         panic on user input is a robustness defect (§9.2/§9.3); got stdout={} \
         stderr={}",
        out.stdout,
        out.stderr
    );

    // (iii) the session survived: the following independent form still evals.
    assert!(
        out.stdout.contains(":primitives/Int 5"),
        "after the ambiguous-type error the REPL MUST stay alive — the \
         following `(add-i64 2 3)` must eval to `:primitives/Int 5` (proves no \
         crash); got stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/05-definitions.md §5.1.2 — 0432.E2: the same Face-B form via
// `--run` produces the clean ambiguous-type error. This face is the
// convergence TARGET the REPL face (E1) must match — the `--run` path compiles
// out the monomorphiser `debug_assert!`, so the §4 ambiguity backstop already
// reports the clean error (no panic). Pins the target message.
#[test]
fn multi_clause_defn_self_call_run_clean_error() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(&format!("{FIXME_0432_FACE_B}\n(defn main [] (Pure 0))"))
        .output();
    let combined = format!("{}{}", out.stdout, out.stderr);

    assert!(
        combined.contains("ambiguous type"),
        "the Face-B self-call via `--run` MUST surface a clean `ambiguous \
         type` error per §5.1.2 / monomorphisation §9.4; got stdout={} \
         stderr={}",
        out.stdout,
        out.stderr
    );
    // No panic / abnormal termination on the batch path.
    let lc = combined.to_lowercase();
    assert!(
        !lc.contains("panicked")
            && !combined.contains("build_mangled_name")
            && !combined.contains("non-concrete param"),
        "the `--run` path MUST report the clean type error with NO panic; got \
         stdout={} stderr={}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/05-definitions.md §5.1.2 — 0432.E3 (+neg): REPL and `--run`
// produce the IDENTICAL ambiguous-type diagnostic — the cross-mode convergence
// the FIXME demands. The +neg is NO REPL/`--run` divergence: neither a panic
// nor a differing message. (Pre-§9-fix the REPL panicked while `--run` reported
// the clean error — the exact divergence this guard rejects.)
#[test]
fn multi_clause_defn_self_call_repl_equals_run_neg() {
    // REPL face.
    let repl_out = repl_prims(&format!("{FIXME_0432_FACE_B}\n"));
    let repl_combined = format!("{}{}", repl_out.stdout, repl_out.stderr);

    // `--run` face.
    let run_out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(&format!("{FIXME_0432_FACE_B}\n(defn main [] (Pure 0))"))
        .output();
    let run_combined = format!("{}{}", run_out.stdout, run_out.stderr);

    // Both report the ambiguous-type error (neither panics, neither succeeds).
    assert!(
        repl_combined.contains("ambiguous type"),
        "REPL face MUST report `ambiguous type`; got stdout={} stderr={}",
        repl_out.stdout,
        repl_out.stderr
    );
    assert!(
        run_combined.contains("ambiguous type"),
        "`--run` face MUST report `ambiguous type`; got stdout={} stderr={}",
        run_out.stdout,
        run_out.stderr
    );

    // The convergence: the SAME diagnostic core appears in both. Extract the
    // `ambiguous type …` clause through end-of-line from each mode and assert
    // they are byte-identical (no message divergence, no panic in one mode).
    let extract = |s: &str| -> String {
        s.lines()
            .find(|l| l.contains("ambiguous type"))
            .map(|l| {
                let idx = l.find("ambiguous type").unwrap();
                l[idx..].to_string()
            })
            .unwrap_or_default()
    };
    let repl_msg = extract(&repl_combined);
    let run_msg = extract(&run_combined);
    assert!(
        !repl_msg.is_empty() && repl_msg == run_msg,
        "REPL and `--run` MUST converge on the IDENTICAL ambiguous-type \
         diagnostic (§9.4) — no divergence, no panic in either mode.\n\
         repl_msg={repl_msg:?}\nrun_msg={run_msg:?}"
    );
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

// spec: spec/05-definitions.md §5.1.2 — the spec's ERROR example: a multi-arity
// `defn` whose 2-arg delegating clause is unannotated is an ambiguous-type
// compile-time error (the annotated 3-arg sibling is NOT consulted; the
// delegating call does not back-flow types). The rejection already fires; the
// DIAGNOSTIC-QUALITY facet is the RED — the error MUST NAME the offending
// param/clause (the 0576 `/dev` diagnostic tail) and MUST NOT leak `__expr` (0568).
// defect: class=silent-accept locus=crates/cranelisp-typecheck (multi-arity ambiguous-clause error names the fn but not the offending param/clause) found=S108 owner=/dev
#[test]
fn defn_multi_arity_unpinned_clause_ambiguous_error_names_clause_neg() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(
            "(import [primitives [Pure Int]])\n\
             (deftype Position PZero)\n\
             (deftype Rotation RZero)\n\
             (defn rp\n\
               ([p rot] (rp p rot 0))\n\
               ([:Position p :Rotation rot :Int idx] idx))\n\
             (defn main [] (Pure 0))\n",
        )
        .output();
    let text = format!("{}\n{}", out.stdout, out.stderr);
    assert!(
        !out.status.success(),
        "an unannotated delegating multi-arity clause MUST be an ambiguous-type \
         error (§5.1.2); {text}"
    );
    assert!(
        text.contains("rot")
            || text.contains("clause")
            || text.contains("variant")
            || text.contains("arity")
            || text.contains("2-arg"),
        "the diagnostic MUST NAME the offending param/clause, not only the fn \
         name (0576); {text}"
    );
    assert!(
        !text.contains("__expr"),
        "the diagnostic MUST NOT leak the internal `__expr` binder (0568); {text}"
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
// §5.1.2 × §3.3 [S109] — Written free vars in multi-arity clauses (W6).
// Plan: tests/plan/PLAN.md §S109 §L.1 (FV-11, FV-12).
//
// §3.3 (S109) MUST-1/MUST-2 crossed with §5.1.2 "each variant type-checked
// independently": matching `:a` identifiers across clauses are NO signal — each
// clause scopes its own fresh var. And a free-var annotation does NOT rescue a
// variant that stays unpinned by its own body — that is the §5.1.2 ambiguity
// error naming the clause, NEVER `unknown type`.
// =============================================================================

// spec: spec/03-types.md §3.3 — MUST-1 ("never by the definition's own body") +
// MUST-4 (rigid, no by-use pin), RECLASSIFIED W6.2 (2026-07-14): was a
// positive-acquire GREEN test asserting each clause's body pins its OWN `:a`
// concretely; under the rigid ruling that body-pin is a per-clause
// SKOLEM-ESCAPE error. SAME fixture, INVERTED verdict:
// `(defn h ([:a x] (add-i64 x 1)) ([:a x :Int n] (str-concat x x)))` — clause 1's
// body USE `(add-i64 x 1)` forces its rigid `a ~ Int`, clause 2's `(str-concat x
// x)` forces its rigid `a ~ String`; EACH clause is a type error against ITS OWN
// rigid var. Facets: (i) never `unknown type` (MUST-2) and the defn does NOT
// compile — `(h 5)`/`(h "ab" 0)` never evaluate to 6/"abab"; (ii) cross-clause
// independence (§5.1.2, unchanged): each clause errors against its OWN rigid `a`
// — the diagnostic MUST NOT be an Int-vs-String CROSS-CLAUSE conflict (which
// would betray a shared var). Per-clause skolem freshness beyond the error-shape
// observable is unit u3.
// defect: class=silent-accept locus=crates/cranelisp-typecheck/src/infer.rs::infer_annotate + resolve.rs::resolve_type_expr (W6 minted FLEXIBLE inference vars for written annotation vars — each clause body ACQUIRES/narrows its `:a` instead of the rigid var rejecting; no rigid skolem — F1/0588) found=S109 owner=/dev
#[test]
fn multi_arity_written_var_body_pin_skolem_escape_per_clause_neg() {
    // REPL: neither clause may successfully evaluate — each body forces its own
    // rigid `a` concrete (skolem-escape), so the defn is rejected.
    let out = repl_prims(
        "(defn h ([:a x] (add-i64 x 1)) ([:a x :Int n] (str-concat x x)))\n\
         (h 5)\n\
         (h \"ab\" 0)\n",
    );
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !combined.contains("unknown type"),
        "a per-clause body-use skolem-escape MUST be a type error, never \
         `unknown type` (§3.3 MUST-2); got:\n{combined}"
    );
    assert!(
        !out.stdout.contains(":primitives/Int 6"),
        "clause 1's body `(add-i64 x 1)` forces its rigid `a ~ Int` \
         (skolem-escape); the defn MUST NOT compile, so `(h 5)` MUST NOT \
         evaluate to 6 (§3.3 MUST-1/MUST-4); got:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains(":primitives/String \"abab\""),
        "clause 2's body `(str-concat x x)` forces its rigid `a ~ String` \
         (skolem-escape); `(h \"ab\" 0)` MUST NOT evaluate to \"abab\" (§3.3 \
         MUST-1/MUST-4); got:\n{}",
        out.stdout
    );

    // --run: the defn is rejected → non-zero exit; never unknown-type.
    let run = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(
            "(defn h ([:a x] (add-i64 x 1)) ([:a x :Int n] (str-concat x x)))\n\
             (defn main [] (Pure 0))\n",
        )
        .output();
    let rcomb = format!("{}{}", run.stdout, run.stderr);
    assert!(
        !run.status.success(),
        "--run: each clause's body forces its own rigid `a` concrete — the defn \
         MUST be rejected as skolem-escape (§3.3 MUST-4, no by-use exemption); \
         got success:\n{rcomb}"
    );
    assert!(
        !rcomb.contains("unknown type"),
        "--run: the rejection MUST be a type error, never `unknown type`; \
         got:\n{rcomb}"
    );
}

// spec: spec/05-definitions.md §5.1.2 × spec/03-types.md §3.3 — a free-var
// annotation does NOT rescue multi-arity ambiguity: the 2-arg delegating clause
// `([:a p :a rot] (rp p rot 0))` cannot pin `a` from its own body (the delegating
// call does not back-flow the 3-arg sibling's `:Int` types), so it is the §5.1.2
// ambiguous-type error naming the clause — NEVER `unknown type `a``. Couples SS-3's
// diagnostic-quality contract.
//
// W6.2 re-read (2026-07-14 — verdict UNCHANGED, not a reclassification): under
// the rigid model the rejection is DOUBLY grounded — the body could not pin the
// rigid `a` even in principle (MUST-3/MUST-4: the delegating call unifying `a`
// with the sibling's `:Int` params is itself skolem-escape), and an unpinned
// variant is §5.1.2's poly-variant error. Error-CLASS facet stays SOFT:
// ambiguous-variant OR skolem-escape/no-matching-variant are both conforming;
// only `unknown type` and silent acquisition are non-conforming.
// defect: class=wrong-scope-lookup locus=crates/cranelisp-typecheck/src/resolve.rs::resolve_type_expr (free lowercase annotation var absent from var_map fell to TypeNotFound instead of minting a fresh quantified var; W6 fix) found=S109 owner=/dev
#[test]
fn multi_arity_unpinned_free_var_variant_ambiguous_not_unknown_type_neg() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(
            "(import [primitives [Pure Int]])\n\
             (defn rp\n\
               ([:a p :a rot] (rp p rot 0))\n\
               ([:Int p :Int rot :Int idx] idx))\n\
             (defn main [] (Pure 0))\n",
        )
        .output();
    let text = format!("{}\n{}", out.stdout, out.stderr);
    assert!(
        !text.contains("unknown type"),
        "an unpinned free-var multi-arity clause MUST route to the §5.1.2 \
         ambiguity path, NEVER `unknown type` (§3.3 MUST-2); got:\n{text}"
    );
    assert!(
        !out.status.success(),
        "a variant whose free-var params stay unpinned by its own body MUST be \
         an ambiguous-type error (§5.1.2 — the free var does not rescue it); \
         got:\n{text}"
    );
    assert!(
        text.contains("ambig")
            || text.contains("annotat")
            || text.contains("rot")
            || text.contains("clause")
            || text.contains("variant")
            || text.contains("arity"),
        "the diagnostic SHOULD name the offending clause/param (couples SS-3); \
         got:\n{text}"
    );
}
