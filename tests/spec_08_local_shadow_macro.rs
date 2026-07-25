// spec_08_local_shadow_macro.rs — §8.6.3 lexical-shadow-of-a-def-macro defect
// (S103 Defect 2; owner /int; FIXME(/int)).
//
// §8.6.3 (spec/08-modules.md) PERMITS a `let`/`fn`/`match` local binding to
// lexically shadow a module-scope name — this is the layer-1 scoping the
// §8.6.4 no-exception ruling explicitly preserves ("The only shadowing
// relation is layer 1"). A top-level `(def g …)` expands (via the stdlib
// `def` macro) to a ZERO-ARG, bare-symbol macro named `g` plus a `g-def`
// zero-arg fn. When a local binding named `g` is then introduced, the macro
// expander (`src/expander.rs::expand_sexp_recursive`) recognises the bare
// symbol `g` in the BINDING position (fn-param list, let-binding name, match
// pattern variable — all `Sexp::Bracket`/bare-`Sexp::Symbol` positions) as a
// zero-arg macro invocation and expands it to `(g-def)`. The rewritten binder
// `(g-def)` then fails `ast_builder.rs::expect_symbol` — the ~1,000,000 offset
// is a quasiquote expansion-buffer SYNTHETIC span
// (`quasiquote.rs::SYNTHETIC_SPAN_COUNTER`, base `1_000_000`), NOT a module-
// source-regen byte offset.
//
// The expander already shields the `defmacro` NAME position (S102 CS-D1,
// `expander.rs` §"defmacro name shield") but NOT the general binding-position
// class. Root cause is upstream of typecheck (`ast_builder` runs BEFORE
// `checker.rs::lookup`), so the S103 Wave-2 `0513 checker.rs::lookup` reorder
// is NOT implicated; the defect is pre-existing.
//
// RED on HEAD: `parse error at ~1000131: expected symbol`. Flips GREEN when
// /int shields binding positions from bare zero-arg macro expansion (respecting
// the §8.6.3 lexical shadow). Failing-not-ignored per
// `memory/feedback_failing_not_ignored.md`.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{CrOutput, Cranelisp, PreludeVariant};

// The stdlib `def` macro, inlined VERBATIM (from stdlib/defs.cl §def) so the
// repro is stdlib-free per tests/CLAUDE.md §Test-Isolation. `(def g v)` expands
// to `(begin (defn g-def [] v) (defmacro g [] …))` — making `g` a bare-symbol
// zero-arg macro. Uses only `macros/*` + `primitives/*` (both resolvable under
// the PrimitivesOnly re-export prelude).
const DEF_MACRO: &str = "\
(defmacro def [name value]
  (match name
    [(macros/SexpSym s)
     (let [impl-name (macros/SexpSym (primitives/str-concat s \"-def\"))]
       `(begin
         (defn ~impl-name [] ~value)
         (defmacro ~name [] (macros/SexpList (macros/SCons ~(primitives/quote-sexp impl-name) macros/SNil)))))
     _ name]))
";

fn repl_prims(lines: &str) -> CrOutput {
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(lines)
        .output()
}

/// The §8.6.3 defect signature: the runaway synthetic-span parse error the
/// expander produces when it rewrites a binder into a zero-arg macro expansion.
fn assert_no_shadow_parse_error(out: &CrOutput) {
    let combined = format!("stdout:\n{}\nstderr:\n{}", out.stdout, out.stderr);
    assert!(
        !out.stdout.contains("expected symbol"),
        "§8.6.3 permits a local binding to lexically shadow a module-scope \
         name; the expander must NOT rewrite the binder into a zero-arg macro \
         expansion (runaway synthetic-span `expected symbol` parse error) — \
         FIXME(/int)\n{combined}"
    );
}

// spec: spec/08-modules.md §8.6.3 — a `let` binding named `g` MUST lexically
// shadow the top-level `def`-macro `g`; the `let` body resolves to the local
// (`7`), not the module-scope value. RED on HEAD (FIXME(/int)): the binder
// `g` in `[g 7]` is macro-expanded → `parse error at 1000131: expected symbol`.
#[test]
fn let_binding_shadows_top_level_def_macro() {
    let src = format!("{DEF_MACRO}(def g 99)\n(let [g 7] g)\n");
    let out = repl_prims(&src);
    assert_no_shadow_parse_error(&out);
    assert!(
        out.stdout.contains(":primitives/Int 7"),
        "the `let` body MUST resolve to the local shadow (7); stdout:\n{}",
        out.stdout
    );
}

// spec: spec/08-modules.md §8.6.3 — a `fn` PARAMETER named `g` MUST lexically
// shadow the top-level `def`-macro `g`; the body resolves to the argument.
// RED on HEAD (FIXME(/int)): the param `g` in `[:Int g]` is macro-expanded →
// `parse error at 1000131: expected symbol` (and `f` never defines).
#[test]
fn fn_param_shadows_top_level_def_macro() {
    let src = format!("{DEF_MACRO}(def g 99)\n(defn f [:Int g] g)\n(f 7)\n");
    let out = repl_prims(&src);
    assert_no_shadow_parse_error(&out);
    assert!(
        out.stdout.contains(":primitives/Int 7"),
        "the fn body MUST resolve the param shadow (7); stdout:\n{}",
        out.stdout
    );
}

// spec: spec/08-modules.md §8.6.3 — a `match` PATTERN variable named `g` MUST
// lexically shadow the top-level `def`-macro `g` within the arm body. RED on
// HEAD (FIXME(/int)): the pattern var `g` is macro-expanded → `parse error at
// 1000150: expected symbol` (this is the originally-reported Option/match
// shape, reduced to a bare `deftype`).
#[test]
fn match_pattern_shadows_top_level_def_macro() {
    let src = format!(
        "{DEF_MACRO}(deftype Box (Box [:Int v]))\n\
         (def g 99)\n\
         (defn unbox [:Box b] (match b [(Box g) g]))\n\
         (unbox (Box 7))\n"
    );
    let out = repl_prims(&src);
    assert_no_shadow_parse_error(&out);
    assert!(
        out.stdout.contains(":primitives/Int 7"),
        "the match arm MUST resolve the pattern-var shadow (7); stdout:\n{}",
        out.stdout
    );
}

// spec: spec/08-modules.md §8.6.3 — GREEN control isolating the defect to the
// SHADOW: the same program with the local binding RENAMED (`g` → `h`, no name
// collision with the `def`-macro) compiles and evaluates cleanly. GREEN on
// HEAD (stays green; the shadow tests above are the RED). Proves the fault is
// the binder-name/macro-name collision, not the `def` macro or `let` itself.
#[test]
fn local_binding_no_collision_control_is_clean() {
    let src = format!("{DEF_MACRO}(def g 99)\n(let [h 7] h)\n");
    let out = repl_prims(&src).assert_ok();
    assert_no_shadow_parse_error(&out);
    assert!(
        out.stdout.contains(":primitives/Int 7"),
        "the renamed local (h=7) MUST evaluate cleanly; stdout:\n{}",
        out.stdout
    );
}
