// dotted_binder_reject_0702.rs — S115 W1, FIXME 0702 M3 dotted-binder matrix.
//
// USER RULING (2026-07-20, SPRINT.md §Notes; 0702 SETTLED, Ruling 1): a dotted
// (`.`) spelling in ANY binder position is a LOCATED compile-time error, span on
// the name, EXACTLY as a `/`-qualified binder already is. `.` is reserved for
// type/trait qualification only; REFERENCE positions — the dotted ctor-pattern
// head `(Maybe.Some x)` (§6.2.1), dotted var/call/type references (§8.5) — stay
// legal. The rule is drawn at the binder/reference line, identical to the `/` rule.
//
// This file is the `.`-column twin of the landed `/`-column binder matrix
// (spec_05_definitions.rs BD-M1, spec_07_traits.rs). Mechanism (design
// `binder-head-reject.md` §2.2): ONE predicate widened at the shared helper
// `reject_qualified_binder_head` (`/`-or-`.`) + ONE sibling `split_dotted_name`,
// closing the `.` column at EVERY binder position the `/` column covers, with the
// deftype type-param the one site that gains a routing call (§3.2). The `.`-axis
// is an unenforced hole today (falsified "dotted never reaches a head slot"
// premise), so EVERY dotted binder below SILENTLY ACCEPTS at HEAD — FAILING-NOT-
// IGNORED until /dev(frontend) lands the widening in W5 (all reject cells flip
// together on that ONE seam; a cell that flips differently has grown its own path).
//
// The located-reject proxy mirrors the `/`-column: a compile-time `error`, NOT an
// incidental downstream `module … not found` resolution error, NOT a silent bind
// of the corrupted name. Free-standing, PrimitivesOnly (stdlib-free).

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
// Def-form heads (defn / defn- / deftype / deftype- / deftrait / defmacro / …)
// =============================================================================

// defn dotted head — reject.
// spec: spec/05-definitions.md §5 — Declaration heads are binders (defn, `.` axis).
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs::reject_qualified_binder_head (.-axis widening, 0702) found=S115 owner=/dev
#[test]
fn defn_dotted_head_rejected_binder_neg() {
    let out = repl_prims("(defn a.b [x] x)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the dotted `defn` head `a.b` MUST be a located compile-time error (§5 \
         binder principle, 0702 Ruling 1); today it silently binds `user/a.b`. \
         got:\n{c}"
    );
    assert!(
        !out.stdout.contains("user/a.b"),
        "the dotted head MUST NOT silently bind a `user/a.b` name; got:\n{}",
        out.stdout
    );
}

// defn dotted head — bare-head accept TWIN (proves the reject is `.`-specific).
// spec: spec/05-definitions.md §5.1.1 — a bare `defn` head binds normally.
#[test]
fn defn_bare_head_accepts_twin_green() {
    let out = repl_prims("(defn ab [x] x)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.to_lowercase().contains("error"),
        "a bare (dot-free) `defn` head MUST bind without error; got:\n{c}"
    );
}

// defn- dotted head — reject.
// spec: spec/05-definitions.md §5 — Declaration heads are binders (defn-, `.` axis).
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs::reject_qualified_binder_head (.-axis widening, 0702) found=S115 owner=/dev
#[test]
fn defn_private_dotted_head_rejected_binder_neg() {
    let out = repl_prims("(defn- a.b [x] x)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the dotted `defn-` head `a.b` MUST be a located compile-time error; today \
         it silently binds. got:\n{c}"
    );
    assert!(
        !out.stdout.contains("user/a.b"),
        "the dotted `defn-` head MUST NOT silently bind; got:\n{}",
        out.stdout
    );
}

// deftype dotted head — reject.
// spec: spec/05-definitions.md §5 — Declaration heads are binders (deftype, `.` axis).
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs::build_type_head (.-axis widening, 0702) found=S115 owner=/dev
#[test]
fn deftype_dotted_head_rejected_binder_neg() {
    let out = repl_prims("(deftype A.B Red2 Green2)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the dotted `deftype` head `A.B` MUST be a located compile-time error; \
         today it silently binds `user/A.B`. got:\n{c}"
    );
    assert!(
        !c.contains("not found"),
        "the dotted head MUST be a LOCATED binder reject at the head, NOT an \
         incidental `module … not found` resolution error; got:\n{c}"
    );
    assert!(
        !out.stdout.contains("user/A.B"),
        "the dotted `deftype` head MUST NOT silently bind; got:\n{}",
        out.stdout
    );
}

// deftype dotted head — bare-head accept TWIN.
// spec: spec/05-definitions.md §5.2 — a bare `deftype` head binds normally.
#[test]
fn deftype_bare_head_accepts_twin_green() {
    let out = repl_prims("(deftype Ab Red3 Green3)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.to_lowercase().contains("error"),
        "a bare (dot-free) `deftype` head MUST bind without error; got:\n{c}"
    );
}

// deftype dotted head — THE SHARPEST FACE (`binder-head-reject.md` §2.2): today
// `(deftype A.B [:Int v])` SILENTLY ACCEPTS, echoing type `user/A.B` but minting
// the CORRUPTED constructor `user/B` (the dotted head is re-read downstream as a
// `Type.Ctor` member spelling, so the ctor identity is corrupted). The widened
// helper rejects at the head span BEFORE any constructor synthesis runs, so the
// corrupted `user/B` mint is structurally unreachable — the incoherence never forms.
// spec: spec/05-definitions.md §5 — a dotted deftype head is a binder reject before
// ctor synthesis; the corrupted `user/B` ctor identity must never be minted.
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs::build_type_head — dotted head mints corrupted ctor user/B before reject (0702) found=S115 owner=/dev
#[test]
fn deftype_dotted_head_does_not_mint_corrupted_ctor_neg() {
    let out = repl_prims("(deftype A.B [:Int v])\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "`(deftype A.B [:Int v])` MUST be a located binder reject; today it \
         silently accepts and mints a corrupted ctor. got:\n{c}"
    );
    assert!(
        !out.stdout.contains("user/B"),
        "the dotted deftype head MUST NOT mint the CORRUPTED constructor `user/B` \
         (the incoherence closes at the head reject, before ctor synthesis); \
         got:\n{}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("user/A.B"),
        "the dotted deftype head MUST NOT silently accept type `user/A.B`; got:\n{}",
        out.stdout
    );
}

// deftype- dotted head — reject.
// spec: spec/05-definitions.md §5 — Declaration heads are binders (deftype-, `.` axis).
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs::build_type_head (.-axis widening, 0702) found=S115 owner=/dev
#[test]
fn deftype_private_dotted_head_rejected_binder_neg() {
    let out = repl_prims("(deftype- A.B Hidden2)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the dotted `deftype-` head `A.B` MUST be a located compile-time error; \
         today it silently binds. got:\n{c}"
    );
    assert!(
        !c.contains("not found"),
        "the dotted `deftype-` head MUST be a LOCATED binder reject, NOT an \
         incidental `module … not found`; got:\n{c}"
    );
    assert!(
        !out.stdout.contains("user/A.B"),
        "the dotted `deftype-` head MUST NOT silently bind; got:\n{}",
        out.stdout
    );
}

// deftype dotted CTOR NAME (list arm) — reject. `A.b` starts uppercase (passes the
// matchable-ctor gate) but is a dotted binder; a variant ctor is a binder (§5.2.2,
// user ruling 2026-07-19). Today it silently mints ctor `A.b`.
// spec: spec/05-definitions.md §5.2.2 — a variant-constructor name is a binder;
// a dotted spelling is a located reject.
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs::build_constructor_def (.-axis widening, 0702) found=S115 owner=/dev
#[test]
fn deftype_dotted_ctor_name_rejected_binder_neg() {
    let out = repl_prims("(deftype Shape (A.b [:Int r]))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the dotted variant-ctor name `A.b` MUST be a located binder reject \
         (§5.2.2 binder); today it silently mints. got:\n{c}"
    );
}

// deftype dotted CTOR NAME — bare-ctor accept TWIN.
// spec: spec/05-definitions.md §5.2.2 — a bare uppercase variant-ctor binds.
#[test]
fn deftype_bare_ctor_name_accepts_twin_green() {
    let out = repl_prims("(deftype Shape2 (Ab [:Int r]))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.to_lowercase().contains("error"),
        "a bare uppercase variant-ctor name MUST bind without error; got:\n{c}"
    );
}

// deftype dotted FIELD NAME — reject. A field binder mints a `Type.field` accessor
// (§5.2.6), so a dotted field spelling is a located reject. Today silent-accept.
// spec: spec/05-definitions.md §5.2.6 — a field name is a binder; dotted rejects.
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs::build_field_list (.-axis widening, 0702) found=S115 owner=/dev
#[test]
fn deftype_dotted_field_name_rejected_binder_neg() {
    let out = repl_prims("(deftype P [:Int a.b])\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the dotted field name `a.b` MUST be a located binder reject (§5.2.6 \
         accessor-minting binder); today it silently accepts. got:\n{c}"
    );
}

// deftype dotted FIELD NAME — bare-field accept TWIN.
// spec: spec/05-definitions.md §5.2.6 — a bare field name binds (mints accessor).
#[test]
fn deftype_bare_field_name_accepts_twin_green() {
    let out = repl_prims("(deftype P2 [:Int ab])\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.to_lowercase().contains("error"),
        "a bare field name MUST bind without error; got:\n{c}"
    );
}

// deftype dotted TYPE-PARAM — reject (the `.` axis of the §3.2 rider; the ONE
// site that gains a routing call onto the shared helper). Today silent-accept.
// spec: spec/05-definitions.md §5.2 — a deftype type parameter is a binder; a
// dotted spelling is a located reject at the param span.
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs::build_type_head type-param arm (0702 §3.2 rider) found=S115 owner=/dev
#[test]
fn deftype_dotted_type_param_rejected_binder_neg() {
    let out = repl_prims("(deftype (Duo a.b c) (Mk [:c x]))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the dotted type-param `a.b` MUST be a located binder reject at the param \
         span (§3.2 rider); today it silently accepts. got:\n{c}"
    );
}

// deftype QUALIFIED TYPE-PARAM — the never-drawn §3.2 row (the `/` axis rider).
// TODAY `(deftype (Duo prim/a b) …)` dies with an INCIDENTAL `module 'prim' …
// not found` at a degenerate `0..0` span (the qualified param is re-rooted and
// dies downstream). The fix routes the type-param arm through the shared helper so
// it becomes a CLEAN located binder reject at the param span — the incidental
// `0..0`/`not found` artifact ABSENT (RA-N5/N6 incidental-artifact-absent shape).
// spec: spec/05-definitions.md §5.2 — a qualified deftype type-param is a located
// binder reject, NOT an incidental module-resolution error.
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs::build_type_head type-param arm — qualified param re-rooted, dies incidentally at 0..0 (0702 §3.2 rider) found=S115 owner=/dev
#[test]
fn deftype_qualified_type_param_located_reject_not_incidental_neg() {
    let out = repl_prims("(deftype (Duo prim/a b) (Mk [:b x]))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the qualified type-param `prim/a` MUST be rejected; got:\n{c}"
    );
    assert!(
        !c.contains("not found"),
        "the qualified type-param MUST be a LOCATED binder reject at the param \
         span, NOT the incidental `module 'prim' … not found` (the §3.2 rider's \
         explicit ask — retire the incidental death); got:\n{c}"
    );
    assert!(
        !c.contains("0..0"),
        "the qualified type-param reject MUST carry a REAL param span, NOT the \
         degenerate `0..0` span the incidental death reports; got:\n{c}"
    );
}

// deftype TYPE-PARAM — bare accept TWIN.
// spec: spec/05-definitions.md §5.2 — a bare lowercase type-param binds normally.
#[test]
fn deftype_bare_type_param_accepts_twin_green() {
    let out = repl_prims("(deftype (Duo2 a c) (Mk2 [:c x]))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.to_lowercase().contains("error"),
        "a bare lowercase type-param MUST bind without error; got:\n{c}"
    );
}

// deftrait dotted BARE head — reject.
// spec: spec/05-definitions.md §5 — Declaration heads are binders (deftrait, `.` axis).
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs::build_trait_head (.-axis widening, 0702) found=S115 owner=/dev
#[test]
fn deftrait_dotted_bare_head_rejected_binder_neg() {
    let out = repl_prims("(deftrait A.B (m [x] x))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the dotted `deftrait` head `A.B` MUST be a located binder reject; today \
         it silently binds `user/A.B`. got:\n{c}"
    );
    assert!(
        !out.stdout.contains("user/A.B"),
        "the dotted `deftrait` head MUST NOT silently bind; got:\n{}",
        out.stdout
    );
}

// deftrait dotted BARE head — bare-head accept TWIN.
// spec: spec/07-traits.md §7.1 — a bare `deftrait` head binds normally.
#[test]
fn deftrait_bare_head_accepts_twin_green() {
    let out = repl_prims("(deftrait Ab (m [x] x))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.to_lowercase().contains("error"),
        "a bare `deftrait` head MUST bind without error; got:\n{c}"
    );
}

// deftrait dotted PARENTHESIZED head — reject (distinct parse arm; con_var applied
// so the head is well-formed apart from the dotted trait name). Today silent-accept.
// spec: spec/07-traits.md §7.2 — a parenthesized (HKT) deftrait head is a binder;
// a dotted trait name is a located reject.
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs::build_trait_head parenthesized arm (.-axis widening, 0702) found=S115 owner=/dev
#[test]
fn deftrait_dotted_parenthesized_head_rejected_binder_neg() {
    let out = repl_prims("(deftrait (Cat.X f) (fmap [:(Fn [x] y) g :(f x) v] v))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the dotted parenthesized `deftrait` head `Cat.X` MUST be a located binder \
         reject; today it silently binds `user/Cat.X`. got:\n{c}"
    );
    assert!(
        !out.stdout.contains("user/Cat.X"),
        "the dotted parenthesized head MUST NOT silently bind; got:\n{}",
        out.stdout
    );
}

// deftrait dotted METHOD NAME — reject. A method-sig name introduces a method into
// scope (§5.3.3 / §7.1) — a binder. Today silent-accept.
// spec: spec/05-definitions.md §5.3.3 — a deftrait method-signature name is a
// binder; a dotted spelling is a located reject.
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs::build_method_sig (.-axis widening, 0702) found=S115 owner=/dev
#[test]
fn deftrait_dotted_method_name_rejected_binder_neg() {
    let out = repl_prims("(deftrait Foo (a.b [x] x))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the dotted method-sig name `a.b` MUST be a located binder reject (§5.3.3 \
         method-name binder); today it silently accepts. got:\n{c}"
    );
}

// deftrait dotted CON_VAR — reject. The con_var is a bare lowercase type-constructor
// variable binder (§7.2 `con_var = lowercase_symbol`); a dotted spelling is a
// located reject — the sibling of the uppercase/qualified con_var rejects. Today
// silent-accept.
// spec: spec/07-traits.md §7.2 — con_var is a bare lowercase symbol; dotted rejects.
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs::parse_trait_head_shape con_var arm (.-axis widening, 0702) found=S115 owner=/dev
#[test]
fn deftrait_dotted_con_var_rejected_binder_neg() {
    let out = repl_prims("(deftrait (Functor a.b) (fmap [:(Fn [x] y) g :(a.b x) v] v))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the dotted con_var `a.b` MUST be a located binder reject (§7.2 bare \
         lowercase con_var); today it silently accepts. got:\n{c}"
    );
}

// defmacro dotted head — reject.
// spec: spec/05-definitions.md §5 — Declaration heads are binders (defmacro, `.` axis).
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/defmacro.rs (.-axis widening, 0702) found=S115 owner=/dev
#[test]
fn defmacro_dotted_head_rejected_binder_neg() {
    let out = repl_prims("(defmacro a.b [] 0)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the dotted `defmacro` head `a.b` MUST be a located binder reject; today \
         it silently binds `user/a.b`. got:\n{c}"
    );
    assert!(
        !out.stdout.contains("user/a.b"),
        "the dotted `defmacro` head MUST NOT silently bind; got:\n{}",
        out.stdout
    );
}

// defmacro- dotted head — reject.
// spec: spec/05-definitions.md §5 — Declaration heads are binders (defmacro-, `.` axis).
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/defmacro.rs (.-axis widening, 0702) found=S115 owner=/dev
#[test]
fn defmacro_private_dotted_head_rejected_binder_neg() {
    let out = repl_prims("(defmacro- a.b [] 0)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the dotted `defmacro-` head `a.b` MUST be a located binder reject; today \
         it silently binds. got:\n{c}"
    );
    assert!(
        !out.stdout.contains("user/a.b"),
        "the dotted `defmacro-` head MUST NOT silently bind; got:\n{}",
        out.stdout
    );
}

// defmacro dotted head — bare-head accept TWIN.
// spec: spec/05-definitions.md §5.5 — a bare `defmacro` head binds normally.
#[test]
fn defmacro_bare_head_accepts_twin_green() {
    let out = repl_prims("(defmacro ab [] 0)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.to_lowercase().contains("error"),
        "a bare `defmacro` head MUST bind without error; got:\n{c}"
    );
}

// =============================================================================
// Value-level local binders (let name / param / match var-pattern)
// =============================================================================

// let dotted binder — reject. Today `(let [a.b 5] a.b)` silently binds the dotted
// local and returns 5.
// spec: spec/05-definitions.md §5 — a `let` name is a bare-symbol binder; dotted rejects.
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs::build_let_bindings (.-axis widening, 0702) found=S115 owner=/dev
#[test]
fn let_dotted_binder_rejected_binder_neg() {
    let out = repl_prims("(let [a.b 5] a.b)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the dotted `let` binder `a.b` MUST be a located binder reject; today it \
         silently binds. got:\n{c}"
    );
    assert!(
        !out.stdout.contains(":primitives/Int 5"),
        "the dotted `let` binder MUST NOT silently bind + evaluate to 5; got:\n{}",
        out.stdout
    );
}

// let bare binder — accept TWIN.
// spec: spec/05-definitions.md §5 — a bare `let` name binds normally.
#[test]
fn let_bare_binder_accepts_twin_green() {
    repl_prims("(let [ab 5] ab)\n").assert_stdout_contains(":primitives/Int 5");
}

// defn dotted PARAM — reject. Today `(defn g [a.b] 1)` silently binds the dotted
// param and the call works.
// spec: spec/05-definitions.md §5.1.1 — a defn param is a bare-symbol binder; dotted rejects.
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs::build_annotated_params (.-axis widening, 0702) found=S115 owner=/dev
#[test]
fn defn_dotted_param_rejected_binder_neg() {
    let out = repl_prims("(defn g [a.b] 1)\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the dotted defn param `a.b` MUST be a located binder reject; today it \
         silently binds. got:\n{c}"
    );
    assert!(
        !out.stdout.contains("user/g"),
        "the dotted-param defn MUST NOT silently bind `user/g`; got:\n{}",
        out.stdout
    );
}

// defn bare PARAM — accept TWIN.
// spec: spec/05-definitions.md §5.1.1 — a bare defn param binds normally.
#[test]
fn defn_bare_param_accepts_twin_green() {
    repl_prims("(defn g2 [ab] 1)\n(g2 7)\n").assert_stdout_contains(":primitives/Int 1");
}

// match dotted VAR-PATTERN — reject. Today `(match 1 [a.b a.b])` silently binds the
// dotted var-pattern and returns 1.
// spec: spec/06-pattern-matching.md §6 — a match var-pattern is a bare-symbol
// binder; a dotted spelling is a located reject (§6.2.1 ctor-pattern head stays legal).
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs::build_pattern var-binder arm (.-axis widening, 0702) found=S115 owner=/dev
#[test]
fn match_dotted_var_pattern_rejected_binder_neg() {
    let out = repl_prims("(match 1 [a.b a.b])\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("error"),
        "the dotted match var-pattern `a.b` MUST be a located binder reject; today \
         it silently binds. got:\n{c}"
    );
    assert!(
        !out.stdout.contains(":primitives/Int 1"),
        "the dotted match var-pattern MUST NOT silently bind + evaluate to 1; \
         got:\n{}",
        out.stdout
    );
}

// match bare VAR-PATTERN — accept TWIN.
// spec: spec/06-pattern-matching.md §6 — a bare match var-pattern binds normally.
#[test]
fn match_bare_var_pattern_accepts_twin_green() {
    repl_prims("(match 1 [ab ab])\n").assert_stdout_contains(":primitives/Int 1");
}

// =============================================================================
// Positive fences — REFERENCE-position `.` stays LEGAL (must hold under Ruling 1)
// =============================================================================

// §6.2.1 positive fence: a dotted ctor-pattern HEAD `Maybe.Some` in match position
// is a REFERENCE (not a binder) and stays LEGAL. Born-green; the binder widening
// MUST NOT touch it.
// spec: spec/06-pattern-matching.md §6.2.1 — a dotted ctor-pattern head is a legal
// qualified reference.
#[test]
fn dotted_ctor_pattern_head_reference_stays_legal_green() {
    repl_prims(
        "(deftype Maybe (Some [:Int v]) None)\n\
         (match (Some 5) [(Maybe.Some x) x Maybe.None 0])\n",
    )
    .assert_stdout_contains(":primitives/Int 5");
}

// Positive fence: a dotted ctor in VALUE (construction) position `(Maybe.Some 5)`
// is a REFERENCE and stays LEGAL (§8.5). Born-green.
// spec: spec/08-modules.md §8.5 — a dotted `Type.Ctor` reference in value position
// is legal.
#[test]
fn dotted_ctor_value_construction_reference_stays_legal_green() {
    repl_prims(
        "(deftype Maybe (Some [:Int v]) None)\n\
         (match (Maybe.Some 7) [(Some x) x None 0])\n",
    )
    .assert_stdout_contains(":primitives/Int 7");
}

// Positive fence: a DOTTED MODULE PATH in an import (`main.util`) is a legal
// module reference — the `.` there qualifies a nested module path, NOT a binder.
// Born-green; the binder widening MUST NOT reject dotted module paths.
// spec: spec/08-modules.md §8.5 — a dotted module path in an import is a legal reference.
#[test]
fn dotted_module_path_in_import_stays_legal_green() {
    Cranelisp::new()
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n(mod util)\n(import [main.util [helper]])\n\
             (defn main [] (Pure (helper)))",
        )
        .file("main/util.cl", "(defn helper [] 99)")
        .run("main.cl")
        .output()
        .assert_exit(99);
}
