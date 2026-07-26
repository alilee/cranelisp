// ctor_as_value.rs — S114 Phase-6b, FIXME 0712 born-green regression guards.
//
// Constructors — user sum/product ctors AND the seeded `Some`/`None` — are
// first-class values (spec §5.2.7): passable to a HOF, bindable with `let`,
// composable through `map`-style IO. The S102 `null-got-slot` family
// (`vec-query`/generic-value-use SIGSEGV, 0476) once made a bare ctor used as a
// first-class value crash; the S114 carrier/GOT-slot work fixed it. /qa verified
// all three shapes GREEN at HEAD `9fda5f40`, both `--run` and `--link`
// (s114-test-plan §12 item 3). These guards pin that fix so a regression reddens
// here. The composed map-io cell is the named gate for /stdlib's io.cl bare-`Some`
// `timeout` simplification and the /docs concurrency.md ctor rough-edge retirement.
//
// GREEN guards (past tense — the defect is fixed; retro-tagged for the density/
// hotspot analysis over the permanent corpus, per tests/CLAUDE.md §Defect-repro).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// Run the program in BOTH `--run` and `--link`, asserting the same exit both modes
// (a ctor-as-value defect that survives one mode but not the other is exactly the
// GOT-slot-population class this family guards).
fn assert_run_and_link(user: &str, code: i32) {
    for link in [false, true] {
        let b = Cranelisp::new().with_prelude(PreludeVariant::PrimitivesOnly);
        let b = if link {
            b.link_then_run("user.cl")
        } else {
            b.run("user.cl")
        };
        let o = b.user(user).output();
        assert_eq!(
            o.status.code(),
            Some(code),
            "[{}] expected exit {code}; got {:?}:\n{}{}",
            if link { "--link" } else { "--run" },
            o.status.code(),
            o.stdout,
            o.stderr
        );
    }
}

// Shape 1 — a bare user ctor to a HOF (`(apply-it Bx 7)`), a bare seeded ctor to a
// HOF (`(apply-it Some 8)`), and a ctor bound-then-applied (`(let [f Some] (f 9))`)
// — one program, three first-class-ctor forms. Sum a=7 + b=8 + c=9 = 24 ⇒ exit 7.
// spec: spec/05-definitions.md §5.2.7 — constructors are first-class values
// (passable as arguments, bound to variables); nullary/seeded ctors alike.
// defect: class=null-got-slot locus=crates/cranelisp-backend carrier/GOT-slot population for a bare constructor used as a first-class value (0476 vec-query family; fixed S114 carrier work) found=S102 owner=/dev
#[test]
fn bare_ctors_as_first_class_values_run_and_link() {
    assert_run_and_link(
        "(deftype B (Bx [:Int v]))\n\
         (defn apply-it [f x] (f x))\n\
         (defn unbx [b] (match b [(Bx v) v]))\n\
         (defn opt-or [o d] (match o [(Some x) x None d]))\n\
         (defn main []\n\
         \x20 (let [a (unbx (apply-it Bx 7))\n\
         \x20       b (opt-or (apply-it Some 8) 0)\n\
         \x20       c (opt-or (let [f Some] (f 9)) 0)]\n\
         \x20   (Pure (if (eq-i64 (add-i64 a (add-i64 b c)) 24) 7 99))))\n",
        7,
    );
}

// Shape 2 — the composed `map-io` + bare-`Some` shape (the /stdlib io.cl gate):
// `my-map-io = (bind io (fn [x] (Pure (f x))))`, applied as `(my-map-io Some (Pure
// 5))` — the bare ctor `Some` flows as the mapped function through an IO bind. The
// mapped `(Some 5)` unwraps to 5 ⇒ exit 5.
// spec: spec/05-definitions.md §5.2.7 — a constructor passed as the mapping fn of
// a first-class map-over-IO composition.
// defect: class=null-got-slot locus=crates/cranelisp-backend carrier/GOT-slot population for a bare constructor threaded through an IO-bind map (io.cl timeout simplification gate; fixed S114) found=S102 owner=/dev
// defect: class=wrong-reject locus=crates/cranelisp-backend/src/drop_glue.rs::ctor_shapes found=S118 owner=/dev
//   — the cell's CURRENT red is NOT the S102 slot defect above (fixed S114);
//   it is FIXME 0907's hard refusal, `constructor 'Bind' disagrees on declared
//   parameter identity for 'primitives/IO'`, which every concrete-`IO T`
//   release trips in `DropGlueRegistry::ctor_shapes`. Two defects, one cell,
//   both lines kept: the locus records where each bug LIVED
//   (tests/plan/s118-test-plan.md §11.1).
#[test]
fn bare_ctor_as_map_io_function_run_and_link() {
    assert_run_and_link(
        "(defn my-map-io [f io] (bind io (fn [x] (Pure (f x)))))\n\
         (defn opt-or [o d] (match o [(Some x) x None d]))\n\
         (defn main []\n\
         \x20 (bind (my-map-io Some (Pure 5)) (fn [o] (Pure (opt-or o 0)))))\n",
        5,
    );
}

// Shape 3 — the docs `timeout` shape: `race` of a `map-io` producing a bare `(Some
// 6)` against a sleep-arm yielding `None`. The map-io arm wins the race; the bare
// ctor `Some` composes through both the race and the map ⇒ exit 6. (The /docs
// concurrency.md rough-edge retirement is gated on this.)
// spec: spec/05-definitions.md §5.2.7 — a constructor composed through race + map-io.
// defect: class=null-got-slot locus=crates/cranelisp-backend carrier/GOT-slot population for a bare constructor composed through race + map-io (concurrency.md rough-edge gate; fixed S114) found=S102 owner=/dev
// defect: class=wrong-reject locus=crates/cranelisp-backend/src/drop_glue.rs::ctor_shapes found=S118 owner=/dev
//   — as with the sibling above: the S102 slot defect is fixed (S114) and the
//   current red is FIXME 0907's `Bind` refusal on the concrete-`IO T` release
//   path (tests/plan/s118-test-plan.md §11.1).
#[test]
fn bare_ctor_through_race_map_io_run_and_link() {
    assert_run_and_link(
        "(defn my-map-io [f io] (bind io (fn [x] (Pure (f x)))))\n\
         (defn opt-or [o d] (match o [(Some x) x None d]))\n\
         (defn main []\n\
         \x20 (bind (race (my-map-io Some (Pure 6))\n\
         \x20             (bind (sleep 1000) (fn [_] (Pure None))))\n\
         \x20       (fn [o] (Pure (opt-or o 0)))))\n",
        6,
    );
}
