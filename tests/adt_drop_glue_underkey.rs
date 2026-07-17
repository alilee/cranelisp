// adt_drop_glue_underkey.rs — FIXME 0633 memory-safety repros (S111 CS-1.1).
//
// The vec drop-glue naming under-keys on the bare type name (`fqtn.name`),
// dropping BOTH the module qualifier AND the concrete type args, while the glue
// BODY is per-INSTANTIATION (concrete args are substituted into each ctor field
// and heap-classified per field BEFORE the field decs are emitted). Two
// heap-category-divergent uses of one bare name therefore collide on a single
// `Linkage::Local` glue symbol inside one `compile_to_module` batch, and the
// first-build-wins `get_name` skip hands the first-built (possibly wrong) glue
// to the second use. Two independently-sufficient under-keyed layers:
//   - `adt_drop_glue_name`  (compiler/resolution.rs)   → `runtime/drop_glue_{name}`
//   - `build_elem_dec_fn`   (compiler/vec_codegen.rs)   → `runtime/vec_elem_dec_{cat}_{name}`
//
// Attribution + reachability record: `tests/plan/s111-0633-adt-drop-glue-underkey.md`
// (REACHABLE, both axes, all three modes). Owner: /dev (backend) — both
// under-keys and both `get_name` skips are backend-local; typecheck/mono hand
// vec codegen a fully-disambiguated `Type::ADT(fqtn, args)` and are not
// implicated. These REDs flip GREEN when CS-1.1 re-keys BOTH layers on a mangle
// of the full concrete instantiation (module + type name + concrete args).
//
// NOTE ON THE `class=` TAG: `drop-glue-underkey` is not yet in the controlled
// `// defect:` vocabulary (`tests/CLAUDE.md`). It is used here per the S111
// dispatch; /qa to ratify the class addition (the closest existing tags are
// `uaf` for the R1 corruption face and `rc-miscount` for the R2 leak face —
// both are the SAME root under-key, hence the dedicated class).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// One generic ADT, one data ctor with two fields. `main` builds two
// heap-category-divergent Vec instantiations — `(Vec (Duo Int String))` and
// `(Vec (Duo String Int))` — in ONE `let`, keeps both live (so neither is
// DCE'd), and drops both at `let` scope exit. Clean behaviour: exit 2
// (vec-len 1 + vec-len 1), no crash. Under the defect the second use reuses the
// first's glue: the String-field dec is applied to the divergent instantiation's
// raw `Int` field (`atomic_rmw Sub` at a near-null address) → SIGBUS, and the
// String it should have dec'd leaks.
const R1_MODULE: &str = "\
(deftype (Duo a b) (MkDuo [:a fst :b snd]))
(defn main []
  (let [v1 [(MkDuo 1 \"one\")]
        v2 [(MkDuo \"two\" 2)]]
    (Pure (add-i64 (vec-len v1) (vec-len v2)))))
";

// Count `[RC] alloc` / `[RC]  free` lines in the RC trace stderr (the alloc/free
// balance witness for a pure leak — the DEF-3 precedent). Mirrors the helper in
// `spec_12_runtime.rs`.
fn rc_alloc_free_counts(stderr: &str) -> (usize, usize) {
    let allocs = stderr
        .lines()
        .filter(|l| l.contains("[RC]") && l.contains(" alloc "))
        .count();
    let frees = stderr
        .lines()
        .filter(|l| l.contains("[RC]") && l.contains(" free "))
        .count();
    (allocs, frees)
}

// -----------------------------------------------------------------------------
// 0633-R1 — concrete-args axis (single defn, single module). PRIORITY row.
// Deterministic within a batch: the collision fires the same way every run
// (order-dependent but the codegen order is fixed for a fixed source), so the
// observable is asserted deterministically (clean exit / correct value), not an
// intermittent crash. Covered in all three modes — the collision scope differs
// (REPL: one JIT per eval turn, both vecs in one turn = one batch; --run: whole
// module = one batch; --link/object: whole module into one ObjectModule) so
// each is an independent guard against a partial (one-path-only) fix.
// -----------------------------------------------------------------------------

// spec: spec/12-runtime.md §12.3.1 — no UAF / no corruption at ADT-in-Vec drop
// defect: class=drop-glue-underkey locus=crates/cranelisp-backend/src/compiler/{resolution.rs::adt_drop_glue_name,vec_codegen.rs::build_elem_dec_fn} found=S111 owner=/dev
#[test]
fn adt_vec_drop_glue_concrete_args_axis_repl_r1() {
    // Both vecs built and dropped in ONE REPL turn (one JIT batch). Clean:
    // `:primitives/Int 2`. Defect: the process SIGBUSes mid-teardown before the
    // value prints.
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(deftype (Duo a b) (MkDuo [:a fst :b snd]))\n\
             (let [v1 [(MkDuo 1 \"one\")] v2 [(MkDuo \"two\" 2)]] \
              (add-i64 (vec-len v1) (vec-len v2)))\n",
        )
        .output()
        .assert_stdout_contains(":primitives/Int 2");
}

// spec: spec/12-runtime.md §12.3.1 — no UAF / no corruption at ADT-in-Vec drop
// defect: class=drop-glue-underkey locus=crates/cranelisp-backend/src/compiler/{resolution.rs::adt_drop_glue_name,vec_codegen.rs::build_elem_dec_fn} found=S111 owner=/dev
#[test]
fn adt_vec_drop_glue_concrete_args_axis_run_r1() {
    // --run: the whole module is one codegen batch. Clean exit == the returned
    // Int (2). Defect: SIGBUS (no exit code).
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("main.cl", R1_MODULE)
        .run("main.cl")
        .output()
        .assert_exit(2);
}

// spec: spec/12-runtime.md §12.3.1 — no UAF / no corruption at ADT-in-Vec drop
// defect: class=drop-glue-underkey locus=crates/cranelisp-backend/src/compiler/{resolution.rs::adt_drop_glue_name,vec_codegen.rs::build_elem_dec_fn} found=S111 owner=/dev
#[test]
fn adt_vec_drop_glue_concrete_args_axis_link_r1() {
    // --link → run the produced standalone binary: the whole module compiles
    // into one ObjectModule (the widest collision scope). Clean exit == 2.
    // Defect: the linked binary SIGBUSes at teardown.
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("main.cl", R1_MODULE)
        .link_then_run("main.cl")
        .output()
        .assert_exit(2);
}

// -----------------------------------------------------------------------------
// 0633-R2 — module axis. Two ADTs with the SAME bare type name `Thing` from two
// different modules, different field layouts (one String field = heap, one Int
// field = non-heap), vecs of each dropped in ONE importing module's `main`.
// `FQTypeName` distinguishes them everywhere upstream; only the glue naming fn
// drops the module qualifier, so `runtime/drop_glue_Thing` collides in the
// importing module's batch. In this fixture the collision manifests as the LEAK
// face (the String-field element's heap string is never dec'd) rather than a
// crash — the program returns the correct value (exit 2) and the only witness is
// the RC alloc/free imbalance (5 allocs / 4 frees today; balanced when GREEN).
// -----------------------------------------------------------------------------

// spec: spec/12-runtime.md §12.3.1 — heap value freed when no longer reachable
// defect: class=drop-glue-underkey locus=crates/cranelisp-backend/src/compiler/{resolution.rs::adt_drop_glue_name,vec_codegen.rs::build_elem_dec_fn} found=S111 owner=/dev
#[test]
fn adt_vec_drop_glue_module_axis_leak_r2() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .env("CRANELISP_RC_TRACE", "1")
        .file("ma.cl", "(deftype Thing (MkA [:String s]))\n")
        .file("mb.cl", "(deftype Thing (MkB [:Int n]))\n")
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (import [ma [MkA]])\n\
             (import [mb [MkB]])\n\
             (defn main []\n\
               (let [va [(MkA \"hi\")]\n\
                     vb [(MkB 7)]]\n\
                 (Pure (add-i64 (vec-len va) (vec-len vb)))))\n",
        )
        .run("main.cl")
        .output();
    // The program computes the right answer under the leak (exit 2 = 1 + 1).
    assert_eq!(
        out.status.code(),
        Some(2),
        "expected clean exit 2 (vec-len 1 + vec-len 1)\nstdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    let (allocs, frees) = rc_alloc_free_counts(&out.stderr);
    assert_eq!(
        allocs, frees,
        "vecs of two same-bare-name ADTs (ma/Thing, mb/Thing) from different \
         modules must drop alloc/free balanced — the bare-name-keyed drop glue \
         collides in the importing module's batch, reusing the non-heap Int \
         glue for the String-field instantiation, leaking its heap string; got \
         {allocs} allocs / {frees} frees.\nstderr:\n{}",
        out.stderr
    );
}
