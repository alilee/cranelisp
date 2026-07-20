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
// The `class=drop-glue-underkey` tag is the ratified controlled vocabulary
// (`tests/CLAUDE.md` §"Defect-repro notation"; ratified S111, /qa): a
// per-INSTANTIATION artifact deduped under a key that under-determines its
// body. The closest existing tags — `uaf` (R1 corruption face) and
// `rc-miscount` (R2 leak face) — are two symptoms of the SAME root under-key,
// hence the dedicated class.

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

// RE-ATTRIBUTION (PLAN §I.4, /qa 2026-07-17 — DG-R2 4th re-attribution): the
// alloc/free imbalance this fixture witnesses is NOT the drop-glue collision
// (CS-1.1 proved) — it survives with ONE ADT / ONE module / no vec
// (`(defn main [] (let [s "hi"] (Pure 9)))` → 2 allocs / 1 free), is ownership-
// independent, and the leaked box is always the chronologically-LAST allocation
// (the IO result box). It is an ENTRY-`main` teardown leak of the final IO/result
// allocation, triggered by any heap-valued let in `main`'s body. The narrow 2-line
// guard (`entry_main_heap_let_teardown_balances_r2`, below) supersedes this fixture
// as the canonical guard; the module-axis COLLISION itself is guarded on its
// corruption face by `safety_oracle_lane.rs` (MS-P4).
// spec: spec/12-runtime.md §12.3.1 — heap value freed when no longer reachable
// defect: class=rc-miscount locus=entry-main IO-teardown seam found=S111 owner=/dev
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

// F-R1 (§1.6) — the NARROW 2-line guard for the DG-R2 re-attribution (PLAN §I.4):
// an entry-`main` teardown leak of the final IO/result allocation, triggered by
// ANY heap-valued let in `main`'s body. `(defn main [] (let [s "hi"] (Pure 9)))`
// leaks the LAST allocation (the IO result box) — 2 allocs / 1 free today —
// ownership-independent; the heap let value `s` IS freed, only the result box
// leaks. No ADTs, no vecs, no modules: this isolates the leak from the drop-glue
// collision (guarded separately on its corruption face by safety_oracle_lane.rs
// MS-P4). RED until the main-epilogue / IO-trampoline result-dec seam is fixed.
//
// R-3 CHARACTERIZATION (W5b discriminator, /qa reconciliation §2.2): this family is
// the shared record for the `ownership_reuse` +6 parity-abort delta cases and the
// standalone ALLOC=3/DEALLOC=1 case. Two discriminator runs (2026-07-19), BOTH
// confirming a scale-INVARIANT (fixed-residual) signature, NOT a per-value/-iteration
// leak:
//   (a) entry-main heap-let scaling: delta stays 1 (2/1 → 3/2 → 4/3) — only the
//       final IO/result box leaks (the let values ARE freed);
//   (b) `ownership_reuse` CHAIN_SRC under `CRANELISP_RC_STATS` at N=8/64/256:
//       allocs=6 / deallocs=2 — delta 4 INVARIANT across scale (a fixed set of
//       intermediate/result allocations, not per-element), and it aborts under
//       `CRANELISP_ALLOC_PARITY` (one of the +6). Fixed-residual, teardown-family.
// W5b runs (no modes set) read all of these as this family's residual, never as
// regressions; the flip trigger is the one teardown / fixed-residual fix, not a
// per-test leak fix. (`chaining_toggle_off_allocates_intermediate` is separately
// RED for the reuse-token differential, not this residual.)
// spec: spec/12-runtime.md §12.3.1 — heap value freed when no longer reachable
// defect: class=rc-miscount locus=entry-main IO-teardown seam found=S111 owner=/dev
#[test]
fn entry_main_heap_let_teardown_balances_r2() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .env("CRANELISP_RC_TRACE", "1")
        .user("(defn main [] (let [s \"hi\"] (Pure 9)))\n")
        .run("user.cl")
        .output();
    assert_eq!(
        out.status.code(),
        Some(9),
        "the program must exit 9:\nstdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    let (allocs, frees) = rc_alloc_free_counts(&out.stderr);
    assert_eq!(
        allocs, frees,
        "a heap-valued let in `main`'s body must not leak the final IO/result \
         allocation on entry-`main` teardown; got {allocs} allocs / {frees} frees \
         (PLAN §I.4 DG-R2 re-attribution — entry-main IO-teardown seam).\nstderr:\n{}",
        out.stderr
    );
}

// -----------------------------------------------------------------------------
// 0640 — the mangle-sanitize NON-INJECTIVITY axis (S111 CS-1.2). CS-1.1 re-keyed
// both layers on `adt_instantiation_mangle`, but the mangle "sanitized" the
// `render_type` output by mapping every non-`[A-Za-z0-9_]` char to `_` (and `_`
// to itself). That map is NOT injective: `-`/`?`/`!`/`.`/`/`/space all collapse
// to `_`, so two instantiations whose renders differ ONLY in those chars share
// one drop-glue symbol → the exact 0633 mis-drop, reproduced against the CS-1.1
// compiler. Hyphenated type names are IDIOMATIC, so this is directly reachable.
// These REDs flip GREEN when CS-1.2 makes the mangle injective (prefix-free
// escaping). Both under-keyed layers route through `adt_instantiation_mangle`,
// so the one fix covers both by construction.
// -----------------------------------------------------------------------------

// COLLIDING pair on the TYPE-NAME axis: `A-B` and `A_B` both sanitize to `A_B`
// under CS-1.1. Divergent field ORDER (Int,String vs String,Int) → divergent
// per-field heap categories → the shared first-built glue runs `atomic_rmw Sub`
// against the other instantiation's raw `Int` field (SIGBUS). Clean: exit 2.
const R1_0640_NAME_AXIS_MODULE: &str = "\
(deftype A-B (MkA [:Int n :String s]))
(deftype A_B (MkB [:String s :Int n]))
(defn main []
  (let [va [(MkA 1 \"one\")]
        vb [(MkB \"two\" 2)]]
    (Pure (add-i64 (vec-len va) (vec-len vb)))))
";

// spec: spec/12-runtime.md §12.3.1 — no UAF / no corruption at ADT-in-Vec drop
// defect: class=drop-glue-underkey locus=crates/cranelisp-backend/src/compiler/resolution.rs::adt_instantiation_mangle found=S111 owner=/dev
#[test]
fn adt_vec_drop_glue_name_sanitize_axis_repl_0640() {
    // Both vecs in ONE REPL turn (one JIT batch). Clean: `:primitives/Int 2`.
    // Defect: SIGBUS mid-teardown before the value prints.
    Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(
            "(deftype A-B (MkA [:Int n :String s]))\n\
             (deftype A_B (MkB [:String s :Int n]))\n\
             (let [va [(MkA 1 \"one\")] vb [(MkB \"two\" 2)]] \
              (add-i64 (vec-len va) (vec-len vb)))\n",
        )
        .output()
        .assert_stdout_contains(":primitives/Int 2");
}

// spec: spec/12-runtime.md §12.3.1 — no UAF / no corruption at ADT-in-Vec drop
// defect: class=drop-glue-underkey locus=crates/cranelisp-backend/src/compiler/resolution.rs::adt_instantiation_mangle found=S111 owner=/dev
#[test]
fn adt_vec_drop_glue_name_sanitize_axis_run_0640() {
    // --run: whole module = one codegen batch. Clean exit == returned Int (2).
    // Defect: SIGBUS (exit 135, no clean 2).
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("main.cl", R1_0640_NAME_AXIS_MODULE)
        .run("main.cl")
        .output()
        .assert_exit(2);
}

// spec: spec/12-runtime.md §12.3.1 — no UAF / no corruption at ADT-in-Vec drop
// defect: class=drop-glue-underkey locus=crates/cranelisp-backend/src/compiler/resolution.rs::adt_instantiation_mangle found=S111 owner=/dev
#[test]
fn adt_vec_drop_glue_name_sanitize_axis_link_0640() {
    // --link → run the standalone binary: whole module into one ObjectModule
    // (widest collision scope). Clean exit == 2. Defect: SIGBUS at teardown.
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("main.cl", R1_0640_NAME_AXIS_MODULE)
        .link_then_run("main.cl")
        .output()
        .assert_exit(2);
}

// spec: spec/12-runtime.md §12.3.1 — no UAF / no corruption at ADT-in-Vec drop
// defect: class=drop-glue-underkey locus=crates/cranelisp-backend/src/compiler/resolution.rs::adt_instantiation_mangle found=S111 owner=/dev
#[test]
fn adt_vec_drop_glue_module_sanitize_axis_run_0640() {
    // MODULE axis: two modules whose names differ ONLY in a sanitize-equivalent
    // char (`a-b` vs `a_b`), each defining a same-bare-name `Thing` with
    // divergent field ORDER. `FQTypeName` distinguishes `a-b/Thing` from
    // `a_b/Thing` everywhere upstream, but the CS-1.1 sanitize mapped both module
    // qualifiers to `a_b`, colliding the glue in the importing module's batch.
    // Divergent order (Int,String vs String,Int) → SIGBUS. Clean exit == 2.
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .file("a-b.cl", "(deftype Thing (MkA [:Int n :String s]))\n")
        .file("a_b.cl", "(deftype Thing (MkB [:String s :Int n]))\n")
        .file(
            "main.cl",
            "(import [primitives [Pure]])\n\
             (import [a-b [MkA]])\n\
             (import [a_b [MkB]])\n\
             (defn main []\n\
               (let [va [(MkA 1 \"one\")]\n\
                     vb [(MkB \"two\" 2)]]\n\
                 (Pure (add-i64 (vec-len va) (vec-len vb)))))\n",
        )
        .run("main.cl")
        .output()
        .assert_exit(2);
}
