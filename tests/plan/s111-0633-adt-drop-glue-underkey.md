# S111 — FIXME 0633 reachability assessment: ADT drop-glue name under-keys (bare `fqtn.name`)

`/qa` attribution + reachability record (Phase 5, 2026-07-17). Read-only analysis —
no build, no test run. Refers to the S111 CS-1 `/review` finding I1 and FIXME 0633.

## Verdict: REACHABLE — both axes, all three modes. Repro warranted.

The collision is a real, reachable silent-mis-drop / UAF defect of the 0350 /
ledger-25 class, not a latent sharp edge. Two independently sufficient naming
under-keys, **both** with a first-build-wins `get_name` skip:

1. **`adt_drop_glue_name`** (`crates/cranelisp-backend/src/compiler/resolution.rs:114`)
   keys `runtime/drop_glue_{fqtn.name}` — drops the **module** AND the **concrete
   type args**. The glue BODY is per-INSTANTIATION: `build_adt_drop_glue_fn`
   (`compiler/vec_codegen.rs:803-973`) substitutes `concrete_args` into each ctor
   field (`:834-838`) and classifies per-field heap-ness (`:851-858`,
   `emit_standalone_field_decs :999-1000`) before emitting field decs. The
   `get_name` skip at `:874` hands the FIRST-built glue to any later same-named
   request in the same Cranelift `Module`.
2. **The layer above collides first**: `build_elem_dec_fn`
   (`vec_codegen.rs:727-797`) names the per-element dec fn
   `runtime/vec_elem_dec_{heap|mixed}_{fqtn.name}` (`:734-738`) — same bare-name
   key, same `get_name` skip (`:741-745`), and the (possibly wrong) glue is baked
   into whichever dec fn built first. Even where the two instantiations would
   diverge on the `guarded` suffix, the glue name itself carries no suffix, so
   layer 1 still collides.

### Collision scope (the compilation-unit fact)

`get_name` is Cranelift-`Module`-local and the glue is `Linkage::Local`, so the
collision scope is **one `compile_to_module` batch**:

- **JIT (REPL/`--run` in-memory)**: `worker.rs::inline_jit_codegen_for_names`
  builds a **fresh `Jit` per batch** (`:1177`); under `--run` the batch is the
  whole module (`derive_codegen_batch`), under REPL incremental it is one eval
  turn's names. A single defn body is a sufficient batch.
- **Object (`--run` cache-write / `--link`)**: `session_v4/nice_worker.rs::emit_object`
  (`:310-322`) compiles **all names of a module into one `ObjectModule`** — the
  widest scope. Note the divergence surface this creates: a REPL session that
  never collided (two defns in two turns = two Jits) still writes a colliding
  `.o` for the same module — a latent REPL-vs-`--run` behavioural divergence
  (the red-flag class of `feedback_investigate_suspected_dual_path`).

### Axis (a) — concrete-args divergence: REACHABLE in ONE defn body

Nothing upstream disambiguates: monomorphisation mangles the **enclosing fn**
symbol (`f$Int+Vec`), never these runtime helper names; the `Type::ADT(fqtn,
args)` reaching vec codegen carries the concrete args, and the naming fn drops
them. Minimal shape (one module, one defn — fires in REPL, `--run`, `--link`):

```clojure
(deftype (Pair a b) (MkPair ...))   ; one data ctor, fields [a b]

(defn main []
  (let [v1 <Vec of (MkPair 1 "one")>    ; (Vec (Pair Int Str)) — first-built:
                                        ;   elem dec runtime/vec_elem_dec_heap_Pair
                                        ;   + glue runtime/drop_glue_Pair dec'ing field 1
        v2 <Vec of (MkPair "two" 2)>]   ; (Vec (Pair Str Int)) — get_name HIT:
                                        ;   REUSES v1's dec fn + glue
    0))                                 ; scope exit drops both vecs
```

At `v2`'s element drop the reused glue emits an **unguarded** `emit_rc_dec` on
field slot 1 (AlwaysHeap-classified for v1's `Str`; `vec_codegen.rs:1044`) —
for v2 that slot holds the raw `Int` → atomic-sub at `(2 + RC_OFFSET)` →
SIGSEGV / silent corruption; v2's `Str` in slot 0 is never dec'd → leak. Both
polarities of the silent-mis-drop class, order-dependent (whichever
instantiation codegens first wins) — the Principle-24 acid test (answer depends
on incidental order) fails. A single-type-param variant (`(Vec (Box Str))` then
`(Vec (Box Int))`) is even smaller and still fires (order 1: Int field dec'd as
pointer → crash; order 2: Str never dec'd → leak).

Reach requires the **vec-element** drop path (`emit_vec_aware_rc_dec` — scope
exit `fn_compiler.rs:1079`, ADT-field teardown `rc_emission.rs:224`, match
scrutinee `match_codegen.rs:206` — or the COW release path
`resolve_elem_dec_fn_ptr`): the non-vec ADT dec path uses per-site INLINE glue
(`rc_emission.rs::emit_inline_drop_glue`), which is not name-keyed and does not
collide. Nested ADTs under a vec glue recurse through the same named-glue path
(`emit_standalone_field_decs :1034/:1055`), so the collision also propagates one
level down.

### Axis (b) — module axis: REACHABLE

Two ADTs with the same bare name from different modules (different field
layouts), both used as vec element types in defns of ONE compiling module →
`runtime/drop_glue_{Name}` / `runtime/vec_elem_dec_heap_{Name}` collide in that
module's batch. `FQTypeName` distinguishes them everywhere upstream; only the
naming fn drops the module. Same observable class.

## The CS-1 assertion is wrong as stated

`resolution/tests.rs::adt_drop_glue_naming_identity_is_fqtn_keyed` (`:126-141`)
+ the `adt_drop_glue_name` rustdoc (`resolution.rs:109-113`) assert "per-TYPE
keying ⇒ the span×mono collision class does not apply". Two falsehoods:

1. **The key is not even fqtn-keyed.** The test name says `is_fqtn_keyed` and
   the rustdoc says "fqtn-keyed", but the format string uses `fqtn.name` alone —
   the test itself pins `"runtime/drop_glue_Box"` with the `user` module
   dropped. Two same-named FQTypeNames from different modules produce ONE name.
2. **Per-TYPE keying would still under-key.** The glue body is
   per-INSTANTIATION (concrete-args substitution precedes heap classification),
   so even a true module-qualified per-type key collides across heap-divergent
   instantiations. The closure/curry mirrors fold the mono discriminator for
   exactly this reason; the ADT glue folds nothing.

**What the corrected assertion must state** (post re-key): ADT drop-glue
identity = the full concrete instantiation — module + type name + concrete
args (i.e. a mangle of `Type::ADT(fqtn, args)`). Pins: (i) same fqtn,
different concrete args ⇒ DIFFERENT names; (ii) same bare name, different
modules ⇒ DIFFERENT names; (iii) same instantiation ⇒ stable name (the
`get_name` re-emit dedup is then sound). The elem-dec layer
(`vec_elem_dec_{suffix}_…`) must key identically — a fix that re-keys only the
glue leaves the outer collision intact and changes nothing observable. Until
the re-key lands, the test/rustdoc must not assert collision-freedom at all:
they state the true key (bare name), that the body is per-instantiation, and
cite the committed failing repro as the open-defect record.

## Attribution + handoff

- **Owner: `/dev` (backend), single-crate.** Both under-keys and both
  `get_name` skips are backend-local (`resolution.rs` + `vec_codegen.rs`);
  typecheck/mono produce fully-disambiguated `Type::ADT(fqtn, args)` and are
  not implicated. No cross-crate layer.
- **Defect protocol: `/testing` repro FIRST.** Per root `CLAUDE.md`
  §Usability-Findings-and-Defects, this defect closes only through a committed
  failing-not-ignored e2e repro. Plan rows below. The fix change-set then
  carries: the re-key of BOTH layers, the corrected unit assertion (renamed —
  it is no longer "is_fqtn_keyed"), the corrected rustdoc, and flips the e2e
  guards green. `/design` (backend) corrects the canonized claim in
  `audit-drain-s111.md` §4 per FIXME 0633.
- Byte-identity note (from the FIXME, confirmed): CS-1 did not regress
  behaviour — the old inline `format!` keyed identically. CS-1's defect is the
  false regression guard. Fix-vs-carry is `/sprint`'s call; if carried, the
  committed REDs are the durable trigger.

## Plan rows

| Row | Spec | Test | Status |
|---|---|---|---|
| 0633-R1 | spec/12-runtime.md §12.3.1 reqs 1+2 (no UAF, no leak) — concrete-args axis | e2e: one module, one defn, two heap-divergent vec-element instantiations of one generic ADT (axis-a sketch above); asserts clean exit + balanced alloc/drop (the `string_literal_alloc_drop_balanced` harness pattern) | [S111] — `/testing` to author, failing-not-ignored |
| 0633-R2 | spec/12-runtime.md §12.3.1 reqs 1+2 — module axis | e2e: same-bare-name ADTs from two modules, vecs of each dropped in one importing module | [S111] — `/testing` to author, failing-not-ignored |
| 0633-R3 | Coverage-matrix note (the standing variant×{pos,neg} category): glue-identity unit battery must cover the SAME axes as the closure/curry mirrors — {concrete-args, module, stability} × {distinct⇒distinct, same⇒same} | unit: corrected `resolution/tests.rs` identity test (replaces `adt_drop_glue_naming_identity_is_fqtn_keyed`), authored by `/dev` in the fix change-set | [S111] — blocked on re-key |

R1 is the priority row (single-defn, fires in all modes, deterministic order
within a batch). R2 may share a fixture. Both get `// defect:` notation per
`tests/CLAUDE.md` (class = silent-mis-drop, owner `/dev` backend, this file as
the attribution record).
