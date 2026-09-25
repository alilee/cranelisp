# W0.b synthetic-body golden-CLIF corpus — MANIFEST

**Purpose:** the CLIF byte-identity gate for the entry classes whose codegen
view typecheck builds with the lenient (types-only) builder, per
`design/arch/backend-keyed-consumer.md` §4. A passing suite proves only that
these bodies still run; this corpus proves their generated code is unchanged.
**Owner:** `test` (corpus, goldens, this manifest and the harness
`tests/golden_clif_w0b.rs`).

## Entries

| # | Entry | Class | Focus frame(s) |
|---|---|---|---|
| 01 | `corpus/01_ctor_def.cl` | constructor `Def` synthetic body | `user::Box.MkBox` |
| 02 | `corpus/02_synth_accessor.cl` | synthesised field accessor | `user::Point.x`, `user::Point.y` |
| 03 | `corpus/03_multisig_variant.cl` | `f$Var` multi-sig variant body | `user::pick$overload-arm$0`, `user::pick$overload-arm$1` |
| 04 | `corpus/04_expr_disposition3.cl` | `__expr` §3.11.2-disposition-3 body | `user::__expr` |
| 05 | `corpus/05_macro_clause.cl` | non-concretized macro-clause body | `user::twice$macro-clause$0` |

Every golden also carries the `IO.Pure` Int constructor-instance frame; 05
also carries the `SList.SCons` Sexp instance frame. The remaining lenient
class in the design — a generic template reached by direct compile — has no
free-standing program that reaches codegen, so it has no e2e golden here.

## Capture contract

- **Mechanism:** `CRANELISP_CODEGEN_DUMP='*'`, cold-cache `--run --no-cache`,
  one invocation per corpus entry in an isolated tmpdir (self-importing —
  `(import [primitives [*]])`, no prelude file). `--no-cache` eliminates the
  nice-worker `.o` cache-write pass, so each symbol dumps exactly once. A
  **duplicate frame is a hard error**, never deduped.
- **Frames** are extracted per `; === CLIF <name> ===` …
  `; === end CLIF <name> ===` block, where `<name>` is the rest of the header
  line: canonical constructor-instance names contain spaces, for example
  `user::(primitives/IO.Pure [primitives/Int] (primitives/IO primitives/Int))`.
  Frames are sorted by name, content **byte-verbatim, NO canonicalization**.
  **Zero frames, a duplicate frame, disagreeing start/end names and a header no
  complete frame accounts for are hard errors.** The dump channel is STDERR.
  Keep the extraction in step with `tests/ownership_fences.rs`
  (`extract_clif_frames`) and `tests/scripts/clif_golden.sh`.
- **No normalization:** SSA value numbers, block labels, GOT-slot operands and
  wrapper identity are load-bearing — masking them would hide carrier-versus-code
  drift. Byte identity is admissible because the dump is deterministic; a
  nondeterministic class is an ordering bug to investigate, not a reason to
  canonicalize.
- **Determinism self-test:** `assert_golden_clif` double-captures each entry
  and byte-compares before the golden compare, on every run.
- **Config pins:** the same emission-affecting and trace variables are unset
  as in the [L-B1 capture contract](../clif_baseline/MANIFEST.md#capture-contract);
  keep the lists in step.
- **Extension ≠ re-baseline; scoped re-baseline only.** An emission-affecting
  change re-captures only the drifted entries and attributes every changed
  frame to the change's seam in its commit message. Wholesale re-capture
  without attribution is forbidden. The Git history of `golden/` holds each
  attributed re-baseline.
