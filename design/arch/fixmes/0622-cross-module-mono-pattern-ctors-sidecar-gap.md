---
number: 0622
target: /arch
filed_by: /dev
filed_at: 2026-07-16
sprint_filed: 110
status: open
refers_to: crates/cranelisp-typecheck/src/traits/monomorphise.rs:516-519
  (the mono-instance `codegen_view` build threads the CALLER module's
  `state.method_resolutions.pattern_ctors`); design/arch/backend-keyed-consumer.md
  §1.1.2 re-sweep row 10 ("Pattern ctors (sidecar) — correct S109 §10");
  design/arch/backend-keyed-consumer.md §4/§5 (W3 deletes the S19 fallback).
---

# Cross-module monomorphisation drops the template's `pattern_ctors` sidecar — a match-position ctor producer gap that BLOCKS S110 W3

## One line

A generic function with a ctor-pattern body (`(match r [(Ok x) …])`), defined in
module A and **monomorphised by a call from module B**, produces a mono instance
whose `MonoMatchArm.resolved_ctor` is `None` — because the template's pattern
spans were recorded in **A's** check run, but the mono view is built with **B's**
`pattern_ctors` map. This was masked on W1/W2 by backend `compile_constructor_pattern`'s
S19 `None`-arm `lookup_constructor` fallback; **W3 deletes that fallback**, so the
gap surfaces as a hard `CodegenError` and BLOCKS W3.

## Repro (reproducible, root-caused)

With the W3 stash applied (`stash@{0}` — "S110 W3 backend deletion"), run the REPL
against the workspace stdlib:

```
env CRANELISP_LIB=$(pwd)/stdlib ./target/debug/cranelisp
> (let [r :(Result Int String) (Ok 42)] (match r [(Ok x) (= x 42) (Err _) false]))
```

Backend codegen of module `fn.result.test` fails:

```
codegen error at 866..912: pattern constructor 'Ok' reached codegen with no
resolved_ctor carrier (typecheck keying drift; every ctor pattern carries its
storage identity post-W0.b)
```

which cascades (the module fails to commit) to the user-visible
`type error: unknown type 'Result'`. On clean W2 (S19 fallback intact) this same
body compiles via `lookup_constructor`. The whole workspace stdlib and ~53
`spec_11_stdlib` / `stdlib_conformance` tests fail identically once W3 lands.

`fn.result.test` imports `is-ok?`/`is-err?`/`unwrap-or`/`map-ok`/… from
`fn.result` via `(import [super […]])`; those are generic `(Result a b)` functions
whose bodies `(match r [(Ok …) (Err …)])` monomorphise per concrete call from the
test module. The mono instance registers in the caller (`fn.result.test`,
per §1.1.1), and its body is built at `monomorphise.rs:519`:

```rust
// monomorphise.rs:516-518 (the FALSE assumption):
// "`pattern_ctors` stays on the enclosing map: template ctors are instance-
//  INVARIANT (same span → same ctor), so the original template check's entries
//  serve every instance."
let codegen_view = match MonoExpr::from_expr(
    mono_defn_ast.body(),
    &state.method_resolutions.pattern_ctors,   // <-- the CALLER's map
    resolved_targets,
) { … }
```

The assumption holds for **same-module** mono (template + call in one check run,
one `pattern_ctors` map). It is **false cross-module**: the template body's Ok/Err
pattern spans were recorded during `fn.result`'s check; `fn.result.test`'s
`pattern_ctors` never saw them → `from_expr` reads `None` → `MonoMatchArm.resolved_ctor
= None`.

The §1.1.2 recorder-grounded re-sweep row 10 marked "Pattern ctors (sidecar) —
correct (S109 §10)", but S109 §10 only verified the SAME-module mint at
`instantiate_ctor`; the cross-module mono TRANSPORT of `pattern_ctors` was never
in scope. This is the pattern-ctor analog of the W0.1b cross-module
storage-module gap (§1.1.1) — the sweep found it for the `resolved_target`
(Var/Apply) carrier but not for the `pattern_ctors` sidecar.

## Why this is a producer gap, not a backend workaround

Rev-2 (§1.2) forbids a keyed-read-else-resolver hybrid, and the W3 dispatch is
explicit: a match-position hard-miss is "a producer gap to flag to /arch (NOT a
hybrid workaround)". The identity is not recoverable in the backend without a
name resolver (exactly what W3 deletes). The fix must populate the sidecar in
typecheck.

## Requested ruling (the transport mechanism — /arch)

The cross-module mono seam must supply the DEFINING module's template pattern
identities to the mono view build. Candidate shapes (for /arch to rule, mirroring
the W0.1b storage-module derivation):

1. At the mono seam, build the view against the **union** of the caller's
   `pattern_ctors` and the DEFINING module's template `pattern_ctors` (the home's
   check-run sidecar — the module whose source contains the template body); or
2. **Transport** the template's `pattern_ctors` entries for the template body's
   spans onto the per-instance map at `recheck_body_for_mono` (the same place the
   per-instance `resolved_targets` is assembled), keyed by the (span-stable)
   template body spans.

Same-module mono and direct user matches are already correct (verified: a user
`(match r [(Ok x) …])` in its own module compiles on the W3 stash). The fix is
scoped to the cross-module mono transport in `traits/monomorphise.rs` /
`recheck_body_for_mono`. No `cranelisp-types`/schema change is anticipated
(sidecar VALUES only), but /arch owns that call.

## Blocking relationship

- **BLOCKS S110 W3** (`### /dev (W3)` in `sprints/SPRINT.md`). W3's backend
  deletions are complete and green in `stash@{0}` **except** they cannot delete
  the S19/S20/`lookup_constructor` fallback until this producer gap is closed.
  The pattern mirrors W1 → BLOCKED on 0620 → W1.1b producer fix → W1 re-deploy.
- After the typecheck fix lands (with a `/testing` cross-module-mono pattern-ctor
  repro, failing-not-ignored), W3 re-deploys wholesale from the stash.

## Suggested handling

`/arch` rules the transport mechanism (1 vs 2 or better); `/sprint` schedules the
typecheck `/dev` fix + `/testing` repro; then re-dispatch W3 `/dev` (backend) to
pop the stash and complete the grep-gate deletion.
