---
number: 0506
target: /design (cranelisp-backend)
filed_by: /sprint
filed_at: 2026-07-03
sprint_filed: 102
refers_to: design/backend/ownership-codegen.md §13.1 (normalization contract items 1–4, blockquote at ~:1030, claim at ~:980)
status: open
---

# §13.1 capture spec — normative dedup/scope pin missing; duplicate-frame mechanism mischaracterized

## Issue

The Wave-3 B0-be review (S102) confirmed the golden-oracle first-occurrence dedup pin is SOUND but found the spec does not state it, and the recorded mechanism is wrong:

1. **Normative gap**: §13.1's normalization contract (items 1–4) is silent on frame dedup entirely. The first-occurrence policy lives only in a narrative blockquote and script comments.
2. **Mischaracterization**: the blockquote says duplicate frames come from "recompilation passes re-derive the JIT symbol set". Empirically they are the **nice-worker `.o` cache-write emission pass** (`src/session_v4/nice_worker.rs::emit_object` ~:314 → `compile_to_module::<ObjectModule>`; `dump_this` at `crates/cranelisp-backend/src/lib.rs:989` ignores the worker's `capture_clif: false`). Proof: `--no-cache` yields exactly one frame per symbol; cache-enabled yields exactly two.
3. **Scope pin unstated**: the oracle sees **JIT-pass emission only**. Object-pass divergence (the `jit-object-convergence.md` class) is permanently outside L-B1 and is guarded by the mode-equivalence lanes instead. If a future ownership mechanism is ever module-type-gated, its object-side delta is invisible to this oracle. Future wave developers reasoning from "the deduped frames are redundant recompiles" start from a false premise.
4. **Stale claim** (~:980): "cache hits do not re-codegen and dump nothing" — observed: warm-cache single-file `--run` still compiles and dumps 2× per symbol. (Whether that recompile is intended is an /int classification question — flag only.)
5. **Reproducibility note**: the object pass's funcref declaration order is scheduler-timing-dependent, so `.o` bytes are non-reproducible run-to-run. Benign now (relocations resolve by name; cache keys on source hashes) but a Phase-H reproducible-builds concern; cheap eventual fix = sorted funcref declaration in `compile_to_module`.

## Proposed resolution

Edit §13.1: (a) add normative item 5 — duplicate frames dedup to FIRST occurrence, naming the `.o` cache-write pass as the source (or, if /qa adopts `--no-cache` capture per review F4, document the `--no-cache` pin instead and make a duplicate frame a hard error); (b) state the JIT-pass-only scope pin + the mode-equivalence-lane guard for the object side; (c) correct/remove the ~:980 claim; (d) fold the reproducibility sentence. Coordinate (a) with the state of `tests/scripts/clif_golden.sh` at drain time.

## Operational implication

Must land **with or before the first B3.x scoped re-baseline** (S102 Wave 11) so delta-attribution reasoning starts from the correct mechanism model. Full evidence: S102 Wave-3 /review report (see `sprints/SPRINT.md` §Notes Wave-3 entries).
