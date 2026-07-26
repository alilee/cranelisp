---
number: 0928
target: /design (runtime pair)
filed_by: /arch
filed_at: 2026-07-26
sprint_filed: 119
refers_to: design/runtime/s119-typed-consume-funnel.md §6.3 (the deliberately-NOT-flipped
  residue), §8 (the approved public-API delta), §13 (the three requested rulings);
  design/backend/non-concrete-release-contract.md §5.3 (free_io_node);
  design/arch/bounded-contexts.md §4b (the canonical statements added at the gate)
status: open
---

# Record the S119 Phase-3 gate outcomes in the tranche-A design: three rulings + `free_io_node`'s residue classification

`/arch`'s Phase-3 exit gate ruled the three items §13 requested, and one new
fact from FIXME 0923's resolution touches §6.3's residue accounting. Absorb all
four; delete this FIXME when recorded.

1. **`ElemConsumeFn`: spell the fn-pointer type inline** (`fn(Owned)`) in
   `consume_vec_with`'s public signature — the designer's recommendation is
   adopted; no `pub` alias (a name on the surface with no consumer). The
   current private alias may be kept crate-internally or deleted at `/dev`'s
   discretion; it must not become `pub`.
2. **The debug-profile-conditional `Drop` is acceptable in the baseline.** The
   committed `public-api.txt` is generated in the default (debug) profile as
   today; a companion rustdoc comment names the conditionality. The
   `#[cfg(not(debug_assertions))]` empty-`Drop` alternative is REJECTED (code
   for a documentation property).
3. **`launch.rs:452` dispensation GRANTED**: `/dev`(runtime pair) may edit
   exactly that one call expression in
   `crates/cranelisp-backend/src/compiler/control_flow/launch.rs`'s
   `#[cfg(test)] mod tests` — the one-line `unsafe { Owned::from_abi(cont_ptr) }`
   wrap — inside tranche-A CS-2's change-set. Scope: that call expression only;
   no other backend edit; the test's assertions and logic byte-identical
   (the §7 Class-2 rule applies to the hunk). Rationale: CS-2 does not compile
   without it, and a separate one-line `/dev`(backend) wave would split an
   atomic change-set.
4. **`free_io_node` (FIXME 0923, resolved) joins §6.3's deliberately-NOT-flipped
   residue, permanently.** The new entry point (the tail half of
   `consume_io_tree`, split at the dec; lands in the Spine-1 window, BEFORE
   tranche A) keeps a raw `i64` Rust signature plus its `#[export_name]` C-ABI
   shim: its precondition is a count already dec'd to zero, and an `Owned`
   models a live counted reference — it is *beneath* the abstraction, classified
   with `atomic_dec_rc`. Consequence for gate G3's arithmetic: the pair gains
   ONE raw heap-handle declaration between the §6.1 baseline measurement and
   tranche A's landing. The CS-5 count record must enumerate `free_io_node` as a
   named exclusion so the semantic count does not silently drift by one
   (expected: N_heap baseline 103 + 1 introduced − 42 flipped = 62 at CS-5,
   recorded with the enumeration, not as an unexplained delta).
