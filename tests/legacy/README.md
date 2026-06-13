# tests/legacy/ — Quarantine archive

Source archive of test files moved out of the e2e tier during the
Sprint 64 test-port. Not built by Cargo (nested directory under
`tests/` is not auto-discovered). Each file is awaiting harvest
into the owning crate's `#[cfg(test)]` unit tests.

| File | LOC | Tests | Owning skill | FIXME | Quarantined |
|---|---:|---:|---|---|---|
| `repl_experience.rs` | 3120 | 190 | /int (with /typecheck, /backend) | 0124 | 2026-05-03 |
| `repl_negative_old.rs` | 917 | 31 | /int (with /typecheck) | 0124 | 2026-05-03 |
| `ring3_repl.rs` | 763 | 41 | /int (with /typecheck) | 0125 | 2026-05-03 |
| `io.rs` | 1360 | 76 | /int (with /typecheck, /backend, /runtime) | 0127 | 2026-05-03 |
| `io_minimal.rs` | 120 | 5 | /int (Sprint 57 W6 reductions; with /backend) | 0127 | 2026-05-03 |
| `ring4_trace_taxonomy.rs` | 578 | 31 | /typecheck (with /runtime co-owner) | 0130 | 2026-05-04 |
| `v4_jit_reclaim.rs` | 700 | 6 | /backend (with /runtime co-owner) | 0133 | 2026-05-04 |
| `e2e.rs` | 2701 | 309 | /int (with /frontend, /typecheck, /backend) | 0134 | 2026-05-04 |
| `ring0.rs` | 1135 | 216 | /typecheck (with /backend, /int) | 0134 | 2026-05-04 |
| `ring1.rs` | 2253 | 380 | /typecheck (with /backend, /int) | 0134 | 2026-05-04 |
| `ring2.rs` | 2484 | 405 | /typecheck (with /backend, /int) | 0134 | 2026-05-04 |
| `lenient.rs` | 289 | 32 | /backend (with /runtime co-owner) | 0135 | 2026-05-04 |
| `sketch_port.rs` | 1886 | 296 | /qa (test-shape harvest) | 0136 | 2026-05-04 |
| `examples.rs` | 132 | 15 | /port | 0143 | 2026-05-05 |
| `examples_run.rs` | 193 | 1 | /port | 0143 | 2026-05-05 |
| `exemplar.rs` | 78 | 3 | /port | 0143 | 2026-05-05 |
| `exemplar_solver_correctness.rs` | 302 | 2 | /port | 0143 | 2026-05-05 |
| `sprint23.rs` | 2744 | 61 | /int | 0144 | 2026-05-05 |
| `wave6_demo_repros.rs` | 495 | 5 | /int (with /backend, /stdlib, /port co-owners) | 0148 | 2026-05-05 |
| `v4_pipeline.rs` | 1206 | 47 | /int (with /backend, /frontend, /platform co-owners) | 0149 | 2026-05-05 |

## Discipline

- Files here are NOT modified after quarantine. They are read-only
  archive until the FIXME is actioned and the file is deleted.
- Each FIXME is filed against the owning crate's `/dev` skill with
  a `harvest:` prefix in the title (e.g.,
  "harvest: tests/legacy/scheduler.rs into src/ (scheduler) unit tests").
- When a file is fully harvested, it is deleted (not blanked) and
  its row removed from this README. Git history preserves
  provenance.
