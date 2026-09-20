# design/backend/archive/

One document remains here, and it is **not** historical.

| Doc | Why it is retained |
|---|---|
| `io-trampoline-trace.md` | The IO event taxonomy, its emission disciplines and its off-path performance bound are cited from `benches/io_trace_off_path.rs`, `tests/spec_10_io.rs`, `src/observability.rs` and `src/io_trace.rs`. It is a live contract that happens to live at this path. |

Its placement is a known wart: the consumer side relocated to the integration
layer, so the natural home is `design/int/observability.md`. Moving it would
break live source citations, and the destination belongs to another owner — so
it stays until that relocation is done deliberately, with the citations repaired
in the same change.

**Do not add documents here.** The directory is not a holding pen. A record
whose content has landed is deleted, not moved; Git preserves it. A record that
is still the canonical source of something belongs with the current designs at
`design/backend/`, where readers look.

**Retired at S122**, after verifying that every reduction they described is a
committed test and that their durable rules had a current home:

- the Sprint-59 cache-load triage — its `.L`-local GOT-symbol rule is now
  `module-caching.md` §13.3.1;
- the Sprint-59 defects 4/5/6 reduction — its repros are the `d45_*`/`d6_*`/
  `s60_*` families in `tests/regression.rs`, and its convergence invariant is
  `jit-object-convergence.md` §1;
- the Sprint-61 closure double-free investigation — its rule and the boundary
  ruling behind it are `ring2-rc.md` §5.6, and its raw logs are retained in
  `tests/sprint61/race-evidence/`;
- the defect-8 repro notes — the code they describe was deleted, and the rule
  that replaced it is in `src/CLAUDE.md`.
