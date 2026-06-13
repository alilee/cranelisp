---
number: 0336
target: /dev
filed_by: /qa
filed_at: 2026-06-13
sprint_filed: 81
refers_to: src/process_form.rs::rewrite_parent_inline_mod + handle_mod + process_cluster_once Pass-0, spec/08-modules.md §8.2.2, design/arch/fixmes/0217 (resolved), design/arch/fixmes/0330 (e2e owed)
status: open
---

# Inline `(mod …)` parent-rewrite double-invocation with a stale span corrupts the parent file

## Issue

While authoring the owed e2e for FIXME 0330 (the §8.2.2 step-2 parent rewrite
introduced by FIXME 0217), the e2e SURFACED a defect: under `--run`, the parent
source file is **corrupted** after a successful run.

Repro (`app.cl` in a fresh project dir):

```
(import [primitives [Pure]])
(mod child (defn helper [] 7))
(defn main [] (Pure (child/helper)))
```

```
$ cranelisp --run app.cl     # exits 7 (in-memory state is correct)
$ cat app.cl
(import [primitives [Pure]])
(mod child)e (child/helper)))      # <-- CORRUPT: `main` form truncated
```

Any subsequent run of the project then fails to parse:
`app.cl:2:28: error: parse error: unexpected character: ')'`.

## Root cause (isolated)

`rewrite_parent_inline_mod` (`src/process_form.rs`) is invoked **twice** for the
same `(mod child …)` form during a single `--run`:

1. **First call:** `source.len() = 96`, `decl.span = 29..59` (correct — slices
   exactly `(mod child (defn helper [] 7))`). Rewrites the file to
   `(mod child)\n(defn main …)` (now 77 bytes). Correct.
2. **Second call:** `source.len() = 77` (the already-rewritten file), but
   `decl.span` is **STILL 29..59** — the stale span from the original 96-byte
   parse. Slicing 29..59 over the 77-byte file yields
   `(mod child)\n(defn main [] (Pur`, which is not exactly `(mod child)`, so the
   exact-match idempotence guard in `splice_inline_mod_to_bare` misses, and the
   splice overwrites that range with `(mod child)` — truncating `main`.

The **reader span is correct** (verified: the `(mod …)` `Sexp::List` span is
29..59, slicing the form exactly) and the **pure splice is correct** (its three
unit tests pass with hand-built spans). The bug is the **double-invocation with a
stale span on cluster retry**: the S78 cluster retry-from-top re-runs Pass-0
(`process_cluster_once`) against the *original* `sexps` (span 29..59) after the
first pass has already shrunk the on-disk file. The `inline_body`-dropped guard
on the in-memory symbol table (line ~2486) does not prevent the second call,
because Pass-0 re-classifies the `decl` fresh from `sexps` (which still carries
the inline body + original span) on each retry.

## Proposed resolution (int — /dev)

Make the parent rewrite robust to retry. Options (int's choice):

1. **Track extraction-done per (module, submodule):** once `handle_mod` has
   extracted+rewritten an inline form this session, skip the rewrite on
   subsequent Pass-0 retries (a session-side `HashSet<(ModuleFullPath,
   ModuleName)>` on `SharedState`, or a flag on `ModuleState`). Cleanest — the
   rewrite is a one-time side effect, not a per-pass operation.
2. **Make `splice_inline_mod_to_bare` self-locating / retry-safe:** instead of
   trusting the stale `decl.span`, re-locate the inline `(mod name …)` form in
   the *current* on-disk source (or no-op when the file already contains a bare
   `(mod name)` at a parse, not at the stale byte range). Strictly idempotent
   against a moved span.

Option 1 is preferred (one-time side effect modelled as one-time).

## Test coverage

The two failing-not-ignored e2e regression guards are landed (S81 W-H,
`tests/spec_08_modules.rs`):

- `inline_mod_extracts_backing_file_and_rewrites_parent` — asserts the
  surrounding `main` form is preserved (fails on the corruption);
- `inline_mod_extraction_is_idempotent_on_rerun` — asserts the re-run exits 7
  (fails because the first run corrupts the parent).

Both carry `FIXME(/dev 0336)` and `// spec: spec/08-modules.md §8.2.2`. They
flip green when this FIXME is resolved. FIXME 0330's e2e obligation is satisfied
by these two tests (they ARE the e2e — they just additionally caught 0336).

## Context

FIXME 0217's "manually verified by hand" claim was true only for the FIRST run's
exit code; the durable on-disk corruption was not observed because the run
succeeds. The unit tests gave false confidence — they used a hand-built span and
single invocation, never exercising the real cluster-retry double-call. This is
the canonical "unit test passes, e2e fails → bug is in the integration wiring"
case from `tests/CLAUDE.md §"Isolating Cross-Crate Failures" Step 4`.
