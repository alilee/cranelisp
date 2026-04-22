# Heisenbug race evidence — Sprint 61 Wave 3 step 3b

**Frozen artefacts.** These dumps capture the scheduler-trace output for
one failing and one passing repro of the heisenbug race documented in
`design/int/heisenbug-race-closure.md`. They are committed as evidence
supporting step 3c's hypothesis selection (a separate agent). They
MUST NOT be overwritten by step 3d/3e — post-fix dumps will be
committed as `*-post-fix-<SHA>.log`, not as replacements. Preserve
these files across subsequent sprints.

## Harness

Both dumps were captured against commit `35062ca` (Sprint 61 Wave 2
slices 1+2 close). The driver is the reduced harness
`tests/sprint23.rs::heisenbug_race_reduced_concurrent_import_pairs`,
authored in step 3a: 6 concurrent OS threads × 2 sequential
(`session 1 → rm cache → session 2`) pairs × up to 10 trials (fast-fail
on first reproduction), each thread against its own `tempfile::TempDir`.
See `design/int/heisenbug-race-closure.md §3b`.

## Invocation

    CRANELISP_SCHEDULER_TRACE=1 RUST_BACKTRACE=1 \
      cargo nextest run --test sprint23 \
        heisenbug_race_reduced_concurrent_import_pairs --no-capture \
      2>&1 | tee /tmp/heisenbug-run.log

The SCHEDULER_TRACE dump lands on the subprocess's stderr (via
`src/main.rs::SchedulerTraceFlushGuard`) and only surfaces to the test
runner output when the test panics with a captured-stderr error
message — i.e., only on the failing path. See "Passing-run caveat" below.

## Runs

- **`failing-run-35062ca.log`** (70 lines): first capture attempt (1 of 1)
  was already red. Full nextest framing plus the one failing
  subprocess's `=== CRANELISP_SCHEDULER_TRACE DUMP ===` section
  (23 `[SCH]` events) surfaced via the test's assert-panic message.
  Signature matches the baseline ledger entry verbatim:
  `'helper-val' not found in module 'helper'` + `undefined variable:
  helper-val`.

- **`passing-run-35062ca.log`** (60 lines): assembled from two captures.
  Part 1 — nextest framing from attempt 12 of 25 (per-test pass rate
  ~5% with `CRANELISP_SCHEDULER_TRACE=1` enabled). Part 2 — a
  representative passing subprocess trace, captured by hand-replaying
  the harness's session-1 invocation six-way concurrent against fresh
  `tempfile::TempDir`s (all six subprocesses exited 0 with stdout
  containing `99`). Subprocess 1 of 6 is embedded; the other five
  have the same event set with different timestamps.

## Passing-run caveat

The reduced harness uses `Stdio::piped()` on each subprocess's stderr
and only references the captured stderr inside an `if !stdout.contains("99")`
error-message construction. On the passing test path, all 24 subprocess
stderrs (6 threads × 2 iters × 2 sessions) are discarded. To capture
genuine passing-subprocess trace content, the solo hand-replay above
was the minimal-invasive option that avoids modifying the step 3a harness.
The event set in the solo replay matches the failing-subprocess event
shape 1:1 — same 23 tags, same 4 modules (`user`, `prelude`,
`primitives`, `helper`), differing only in ordering at the cross-thread
interleaving points. No production code was touched.

## High-level divergence signature

Both dumps have 23 `[SCH]` events and touch the same four modules.
Near the end of each trace, around the `helper` module typecheck
window, the event ordering across `ThreadId(1)/0` and `ThreadId(2)/1`
differs. See `design/int/heisenbug-race-closure.md §3c` for the
factual observation notes. Step 3c selects the hypothesis (H1/H2/H3).

## Reproduction

Failing run:

    CRANELISP_SCHEDULER_TRACE=1 RUST_BACKTRACE=1 \
      cargo nextest run --test sprint23 \
        heisenbug_race_reduced_concurrent_import_pairs --no-capture

(Expect ~90% fire rate per invocation.)

Passing subprocess trace (solo replay):

    BINARY=target/debug/cranelisp
    FIXTURES=tests/fixtures
    D=$(mktemp -d); printf '(defn helper-val [] 99)\n' > "$D/helper.cl"
    cd "$D" && CRANELISP_SCHEDULER_TRACE=1 CRANELISP_LIB="$FIXTURES" \
      "$BINARY" 2>stderr.log <<'EOF'
    (import [helper [helper-val]])
    (helper-val)
    /quit
    EOF
    cat stderr.log

## Scope

- Frozen. DO NOT overwrite when step 3e's fix lands.
- Step 3c (hypothesis selection) reads these files and updates
  `design/int/heisenbug-race-closure.md §7` + §8.
- Step 3d/3e (fix) leaves these files intact; post-fix dumps go under
  `*-post-fix-<SHA>.log`.
