#!/usr/bin/env bash
# suite_polarity.sh — L-B2(i) suite-polarity leg (S101 stage M).
#
# tests/plan/s100-ownership-verification.md §3.1 L-B2(i) / §6.1: the entire
# canonical `cargo nextest run` must produce the IDENTICAL pass/fail set under
# both polarities of CRANELISP_NO_OWNERSHIP. The allowed delta between the two
# runs is empty (the toggle changes no observable pass/fail); the shared failure
# set must equal the ledgered intentional-failing set at execution time
# (tests/plan/ledger.md — verify by eye against the printed list).
#
# S103 (2026-07-05): the expected shared failing set at execution time is `{h3}`
# + the transient increment-II QA-first reds (ledger §"Sprint 103 Phase-5
# Stage-1 increment-II QA-first RED set") until each flips with its mechanism.
# These fail IDENTICALLY under both polarities (they are toggle-independent —
# schema/rc_inc/reuse_hit/undefined-symbol/T1-reload facts), so the two failsets
# still MATCH; the diff below stays empty. Re-run after each flip so the
# expected shared set shrinks toward `{}`.
#
# GATE-TIME lane, NOT the per-commit loop: two full suite runs (~2 × suite
# time). Executed at Phase-5 exit / wave gates per §6.1; run it AFTER the
# vec-query flip (qa plan §7.1 step 6) so the expected intentional-failing
# delta is empty.
#
# Usage: bash tests/scripts/suite_polarity.sh
# Exit: 0 iff both polarities produce the identical failing-test set.

set -u
cd "$(dirname "$0")/../.."

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

run_polarity() {
    # $1 = label, $2 = env assignment (may be empty)
    local label="$1" envs="$2"
    echo "=== suite_polarity: running canonical suite [$label] ..." >&2
    # --no-fail-fast: we need the complete failure set, not the first failure.
    if [ -n "$envs" ]; then
        env $envs cargo nextest run --no-fail-fast >"$WORK/$label.out" 2>&1
    else
        cargo nextest run --no-fail-fast >"$WORK/$label.out" 2>&1
    fi
    # Extract the failing-test identifiers (nextest "FAIL [ ...] binary::test"
    # result lines and abort/sigsegv lines), normalized + sorted.
    grep -E '^\s*(FAIL|ABORT|SIGSEGV|SIGABRT|TIMEOUT)' "$WORK/$label.out" \
        | awk '{print $NF}' | sort -u >"$WORK/$label.failset"
    echo "=== [$label] failing set ($(wc -l <"$WORK/$label.failset") tests):" >&2
    sed 's/^/    /' "$WORK/$label.failset" >&2
}

run_polarity "default" ""
run_polarity "no_ownership" "CRANELISP_NO_OWNERSHIP=1"

if diff -u "$WORK/default.failset" "$WORK/no_ownership.failset"; then
    echo "suite_polarity: PASS — identical pass/fail sets under both polarities."
    echo "Reminder: verify the shared failing set above equals the ledgered"
    echo "intentional-failing set in tests/plan/ledger.md (expected empty after"
    echo "the S101 flips)."
    exit 0
else
    echo "suite_polarity: FAIL — the two polarities diverge (diff above)." >&2
    echo "A test passing under only one polarity means the ownership toggle"    >&2
    echo "changes observable behaviour — a violation of the L-B2 oracle"        >&2
    echo "(tests/plan/s100-ownership-verification.md §0.1)."                    >&2
    exit 1
fi
