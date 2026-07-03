#!/usr/bin/env bash
# clif_golden.sh — L-B1 golden-CLIF capture + diff runner.
#
# Contract: tests/fixtures/clif_baseline/MANIFEST.md (capture pins) +
# tests/plan/s100-ownership-verification.md §3.1 (lane spec) +
# design/backend/ownership-codegen.md §13.1 (capture substrate, Hook H1).
#
# Usage:
#   tests/scripts/clif_golden.sh capture   # (re)capture goldens — B0-be and
#                                          # scoped re-baselines ONLY; never
#                                          # run casually (wholesale re-capture
#                                          # without attribution is forbidden)
#   tests/scripts/clif_golden.sh diff      # toggle-off dump of HEAD vs golden;
#                                          # exit non-zero on any delta
#   tests/scripts/clif_golden.sh selftest  # determinism self-test: double
#                                          # capture, byte-compare (H1 witness)
#
# Frames are extracted per `; === CLIF <module>::<symbol> ===` block and
# sorted by module::symbol (harness-side sort — the G-1 default resolution;
# if /backend's H1 work shows mid-function interleaving, the sort moves
# in-process and this script drops its own).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BIN="$ROOT/target/debug/cranelisp"
BASE="$ROOT/tests/fixtures/clif_baseline"
GOLD="$BASE/golden"
S99="$ROOT/tests/fixtures/s99"

# entry:source pairs — keep in sync with MANIFEST.md §Entries.
ENTRIES=(
  "01_adt_construct_match:$BASE/corpus/01_adt_construct_match.cl"
  "02_closures_fn_as_value:$BASE/corpus/02_closures_fn_as_value.cl"
  "03_auto_curry:$BASE/corpus/03_auto_curry.cl"
  "04_vec_cow_loop:$BASE/corpus/04_vec_cow_loop.cl"
  "05_string_externs:$BASE/corpus/05_string_externs.cl"
  "06_tco_loop:$BASE/corpus/06_tco_loop.cl"
  "07_trait_dispatch:$BASE/corpus/07_trait_dispatch.cl"
  "08_adt_in_vec_projection:$BASE/corpus/08_adt_in_vec_projection.cl"
  "09_parbind_launch:$BASE/corpus/09_parbind_launch.cl"
  "f1_machinery:$S99/f1_machinery.cl"
  "f2_contention:$S99/f2_contention.cl"
  "f3_inverted_search:$S99/f3_inverted_search.cl"
  "f4_sudoku:$S99/f4_sudoku.cl"
)

[ -x "$BIN" ] || { echo "error: $BIN not built (cargo build first)"; exit 2; }

# dump <source.cl> <out-file> — cold-cache --run with the config pins
# (MANIFEST §Capture contract): perf toggles UNSET, fresh tmpdir, dump
# frames extracted from STDERR (the CRANELISP_CODEGEN_DUMP channel per
# design/backend/ownership-codegen.md §13.1 and backend lib.rs — stdout
# carries only the program's own output), sorted by module::symbol.
dump() {
  local src="$1" out="$2"
  local d
  d="$(mktemp -d)"
  cp "$src" "$d/user.cl"
  (
    cd "$d"
    env -u CRANELISP_NO_OWNERSHIP -u CRANELISP_NO_LENIENT -u CRANELISP_RC_STATS \
        -u CRANELISP_RC_TRACE -u CRANELISP_CODEGEN_TRACE \
        CRANELISP_CODEGEN_DUMP='*' "$BIN" --run user.cl >raw.txt 2>err.txt
  ) || true   # program exit code is its return value, not a failure signal
  # Extract frames and sort by the module::symbol header. Frames are
  # `; === CLIF <name> ===` ... `; === end CLIF <name> ===`; duplicate
  # frames (recompilation passes) dedup to the FIRST occurrence — the
  # initial cold-cache compile, which is byte-deterministic. Later passes
  # re-derive the JIT symbol set after scheduler-timing-dependent symbol
  # registrations, so their FuncId immediates (`u0:N`) shuffle run-to-run
  # and carry no emission signal (B0-be determinism finding, S102; see
  # design/backend/ownership-codegen.md §13.1).
  python3 - "$d/err.txt" "$out" <<'PY'
import re, sys
raw = open(sys.argv[1]).read()
frames = {}
for m in re.finditer(r'; === CLIF (\S+) ===\n(.*?); === end CLIF \1 ===\n',
                     raw, re.S):
    frames.setdefault(m.group(1), m.group(0))
with open(sys.argv[2], 'w') as f:
    for name in sorted(frames):
        f.write(frames[name])
PY
  rm -rf "$d"
}

mode="${1:-diff}"
fail=0
case "$mode" in
  capture)
    mkdir -p "$GOLD"
    for e in "${ENTRIES[@]}"; do
      name="${e%%:*}"; src="${e#*:}"
      # Determinism self-test before writing the golden (MANIFEST pin).
      dump "$src" "$GOLD/.$name.a"; dump "$src" "$GOLD/.$name.b"
      if ! cmp -s "$GOLD/.$name.a" "$GOLD/.$name.b"; then
        echo "NONDETERMINISTIC: $name — H1 (frame-atomic/ordered dump) not satisfied; golden NOT written"
        rm -f "$GOLD/.$name.a" "$GOLD/.$name.b"; fail=1; continue
      fi
      mv "$GOLD/.$name.a" "$GOLD/$name.clif"; rm -f "$GOLD/.$name.b"
      echo "captured: $name ($(wc -l < "$GOLD/$name.clif") lines)"
    done
    ;;
  diff)
    for e in "${ENTRIES[@]}"; do
      name="${e%%:*}"; src="${e#*:}"
      if [ ! -f "$GOLD/$name.clif" ]; then
        echo "MISSING GOLDEN: $name (B0-be capture not landed?)"; fail=1; continue
      fi
      t="$(mktemp)"; dump "$src" "$t"
      if ! diff -u "$GOLD/$name.clif" "$t" > /dev/null; then
        echo "DIFF: $name"; diff -u "$GOLD/$name.clif" "$t" | head -40; fail=1
      else
        echo "ok: $name"
      fi
      rm -f "$t"
    done
    ;;
  selftest)
    for e in "${ENTRIES[@]}"; do
      name="${e%%:*}"; src="${e#*:}"
      a="$(mktemp)"; b="$(mktemp)"
      dump "$src" "$a"; dump "$src" "$b"
      if cmp -s "$a" "$b"; then echo "deterministic: $name"; else echo "NONDETERMINISTIC: $name"; fail=1; fi
      rm -f "$a" "$b"
    done
    ;;
  *) echo "usage: $0 {capture|diff|selftest}"; exit 2 ;;
esac
exit $fail
